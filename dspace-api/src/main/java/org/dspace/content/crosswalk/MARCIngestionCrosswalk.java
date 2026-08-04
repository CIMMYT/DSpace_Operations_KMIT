/**
 * The contents of this file are subject to the license and copyright
 * detailed in the LICENSE and NOTICE files at the root of the source
 * tree and available online at
 *
 * http://www.dspace.org/license/
 */
package org.dspace.content.crosswalk;

import java.io.IOException;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.BasicFileAttributes;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;
import java.util.stream.Collectors;

import jakarta.mail.MessagingException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.ThreadContext;
import org.dspace.authorize.AuthorizeException;
import org.dspace.content.DSpaceObject;
import org.dspace.content.Item;
import org.dspace.content.MetadataField;
import org.dspace.content.factory.ContentServiceFactory;
import org.dspace.content.service.ItemService;
import org.dspace.core.Constants;
import org.dspace.core.Context;
import org.dspace.core.Email;
import org.dspace.core.I18nUtil;
import org.dspace.services.ConfigurationService;
import org.dspace.services.factory.DSpaceServicesFactory;
import org.jdom2.Element;

/**
 * Ingestion crosswalk that maps MARC21 (MARCXML) records harvested from Koha onto the
 * Dublin Core schema of DSpace, driven entirely by {@code [dspace]/config/modules/marc21cross.cfg}.
 *
 * <p>Refactor of the DSpace 7.6 implementation for <b>DSpace 9.3 / Java 17</b>. All business
 * rules of the original are preserved: default-valued metadata
 * ({@code crosswalk.marc21.default.metadata}), direct pass-through metadata
 * ({@code crosswalk.marc21.directly.metadata} and {@code .single}), per-resource-type harvesting
 * ({@code crosswalk.marc21.fields.fortype.enable}), the special dc.title assembly and MARC 700
 * author/contributor split, the discoverable/notification behaviour, and the five value
 * transformations {@code DIVIDE}, {@code MAYUS}/{@code MINUS}, {@code SELECT}/{@code SELECTNR},
 * {@code REPLACE} and {@code CONVERT}.</p>
 *
 * <h2>Compatibility-critical change for DSpace 8+/9.x</h2>
 * <p>Since DSpace 8.0, {@code DSpaceObjectServiceImpl.addMetadata(..., List<String> values, ...)}
 * throws {@link IllegalArgumentException} ("Cannot add empty values...") when the list is empty.
 * That guard does <b>not</b> exist in 7.6, where the empty call was a silent no-op the original
 * code relied on constantly (missing MARC tag, SELECT with no match, no 700$e entries...). Every
 * write now goes through {@link #addIfPresent}, which still invokes
 * {@link CrosswalkMetadataValidator#checkMetadata} (preserving the field-creation side effect of
 * {@code createMissingMetadataFields}) but only calls {@code addMetadata} when there is at least
 * one value. Without this, virtually every harvested record aborts on 9.3.</p>
 *
 * <h2>Logging</h2>
 * <p>All {@code System.out} / {@code System.err} tracing has been replaced by a dedicated Log4j2
 * logger named {@value #LOGGER_NAME}, routed by {@code [dspace]/config/log4j2.xml} to
 * {@code [dspace]/log/marc21-ingestion.log}. Severities: {@code ERROR} for failures, {@code WARN}
 * for anomalous data (unmapped vocabulary terms, malformed directives, MARC subfields without a
 * {@code code} attribute), {@code DEBUG} for value-level tracing. Every line is correlated with
 * the MARC control number (field 001) through the ThreadContext/MDC key
 * {@value #MDC_RECORD_ID}, rendered by the appender pattern as {@code %X{marcRecordId}}.</p>
 *
 * <p>The class is stateless apart from immutable caches and is safe for concurrent harvests.</p>
 */
public class MARCIngestionCrosswalk implements IngestionCrosswalk {

    /** Logger name referenced from {@code log4j2.xml}; do not rename without updating that file. */
    public static final String LOGGER_NAME = "org.dspace.marc21.ingestion";

    /** MDC key carrying the MARC control number (field 001) of the record being processed. */
    public static final String MDC_RECORD_ID = "marcRecordId";

    private static final Logger LOG = LogManager.getLogger(LOGGER_NAME);

    /* -------------------------------------------------------------------------------------- */
    /* Configuration property names (unchanged from the 7.6 implementation)                    */
    /* -------------------------------------------------------------------------------------- */

    private static final String PROP_CUSTOM = "crosswalk.marc21.custom.metadata";
    private static final String PROP_CUSTOM_ACTION_PREFIX = "crosswalk.marc21.custom.";
    private static final String PROP_CUSTOM_ACTION_SUFFIX = ".action";
    private static final String PROP_DEFAULT = "crosswalk.marc21.default.metadata";
    private static final String PROP_DIRECTLY = "crosswalk.marc21.directly.metadata";
    private static final String PROP_DIRECTLY_SINGLE = "crosswalk.marc21.directly.metadata.single";
    private static final String PROP_FORTYPE_ENABLE = "crosswalk.marc21.fields.fortype.enable";
    private static final String PROP_TYPE_LABEL = "crosswalk.marc21.type.label";
    private static final String PROP_ONLY_PREFIX = "crosswalk.marc21.only.";
    private static final String PROP_ONLY_SUFFIX = ".metadata";
    private static final String PROP_TITLE_SPLIT = "crosswalk.marc21.is.dc.tittle.split";
    private static final String PROP_TITLE_CLEAN = "crosswalk.marc21.dc.title.clean";
    private static final String PROP_700_ENABLED = "crosswalk.marc21.dc.optional.700.enabled";
    private static final String PROP_700_OPTIONAL_DC = "crosswalk.marc21.700.e-enabled.optional.dc";
    private static final String PROP_DISCOVERABLE = "crosswalk.marc21.item.discoverable";
    private static final String PROP_NOTIFICATION = "crosswalk.marc21.item.harvest.notification";
    private static final String PROP_MAIL_RECIPIENTS = "mail.harvest.koha";
    private static final String EMAIL_TEMPLATE = "submit_koha";

    /** Separator between consecutive entries inside a single configuration property. */
    private static final String ENTRY_SEPARATOR = ":-:";

    /* -------------------------------------------------------------------------------------- */
    /* DSpace services                                                                         */
    /* -------------------------------------------------------------------------------------- */

    protected ItemService itemService = ContentServiceFactory.getInstance().getItemService();
    private final CrosswalkMetadataValidator metadataValidator = new CrosswalkMetadataValidator();
    protected ConfigurationService configurationService =
        DSpaceServicesFactory.getInstance().getConfigurationService();

    /* ====================================================================================== */
    /* IngestionCrosswalk contract (signatures unchanged between DSpace 7.6 and 9.3)          */
    /* ====================================================================================== */

    @Override
    public void ingest(Context context, DSpaceObject dso, List<Element> metadata,
                       boolean createMissingMetadataFields)
        throws CrosswalkException, IOException, SQLException, AuthorizeException {

        // If this list contains only the root already, just pass it on
        if (metadata.size() == 1) {
            ingest(context, dso, metadata.get(0), createMissingMetadataFields);
        } else {
            // Otherwise, wrap them up
            Element wrapper = new Element("wrap", metadata.get(0).getNamespace());
            wrapper.addContent(metadata);
            ingest(context, dso, wrapper, createMissingMetadataFields);
        }
    }

    @Override
    public void ingest(Context context, DSpaceObject dso, Element root, boolean createMissingMetadataFields)
        throws CrosswalkException, IOException, SQLException, AuthorizeException {

        if (dso.getType() != Constants.ITEM) {
            throw new CrosswalkObjectNotSupported("MARCIngestionCrosswalk can only crosswalk an Item.");
        }
        Item item = (Item) dso;

        if (root == null) {
            LOG.error("The element received by ingest was null; record skipped");
            return;
        }

        List<Element> metadata = root.getChildren();

        // Correlate every log line of this record with its MARC control number (001).
        String previousMdc = ThreadContext.get(MDC_RECORD_ID);
        ThreadContext.put(MDC_RECORD_ID, controlNumber(metadata).orElse("unknown"));
        try {
            processCustomMetadata(context, item, metadata, createMissingMetadataFields);
            processDefaultMetadata(context, item, createMissingMetadataFields);
            processDirectlySingleMetadata(context, item, metadata, createMissingMetadataFields);
            processTypeSpecificMetadata(context, item, metadata, createMissingMetadataFields);
            processDirectlyMetadata(context, item, metadata, createMissingMetadataFields);
            applyDiscoverabilityAndNotify(item);
        } finally {
            if (previousMdc == null) {
                ThreadContext.remove(MDC_RECORD_ID);
            } else {
                ThreadContext.put(MDC_RECORD_ID, previousMdc);
            }
        }
    }

    /* ====================================================================================== */
    /* Processing sections (one per configuration block, same order as the original)          */
    /* ====================================================================================== */

    /**
     * {@code crosswalk.marc21.custom.metadata}: values harvested from MARC and passed through the
     * per-field {@code .action} directive (DIVIDE, MAYUS/MINUS, SELECT, REPLACE, CONVERT).
     */
    private void processCustomMetadata(Context context, Item item, List<Element> metadata,
                                       boolean createMissingMetadataFields)
        throws CrosswalkException, SQLException, AuthorizeException {

        for (Directive directive : parseDirectives(configurationService.getProperty(PROP_CUSTOM))) {
            List<String> values = getCompoundValues(metadata, directive.argument());
            String action = configurationService.getProperty(
                PROP_CUSTOM_ACTION_PREFIX + directive.rawKey() + PROP_CUSTOM_ACTION_SUFFIX);
            LOG.debug("custom [{}] action [{}] raw values {}", directive.rawKey(), action, values);
            if (action != null && !action.isBlank()) {
                values = getCustomValues(values, action, dspaceDir());
                LOG.debug("custom [{}] transformed values {}", directive.rawKey(), values);
            }
            addIfPresent(context, item, directive.key(), values, createMissingMetadataFields);
        }
    }

    /**
     * {@code crosswalk.marc21.default.metadata}: constant values recorded on every item.
     */
    private void processDefaultMetadata(Context context, Item item, boolean createMissingMetadataFields)
        throws CrosswalkException, SQLException, AuthorizeException {

        for (Directive directive : parseDirectives(configurationService.getProperty(PROP_DEFAULT))) {
            addIfPresent(context, item, directive.key(), List.of(directive.argument()),
                         createMissingMetadataFields);
        }
    }

    /**
     * {@code crosswalk.marc21.directly.metadata.single}: control fields addressed by tag only
     * (e.g. {@code dcterms.identifier = 001}).
     */
    private void processDirectlySingleMetadata(Context context, Item item, List<Element> metadata,
                                               boolean createMissingMetadataFields)
        throws CrosswalkException, SQLException, AuthorizeException {

        for (Directive directive : parseDirectives(configurationService.getProperty(PROP_DIRECTLY_SINGLE))) {
            List<String> values = getSingleValues(metadata, directive.argument());
            addIfPresent(context, item, directive.key(), values, createMissingMetadataFields);
        }
    }

    /**
     * {@code crosswalk.marc21.only.<type>.metadata}: fields harvested only for the resource type
     * announced by {@code crosswalk.marc21.type.label}, gated by
     * {@code crosswalk.marc21.fields.fortype.enable} (default {@code false}).
     */
    private void processTypeSpecificMetadata(Context context, Item item, List<Element> metadata,
                                             boolean createMissingMetadataFields)
        throws CrosswalkException, SQLException, AuthorizeException {

        if (!configurationService.getBooleanProperty(PROP_FORTYPE_ENABLE, false)) {
            return;
        }
        String typeLabel = configurationService.getProperty(PROP_TYPE_LABEL);
        if (typeLabel == null || typeLabel.isBlank()) {
            return;
        }
        List<String> typeValues = getCompoundValues(metadata, typeLabel.trim());
        if (typeValues.isEmpty()) {
            LOG.warn("fields.fortype enabled but the record carries no [{}] type tag", typeLabel.trim());
            return;
        }
        String resourceType = typeValues.get(0).toLowerCase(Locale.ROOT).trim();
        String property = configurationService.getProperty(PROP_ONLY_PREFIX + resourceType + PROP_ONLY_SUFFIX);
        LOG.debug("resource type [{}], type-specific mapping {}", resourceType,
                  property == null ? "absent" : "present");
        for (Directive directive : parseDirectives(property)) {
            List<String> values = getCompoundValues(metadata, directive.argument());
            addIfPresent(context, item, directive.key(), values, createMissingMetadataFields);
        }
    }

    /**
     * {@code crosswalk.marc21.directly.metadata}: pass-through subfield values, with the two
     * special cases of the original preserved verbatim - dc.title assembly from several subfields
     * when {@code crosswalk.marc21.is.dc.tittle.split} is on, and the MARC 700 creator/contributor
     * split when {@code crosswalk.marc21.dc.optional.700.enabled} is on.
     */
    private void processDirectlyMetadata(Context context, Item item, List<Element> metadata,
                                         boolean createMissingMetadataFields)
        throws CrosswalkException, SQLException, AuthorizeException {

        boolean titleSplit = configurationService.getBooleanProperty(PROP_TITLE_SPLIT, false);
        boolean field700Enabled = configurationService.getBooleanProperty(PROP_700_ENABLED, false);

        for (Directive directive : parseDirectives(configurationService.getProperty(PROP_DIRECTLY))) {
            String rawKey = directive.rawKey();
            String label = directive.argument();

            if (rawKey.contains("dc.title") && titleSplit) {
                LOG.debug("dc.title split option enabled for [{}]", rawKey);
                boolean clean = configurationService.getBooleanProperty(PROP_TITLE_CLEAN, false);
                List<String> values = getTitleValues(metadata, label, clean);
                addIfPresent(context, item, directive.key(), values, createMissingMetadataFields);

            } else if (label.contains("700") && field700Enabled) {
                LOG.debug("MARC 700 author/contributor option enabled");
                AuthorNames names = separateAuthorNames(metadata, label);

                // Names carrying $e go to the alternative field (dc.contributor by default)...
                String optionalDc = configurationService.getProperty(PROP_700_OPTIONAL_DC, "dc.contributor");
                addIfPresent(context, item, MetadataKey.parse(optionalDc), names.contributors(),
                             createMissingMetadataFields);
                // ...and the rest to the field configured for the 700 label itself.
                addIfPresent(context, item, directive.key(), names.creators(), createMissingMetadataFields);

            } else {
                List<String> values = getCompoundValues(metadata, label);
                addIfPresent(context, item, directive.key(), values, createMissingMetadataFields);
            }
        }
    }

    /**
     * Discoverability and curator notification, unchanged from the original: when
     * {@code crosswalk.marc21.item.discoverable} is off (the default) the item is hidden and,
     * unless {@code crosswalk.marc21.item.harvest.notification} is explicitly disabled, the
     * {@code submit_koha} email is sent.
     */
    private void applyDiscoverabilityAndNotify(Item item) {
        boolean discoverable = configurationService.getBooleanProperty(PROP_DISCOVERABLE, false);
        if (discoverable) {
            return;
        }
        LOG.info("Item is not discoverable; it will appear under private items");
        item.setDiscoverable(false);
        if (configurationService.getBooleanProperty(PROP_NOTIFICATION, true)) {
            emailSuccessMail(item.getName());
        }
    }

    /* ====================================================================================== */
    /* Metadata write helper                                                                   */
    /* ====================================================================================== */

    /**
     * Validates (and, when {@code createMissingMetadataFields} allows, creates) the metadata field
     * and records the values.
     *
     * <p>{@code checkMetadata} is invoked unconditionally to preserve its field-creation side
     * effect; {@code addMetadata} is invoked only when at least one value survived, because
     * DSpace 8+/9.x throws {@link IllegalArgumentException} on an empty list - the single most
     * important behavioural difference with the 7.6 runtime this code was written for.</p>
     */
    private void addIfPresent(Context context, Item item, MetadataKey key, List<String> values,
                              boolean createMissingMetadataFields)
        throws CrosswalkException, SQLException, AuthorizeException {

        MetadataField field = metadataValidator.checkMetadata(
            context, key.schema(), key.element(), key.qualifier(), createMissingMetadataFields);
        if (values == null || values.isEmpty()) {
            LOG.debug("No values for [{}]; skipping addMetadata (empty lists abort on DSpace 8+)", key);
            return;
        }
        itemService.addMetadata(context, item, field, null, values);
    }

    /* ====================================================================================== */
    /* Configuration parsing                                                                   */
    /* ====================================================================================== */

    /**
     * Immutable Dublin Core coordinate (schema / element / qualifier). Replaces the positional
     * {@code ArrayList<String> get_metadata_schema(String)} of the original; the parsing rule is
     * identical - split on dots, missing components are {@code null}, extra components ignored.
     */
    record MetadataKey(String schema, String element, String qualifier) {

        static MetadataKey parse(String raw) {
            String[] parts = raw.trim().split("[.]");
            return new MetadataKey(
                parts.length > 0 ? parts[0] : null,
                parts.length > 1 ? parts[1] : null,
                parts.length > 2 ? parts[2] : null);
        }

        @Override
        public String toString() {
            return schema + (element == null ? "" : "." + element)
                + (qualifier == null ? "" : "." + qualifier);
        }
    }

    /**
     * One {@code left = right} entry of a {@code :-:}-separated configuration property.
     *
     * @param rawKey   left hand side, e.g. {@code dc.title.alternative} (used to build the
     *                 {@code .action} property name)
     * @param key      parsed Dublin Core coordinate
     * @param argument right hand side: a MARC label, a control tag, or a literal default value
     */
    record Directive(String rawKey, MetadataKey key, String argument) {
    }

    /**
     * Parsed-directive cache. Configuration strings are stable for the JVM lifetime while
     * {@code ingest()} runs once per harvested record, so caching turns a per-record
     * split/substring storm into one map lookup. Bounded by the number of distinct properties.
     */
    private static final Map<String, List<Directive>> DIRECTIVE_CACHE = new ConcurrentHashMap<>();

    /**
     * Parses a whole configuration property into its directives.
     *
     * <p><b>Hardening:</b> the original ran {@code substring(0, indexOf('='))} and threw
     * {@link StringIndexOutOfBoundsException} - aborting the whole record - when one entry lacked
     * its {@code =}. Malformed entries are now skipped and reported.</p>
     */
    static List<Directive> parseDirectives(String property) {
        if (property == null || property.isBlank()) {
            return List.of();
        }
        return DIRECTIVE_CACHE.computeIfAbsent(property, p -> {
            List<Directive> directives = new ArrayList<>();
            for (String entry : p.split(ENTRY_SEPARATOR)) {
                int eq = entry.indexOf('=');
                if (eq < 0) {
                    LOG.warn("Malformed crosswalk entry, '=' not found, entry skipped: [{}]", entry.trim());
                    continue;
                }
                String rawKey = entry.substring(0, eq).trim();
                String argument = entry.substring(eq + 1).trim();
                if (rawKey.isEmpty()) {
                    LOG.warn("Malformed crosswalk entry, empty metadata field, entry skipped: [{}]",
                             entry.trim());
                    continue;
                }
                directives.add(new Directive(rawKey, MetadataKey.parse(rawKey), argument));
            }
            return List.copyOf(directives);
        });
    }

    /* ====================================================================================== */
    /* MARCXML readers (formerly get_compound_values / get_single_values / get_title_values /  */
    /* separate_author_names)                                                                  */
    /* ====================================================================================== */

    /**
     * MARC control number (field 001), used only for log correlation.
     */
    private static Optional<String> controlNumber(List<Element> metadata) {
        return metadata.stream()
                       .filter(e -> "001".equals(e.getAttributeValue("tag")))
                       .map(Element::getValue)
                       .filter(v -> v != null && !v.isBlank())
                       .map(String::trim)
                       .findFirst();
    }

    /**
     * Values of a repeatable subfield, e.g. {@code 650 - a}.
     *
     * <p><b>Hardening applied here and in every reader below:</b> subfield tests are written as
     * {@code code.equals(node.getAttributeValue("code"))}. The original inverted form threw
     * {@link NullPointerException} - aborting the harvest - whenever Koha exported a
     * {@code <subfield>} without a {@code code} attribute. Same result on well-formed data.</p>
     */
    static List<String> getCompoundValues(List<Element> metadata, String metadataLabel) {
        String[] label = metadataLabel.split("-");
        if (label.length < 2) {
            LOG.warn("MARC label [{}] has no subfield code ('<tag> - <code>' expected), entry skipped",
                     metadataLabel);
            return new ArrayList<>();
        }
        String tag = label[0].trim();
        String code = label[1].trim();

        List<String> values = new ArrayList<>();
        for (Element element : metadata) {
            if (!tag.equals(element.getAttributeValue("tag"))) {
                continue;
            }
            for (Element node : element.getChildren()) {
                if (code.equals(node.getAttributeValue("code"))) {
                    values.add(node.getValue());
                }
            }
        }
        return values;
    }

    /**
     * Text content of fields addressed by tag only (control fields such as {@code 001}).
     */
    static List<String> getSingleValues(List<Element> metadata, String metadataLabel) {
        String tag = metadataLabel.split("-")[0].trim();
        List<String> values = new ArrayList<>();
        for (Element element : metadata) {
            if (tag.equals(element.getAttributeValue("tag"))) {
                values.add(element.getValue());
            }
        }
        return values;
    }

    /**
     * Title assembled from several subfields of one field, e.g. {@code 245 - a,b}: subfields are
     * concatenated in label order, blank-separated; empty results are discarded; when
     * {@code clean} is on, {@code " : "} collapses into {@code ": "}. Identical to the original.
     */
    static List<String> getTitleValues(List<Element> metadata, String metadataLabel, boolean clean) {
        String[] label = metadataLabel.split("-");
        if (label.length < 2) {
            LOG.warn("MARC title label [{}] has no subfield codes, entry skipped", metadataLabel);
            return new ArrayList<>();
        }
        String tag = label[0].trim();
        String[] codes = label[1].trim().split(",");

        List<String> values = new ArrayList<>();
        for (Element element : metadata) {
            if (!tag.equals(element.getAttributeValue("tag"))) {
                continue;
            }
            StringBuilder assembled = new StringBuilder();
            for (String rawCode : codes) {
                String code = rawCode.trim();
                for (Element node : element.getChildren()) {
                    if (code.equals(node.getAttributeValue("code"))) {
                        assembled.append(' ').append(node.getValue());
                    }
                }
            }
            String value = assembled.toString();
            if (!value.trim().isEmpty()) {
                if (clean) {
                    value = value.replaceAll("\\s+:\\s+", ": ");
                }
                values.add(value.trim());
            }
        }
        return values;
    }

    /**
     * Two buckets produced by the MARC 700 split.
     *
     * @param contributors names whose field carries a {@code $e} relator subfield
     * @param creators     names without a relator subfield
     */
    record AuthorNames(List<String> contributors, List<String> creators) {
    }

    /**
     * Splits personal names (typically MARC 700): a field carrying {@code $e} yields a
     * contributor, otherwise a creator.
     *
     * <p><b>Hardening:</b> a field matching the tag but lacking the requested subfield produced a
     * {@code null} entry in the original lists; such fields are now dropped and reported, since a
     * null value is silently discarded by {@code addMetadata} anyway and only hid a data problem.</p>
     */
    static AuthorNames separateAuthorNames(List<Element> metadata, String metadataLabel) {
        String[] label = metadataLabel.split("-");
        if (label.length < 2) {
            LOG.warn("MARC label [{}] has no subfield code, author split skipped", metadataLabel);
            return new AuthorNames(new ArrayList<>(), new ArrayList<>());
        }
        String tag = label[0].trim();
        String code = label[1].trim();

        List<String> contributors = new ArrayList<>();
        List<String> creators = new ArrayList<>();
        for (Element element : metadata) {
            if (!tag.equals(element.getAttributeValue("tag"))) {
                continue;
            }
            String name = null;
            boolean hasRole = false;
            for (Element node : element.getChildren()) {
                String subfieldCode = node.getAttributeValue("code");
                if (code.equals(subfieldCode)) {
                    name = node.getValue();
                }
                if ("e".equals(subfieldCode)) {
                    hasRole = true;
                }
            }
            if (name == null) {
                LOG.warn("MARC field [{}] present but subfield [${}] missing; entry discarded", tag, code);
                continue;
            }
            if (hasRole) {
                contributors.add(name);
            } else {
                creators.add(name);
            }
        }
        return new AuthorNames(contributors, creators);
    }

    /* ====================================================================================== */
    /* Value transformations (Strategy dispatch, formerly get_custom_values)                   */
    /* ====================================================================================== */

    /**
     * Stateless strategy for one {@code .action} keyword family. All state travels through the
     * arguments, so a single lambda instance is shared by every harvest thread.
     */
    @FunctionalInterface
    interface ValueTransformer {
        List<String> apply(List<String> values, String command, String dspaceDir);
    }

    /**
     * One dispatch rule: the keywords routed to a strategy.
     */
    private record TransformRule(List<String> keywords, ValueTransformer transformer) {
        boolean matches(String normalisedCommand) {
            return keywords.stream().anyMatch(normalisedCommand::contains);
        }
    }

    /**
     * Ordered dispatch table. <b>The order and the {@code contains} test over the whole directive
     * are load-bearing and reproduce the original {@code if/else if} chain exactly</b> (DIVIDE,
     * MAYUS/MINUS, SELECT/SELECTNR, REPLACE, CONVERT, fall through to identity). A directive whose
     * <i>argument</i> contains an earlier keyword is routed to that earlier strategy, just as
     * before; none of the directives in {@code marc21cross.cfg} hits this, and the behaviour is
     * kept on purpose so the refactor cannot change the output of the production configuration.
     */
    private static final List<TransformRule> TRANSFORM_RULES = List.of(
        new TransformRule(List.of("divide"), (v, c, d) -> divideTerms(v, c)),
        new TransformRule(List.of("mayus", "minus"), (v, c, d) -> capitalize(v, c)),
        new TransformRule(List.of("select", "selectnr"), (v, c, d) -> selectSubstring(v, c)),
        new TransformRule(List.of("replace"), (v, c, d) -> replaceString(v, c)),
        new TransformRule(List.of("convert"), MARCIngestionCrosswalk::convertString));

    /**
     * Applies the matching action, or returns the values untouched when the directive is
     * unrecognised - the original {@code else return values;} branch.
     */
    static List<String> getCustomValues(List<String> values, String command, String dspaceDir) {
        String normalised = command.toLowerCase(Locale.ROOT);
        return TRANSFORM_RULES.stream()
                              .filter(rule -> rule.matches(normalised))
                              .findFirst()
                              .map(rule -> rule.transformer().apply(values, command, dspaceDir))
                              .orElseGet(() -> {
                                  LOG.warn("Unknown crosswalk action [{}], values left untouched", command);
                                  return values;
                              });
    }

    /**
     * {@code DIVIDE - <separator> - <L|R|A>}: splits every value in two around the first match of
     * {@code separator} (a regular expression, as before) and keeps left, right or both halves.
     * Edge cases preserved: a directive without exactly three parts is rejected with the values
     * untouched; any retention flag other than {@code l}/{@code r} keeps both halves; a value not
     * containing the separator passes through unchanged.
     */
    static List<String> divideTerms(List<String> values, String command) {
        String[] parts = command.split("-");
        if (parts.length != 3) {
            LOG.warn("Command DIVIDE invalid, not have all arguments [{}]", command);
            return values;
        }
        Optional<Pattern> pattern = compiled(parts[1].trim());
        if (pattern.isEmpty()) {
            LOG.error("Command DIVIDE has an invalid separator [{}], values left untouched", parts[1].trim());
            return values;
        }
        String retain = parts[2].trim().toLowerCase(Locale.ROOT);

        List<String> result = new ArrayList<>(values.size());
        for (String value : values) {
            String[] halves = pattern.get().split(value, 2);
            if (halves.length == 2 && "l".equals(retain)) {
                result.add(halves[0]);
            } else if (halves.length == 2 && "r".equals(retain)) {
                result.add(halves[1]);
            } else {
                Collections.addAll(result, halves);
            }
        }
        return result;
    }

    /**
     * {@code MAYUS} / {@code MINUS}: upper- or lower-cases every value. The directive takes no
     * arguments, so anything containing {@code -} is rejected with the values untouched; an
     * unrecognised keyword leaves each value unchanged - both as before. Case conversion is now
     * locale-independent ({@link Locale#ROOT}); the original used the JVM default locale, which
     * corrupts {@code i} under a Turkish locale.
     */
    static List<String> capitalize(List<String> values, String command) {
        String[] parts = command.split("-");
        if (parts.length != 1) {
            LOG.warn("Command MAYUS | MINUS invalid, This command not have arguments [{}]", command);
            return values;
        }
        String keyword = parts[0].trim().toLowerCase(Locale.ROOT);
        return values.stream()
                     .map(value -> switch (keyword) {
                         case "mayus" -> value.toUpperCase(Locale.ROOT);
                         case "minus" -> value.toLowerCase(Locale.ROOT);
                         default -> value;
                     })
                     .collect(Collectors.toCollection(ArrayList::new));
    }

    /**
     * {@code SELECT - <prefix>} / {@code SELECTNR - <literal>}, optionally chained with
     * {@code :-:}. Each value is split on commas; fragments whose trimmed form starts with the
     * token are selected. SELECT strips the token ({@code v. 12} - {@code 12}); SELECTNR emits the
     * token itself (how {@code In press} becomes a volume). Chain semantics preserved: first
     * non-empty result wins; a malformed link aborts the chain returning the <i>original</i>
     * values; no match at all returns an empty list so no metadata is recorded.
     */
    static List<String> selectSubstring(List<String> values, String command) {
        for (String single : command.split(ENTRY_SEPARATOR)) {
            String[] parts = single.split("-");
            if (parts.length != 2) {
                LOG.warn("Command SELECT invalid, not have all arguments [{}]", command);
                return values;
            }
            String option = parts[0].toLowerCase(Locale.ROOT).trim();
            String token = parts[1].trim();

            List<String> selected;
            if ("select".equals(option)) {
                selected = selectFragments(values, token, true);
            } else if ("selectnr".equals(option)) {
                selected = selectFragments(values, token, false);
            } else {
                selected = new ArrayList<>();
            }
            if (!selected.isEmpty()) {
                return selected;
            }
        }
        return new ArrayList<>();
    }

    private static List<String> selectFragments(List<String> values, String token, boolean strip) {
        List<String> result = new ArrayList<>();
        for (String value : values) {
            for (String fragment : value.split(",")) {
                if (fragment.trim().startsWith(token)) {
                    result.add(strip ? fragment.replace(token, "").trim() : token.trim());
                }
            }
        }
        return result;
    }

    /**
     * {@code REPLACE - <regex> - <replacement>}: regular-expression replacement with the three
     * documented escapes - {@code [c]} in the search position is a literal comma (a bare comma is
     * a list delimiter for the DSpace configuration parser), {@code [s]} in the replacement
     * position is a blank, {@code [d]} deletes. {@code [.]} and {@code http[s]?://doi.org/} reach
     * the regex engine untouched, which is what the production directives rely on. A directive
     * without exactly three {@code -}-separated parts is rejected with the values untouched.
     */
    static List<String> replaceString(List<String> values, String command) {
        String[] parts = command.split("-");
        if (parts.length != 3) {
            LOG.warn("Command REPLACE invalid, not have all arguments [{}]", command);
            return values;
        }
        String search = parts[1].trim();
        if ("[c]".equals(search)) {
            search = ",";
        }
        String rawReplacement = parts[2].trim();
        String replacement = switch (rawReplacement) {
            case "[s]" -> " ";
            case "[d]" -> "";
            default -> rawReplacement;
        };
        Optional<Pattern> pattern = compiled(search);
        if (pattern.isEmpty()) {
            LOG.error("Command REPLACE has an invalid expression [{}], values left untouched", search);
            return values;
        }
        Pattern compiled = pattern.get();
        // Matcher.quoteReplacement is deliberately NOT applied: the original used
        // String.replaceAll, so '$'/'\' group references in the replacement keep their meaning.
        return values.stream()
                     .map(value -> compiled.matcher(value).replaceAll(replacement))
                     .collect(Collectors.toCollection(ArrayList::new));
    }

    /**
     * {@code CONVERT - <vocabulary file> - [default]}: maps each value through a controlled
     * vocabulary from {@code [dspace]/config/controlled-vocabularies/}. Resolution rules
     * preserved: case-insensitive whole-value match; no match and no default keeps the value; no
     * match with a default uses the default; unreadable/empty vocabulary keeps every value.
     * Unmapped terms are written to the anomaly log so vocabulary drift between Koha and DSpace
     * becomes visible after each harvest.
     *
     * <p><b>Intentional fix:</b> the default is now trimmed. The original read it untrimmed, so
     * {@code CONVERT - marc21_correspondencias - Other} stored the literal {@code " Other"} - with
     * a leading blank - into dc.type for every unmapped resource type.</p>
     */
    static List<String> convertString(List<String> values, String command, String dspaceDir) {
        String[] parts = command.split("-");
        if (parts.length != 2 && parts.length != 3) {
            LOG.warn("Command CONVERT invalid, not have all arguments [{}]", command);
            return values;
        }
        String fileName = parts[1].trim();
        String defaultValue = parts.length == 3 ? parts[2].trim() : null;

        Map<String, String> table = vocabularyTable(dspaceDir, fileName);
        if (table.isEmpty()) {
            return values;
        }
        List<String> result = new ArrayList<>(values.size());
        for (String value : values) {
            String converted = table.get(value.toLowerCase(Locale.ROOT));
            if (converted != null) {
                result.add(converted);
            } else if (defaultValue == null) {
                LOG.warn("CONVERT: value [{}] not in vocabulary [{}], no default; value kept as-is",
                         value, fileName);
                result.add(value);
            } else {
                LOG.warn("CONVERT: value [{}] not in vocabulary [{}]; using default [{}]",
                         value, fileName, defaultValue);
                result.add(defaultValue);
            }
        }
        return result;
    }

    /* ====================================================================================== */
    /* Controlled-vocabulary cache (formerly get_file_lines)                                   */
    /* ====================================================================================== */

    /** Cheap file identity used to detect out-of-band edits without re-reading the file. */
    private record VocabStamp(long lastModified, long size) {
        static final VocabStamp MISSING = new VocabStamp(-1L, -1L);
    }

    private record VocabEntry(Map<String, String> table, VocabStamp stamp) {
    }

    private static final Map<String, VocabEntry> VOCABULARY_CACHE = new ConcurrentHashMap<>();

    /**
     * Loads (or returns the cached) conversion table of a vocabulary file.
     *
     * <p><b>Why this replaces {@code get_file_lines}:</b> the original opened a
     * {@code BufferedReader(new FileReader(...))}, read the whole file, and <i>never closed the
     * reader</i>; it ran once per CONVERT field per record, so a harvest of N records performed
     * 4xN full reads and leaked 4xN file descriptors. The file is now read once through NIO with
     * an explicit charset, held as a map for O(1) lookup instead of a per-value linear scan, and
     * re-read only when its mtime or size changes - operators can still edit a vocabulary without
     * restarting Tomcat.</p>
     *
     * <p>Parsing semantics preserved: key = text before the <i>first</i> {@code -}, value = the
     * rest, both trimmed; matching is case-insensitive over the whole value; on duplicate keys the
     * first occurrence wins (the original {@code break} on first match). Hardening: blank lines
     * and lines without {@code -} are skipped and reported - the original threw
     * {@link StringIndexOutOfBoundsException} on them, aborting the record.</p>
     */
    static Map<String, String> vocabularyTable(String dspaceDir, String fileName) {
        Path path = Path.of(dspaceDir, "config", "controlled-vocabularies", fileName.trim());
        String cacheKey = path.toString();
        VocabStamp current = stampOf(path);
        VocabEntry cached = VOCABULARY_CACHE.get(cacheKey);
        if (cached != null && cached.stamp().equals(current)) {
            return cached.table();
        }
        Map<String, String> table = loadVocabulary(path);
        VOCABULARY_CACHE.put(cacheKey, new VocabEntry(table, current));
        return table;
    }

    private static Map<String, String> loadVocabulary(Path path) {
        List<String> lines;
        try {
            lines = Files.readAllLines(path, StandardCharsets.UTF_8);
        } catch (IOException e) {
            LOG.warn("Controlled vocabulary [{}] could not be read ({}); CONVERT leaves values untouched",
                     path, e.getMessage());
            return Map.of();
        }
        Map<String, String> table = new HashMap<>(Math.max(16, lines.size() * 2));
        int lineNumber = 0;
        for (String rawLine : lines) {
            lineNumber++;
            String line = rawLine.trim();
            if (line.isEmpty()) {
                continue;
            }
            int dash = line.indexOf('-');
            if (dash < 0) {
                LOG.warn("Vocabulary [{}] line {} has no '-' separator, line ignored: [{}]",
                         path, lineNumber, line);
                continue;
            }
            table.putIfAbsent(line.substring(0, dash).trim().toLowerCase(Locale.ROOT),
                              line.substring(dash + 1).trim());
        }
        LOG.debug("Loaded controlled vocabulary [{}] with {} entries", path, table.size());
        return Map.copyOf(table);
    }

    private static VocabStamp stampOf(Path path) {
        try {
            BasicFileAttributes attrs = Files.readAttributes(path, BasicFileAttributes.class);
            return new VocabStamp(attrs.lastModifiedTime().toMillis(), attrs.size());
        } catch (IOException e) {
            return VocabStamp.MISSING;
        }
    }

    /* ====================================================================================== */
    /* Compiled-pattern cache                                                                  */
    /* ====================================================================================== */

    /**
     * {@code String.split}/{@code replaceAll} recompile their regex on every call; the original
     * did so once per harvested value. {@link Pattern} is immutable and thread-safe, so each
     * distinct expression is compiled once. Bounded by the number of directives in the
     * configuration. An invalid expression is reported once and yields {@link Optional#empty()}.
     */
    private static final Map<String, Optional<Pattern>> PATTERN_CACHE = new ConcurrentHashMap<>();

    private static Optional<Pattern> compiled(String regex) {
        return PATTERN_CACHE.computeIfAbsent(regex, r -> {
            try {
                return Optional.of(Pattern.compile(r));
            } catch (PatternSyntaxException e) {
                LOG.warn("Invalid regular expression in crosswalk directive [{}]: {}", r, e.getDescription());
                return Optional.empty();
            }
        });
    }

    /** Clears every internal cache. Intended for tests and administrative configuration reloads. */
    static void invalidateCaches() {
        DIRECTIVE_CACHE.clear();
        VOCABULARY_CACHE.clear();
        PATTERN_CACHE.clear();
    }

    /* ====================================================================================== */
    /* Harvest notification (formerly emailSuccessMail)                                        */
    /* ====================================================================================== */

    /**
     * Sends the {@code submit_koha} notification to the {@code mail.harvest.koha} recipients. A
     * mail failure can never abort a harvest: every exception is swallowed and logged - as before,
     * but with the stack trace preserved instead of only {@code e.getMessage()}.
     *
     * <p>DSpace 9 notes: {@code Email.send()} throws {@code jakarta.mail.MessagingException}
     * (the javax-to-jakarta migration), and
     * {@code URLEncoder.encode(String, Charset)} replaces the deprecated {@code (String, String)}
     * overload, removing the checked {@code UnsupportedEncodingException}.</p>
     */
    public void emailSuccessMail(String title) {
        String safeTitle = title == null ? "" : title;
        try {
            String[] recipients = configurationService.getArrayProperty(PROP_MAIL_RECIPIENTS);
            if (recipients == null || recipients.length == 0) {
                LOG.warn("No recipients configured in [{}], harvest notification not sent",
                         PROP_MAIL_RECIPIENTS);
                return;
            }
            Email email = Email.getEmail(
                I18nUtil.getEmailFilename(I18nUtil.getDefaultLocale(), EMAIL_TEMPLATE));
            Arrays.stream(recipients)
                  .map(String::trim)
                  .filter(r -> !r.isEmpty())
                  .forEach(email::addRecipient);
            email.addArgument(safeTitle);
            email.addArgument(configurationService.getProperty("dspace.ui.url")
                + "/admin/search?f.discoverable=false,equals&spc.page=1&query="
                + URLEncoder.encode(safeTitle.replace(":", " "), StandardCharsets.UTF_8));
            email.send();
            LOG.info("Harvest notification sent to {} recipient(s)", recipients.length);
        } catch (MessagingException | IOException | RuntimeException e) {
            LOG.error("Harvest notification could not be sent for item [" + safeTitle + "]", e);
        }
    }

    /* ====================================================================================== */
    /* Retained helper                                                                         */
    /* ====================================================================================== */

    private static final Set<Character> URL_SAFE_CHARS =
        ("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_.!~*'();/?:@&=+$,%#")
            .chars().mapToObj(c -> (char) c).collect(Collectors.toUnmodifiableSet());

    /**
     * Helper method to escape all characters that are not part of the canon set.
     *
     * <p>Retained verbatim from the 7.6 class, where it was private and never invoked; kept so
     * that nothing present in the original is lost. Note it is <i>not</i> a correct
     * percent-encoder (reserved characters pass through, hex is not zero-padded) - do not use it
     * for new work; use {@code URLEncoder.encode(String, Charset)} instead. The only change is
     * that the character set is built once instead of five array allocations per call.</p>
     *
     * @param sourceString source unescaped string
     */
    @SuppressWarnings("unused")
    private String encodeForURL(String sourceString) {
        StringBuilder processedString = new StringBuilder(sourceString.length());
        for (int i = 0; i < sourceString.length(); i++) {
            char ch = sourceString.charAt(i);
            if (URL_SAFE_CHARS.contains(ch)) {
                processedString.append(ch);
            } else {
                processedString.append('%').append(Integer.toHexString(ch));
            }
        }
        return processedString.toString();
    }

    private String dspaceDir() {
        return configurationService.getProperty("dspace.dir");
    }
}
