package org.dspace.content.crosswalk;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.ConnectException;
import java.net.URL;
import java.sql.SQLException;
import java.text.NumberFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.BufferedReader;
import java.io.FileReader;
import java.net.URLEncoder;
import java.util.Locale;
import java.util.UUID;

import org.apache.logging.log4j.Logger;
import org.dspace.authorize.AuthorizeException;
import org.dspace.content.*;
import org.dspace.content.factory.ContentServiceFactory;
import org.dspace.content.service.BitstreamFormatService;
import org.dspace.content.service.BitstreamService;
import org.dspace.content.service.BundleService;
import org.dspace.content.service.ItemService;
import org.dspace.core.Constants;
import org.dspace.core.Context;
import org.dspace.services.ConfigurationService;
import org.dspace.services.factory.DSpaceServicesFactory;
import org.jdom2.Attribute;
import org.jdom2.Document;
import org.jdom2.Element;
import org.jdom2.Namespace;
import org.jdom2.filter.Filters;
import org.jdom2.xpath.XPathExpression;
import org.jdom2.xpath.XPathFactory;

import org.dspace.core.Email;
import org.dspace.core.I18nUtil;


public class MARCIngestionCrosswalk implements IngestionCrosswalk {
    /**
     * log4j category
     */
    private static final Logger log = org.apache.logging.log4j.LogManager.getLogger();

    /* Namespaces */
    private static final Namespace DC_NS = Namespace.getNamespace("http://www.dspace.org/xmlns/dspace/dim");
    private static final Namespace MARC_NS = Namespace.getNamespace("http://www.loc.gov/MARC21/slim http://www.loc.gov/standards/marcxml/schema/MARC21slim");


    protected ItemService itemService = ContentServiceFactory.getInstance().getItemService();
    private CrosswalkMetadataValidator metadataValidator = new CrosswalkMetadataValidator();

    ConfigurationService configurationService = DSpaceServicesFactory.getInstance().getConfigurationService();



    @Override
    public void ingest(Context context, DSpaceObject dso, List<Element> metadata, boolean createMissingMetadataFields)
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

        Date timeStart = new Date();

        if (dso.getType() != Constants.ITEM) {
            throw new CrosswalkObjectNotSupported("OREIngestionCrosswalk can only crosswalk an Item.");
        }
        Item item = (Item) dso;

        if (root == null) {
            System.err.println("The element received by ingest was null");
            return;
        }

        List<Element> metadata = root.getChildren();

        MetadataField metadataField;

        /* Datos que requieren un tipo de procesado */

        String properties_custom = configurationService.getProperty("crosswalk.marc21.custom.metadata");
        if ((properties_custom != null) && (!"".equals(properties_custom.trim()))){
            String[] properties_custom_array = properties_custom.split(":-:");
            String metadata_label, metadata_key_string;
            ArrayList<String> metadata_key;
            for (String propertie: properties_custom_array) {
                metadata_key_string = propertie.substring(0, propertie.indexOf('=')).trim();
                metadata_key = get_metadata_schema(metadata_key_string);
                metadata_label = propertie.substring(propertie.indexOf('=')+1).trim();
                List<String> values = get_compound_values(metadata,metadata_label);
                //String propertie_custom_method = ConfigurationManager.getProperty("marc21cross","crosswalk.marc21.custom." + metadata_key_string + ".action");
                System.out.print("\t" +"crosswalk.marc21.custom." + metadata_key_string + ".action" + "\n");
                String propertie_custom_method = configurationService.getProperty("crosswalk.marc21.custom." + metadata_key_string + ".action");
                System.out.print("\t \t" + propertie_custom_method + "\n");
                if ((propertie_custom_method != null) && (!"".equals(propertie_custom_method.trim()))) {
                    //System.out.println("Se encontro un método que aplicarle a este metadato");
                    values = get_custom_values(values, propertie_custom_method);
                }
                metadataField = metadataValidator
                        .checkMetadata(context, metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), createMissingMetadataFields);
                itemService.addMetadata(context, item, metadataField, null, values);
            }
        }

        /* Datos con valores por defecto */

        String properties_default = configurationService.getProperty("crosswalk.marc21.default.metadata");
        if (properties_default != null && !"".equals(properties_default.trim())) {
            String[] properties = properties_default.split(":-:");
            for (String propertie : properties) {
                    ArrayList<String> metadata_key = get_metadata_schema(propertie.substring(0, propertie.indexOf('=')).trim());
                    String value = propertie.substring(propertie.indexOf('=') + 1).trim();
                    metadataField = metadataValidator.checkMetadata(context, metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), createMissingMetadataFields);
                    itemService.addMetadata(context, item, metadataField, null, value);
                } 
        }


        /* Metadatos directos sin necesidad de un procesamiento de datos */

        String properties_directly_single = configurationService.getProperty("crosswalk.marc21.directly.metadata.single");
        if (properties_directly_single != null && !"".equals(properties_directly_single.trim())) {
          String[] properties_single_array = properties_directly_single.split(":-:");
          for (String propertie : properties_single_array) {
            ArrayList<String> metadata_key = get_metadata_schema(propertie.substring(0, propertie.indexOf('=')).trim());
            String metadata_label = propertie.substring(propertie.indexOf('=') + 1).trim();
            List<String> values = get_single_values(metadata, metadata_label);
            metadataField = metadataValidator.checkMetadata(context, metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), createMissingMetadataFields);
            /* item.addMetadata(metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), null, values); */
            itemService.addMetadata(context, item, metadataField, null, values);
          } 
        }

        /* Datos que solo se deben consechar para  un tipo de recurso */

        Boolean fields_for_type = configurationService.getBooleanProperty("crosswalk.marc21.fields.fortype.enable", false);
        if (fields_for_type) {
          String property_type_tag = configurationService.getProperty("crosswalk.marc21.type.label");
          if (property_type_tag != null && !"".equals(property_type_tag.trim())) {
            List<String> type_values = get_compound_values(metadata, property_type_tag.trim());
            if (type_values.size() != 0) {
              String resource_type = type_values.get(0).toLowerCase().trim();
              String type_properties_values = configurationService.getProperty("crosswalk.marc21.only." + resource_type + ".metadata");
              if (type_properties_values != null && !"".equals(type_properties_values.trim())) {
                String[] properties_single_array = type_properties_values.split(":-:");
                
                for (String propertie : properties_single_array) {
                  ArrayList<String> metadata_key = get_metadata_schema(propertie.substring(0, propertie.indexOf('=')).trim());
                  String metadata_label = propertie.substring(propertie.indexOf('=') + 1).trim();
                  List<String> values = get_compound_values(metadata, metadata_label);
                  metadataField = metadataValidator.checkMetadata(context, metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), createMissingMetadataFields);
                  itemService.addMetadata(context, item, metadataField, null, values);
                } 
              } 
            } 
          } 
        }


        /* Datos que solo se recopilan */

        String properties_directly = configurationService.getProperty("crosswalk.marc21.directly.metadata");
        if (properties_directly != null && !"".equals(properties_directly.trim())) {
          String[] properties_directly_array = properties_directly.split(":-:");
          for (String propertie : properties_directly_array) {
            String metadata_key_string = propertie.substring(0, propertie.indexOf('=')).trim();
            ArrayList<String> metadata_key = get_metadata_schema(metadata_key_string);
            String metadata_label = propertie.substring(propertie.indexOf('=') + 1).trim();
            if (metadata_key_string.contains("dc.title") && configurationService.getBooleanProperty("crosswalk.marc21.is.dc.tittle.split", false)) {
              System.out.println("Esta habilitada la opcion de dc.title.* separado en dos subcampos");
              List<String> values = get_title_values(metadata, metadata_label);
              metadataField = metadataValidator.checkMetadata(context, metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), createMissingMetadataFields);
              itemService.addMetadata(context, item, metadataField, null, values);
            }
            else if (metadata_label.contains("700") && configurationService.getBooleanProperty("crosswalk.marc21.dc.optional.700.enabled", false)) {
              System.out.println("Esta habilitado la opcion 700 para autores");
              List<List<String>> dc_values = separate_author_names(metadata, metadata_label);

              String dc_optional = configurationService.getProperty("crosswalk.marc21.700.e-enabled.optional.dc", "dc.contributor");
              ArrayList<String> metadata_key_optional = get_metadata_schema(dc_optional);
              //metadata_key_optional.add("dc");
              //metadata_key_optional.add("contributor");
              //metadata_key_optional.add(null);
              /*
              if (dc_optional != null && !"".equals(dc_optional.trim())) {
                System.out.println("Se va a " + dc_optional + " en lugar de dc.contributor");
                metadata_key_optional = get_metadata_schema(dc_optional);
              }
              */
              metadataField = metadataValidator.checkMetadata(context, metadata_key_optional.get(0), metadata_key_optional.get(1), metadata_key_optional.get(2), createMissingMetadataFields);
              //item.addMetadata(metadata_key_optional.get(0), metadata_key_optional.get(1), metadata_key_optional.get(2), null, dc_values.get(0));
              itemService.addMetadata(context, item, metadataField, null, dc_values.get(0));

              metadataField = metadataValidator.checkMetadata(context, metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), createMissingMetadataFields);
              //item.addMetadata(metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), null, dc_values.get(1));
              itemService.addMetadata(context, item, metadataField, null, dc_values.get(1));
            } else {
              List<String> values = get_compound_values(metadata, metadata_label);
              metadataField = metadataValidator.checkMetadata(context, metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), createMissingMetadataFields);
              itemService.addMetadata(context, item, metadataField, null, values);
              //item.addMetadata(metadata_key.get(0), metadata_key.get(1), metadata_key.get(2), null, values);
            } 
          } 
        }

        Boolean is_discoverable = configurationService.getBooleanProperty("crosswalk.marc21.item.discoverable", false);
        if (!is_discoverable) {
            System.out.println("This item is not discoverable, check private items");
            item.setDiscoverable(false);
            Boolean send_mail = Boolean.valueOf(configurationService.getBooleanProperty("crosswalk.marc21.item.harvest.notification", true));
            if (send_mail){
                System.out.println("Harvest email send...");
                emailSuccessMail(item.getName(), item.getID());
            }
        }
        
    }


    /**
     * Helper method to escape all characters that are not part of the canon set
     *
     * @param sourceString source unescaped string
     */
    private String encodeForURL(String sourceString) {
        Character lowalpha[] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i',
                'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r',
                's', 't', 'u', 'v', 'w', 'x', 'y', 'z'};
        Character upalpha[] = {'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I',
                'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R',
                'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'};
        Character digit[] = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9'};
        Character mark[] = {'-', '_', '.', '!', '~', '*', '\'', '(', ')'};

        // reserved
        Character reserved[] = {';', '/', '?', ':', '@', '&', '=', '+', '$', ',', '%', '#'};

        Set<Character> URLcharsSet = new HashSet<Character>();
        URLcharsSet.addAll(Arrays.asList(lowalpha));
        URLcharsSet.addAll(Arrays.asList(upalpha));
        URLcharsSet.addAll(Arrays.asList(digit));
        URLcharsSet.addAll(Arrays.asList(mark));
        URLcharsSet.addAll(Arrays.asList(reserved));

        StringBuilder processedString = new StringBuilder();
        for (int i = 0; i < sourceString.length(); i++) {
            char ch = sourceString.charAt(i);
            if (URLcharsSet.contains(ch)) {
                processedString.append(ch);
            } else {
                processedString.append("%").append(Integer.toHexString((int) ch));
            }
        }

        return processedString.toString();
    }


    public ArrayList<String> get_metadata_schema(String metadata_string){
        ArrayList<String> metadata_array = new ArrayList<>(Arrays.asList(metadata_string.split("[.]")));
        if (metadata_array.size() != 3) {
            while (metadata_array.size() < 3){
                metadata_array.add(null);
            }
        }
        return metadata_array;
    }

    public List<String> get_compound_values(List<Element> metadata, String metadata_label){
        String[] label = metadata_label.split("-");
        String tag = label[0].trim();
        String code = label[1].trim();
        //System.out.println("Tag: "+ tag + "Code: " + code);
        List<String> values = new ArrayList<>();
        for (Element element: metadata) {
            if (tag.equals(element.getAttributeValue("tag"))){
                for (Object subelement: element.getChildren()) {
                    Element node = (Element) subelement;
                    if (node.getAttributeValue("code").equals(code)) {
                        values.add(node.getValue());
                    }
                }
            }
        }
        if (values.size() > 0) {
            return values;
        }
        return new ArrayList<>();
    }

    public List<String> get_custom_values(List<String> values, String command){
        //System.out.println(command.toLowerCase());
        if (command.toLowerCase().contains("divide")) {
            return divide_terms(values, command);
        }
        else if ( (command.toLowerCase().contains("mayus") || (command.toLowerCase().contains("minus")) )) {
            return capitalize(values, command);
        }
        else if ( (command.toLowerCase().contains("select") || (command.toLowerCase().contains("selectnr")) )){
            return select_substring(values, command);
        }
        else if(command.toLowerCase().contains("replace")){
            return replace_string(values, command);
        }
        else if(command.toLowerCase().contains("convert")){
            return convert_string(values, command);
        }
        else {
            return  values;
        }
    }

    public List<String> divide_terms(List<String> values, String command){
        String[] command_array = command.split("-");
        if (command_array.length != 3) {
            System.out.println("Command DIVIDE invalid, not have all arguments "+ command);
            return values;
        }
        String value_to_cut = command_array[1].trim();
        String value_to_save = command_array[2].trim();
        List<String> new_array_string = new ArrayList<>();
        for (String value: values) {
            String[] new_values_cut = value.split(value_to_cut, 2);
            if (new_values_cut.length == 2) {
                if (value_to_save.toLowerCase().equals("l")) {
                    new_array_string.add(new_values_cut[0]);
                }
                else if (value_to_save.toLowerCase().equals("r")) {
                    new_array_string.add(new_values_cut[1]);
                }
                else {
                    for (String value_cut: new_values_cut) {
                        new_array_string.add(value_cut);
                    }
                }
            }
            else {
                for (String value_cut: new_values_cut) {
                    new_array_string.add(value_cut);
                }
            }
        }
        //String[] return_values = new String[new_array_string.size()];
        //new_array_string.toArray(return_values);
        return new_array_string;
    }

    public List<String> capitalize(List<String> values, String command){
        String[] command_array = command.split("-");
        if (command_array.length != 1) {
            System.out.println("Command MAYUS | MINUS invalid, This command not have arguments "+ command);
            return values;
        }
        String convert_string = command_array[0].trim().toLowerCase();
        List<String> new_array_string = new ArrayList<>();
        for (String value: values) {
            if (convert_string.equals("mayus")) {
                new_array_string.add(value.toUpperCase());
            }
            else if(convert_string.equals("minus")){
                new_array_string.add((value.toLowerCase()));
            }
            else {
                new_array_string.add(value);
            }
        }
        return new_array_string;
    }

    public List<String> select_substring(List<String> values, String command){
        String[] commands_array = command.split(":-:");
        for (String single_command: commands_array) {
            String[] command_array = single_command.split("-");
            if (command_array.length != 2) {
                System.out.println("Command SELECT invalid, not have all arguments " + command);
                return values;
            }
            String select_option = command_array[0].toLowerCase().trim();
            List<String> array_return;
            if (select_option.equals("select")){
                array_return = select_substring(values, command_array[1].trim(), true);
            }
            else if (select_option.equals("selectnr")){
                array_return = select_substring(values, command_array[1].trim(), false);
            }
            else {
                array_return = new ArrayList<>();
            }
            if (array_return.size() != 0) {
                return array_return;
            }
        }
        return new ArrayList<>();
    }

    public List<String> select_substring(List<String> values, String select_string, Boolean replace){
        List<String> new_array_string = new ArrayList<>();
        for (String value: values) {
            String[] elements = value.split(",");
            for (String element: elements) {
                if(element.trim().startsWith(select_string)){
                    if (replace){
                        new_array_string.add(element.replace(select_string, "").trim());
                    }
                    else {
                        new_array_string.add(select_string.trim());
                    }
                }
            }
        }
        return new_array_string;
    }

    public List<String> replace_string(List<String> values, String command){
        String[] command_array = command.split("-");
        if (command_array.length != 3) {
            System.out.println("Command REPLACE invalid, not have all arguments "+ command);
            return values;
        }
        String string_to_replace = command_array[1].trim();
        if (string_to_replace.equals("[c]")){
            string_to_replace = ",";
        }
        String string_replace = command_array[2].trim();
        List<String> new_array_string = new ArrayList<>();
        for (String value: values) {
            if (string_replace.equals("[s]")){
                new_array_string.add(value.replaceAll(string_to_replace , " "));
            }
            else if(string_replace.equals("[d]")){
                new_array_string.add(value.replaceAll(string_to_replace , ""));
            }
            else {
                new_array_string.add(value.replaceAll(string_to_replace, string_replace));
            }
        }
        return new_array_string;
    }

    public List<String>  convert_string(List<String>  values, String command){
        String[] command_array = command.split("-");
        if((command_array.length == 2) || (command_array.length == 3)){
            String file_name = command_array[1];
            String default_value = ((command_array.length == 3) ? command_array[2] : null);
            List<String> file_values = get_file_lines(file_name);
            if (file_values.size() == 0){
                return values;
            }
            List<String> new_values = new ArrayList<>();
            for (String value: values) {
                String conversion = null;
                String conversion_key, conversion_value;
                for (String convert: file_values) {
                    conversion_key = convert.substring(0, convert.indexOf('-')).trim();
                    conversion_value = convert.substring(convert.indexOf('-')+1).trim();
                    //System.out.println("Valores de conversion en CONVERT: " + conversion_key.toLowerCase() + " " + value.toLowerCase());
                    if (conversion_key.toLowerCase().equals(value.toLowerCase())) {
                        conversion = conversion_value;
                        break;
                    }
                }
                if ((conversion == null) && (default_value == null)){
                    new_values.add(value);
                }
                else if ((conversion == null) && (default_value != null)){
                    new_values.add(default_value);
                }
                else {
                    new_values.add(conversion);
                }
            }
            return new_values;
        }
        System.out.println("Command CONVERT invalid, not have all arguments "+ command);
        return values;
    }

    public List<String> get_file_lines(String file_name){
        List<String> return_content = new ArrayList<>();
        try{
            String vocabularies_path = configurationService.getProperty("dspace.dir") + "/config/controlled-vocabularies/" + file_name.trim();
            BufferedReader reader = new BufferedReader(new FileReader(vocabularies_path));
            String line = reader.readLine();
            while (line != null) {
                return_content.add(line.trim());
                line = reader.readLine();
            }
        }catch (IOException e){
            System.out.println("No existe el archivo de configuración, se ponen los valores directamente");
            e.printStackTrace();
        }
        return return_content;
    }

    public List<String> get_single_values(List<Element> metadata, String metadata_label) {
        String[] label = metadata_label.split("-");
        String tag = label[0].trim();
        
        List<String> values = new ArrayList<>();
        for (Element element : metadata) {
          if (tag.equals(element.getAttributeValue("tag"))) {
            values.add(element.getValue());
          }
        } 
        return values;
    }

    public List<List<String>> separate_author_names(List<Element> metadata, String metadata_label) {
        String[] label = metadata_label.split("-");
        String tag = label[0].trim();
        String code = label[1].trim();
        List<String> e_values = new ArrayList<>();
        List<String> values = new ArrayList<>();
        for (Element element : metadata) {
          if (tag.equals(element.getAttributeValue("tag"))) {
            String string_value = null;
            Boolean is_e = Boolean.valueOf(false);
            for (Object subelement : element.getChildren()) {
              Element node = (Element)subelement;
              if (node.getAttributeValue("code").equals(code)) {
                string_value = node.getValue();
              }
              if (node.getAttributeValue("code").equals("e")) {
                is_e = Boolean.valueOf(true);
              }
            } 
            
            if (is_e.booleanValue()) {
              e_values.add(string_value);
              continue;
            } 
            values.add(string_value);
          } 
        } 
        List<List<String>> return_array = new ArrayList<List<String>>();
        return_array.add(e_values);
        return_array.add(values);
        return return_array;
    }


    public List<String> get_title_values(List<Element> metadata, String metadata_label) {
        String[] label = metadata_label.split("-");
        String tag = label[0].trim();
        String[] codes = label[1].trim().split(",");
        List<String> values = new ArrayList<>();
        for (Element element : metadata) {
          if (tag.equals(element.getAttributeValue("tag"))) {
            String value = "";
            for (int i = 0; i < codes.length; i++) {
              for (Object subelement : element.getChildren()) {
                Element node = (Element)subelement;
                if (node.getAttributeValue("code").equals(codes[i])) {
                  value = value + " " + node.getValue();
                }
              } 
            } 
            if (value.trim().length() > 0) {
              if (configurationService.getBooleanProperty("crosswalk.marc21.dc.title.clean", false)) {
                value = value.replaceAll("\\s+:\\s+", ": ");
              }
              values.add(value.trim());
            } 
          } 
        } 
        return values;
      }
    
    public void emailSuccessMail(String title, UUID item_id) {
        try {
            Email email = Email.getEmail(I18nUtil.getEmailFilename(I18nUtil.getDefaultLocale(), "submit_koha"));
            String[] recipients = configurationService.getArrayProperty("mail.harvest.koha");
            for (String recipient : recipients) {
                email.addRecipient(recipient);
            }
            email.addArgument(title);
            //email.addArgument(configurationService.getProperty("dspace.ui.url") + "/items/" + item_id.toString() + "/edit/status");
            email.addArgument(configurationService.getProperty("dspace.ui.url") + "/admin/search?f.discoverable=false,equals&spc.page=1&query=" + URLEncoder.encode(title.replace(":", " "), "UTF8"));
            email.send();
        } catch (Exception e) {
            log.info(e.getMessage());
        }
    }
}
