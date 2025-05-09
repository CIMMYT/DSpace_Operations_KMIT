/**
 * The contents of this file are subject to the license and copyright
 * detailed in the LICENSE and NOTICE files at the root of the source
 * tree and available online at
 *
 * http://www.dspace.org/license/
 */
package org.dspace.checker.dao;

import java.sql.SQLException;
import java.time.Instant;
import java.util.List;

import org.dspace.checker.ChecksumResultCode;
import org.dspace.checker.MostRecentChecksum;
import org.dspace.content.Bitstream;
import org.dspace.core.Context;
import org.dspace.core.GenericDAO;

/**
 * Database Access Object interface class for the MostRecentChecksum object.
 * The implementation of this class is responsible for all database calls for the MostRecentChecksum object and is
 * autowired by spring
 * This class should only be accessed from a single service and should never be exposed outside of the API
 *
 * @author kevinvandevelde at atmire.com
 */
public interface MostRecentChecksumDAO extends GenericDAO<MostRecentChecksum> {

    public List<MostRecentChecksum> findByNotProcessedInDateRange(Context context, Instant startDate, Instant endDate)
        throws SQLException;

    public List<MostRecentChecksum> findByResultTypeInDateRange(Context context, Instant startDate, Instant endDate,
                                                                ChecksumResultCode resultCode) throws SQLException;

    public void deleteByBitstream(Context context, Bitstream bitstream) throws SQLException;

    public MostRecentChecksum getOldestRecord(Context context) throws SQLException;

    public MostRecentChecksum getOldestRecord(Context context, Instant lessThanDate) throws SQLException;

    public List<MostRecentChecksum> findNotInHistory(Context context) throws SQLException;

    public MostRecentChecksum findByBitstream(Context context, Bitstream bitstream) throws SQLException;
}
