/*
 * gw/box-dlr.h
 *
 * Opensmppbox additions of delivery report (DLR) handling
 *
 * Aarno Syvanen <aarno@alisanus.com> 12.1 2012
 */

#ifndef BOX_DLR_H
#define BOX_DLR_H 1

#include "gwlib/gwlib.h"
#include "gw/msg.h"

/*
 * Iniatilizing box dlr storage additions. This function MUST 
 * be called before calling any other functions of this module
 */
void box_dlr_init(Cfg* cfg);

/*
 * Releasing memory used for dlr stoage addition. This MUST
 * be called when the user of the module is going down.
 
void box_dlr_shutdown(void);

/*
 * Adding DLR with id to storage, if delivery reports are 
 * requested 
 */
void box_dlr_add(const Octstr *smsc, const Octstr *ts, Msg *msg);

/*
 * Adding DLR with id to storage in all cases
 */
void msg_add(const Octstr *smsc, const Octstr *ts, Msg *msg);

/*
 * Return Msg* if dlr entry found in DB, otherwise NULL,
 * using msg id as key.
 * NOTE: msg is not removed. This function is used to
 * fetch data from dlr table. If usesmppid flag is set,
 * only first 8 characters are meaningful.
 */
Msg *dlr_find_by_id(const Octstr *id, int usesmppid);

#endif
