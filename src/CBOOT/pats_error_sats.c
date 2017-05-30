/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2017-5-22:  9h:52m
**
*/

/* include some .h files */
#ifndef _ATS_HEADER_NONE
#include "ats_config.h"
#include "ats_basics.h"
#include "ats_types.h"
#include "ats_exception.h"
#include "ats_memory.h"
#endif /* _ATS_HEADER_NONE */

/* prologues from statically loaded files */
/* external codes at top */
/* type definitions */
/* external typedefs */
/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn) ;
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn_interr) ;
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FILENONE_EXN) ;
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FIXITY_EXN) ;
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS1_EXN) ;
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS2_EXN) ;
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS3_EXN) ;
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS4_EXN) ;

/* static load function */

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__staload_flag = 1 ;

_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn" ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn_interr.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn_interr.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__FatalErrorExn_interr" ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FILENONE_EXN.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FILENONE_EXN.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FILENONE_EXN" ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FIXITY_EXN.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FIXITY_EXN.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_FIXITY_EXN" ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS1_EXN.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS1_EXN.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS1_EXN" ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS2_EXN.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS2_EXN.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS2_EXN" ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS3_EXN.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS3_EXN.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS3_EXN" ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS4_EXN.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS4_EXN.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_error_2esats__PATSOPT_TRANS4_EXN" ;
return ;
} /* staload function */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_error_sats.c] */
