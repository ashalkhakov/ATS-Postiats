/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2015-4-27: 10h:34m
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

#include "pats_location.cats"
/* external codes at top */
/* type definitions */
/* external typedefs */
/* assuming abstract types */
/* sum constructor declarations */
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONnul_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONint_1) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONintinf_2) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONbool_3) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONfloat_4) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONstring_5) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONlocation_6) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONfilename_7) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONlist_8) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONlablist_9) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONoption_10) ;

/* exn constructor declarations */
/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_stamp_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_label_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_stamp_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_label_2esats__staload () ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONnul_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONint_1.tag = 1 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONintinf_2.tag = 2 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONbool_3.tag = 3 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONfloat_4.tag = 4 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONstring_5.tag = 5 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONlocation_6.tag = 6 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONfilename_7.tag = 7 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONlist_8.tag = 8 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONlablist_9.tag = 9 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_jsonize_2esats__JSONoption_10.tag = 10 ;
return ;
} /* staload function */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_jsonize_sats.c] */
