/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2015-8-29: 12h:45m
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

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"
/* external codes at top */
/* type definitions */
/* external typedefs */
/* assuming abstract types */
/* sum constructor declarations */
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_defined_1) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_undefined_2) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_maxlevel_3) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_opr_arglst_4) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPide_unbound_5) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPundef_6) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPlist_7) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPapp_fun_8) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_fun_9) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_opr_10) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_arity_11) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPfun_12) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPerr_13) ;

/* exn constructor declarations */
/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload () ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_defined_1.tag = 1 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_undefined_2.tag = 2 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_maxlevel_3.tag = 3 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_opr_arglst_4.tag = 4 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPide_unbound_5.tag = 5 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPundef_6.tag = 6 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPlist_7.tag = 7 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPapp_fun_8.tag = 8 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_fun_9.tag = 9 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_opr_10.tag = 10 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_arity_11.tag = 11 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPfun_12.tag = 12 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPerr_13.tag = 13 ;
return ;
} /* staload function */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_e1xpval_sats.c] */
