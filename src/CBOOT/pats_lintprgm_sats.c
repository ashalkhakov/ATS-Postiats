/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2014-2-16: 16h:44m
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

#include "libc/CATS/gmp.cats"
/* external codes at top */
/* type definitions */
/* external typedefs */
/* assuming abstract types */
/* sum constructor declarations */
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__ICvec_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__ICveclst_1) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__ICerr_2) ;

/* exn constructor declarations */
/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload () ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__ICvec_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__ICveclst_1.tag = 1 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__ICerr_2.tag = 2 ;
return ;
} /* staload function */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_lintprgm_sats.c] */
