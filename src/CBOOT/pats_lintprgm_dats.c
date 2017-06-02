/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2017-6-2: 14h:15m
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

/* include some .cats files */
#ifndef _ATS_PRELUDE_NONE
#include "prelude/CATS/basics.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/integer_ptr.cats"
#include "prelude/CATS/integer_fixed.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/string.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/lazy.cats"
#include "prelude/CATS/lazy_vt.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/list.cats"
#include "prelude/CATS/option.cats"
#include "prelude/CATS/array.cats"
#include "prelude/CATS/matrix.cats"
#endif /* _ATS_PRELUDE_NONE */
/* prologues from statically loaded files */

#include "pats_location.cats"
/* external codes at top */
/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_assert_errmsg) (ats_bool_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_string_append) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_neq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_ineg) (ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_isub) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_igt) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_ieq) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_ineq) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_size1_of_int1) (ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvec0_free) (ats_ptr_type, ats_int_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvecout_addback_prfck () ;
extern
ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvecout0_addback_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
ATSglobal(ats_exn_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__Finished) ;

/* global dynamic (non-functional) constant declarations */
/* internal function declarations */

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lintprgm.dats: 3379(line=122, offs=10) -- 3643(line=131, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvec0_free (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
// ATSlocal_void (tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvec0_free:
tmp1 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, arg0), atslab_2) ;
/* tmp0 = */ atspre_array_ptr_free (tmp1) ;
return /* (tmp0) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvec0_free] */

/* static load function */

// extern ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2unsafe_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_utils_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__staload_flag = 1 ;

// ATS_2d0_2e2_2e12_2prelude_2SATS_2unsafe_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_utils_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__staload () ;

_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__Finished.tag = ats_exception_con_tag_new () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__Finished.name = "_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__Finished" ;
return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvecout_addback_prfck () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lintprgm_2esats__myintvecout0_addback_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_lintprgm_dats.c] */
