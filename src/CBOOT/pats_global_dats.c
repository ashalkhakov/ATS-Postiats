/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2014-5-4: 23h: 4m
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
#include "prelude/CATS/bool.cats"
#include "prelude/CATS/char.cats"
#include "prelude/CATS/byte.cats"
#include "prelude/CATS/float.cats"
#include "prelude/CATS/integer.cats"
#include "prelude/CATS/integer_ptr.cats"
#include "prelude/CATS/integer_fixed.cats"
#include "prelude/CATS/sizetype.cats"
#include "prelude/CATS/pointer.cats"
#include "prelude/CATS/reference.cats"
#include "prelude/CATS/string.cats"
#include "prelude/CATS/lazy.cats"
#include "prelude/CATS/lazy_vt.cats"
#include "prelude/CATS/printf.cats"
#include "prelude/CATS/list.cats"
#include "prelude/CATS/option.cats"
#include "prelude/CATS/array.cats"
#include "prelude/CATS/matrix.cats"
#endif /* _ATS_PRELUDE_NONE */
/* prologues from statically loaded files */
/* external codes at top */
/* type definitions */
typedef
struct {
ats_ptr_type atslab_3 ;
ats_ptr_type atslab_4 ;
} anairiats_rec_0 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_1 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_nil_1) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_vbox_make_view_ptr) (ats_ptr_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_isucc) (ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_iadd) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_isub) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_idiv) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_ilt) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_igt) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_igte) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_size1_of_int1) (ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_add_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_sub_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_mul2_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_neq_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atspre_ptr_alloc_tsz) (ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_ptr_zero_tsz) (ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atspre_ref_make_elt_tsz) (ats_ref_type, ats_size_type) ;
ATSextern_val(ats_ptr_type, atspre_stropt_none) ;
ATSextern_fun(ats_ptr_type, ListSubscriptException_make) () ;
ATSextern_fun(ats_ptr_type, atspre_array_ptr_alloc_tsz) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_initialize_funenv_tsz) (ats_ref_type, ats_size_type, ats_ptr_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_initialize_cloenv_tsz) (ats_ref_type, ats_size_type, ats_ref_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_array_ptr_split_tsz) (ats_ptr_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atspre_array_ptr_takeout_tsz) (ats_ptr_type, ats_size_type, ats_size_type) ;
ATSextern_fun(anairiats_rec_0, atspre_array_ptr_takeout2_tsz) (ats_ptr_type, ats_size_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_foreach_funenv_tsz) (ats_ref_type, ats_ptr_type, ats_size_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_iforeach_funenv_tsz) (ats_ref_type, ats_ptr_type, ats_size_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_array2_ptr_takeout_tsz) (ats_ptr_type, ats_size_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atslib_qsort) (ats_ref_type, ats_size_type, ats_size_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set) (ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____copy_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____free_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_ptr_type ref_01087_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_ptr_type ref_01087_ats_int_type (ats_int_type arg0) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp0) ;
ATSstatic (ats_ptr_type, statmp7) ;
ATSstatic (ats_ptr_type, statmp10) ;
ATSstatic (ats_ptr_type, statmp16) ;
ATSstatic (ats_ptr_type, statmp17) ;
ATSstatic (ats_ptr_type, statmp22) ;
ATSstatic (ats_ptr_type, statmp25) ;
ATSstatic (ats_ptr_type, statmp26) ;
ATSstatic (ats_ptr_type, statmp31) ;
ATSstatic (ats_ptr_type, statmp34) ;
ATSstatic (ats_ptr_type, statmp37) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/reference.dats: 1828(line=57, offs=18) -- 1902(line=59, offs=4)
*/
ATSstaticdec()
ats_ptr_type
ref_01087_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp1) ;
ATSlocal (ats_ptr_type, tmp2) ;

__ats_lab_ref_01087_ats_ptr_type:
/* ats_ptr_type tmp2 ; */
tmp2 = arg0 ;
tmp1 = atspre_ref_make_elt_tsz ((&tmp2), sizeof(ats_ptr_type)) ;
return (tmp1) ;
} /* end of [ref_01087_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 1666(line=55, offs=28) -- 1684(line=55, offs=46)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_get () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp3) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_get:
tmp3 = ats_ptrget_mac(ats_ptr_type, statmp0) ;
return (tmp3) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 1713(line=58, offs=18) -- 1741(line=58, offs=46)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp4) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set:
ats_ptrget_mac(ats_ptr_type, statmp0) = arg0 ;
return /* (tmp4) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 1800(line=64, offs=3) -- 1840(line=64, offs=43)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set_name (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp5) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set_name:
/* tmp5 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set (ats_castfn_mac(ats_ptr_type, arg0)) ;
return /* (tmp5) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set_name] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 1906(line=68, offs=3) -- 1948(line=68, offs=45)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set_none () {
/* local vardec */
// ATSlocal_void (tmp6) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set_none:
/* tmp6 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set (atspre_stropt_none) ;
return /* (tmp6) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PACKNAME_set_none] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/reference.dats: 1828(line=57, offs=18) -- 1902(line=59, offs=4)
*/
ATSstaticdec()
ats_ptr_type
ref_01087_ats_int_type (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_int_type, tmp9) ;

__ats_lab_ref_01087_ats_int_type:
/* ats_int_type tmp9 ; */
tmp9 = arg0 ;
tmp8 = atspre_ref_make_elt_tsz ((&tmp9), sizeof(ats_int_type)) ;
return (tmp8) ;
} /* end of [ref_01087_ats_int_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2141(line=81, offs=18) -- 2159(line=81, offs=36)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_get () {
/* local vardec */
ATSlocal (ats_int_type, tmp11) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_get:
tmp11 = ats_ptrget_mac(ats_int_type, statmp7) ;
return (tmp11) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2187(line=83, offs=18) -- 2217(line=83, offs=48)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_set (ats_int_type arg0) {
/* local vardec */
// ATSlocal_void (tmp12) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_set:
ats_ptrget_mac(ats_int_type, statmp7) = arg0 ;
return /* (tmp12) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_set] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2253(line=86, offs=23) -- 2349(line=89, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_get_decl () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_get_decl:
tmp14 = ats_ptrget_mac(ats_ptr_type, statmp10) ;
ats_ptrget_mac(ats_ptr_type, statmp10) = atspre_null_ptr ;
tmp13 = tmp14 ;
return (tmp13) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_get_decl] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2416(line=91, offs=23) -- 2449(line=91, offs=56)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_set_decl (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp15) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_set_decl:
ats_ptrget_mac(ats_ptr_type, statmp10) = arg0 ;
return /* (tmp15) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_PKGRELOC_set_decl] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2629(line=104, offs=31) -- 2650(line=104, offs=52)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_STALOADFLAG_get () {
/* local vardec */
ATSlocal (ats_int_type, tmp18) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_STALOADFLAG_get:
tmp18 = ats_ptrget_mac(ats_int_type, statmp16) ;
return (tmp18) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_STALOADFLAG_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2681(line=105, offs=31) -- 2714(line=105, offs=64)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_STALOADFLAG_set (ats_int_type arg0) {
/* local vardec */
// ATSlocal_void (tmp19) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_STALOADFLAG_set:
ats_ptrget_mac(ats_int_type, statmp16) = arg0 ;
return /* (tmp19) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_STALOADFLAG_set] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2746(line=107, offs=31) -- 2767(line=107, offs=52)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DYNLOADFLAG_get () {
/* local vardec */
ATSlocal (ats_int_type, tmp20) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DYNLOADFLAG_get:
tmp20 = ats_ptrget_mac(ats_int_type, statmp17) ;
return (tmp20) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DYNLOADFLAG_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2798(line=108, offs=31) -- 2831(line=108, offs=64)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DYNLOADFLAG_set (ats_int_type arg0) {
/* local vardec */
// ATSlocal_void (tmp21) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DYNLOADFLAG_set:
ats_ptrget_mac(ats_int_type, statmp17) = arg0 ;
return /* (tmp21) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DYNLOADFLAG_set] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 2974(line=120, offs=31) -- 2995(line=120, offs=52)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_MAINATSFLAG_get () {
/* local vardec */
ATSlocal (ats_int_type, tmp23) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_MAINATSFLAG_get:
tmp23 = ats_ptrget_mac(ats_int_type, statmp22) ;
return (tmp23) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_MAINATSFLAG_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 3026(line=121, offs=31) -- 3059(line=121, offs=64)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_MAINATSFLAG_set (ats_int_type arg0) {
/* local vardec */
// ATSlocal_void (tmp24) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_MAINATSFLAG_set:
ats_ptrget_mac(ats_int_type, statmp22) = arg0 ;
return /* (tmp24) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_MAINATSFLAG_set] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 3244(line=136, offs=21) -- 3265(line=136, offs=42)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_get () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp27) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_get:
tmp27 = ats_ptrget_mac(ats_ptr_type, statmp25) ;
return (tmp27) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 3301(line=140, offs=3) -- 3393(line=144, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_ppush (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_ppush:
tmp29 = ats_ptrget_mac(ats_ptr_type, statmp25) ;
tmp30 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
ats_selptrset_mac(anairiats_sum_1, tmp30, atslab_0, arg0) ;
ats_selptrset_mac(anairiats_sum_1, tmp30, atslab_1, tmp29) ;
ats_ptrget_mac(ats_ptr_type, statmp25) = tmp30 ;
return /* (tmp28) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_ppush] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 3565(line=157, offs=26) -- 3579(line=157, offs=40)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgflag_get () {
/* local vardec */
ATSlocal (ats_int_type, tmp32) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgflag_get:
tmp32 = ats_ptrget_mac(ats_int_type, statmp31) ;
return (tmp32) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgflag_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 3615(line=159, offs=26) -- 3641(line=159, offs=52)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgflag_set (ats_int_type arg0) {
/* local vardec */
// ATSlocal_void (tmp33) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgflag_set:
ats_ptrget_mac(ats_int_type, statmp31) = arg0 ;
return /* (tmp33) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgflag_set] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 3779(line=172, offs=26) -- 3793(line=172, offs=40)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgline_get () {
/* local vardec */
ATSlocal (ats_int_type, tmp35) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgline_get:
tmp35 = ats_ptrget_mac(ats_int_type, statmp34) ;
return (tmp35) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgline_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 3829(line=174, offs=26) -- 3855(line=174, offs=52)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgline_set (ats_int_type arg0) {
/* local vardec */
// ATSlocal_void (tmp36) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgline_set:
ats_ptrget_mac(ats_int_type, statmp34) = arg0 ;
return /* (tmp36) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_DEBUGATS_dbgline_set] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 4029(line=187, offs=33) -- 4050(line=187, offs=54)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_CCOMPENV_maxtmprecdepth_get () {
/* local vardec */
ATSlocal (ats_int_type, tmp38) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_CCOMPENV_maxtmprecdepth_get:
tmp38 = ats_ptrget_mac(ats_int_type, statmp37) ;
return (tmp38) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_CCOMPENV_maxtmprecdepth_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_global.dats: 4093(line=189, offs=33) -- 4124(line=189, offs=64)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_CCOMPENV_maxtmprecdepth_set (ats_int_type arg0) {
/* local vardec */
// ATSlocal_void (tmp39) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_CCOMPENV_maxtmprecdepth_set:
ats_ptrget_mac(ats_int_type, statmp37) = arg0 ;
return /* (tmp39) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_CCOMPENV_maxtmprecdepth_set] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__staload_flag = 1 ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
ATS_2d0_2e2_2e11_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____copy_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____free_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */
ATS_GC_MARKROOT(&statmp0, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp7, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp10, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp16, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp17, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp22, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp25, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp26, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp31, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp34, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp37, sizeof(ats_ptr_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
statmp0 = ref_01087_ats_ptr_type (atspre_stropt_none) ;
statmp7 = ref_01087_ats_int_type (0) ;
statmp10 = ref_01087_ats_ptr_type (atspre_null_ptr) ;
statmp16 = ref_01087_ats_int_type (1) ;
statmp17 = ref_01087_ats_int_type (1) ;
statmp22 = ref_01087_ats_int_type (0) ;
statmp26 = (ats_sum_ptr_type)0 ;
statmp25 = ref_01087_ats_ptr_type (statmp26) ;
statmp31 = ref_01087_ats_int_type (0) ;
statmp34 = ref_01087_ats_int_type (0) ;
statmp37 = ref_01087_ats_int_type (100) ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_global_dats.c] */
