/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2018-1-11: 12h:39m
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
/* external codes at top */
/* type definitions */
typedef
struct {
ats_ptr_type atslab_3 ;
ats_ptr_type atslab_4 ;
} anairiats_rec_0 ;

/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_vbox_make_view_ptr) (ats_ptr_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_neq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_compare_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_int) (ats_ptr_type, ats_int_type) ;
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
ATSextern_fun(ats_ptr_type, atspre_tostringf) (ats_ptr_type, ...) ;
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

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____copy_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____free_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__sasp__counter_type = 0 ;
int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__sasp__count_t0ype = 0 ;

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_ptr_type ref_01088_ats_int_type (ats_int_type arg0) ;
static
ats_ptr_type ref_make_elt_01089_ats_int_type (ats_int_type arg0) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 1613(line=50, offs=25) -- 1620(line=50, offs=32)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__count_get_int (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp0) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__count_get_int:
tmp0 = arg0 ;
return (tmp0) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__count_get_int] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 1668(line=55, offs=16) -- 1698(line=55, offs=46)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__lt_count_count (ats_int_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp1) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__lt_count_count:
tmp1 = atspre_lt_int_int (arg0, arg1) ;
return (tmp1) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__lt_count_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 1725(line=57, offs=17) -- 1756(line=57, offs=48)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__lte_count_count (ats_int_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp2) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__lte_count_count:
tmp2 = atspre_lte_int_int (arg0, arg1) ;
return (tmp2) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__lte_count_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 1783(line=60, offs=16) -- 1813(line=60, offs=46)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__gt_count_count (ats_int_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp3) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__gt_count_count:
tmp3 = atspre_gt_int_int (arg0, arg1) ;
return (tmp3) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__gt_count_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 1840(line=62, offs=17) -- 1871(line=62, offs=48)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__gte_count_count (ats_int_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp4) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__gte_count_count:
tmp4 = atspre_gte_int_int (arg0, arg1) ;
return (tmp4) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__gte_count_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 1898(line=65, offs=16) -- 1928(line=65, offs=46)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__eq_count_count (ats_int_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp5) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__eq_count_count:
tmp5 = atspre_eq_int_int (arg0, arg1) ;
return (tmp5) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__eq_count_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 1955(line=67, offs=17) -- 1986(line=67, offs=48)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__neq_count_count (ats_int_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_bool_type, tmp6) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__neq_count_count:
tmp6 = atspre_neq_int_int (arg0, arg1) ;
return (tmp6) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__neq_count_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2018(line=70, offs=21) -- 2053(line=70, offs=56)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__compare_count_count (ats_int_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp7) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__compare_count_count:
tmp7 = atspre_compare_int_int (arg0, arg1) ;
return (tmp7) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__compare_count_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2099(line=75, offs=14) -- 2129(line=75, offs=44)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__fprint_count (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
// ATSlocal_void (tmp8) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__fprint_count:
/* tmp8 = */ atspre_fprint_int (arg0, arg1) ;
return /* (tmp8) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__fprint_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2177(line=80, offs=16) -- 2253(line=82, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__tostring_count (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__tostring_count:
tmp10 = atspre_tostringf (ATSstrcst("%i"), arg0) ;
tmp9 = ats_castfn_mac(ats_ptr_type, tmp10) ;
return (tmp9) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__tostring_count] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2314(line=85, offs=23) -- 2401(line=87, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__tostring_prefix_count (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__tostring_prefix_count:
tmp12 = atspre_tostringf (ATSstrcst("%s%i"), arg0, arg1) ;
tmp11 = ats_castfn_mac(ats_ptr_type, tmp12) ;
return (tmp11) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__tostring_prefix_count] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/reference.dats: 1828(line=57, offs=18) -- 1902(line=59, offs=4)
*/
ATSstaticdec()
ats_ptr_type
ref_01088_ats_int_type (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp15) ;
ATSlocal (ats_int_type, tmp16) ;

__ats_lab_ref_01088_ats_int_type:
/* ats_int_type tmp16 ; */
tmp16 = arg0 ;
tmp15 = atspre_ref_make_elt_tsz ((&tmp16), sizeof(ats_int_type)) ;
return (tmp15) ;
} /* end of [ref_01088_ats_int_type] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/reference.dats: 1994(line=62, offs=27) -- 2009(line=62, offs=42)
*/
ATSstaticdec()
ats_ptr_type
ref_make_elt_01089_ats_int_type (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp14) ;

__ats_lab_ref_make_elt_01089_ats_int_type:
tmp14 = ref_01088_ats_int_type (arg0) ;
return (tmp14) ;
} /* end of [ref_make_elt_01089_ats_int_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2483(line=92, offs=14) -- 2510(line=92, offs=41)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_make () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp13) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_make:
tmp13 = ref_make_elt_01089_ats_int_type (0) ;
return (tmp13) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_make] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2537(line=95, offs=13) -- 2564(line=95, offs=40)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_inc (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp17) ;
ATSlocal (ats_int_type, tmp18) ;
ATSlocal (ats_int_type, tmp19) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_inc:
tmp19 = ats_ptrget_mac(ats_int_type, arg0) ;
tmp18 = atspre_add_int_int (tmp19, 1) ;
ats_ptrget_mac(ats_int_type, arg0) = tmp18 ;
return /* (tmp17) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_inc] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2587(line=96, offs=23) -- 2601(line=96, offs=37)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_get (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp20) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_get:
tmp20 = ats_ptrget_mac(ats_int_type, arg0) ;
return (tmp20) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_get] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2624(line=97, offs=23) -- 2650(line=97, offs=49)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_set (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
// ATSlocal_void (tmp21) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_set:
ats_ptrget_mac(ats_int_type, arg0) = arg1 ;
return /* (tmp21) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_set] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2675(line=98, offs=25) -- 2694(line=98, offs=44)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_reset (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp22) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_reset:
ats_ptrget_mac(ats_int_type, arg0) = 0 ;
return /* (tmp22) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_reset] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2725(line=102, offs=3) -- 2787(line=104, offs=2)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_getinc (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp23) ;
ATSlocal (ats_int_type, tmp24) ;
ATSlocal (ats_int_type, tmp25) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_getinc:
tmp24 = ats_ptrget_mac(ats_int_type, arg0) ;
tmp25 = atspre_add_int_int (tmp24, 1) ;
ats_ptrget_mac(ats_int_type, arg0) = tmp25 ;
tmp23 = tmp24 ;
return (tmp23) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_getinc] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_counter.dats: 2845(line=108, offs=3) -- 2909(line=110, offs=2)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_incget (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp26) ;
ATSlocal (ats_int_type, tmp27) ;
ATSlocal (ats_int_type, tmp28) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_incget:
tmp28 = ats_ptrget_mac(ats_int_type, arg0) ;
tmp27 = atspre_add_int_int (tmp28, 1) ;
ats_ptrget_mac(ats_int_type, arg0) = tmp27 ;
tmp26 = tmp27 ;
return (tmp26) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__counter_incget] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__staload_flag = 1 ;

// _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_counter_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
ATS_2d0_2e2_2e12_2prelude_2SATS_2list_2esats__list_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2SATS_2list_vt_2esats__list_vt_length_is_nonnegative_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2SATS_2array_2esats__array_v_takeout2_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2list_vt_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____copy_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____free_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2array_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_counter_dats.c] */
