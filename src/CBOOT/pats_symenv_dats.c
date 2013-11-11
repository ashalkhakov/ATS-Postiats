/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2013-11-10: 21h:24m
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

typedef
struct {
ats_ptr_type atslab_map ;
ats_ptr_type atslab_maplst ;
ats_ptr_type atslab_savedlst ;
ats_ptr_type atslab_pervasive ;
} anairiats_rec_2 ;

typedef
struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_rec_3 ;

typedef struct {
anairiats_rec_3 atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_4 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_vt_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__Some_vt_1) ;

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
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_make_nil) () ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_free) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_search) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_insert) (ats_ref_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_joinwth) (ats_ref_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__fprint_symmap) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop) (ats_ref_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push) (ats_ref_type, ats_ptr_type) ;

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
int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__sasp__symenv_vt0ype = 0 ;

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_void_type symmaplst_free_0 (ats_ptr_type arg0) ;
static
ats_ptr_type symmaplst_search_1 (ats_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_ptr_type ptr_alloc_01069_anairiats_rec_2 () ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 1696(line=56, offs=1) -- 1884(line=62, offs=26)
*/
ATSstaticdec()
ats_void_type
symmaplst_free_0 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;
ATSlocal (ats_ptr_type, tmp2) ;
// ATSlocal_void (tmp3) ;

__ats_lab_symmaplst_free_0:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp1 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_0) ;
tmp2 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_1) ;
ATS_FREE(arg0) ;
/* tmp3 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_free (tmp1) ;
arg0 = tmp2 ;
goto __ats_lab_symmaplst_free_0 ; // tail call
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_1_1:
break ;
} while (0) ;
return /* (tmp0) */ ;
} /* end of [symmaplst_free_0] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 1917(line=66, offs=1) -- 2497(line=84, offs=4)
*/
ATSstaticdec()
ats_ptr_type
symmaplst_search_1 (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_ptr_type, tmp6) ;
ATSlocal (ats_ptr_type, tmp7) ;
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;

__ats_lab_symmaplst_search_1:
do {
/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_5_0 ; }
__ats_lab_2_1:
tmp5 = &ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_0) ;
tmp6 = &ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_1) ;
tmp8 = ats_ptrget_mac(ats_ptr_type, tmp5) ;
tmp7 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_search (tmp8, arg1) ;
do {
/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (tmp7 == (ats_sum_ptr_type)0) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp4 = tmp7 ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
// if (tmp7 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_4_1:
tmp10 = ats_ptrget_mac(ats_ptr_type, tmp6) ;
tmp9 = symmaplst_search_1 (tmp10, arg1) ;
tmp4 = tmp9 ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_5_1:
tmp4 = (ats_sum_ptr_type)0 ;
break ;
} while (0) ;
return (tmp4) ;
} /* end of [symmaplst_search_1] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/pointer.dats: 1817(line=56, offs=24) -- 1850(line=56, offs=57)
*/
ATSstaticdec()
ats_ptr_type
ptr_alloc_01069_anairiats_rec_2 () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp13) ;

__ats_lab_ptr_alloc_01069_anairiats_rec_2:
tmp13 = atspre_ptr_alloc_tsz (sizeof(anairiats_rec_2)) ;
return (tmp13) ;
} /* end of [ptr_alloc_01069_anairiats_rec_2] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 2793(line=101, offs=9) -- 3087(line=111, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_make_nil () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;
ATSlocal (ats_ptr_type, tmp16) ;
ATSlocal (ats_ptr_type, tmp17) ;
ATSlocal (ats_ptr_type, tmp18) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_make_nil:
tmp12 = ptr_alloc_01069_anairiats_rec_2 () ;
tmp14 = ats_selsin_mac(tmp12, atslab_2) ;
tmp15 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_make_nil () ;
ats_selptr_mac(ats_castptr_mac(anairiats_rec_2, tmp14), atslab_map) = tmp15 ;
tmp16 = (ats_sum_ptr_type)0 ;
ats_selptr_mac(ats_castptr_mac(anairiats_rec_2, tmp14), atslab_maplst) = tmp16 ;
tmp17 = (ats_sum_ptr_type)0 ;
ats_selptr_mac(ats_castptr_mac(anairiats_rec_2, tmp14), atslab_savedlst) = tmp17 ;
tmp18 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_make_nil () ;
ats_selptr_mac(ats_castptr_mac(anairiats_rec_2, tmp14), atslab_pervasive) = tmp18 ;
tmp11 = tmp14 ;
return (tmp11) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_make_nil] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 3171(line=117, offs=9) -- 3334(line=123, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_search (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp19) ;
ATSlocal (ats_ptr_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_ptr_type, tmp22) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_search:
tmp21 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) ;
tmp20 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_search (tmp21, arg1) ;
do {
/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (tmp20 == (ats_sum_ptr_type)0) { goto __ats_lab_7_0 ; }
__ats_lab_6_1:
tmp19 = tmp20 ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
// if (tmp20 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_7_1:
tmp22 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) ;
tmp19 = symmaplst_search_1 (tmp22, arg1) ;
break ;
} while (0) ;
return (tmp19) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_search] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 3415(line=129, offs=3) -- 3464(line=129, offs=52)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_insert (ats_ref_type arg0, ats_ptr_type arg1, ats_ptr_type arg2) {
/* local vardec */
// ATSlocal_void (tmp23) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_insert:
/* tmp23 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_insert (&ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map), arg1, arg2) ;
return /* (tmp23) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_insert] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 3536(line=136, offs=3) -- 3680(line=141, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop:
tmp25 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) ;
tmp26 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) ;
if (tmp26 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_symenv.dats: 3584(line=138, offs=7) -- 3622(line=138, offs=45)") ; }
tmp27 = ats_caselptrlab_mac(anairiats_sum_1, tmp26, atslab_0) ;
tmp28 = ats_caselptrlab_mac(anairiats_sum_1, tmp26, atslab_1) ;
ATS_FREE(tmp26) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) = tmp27 ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) = tmp28 ;
tmp24 = tmp25 ;
return (tmp24) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 3733(line=145, offs=3) -- 3811(line=148, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop_free (ats_ref_type arg0) {
/* local vardec */
// ATSlocal_void (tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop_free:
tmp30 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop (arg0) ;
/* tmp29 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_free (tmp30) ;
return /* (tmp29) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pop_free] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 3865(line=152, offs=3) -- 3978(line=155, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push:
tmp33 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) ;
tmp34 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) ;
tmp32 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
ats_selptrset_mac(anairiats_sum_1, tmp32, atslab_0, tmp33) ;
ats_selptrset_mac(anairiats_sum_1, tmp32, atslab_1, tmp34) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) = tmp32 ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) = arg1 ;
return /* (tmp31) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 4032(line=159, offs=3) -- 4117(line=162, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push_nil (ats_ref_type arg0) {
/* local vardec */
// ATSlocal_void (tmp35) ;
ATSlocal (ats_ptr_type, tmp36) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push_nil:
tmp36 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_make_nil () ;
/* tmp35 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push (arg0, tmp36) ;
return /* (tmp35) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_push_nil] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 4201(line=168, offs=9) -- 4417(line=176, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_savecur (ats_ref_type arg0) {
/* local vardec */
// ATSlocal_void (tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;
ATSlocal (ats_ptr_type, tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
ATSlocal (anairiats_rec_3, tmp43) ;
ATSlocal (ats_ptr_type, tmp44) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_savecur:
tmp38 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) ;
tmp39 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_make_nil () ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) = tmp39 ;
tmp40 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) ;
tmp41 = (ats_sum_ptr_type)0 ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) = tmp41 ;
tmp43.atslab_0 = tmp38 ;
tmp43.atslab_1 = tmp40 ;

tmp44 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_savedlst) ;
tmp42 = ATS_MALLOC(sizeof(anairiats_sum_4)) ;
ats_selptrset_mac(anairiats_sum_4, tmp42, atslab_0, tmp43) ;
ats_selptrset_mac(anairiats_sum_4, tmp42, atslab_1, tmp44) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_savedlst) = tmp42 ;
return /* (tmp37) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_savecur] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 4479(line=180, offs=9) -- 4721(line=189, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_restore (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
// ATSlocal_void (tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
ATSlocal (ats_ptr_type, tmp49) ;
ATSlocal (anairiats_rec_3, tmp50) ;
ATSlocal (ats_ptr_type, tmp51) ;
ATSlocal (ats_ptr_type, tmp52) ;
ATSlocal (ats_ptr_type, tmp53) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_restore:
tmp46 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) ;
tmp48 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) ;
/* tmp47 = */ symmaplst_free_0 (tmp48) ;
tmp49 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_savedlst) ;
if (tmp49 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_symenv.dats: 4589(line=184, offs=7) -- 4625(line=184, offs=43)") ; }
tmp50 = ats_caselptrlab_mac(anairiats_sum_4, tmp49, atslab_0) ;
tmp51 = ats_caselptrlab_mac(anairiats_sum_4, tmp49, atslab_1) ;
ATS_FREE(tmp49) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_savedlst) = tmp51 ;
tmp52 = ats_select_mac(tmp50, atslab_0) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) = tmp52 ;
tmp53 = ats_select_mac(tmp50, atslab_1) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) = tmp53 ;
tmp45 = tmp46 ;
return (tmp45) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_restore] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 4806(line=195, offs=9) -- 5219(line=214, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_localjoin (ats_ref_type arg0) {
/* local vardec */
// ATSlocal_void (tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;
ATSlocal (ats_ptr_type, tmp56) ;
ATSlocal (ats_ptr_type, tmp57) ;
// ATSlocal_void (tmp58) ;
ATSlocal (ats_ptr_type, tmp59) ;
ATSlocal (ats_ptr_type, tmp60) ;
ATSlocal (ats_ptr_type, tmp61) ;
// ATSlocal_void (tmp62) ;
// ATSlocal_void (tmp63) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_localjoin:
tmp55 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) ;
if (tmp55 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_symenv.dats: 4845(line=198, offs=5) -- 4872(line=198, offs=32)") ; }
tmp56 = ats_caselptrlab_mac(anairiats_sum_1, tmp55, atslab_0) ;
tmp57 = ats_caselptrlab_mac(anairiats_sum_1, tmp55, atslab_1) ;
ATS_FREE(tmp55) ;
/* tmp58 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_free (tmp56) ;
if (tmp57 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_symenv.dats: 4903(line=200, offs=5) -- 4930(line=200, offs=32)") ; }
tmp59 = ats_caselptrlab_mac(anairiats_sum_1, tmp57, atslab_0) ;
tmp60 = ats_caselptrlab_mac(anairiats_sum_1, tmp57, atslab_1) ;
ATS_FREE(tmp57) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_maplst) = tmp60 ;
tmp61 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) ;
ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map) = tmp59 ;
/* tmp62 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_joinwth (&ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_map), tmp61) ;
/* tmp63 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_free (tmp61) ;
/* tmp54 = tmp62 */ ;
return /* (tmp54) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_localjoin] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 5313(line=220, offs=9) -- 5356(line=220, offs=52)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_search (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp64) ;
ATSlocal (ats_ptr_type, tmp65) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_search:
tmp65 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_pervasive) ;
tmp64 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_search (tmp65, arg1) ;
return (tmp64) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_search] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 5436(line=225, offs=3) -- 5491(line=225, offs=58)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_insert (ats_ref_type arg0, ats_ptr_type arg1, ats_ptr_type arg2) {
/* local vardec */
// ATSlocal_void (tmp66) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_insert:
/* tmp66 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_insert (&ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_pervasive), arg1, arg2) ;
return /* (tmp66) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_insert] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 5584(line=232, offs=9) -- 5678(line=238, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_joinwth0 (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp67) ;
// ATSlocal_void (tmp68) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_joinwth0:
/* tmp68 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_joinwth (&ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_pervasive), arg1) ;
/* tmp67 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_free (arg1) ;
return /* (tmp67) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_joinwth0] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 5762(line=242, offs=9) -- 5810(line=242, offs=57)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_joinwth1 (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp69) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_joinwth1:
/* tmp69 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__symmap_joinwth (&ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg0), atslab_pervasive), arg1) ;
return /* (tmp69) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__symenv_pervasive_joinwth1] */

/*
// /home/hwxi/research/Postiats/git/src/pats_symenv.dats: 5901(line=249, offs=3) -- 5948(line=249, offs=50)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__fprint_symenv_map (ats_ptr_type arg0, ats_ref_type arg1, ats_ptr_type arg2) {
/* local vardec */
// ATSlocal_void (tmp70) ;
ATSlocal (ats_ptr_type, tmp71) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__fprint_symenv_map:
tmp71 = ats_select_mac(ats_ptrget_mac(anairiats_rec_2, arg1), atslab_map) ;
/* tmp70 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__fprint_symmap (arg0, tmp71, arg2) ;
return /* (tmp70) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__fprint_symenv_map] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__staload_flag = 1 ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symmap_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symenv_2edats__staload () ;

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

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_symenv_dats.c] */
