/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2014-1-15: 21h:57m
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

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"
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
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_rec_2 ;

typedef struct {
anairiats_rec_2 atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_3 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_vt_0) ;

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
ats_void_type loop_2 (ats_ptr_type arg0) ;
static
ats_void_type list_vt_free_01498_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_void_type fenvlst_vt_free_0 (ats_ptr_type arg0) ;
static
ats_void_type fenvlstlst_vt_free_3 (ats_ptr_type arg0) ;
static
ats_ptr_type ref_01087_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_ptr_type auxlst_7 (ats_clo_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_ptr_type auxlstlst_8 (ats_clo_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_void_type loop_13 (ats_ref_type arg0, ats_ptr_type arg1) ;
static
ats_ptr_type list_vt_append_01503_ats_ptr_type (ats_ptr_type arg0, ats_ptr_type arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp8) ;
ATSstatic (ats_ptr_type, statmp11) ;
ATSstatic (ats_ptr_type, statmp12) ;
ATSstatic (ats_ptr_type, statmp13) ;
ATSstatic (ats_ptr_type, statmp14) ;
ATSstatic (ats_ptr_type, statmp15) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/list_vt.dats: 4893(line=177, offs=7) -- 5015(line=178, offs=73)
*/
ATSstaticdec()
ats_void_type
loop_2 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp2) ;
ATSlocal (ats_ptr_type, tmp3) ;

__ats_lab_loop_2:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp3 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_1) ;
ATS_FREE(arg0) ;
arg0 = tmp3 ;
goto __ats_lab_loop_2 ; // tail call
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_1_1:
break ;
} while (0) ;
return /* (tmp2) */ ;
} /* end of [loop_2] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/list_vt.dats: 4875(line=176, offs=14) -- 5054(line=182, offs=4)
*/
ATSstaticdec()
ats_void_type
list_vt_free_01498_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp1) ;

__ats_lab_list_vt_free_01498_ats_ptr_type:
/* tmp1 = */ loop_2 (arg0) ;
return /* (tmp1) */ ;
} /* end of [list_vt_free_01498_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 1691(line=56, offs=4) -- 1753(line=57, offs=47)
*/
ATSstaticdec()
ats_void_type
fenvlst_vt_free_0 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp0) ;

__ats_lab_fenvlst_vt_free_0:
/* tmp0 = */ list_vt_free_01498_ats_ptr_type (arg0) ;
return /* (tmp0) */ ;
} /* end of [fenvlst_vt_free_0] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 1758(line=58, offs=5) -- 2007(line=64, offs=26)
*/
ATSstaticdec()
ats_void_type
fenvlstlst_vt_free_3 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_ptr_type, tmp6) ;
// ATSlocal_void (tmp7) ;

__ats_lab_fenvlstlst_vt_free_3:
do {
/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp5 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_0) ;
tmp6 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_1) ;
ATS_FREE(arg0) ;
/* tmp7 = */ fenvlst_vt_free_0 (tmp5) ;
arg0 = tmp6 ;
goto __ats_lab_fenvlstlst_vt_free_3 ; // tail call
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_3_1:
break ;
} while (0) ;
return /* (tmp4) */ ;
} /* end of [fenvlstlst_vt_free_3] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/reference.dats: 1828(line=57, offs=18) -- 1902(line=59, offs=4)
*/
ATSstaticdec()
ats_ptr_type
ref_01087_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;

__ats_lab_ref_01087_ats_ptr_type:
/* ats_ptr_type tmp10 ; */
tmp10 = arg0 ;
tmp9 = atspre_ref_make_elt_tsz ((&tmp10), sizeof(ats_ptr_type)) ;
return (tmp9) ;
} /* end of [ref_01087_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 2272(line=79, offs=3) -- 2403(line=84, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_add (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp16) ;
ATSlocal (ats_ptr_type, tmp17) ;
ATSlocal (ats_ptr_type, tmp18) ;
ATSlocal (ats_ptr_type, tmp19) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_add:
tmp17 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp8), atslab_1) ;
tmp19 = ats_ptrget_mac(ats_ptr_type, tmp17) ;
tmp18 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
ats_selptrset_mac(anairiats_sum_1, tmp18, atslab_0, arg0) ;
ats_selptrset_mac(anairiats_sum_1, tmp18, atslab_1, tmp19) ;
ats_ptrget_mac(ats_ptr_type, tmp17) = tmp18 ;
return /* (tmp16) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_add] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 2566(line=93, offs=7) -- 2819(line=100, offs=32)
*/
ATSstaticdec()
ats_ptr_type
auxlst_7 (ats_clo_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_ptr_type, tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;

__ats_lab_auxlst_7:
do {
/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (arg1 == (ats_sum_ptr_type)0) { goto __ats_lab_7_0 ; }
__ats_lab_4_1:
tmp22 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp23 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_1) ;
tmp24 = ((ats_ptr_type(*)(ats_clo_ptr_type, ats_ptr_type))(ats_closure_fun(arg0))) (arg0, tmp22) ;
do {
/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (tmp24 != (ats_sum_ptr_type)0) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
arg0 = arg0 ;
arg1 = tmp23 ;
goto __ats_lab_auxlst_7 ; // tail call
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
__ats_lab_6_1:
tmp21 = tmp24 ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
// if (arg1 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_7_1:
tmp21 = (ats_sum_ptr_type)0 ;
break ;
} while (0) ;
return (tmp21) ;
} /* end of [auxlst_7] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 2874(line=103, offs=7) -- 3159(line=111, offs=32)
*/
ATSstaticdec()
ats_ptr_type
auxlstlst_8 (ats_clo_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;

__ats_lab_auxlstlst_8:
do {
/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (arg1 == (ats_sum_ptr_type)0) { goto __ats_lab_11_0 ; }
__ats_lab_8_1:
tmp26 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp27 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_1) ;
tmp28 = auxlst_7 (arg0, tmp26) ;
do {
/* branch: __ats_lab_9 */
__ats_lab_9_0:
if (tmp28 != (ats_sum_ptr_type)0) { goto __ats_lab_10_0 ; }
__ats_lab_9_1:
arg0 = arg0 ;
arg1 = tmp27 ;
goto __ats_lab_auxlstlst_8 ; // tail call
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
__ats_lab_10_1:
tmp25 = tmp28 ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
// if (arg1 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_11_1:
tmp25 = (ats_sum_ptr_type)0 ;
break ;
} while (0) ;
return (tmp25) ;
} /* end of [auxlstlst_8] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 2472(line=88, offs=7) -- 3565(line=126, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_search (ats_clo_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_search:
tmp30 = ats_ptrget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, statmp8)) ;
tmp29 = auxlst_7 (arg0, tmp30) ;
do {
/* branch: __ats_lab_12 */
__ats_lab_12_0:
if (tmp29 != (ats_sum_ptr_type)0) { goto __ats_lab_13_0 ; }
__ats_lab_12_1:
tmp31 = ats_ptrget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, statmp12)) ;
tmp20 = auxlstlst_8 (arg0, tmp31) ;
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
__ats_lab_13_1:
tmp20 = tmp29 ;
break ;
} while (0) ;
return (tmp20) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_search] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 3649(line=131, offs=19) -- 3976(line=145, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_pop () {
/* local vardec */
// ATSlocal_void (tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;
ATSlocal (ats_ptr_type, tmp35) ;
ATSlocal (ats_ptr_type, tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_pop:
tmp33 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp12), atslab_1) ;
tmp34 = ats_ptrget_mac(ats_ptr_type, tmp33) ;
if (tmp34 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_namespace.dats: 3746(line=134, offs=9) -- 3774(line=134, offs=37)") ; }
tmp35 = ats_caselptrlab_mac(anairiats_sum_1, tmp34, atslab_0) ;
tmp36 = ats_caselptrlab_mac(anairiats_sum_1, tmp34, atslab_1) ;
ATS_FREE(tmp34) ;
ats_ptrget_mac(ats_ptr_type, tmp33) = tmp36 ;
tmp37 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp8), atslab_1) ;
tmp38 = ats_ptrget_mac(ats_ptr_type, tmp37) ;
ats_ptrget_mac(ats_ptr_type, tmp37) = tmp35 ;
/* tmp32 = */ fenvlst_vt_free_0 (tmp38) ;
return /* (tmp32) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_pop] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 4037(line=148, offs=20) -- 4337(line=160, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_push () {
/* local vardec */
// ATSlocal_void (tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
ATSlocal (ats_ptr_type, tmp43) ;
ATSlocal (ats_ptr_type, tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_push:
tmp40 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp8), atslab_1) ;
tmp41 = ats_ptrget_mac(ats_ptr_type, tmp40) ;
tmp42 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, tmp40) = tmp42 ;
tmp43 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp12), atslab_1) ;
tmp45 = ats_ptrget_mac(ats_ptr_type, tmp43) ;
tmp44 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
ats_selptrset_mac(anairiats_sum_1, tmp44, atslab_0, tmp41) ;
ats_selptrset_mac(anairiats_sum_1, tmp44, atslab_1, tmp45) ;
ats_ptrget_mac(ats_ptr_type, tmp43) = tmp44 ;
return /* (tmp39) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_push] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/list_vt.dats: 6702(line=253, offs=5) -- 6923(line=259, offs=4)
*/
ATSstaticdec()
ats_void_type
loop_13 (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp58) ;
ATSlocal (ats_ptr_type, tmp59) ;

__ats_lab_loop_13:
do {
/* branch: __ats_lab_14 */
__ats_lab_14_0:
if (ats_ptrget_mac(ats_ptr_type, arg0) == (ats_sum_ptr_type)0) { goto __ats_lab_15_0 ; }
__ats_lab_14_1:
tmp59 = &ats_caselptrlab_mac(anairiats_sum_1, ats_ptrget_mac(ats_ptr_type, arg0), atslab_1) ;
arg0 = tmp59 ;
arg1 = arg1 ;
goto __ats_lab_loop_13 ; // tail call
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
// if (ats_ptrget_mac(ats_ptr_type, arg0) != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_15_1:
ats_ptrget_mac(ats_ptr_type, arg0) = arg1 ;
break ;
} while (0) ;
return /* (tmp58) */ ;
} /* end of [loop_13] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/list_vt.dats: 6567(line=247, offs=16) -- 6970(line=262, offs=4)
*/
ATSstaticdec()
ats_ptr_type
list_vt_append_01503_ats_ptr_type (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp56) ;
ATSlocal (ats_ptr_type, tmp57) ;
// ATSlocal_void (tmp60) ;

__ats_lab_list_vt_append_01503_ats_ptr_type:
/* ats_ptr_type tmp57 ; */
tmp57 = arg0 ;
/* tmp60 = */ loop_13 ((&tmp57), arg1) ;
tmp56 = tmp57 ;
return (tmp56) ;
} /* end of [list_vt_append_01503_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 4425(line=165, offs=25) -- 4831(line=179, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_localjoin () {
/* local vardec */
// ATSlocal_void (tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
ATSlocal (ats_ptr_type, tmp49) ;
ATSlocal (ats_ptr_type, tmp50) ;
// ATSlocal_void (tmp51) ;
ATSlocal (ats_ptr_type, tmp52) ;
ATSlocal (ats_ptr_type, tmp53) ;
ATSlocal (ats_ptr_type, tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;
ATSlocal (ats_ptr_type, tmp61) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_localjoin:
tmp47 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp12), atslab_1) ;
tmp48 = ats_ptrget_mac(ats_ptr_type, tmp47) ;
if (tmp48 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_namespace.dats: 4524(line=168, offs=9) -- 4553(line=168, offs=38)") ; }
tmp49 = ats_caselptrlab_mac(anairiats_sum_1, tmp48, atslab_0) ;
tmp50 = ats_caselptrlab_mac(anairiats_sum_1, tmp48, atslab_1) ;
ATS_FREE(tmp48) ;
/* tmp51 = */ fenvlst_vt_free_0 (tmp49) ;
if (tmp50 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_namespace.dats: 4597(line=170, offs=9) -- 4627(line=170, offs=39)") ; }
tmp52 = ats_caselptrlab_mac(anairiats_sum_1, tmp50, atslab_0) ;
tmp53 = ats_caselptrlab_mac(anairiats_sum_1, tmp50, atslab_1) ;
ATS_FREE(tmp50) ;
ats_ptrget_mac(ats_ptr_type, tmp47) = tmp53 ;
tmp54 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp8), atslab_1) ;
tmp61 = ats_ptrget_mac(ats_ptr_type, tmp54) ;
tmp55 = list_vt_append_01503_ats_ptr_type (tmp61, tmp52) ;
ats_ptrget_mac(ats_ptr_type, tmp54) = tmp55 ;
return /* (tmp46) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_localjoin] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 4919(line=184, offs=20) -- 5393(line=201, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_save () {
/* local vardec */
// ATSlocal_void (tmp62) ;
ATSlocal (ats_ptr_type, tmp63) ;
ATSlocal (ats_ptr_type, tmp64) ;
ATSlocal (ats_ptr_type, tmp65) ;
ATSlocal (ats_ptr_type, tmp66) ;
ATSlocal (ats_ptr_type, tmp67) ;
ATSlocal (ats_ptr_type, tmp68) ;
ATSlocal (ats_ptr_type, tmp69) ;
ATSlocal (ats_ptr_type, tmp70) ;
ATSlocal (anairiats_rec_2, tmp71) ;
ATSlocal (ats_ptr_type, tmp72) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_save:
tmp63 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp8), atslab_1) ;
tmp64 = ats_ptrget_mac(ats_ptr_type, tmp63) ;
tmp65 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, tmp63) = tmp65 ;
tmp66 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp12), atslab_1) ;
tmp67 = ats_ptrget_mac(ats_ptr_type, tmp66) ;
tmp68 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, tmp66) = tmp68 ;
tmp69 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp14), atslab_1) ;
tmp71.atslab_0 = tmp64 ;
tmp71.atslab_1 = tmp67 ;

tmp72 = ats_ptrget_mac(ats_ptr_type, tmp69) ;
tmp70 = ATS_MALLOC(sizeof(anairiats_sum_3)) ;
ats_selptrset_mac(anairiats_sum_3, tmp70, atslab_0, tmp71) ;
ats_selptrset_mac(anairiats_sum_3, tmp70, atslab_1, tmp72) ;
ats_ptrget_mac(ats_ptr_type, tmp69) = tmp70 ;
return /* (tmp62) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_save] */

/*
// /home/hwxi/research/Postiats/git/src/pats_namespace.dats: 5460(line=205, offs=3) -- 5956(line=231, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_restore () {
/* local vardec */
// ATSlocal_void (tmp73) ;
ATSlocal (ats_ptr_type, tmp74) ;
ATSlocal (ats_ptr_type, tmp75) ;
ATSlocal (anairiats_rec_2, tmp76) ;
ATSlocal (ats_ptr_type, tmp77) ;
ATSlocal (ats_ptr_type, tmp78) ;
// ATSlocal_void (tmp79) ;
ATSlocal (ats_ptr_type, tmp80) ;
ATSlocal (ats_ptr_type, tmp81) ;
ATSlocal (ats_ptr_type, tmp82) ;
// ATSlocal_void (tmp83) ;
ATSlocal (ats_ptr_type, tmp84) ;
ATSlocal (ats_ptr_type, tmp85) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_restore:
tmp74 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp14), atslab_1) ;
tmp75 = ats_ptrget_mac(ats_ptr_type, tmp74) ;
if (tmp75 == (ats_sum_ptr_type)0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_namespace.dats: 5565(line=211, offs=7) -- 5591(line=211, offs=33)") ; }
tmp76 = ats_caselptrlab_mac(anairiats_sum_3, tmp75, atslab_0) ;
tmp77 = ats_caselptrlab_mac(anairiats_sum_3, tmp75, atslab_1) ;
ATS_FREE(tmp75) ;
ats_ptrget_mac(ats_ptr_type, tmp74) = tmp77 ;
tmp78 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp8), atslab_1) ;
tmp80 = ats_ptrget_mac(ats_ptr_type, tmp78) ;
/* tmp79 = */ fenvlst_vt_free_0 (tmp80) ;
tmp81 = ats_select_mac(tmp76, atslab_0) ;
ats_ptrget_mac(ats_ptr_type, tmp78) = tmp81 ;
tmp82 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp12), atslab_1) ;
tmp84 = ats_ptrget_mac(ats_ptr_type, tmp82) ;
/* tmp83 = */ fenvlstlst_vt_free_3 (tmp84) ;
tmp85 = ats_select_mac(tmp76, atslab_1) ;
ats_ptrget_mac(ats_ptr_type, tmp82) = tmp85 ;
return /* (tmp73) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__the_namespace_restore] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__staload_flag = 1 ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_namespace_2edats__staload () ;

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
ATS_GC_MARKROOT(&statmp8, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp11, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp12, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp13, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp14, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp15, sizeof(ats_ptr_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
statmp11 = (ats_sum_ptr_type)0 ;
statmp8 = ref_01087_ats_ptr_type (statmp11) ;
statmp13 = (ats_sum_ptr_type)0 ;
statmp12 = ref_01087_ats_ptr_type (statmp13) ;
statmp15 = (ats_sum_ptr_type)0 ;
statmp14 = ref_01087_ats_ptr_type (statmp15) ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_namespace_dats.c] */
