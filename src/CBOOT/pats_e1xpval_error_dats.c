/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2015-6-9: 20h:50m
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

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

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
typedef
struct {
ats_ptr_type atslab_3 ;
ats_ptr_type atslab_4 ;
} anairiats_rec_0 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_1 ;

typedef
struct {
ats_ptr_type atslab_e1xp_loc ;
ats_ptr_type atslab_e1xp_node ;
} anairiats_rec_2 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_3 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_4 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_5 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_nil_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__E1XPide_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_defined_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_valize_undefined_2) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_maxlevel_3) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_opr_arglst_4) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPide_unbound_5) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPundef_6) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPlist_7) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPapp_fun_8) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_fun_9) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_opr_10) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPappid_arity_11) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPfun_12) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__VE_E1XPerr_13) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_vbox_make_view_ptr) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_newline) (ats_ptr_type) ;
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
ATSextern_fun(ats_void_type, atspre_fprint_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_fprintf_exn) (ats_ptr_type, ats_ptr_type, ...) ;
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
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__fprint_symbol) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_valerr) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__the_valerrlst_get) () ;

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
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_ptr_type ref_01088_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_void_type loop_5 (ats_ptr_type arg0, ats_ptr_type arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp71) ;
ATSstatic (ats_ptr_type, statmp74) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_e1xpval_error.dats: 1566(line=48, offs=3) -- 4863(line=136, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_valerr (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;
// ATSlocal_void (tmp2) ;
ATSlocal (ats_ptr_type, tmp3) ;
// ATSlocal_void (tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
// ATSlocal_void (tmp6) ;
ATSlocal (ats_ptr_type, tmp7) ;
// ATSlocal_void (tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
// ATSlocal_void (tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
// ATSlocal_void (tmp12) ;
ATSlocal (ats_int_type, tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
// ATSlocal_void (tmp15) ;
ATSlocal (ats_ptr_type, tmp16) ;
// ATSlocal_void (tmp17) ;
ATSlocal (ats_ptr_type, tmp18) ;
ATSlocal (ats_ptr_type, tmp19) ;
// ATSlocal_void (tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
// ATSlocal_void (tmp22) ;
// ATSlocal_void (tmp23) ;
// ATSlocal_void (tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
// ATSlocal_void (tmp29) ;
// ATSlocal_void (tmp30) ;
// ATSlocal_void (tmp31) ;
// ATSlocal_void (tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
// ATSlocal_void (tmp34) ;
ATSlocal (ats_ptr_type, tmp35) ;
// ATSlocal_void (tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
// ATSlocal_void (tmp38) ;
ATSlocal (ats_ptr_type, tmp39) ;
// ATSlocal_void (tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
// ATSlocal_void (tmp42) ;
ATSlocal (ats_ptr_type, tmp43) ;
// ATSlocal_void (tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
// ATSlocal_void (tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
// ATSlocal_void (tmp49) ;
// ATSlocal_void (tmp50) ;
// ATSlocal_void (tmp51) ;
ATSlocal (ats_ptr_type, tmp52) ;
ATSlocal (ats_ptr_type, tmp53) ;
// ATSlocal_void (tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;
// ATSlocal_void (tmp56) ;
// ATSlocal_void (tmp57) ;
// ATSlocal_void (tmp58) ;
ATSlocal (ats_ptr_type, tmp59) ;
// ATSlocal_void (tmp60) ;
ATSlocal (ats_ptr_type, tmp61) ;
// ATSlocal_void (tmp62) ;
ATSlocal (ats_ptr_type, tmp63) ;
// ATSlocal_void (tmp64) ;
ATSlocal (ats_ptr_type, tmp65) ;
// ATSlocal_void (tmp66) ;
ATSlocal (ats_ptr_type, tmp67) ;
// ATSlocal_void (tmp68) ;
ATSlocal (ats_ptr_type, tmp69) ;
// ATSlocal_void (tmp70) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_valerr:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (((ats_sum_ptr_type)arg1)->tag != 0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp1 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp3 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp1), atslab_e1xp_loc) ;
/* tmp2 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp3) ;
/* tmp4 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the expression cannot be evaluated to a value.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (((ats_sum_ptr_type)arg1)->tag != 1) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp5 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp7 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp5), atslab_e1xp_loc) ;
/* tmp6 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp7) ;
/* tmp8 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the expression is expected to be an indentifer.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)arg1)->tag != 2) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp9 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp11 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp9), atslab_e1xp_loc) ;
/* tmp10 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp11) ;
/* tmp12 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the expression is expected to be an indentifer.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (((ats_sum_ptr_type)arg1)->tag != 3) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp13 = ats_caselptrlab_mac(anairiats_sum_3, arg1, atslab_0) ;
tmp14 = ats_caselptrlab_mac(anairiats_sum_3, arg1, atslab_1) ;
tmp16 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp14), atslab_e1xp_loc) ;
/* tmp15 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp16) ;
/* tmp17 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(1): the maximal evaluation depth (%i) has been reached."), tmp13) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)arg1)->tag != 4) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
tmp18 = ats_caselptrlab_mac(anairiats_sum_4, arg1, atslab_0) ;
tmp19 = ats_caselptrlab_mac(anairiats_sum_4, arg1, atslab_1) ;
tmp21 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp18), atslab_e1xp_loc) ;
/* tmp20 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp21) ;
/* tmp22 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the operator [")) ;
/* tmp23 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__fprint_symbol (arg0, tmp19) ;
/* tmp24 = */ atspre_fprint_string (arg0, ATSstrcst("] cannot handle its argument(s).")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (((ats_sum_ptr_type)arg1)->tag != 5) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
tmp25 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp26 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp25), atslab_e1xp_loc) ;
tmp27 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp25), atslab_e1xp_node) ;
if (((ats_sum_ptr_type)tmp27)->tag != 0) { ats_caseof_failure_handle ("/home/hwxi/research/Postiats/git/src/pats_e1xpval_error.dats: 2825(line=84, offs=9) -- 2852(line=84, offs=36)") ; }
tmp28 = ats_caselptrlab_mac(anairiats_sum_1, tmp27, atslab_0) ;
/* tmp29 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp26) ;
/* tmp30 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the identifier [")) ;
/* tmp31 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__fprint_symbol (arg0, tmp28) ;
/* tmp32 = */ atspre_fprint_string (arg0, ATSstrcst("] is unbound.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (((ats_sum_ptr_type)arg1)->tag != 6) { goto __ats_lab_7_0 ; }
__ats_lab_6_1:
tmp33 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp35 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp33), atslab_e1xp_loc) ;
/* tmp34 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp35) ;
/* tmp36 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the expression cannot be evaluated as it is un-defined.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
if (((ats_sum_ptr_type)arg1)->tag != 7) { goto __ats_lab_8_0 ; }
__ats_lab_7_1:
tmp37 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp39 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp37), atslab_e1xp_loc) ;
/* tmp38 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp39) ;
/* tmp40 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the expression cannot be evaluated as it is a tuple.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)arg1)->tag != 8) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
tmp41 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp43 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp41), atslab_e1xp_loc) ;
/* tmp42 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp43) ;
/* tmp44 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the applied expression is required to be an identifier.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
if (((ats_sum_ptr_type)arg1)->tag != 9) { goto __ats_lab_10_0 ; }
__ats_lab_9_1:
tmp45 = ats_caselptrlab_mac(anairiats_sum_4, arg1, atslab_0) ;
tmp46 = ats_caselptrlab_mac(anairiats_sum_4, arg1, atslab_1) ;
tmp48 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp45), atslab_e1xp_loc) ;
/* tmp47 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp48) ;
/* tmp49 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the applied identifier [")) ;
/* tmp50 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__fprint_symbol (arg0, tmp46) ;
/* tmp51 = */ atspre_fprint_string (arg0, ATSstrcst("] does not refer to a function.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
if (((ats_sum_ptr_type)arg1)->tag != 10) { goto __ats_lab_11_0 ; }
__ats_lab_10_1:
tmp52 = ats_caselptrlab_mac(anairiats_sum_4, arg1, atslab_0) ;
tmp53 = ats_caselptrlab_mac(anairiats_sum_4, arg1, atslab_1) ;
tmp55 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp52), atslab_e1xp_loc) ;
/* tmp54 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp55) ;
/* tmp56 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the applied identifier [")) ;
/* tmp57 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__fprint_symbol (arg0, tmp53) ;
/* tmp58 = */ atspre_fprint_string (arg0, ATSstrcst("] does not refer to a supported operator.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
if (((ats_sum_ptr_type)arg1)->tag != 11) { goto __ats_lab_12_0 ; }
__ats_lab_11_1:
tmp59 = ats_caselptrlab_mac(anairiats_sum_4, arg1, atslab_0) ;
tmp61 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp59), atslab_e1xp_loc) ;
/* tmp60 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp61) ;
/* tmp62 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): arity mismatch for this function application.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_12 */
__ats_lab_12_0:
if (((ats_sum_ptr_type)arg1)->tag != 12) { goto __ats_lab_13_0 ; }
__ats_lab_12_1:
tmp63 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp65 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp63), atslab_e1xp_loc) ;
/* tmp64 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp65) ;
/* tmp66 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the expression cannot be evaluated as it is a function.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
// if (((ats_sum_ptr_type)arg1)->tag != 13) { ats_deadcode_failure_handle () ; }
__ats_lab_13_1:
tmp67 = ats_caselptrlab_mac(anairiats_sum_1, arg1, atslab_0) ;
tmp69 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_2, tmp67), atslab_e1xp_loc) ;
/* tmp68 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (arg0, tmp69) ;
/* tmp70 = */ atspre_fprint_string (arg0, ATSstrcst(": error(1): the expression cannot be evaluated as it indicates an error.")) ;
/* tmp0 = */ atspre_fprint_newline (arg0) ;
break ;
} while (0) ;
return /* (tmp0) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_valerr] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/reference.dats: 1828(line=57, offs=18) -- 1902(line=59, offs=4)
*/
ATSstaticdec()
ats_ptr_type
ref_01088_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp72) ;
ATSlocal (ats_ptr_type, tmp73) ;

__ats_lab_ref_01088_ats_ptr_type:
/* ats_ptr_type tmp73 ; */
tmp73 = arg0 ;
tmp72 = atspre_ref_make_elt_tsz ((&tmp73), sizeof(ats_ptr_type)) ;
return (tmp72) ;
} /* end of [ref_01088_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_e1xpval_error.dats: 5135(line=154, offs=3) -- 5250(line=158, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__the_valerrlst_add (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp75) ;
ATSlocal (ats_ptr_type, tmp76) ;
ATSlocal (ats_ptr_type, tmp77) ;
ATSlocal (ats_ptr_type, tmp78) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__the_valerrlst_add:
tmp76 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp71), atslab_1) ;
tmp78 = ats_ptrget_mac(ats_ptr_type, tmp76) ;
tmp77 = ATS_MALLOC(sizeof(anairiats_sum_5)) ;
ats_selptrset_mac(anairiats_sum_5, tmp77, atslab_0, arg0) ;
ats_selptrset_mac(anairiats_sum_5, tmp77, atslab_1, tmp78) ;
ats_ptrget_mac(ats_ptr_type, tmp76) = tmp77 ;
return /* (tmp75) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__the_valerrlst_add] */

/*
// /home/hwxi/research/Postiats/git/src/pats_e1xpval_error.dats: 5312(line=162, offs=3) -- 5434(line=167, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__the_valerrlst_get () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp79) ;
ATSlocal (ats_ptr_type, tmp80) ;
ATSlocal (ats_ptr_type, tmp81) ;
ATSlocal (ats_ptr_type, tmp82) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__the_valerrlst_get:
tmp80 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp71), atslab_1) ;
tmp81 = ats_ptrget_mac(ats_ptr_type, tmp80) ;
tmp82 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, tmp80) = tmp82 ;
tmp79 = tmp81 ;
return (tmp79) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__the_valerrlst_get] */

/*
// /home/hwxi/research/Postiats/git/src/pats_e1xpval_error.dats: 5593(line=177, offs=7) -- 5804(line=184, offs=28)
*/
ATSstaticdec()
ats_void_type
loop_5 (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp85) ;
ATSlocal (ats_ptr_type, tmp86) ;
ATSlocal (ats_ptr_type, tmp87) ;
// ATSlocal_void (tmp88) ;

__ats_lab_loop_5:
do {
/* branch: __ats_lab_14 */
__ats_lab_14_0:
if (arg1 == (ats_sum_ptr_type)0) { goto __ats_lab_15_0 ; }
__ats_lab_14_1:
tmp86 = ats_caselptrlab_mac(anairiats_sum_5, arg1, atslab_0) ;
tmp87 = ats_caselptrlab_mac(anairiats_sum_5, arg1, atslab_1) ;
ATS_FREE(arg1) ;
/* tmp88 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_valerr (arg0, tmp86) ;
arg0 = arg0 ;
arg1 = tmp87 ;
goto __ats_lab_loop_5 ; // tail call
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
// if (arg1 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_15_1:
break ;
} while (0) ;
return /* (tmp85) */ ;
} /* end of [loop_5] */

/*
// /home/hwxi/research/Postiats/git/src/pats_e1xpval_error.dats: 5543(line=175, offs=3) -- 5847(line=188, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_the_valerrlst (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp83) ;
ATSlocal (ats_ptr_type, tmp84) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_the_valerrlst:
tmp84 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__the_valerrlst_get () ;
/* tmp83 = */ loop_5 (arg0, tmp84) ;
return /* (tmp83) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__fprint_the_valerrlst] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__staload_flag = 1 ;

// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_e1xpval_error_2edats__staload () ;

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
ATS_GC_MARKROOT(&statmp71, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp74, sizeof(ats_ptr_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
statmp74 = (ats_sum_ptr_type)0 ;
statmp71 = ref_01088_ats_ptr_type (statmp74) ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_e1xpval_error_dats.c] */
