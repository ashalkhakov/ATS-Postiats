/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2013-12-30: 20h:47m
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

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

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
ats_ptr_type atslab_hisexp_name ;
ats_ptr_type atslab_hisexp_node ;
} anairiats_rec_0 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
ats_ptr_type atslab_2 ;
} anairiats_sum_1 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_2 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_3 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_4 ;

typedef struct {
int tag ;
ats_int_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_5 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
ats_ptr_type atslab_2 ;
} anairiats_sum_6 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_nil_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSLABELED_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtybox_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyabs_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEfun_2) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEcfun_3) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEcst_4) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEapp_5) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEextype_6) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSErefarg_7) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyarr_8) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyrec_9) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyrecsin_10) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtysum_11) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEtyvar_12) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEvararg_13) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__HSEs2exp_14) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_bool_type, atspre_lt_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_neq_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_char_isdigit) (ats_char_type) ;
ATSextern_fun(ats_char_type, atspre_char_toupper) (ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_int) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_uint_type, atspre_add_uint_uint) (ats_uint_type, ats_uint_type) ;
ATSextern_fun(ats_bool_type, atspre_igte) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_llint_type, atspre_llint_of_int) (ats_int_type) ;
ATSextern_fun(ats_llint_type, atspre_mul_llint_llint) (ats_llint_type, ats_llint_type) ;
ATSextern_fun(ats_size_type, atspre_sub_size_size) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_size_size) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_size_type, atspre_size1_of_int1) (ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_add_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_sub_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_size_type, atspre_sub_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_size_type, atspre_mul_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_size_type, atspre_mul2_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_size1_int1) (ats_size_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, ats_malloc_gc) (ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_bytes_strbuf_trans) (ats_ptr_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_string_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_char_type, atspre_string_get_char_at) (ats_ptr_type, ats_size_type) ;
ATSextern_fun(ats_char_type, atspre_string_get_char_at__intsz) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_string_contains) (ats_ptr_type, ats_char_type) ;
ATSextern_fun(ats_size_type, atspre_string_length) (ats_ptr_type) ;
ATSextern_fun(ats_size_type, atspre_string_length) (ats_ptr_type) ;
ATSextern_fun(ats_bool_type, atspre_string_isnot_empty) (ats_ptr_type) ;
ATSextern_fun(ats_bool_type, atspre_string_isnot_atend) (ats_ptr_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_stropt_is_some) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_strptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_tostringf) (ats_ptr_type, ...) ;
ATSextern_fun(ats_ptr_type, atspre_array_ptr_alloc_tsz) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_array_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, patsopt_file2strptr) (ats_int_type) ;
ATSextern_fun(ats_size_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_cap) (ats_ref_type) ;
ATSextern_fun(ats_size_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_size) (ats_ref_type) ;
ATSextern_fun(ats_bool_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_is_empty) (ats_ref_type) ;
ATSextern_fun(ats_bool_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_isnot_empty) (ats_ref_type) ;
ATSextern_fun(ats_bool_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_is_full) (ats_ref_type) ;
ATSextern_fun(ats_bool_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_isnot_full) (ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_ngc_deque_arr_deque_initialize_tsz) (ats_ref_type, ats_size_type, ats_ptr_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atslib_ngc_deque_arr_deque_uninitialize) (ats_ref_type) ;
ATSextern_fun(ats_ptr_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_uninitialize_vt) (ats_ref_type) ;
ATSextern_fun(ats_ptr_type, atslib_ngc_deque_arr_deque_takeout_tsz) (ats_ref_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atslib_ngc_deque_arr_deque_insert_end_many_tsz) (ats_ref_type, ats_size_type, ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atslib_ngc_deque_arr_deque_remove_beg_many_tsz) (ats_ref_type, ats_size_type, ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_void_type, ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__deque_clear_all) (ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_ngc_deque_arr_deque_copyout_tsz) (ats_ref_type, ats_size_type, ats_size_type, ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atslib_ngc_deque_arr_deque_update_capacity_tsz) (ats_ref_type, ats_size_type, ats_ptr_type, ats_size_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__fprint_symbol) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_label_2esats__fprint_label) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_tyreckind) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_s2cst) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_s2var) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_d2con) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fpprint_s2exp) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fpprint_s2explst) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_funlab) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexplst) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__fprint_labhisexp) (ats_ptr_type, ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__lemma_deque_param_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_v_encode_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_v_decode_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_v_clear_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_insert_beg_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_insert_end_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_remove_beg_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_remove_end_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
extern
ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2edats____assert_prfck () ;
extern
ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_void_type aux_2 (ats_ptr_type env0, ats_ptr_type env1, ats_ptr_type env2, ats_ptr_type arg0, ats_int_type arg1) ;
static
ats_clo_ptr_type aux_2_closure_make (ats_ptr_type env0, ats_ptr_type env1, ats_ptr_type env2) ;
static
ats_void_type aux_2_clofun (ats_clo_ptr_type cloptr, ats_ptr_type arg0, ats_int_type arg1) ;
static
ats_void_type fprintlst_01693_ats_ptr_type (ats_ptr_type arg0, ats_ptr_type arg1, ats_ptr_type arg2, ats_ptr_type arg3) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_utils.dats: 10127(line=468, offs=7) -- 10401(line=478, offs=24)
*/
ATSstaticdec()
ats_void_type
aux_2 (ats_ptr_type env0, ats_ptr_type env1, ats_ptr_type env2, ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
// ATSlocal_void (tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
// ATSlocal_void (tmp27) ;
ATSlocal (ats_bool_type, tmp28) ;
// ATSlocal_void (tmp29) ;
ATSlocal (ats_int_type, tmp30) ;

__ats_lab_aux_2:
do {
/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
tmp25 = ats_caselptrlab_mac(anairiats_sum_4, arg0, atslab_0) ;
tmp26 = ats_caselptrlab_mac(anairiats_sum_4, arg0, atslab_1) ;
tmp28 = atspre_gt_int_int (arg1, 0) ;
if (tmp28) {
/* tmp27 = */ atspre_fprint_string (env0, env1) ;
} else {
/* empty */
} /* end of [if] */
/* tmp29 = */ ((ats_void_type(*)(ats_ptr_type, ats_ptr_type))env2) (env0, tmp25) ;
tmp30 = atspre_add_int_int (arg1, 1) ;
arg0 = tmp26 ;
arg1 = tmp30 ;
goto __ats_lab_aux_2 ; // tail call
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_6_1:
break ;
} while (0) ;
return /* (tmp24) */ ;
} /* end of [aux_2] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
ats_ptr_type closure_env_1 ;
ats_ptr_type closure_env_2 ;
} aux_2_closure_type ;

ats_void_type
aux_2_clofun (ats_clo_ptr_type cloptr, ats_ptr_type arg0, ats_int_type arg1) {
aux_2 (((aux_2_closure_type*)cloptr)->closure_env_0, ((aux_2_closure_type*)cloptr)->closure_env_1, ((aux_2_closure_type*)cloptr)->closure_env_2, arg0, arg1) ; return ;
} /* end of function */

ATSinline()
ats_void_type
aux_2_closure_init (aux_2_closure_type *p_clo, ats_ptr_type env0, ats_ptr_type env1, ats_ptr_type env2) {
p_clo->closure_fun = (ats_fun_ptr_type)&aux_2_clofun ;
p_clo->closure_env_0 = env0 ;
p_clo->closure_env_1 = env1 ;
p_clo->closure_env_2 = env2 ;
return ;
} /* end of function */

ats_clo_ptr_type
aux_2_closure_make (ats_ptr_type env0, ats_ptr_type env1, ats_ptr_type env2) {
aux_2_closure_type *p_clo = ATS_MALLOC(sizeof(aux_2_closure_type)) ;
aux_2_closure_init (p_clo, env0, env1, env2) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/research/Postiats/git/src/pats_utils.dats: 10088(line=465, offs=11) -- 10461(line=482, offs=4)
*/
ATSstaticdec()
ats_void_type
fprintlst_01693_ats_ptr_type (ats_ptr_type arg0, ats_ptr_type arg1, ats_ptr_type arg2, ats_ptr_type arg3) {
/* local vardec */
// ATSlocal_void (tmp23) ;

__ats_lab_fprintlst_01693_ats_ptr_type:
/* tmp23 = */ aux_2 (arg0, arg2, arg3, arg1, 0) ;
return /* (tmp23) */ ;
} /* end of [fprintlst_01693_ats_ptr_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_histaexp_print.dats: 1838(line=65, offs=4) -- 4505(line=184, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;
ATSlocal (ats_ptr_type, tmp2) ;
ATSlocal (ats_ptr_type, tmp3) ;
// ATSlocal_void (tmp4) ;
// ATSlocal_void (tmp5) ;
// ATSlocal_void (tmp6) ;
// ATSlocal_void (tmp7) ;
ATSlocal (ats_ptr_type, tmp8) ;
// ATSlocal_void (tmp9) ;
// ATSlocal_void (tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
// ATSlocal_void (tmp12) ;
// ATSlocal_void (tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;
// ATSlocal_void (tmp16) ;
// ATSlocal_void (tmp17) ;
// ATSlocal_void (tmp18) ;
// ATSlocal_void (tmp19) ;
ATSlocal (ats_ptr_type, tmp20) ;
// ATSlocal_void (tmp21) ;
// ATSlocal_void (tmp22) ;
ATSlocal (ats_int_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
// ATSlocal_void (tmp33) ;
// ATSlocal_void (tmp34) ;
// ATSlocal_void (tmp35) ;
// ATSlocal_void (tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
// ATSlocal_void (tmp38) ;
// ATSlocal_void (tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
// ATSlocal_void (tmp42) ;
// ATSlocal_void (tmp43) ;
// ATSlocal_void (tmp44) ;
// ATSlocal_void (tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;
// ATSlocal_void (tmp48) ;
// ATSlocal_void (tmp49) ;
// ATSlocal_void (tmp50) ;
// ATSlocal_void (tmp51) ;
ATSlocal (ats_ptr_type, tmp52) ;
// ATSlocal_void (tmp53) ;
// ATSlocal_void (tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;
ATSlocal (ats_ptr_type, tmp56) ;
// ATSlocal_void (tmp57) ;
// ATSlocal_void (tmp58) ;
// ATSlocal_void (tmp59) ;
// ATSlocal_void (tmp60) ;
ATSlocal (ats_ptr_type, tmp61) ;
// ATSlocal_void (tmp62) ;
// ATSlocal_void (tmp63) ;
ATSlocal (ats_ptr_type, tmp64) ;
// ATSlocal_void (tmp65) ;
// ATSlocal_void (tmp66) ;
ATSlocal (ats_ptr_type, tmp67) ;
// ATSlocal_void (tmp68) ;
// ATSlocal_void (tmp69) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp:
tmp1 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_hisexp_node) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (((ats_sum_ptr_type)tmp1)->tag != 2) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp2 = ats_caselptrlab_mac(anairiats_sum_1, tmp1, atslab_1) ;
tmp3 = ats_caselptrlab_mac(anairiats_sum_1, tmp1, atslab_2) ;
/* tmp4 = */ atspre_fprint_string (arg0, ATSstrcst("HSEfun(")) ;
/* tmp5 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexplst (arg0, tmp2) ;
/* tmp6 = */ atspre_fprint_string (arg0, ATSstrcst("; ")) ;
/* tmp7 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (arg0, tmp3) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (((ats_sum_ptr_type)tmp1)->tag != 3) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp8 = ats_caselptrlab_mac(anairiats_sum_2, tmp1, atslab_0) ;
/* tmp9 = */ atspre_fprint_string (arg0, ATSstrcst("HSEcfun(")) ;
/* tmp10 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_funlab (arg0, tmp8) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)tmp1)->tag != 4) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp11 = ats_caselptrlab_mac(anairiats_sum_2, tmp1, atslab_0) ;
/* tmp12 = */ atspre_fprint_string (arg0, ATSstrcst("HSEcst(")) ;
/* tmp13 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_s2cst (arg0, tmp11) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
if (((ats_sum_ptr_type)tmp1)->tag != 5) { goto __ats_lab_4_0 ; }
__ats_lab_3_1:
tmp14 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_0) ;
tmp15 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_1) ;
/* tmp16 = */ atspre_fprint_string (arg0, ATSstrcst("HSEapp(")) ;
/* tmp17 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (arg0, tmp14) ;
/* tmp18 = */ atspre_fprint_string (arg0, ATSstrcst("; ")) ;
/* tmp19 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexplst (arg0, tmp15) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)tmp1)->tag != 6) { goto __ats_lab_7_0 ; }
__ats_lab_4_1:
tmp20 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_1) ;
/* tmp21 = */ atspre_fprint_string (arg0, ATSstrcst("HSEextype(")) ;
/* tmp22 = */ fprintlst_01693_ats_ptr_type (arg0, tmp20, ATSstrcst("; "), &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexplst) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
if (((ats_sum_ptr_type)tmp1)->tag != 7) { goto __ats_lab_8_0 ; }
__ats_lab_7_1:
tmp31 = ats_caselptrlab_mac(anairiats_sum_5, tmp1, atslab_0) ;
tmp32 = ats_caselptrlab_mac(anairiats_sum_5, tmp1, atslab_1) ;
/* tmp33 = */ atspre_fprint_string (arg0, ATSstrcst("HSErefarg(")) ;
/* tmp34 = */ atspre_fprint_int (arg0, tmp31) ;
/* tmp35 = */ atspre_fprint_string (arg0, ATSstrcst("; ")) ;
/* tmp36 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (arg0, tmp32) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)tmp1)->tag != 1) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
tmp37 = ats_caselptrlab_mac(anairiats_sum_2, tmp1, atslab_0) ;
/* tmp38 = */ atspre_fprint_string (arg0, ATSstrcst("HSEtyabs(")) ;
/* tmp39 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__fprint_symbol (arg0, tmp37) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
if (((ats_sum_ptr_type)tmp1)->tag != 0) { goto __ats_lab_10_0 ; }
__ats_lab_9_1:
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst("HSEtybox()")) ;
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
if (((ats_sum_ptr_type)tmp1)->tag != 8) { goto __ats_lab_11_0 ; }
__ats_lab_10_1:
tmp40 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_0) ;
tmp41 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_1) ;
/* tmp42 = */ atspre_fprint_string (arg0, ATSstrcst("HSEtyarr(")) ;
/* tmp43 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (arg0, tmp40) ;
/* tmp44 = */ atspre_fprint_string (arg0, ATSstrcst("; ")) ;
/* tmp45 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fpprint_s2explst (arg0, tmp41) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
if (((ats_sum_ptr_type)tmp1)->tag != 9) { goto __ats_lab_12_0 ; }
__ats_lab_11_1:
tmp46 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_0) ;
tmp47 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_1) ;
/* tmp48 = */ atspre_fprint_string (arg0, ATSstrcst("HSEtyrec(")) ;
/* tmp49 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_tyreckind (arg0, tmp46) ;
/* tmp50 = */ atspre_fprint_string (arg0, ATSstrcst("; ")) ;
/* tmp51 = */ fprintlst_01693_ats_ptr_type (arg0, tmp47, ATSstrcst(", "), &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__fprint_labhisexp) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_12 */
__ats_lab_12_0:
if (((ats_sum_ptr_type)tmp1)->tag != 10) { goto __ats_lab_13_0 ; }
__ats_lab_12_1:
tmp52 = ats_caselptrlab_mac(anairiats_sum_2, tmp1, atslab_0) ;
/* tmp53 = */ atspre_fprint_string (arg0, ATSstrcst("HSEtyrecsin(")) ;
/* tmp54 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__fprint_labhisexp (arg0, tmp52) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
if (((ats_sum_ptr_type)tmp1)->tag != 11) { goto __ats_lab_14_0 ; }
__ats_lab_13_1:
tmp55 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_0) ;
tmp56 = ats_caselptrlab_mac(anairiats_sum_3, tmp1, atslab_1) ;
/* tmp57 = */ atspre_fprint_string (arg0, ATSstrcst("HSEtysum(")) ;
/* tmp58 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_d2con (arg0, tmp55) ;
/* tmp59 = */ atspre_fprint_string (arg0, ATSstrcst("; ")) ;
/* tmp60 = */ fprintlst_01693_ats_ptr_type (arg0, tmp56, ATSstrcst(", "), &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__fprint_labhisexp) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_14 */
__ats_lab_14_0:
if (((ats_sum_ptr_type)tmp1)->tag != 12) { goto __ats_lab_15_0 ; }
__ats_lab_14_1:
tmp61 = ats_caselptrlab_mac(anairiats_sum_2, tmp1, atslab_0) ;
/* tmp62 = */ atspre_fprint_string (arg0, ATSstrcst("HSEtyvar(")) ;
/* tmp63 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fprint_s2var (arg0, tmp61) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
if (((ats_sum_ptr_type)tmp1)->tag != 13) { goto __ats_lab_16_0 ; }
__ats_lab_15_1:
tmp64 = ats_caselptrlab_mac(anairiats_sum_2, tmp1, atslab_0) ;
/* tmp65 = */ atspre_fprint_string (arg0, ATSstrcst("HSEvararg(")) ;
/* tmp66 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fpprint_s2exp (arg0, tmp64) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;

/* branch: __ats_lab_16 */
__ats_lab_16_0:
// if (((ats_sum_ptr_type)tmp1)->tag != 14) { ats_deadcode_failure_handle () ; }
__ats_lab_16_1:
tmp67 = ats_caselptrlab_mac(anairiats_sum_2, tmp1, atslab_0) ;
/* tmp68 = */ atspre_fprint_string (arg0, ATSstrcst("HSEs2exp(")) ;
/* tmp69 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__fpprint_s2exp (arg0, tmp67) ;
/* tmp0 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
break ;
} while (0) ;
return /* (tmp0) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp] */

/*
// /home/hwxi/research/Postiats/git/src/pats_histaexp_print.dats: 4577(line=189, offs=14) -- 4616(line=189, offs=53)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__print_hisexp (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp70) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__print_hisexp:
/* tmp70 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (stdout, arg0) ;
return /* (tmp70) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__print_hisexp] */

/*
// /home/hwxi/research/Postiats/git/src/pats_histaexp_print.dats: 4640(line=191, offs=14) -- 4679(line=191, offs=53)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__prerr_hisexp (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp71) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__prerr_hisexp:
/* tmp71 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (stderr, arg0) ;
return /* (tmp71) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__prerr_hisexp] */

/*
// /home/hwxi/research/Postiats/git/src/pats_histaexp_print.dats: 4731(line=197, offs=3) -- 4909(line=205, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__fprint_labhisexp (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp72) ;
ATSlocal (ats_ptr_type, tmp73) ;
ATSlocal (ats_ptr_type, tmp74) ;
// ATSlocal_void (tmp75) ;
// ATSlocal_void (tmp76) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__fprint_labhisexp:

tmp73 = ats_caselptrlab_mac(anairiats_sum_6, arg1, atslab_0) ;
tmp74 = ats_caselptrlab_mac(anairiats_sum_6, arg1, atslab_2) ;
/* tmp75 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_label_2esats__fprint_label (arg0, tmp73) ;
/* tmp76 = */ atspre_fprint_string (arg0, ATSstrcst("=")) ;
/* tmp72 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp (arg0, tmp74) ;
return /* (tmp72) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__fprint_labhisexp] */

/*
// /home/hwxi/research/Postiats/git/src/pats_histaexp_print.dats: 4990(line=211, offs=3) -- 5046(line=211, offs=59)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexplst (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp77) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexplst:
/* tmp77 = */ fprintlst_01693_ats_ptr_type (arg0, arg1, ATSstrcst(", "), &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexp) ;
return /* (tmp77) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__fprint_hisexplst] */

/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_label_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2edats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_basics_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_label_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp2_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_histaexp_print_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
ATS_2d0_2e2_2e11_2libats_2ngc_2SATS_2deque_arr_2esats__lemma_deque_param_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_v_encode_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_v_decode_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_v_clear_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_insert_beg_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_insert_end_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_remove_beg_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats__DEQUEarr_remove_end_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
ATS_2d0_2e2_2e11_2libats_2ngc_2DATS_2deque_arr_2edats____assert_prfck () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2edats____assert_prfck () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2edats____assert_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_histaexp_print_dats.c] */
