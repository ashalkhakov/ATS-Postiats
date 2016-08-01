/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2016-7-23: 22h:11m
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

typedef
struct {
ats_ptr_type atslab_lexerr_loc ;
ats_ptr_type atslab_lexerr_node ;
} anairiats_rec_1 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_2 ;

typedef struct {
int tag ;
ats_char_type atslab_0 ;
} anairiats_sum_3 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_nil_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_CHAR_oct_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_CHAR_hex_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_CHAR_unclose_2) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_QUOTE_dangling_3) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_STRING_unclose_4) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_STRING_char_oct_5) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_STRING_char_hex_6) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_COMMENT_block_unclose_7) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_EXTCODE_unclose_8) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_DIGIT_oct_89_9) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_FEXPONENT_empty_10) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__LE_UNSUPPORTED_char_11) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_vbox_make_view_ptr) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_newline) (ats_ptr_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_sub_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
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
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__fprint_location) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_lexerr) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__the_lexerrlst_get) (ats_ref_type) ;

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
ats_ptr_type ref_01088_ats_int_type (ats_int_type arg0) ;
static
ats_ptr_type ref_01088_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_void_type loop_5 (ats_ptr_type arg0) ;
static
ats_void_type list_vt_free_01499_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_ptr_type revapp_10 (ats_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_ptr_type list_vt_reverse_append_01507_ats_ptr_type (ats_ptr_type arg0, ats_ptr_type arg1) ;
static
ats_ptr_type list_vt_reverse_01506_ats_ptr_type (ats_ptr_type arg0) ;
static
ats_int_type loop_13 (ats_ptr_type arg0, ats_ptr_type arg1, ats_int_type arg2) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp1) ;
ATSstatic (ats_ptr_type, statmp4) ;
ATSstatic (ats_ptr_type, statmp7) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lexing_error.dats: 1667(line=54, offs=3) -- 1722(line=56, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__lexerr_make (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__lexerr_make:
tmp0 = ATS_MALLOC(sizeof(anairiats_rec_1)) ;
ats_selptrset_mac(anairiats_rec_1, tmp0, atslab_lexerr_loc, arg0) ;
ats_selptrset_mac(anairiats_rec_1, tmp0, atslab_lexerr_node, arg1) ;

return (tmp0) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__lexerr_make] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/reference.dats: 1828(line=57, offs=18) -- 1902(line=59, offs=4)
*/
ATSstaticdec()
ats_ptr_type
ref_01088_ats_int_type (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp2) ;
ATSlocal (ats_int_type, tmp3) ;

__ats_lab_ref_01088_ats_int_type:
/* ats_int_type tmp3 ; */
tmp3 = arg0 ;
tmp2 = atspre_ref_make_elt_tsz ((&tmp3), sizeof(ats_int_type)) ;
return (tmp2) ;
} /* end of [ref_01088_ats_int_type] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/reference.dats: 1828(line=57, offs=18) -- 1902(line=59, offs=4)
*/
ATSstaticdec()
ats_ptr_type
ref_01088_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_ptr_type, tmp6) ;

__ats_lab_ref_01088_ats_ptr_type:
/* ats_ptr_type tmp6 ; */
tmp6 = arg0 ;
tmp5 = atspre_ref_make_elt_tsz ((&tmp6), sizeof(ats_ptr_type)) ;
return (tmp5) ;
} /* end of [ref_01088_ats_ptr_type] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 4893(line=177, offs=7) -- 5015(line=178, offs=73)
*/
ATSstaticdec()
ats_void_type
loop_5 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp12) ;
ATSlocal (ats_ptr_type, tmp13) ;

__ats_lab_loop_5:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp13 = ats_caselptrlab_mac(anairiats_sum_2, arg0, atslab_1) ;
ATS_FREE(arg0) ;
arg0 = tmp13 ;
goto __ats_lab_loop_5 ; // tail call
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_1_1:
break ;
} while (0) ;
return /* (tmp12) */ ;
} /* end of [loop_5] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 4875(line=176, offs=14) -- 5054(line=182, offs=4)
*/
ATSstaticdec()
ats_void_type
list_vt_free_01499_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp11) ;

__ats_lab_list_vt_free_01499_ats_ptr_type:
/* tmp11 = */ loop_5 (arg0) ;
return /* (tmp11) */ ;
} /* end of [list_vt_free_01499_ats_ptr_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lexing_error.dats: 2279(line=87, offs=3) -- 2488(line=94, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__the_lexerrlst_clear () {
/* local vardec */
// ATSlocal_void (tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
// ATSlocal_void (tmp10) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__the_lexerrlst_clear:
ats_ptrget_mac(ats_int_type, statmp1) = 0 ;
tmp9 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp4), atslab_1) ;
tmp14 = ats_ptrget_mac(ats_ptr_type, tmp9) ;
/* tmp10 = */ list_vt_free_01499_ats_ptr_type (tmp14) ;
tmp15 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, tmp9) = tmp15 ;
return /* (tmp8) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__the_lexerrlst_clear] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lexing_error.dats: 2552(line=98, offs=3) -- 2858(line=109, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__the_lexerrlst_add (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp16) ;
ATSlocal (ats_ptr_type, tmp17) ;
ATSlocal (ats_int_type, tmp18) ;
ATSlocal (ats_int_type, tmp19) ;
ATSlocal (ats_bool_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_ptr_type, tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__the_lexerrlst_add:
tmp17 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp1), atslab_1) ;
tmp18 = ats_ptrget_mac(ats_int_type, tmp17) ;
tmp19 = atspre_add_int_int (tmp18, 1) ;
ats_ptrget_mac(ats_int_type, tmp17) = tmp19 ;
tmp20 = atspre_lt_int_int (tmp18, 100) ;
if (tmp20) {
tmp21 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp4), atslab_1) ;
tmp23 = ats_ptrget_mac(ats_ptr_type, tmp21) ;
tmp22 = ATS_MALLOC(sizeof(anairiats_sum_2)) ;
ats_selptrset_mac(anairiats_sum_2, tmp22, atslab_0, arg0) ;
ats_selptrset_mac(anairiats_sum_2, tmp22, atslab_1, tmp23) ;
ats_ptrget_mac(ats_ptr_type, tmp21) = tmp22 ;
} else {
/* empty */
} /* end of [if] */
return /* (tmp16) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__the_lexerrlst_add] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 7889(line=308, offs=7) -- 8174(line=317, offs=28)
*/
ATSstaticdec()
ats_ptr_type
revapp_10 (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;

__ats_lab_revapp_10:
do {
/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp32 = &ats_caselptrlab_mac(anairiats_sum_2, arg0, atslab_1) ;
tmp33 = ats_ptrget_mac(ats_ptr_type, tmp32) ;
ats_ptrget_mac(ats_ptr_type, tmp32) = arg1 ;
tmp34 = arg0 ;
arg0 = tmp33 ;
arg1 = tmp34 ;
goto __ats_lab_revapp_10 ; // tail call
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_3_1:
tmp31 = arg1 ;
break ;
} while (0) ;
return (tmp31) ;
} /* end of [revapp_10] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 7770(line=303, offs=24) -- 8220(line=321, offs=4)
*/
ATSstaticdec()
ats_ptr_type
list_vt_reverse_append_01507_ats_ptr_type (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp30) ;

__ats_lab_list_vt_reverse_append_01507_ats_ptr_type:
tmp30 = revapp_10 (arg0, arg1) ;
return (tmp30) ;
} /* end of [list_vt_reverse_append_01507_ats_ptr_type] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 7652(line=298, offs=17) -- 7704(line=299, offs=46)
*/
ATSstaticdec()
ats_ptr_type
list_vt_reverse_01506_ats_ptr_type (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp35) ;

__ats_lab_list_vt_reverse_01506_ats_ptr_type:
tmp35 = (ats_sum_ptr_type)0 ;
tmp29 = list_vt_reverse_append_01507_ats_ptr_type (arg0, tmp35) ;
return (tmp29) ;
} /* end of [list_vt_reverse_01506_ats_ptr_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lexing_error.dats: 2920(line=113, offs=3) -- 3127(line=120, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__the_lexerrlst_get (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_int_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
ATSlocal (ats_ptr_type, tmp36) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__the_lexerrlst_get:
tmp25 = ats_ptrget_mac(ats_int_type, statmp1) ;
ats_ptrget_mac(ats_int_type, arg0) = tmp25 ;
ats_ptrget_mac(ats_int_type, statmp1) = 0 ;
tmp26 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, statmp4), atslab_1) ;
tmp27 = ats_ptrget_mac(ats_ptr_type, tmp26) ;
tmp28 = list_vt_reverse_01506_ats_ptr_type (tmp27) ;
tmp36 = (ats_sum_ptr_type)0 ;
ats_ptrget_mac(ats_ptr_type, tmp26) = tmp36 ;
tmp24 = tmp28 ;
return (tmp24) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__the_lexerrlst_get] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lexing_error.dats: 3229(line=128, offs=3) -- 5917(line=203, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_lexerr (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;
// ATSlocal_void (tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;
// ATSlocal_void (tmp41) ;
// ATSlocal_void (tmp42) ;
// ATSlocal_void (tmp43) ;
// ATSlocal_void (tmp44) ;
// ATSlocal_void (tmp45) ;
// ATSlocal_void (tmp46) ;
// ATSlocal_void (tmp47) ;
// ATSlocal_void (tmp48) ;
// ATSlocal_void (tmp49) ;
// ATSlocal_void (tmp50) ;
// ATSlocal_void (tmp51) ;
// ATSlocal_void (tmp52) ;
// ATSlocal_void (tmp53) ;
// ATSlocal_void (tmp54) ;
// ATSlocal_void (tmp55) ;
// ATSlocal_void (tmp56) ;
ATSlocal (ats_char_type, tmp57) ;
// ATSlocal_void (tmp58) ;
// ATSlocal_void (tmp59) ;
// ATSlocal_void (tmp60) ;
// ATSlocal_void (tmp61) ;
// ATSlocal_void (tmp62) ;
// ATSlocal_void (tmp63) ;
ATSlocal (ats_char_type, tmp64) ;
// ATSlocal_void (tmp65) ;
// ATSlocal_void (tmp66) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_lexerr:
tmp38 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, arg1), atslab_lexerr_loc) ;
/* tmp39 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__fprint_location (arg0, tmp38) ;
tmp40 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, arg1), atslab_lexerr_node) ;
do {
/* branch: __ats_lab_4 */
__ats_lab_4_0:
if (((ats_sum_ptr_type)tmp40)->tag != 0) { goto __ats_lab_5_0 ; }
__ats_lab_4_1:
/* tmp41 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp42 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the char format (oct) is incorrect.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
if (((ats_sum_ptr_type)tmp40)->tag != 1) { goto __ats_lab_6_0 ; }
__ats_lab_5_1:
/* tmp43 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp44 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the char format (hex) is incorrect.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_6 */
__ats_lab_6_0:
if (((ats_sum_ptr_type)tmp40)->tag != 2) { goto __ats_lab_7_0 ; }
__ats_lab_6_1:
/* tmp45 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp46 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the char consant is unclosed.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_7 */
__ats_lab_7_0:
if (((ats_sum_ptr_type)tmp40)->tag != 5) { goto __ats_lab_8_0 ; }
__ats_lab_7_1:
/* tmp47 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp48 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the string-char format (oct) is incorrect.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)tmp40)->tag != 6) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
/* tmp49 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp50 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the string-char format (hex) is incorrect.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
if (((ats_sum_ptr_type)tmp40)->tag != 4) { goto __ats_lab_10_0 ; }
__ats_lab_9_1:
/* tmp51 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp52 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the string constant is unclosed.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
if (((ats_sum_ptr_type)tmp40)->tag != 7) { goto __ats_lab_11_0 ; }
__ats_lab_10_1:
/* tmp53 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp54 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the comment block is unclosed.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
if (((ats_sum_ptr_type)tmp40)->tag != 8) { goto __ats_lab_12_0 ; }
__ats_lab_11_1:
/* tmp55 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp56 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the external code block is unclosed.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_12 */
__ats_lab_12_0:
if (((ats_sum_ptr_type)tmp40)->tag != 9) { goto __ats_lab_13_0 ; }
__ats_lab_12_1:
tmp57 = ats_caselptrlab_mac(anairiats_sum_3, tmp40, atslab_0) ;
/* tmp58 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp59 = */ atspre_fprintf_exn (arg0, ATSstrcst(": illegal digit (oct): %c"), tmp57) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_13 */
__ats_lab_13_0:
if (((ats_sum_ptr_type)tmp40)->tag != 10) { goto __ats_lab_14_0 ; }
__ats_lab_13_1:
/* tmp60 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp61 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the floating exponent is empty.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_14 */
__ats_lab_14_0:
if (((ats_sum_ptr_type)tmp40)->tag != 3) { goto __ats_lab_15_0 ; }
__ats_lab_14_1:
/* tmp62 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp63 = */ atspre_fprintf_exn (arg0, ATSstrcst(": the quote symbol (') is dangling.")) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
// if (((ats_sum_ptr_type)tmp40)->tag != 11) { ats_deadcode_failure_handle () ; }
__ats_lab_15_1:
tmp64 = ats_caselptrlab_mac(anairiats_sum_3, tmp40, atslab_0) ;
/* tmp65 = */ atspre_fprintf_exn (arg0, ATSstrcst(": error(lexing)")) ;
/* tmp66 = */ atspre_fprintf_exn (arg0, ATSstrcst(": unsupported char: %c"), tmp64) ;
/* tmp37 = */ atspre_fprint_newline (arg0) ;
break ;
} while (0) ;
return /* (tmp37) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_lexerr] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lexing_error.dats: 6067(line=213, offs=7) -- 6304(line=220, offs=27)
*/
ATSstaticdec()
ats_int_type
loop_13 (ats_ptr_type arg0, ats_ptr_type arg1, ats_int_type arg2) {
/* local vardec */
ATSlocal (ats_int_type, tmp70) ;
ATSlocal (ats_ptr_type, tmp71) ;
ATSlocal (ats_ptr_type, tmp72) ;
// ATSlocal_void (tmp73) ;
ATSlocal (ats_int_type, tmp74) ;

__ats_lab_loop_13:
do {
/* branch: __ats_lab_16 */
__ats_lab_16_0:
if (arg1 == (ats_sum_ptr_type)0) { goto __ats_lab_17_0 ; }
__ats_lab_16_1:
tmp71 = ats_caselptrlab_mac(anairiats_sum_2, arg1, atslab_0) ;
tmp72 = ats_caselptrlab_mac(anairiats_sum_2, arg1, atslab_1) ;
ATS_FREE(arg1) ;
/* tmp73 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_lexerr (arg0, tmp71) ;
tmp74 = atspre_sub_int_int (arg2, 1) ;
arg0 = arg0 ;
arg1 = tmp72 ;
arg2 = tmp74 ;
goto __ats_lab_loop_13 ; // tail call
break ;

/* branch: __ats_lab_17 */
__ats_lab_17_0:
// if (arg1 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_17_1:
tmp70 = arg2 ;
break ;
} while (0) ;
return (tmp70) ;
} /* end of [loop_13] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_lexing_error.dats: 5999(line=209, offs=3) -- 6719(line=239, offs=4)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_the_lexerrlst (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp67) ;
ATSlocal (ats_int_type, tmp68) ;
ATSlocal (ats_ptr_type, tmp69) ;
ATSlocal (ats_int_type, tmp75) ;
// ATSlocal_void (tmp76) ;
ATSlocal (ats_bool_type, tmp77) ;
// ATSlocal_void (tmp78) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_the_lexerrlst:
/* ats_int_type tmp68 ; */
tmp69 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__the_lexerrlst_get ((&tmp68)) ;
do {
/* branch: __ats_lab_18 */
__ats_lab_18_0:
if (tmp69 == (ats_sum_ptr_type)0) { goto __ats_lab_19_0 ; }
__ats_lab_18_1:
tmp75 = loop_13 (arg0, tmp69, tmp68) ;
tmp77 = atspre_gt_int_int (tmp75, 0) ;
if (tmp77) {
/* tmp78 = */ atspre_fprint_string (arg0, ATSstrcst("There are possibly some additional errors.")) ;
/* tmp76 = */ atspre_fprint_newline (arg0) ;
} else {
/* empty */
} /* end of [if] */
tmp67 = 1 ;
break ;

/* branch: __ats_lab_19 */
__ats_lab_19_0:
// if (tmp69 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_19_1:
tmp67 = 0 ;
break ;
} while (0) ;
return (tmp67) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__fprint_the_lexerrlst] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__staload_flag = 1 ;

// _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_location_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_lexing_error_2edats__staload () ;

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
ATS_GC_MARKROOT(&statmp1, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp4, sizeof(ats_ptr_type)) ;
ATS_GC_MARKROOT(&statmp7, sizeof(ats_ptr_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
statmp1 = ref_01088_ats_int_type (0) ;
statmp7 = (ats_sum_ptr_type)0 ;
statmp4 = ref_01088_ats_ptr_type (statmp7) ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_lexing_error_dats.c] */
