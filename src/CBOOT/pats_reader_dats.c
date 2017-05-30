/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2017-5-22:  9h:52m
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

#include "pats_reader.cats"

#include "libc/CATS/stdio.cats"

#include "libc/sys/CATS/types.cats"
/* external codes at top */
/* type definitions */
typedef
struct {
ats_ptr_type atslab_3 ;
ats_ptr_type atslab_4 ;
} anairiats_rec_0 ;

typedef struct {
ats_char_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_1 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__list_vt_nil_1) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_cloptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_vbox_make_view_ptr) (ats_ptr_type) ;
ATSextern_fun(ats_int_type, atspre_int_of_char) (ats_char_type) ;
ATSextern_fun(ats_int_type, atspre_int_of_uchar) (ats_uchar_type) ;
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
ATSextern_fun(ats_void_type, atspre_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_ptr_zero_tsz) (ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_ptr_type, atspre_ref_make_elt_tsz) (ats_ref_type, ats_size_type) ;
ATSextern_fun(ats_char_type, atspre_string_get_char_at) (ats_ptr_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_string_isnot_atend) (ats_ptr_type, ats_size_type) ;
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
ATSextern_fun(ats_void_type, atslib_fclose_exn) (ats_ptr_type) ;

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
extern
ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats____assert_prfck () ;
extern
ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__reader0_encode_prfck () ;
extern
ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__reader0_decode_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__sasp__reader_vt0ype = 0 ;
int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__sasp__reader0 = 0 ;

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_int_type __ats_fun_2 (ats_ptr_type env0) ;
static
ats_clo_ptr_type __ats_fun_2_closure_make (ats_ptr_type env0) ;
static
ats_int_type __ats_fun_2_clofun (ats_clo_ptr_type cloptr) ;
static
ats_void_type __ats_fun_3 (ats_ptr_type env0) ;
static
ats_clo_ptr_type __ats_fun_3_closure_make (ats_ptr_type env0) ;
static
ats_void_type __ats_fun_3_clofun (ats_clo_ptr_type cloptr) ;
static
ats_void_type reader0_initize_filp_1 (ats_ref_type arg0, ats_ptr_type arg1) ;
static
ats_void_type __ats_fun_5 () ;
static
ats_clo_ptr_type __ats_fun_5_closure_make () ;
static
ats_void_type __ats_fun_5_clofun (ats_clo_ptr_type cloptr) ;
static
ats_void_type reader0_initize_getc_4 (ats_ref_type arg0, ats_clo_ptr_type arg1) ;
static
ats_int_type __ats_fun_7 (ats_ptr_type env0, ats_ptr_type env1) ;
static
ats_clo_ptr_type __ats_fun_7_closure_make (ats_ptr_type env0, ats_ptr_type env1) ;
static
ats_int_type __ats_fun_7_clofun (ats_clo_ptr_type cloptr) ;
static
ats_void_type __ats_fun_8 (ats_ptr_type env0) ;
static
ats_clo_ptr_type __ats_fun_8_closure_make (ats_ptr_type env0) ;
static
ats_void_type __ats_fun_8_clofun (ats_clo_ptr_type cloptr) ;
static
ats_void_type reader0_initize_string_6 (ats_ref_type arg0, ats_ptr_type arg1, ats_ptr_type arg2) ;
static
ats_int_type __ats_fun_10 (ats_ptr_type env0) ;
static
ats_clo_ptr_type __ats_fun_10_closure_make (ats_ptr_type env0) ;
static
ats_int_type __ats_fun_10_clofun (ats_clo_ptr_type cloptr) ;
static
ats_void_type loop_13 (ats_ptr_type arg0) ;
static
ats_void_type list_vt_free_01499_ats_char_type (ats_ptr_type arg0) ;
static
ats_void_type __ats_fun_11 (ats_ptr_type env0) ;
static
ats_clo_ptr_type __ats_fun_11_closure_make (ats_ptr_type env0) ;
static
ats_void_type __ats_fun_11_clofun (ats_clo_ptr_type cloptr) ;
static
ats_void_type reader0_initize_charlst_vt_9 (ats_ref_type arg0, ats_ptr_type arg1) ;
static
ats_void_type reader0_uninitize_14 (ats_ref_type arg0) ;
static
ats_ptr_type ptr_alloc_01070_ats_size_type () ;
static
ats_ptr_type ptr_alloc_01070_ats_ptr_type () ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 1998(line=74, offs=3) -- 2034(line=74, offs=39)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_get_char (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp0) ;
ATSlocal (ats_clo_ptr_type, tmp1) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_get_char:
tmp1 = ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), getchar) ;
tmp0 = ((ats_int_type(*)(ats_clo_ptr_type))(ats_closure_fun(tmp1))) (tmp1) ;
return (tmp0) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_get_char] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 2262(line=92, offs=11) -- 2330(line=93, offs=65)
*/
ATSstaticdec()
ats_int_type
__ats_fun_2 (ats_ptr_type env0) {
/* local vardec */
ATSlocal (ats_int_type, tmp3) ;

__ats_lab___ats_fun_2:
tmp3 = atslib_fgetc_err (env0) ;
return (tmp3) ;
} /* end of [__ats_fun_2] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
} __ats_fun_2_closure_type ;

ats_int_type
__ats_fun_2_clofun (ats_clo_ptr_type cloptr) {
return __ats_fun_2 (((__ats_fun_2_closure_type*)cloptr)->closure_env_0) ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_2_closure_init (__ats_fun_2_closure_type *p_clo, ats_ptr_type env0) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_2_clofun ;
p_clo->closure_env_0 = env0 ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_2_closure_make (ats_ptr_type env0) {
__ats_fun_2_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_2_closure_type)) ;
__ats_fun_2_closure_init (p_clo, env0) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 2368(line=97, offs=11) -- 2436(line=98, offs=65)
*/
ATSstaticdec()
ats_void_type
__ats_fun_3 (ats_ptr_type env0) {
/* local vardec */
// ATSlocal_void (tmp5) ;

__ats_lab___ats_fun_3:
/* tmp5 = */ atslib_fclose_exn (env0) ;
return /* (tmp5) */ ;
} /* end of [__ats_fun_3] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
} __ats_fun_3_closure_type ;

ats_void_type
__ats_fun_3_clofun (ats_clo_ptr_type cloptr) {
__ats_fun_3 (((__ats_fun_3_closure_type*)cloptr)->closure_env_0) ; return ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_3_closure_init (__ats_fun_3_closure_type *p_clo, ats_ptr_type env0) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_3_clofun ;
p_clo->closure_env_0 = env0 ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_3_closure_make (ats_ptr_type env0) {
__ats_fun_3_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_3_closure_type)) ;
__ats_fun_3_closure_init (p_clo, env0) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 2063(line=79, offs=1) -- 2553(line=105, offs=2)
*/
ATSstaticdec()
ats_void_type
reader0_initize_filp_1 (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp2) ;
ATSlocal (ats_ptr_type, tmp4) ;
ATSlocal (ats_ptr_type, tmp6) ;

__ats_lab_reader0_initize_filp_1:
tmp4 = __ats_fun_2_closure_make (arg1) ;
tmp6 = __ats_fun_3_closure_make (arg1) ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), getchar) = tmp4 ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), freeres) = tmp6 ;
return /* (tmp2) */ ;
} /* end of [reader0_initize_filp_1] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 2914(line=120, offs=17) -- 3003(line=122, offs=63)
*/
ATSstaticdec()
ats_void_type
__ats_fun_5 () {
/* local vardec */
// ATSlocal_void (tmp8) ;

__ats_lab___ats_fun_5:
return /* (tmp8) */ ;
} /* end of [__ats_fun_5] */

typedef struct {
ats_fun_ptr_type closure_fun ;
} __ats_fun_5_closure_type ;

ats_void_type
__ats_fun_5_clofun (ats_clo_ptr_type cloptr) {
__ats_fun_5 () ; return ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_5_closure_init (__ats_fun_5_closure_type *p_clo) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_5_clofun ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_5_closure_make () {
__ats_fun_5_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_5_closure_type)) ;
__ats_fun_5_closure_init (p_clo) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 2616(line=110, offs=1) -- 3102(line=126, offs=2)
*/
ATSstaticdec()
ats_void_type
reader0_initize_getc_4 (ats_ref_type arg0, ats_clo_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp7) ;
ATSlocal (ats_ptr_type, tmp9) ;

__ats_lab_reader0_initize_getc_4:
tmp9 = __ats_fun_5_closure_make () ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), getchar) = ats_castfn_mac(ats_clo_ptr_type, arg1) ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), freeres) = tmp9 ;
return /* (tmp7) */ ;
} /* end of [reader0_initize_getc_4] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 3434(line=142, offs=17) -- 3821(line=157, offs=6)
*/
ATSstaticdec()
ats_int_type
__ats_fun_7 (ats_ptr_type env0, ats_ptr_type env1) {
/* local vardec */
ATSlocal (ats_int_type, tmp11) ;
ATSlocal (ats_size_type, tmp12) ;
ATSlocal (ats_bool_type, tmp13) ;
ATSlocal (ats_char_type, tmp14) ;
ATSlocal (ats_size_type, tmp15) ;

__ats_lab___ats_fun_7:
tmp12 = ats_ptrget_mac(ats_size_type, env1) ;
tmp13 = atspre_string_isnot_atend (env0, tmp12) ;
if (tmp13) {
tmp14 = atspre_string_get_char_at (env0, tmp12) ;
tmp15 = atspre_add_size1_int1 (tmp12, 1) ;
ats_ptrget_mac(ats_size_type, env1) = tmp15 ;
tmp11 = atspre_int_of_char (tmp14) ;
} else {
tmp11 = -1 ;
} /* end of [if] */
return (tmp11) ;
} /* end of [__ats_fun_7] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
ats_ptr_type closure_env_1 ;
} __ats_fun_7_closure_type ;

ats_int_type
__ats_fun_7_clofun (ats_clo_ptr_type cloptr) {
return __ats_fun_7 (((__ats_fun_7_closure_type*)cloptr)->closure_env_0, ((__ats_fun_7_closure_type*)cloptr)->closure_env_1) ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_7_closure_init (__ats_fun_7_closure_type *p_clo, ats_ptr_type env0, ats_ptr_type env1) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_7_clofun ;
p_clo->closure_env_0 = env0 ;
p_clo->closure_env_1 = env1 ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_7_closure_make (ats_ptr_type env0, ats_ptr_type env1) {
__ats_fun_7_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_7_closure_type)) ;
__ats_fun_7_closure_init (p_clo, env0, env1) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 3857(line=159, offs=17) -- 3926(line=160, offs=66)
*/
ATSstaticdec()
ats_void_type
__ats_fun_8 (ats_ptr_type env0) {
/* local vardec */
// ATSlocal_void (tmp17) ;

__ats_lab___ats_fun_8:
/* tmp17 = */ atspre_ptr_free (env0) ;
return /* (tmp17) */ ;
} /* end of [__ats_fun_8] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
} __ats_fun_8_closure_type ;

ats_void_type
__ats_fun_8_clofun (ats_clo_ptr_type cloptr) {
__ats_fun_8 (((__ats_fun_8_closure_type*)cloptr)->closure_env_0) ; return ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_8_closure_init (__ats_fun_8_closure_type *p_clo, ats_ptr_type env0) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_8_clofun ;
p_clo->closure_env_0 = env0 ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_8_closure_make (ats_ptr_type env0) {
__ats_fun_8_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_8_closure_type)) ;
__ats_fun_8_closure_init (p_clo, env0) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 3162(line=131, offs=1) -- 4052(line=166, offs=2)
*/
ATSstaticdec()
ats_void_type
reader0_initize_string_6 (ats_ref_type arg0, ats_ptr_type arg1, ats_ptr_type arg2) {
/* local vardec */
// ATSlocal_void (tmp10) ;
ATSlocal (ats_ptr_type, tmp16) ;
ATSlocal (ats_ptr_type, tmp18) ;

__ats_lab_reader0_initize_string_6:
tmp16 = __ats_fun_7_closure_make (arg1, arg2) ;
tmp18 = __ats_fun_8_closure_make (arg2) ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), getchar) = tmp16 ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), freeres) = tmp18 ;
return /* (tmp10) */ ;
} /* end of [reader0_initize_string_6] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 4417(line=189, offs=5) -- 4864(line=206, offs=6)
*/
ATSstaticdec()
ats_int_type
__ats_fun_10 (ats_ptr_type env0) {
/* local vardec */
ATSlocal (ats_int_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_char_type, tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;

__ats_lab___ats_fun_10:
tmp21 = ats_ptrget_mac(ats_ptr_type, env0) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (tmp21 == (ats_sum_ptr_type)0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp22 = ats_caselptrlab_mac(anairiats_sum_1, tmp21, atslab_0) ;
tmp23 = ats_caselptrlab_mac(anairiats_sum_1, tmp21, atslab_1) ;
ATS_FREE(tmp21) ;
ats_ptrget_mac(ats_ptr_type, env0) = tmp23 ;
tmp20 = atspre_int_of_uchar (ats_castfn_mac(ats_uchar_type, tmp22)) ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
// if (tmp21 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_1_1:
tmp20 = -1 ;
break ;
} while (0) ;
return (tmp20) ;
} /* end of [__ats_fun_10] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
} __ats_fun_10_closure_type ;

ats_int_type
__ats_fun_10_clofun (ats_clo_ptr_type cloptr) {
return __ats_fun_10 (((__ats_fun_10_closure_type*)cloptr)->closure_env_0) ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_10_closure_init (__ats_fun_10_closure_type *p_clo, ats_ptr_type env0) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_10_clofun ;
p_clo->closure_env_0 = env0 ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_10_closure_make (ats_ptr_type env0) {
__ats_fun_10_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_10_closure_type)) ;
__ats_fun_10_closure_init (p_clo, env0) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 4893(line=177, offs=7) -- 5015(line=178, offs=73)
*/
ATSstaticdec()
ats_void_type
loop_13 (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;

__ats_lab_loop_13:
do {
/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (arg0 == (ats_sum_ptr_type)0) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp29 = ats_caselptrlab_mac(anairiats_sum_1, arg0, atslab_1) ;
ATS_FREE(arg0) ;
arg0 = tmp29 ;
goto __ats_lab_loop_13 ; // tail call
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
// if (arg0 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_3_1:
break ;
} while (0) ;
return /* (tmp28) */ ;
} /* end of [loop_13] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/list_vt.dats: 4875(line=176, offs=14) -- 5054(line=182, offs=4)
*/
ATSstaticdec()
ats_void_type
list_vt_free_01499_ats_char_type (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp27) ;

__ats_lab_list_vt_free_01499_ats_char_type:
/* tmp27 = */ loop_13 (arg0) ;
return /* (tmp27) */ ;
} /* end of [list_vt_free_01499_ats_char_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 4920(line=209, offs=5) -- 5074(line=216, offs=6)
*/
ATSstaticdec()
ats_void_type
__ats_fun_11 (ats_ptr_type env0) {
/* local vardec */
// ATSlocal_void (tmp25) ;
// ATSlocal_void (tmp26) ;
ATSlocal (ats_ptr_type, tmp30) ;

__ats_lab___ats_fun_11:
tmp30 = ats_ptrget_mac(ats_ptr_type, env0) ;
/* tmp26 = */ list_vt_free_01499_ats_char_type (tmp30) ;
/* tmp25 = */ atspre_ptr_free (env0) ;
return /* (tmp25) */ ;
} /* end of [__ats_fun_11] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
} __ats_fun_11_closure_type ;

ats_void_type
__ats_fun_11_clofun (ats_clo_ptr_type cloptr) {
__ats_fun_11 (((__ats_fun_11_closure_type*)cloptr)->closure_env_0) ; return ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_11_closure_init (__ats_fun_11_closure_type *p_clo, ats_ptr_type env0) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_11_clofun ;
p_clo->closure_env_0 = env0 ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_11_closure_make (ats_ptr_type env0) {
__ats_fun_11_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_11_closure_type)) ;
__ats_fun_11_closure_init (p_clo, env0) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 4182(line=177, offs=1) -- 5198(line=221, offs=2)
*/
ATSstaticdec()
ats_void_type
reader0_initize_charlst_vt_9 (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp19) ;
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_ptr_type, tmp31) ;

__ats_lab_reader0_initize_charlst_vt_9:
tmp24 = __ats_fun_10_closure_make (arg1) ;
tmp31 = __ats_fun_11_closure_make (arg1) ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), getchar) = tmp24 ;
ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), freeres) = tmp31 ;
return /* (tmp19) */ ;
} /* end of [reader0_initize_charlst_vt_9] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 5287(line=228, offs=1) -- 5620(line=240, offs=2)
*/
ATSstaticdec()
ats_void_type
reader0_uninitize_14 (ats_ref_type arg0) {
/* local vardec */
// ATSlocal_void (tmp32) ;
// ATSlocal_void (tmp33) ;
ATSlocal (ats_clo_ptr_type, tmp34) ;
// ATSlocal_void (tmp35) ;
ATSlocal (ats_clo_ptr_type, tmp36) ;
ATSlocal (ats_clo_ptr_type, tmp37) ;

__ats_lab_reader0_uninitize_14:
tmp34 = ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), freeres) ;
/* tmp33 = */ ((ats_void_type(*)(ats_clo_ptr_type))(ats_closure_fun(tmp34))) (tmp34) ;
tmp36 = ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), getchar) ;
/* tmp35 = */ atspre_cloptr_free (tmp36) ;
tmp37 = ats_select_mac(ats_ptrget_mac(pats_reader_struct, arg0), freeres) ;
/* tmp32 = */ atspre_cloptr_free (tmp37) ;
return /* (tmp32) */ ;
} /* end of [reader0_uninitize_14] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 5915(line=261, offs=1) -- 6056(line=271, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_filp (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp38) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_filp:
/* tmp38 = */ reader0_initize_filp_1 (arg0, arg1) ;
return /* (tmp38) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_filp] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 6143(line=277, offs=3) -- 6254(line=284, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_getc (ats_ref_type arg0, ats_clo_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp39) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_getc:
/* tmp39 = */ reader0_initize_getc_4 (arg0, arg1) ;
return /* (tmp39) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_getc] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/pointer.dats: 1817(line=56, offs=24) -- 1850(line=56, offs=57)
*/
ATSstaticdec()
ats_ptr_type
ptr_alloc_01070_ats_size_type () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp42) ;

__ats_lab_ptr_alloc_01070_ats_size_type:
tmp42 = atspre_ptr_alloc_tsz (sizeof(ats_size_type)) ;
return (tmp42) ;
} /* end of [ptr_alloc_01070_ats_size_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 6343(line=290, offs=3) -- 6576(line=302, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_string (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp40) ;
ATSlocal (ats_ptr_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp43) ;
ATSlocal (ats_size_type, tmp44) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_string:
tmp41 = ptr_alloc_01070_ats_size_type () ;
tmp43 = ats_selsin_mac(tmp41, atslab_2) ;
tmp44 = atspre_size1_of_int1 (0) ;
ats_ptrget_mac(ats_size_type, tmp43) = tmp44 ;
/* tmp40 = */ reader0_initize_string_6 (arg0, ats_castfn_mac(ats_ptr_type, arg1), tmp43) ;
return /* (tmp40) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_string] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/pointer.dats: 1817(line=56, offs=24) -- 1850(line=56, offs=57)
*/
ATSstaticdec()
ats_ptr_type
ptr_alloc_01070_ats_ptr_type () {
/* local vardec */
ATSlocal (ats_ptr_type, tmp47) ;

__ats_lab_ptr_alloc_01070_ats_ptr_type:
tmp47 = atspre_ptr_alloc_tsz (sizeof(ats_ptr_type)) ;
return (tmp47) ;
} /* end of [ptr_alloc_01070_ats_ptr_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 6674(line=308, offs=3) -- 6879(line=323, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_charlst_vt (ats_ref_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp48) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_charlst_vt:
tmp46 = ptr_alloc_01070_ats_ptr_type () ;
tmp48 = ats_selsin_mac(tmp46, atslab_2) ;
ats_ptrget_mac(ats_ptr_type, tmp48) = arg1 ;
/* tmp45 = */ reader0_initize_charlst_vt_9 (arg0, tmp48) ;
return /* (tmp45) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_initize_charlst_vt] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_reader.dats: 6972(line=329, offs=3) -- 7068(line=335, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_uninitize (ats_ref_type arg0) {
/* local vardec */
// ATSlocal_void (tmp49) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_uninitize:
/* tmp49 = */ reader0_uninitize_14 (arg0) ;
return /* (tmp49) */ ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__reader_uninitize] */

/* static load function */

// extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__staload (void) ;
extern ats_void_type ATS_2d0_2e2_2e12_2libc_2SATS_2stdio_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__staload_flag = 1 ;

// _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_atspre_2edats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2esats__staload () ;
ATS_2d0_2e2_2e12_2libc_2SATS_2stdio_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__staload () ;

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
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats____assert_prfck () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__reader0_encode_prfck () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_reader_2edats__reader0_decode_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_reader_dats.c] */
