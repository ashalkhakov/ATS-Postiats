/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2014-8-19:  1h: 5m
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

#include "libc/CATS/string.cats"

#include "libc/CATS/errno.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_location.cats"

#include "pats_lexbuf.cats"

#include "pats_location.cats"

#include "pats_tokbuf.cats"

#include "pats_lexbuf.cats"

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

//
extern char* patsopt_ATSPKGRELOCROOT_get () ;
//

/* type definitions */
typedef struct {
ats_int_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_0 ;

typedef struct {
ats_ptr_type atslab_0 ;
ats_ptr_type atslab_1 ;
} anairiats_sum_1 ;

typedef struct {
ats_ptr_type atslab_0 ;
} anairiats_sum_2 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__Some_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_cons_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_vt_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_vt_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__Some_vt_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__DATSDEF_0) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__COMARGkey_0) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_prerr_newline) () ;
ATSextern_fun(ats_bool_type, atspre_neq_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_iadd) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_ilt) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_int1_of_size1) (ats_size_type) ;
ATSextern_fun(ats_size_type, atspre_sub_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_size1_size1) (ats_size_type, ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_prerr_string) (ats_ptr_type) ;
ATSextern_fun(ats_char_type, atspre_string_get_char_at__intsz) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, atspre_string_make_substring) (ats_ptr_type, ats_size_type, ats_size_type) ;
ATSextern_fun(ats_size_type, atspre_string_length) (ats_ptr_type) ;
ATSextern_val(ats_ptr_type, atspre_stropt_none) ;
ATSextern_fun(ats_bool_type, atspre_stropt_is_some) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_tostringf) (ats_ptr_type, ...) ;
ATSextern_fun(ats_varet_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__abort) () ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_ppush) (ats_ptr_type) ;
ATSextern_val(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__symbol_ATSPKGRELOCROOT) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_pathlst_ppush) (ats_ptr_type) ;
ATSextern_val(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_dummy) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_datsdef) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__e1xp_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__e1xp_none) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__e0xp_tr) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__the_e1xpenv_addperv) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_parse) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, getenv) (ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_ptr_type loop_1 (ats_ptr_type arg0, ats_int_type arg1, ats_int_type arg2) ;
static
ats_void_type loop_3 (ats_int_type env0, ats_ref_type arg0, ats_int_type arg1, ats_ptr_type arg2) ;
static
ats_clo_ptr_type loop_3_closure_make (ats_int_type env0) ;
static
ats_void_type loop_3_clofun (ats_clo_ptr_type cloptr, ats_ref_type arg0, ats_int_type arg1, ats_ptr_type arg2) ;
static
ats_ptr_type string_extract_7 (ats_ptr_type arg0, ats_size_type arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 2125(line=80, offs=7) -- 2366(line=86, offs=8)
*/
ATSstaticdec()
ats_ptr_type
loop_1 (ats_ptr_type arg0, ats_int_type arg1, ats_int_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp1) ;
ATSlocal (ats_bool_type, tmp2) ;
ATSlocal (ats_bool_type, tmp3) ;
ATSlocal (ats_char_type, tmp4) ;
ATSlocal (ats_int_type, tmp5) ;

__ats_lab_loop_1:
tmp2 = atspre_ilt (arg2, arg1) ;
if (tmp2) {
tmp4 = atspre_string_get_char_at__intsz (arg0, arg2) ;
tmp3 = atspre_neq_char_char (tmp4, '-') ;
if (tmp3) {
tmp1 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
ats_selptrset_mac(anairiats_sum_0, tmp1, atslab_0, arg2) ;
ats_selptrset_mac(anairiats_sum_0, tmp1, atslab_1, arg0) ;
} else {
tmp5 = atspre_iadd (arg2, 1) ;
arg0 = arg0 ;
arg1 = arg1 ;
arg2 = tmp5 ;
goto __ats_lab_loop_1 ; // tail call
} /* end of [if] */
} else {
tmp1 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
ats_selptrset_mac(anairiats_sum_0, tmp1, atslab_0, arg1) ;
ats_selptrset_mac(anairiats_sum_0, tmp1, atslab_1, arg0) ;
} /* end of [if] */
return (tmp1) ;
} /* end of [loop_1] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 2109(line=79, offs=14) -- 2505(line=92, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_parse (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;
ATSlocal (ats_size_type, tmp6) ;
ATSlocal (ats_int_type, tmp7) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_parse:
tmp6 = atspre_string_length (ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp7 = atspre_int1_of_size1 (tmp6) ;
tmp0 = loop_1 (ats_castfn_mac(ats_ptr_type, arg0), tmp7, 0) ;
return (tmp0) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_parse] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 2662(line=100, offs=7) -- 3129(line=111, offs=24)
*/
ATSstaticdec()
ats_void_type
loop_3 (ats_int_type env0, ats_ref_type arg0, ats_int_type arg1, ats_ptr_type arg2) {
/* local vardec */
// ATSlocal_void (tmp9) ;
ATSlocal (ats_bool_type, tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
ATSlocal (ats_ptr_type, tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;
ATSlocal (ats_ptr_type, tmp16) ;
// ATSlocal_void (tmp17) ;
ATSlocal (ats_int_type, tmp18) ;
// ATSlocal_void (tmp19) ;

__ats_lab_loop_3:
tmp10 = atspre_ilt (arg1, env0) ;
if (tmp10) {
tmp11 = ats_ptrget_mac(ats_ptr_type, arg2) ;
// if (tmp11 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
tmp13 = ats_caselptrind_mac(ats_ptr_type, arg0, [arg1]) ;
tmp12 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_parse (tmp13) ;
tmp15 = (ats_sum_ptr_type)0 ;
tmp14 = ATS_MALLOC(sizeof(anairiats_sum_1)) ;
ats_selptrset_mac(anairiats_sum_1, tmp14, atslab_0, tmp12) ;
ats_selptrset_mac(anairiats_sum_1, tmp14, atslab_1, tmp15) ;
// if (tmp14 == (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
tmp16 = &ats_caselptrlab_mac(anairiats_sum_1, tmp14, atslab_1) ;
tmp18 = atspre_iadd (arg1, 1) ;
/* tmp17 = */ loop_3 (env0, arg0, tmp18, tmp16) ;
/* tmp19 = ats_selsin_mac(tmp17, atslab_1) */ ;
ats_ptrget_mac(ats_ptr_type, arg2) = tmp14 ;
} else {
/* empty */
} /* end of [if] */
return /* (tmp9) */ ;
} /* end of [loop_3] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_int_type closure_env_0 ;
} loop_3_closure_type ;

ats_void_type
loop_3_clofun (ats_clo_ptr_type cloptr, ats_ref_type arg0, ats_int_type arg1, ats_ptr_type arg2) {
loop_3 (((loop_3_closure_type*)cloptr)->closure_env_0, arg0, arg1, arg2) ; return ;
} /* end of function */

ATSinline()
ats_void_type
loop_3_closure_init (loop_3_closure_type *p_clo, ats_int_type env0) {
p_clo->closure_fun = (ats_fun_ptr_type)&loop_3_clofun ;
p_clo->closure_env_0 = env0 ;
return ;
} /* end of function */

ats_clo_ptr_type
loop_3_closure_make (ats_int_type env0) {
loop_3_closure_type *p_clo = ATS_MALLOC(sizeof(loop_3_closure_type)) ;
loop_3_closure_init (p_clo, env0) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 2585(line=98, offs=7) -- 3276(line=117, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarglst_parse (ats_int_type arg0, ats_ref_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp20) ;
// ATSlocal_void (tmp21) ;
// ATSlocal_void (tmp22) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarglst_parse:
/* ats_ptr_type tmp20 ; */
tmp20 = (ats_sum_ptr_type)0 ;
/* tmp21 = */ loop_3 (arg0, arg1, 0, (&tmp20)) ;
/* tmp22 = ats_selsin_mac(tmp21, atslab_1) */ ;
tmp8 = tmp20 ;
return (tmp8) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarglst_parse] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 3352(line=122, offs=16) -- 3542(line=128, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_warning (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp23) ;
// ATSlocal_void (tmp24) ;
// ATSlocal_void (tmp25) ;
// ATSlocal_void (tmp26) ;
// ATSlocal_void (tmp27) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_warning:
/* tmp24 = */ atspre_prerr_string (ATSstrcst("waring(ATS)")) ;
/* tmp25 = */ atspre_prerr_string (ATSstrcst(": unrecognized command line argument [")) ;
/* tmp26 = */ atspre_prerr_string (arg0) ;
/* tmp27 = */ atspre_prerr_string (ATSstrcst("] is ignored.")) ;
/* tmp23 = */ atspre_prerr_newline () ;
return /* (tmp23) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__comarg_warning] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 3615(line=133, offs=14) -- 3679(line=134, offs=56)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__is_DATS_flag (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp28) ;
ATSlocal (ats_bool_type, tmp29) ;
ATSlocal (ats_int_type, tmp30) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__is_DATS_flag:
tmp30 = atslib_strncmp (arg0, ATSstrcst("-DATS"), 5) ;
tmp29 = atspre_eq_int_int (tmp30, 0) ;
if (tmp29) {
tmp28 = ats_true_bool ;
} else {
tmp28 = ats_false_bool ;
} /* end of [if] */
return (tmp28) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__is_DATS_flag] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 3729(line=138, offs=14) -- 3793(line=139, offs=56)
*/
ATSglobaldec()
ats_bool_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__is_IATS_flag (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp31) ;
ATSlocal (ats_bool_type, tmp32) ;
ATSlocal (ats_int_type, tmp33) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__is_IATS_flag:
tmp33 = atslib_strncmp (arg0, ATSstrcst("-IATS"), 5) ;
tmp32 = atspre_eq_int_int (tmp33, 0) ;
if (tmp32) {
tmp31 = ats_true_bool ;
} else {
tmp31 = ats_false_bool ;
} /* end of [if] */
return (tmp31) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__is_IATS_flag] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 3851(line=146, offs=4) -- 4194(line=162, offs=4)
*/
ATSstaticdec()
ats_ptr_type
string_extract_7 (ats_ptr_type arg0, ats_size_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp34) ;
ATSlocal (ats_size_type, tmp35) ;
ATSlocal (ats_bool_type, tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
ATSlocal (ats_size_type, tmp38) ;

__ats_lab_string_extract_7:
tmp35 = atspre_string_length (ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp36 = atspre_gt_size1_size1 (tmp35, ats_castfn_mac(ats_size_type, arg1)) ;
if (tmp36) {
tmp38 = atspre_sub_size1_size1 (tmp35, ats_castfn_mac(ats_size_type, arg1)) ;
tmp37 = atspre_string_make_substring (ats_castfn_mac(ats_ptr_type, arg0), ats_castfn_mac(ats_size_type, arg1), tmp38) ;
tmp34 = ats_castfn_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, tmp37)) ;
} else {
tmp34 = atspre_stropt_none ;
} /* end of [if] */
return (tmp34) ;
} /* end of [string_extract_7] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 4260(line=167, offs=14) -- 4295(line=167, offs=49)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__DATS_extract (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp39) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__DATS_extract:
tmp39 = string_extract_7 (arg0, 5) ;
return (tmp39) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__DATS_extract] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 4319(line=169, offs=14) -- 4354(line=169, offs=49)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__IATS_extract (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp40) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__IATS_extract:
tmp40 = string_extract_7 (arg0, 5) ;
return (tmp40) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__IATS_extract] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 4427(line=176, offs=18) -- 5048(line=202, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_DATS_def (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
ATSlocal (ats_ptr_type, tmp43) ;
ATSlocal (ats_ptr_type, tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;
// ATSlocal_void (tmp48) ;
// ATSlocal_void (tmp49) ;
// ATSlocal_void (tmp50) ;
// ATSlocal_void (tmp51) ;
// ATSlocal_void (tmp52) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_DATS_def:
tmp42 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_string (ats_castfn_mac(ats_ptr_type, arg0), &_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_datsdef) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (tmp42 == (ats_sum_ptr_type)0) { goto __ats_lab_3_0 ; }
__ats_lab_0_1:
tmp43 = ats_caselptrlab_mac(anairiats_sum_2, tmp42, atslab_0) ;
ATS_FREE(tmp42) ;
// 
tmp44 = ats_caselptrlab_mac(anairiats_sum_1, tmp43, atslab_0) ;
tmp45 = ats_caselptrlab_mac(anairiats_sum_1, tmp43, atslab_1) ;
do {
/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (tmp45 == (ats_sum_ptr_type)0) { goto __ats_lab_2_0 ; }
__ats_lab_1_1:
tmp47 = ats_caselptrlab_mac(anairiats_sum_2, tmp45, atslab_0) ;
tmp46 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__e0xp_tr (tmp47) ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
// if (tmp45 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_2_1:
tmp46 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__e1xp_none (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_dummy) ;
break ;
} while (0) ;
/* tmp41 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__the_e1xpenv_addperv (tmp44, tmp46) ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
// if (tmp42 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_3_1:
/* tmp48 = */ atspre_prerr_string (ATSstrcst("error(ATS)")) ;
/* tmp49 = */ atspre_prerr_string (ATSstrcst(": the command-line argument [")) ;
/* tmp50 = */ atspre_prerr_string (ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp51 = */ atspre_prerr_string (ATSstrcst("] cannot be properly parsed.")) ;
/* tmp52 = */ atspre_prerr_newline () ;
/* tmp41 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__abort () ;
break ;
} while (0) ;
return /* (tmp41) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_DATS_def] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 5168(line=209, offs=18) -- 5286(line=216, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_IATS_dir (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp53) ;
// ATSlocal_void (tmp54) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_IATS_dir:
/* tmp54 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_pathlst_ppush (arg0) ;
/* tmp53 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__the_IATS_dirlst_ppush (arg0) ;
return /* (tmp53) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_IATS_dir] */

/*
// /home/hwxi/research/Postiats/git/src/pats_comarg.dats: 5457(line=229, offs=25) -- 6200(line=263, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_ATSPKGRELOCROOT () {
/* local vardec */
// ATSlocal_void (tmp55) ;
ATSlocal (ats_ptr_type, tmp56) ;
ATSlocal (ats_bool_type, tmp57) ;
ATSlocal (ats_ptr_type, tmp58) ;
ATSlocal (ats_ptr_type, tmp59) ;
ATSlocal (ats_bool_type, tmp60) ;
ATSlocal (ats_ptr_type, tmp61) ;
ATSlocal (ats_ptr_type, tmp62) ;
ATSlocal (ats_ptr_type, tmp63) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_ATSPKGRELOCROOT:
tmp56 = patsopt_ATSPKGRELOCROOT_get () ;
tmp57 = atspre_stropt_is_some (tmp56) ;
if (tmp57) {
tmp58 = ats_castfn_mac(ats_ptr_type, tmp56) ;
} else {
tmp59 = getenv (ATSstrcst("USER")) ;
tmp60 = atspre_stropt_is_some (tmp59) ;
if (tmp60) {
tmp61 = ats_castfn_mac(ats_ptr_type, tmp59) ;
} else {
tmp61 = ATSstrcst("$USER") ;
} /* end of [if] */
tmp62 = atspre_tostringf (ATSstrcst("/tmp/.ATSPKGRELOCROOT-%s"), tmp61) ;
tmp58 = ats_castfn_mac(ats_ptr_type, tmp62) ;
} /* end of [if] */
tmp63 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__e1xp_string (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_dummy, tmp58) ;
/* tmp55 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__the_e1xpenv_addperv (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__symbol_ATSPKGRELOCROOT, tmp63) ;
return /* (tmp55) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__process_ATSPKGRELOCROOT] */

/* static load function */

// extern ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2unsafe_2esats__staload (void) ;
extern ats_void_type ATS_2d0_2e2_2e11_2libc_2SATS_2string_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__staload_flag = 1 ;

// ATS_2d0_2e2_2e11_2prelude_2SATS_2unsafe_2esats__staload () ;
ATS_2d0_2e2_2e11_2libc_2SATS_2string_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_global_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_comarg_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_comarg_dats.c] */
