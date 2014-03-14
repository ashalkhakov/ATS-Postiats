/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2014-3-13: 15h:56m
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

#include "libc/CATS/stdio.cats"

#include "libc/sys/CATS/types.cats"

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
/* external codes at top */
/* type definitions */
typedef struct {
ats_ptr_type atslab_0 ;
} anairiats_sum_0 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__list_nil_1) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_vt_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__Some_vt_1) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_void_type, atspre_prerr_newline) () ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_prerr_string) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atslib_fopen_exn) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_varet_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__abort) () ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__symbol_get_name) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_get_fullname) (ats_ptr_type) ;
ATSextern_val(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_dummy) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_filenamelst_pop) () ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_filenamelst_push) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_filenamelst_ppush) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filenameopt_make_local) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__the_lexerrlst_clear) () ;
ATSextern_fun(ats_int_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__fprint_the_lexerrlst) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_initialize_filp) (ats_ref_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_initialize_getc) (ats_ref_type, ats_clo_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_initialize_string) (ats_ref_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_uninitialize) (ats_ref_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__the_parerrlst_clear) () ;
ATSextern_fun(ats_int_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__fprint_the_parerrlst) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_EOF) (ats_ref_type, ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_toplevel_sta) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_toplevel_dyn) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_tokbuf_toplevel) (ats_int_type, ats_ref_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_fileref_toplevel) (ats_int_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_filename_toplevel) (ats_int_type, ats_ptr_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
extern
ats_void_type ATS_2d0_2e2_2e11_2prelude_2basics_dyn_2esats__file_mode_lte_r_r_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_int_type __ats_fun_5 (ats_ptr_type env0) ;
static
ats_clo_ptr_type __ats_fun_5_closure_make (ats_ptr_type env0) ;
static
ats_int_type __ats_fun_5_clofun (ats_clo_ptr_type cloptr) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing.dats: 1774(line=59, offs=3) -- 2074(line=68, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_string (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;
ATSlocal (pats_tokbuf_struct, tmp1) ;
// ATSlocal_void (tmp2) ;
ATSlocal (ats_int_type, tmp3) ;
ATSlocal (ats_ptr_type, tmp4) ;
ATSlocal (ats_ptr_type, tmp5) ;
// ATSlocal_void (tmp6) ;
ATSlocal (ats_bool_type, tmp7) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_string:
/* pats_tokbuf_struct tmp1 ; */
/* tmp2 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_initialize_string ((&tmp1), arg0) ;
/* ats_int_type tmp3 ; */
tmp3 = 0 ;
tmp4 = ((ats_ptr_type(*)(ats_ref_type, ats_int_type, ats_ref_type))arg1) ((&tmp1), 0, (&tmp3)) ;
tmp5 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_EOF ((&tmp1), 0, (&tmp3)) ;
/* tmp6 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_uninitialize ((&tmp1)) ;
tmp7 = atspre_eq_int_int (tmp3, 0) ;
if (tmp7) {
tmp0 = ATS_MALLOC(sizeof(anairiats_sum_0)) ;
ats_selptrset_mac(anairiats_sum_0, tmp0, atslab_0, tmp4) ;
} else {
tmp0 = (ats_sum_ptr_type)0 ;
} /* end of [if] */
return (tmp0) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_string] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing.dats: 2167(line=74, offs=3) -- 2567(line=86, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_tokbuf_toplevel (ats_int_type arg0, ats_ref_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_int_type, tmp9) ;
// ATSlocal_void (tmp10) ;
// ATSlocal_void (tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
ATSlocal (ats_bool_type, tmp13) ;
ATSlocal (ats_int_type, tmp14) ;
ATSlocal (ats_int_type, tmp15) ;
// ATSlocal_void (tmp16) ;
ATSlocal (ats_bool_type, tmp17) ;
ATSlocal (ats_int_type, tmp18) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_tokbuf_toplevel:
/* ats_int_type tmp9 ; */
tmp9 = 0 ;
/* tmp10 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__the_lexerrlst_clear () ;
/* tmp11 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__the_parerrlst_clear () ;
tmp13 = atspre_eq_int_int (arg0, 0) ;
if (tmp13) {
tmp12 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_toplevel_sta (arg1, (&tmp9)) ;
} else {
tmp12 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__p_toplevel_dyn (arg1, (&tmp9)) ;
} /* end of [if] */
tmp14 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__fprint_the_lexerrlst (stderr) ;
tmp15 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__fprint_the_parerrlst (stderr) ;
tmp18 = atspre_add_int_int (tmp14, tmp15) ;
tmp17 = atspre_gt_int_int (tmp18, 0) ;
if (tmp17) {
/* tmp16 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__abort () ;
} else {
/* empty */
} /* end of [if] */
tmp8 = tmp12 ;
return (tmp8) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_tokbuf_toplevel] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing.dats: 2661(line=92, offs=3) -- 3232(line=119, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_filename_toplevel (ats_int_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp19) ;
ATSlocal (pats_tokbuf_struct, tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_ptr_type, tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;
// ATSlocal_void (tmp25) ;
// ATSlocal_void (tmp26) ;
// ATSlocal_void (tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
// ATSlocal_void (tmp29) ;
// ATSlocal_void (tmp30) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_filename_toplevel:
/* pats_tokbuf_struct tmp20 ; */
tmp21 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_get_fullname (arg1) ;
tmp22 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__symbol_get_name (tmp21) ;
tmp23 = atslib_fopen_exn (tmp22, "r") ;
tmp24 = ats_selsin_mac(tmp23, atslab_1) ;
/* tmp25 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_initialize_filp ((&tmp20), tmp24) ;
/* tmp26 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_filenamelst_push (arg1) ;
/* tmp27 = ats_selsin_mac(tmp26, atslab_1) */ ;
tmp28 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_tokbuf_toplevel (arg0, (&tmp20)) ;
/* tmp29 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_filenamelst_pop () ;
/* tmp30 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_uninitialize ((&tmp20)) ;
tmp19 = tmp28 ;
return (tmp19) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_filename_toplevel] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing.dats: 3317(line=123, offs=3) -- 3961(line=151, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_givename_toplevel (ats_int_type arg0, ats_ptr_type arg1, ats_ref_type arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;
ATSlocal (ats_ptr_type, tmp34) ;
// ATSlocal_void (tmp35) ;
// ATSlocal_void (tmp36) ;
// ATSlocal_void (tmp37) ;
// ATSlocal_void (tmp38) ;
// ATSlocal_void (tmp39) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_givename_toplevel:
tmp32 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filenameopt_make_local (arg1) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
if (tmp32 == (ats_sum_ptr_type)0) { goto __ats_lab_1_0 ; }
__ats_lab_0_1:
tmp33 = ats_caselptrlab_mac(anairiats_sum_0, tmp32, atslab_0) ;
ATS_FREE(tmp32) ;
ats_ptrget_mac(ats_ptr_type, arg2) = tmp33 ;
tmp34 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_filename_toplevel (arg0, tmp33) ;
/* tmp35 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__the_filenamelst_ppush (tmp33) ;
tmp31 = tmp34 ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
// if (tmp32 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_1_1:
ats_ptrget_mac(ats_ptr_type, arg2) = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_dummy ;
/* tmp36 = */ atspre_prerr_string (ATSstrcst("error(ATS): the file of the name [")) ;
/* tmp37 = */ atspre_prerr_string (arg1) ;
/* tmp38 = */ atspre_prerr_string (ATSstrcst("] is not available.")) ;
/* tmp39 = */ atspre_prerr_newline () ;
tmp31 = (ats_sum_ptr_type)0 ;
break ;
} while (0) ;
return (tmp31) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_givename_toplevel] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing.dats: 4156(line=160, offs=11) -- 4197(line=160, offs=52)
*/
ATSstaticdec()
ats_int_type
__ats_fun_5 (ats_ptr_type env0) {
/* local vardec */
ATSlocal (ats_int_type, tmp43) ;

__ats_lab___ats_fun_5:
tmp43 = atslib_fgetc_err (env0) ;
return (tmp43) ;
} /* end of [__ats_fun_5] */

typedef struct {
ats_fun_ptr_type closure_fun ;
ats_ptr_type closure_env_0 ;
} __ats_fun_5_closure_type ;

ats_int_type
__ats_fun_5_clofun (ats_clo_ptr_type cloptr) {
return __ats_fun_5 (((__ats_fun_5_closure_type*)cloptr)->closure_env_0) ;
} /* end of function */

ATSinline()
ats_void_type
__ats_fun_5_closure_init (__ats_fun_5_closure_type *p_clo, ats_ptr_type env0) {
p_clo->closure_fun = (ats_fun_ptr_type)&__ats_fun_5_clofun ;
p_clo->closure_env_0 = env0 ;
return ;
} /* end of function */

ats_clo_ptr_type
__ats_fun_5_closure_make (ats_ptr_type env0) {
__ats_fun_5_closure_type *p_clo = ATS_MALLOC(sizeof(__ats_fun_5_closure_type)) ;
__ats_fun_5_closure_init (p_clo, env0) ;
return (ats_clo_ptr_type)p_clo ;
} /* end of function */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing.dats: 4065(line=157, offs=3) -- 4291(line=163, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_fileref_toplevel (ats_int_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp40) ;
ATSlocal (pats_tokbuf_struct, tmp41) ;
// ATSlocal_void (tmp42) ;
ATSlocal (ats_ptr_type, tmp44) ;
// ATSlocal_void (tmp45) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_fileref_toplevel:
/* pats_tokbuf_struct tmp41 ; */
/* tmp42 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_initialize_getc ((&tmp41), __ats_fun_5_closure_make (arg1)) ;
tmp44 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_tokbuf_toplevel (arg0, (&tmp41)) ;
/* tmp45 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__tokbuf_uninitialize ((&tmp41)) ;
tmp40 = tmp44 ;
return (tmp40) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_fileref_toplevel] */

/*
// /home/hwxi/research/Postiats/git/src/pats_parsing.dats: 4372(line=167, offs=3) -- 4432(line=168, offs=50)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_stdin_toplevel (ats_int_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp46) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_stdin_toplevel:
tmp46 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_fileref_toplevel (arg0, stdin) ;
return (tmp46) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__parse_from_stdin_toplevel] */

/* static load function */

extern ats_void_type ATS_2d0_2e2_2e11_2libc_2SATS_2stdio_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__staload_flag = 1 ;

ATS_2d0_2e2_2e11_2libc_2SATS_2stdio_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_error_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
ATS_2d0_2e2_2e11_2prelude_2basics_dyn_2esats__file_mode_lte_r_r_prfck () ;
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */

/* marking external values for GC */

/* code for dynamic loading */
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_parsing_dats.c] */
