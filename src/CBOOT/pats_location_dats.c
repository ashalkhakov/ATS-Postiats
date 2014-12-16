/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2014-12-16: 15h:50m
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
/* external codes at top */
/* type definitions */
typedef
struct {
ats_ptr_type atslab_filename ;
ats_lint_type atslab_beg_ntot ;
ats_int_type atslab_beg_nrow ;
ats_int_type atslab_beg_ncol ;
ats_lint_type atslab_end_ntot ;
ats_int_type atslab_end_nrow ;
ats_int_type atslab_end_ncol ;
} anairiats_rec_0 ;

/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
ATSextern_fun(ats_int_type, atspre_int_of_char) (ats_char_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_sub_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_eq_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_int) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_lint_type, atspre_lint_of_uint) (ats_uint_type) ;
ATSextern_fun(ats_lint_type, atspre_add_lint_lint) (ats_lint_type, ats_lint_type) ;
ATSextern_fun(ats_lint_type, atspre_sub_lint_lint) (ats_lint_type, ats_lint_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_lint_lint) (ats_lint_type, ats_lint_type) ;
ATSextern_fun(ats_bool_type, atspre_lte_lint_lint) (ats_lint_type, ats_lint_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_lint_lint) (ats_lint_type, ats_lint_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_lint) (ats_ptr_type, ats_lint_type) ;
ATSextern_fun(ats_void_type, atspre_fprint_string) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, atspre_fprintf_exn) (ats_ptr_type, ats_ptr_type, ...) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__fprint_filename_full) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__fprint2_filename_full) (ats_ptr_type, ats_ptr_type) ;
ATSextern_val(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_dummy) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_get_current) () ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_position) (ats_ptr_type, pats_position_struct) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_locrange) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_fil_pos_pos) (ats_ptr_type, pats_position_struct, pats_position_struct) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__sasp__location_type = 0 ;
int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__sasp__position_t0ype = 0 ;

/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
ATSglobal(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_dummy) ;

/* internal function declarations */
static
ats_bool_type location_is_none_24 (ats_ptr_type arg0) ;
static
ats_ptr_type location_combine_main_25 (ats_ptr_type arg0, ats_ptr_type arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
ATSstatic (ats_ptr_type, statmp78) ;

/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 1721(line=58, offs=3) -- 1762(line=58, offs=44)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__print_position (pats_position_struct arg0) {
/* local vardec */
// ATSlocal_void (tmp0) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__print_position:
/* tmp0 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_position (stdout, arg0) ;
return /* (tmp0) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__print_position] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 1815(line=64, offs=3) -- 2000(line=77, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_position (ats_ptr_type arg0, pats_position_struct arg1) {
/* local vardec */
// ATSlocal_void (tmp1) ;
ATSlocal (ats_lint_type, tmp2) ;
ATSlocal (ats_int_type, tmp3) ;
ATSlocal (ats_int_type, tmp4) ;
ATSlocal (ats_lint_type, tmp5) ;
ATSlocal (ats_int_type, tmp6) ;
ATSlocal (ats_int_type, tmp7) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_position:
tmp2 = ats_select_mac(arg1, ntot) ;
tmp3 = ats_select_mac(arg1, nrow) ;
tmp4 = ats_select_mac(arg1, ncol) ;
tmp5 = atspre_add_lint_lint (tmp2, 1L) ;
tmp6 = atspre_add_int_int (tmp3, 1) ;
tmp7 = atspre_add_int_int (tmp4, 1) ;
/* tmp1 = */ atspre_fprintf_exn (arg0, ATSstrcst("%li(line=%i, offs=%i)"), tmp5, tmp6, tmp7) ;
return /* (tmp1) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_position] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 2079(line=81, offs=29) -- 2095(line=81, offs=45)
*/
ATSglobaldec()
ats_lint_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_ntot (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_lint_type, tmp8) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_ntot:
tmp8 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) ;
return (tmp8) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_ntot] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 2124(line=82, offs=29) -- 2140(line=82, offs=45)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_nrow (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp9) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_nrow:
tmp9 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), nrow) ;
return (tmp9) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_nrow] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 2169(line=83, offs=29) -- 2185(line=83, offs=45)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_ncol (ats_ref_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp10) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_ncol:
tmp10 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) ;
return (tmp10) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_get_ncol] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 2232(line=89, offs=1) -- 2362(line=95, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_init (ats_ref_type arg0, ats_lint_type arg1, ats_int_type arg2, ats_int_type arg3) {
/* local vardec */
// ATSlocal_void (tmp11) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_init:
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) = arg1 ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), nrow) = arg2 ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) = arg3 ;
return /* (tmp11) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_init] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 2417(line=99, offs=1) -- 2552(line=105, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_copy (ats_ref_type arg0, ats_ref_type arg1) {
/* local vardec */
// ATSlocal_void (tmp12) ;
ATSlocal (ats_lint_type, tmp13) ;
ATSlocal (ats_int_type, tmp14) ;
ATSlocal (ats_int_type, tmp15) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_copy:
tmp13 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg1), ntot) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) = tmp13 ;
tmp14 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg1), nrow) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), nrow) = tmp14 ;
tmp15 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg1), ncol) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) = tmp15 ;
return /* (tmp12) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_copy] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 2636(line=111, offs=3) -- 2992(line=131, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_incby_char (ats_ref_type arg0, ats_int_type arg1) {
/* local vardec */
// ATSlocal_void (tmp16) ;
ATSlocal (ats_bool_type, tmp17) ;
ATSlocal (ats_lint_type, tmp18) ;
ATSlocal (ats_lint_type, tmp19) ;
ATSlocal (ats_bool_type, tmp20) ;
ATSlocal (ats_int_type, tmp21) ;
ATSlocal (ats_int_type, tmp22) ;
ATSlocal (ats_int_type, tmp23) ;
ATSlocal (ats_int_type, tmp24) ;
ATSlocal (ats_int_type, tmp25) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_incby_char:
tmp17 = atspre_gte_int_int (arg1, 0) ;
if (tmp17) {
tmp19 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) ;
tmp18 = atspre_add_lint_lint (tmp19, 1L) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) = tmp18 ;
tmp21 = atspre_int_of_char ('\n') ;
tmp20 = atspre_eq_int_int (arg1, tmp21) ;
if (tmp20) {
tmp23 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), nrow) ;
tmp22 = atspre_add_int_int (tmp23, 1) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), nrow) = tmp22 ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) = 0 ;
} else {
tmp25 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) ;
tmp24 = atspre_add_int_int (tmp25, 1) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) = tmp24 ;
} /* end of [if] */
} else {
/* empty */
} /* end of [if] */
return /* (tmp16) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_incby_char] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 3080(line=137, offs=3) -- 3244(line=144, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_decby_count (ats_ref_type arg0, ats_uint_type arg1) {
/* local vardec */
// ATSlocal_void (tmp26) ;
ATSlocal (ats_lint_type, tmp27) ;
ATSlocal (ats_lint_type, tmp28) ;
ATSlocal (ats_lint_type, tmp29) ;
ATSlocal (ats_int_type, tmp30) ;
ATSlocal (ats_int_type, tmp31) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_decby_count:
tmp28 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) ;
tmp29 = atspre_lint_of_uint (arg1) ;
tmp27 = atspre_sub_lint_lint (tmp28, tmp29) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) = tmp27 ;
tmp31 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) ;
tmp30 = atspre_sub_int_int (tmp31, ats_castfn_mac(ats_int_type, arg1)) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) = tmp30 ;
return /* (tmp26) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_decby_count] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 3312(line=148, offs=3) -- 3476(line=155, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_incby_count (ats_ref_type arg0, ats_uint_type arg1) {
/* local vardec */
// ATSlocal_void (tmp32) ;
ATSlocal (ats_lint_type, tmp33) ;
ATSlocal (ats_lint_type, tmp34) ;
ATSlocal (ats_lint_type, tmp35) ;
ATSlocal (ats_int_type, tmp36) ;
ATSlocal (ats_int_type, tmp37) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_incby_count:
tmp34 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) ;
tmp35 = atspre_lint_of_uint (arg1) ;
tmp33 = atspre_add_lint_lint (tmp34, tmp35) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ntot) = tmp33 ;
tmp37 = ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) ;
tmp36 = atspre_add_int_int (tmp37, ats_castfn_mac(ats_int_type, arg1)) ;
ats_select_mac(ats_ptrget_mac(pats_position_struct, arg0), ncol) = tmp36 ;
return /* (tmp32) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__position_incby_count] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 3826(line=174, offs=20) -- 3846(line=174, offs=40)
*/
ATSglobaldec()
ats_lint_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_get_bchar (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_lint_type, tmp38) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_get_bchar:
tmp38 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ntot) ;
return (tmp38) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_get_bchar] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 3897(line=179, offs=19) -- 3917(line=179, offs=39)
*/
ATSglobaldec()
ats_int_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_beg_nrow (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_int_type, tmp39) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_beg_nrow:
tmp39 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_nrow) ;
return (tmp39) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_beg_nrow] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 3968(line=184, offs=19) -- 3988(line=184, offs=39)
*/
ATSglobaldec()
ats_lint_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_beg_ntot (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_lint_type, tmp40) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_beg_ntot:
tmp40 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ntot) ;
return (tmp40) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_beg_ntot] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 4017(line=186, offs=19) -- 4037(line=186, offs=39)
*/
ATSglobaldec()
ats_lint_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_end_ntot (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_lint_type, tmp41) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_end_ntot:
tmp41 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ntot) ;
return (tmp41) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_end_ntot] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 4092(line=191, offs=23) -- 4112(line=191, offs=43)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_get_filename (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp42) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_get_filename:
tmp42 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_filename) ;
return (tmp42) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_get_filename] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 4162(line=196, offs=16) -- 4203(line=196, offs=57)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__print_location (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp43) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__print_location:
/* tmp43 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (stdout, arg0) ;
return /* (tmp43) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__print_location] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 4229(line=198, offs=16) -- 4270(line=198, offs=57)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__prerr_location (ats_ptr_type arg0) {
/* local vardec */
// ATSlocal_void (tmp44) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__prerr_location:
/* tmp44 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (stderr, arg0) ;
return /* (tmp44) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__prerr_location] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 4323(line=204, offs=3) -- 4471(line=209, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
// ATSlocal_void (tmp47) ;
// ATSlocal_void (tmp48) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location:
tmp46 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_filename) ;
/* tmp47 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__fprint_filename_full (arg0, tmp46) ;
/* tmp48 = */ atspre_fprint_string (arg0, ATSstrcst(": ")) ;
/* tmp45 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_locrange (arg0, arg1) ;
return /* (tmp45) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_location] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 4553(line=215, offs=3) -- 5113(line=235, offs=2)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_locrange (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp49) ;
// ATSlocal_void (tmp50) ;
ATSlocal (ats_lint_type, tmp51) ;
ATSlocal (ats_lint_type, tmp52) ;
// ATSlocal_void (tmp53) ;
// ATSlocal_void (tmp54) ;
ATSlocal (ats_int_type, tmp55) ;
ATSlocal (ats_int_type, tmp56) ;
// ATSlocal_void (tmp57) ;
// ATSlocal_void (tmp58) ;
ATSlocal (ats_int_type, tmp59) ;
ATSlocal (ats_int_type, tmp60) ;
// ATSlocal_void (tmp61) ;
// ATSlocal_void (tmp62) ;
// ATSlocal_void (tmp63) ;
ATSlocal (ats_lint_type, tmp64) ;
ATSlocal (ats_lint_type, tmp65) ;
// ATSlocal_void (tmp66) ;
// ATSlocal_void (tmp67) ;
ATSlocal (ats_int_type, tmp68) ;
ATSlocal (ats_int_type, tmp69) ;
// ATSlocal_void (tmp70) ;
// ATSlocal_void (tmp71) ;
ATSlocal (ats_int_type, tmp72) ;
ATSlocal (ats_int_type, tmp73) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_locrange:
tmp52 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_ntot) ;
tmp51 = atspre_add_lint_lint (tmp52, 1L) ;
/* tmp50 = */ atspre_fprint_lint (arg0, tmp51) ;
/* tmp53 = */ atspre_fprint_string (arg0, ATSstrcst("(line=")) ;
tmp56 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_nrow) ;
tmp55 = atspre_add_int_int (tmp56, 1) ;
/* tmp54 = */ atspre_fprint_int (arg0, tmp55) ;
/* tmp57 = */ atspre_fprint_string (arg0, ATSstrcst(", offs=")) ;
tmp60 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_ncol) ;
tmp59 = atspre_add_int_int (tmp60, 1) ;
/* tmp58 = */ atspre_fprint_int (arg0, tmp59) ;
/* tmp61 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
/* tmp62 = */ atspre_fprint_string (arg0, ATSstrcst(" -- ")) ;
tmp65 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_end_ntot) ;
tmp64 = atspre_add_lint_lint (tmp65, 1L) ;
/* tmp63 = */ atspre_fprint_lint (arg0, tmp64) ;
/* tmp66 = */ atspre_fprint_string (arg0, ATSstrcst("(line=")) ;
tmp69 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_end_nrow) ;
tmp68 = atspre_add_int_int (tmp69, 1) ;
/* tmp67 = */ atspre_fprint_int (arg0, tmp68) ;
/* tmp70 = */ atspre_fprint_string (arg0, ATSstrcst(", offs=")) ;
tmp73 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_end_ncol) ;
tmp72 = atspre_add_int_int (tmp73, 1) ;
/* tmp71 = */ atspre_fprint_int (arg0, tmp72) ;
/* tmp49 = */ atspre_fprint_string (arg0, ATSstrcst(")")) ;
return /* (tmp49) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_locrange] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 5196(line=241, offs=3) -- 5346(line=246, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint2_location (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp74) ;
ATSlocal (ats_ptr_type, tmp75) ;
// ATSlocal_void (tmp76) ;
// ATSlocal_void (tmp77) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint2_location:
tmp75 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_filename) ;
/* tmp76 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__fprint2_filename_full (arg0, tmp75) ;
/* tmp77 = */ atspre_fprint_string (arg0, ATSstrcst(": ")) ;
/* tmp74 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_locrange (arg0, arg1) ;
return /* (tmp74) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint2_location] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 5643(line=266, offs=3) -- 5755(line=270, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_pos_pos (pats_position_struct arg0, pats_position_struct arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp79) ;
ATSlocal (ats_ptr_type, tmp80) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_pos_pos:
tmp80 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_get_current () ;
tmp79 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_fil_pos_pos (tmp80, arg0, arg1) ;
return (tmp79) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_pos_pos] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 5850(line=276, offs=3) -- 6022(line=284, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_fil_pos_pos (ats_ptr_type arg0, pats_position_struct arg1, pats_position_struct arg2) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp81) ;
ATSlocal (ats_lint_type, tmp82) ;
ATSlocal (ats_int_type, tmp83) ;
ATSlocal (ats_int_type, tmp84) ;
ATSlocal (ats_lint_type, tmp85) ;
ATSlocal (ats_int_type, tmp86) ;
ATSlocal (ats_int_type, tmp87) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_fil_pos_pos:
tmp82 = ats_select_mac(arg1, ntot) ;
tmp83 = ats_select_mac(arg1, nrow) ;
tmp84 = ats_select_mac(arg1, ncol) ;
tmp85 = ats_select_mac(arg2, ntot) ;
tmp86 = ats_select_mac(arg2, nrow) ;
tmp87 = ats_select_mac(arg2, ncol) ;
tmp81 = ATS_MALLOC(sizeof(anairiats_rec_0)) ;
ats_selptrset_mac(anairiats_rec_0, tmp81, atslab_filename, arg0) ;
ats_selptrset_mac(anairiats_rec_0, tmp81, atslab_beg_ntot, tmp82) ;
ats_selptrset_mac(anairiats_rec_0, tmp81, atslab_beg_nrow, tmp83) ;
ats_selptrset_mac(anairiats_rec_0, tmp81, atslab_beg_ncol, tmp84) ;
ats_selptrset_mac(anairiats_rec_0, tmp81, atslab_end_ntot, tmp85) ;
ats_selptrset_mac(anairiats_rec_0, tmp81, atslab_end_nrow, tmp86) ;
ats_selptrset_mac(anairiats_rec_0, tmp81, atslab_end_ncol, tmp87) ;

return (tmp81) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_make_fil_pos_pos] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 6109(line=290, offs=3) -- 6296(line=298, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_leftmost (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp88) ;
ATSlocal (ats_ptr_type, tmp89) ;
ATSlocal (ats_lint_type, tmp90) ;
ATSlocal (ats_int_type, tmp91) ;
ATSlocal (ats_int_type, tmp92) ;
ATSlocal (ats_lint_type, tmp93) ;
ATSlocal (ats_int_type, tmp94) ;
ATSlocal (ats_int_type, tmp95) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_leftmost:
tmp89 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_filename) ;
tmp90 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ntot) ;
tmp91 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_nrow) ;
tmp92 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ncol) ;
tmp93 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ntot) ;
tmp94 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_nrow) ;
tmp95 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ncol) ;
tmp88 = ATS_MALLOC(sizeof(anairiats_rec_0)) ;
ats_selptrset_mac(anairiats_rec_0, tmp88, atslab_filename, tmp89) ;
ats_selptrset_mac(anairiats_rec_0, tmp88, atslab_beg_ntot, tmp90) ;
ats_selptrset_mac(anairiats_rec_0, tmp88, atslab_beg_nrow, tmp91) ;
ats_selptrset_mac(anairiats_rec_0, tmp88, atslab_beg_ncol, tmp92) ;
ats_selptrset_mac(anairiats_rec_0, tmp88, atslab_end_ntot, tmp93) ;
ats_selptrset_mac(anairiats_rec_0, tmp88, atslab_end_nrow, tmp94) ;
ats_selptrset_mac(anairiats_rec_0, tmp88, atslab_end_ncol, tmp95) ;

return (tmp88) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_leftmost] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 6359(line=302, offs=3) -- 6546(line=310, offs=2)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_rightmost (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp96) ;
ATSlocal (ats_ptr_type, tmp97) ;
ATSlocal (ats_lint_type, tmp98) ;
ATSlocal (ats_int_type, tmp99) ;
ATSlocal (ats_int_type, tmp100) ;
ATSlocal (ats_lint_type, tmp101) ;
ATSlocal (ats_int_type, tmp102) ;
ATSlocal (ats_int_type, tmp103) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_rightmost:
tmp97 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_filename) ;
tmp98 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ntot) ;
tmp99 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_nrow) ;
tmp100 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ncol) ;
tmp101 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ntot) ;
tmp102 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_nrow) ;
tmp103 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ncol) ;
tmp96 = ATS_MALLOC(sizeof(anairiats_rec_0)) ;
ats_selptrset_mac(anairiats_rec_0, tmp96, atslab_filename, tmp97) ;
ats_selptrset_mac(anairiats_rec_0, tmp96, atslab_beg_ntot, tmp98) ;
ats_selptrset_mac(anairiats_rec_0, tmp96, atslab_beg_nrow, tmp99) ;
ats_selptrset_mac(anairiats_rec_0, tmp96, atslab_beg_ncol, tmp100) ;
ats_selptrset_mac(anairiats_rec_0, tmp96, atslab_end_ntot, tmp101) ;
ats_selptrset_mac(anairiats_rec_0, tmp96, atslab_end_nrow, tmp102) ;
ats_selptrset_mac(anairiats_rec_0, tmp96, atslab_end_ncol, tmp103) ;

return (tmp96) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_rightmost] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 6610(line=317, offs=1) -- 6677(line=320, offs=33)
*/
ATSstaticdec()
ats_bool_type
location_is_none_24 (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp104) ;
ATSlocal (ats_lint_type, tmp105) ;

__ats_lab_location_is_none_24:
tmp105 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ntot) ;
tmp104 = atspre_lt_lint_lint (tmp105, 0L) ;
return (tmp104) ;
} /* end of [location_is_none_24] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 6682(line=323, offs=1) -- 7767(line=365, offs=6)
*/
ATSstaticdec()
ats_ptr_type
location_combine_main_25 (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp106) ;
ATSlocal (ats_lint_type, tmp107) ;
ATSlocal (ats_int_type, tmp108) ;
ATSlocal (ats_int_type, tmp109) ;
ATSlocal (ats_lint_type, tmp110) ;
ATSlocal (ats_int_type, tmp111) ;
ATSlocal (ats_int_type, tmp112) ;
ATSlocal (ats_bool_type, tmp114) ;
ATSlocal (ats_lint_type, tmp115) ;
ATSlocal (ats_lint_type, tmp116) ;
ATSlocal (ats_int_type, tmp117) ;
ATSlocal (ats_int_type, tmp118) ;
ATSlocal (ats_lint_type, tmp119) ;
ATSlocal (ats_int_type, tmp120) ;
ATSlocal (ats_int_type, tmp121) ;
ATSlocal (ats_lint_type, tmp122) ;
ATSlocal (ats_bool_type, tmp124) ;
ATSlocal (ats_lint_type, tmp125) ;
ATSlocal (ats_lint_type, tmp126) ;
ATSlocal (ats_int_type, tmp127) ;
ATSlocal (ats_int_type, tmp128) ;
ATSlocal (ats_lint_type, tmp129) ;
ATSlocal (ats_int_type, tmp130) ;
ATSlocal (ats_int_type, tmp131) ;
ATSlocal (ats_lint_type, tmp132) ;
ATSlocal (ats_ptr_type, tmp133) ;

__ats_lab_location_combine_main_25:
/* ats_lint_type tmp107 ; */
/* ats_int_type tmp108 ; */
/* ats_int_type tmp109 ; */
/* ats_lint_type tmp110 ; */
/* ats_int_type tmp111 ; */
/* ats_int_type tmp112 ; */
tmp115 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ntot) ;
tmp116 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_ntot) ;
tmp114 = atspre_lte_lint_lint (tmp115, tmp116) ;
if (tmp114) {
tmp117 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_nrow) ;
tmp108 = tmp117 ;
tmp118 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ncol) ;
tmp109 = tmp118 ;
tmp119 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_beg_ntot) ;
tmp107 = tmp119 ;
} else {
tmp120 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_nrow) ;
tmp108 = tmp120 ;
tmp121 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_ncol) ;
tmp109 = tmp121 ;
tmp122 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_ntot) ;
tmp107 = tmp122 ;
} /* end of [if] */
tmp125 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ntot) ;
tmp126 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_end_ntot) ;
tmp124 = atspre_gte_lint_lint (tmp125, tmp126) ;
if (tmp124) {
tmp127 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_nrow) ;
tmp111 = tmp127 ;
tmp128 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ncol) ;
tmp112 = tmp128 ;
tmp129 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_end_ntot) ;
tmp110 = tmp129 ;
} else {
tmp130 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_end_nrow) ;
tmp111 = tmp130 ;
tmp131 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_end_ncol) ;
tmp112 = tmp131 ;
tmp132 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_end_ntot) ;
tmp110 = tmp132 ;
} /* end of [if] */
tmp133 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg0), atslab_filename) ;
tmp106 = ATS_MALLOC(sizeof(anairiats_rec_0)) ;
ats_selptrset_mac(anairiats_rec_0, tmp106, atslab_filename, tmp133) ;
ats_selptrset_mac(anairiats_rec_0, tmp106, atslab_beg_ntot, tmp107) ;
ats_selptrset_mac(anairiats_rec_0, tmp106, atslab_beg_nrow, tmp108) ;
ats_selptrset_mac(anairiats_rec_0, tmp106, atslab_beg_ncol, tmp109) ;
ats_selptrset_mac(anairiats_rec_0, tmp106, atslab_end_ntot, tmp110) ;
ats_selptrset_mac(anairiats_rec_0, tmp106, atslab_end_nrow, tmp111) ;
ats_selptrset_mac(anairiats_rec_0, tmp106, atslab_end_ncol, tmp112) ;

return (tmp106) ;
} /* end of [location_combine_main_25] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 7853(line=371, offs=3) -- 8004(line=374, offs=44)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_combine (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp134) ;
ATSlocal (ats_bool_type, tmp135) ;
ATSlocal (ats_bool_type, tmp136) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_combine:
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
__ats_lab_0_1:
tmp135 = location_is_none_24 (arg0) ;
if (!tmp135) { goto __ats_lab_1_1 ; }
tmp134 = arg1 ;
break ;

/* branch: __ats_lab_1 */
__ats_lab_1_0:
__ats_lab_1_1:
tmp136 = location_is_none_24 (arg1) ;
if (!tmp136) { goto __ats_lab_2_1 ; }
tmp134 = arg0 ;
break ;

/* branch: __ats_lab_2 */
__ats_lab_2_0:
__ats_lab_2_1:
tmp134 = location_combine_main_25 (arg0, arg1) ;
break ;
} while (0) ;
return (tmp134) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_combine] */

/*
// /home/hwxi/research/Postiats/git/src/pats_location.dats: 8110(line=383, offs=3) -- 8625(line=409, offs=4)
*/
ATSglobaldec()
ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_line_pragma (ats_ptr_type arg0, ats_ptr_type arg1) {
/* local vardec */
// ATSlocal_void (tmp137) ;
ATSlocal (ats_int_type, tmp138) ;
ATSlocal (ats_bool_type, tmp139) ;
// ATSlocal_void (tmp140) ;
// ATSlocal_void (tmp141) ;
ATSlocal (ats_int_type, tmp142) ;
// ATSlocal_void (tmp143) ;
// ATSlocal_void (tmp144) ;
ATSlocal (ats_ptr_type, tmp145) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_line_pragma:
tmp138 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_beg_nrow) ;
tmp139 = atspre_gte_int_int (tmp138, 0) ;
if (tmp139) {
/* tmp140 = */ atspre_fprint_string (arg0, ATSstrcst("#line ")) ;
tmp142 = atspre_add_int_int (tmp138, 1) ;
/* tmp141 = */ atspre_fprint_int (arg0, tmp142) ;
/* tmp143 = */ atspre_fprint_string (arg0, ATSstrcst(" \"")) ;
tmp145 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_0, arg1), atslab_filename) ;
/* tmp144 = */ _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__fprint_filename_full (arg0, tmp145) ;
/* tmp137 = */ atspre_fprint_string (arg0, ATSstrcst("\"\n")) ;
} else {
/* empty */
} /* end of [if] */
return /* (tmp137) */ ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__fprint_line_pragma] */

/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2edats__staload () ;

#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* marking static variables for GC */
ATS_GC_MARKROOT(&statmp78, sizeof(ats_ptr_type)) ;

/* marking external values for GC */

/* code for dynamic loading */
statmp78 = ATS_MALLOC(sizeof(anairiats_rec_0)) ;
ats_selptrset_mac(anairiats_rec_0, statmp78, atslab_filename, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__filename_dummy) ;
ats_selptrset_mac(anairiats_rec_0, statmp78, atslab_beg_ntot, -1L) ;
ats_selptrset_mac(anairiats_rec_0, statmp78, atslab_beg_nrow, -1) ;
ats_selptrset_mac(anairiats_rec_0, statmp78, atslab_beg_ncol, -1) ;
ats_selptrset_mac(anairiats_rec_0, statmp78, atslab_end_ntot, -1L) ;
ats_selptrset_mac(anairiats_rec_0, statmp78, atslab_end_nrow, -1) ;
ats_selptrset_mac(anairiats_rec_0, statmp78, atslab_end_ncol, -1) ;

ATS_GC_MARKROOT(&_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_dummy, sizeof(ats_ptr_type)) ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_location_2esats__location_dummy = statmp78 ;
return ;
} /* end of [dynload function] */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_location_dats.c] */
