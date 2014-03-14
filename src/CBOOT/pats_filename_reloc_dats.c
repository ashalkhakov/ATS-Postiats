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

#include "libc/CATS/gmp.cats"

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

#include "libc/CATS/gmp.cats"

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

#include "libc/CATS/gmp.cats"

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

typedef
struct {
ats_ptr_type atslab_e1xp_loc ;
ats_ptr_type atslab_e1xp_node ;
} anairiats_rec_1 ;

typedef struct {
int tag ;
ats_ptr_type atslab_0 ;
} anairiats_sum_2 ;

/* external typedefs */
/* external dynamic constructor declarations */
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__None_vt_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e11_2prelude_2basics_sta_2esats__Some_vt_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__E1XPstring_4) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_bool_type, atspre_eq_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_char_isalnum) (ats_char_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_sub_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_gte_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_strptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_tostringf) (ats_ptr_type, ...) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2esats__dirpath_append) (ats_ptr_type, ats_ptr_type, ats_char_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__symbol_make_string) (ats_ptr_type) ;
ATSextern_fun(ats_char_type, patsopt_filename_theDirSep_get) () ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__the_e1xpenv_find) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgtarget_eval) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, patsopt_PATSHOME_get) () ;
ATSextern_fun(ats_ptr_type, patsopt_PATSHOMERELOC_get) () ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_char_type ptr0_get_01700_ats_char_type (ats_ptr_type arg0) ;
static
ats_int_type auxtrav1_4 (ats_ptr_type arg0, ats_int_type arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_filename_reloc.dats: 2291(line=94, offs=3) -- 2433(line=101, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;
ATSlocal (ats_int_type, tmp1) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl:
tmp1 = atspre_sub_int_int (arg1, 2) ;
tmp0 = atspre_string_make_substring (arg0, ats_castfn_mac(ats_size_type, 1), ats_castfn_mac(ats_size_type, tmp1)) ;
return (tmp0) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl] */

/*
// /home/hwxi/research/Anairiats/prelude/DATS/unsafe.dats: 1763(line=50, offs=10) -- 1979(line=60, offs=2)
*/
ATSstaticdec()
ats_char_type
ptr0_get_01700_ats_char_type (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_char_type, tmp4) ;

__ats_lab_ptr0_get_01700_ats_char_type:
tmp4 = ats_ptrget_mac(ats_char_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp4) ;
} /* end of [ptr0_get_01700_ats_char_type] */

/*
// /home/hwxi/research/Postiats/git/src/pats_filename_reloc.dats: 2592(line=110, offs=3) -- 3483(line=140, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp2) ;
ATSlocal (ats_char_type, tmp3) ;
ATSlocal (ats_ptr_type, tmp5) ;
ATSlocal (ats_bool_type, tmp6) ;
ATSlocal (ats_int_type, tmp7) ;
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
// ATSlocal_void (tmp10) ;
ATSlocal (ats_ptr_type, tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
ATSlocal (ats_ptr_type, tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl:
tmp5 = atspre_padd_int (ats_castfn_mac(ats_ptr_type, arg0), 1) ;
tmp3 = ptr0_get_01700_ats_char_type (tmp5) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
__ats_lab_0_1:
tmp6 = atspre_eq_char_char (tmp3, '$') ;
if (!tmp6) { goto __ats_lab_5_1 ; }
tmp7 = atspre_sub_int_int (arg1, 3) ;
tmp8 = atspre_string_make_substring (arg0, ats_castfn_mac(ats_size_type, 2), ats_castfn_mac(ats_size_type, tmp7)) ;
tmp9 = atspre_tostringf (ATSstrcst("%s_targetloc"), ats_castfn_mac(ats_ptr_type, tmp8)) ;
/* tmp10 = */ atspre_strptr_free (tmp8) ;
tmp11 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__symbol_make_string (ats_castfn_mac(ats_ptr_type, tmp9)) ;
tmp12 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__the_e1xpenv_find (tmp11) ;
do {
/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (tmp12 == (ats_sum_ptr_type)0) { goto __ats_lab_4_0 ; }
__ats_lab_1_1:
tmp13 = ats_caselptrlab_mac(anairiats_sum_0, tmp12, atslab_0) ;
ATS_FREE(tmp12) ;
tmp14 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp13), atslab_e1xp_node) ;
do {
/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)tmp14)->tag != 4) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp15 = ats_caselptrlab_mac(anairiats_sum_2, tmp14, atslab_0) ;
tmp2 = atspre_string_copy (tmp15) ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
__ats_lab_3_1:
tmp2 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl (arg0, arg1) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
// if (tmp12 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_4_1:
tmp2 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl (arg0, arg1) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
__ats_lab_5_1:
tmp2 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl (arg0, arg1) ;
break ;
} while (0) ;
return (tmp2) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl] */

/*
// /home/hwxi/research/Postiats/git/src/pats_filename_reloc.dats: 3703(line=153, offs=5) -- 3875(line=162, offs=4)
*/
ATSstaticdec()
ats_int_type
auxtrav1_4 (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp18) ;
ATSlocal (ats_char_type, tmp19) ;
ATSlocal (ats_bool_type, tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_int_type, tmp22) ;

__ats_lab_auxtrav1_4:
tmp19 = ptr0_get_01700_ats_char_type (arg0) ;
tmp20 = atspre_char_isalnum (tmp19) ;
if (tmp20) {
tmp21 = atspre_padd_int (arg0, 1) ;
tmp22 = atspre_add_int_int (arg1, 1) ;
arg0 = tmp21 ;
arg1 = tmp22 ;
goto __ats_lab_auxtrav1_4 ; // tail call
} else {
tmp18 = arg1 ;
} /* end of [if] */
return (tmp18) ;
} /* end of [auxtrav1_4] */

/*
// /home/hwxi/research/Postiats/git/src/pats_filename_reloc.dats: 3616(line=148, offs=3) -- 4798(line=196, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgtarget_eval (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp16) ;
ATSlocal (ats_char_type, tmp17) ;
ATSlocal (ats_bool_type, tmp23) ;
ATSlocal (ats_ptr_type, tmp24) ;
ATSlocal (ats_int_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;
ATSlocal (ats_ptr_type, tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;
ATSlocal (ats_ptr_type, tmp33) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgtarget_eval:
tmp17 = ptr0_get_01700_ats_char_type (ats_castfn_mac(ats_ptr_type, arg0)) ;
do {
/* branch: __ats_lab_6 */
__ats_lab_6_0:
__ats_lab_6_1:
tmp23 = atspre_eq_char_char (tmp17, '$') ;
if (!tmp23) { goto __ats_lab_11_1 ; }
tmp24 = atspre_padd_int (ats_castfn_mac(ats_ptr_type, arg0), 1) ;
tmp25 = auxtrav1_4 (tmp24, 0) ;
tmp26 = atspre_string_make_substring (arg0, ats_castfn_mac(ats_size_type, 1), ats_castfn_mac(ats_size_type, tmp25)) ;
tmp27 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__symbol_make_string (ats_castfn_mac(ats_ptr_type, tmp26)) ;
tmp28 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__the_e1xpenv_find (tmp27) ;
do {
/* branch: __ats_lab_7 */
__ats_lab_7_0:
if (tmp28 == (ats_sum_ptr_type)0) { goto __ats_lab_10_0 ; }
__ats_lab_7_1:
tmp29 = ats_caselptrlab_mac(anairiats_sum_0, tmp28, atslab_0) ;
ATS_FREE(tmp28) ;
tmp30 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp29), atslab_e1xp_node) ;
do {
/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)tmp30)->tag != 4) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
tmp31 = ats_caselptrlab_mac(anairiats_sum_2, tmp30, atslab_0) ;
tmp32 = atspre_padd_int (tmp24, tmp25) ;
tmp33 = atspre_tostringf (ATSstrcst("%s%s"), tmp31, ats_castfn_mac(ats_ptr_type, tmp32)) ;
tmp16 = ats_castfn_mac(ats_ptr_type, tmp33) ;
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
__ats_lab_9_1:
tmp16 = arg0 ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
// if (tmp28 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_10_1:
tmp16 = arg0 ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
__ats_lab_11_1:
tmp16 = arg0 ;
break ;
} while (0) ;
return (tmp16) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgtarget_eval] */

/*
// /home/hwxi/research/Postiats/git/src/pats_filename_reloc.dats: 4931(line=206, offs=3) -- 5667(line=239, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__pkgsrcname_relocatize (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp34) ;
ATSlocal (ats_bool_type, tmp35) ;
ATSlocal (ats_char_type, tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
ATSlocal (ats_ptr_type, tmp38) ;
ATSlocal (ats_ptr_type, tmp39) ;
// ATSlocal_void (tmp40) ;

__ats_lab__2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__pkgsrcname_relocatize:
tmp35 = atspre_gte_int_int (arg1, 0) ;
if (tmp35) {
tmp36 = patsopt_filename_theDirSep_get () ;
tmp37 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl (arg0, arg1) ;
tmp38 = atspre_padd_int (ats_castfn_mac(ats_ptr_type, arg0), arg1) ;
tmp39 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2esats__dirpath_append (ats_castfn_mac(ats_ptr_type, tmp37), ats_castfn_mac(ats_ptr_type, tmp38), tmp36) ;
/* tmp40 = */ atspre_strptr_free (tmp37) ;
tmp34 = _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__pkgtarget_eval (ats_castfn_mac(ats_ptr_type, tmp39)) ;
} else {
tmp34 = arg0 ;
} /* end of [if] */
return (tmp34) ;
} /* end of [_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__pkgsrcname_relocatize] */

/* static load function */

// extern ats_void_type ATS_2d0_2e2_2e11_2prelude_2SATS_2unsafe_2esats__staload (void) ;
extern ats_void_type ATS_2d0_2e2_2e11_2prelude_2DATS_2unsafe_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__staload_flag = 1 ;

// ATS_2d0_2e2_2e11_2prelude_2SATS_2unsafe_2esats__staload () ;
ATS_2d0_2e2_2e11_2prelude_2DATS_2unsafe_2edats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_utils_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_symbol_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_staexp1_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_trans1_env_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__dynload () {
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_filename_reloc_2edats__staload () ;

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

/* end of [pats_filename_reloc_dats.c] */
