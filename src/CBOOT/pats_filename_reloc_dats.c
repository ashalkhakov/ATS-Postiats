/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2015-9-30: 21h:45m
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
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__None_vt_0) ;
ATSextern_val(ats_sum_type, ATS_2d0_2e2_2e12_2prelude_2basics_sta_2esats__Some_vt_1) ;
ATSextern_val(ats_sum_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__E1XPstring_5) ;

/* external dynamic constant declarations */
ATSextern_fun(ats_bool_type, atspre_eq_char_char) (ats_char_type, ats_char_type) ;
ATSextern_fun(ats_bool_type, atspre_char_isalnum) (ats_char_type) ;
ATSextern_fun(ats_int_type, atspre_add_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_int_type, atspre_sub_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_bool_type, atspre_lt_int_int) (ats_int_type, ats_int_type) ;
ATSextern_fun(ats_void_type, atspre_strptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, atspre_tostringf) (ats_ptr_type, ...) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_utils_2esats__dirpath_append) (ats_ptr_type, ats_ptr_type, ats_char_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_global_2esats__the_PKGRELOC_get_decl) () ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_make_string) (ats_ptr_type) ;
ATSextern_fun(ats_char_type, patsopt_filename_theDirSep_get) () ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_e1xpenv_find) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_pkgreloc_insert) (ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_void_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_pkgreloc_insert2) (ats_ptr_type, ats_ptr_type, ats_ptr_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl0) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl1) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl0) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl1) (ats_ptr_type, ats_int_type) ;
ATSextern_fun(ats_ptr_type, _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_eval) (ats_ptr_type) ;
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
ats_char_type ptr0_get_01703_ats_char_type (ats_ptr_type arg0) ;
static
ats_bool_type char_isalnum__6 (ats_char_type arg0) ;
static
ats_int_type auxtrav1_7 (ats_ptr_type arg0, ats_int_type arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 2435(line=105, offs=3) -- 2577(line=112, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl0 (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp0) ;
ATSlocal (ats_int_type, tmp1) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl0:
tmp1 = atspre_sub_int_int (arg1, 2) ;
tmp0 = atspre_string_make_substring (arg0, ats_castfn_mac(ats_size_type, 1), ats_castfn_mac(ats_size_type, tmp1)) ;
return (tmp0) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl0] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 2741(line=122, offs=3) -- 2791(line=122, offs=53)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl1 (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp2) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl1:
tmp2 = atspre_string_copy (ATSstrcst("$ATSPKGRELOCROOT")) ;
return (tmp2) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl1] */

/*
// /home/hwxi/Research/ATS-Anairiats/prelude/DATS/unsafe.dats: 1763(line=50, offs=10) -- 1979(line=60, offs=2)
*/
ATSstaticdec()
ats_char_type
ptr0_get_01703_ats_char_type (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_char_type, tmp5) ;

__ats_lab_ptr0_get_01703_ats_char_type:
tmp5 = ats_ptrget_mac(ats_char_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp5) ;
} /* end of [ptr0_get_01703_ats_char_type] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 2923(line=132, offs=3) -- 3853(line=164, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl0 (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp3) ;
ATSlocal (ats_char_type, tmp4) ;
ATSlocal (ats_ptr_type, tmp6) ;
ATSlocal (ats_bool_type, tmp7) ;
ATSlocal (ats_int_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;
// ATSlocal_void (tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;
ATSlocal (ats_ptr_type, tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;
ATSlocal (ats_ptr_type, tmp16) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl0:
tmp6 = atspre_padd_int (ats_castfn_mac(ats_ptr_type, arg0), 1) ;
tmp4 = ptr0_get_01703_ats_char_type (tmp6) ;
do {
/* branch: __ats_lab_0 */
__ats_lab_0_0:
__ats_lab_0_1:
tmp7 = atspre_eq_char_char (tmp4, '$') ;
if (!tmp7) { goto __ats_lab_5_1 ; }
tmp8 = atspre_sub_int_int (arg1, 3) ;
tmp9 = atspre_string_make_substring (arg0, ats_castfn_mac(ats_size_type, 2), ats_castfn_mac(ats_size_type, tmp8)) ;
tmp10 = atspre_tostringf (ATSstrcst("%s_sourceloc"), ats_castfn_mac(ats_ptr_type, tmp9)) ;
/* tmp11 = */ atspre_strptr_free (tmp9) ;
tmp12 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_make_string (ats_castfn_mac(ats_ptr_type, tmp10)) ;
tmp13 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_e1xpenv_find (tmp12) ;
do {
/* branch: __ats_lab_1 */
__ats_lab_1_0:
if (tmp13 == (ats_sum_ptr_type)0) { goto __ats_lab_4_0 ; }
__ats_lab_1_1:
tmp14 = ats_caselptrlab_mac(anairiats_sum_0, tmp13, atslab_0) ;
ATS_FREE(tmp13) ;
tmp15 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp14), atslab_e1xp_node) ;
do {
/* branch: __ats_lab_2 */
__ats_lab_2_0:
if (((ats_sum_ptr_type)tmp15)->tag != 5) { goto __ats_lab_3_0 ; }
__ats_lab_2_1:
tmp16 = ats_caselptrlab_mac(anairiats_sum_2, tmp15, atslab_0) ;
tmp3 = atspre_string_copy (tmp16) ;
break ;

/* branch: __ats_lab_3 */
__ats_lab_3_0:
__ats_lab_3_1:
tmp3 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl0 (arg0, arg1) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_4 */
__ats_lab_4_0:
// if (tmp13 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_4_1:
tmp3 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl0 (arg0, arg1) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_5 */
__ats_lab_5_0:
__ats_lab_5_1:
tmp3 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl0 (arg0, arg1) ;
break ;
} while (0) ;
return (tmp3) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl0] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 4016(line=174, offs=3) -- 4992(line=209, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl1 (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp17) ;
ATSlocal (ats_char_type, tmp18) ;
ATSlocal (ats_ptr_type, tmp19) ;
ATSlocal (ats_bool_type, tmp20) ;
ATSlocal (ats_int_type, tmp21) ;
ATSlocal (ats_ptr_type, tmp22) ;
ATSlocal (ats_ptr_type, tmp23) ;
// ATSlocal_void (tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;
ATSlocal (ats_ptr_type, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
ATSlocal (ats_ptr_type, tmp29) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl1:
tmp19 = atspre_padd_int (ats_castfn_mac(ats_ptr_type, arg0), 1) ;
tmp18 = ptr0_get_01703_ats_char_type (tmp19) ;
do {
/* branch: __ats_lab_6 */
__ats_lab_6_0:
__ats_lab_6_1:
tmp20 = atspre_eq_char_char (tmp18, '$') ;
if (!tmp20) { goto __ats_lab_11_1 ; }
tmp21 = atspre_sub_int_int (arg1, 3) ;
tmp22 = atspre_string_make_substring (arg0, ats_castfn_mac(ats_size_type, 2), ats_castfn_mac(ats_size_type, tmp21)) ;
tmp23 = atspre_tostringf (ATSstrcst("%s_targetloc"), ats_castfn_mac(ats_ptr_type, tmp22)) ;
/* tmp24 = */ atspre_strptr_free (tmp22) ;
tmp25 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_make_string (ats_castfn_mac(ats_ptr_type, tmp23)) ;
tmp26 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_e1xpenv_find (tmp25) ;
do {
/* branch: __ats_lab_7 */
__ats_lab_7_0:
if (tmp26 == (ats_sum_ptr_type)0) { goto __ats_lab_10_0 ; }
__ats_lab_7_1:
tmp27 = ats_caselptrlab_mac(anairiats_sum_0, tmp26, atslab_0) ;
ATS_FREE(tmp26) ;
tmp28 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp27), atslab_e1xp_node) ;
do {
/* branch: __ats_lab_8 */
__ats_lab_8_0:
if (((ats_sum_ptr_type)tmp28)->tag != 5) { goto __ats_lab_9_0 ; }
__ats_lab_8_1:
tmp29 = ats_caselptrlab_mac(anairiats_sum_2, tmp28, atslab_0) ;
tmp17 = atspre_string_copy (tmp29) ;
break ;

/* branch: __ats_lab_9 */
__ats_lab_9_0:
__ats_lab_9_1:
tmp17 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl1 (arg0, arg1) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_10 */
__ats_lab_10_0:
// if (tmp26 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_10_1:
tmp17 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl1 (arg0, arg1) ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_11 */
__ats_lab_11_0:
__ats_lab_11_1:
tmp17 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get_gurl1 (arg0, arg1) ;
break ;
} while (0) ;
return (tmp17) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl1] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 5279(line=228, offs=5) -- 5356(line=229, offs=46)
*/
ATSstaticdec()
ats_bool_type
char_isalnum__6 (ats_char_type arg0) {
/* local vardec */
ATSlocal (ats_bool_type, tmp32) ;
ATSlocal (ats_bool_type, tmp33) ;

__ats_lab_char_isalnum__6:
tmp33 = atspre_char_isalnum (arg0) ;
if (tmp33) {
tmp32 = ats_true_bool ;
} else {
tmp32 = atspre_eq_char_char (arg0, '_') ;
} /* end of [if] */
return (tmp32) ;
} /* end of [char_isalnum__6] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 5364(line=231, offs=5) -- 5537(line=240, offs=4)
*/
ATSstaticdec()
ats_int_type
auxtrav1_7 (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp34) ;
ATSlocal (ats_char_type, tmp35) ;
ATSlocal (ats_bool_type, tmp36) ;
ATSlocal (ats_ptr_type, tmp37) ;
ATSlocal (ats_int_type, tmp38) ;

__ats_lab_auxtrav1_7:
tmp35 = ptr0_get_01703_ats_char_type (arg0) ;
tmp36 = char_isalnum__6 (tmp35) ;
if (tmp36) {
tmp37 = atspre_padd_int (arg0, 1) ;
tmp38 = atspre_add_int_int (arg1, 1) ;
arg0 = tmp37 ;
arg1 = tmp38 ;
goto __ats_lab_auxtrav1_7 ; // tail call
} else {
tmp34 = arg1 ;
} /* end of [if] */
return (tmp34) ;
} /* end of [auxtrav1_7] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 5128(line=218, offs=3) -- 6471(line=274, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_eval (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp30) ;
ATSlocal (ats_char_type, tmp31) ;
ATSlocal (ats_bool_type, tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;
ATSlocal (ats_int_type, tmp41) ;
ATSlocal (ats_ptr_type, tmp42) ;
ATSlocal (ats_ptr_type, tmp43) ;
ATSlocal (ats_ptr_type, tmp44) ;
ATSlocal (ats_ptr_type, tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;
ATSlocal (ats_ptr_type, tmp48) ;
ATSlocal (ats_ptr_type, tmp49) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_eval:
tmp31 = ptr0_get_01703_ats_char_type (ats_castfn_mac(ats_ptr_type, arg0)) ;
do {
/* branch: __ats_lab_12 */
__ats_lab_12_0:
__ats_lab_12_1:
tmp39 = atspre_eq_char_char (tmp31, '$') ;
if (!tmp39) { goto __ats_lab_17_1 ; }
tmp40 = atspre_padd_int (ats_castfn_mac(ats_ptr_type, arg0), 1) ;
tmp41 = auxtrav1_7 (tmp40, 0) ;
tmp42 = atspre_string_make_substring (arg0, ats_castfn_mac(ats_size_type, 1), ats_castfn_mac(ats_size_type, tmp41)) ;
tmp43 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__symbol_make_string (ats_castfn_mac(ats_ptr_type, tmp42)) ;
tmp44 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_e1xpenv_find (tmp43) ;
do {
/* branch: __ats_lab_13 */
__ats_lab_13_0:
if (tmp44 == (ats_sum_ptr_type)0) { goto __ats_lab_16_0 ; }
__ats_lab_13_1:
tmp45 = ats_caselptrlab_mac(anairiats_sum_0, tmp44, atslab_0) ;
ATS_FREE(tmp44) ;
tmp46 = ats_selbox_mac(ats_castptr_mac(anairiats_rec_1, tmp45), atslab_e1xp_node) ;
do {
/* branch: __ats_lab_14 */
__ats_lab_14_0:
if (((ats_sum_ptr_type)tmp46)->tag != 5) { goto __ats_lab_15_0 ; }
__ats_lab_14_1:
tmp47 = ats_caselptrlab_mac(anairiats_sum_2, tmp46, atslab_0) ;
tmp48 = atspre_padd_int (tmp40, tmp41) ;
tmp49 = atspre_tostringf (ATSstrcst("%s%s"), tmp47, ats_castfn_mac(ats_ptr_type, tmp48)) ;
tmp30 = ats_castfn_mac(ats_ptr_type, tmp49) ;
break ;

/* branch: __ats_lab_15 */
__ats_lab_15_0:
__ats_lab_15_1:
tmp30 = arg0 ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_16 */
__ats_lab_16_0:
// if (tmp44 != (ats_sum_ptr_type)0) { ats_deadcode_failure_handle () ; }
__ats_lab_16_1:
tmp30 = arg0 ;
break ;
} while (0) ;
break ;

/* branch: __ats_lab_17 */
__ats_lab_17_0:
__ats_lab_17_1:
tmp30 = arg0 ;
break ;
} while (0) ;
return (tmp30) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_eval] */

/*
// /home/hwxi/Research/ATS-Postiats/src/pats_filename_reloc.dats: 6605(line=284, offs=3) -- 8076(line=339, offs=4)
*/
ATSglobaldec()
ats_ptr_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_2esats__pkgsrcname_relocatize (ats_ptr_type arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_ptr_type, tmp50) ;
ATSlocal (ats_ptr_type, tmp51) ;
ATSlocal (ats_bool_type, tmp52) ;
// ATSlocal_void (tmp53) ;
ATSlocal (ats_bool_type, tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;
ATSlocal (ats_char_type, tmp56) ;
ATSlocal (ats_ptr_type, tmp57) ;
ATSlocal (ats_ptr_type, tmp58) ;
// ATSlocal_void (tmp59) ;
ATSlocal (ats_ptr_type, tmp60) ;
// ATSlocal_void (tmp61) ;
ATSlocal (ats_bool_type, tmp62) ;
ATSlocal (ats_ptr_type, tmp63) ;
ATSlocal (ats_ptr_type, tmp64) ;
// ATSlocal_void (tmp65) ;
ATSlocal (ats_ptr_type, tmp66) ;

__ats_lab__2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_2esats__pkgsrcname_relocatize:
tmp51 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_global_2esats__the_PKGRELOC_get_decl () ;
tmp52 = atspre_lt_int_int (arg1, 0) ;
if (tmp52) {
tmp54 = atspre_pgt (tmp51, atspre_null_ptr) ;
if (tmp54) {
/* tmp53 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_pkgreloc_insert (ats_castfn_mac(ats_ptr_type, tmp51), arg0) ;
} else {
/* empty */
} /* end of [if] */
tmp50 = arg0 ;
} else {
tmp55 = atspre_padd_int (ats_castfn_mac(ats_ptr_type, arg0), arg1) ;
tmp56 = patsopt_filename_theDirSep_get () ;
tmp57 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl1 (arg0, arg1) ;
tmp58 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_utils_2esats__dirpath_append (ats_castfn_mac(ats_ptr_type, tmp57), ats_castfn_mac(ats_ptr_type, tmp55), tmp56) ;
/* tmp59 = */ atspre_strptr_free (tmp57) ;
tmp60 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_eval (ats_castfn_mac(ats_ptr_type, tmp58)) ;
tmp62 = atspre_pgt (tmp51, atspre_null_ptr) ;
if (tmp62) {
tmp63 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_get2_gurl0 (arg0, arg1) ;
tmp64 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_utils_2esats__dirpath_append (ats_castfn_mac(ats_ptr_type, tmp63), ats_castfn_mac(ats_ptr_type, tmp55), tmp56) ;
/* tmp65 = */ atspre_strptr_free (tmp63) ;
tmp66 = _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__pkgsrcname_eval (ats_castfn_mac(ats_ptr_type, tmp64)) ;
/* tmp61 = */ _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__the_pkgreloc_insert2 (ats_castfn_mac(ats_ptr_type, tmp51), tmp66, tmp60) ;
} else {
/* empty */
} /* end of [if] */
tmp50 = tmp60 ;
} /* end of [if] */
return (tmp50) ;
} /* end of [_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_2esats__pkgsrcname_relocatize] */

/* static load function */

// extern ats_void_type ATS_2d0_2e2_2e12_2prelude_2SATS_2unsafe_2esats__staload (void) ;
extern ats_void_type ATS_2d0_2e2_2e12_2prelude_2DATS_2unsafe_2edats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_utils_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_global_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__staload () {
static int _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__staload_flag) return ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__staload_flag = 1 ;

// ATS_2d0_2e2_2e12_2prelude_2SATS_2unsafe_2esats__staload () ;
ATS_2d0_2e2_2e12_2prelude_2DATS_2unsafe_2edats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_utils_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_global_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_symbol_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_syntax_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_staexp1_2esats__staload () ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_trans1_env_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
extern ats_int_type _2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__dynload () {
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__dynload_flag = 1 ;
_2home_2hwxi_2Research_2ATS_2dPostiats_2src_2pats_filename_reloc_2edats__staload () ;

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
