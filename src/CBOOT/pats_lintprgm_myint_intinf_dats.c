/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2013-9-23: 22h:52m
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

#include "libc/CATS/gmp.cats"

#include "pats_location.cats"

#include "libc/CATS/gmp.cats"
/* external codes at top */

#include "pats_lintprgm_myint.cats"

/* type definitions */
/* external typedefs */
/* external dynamic constructor declarations */
/* external dynamic constant declarations */
ATSextern_fun(ats_ptr_type, atspre_ptr_alloc_tsz) (ats_size_type) ;
ATSextern_fun(ats_void_type, atspre_ptr_free) (ats_ptr_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_neg1) (ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_add2_mpz) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_sub2_mpz) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_mpz_mul2_mpz) (ats_ref_type, ats_ref_type) ;
ATSextern_fun(ats_void_type, atslib_fprint_mpz) (ats_ptr_type, ats_ref_type) ;

/* external dynamic terminating constant declarations */
#ifdef _ATS_PROOFCHECK
#endif /* _ATS_PROOFCHECK */

/* assuming abstract types */
/* sum constructor declarations */
/* exn constructor declarations */
/* global dynamic (non-functional) constant declarations */
/* internal function declarations */
static
ats_void_type fprint_myint_02216_intinfknd (ats_ptr_type arg0, intinfknd arg1) ;
static
intinfknd myint_make_int_02219_intinfknd (ats_int_type arg0) ;
static
intinfknd myint_make_intinf_02220_intinfknd (ats_ptr_type arg0) ;
static
intinfknd myint_copy_02222_intinfknd (intinfknd arg0) ;
static
ats_void_type myint_free_02221_intinfknd (intinfknd arg0) ;
static
intinfknd neg_myint_02223_intinfknd (intinfknd arg0) ;
static
intinfknd neg1_myint_02224_intinfknd (intinfknd arg0) ;
static
intinfknd add01_myint_myint_02226_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd sub01_myint_myint_02227_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd add_myint_int_02225_intinfknd (intinfknd arg0, ats_int_type arg1) ;
static
intinfknd mul01_myint_myint_02228_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd mul10_myint_myint_02229_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd mul11_myint_myint_02230_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd div01_myint_myint_02231_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd ediv01_myint_myint_02233_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd mod01_myint_myint_02234_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd mod11_myint_myint_02235_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
intinfknd gcd01_myint_myint_02236_intinfknd (intinfknd arg0, intinfknd arg1) ;
static
ats_int_type compare_myint_int_02243_intinfknd (intinfknd arg0, ats_int_type arg1) ;
static
ats_int_type compare_myint_myint_02248_intinfknd (intinfknd arg0, intinfknd arg1) ;

/* partial value template declarations */
/* static temporary variable declarations */
/* external value variable declarations */

/* function implementations */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 2255(line=82, offs=3) -- 2423(line=90, offs=4)
*/
ATSstaticdec()
ats_void_type
fprint_myint_02216_intinfknd (ats_ptr_type arg0, intinfknd arg1) {
/* local vardec */
// ATSlocal_void (tmp0) ;
ATSlocal (ats_ptr_type, tmp1) ;

__ats_lab_fprint_myint_02216_intinfknd:
tmp1 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp0 = */ atslib_fprint_mpz (arg0, tmp1) ;
return /* (tmp0) */ ;
} /* end of [fprint_myint_02216_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 2518(line=95, offs=27) -- 2665(line=100, offs=4)
*/
ATSstaticdec()
intinfknd
myint_make_int_02219_intinfknd (ats_int_type arg0) {
/* local vardec */
ATSlocal (intinfknd, tmp2) ;
ATSlocal (ats_ptr_type, tmp3) ;
ATSlocal (ats_ptr_type, tmp4) ;
// ATSlocal_void (tmp5) ;
ATSlocal (ats_ptr_type, tmp6) ;

__ats_lab_myint_make_int_02219_intinfknd:
tmp3 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp4 = ats_selsin_mac(tmp3, atslab_2) ;
/* tmp5 = */ atslib_mpz_init_set_int (tmp4, arg0) ;
tmp6 = tmp4 ;
tmp2 = ats_castfn_mac(intinfknd, tmp6) ;
return (tmp2) ;
} /* end of [myint_make_int_02219_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 2734(line=103, offs=30) -- 2961(line=110, offs=4)
*/
ATSstaticdec()
intinfknd
myint_make_intinf_02220_intinfknd (ats_ptr_type arg0) {
/* local vardec */
ATSlocal (intinfknd, tmp7) ;
ATSlocal (ats_ptr_type, tmp8) ;
ATSlocal (ats_ptr_type, tmp9) ;
ATSlocal (ats_ptr_type, tmp10) ;
// ATSlocal_void (tmp11) ;
ATSlocal (ats_ptr_type, tmp12) ;

__ats_lab_myint_make_intinf_02220_intinfknd:
tmp8 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp9 = ats_selsin_mac(tmp8, atslab_2) ;
tmp10 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, arg0), atslab_2) ;
/* tmp11 = */ atslib_mpz_init_set_mpz (tmp9, tmp10) ;
tmp12 = tmp9 ;
tmp7 = ats_castfn_mac(intinfknd, tmp12) ;
return (tmp7) ;
} /* end of [myint_make_intinf_02220_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 3044(line=115, offs=23) -- 3287(line=124, offs=4)
*/
ATSstaticdec()
intinfknd
myint_copy_02222_intinfknd (intinfknd arg0) {
/* local vardec */
ATSlocal (intinfknd, tmp13) ;
ATSlocal (ats_ptr_type, tmp14) ;
ATSlocal (ats_ptr_type, tmp15) ;
// ATSlocal_void (tmp16) ;
ATSlocal (ats_ptr_type, tmp17) ;
ATSlocal (ats_ptr_type, tmp18) ;

__ats_lab_myint_copy_02222_intinfknd:
tmp14 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp15 = ats_selsin_mac(tmp14, atslab_2) ;
tmp17 = ats_varget_mac(ats_ptr_type, arg0) ;
/* tmp16 = */ atslib_mpz_init_set_mpz (tmp15, tmp17) ;
tmp18 = tmp15 ;
tmp13 = ats_castfn_mac(intinfknd, tmp18) ;
return (tmp13) ;
} /* end of [myint_copy_02222_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 3376(line=129, offs=23) -- 3503(line=135, offs=4)
*/
ATSstaticdec()
ats_void_type
myint_free_02221_intinfknd (intinfknd arg0) {
/* local vardec */
// ATSlocal_void (tmp19) ;
// ATSlocal_void (tmp20) ;
ATSlocal (ats_ptr_type, tmp21) ;
ATSlocal (ats_ptr_type, tmp22) ;

__ats_lab_myint_free_02221_intinfknd:
tmp21 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp20 = */ atslib_mpz_clear (tmp21) ;
tmp22 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp19 = */ atspre_ptr_free (tmp22) ;
return /* (tmp19) */ ;
} /* end of [myint_free_02221_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 3593(line=141, offs=3) -- 3711(line=146, offs=2)
*/
ATSstaticdec()
intinfknd
neg_myint_02223_intinfknd (intinfknd arg0) {
/* local vardec */
ATSlocal (intinfknd, tmp23) ;
// ATSlocal_void (tmp24) ;
ATSlocal (ats_ptr_type, tmp25) ;

__ats_lab_neg_myint_02223_intinfknd:
tmp25 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp24 = */ atslib_mpz_neg1 (tmp25) ;
tmp23 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp23) ;
} /* end of [neg_myint_02223_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 3801(line=152, offs=3) -- 4055(line=160, offs=2)
*/
ATSstaticdec()
intinfknd
neg1_myint_02224_intinfknd (intinfknd arg0) {
/* local vardec */
ATSlocal (intinfknd, tmp26) ;
ATSlocal (ats_ptr_type, tmp27) ;
ATSlocal (ats_ptr_type, tmp28) ;
// ATSlocal_void (tmp29) ;
// ATSlocal_void (tmp30) ;
ATSlocal (ats_ptr_type, tmp31) ;
ATSlocal (ats_ptr_type, tmp32) ;

__ats_lab_neg1_myint_02224_intinfknd:
tmp27 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp28 = ats_selsin_mac(tmp27, atslab_2) ;
/* tmp29 = */ atslib_mpz_init (tmp28) ;
tmp31 = ats_varget_mac(ats_ptr_type, arg0) ;
/* tmp30 = */ atslib_mpz_neg2 (tmp28, tmp31) ;
tmp32 = tmp28 ;
tmp26 = ats_castfn_mac(intinfknd, tmp32) ;
return (tmp26) ;
} /* end of [neg1_myint_02224_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 4153(line=166, offs=3) -- 4378(line=172, offs=2)
*/
ATSstaticdec()
intinfknd
add01_myint_myint_02226_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp33) ;
// ATSlocal_void (tmp34) ;
ATSlocal (ats_ptr_type, tmp35) ;
ATSlocal (ats_ptr_type, tmp36) ;

__ats_lab_add01_myint_myint_02226_intinfknd:
tmp35 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp36 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp34 = */ atslib_mpz_add2_mpz (tmp35, tmp36) ;
tmp33 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp33) ;
} /* end of [add01_myint_myint_02226_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 4481(line=178, offs=3) -- 4706(line=184, offs=2)
*/
ATSstaticdec()
intinfknd
sub01_myint_myint_02227_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp37) ;
// ATSlocal_void (tmp38) ;
ATSlocal (ats_ptr_type, tmp39) ;
ATSlocal (ats_ptr_type, tmp40) ;

__ats_lab_sub01_myint_myint_02227_intinfknd:
tmp39 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp40 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp38 = */ atslib_mpz_sub2_mpz (tmp39, tmp40) ;
tmp37 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp37) ;
} /* end of [sub01_myint_myint_02227_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 4805(line=190, offs=3) -- 4934(line=195, offs=2)
*/
ATSstaticdec()
intinfknd
add_myint_int_02225_intinfknd (intinfknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp41) ;
// ATSlocal_void (tmp42) ;
ATSlocal (ats_ptr_type, tmp43) ;

__ats_lab_add_myint_int_02225_intinfknd:
tmp43 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
/* tmp42 = */ atslib_mpz_add2_int (tmp43, arg1) ;
tmp41 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp41) ;
} /* end of [add_myint_int_02225_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 5035(line=201, offs=3) -- 5261(line=208, offs=2)
*/
ATSstaticdec()
intinfknd
mul01_myint_myint_02228_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp44) ;
// ATSlocal_void (tmp45) ;
ATSlocal (ats_ptr_type, tmp46) ;
ATSlocal (ats_ptr_type, tmp47) ;

__ats_lab_mul01_myint_myint_02228_intinfknd:
tmp46 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp47 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp45 = */ atslib_mpz_mul2_mpz (tmp46, tmp47) ;
tmp44 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp44) ;
} /* end of [mul01_myint_myint_02228_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 5345(line=212, offs=3) -- 5810(line=227, offs=2)
*/
ATSstaticdec()
intinfknd
mul10_myint_myint_02229_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp48) ;
ATSlocal (ats_ptr_type, tmp49) ;
ATSlocal (ats_ptr_type, tmp50) ;
// ATSlocal_void (tmp51) ;
ATSlocal (ats_ptr_type, tmp52) ;
ATSlocal (ats_ptr_type, tmp53) ;

__ats_lab_mul10_myint_myint_02229_intinfknd:
tmp49 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg1)) ;
tmp50 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp49), atslab_2) ;
tmp52 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg1)) ;
tmp53 = ats_varget_mac(ats_ptr_type, arg0) ;
/* tmp51 = */ atslib_mpz_mul3_mpz (tmp52, tmp53, tmp50) ;
tmp48 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg1)) ;
return (tmp48) ;
} /* end of [mul10_myint_myint_02229_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 5894(line=231, offs=3) -- 6248(line=241, offs=4)
*/
ATSstaticdec()
intinfknd
mul11_myint_myint_02230_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp54) ;
ATSlocal (ats_ptr_type, tmp55) ;
ATSlocal (ats_ptr_type, tmp56) ;
// ATSlocal_void (tmp57) ;
// ATSlocal_void (tmp58) ;
ATSlocal (ats_ptr_type, tmp59) ;
ATSlocal (ats_ptr_type, tmp60) ;
ATSlocal (ats_ptr_type, tmp61) ;

__ats_lab_mul11_myint_myint_02230_intinfknd:
tmp55 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp56 = ats_selsin_mac(tmp55, atslab_2) ;
/* tmp57 = */ atslib_mpz_init (tmp56) ;
tmp59 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp60 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp58 = */ atslib_mpz_mul3_mpz (tmp56, tmp59, tmp60) ;
tmp61 = tmp56 ;
tmp54 = ats_castfn_mac(intinfknd, tmp61) ;
return (tmp54) ;
} /* end of [mul11_myint_myint_02230_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 6353(line=247, offs=3) -- 6818(line=261, offs=2)
*/
ATSstaticdec()
intinfknd
div01_myint_myint_02231_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp62) ;
ATSlocal (ats_ptr_type, tmp63) ;
ATSlocal (ats_ptr_type, tmp64) ;
// ATSlocal_void (tmp65) ;
ATSlocal (ats_ptr_type, tmp66) ;
ATSlocal (ats_ptr_type, tmp67) ;

__ats_lab_div01_myint_myint_02231_intinfknd:
tmp63 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp64 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp63), atslab_2) ;
tmp66 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp67 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp65 = */ atslib_mpz_tdiv3_q_mpz (tmp64, tmp66, tmp67) ;
tmp62 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp62) ;
} /* end of [div01_myint_myint_02231_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 6924(line=267, offs=3) -- 7387(line=281, offs=2)
*/
ATSstaticdec()
intinfknd
ediv01_myint_myint_02233_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp68) ;
ATSlocal (ats_ptr_type, tmp69) ;
ATSlocal (ats_ptr_type, tmp70) ;
// ATSlocal_void (tmp71) ;
ATSlocal (ats_ptr_type, tmp72) ;
ATSlocal (ats_ptr_type, tmp73) ;

__ats_lab_ediv01_myint_myint_02233_intinfknd:
tmp69 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp70 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp69), atslab_2) ;
tmp72 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp73 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp71 = */ atslib_mpz_divexact3 (tmp70, tmp72, tmp73) ;
tmp68 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp68) ;
} /* end of [ediv01_myint_myint_02233_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 7493(line=287, offs=3) -- 7955(line=301, offs=2)
*/
ATSstaticdec()
intinfknd
mod01_myint_myint_02234_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp74) ;
ATSlocal (ats_ptr_type, tmp75) ;
ATSlocal (ats_ptr_type, tmp76) ;
// ATSlocal_void (tmp77) ;
ATSlocal (ats_ptr_type, tmp78) ;
ATSlocal (ats_ptr_type, tmp79) ;

__ats_lab_mod01_myint_myint_02234_intinfknd:
tmp75 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp76 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp75), atslab_2) ;
tmp78 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp79 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp77 = */ atslib_mpz_mod3_mpz (tmp76, tmp78, tmp79) ;
tmp74 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp74) ;
} /* end of [mod01_myint_myint_02234_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 8039(line=305, offs=3) -- 8393(line=315, offs=4)
*/
ATSstaticdec()
intinfknd
mod11_myint_myint_02235_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp80) ;
ATSlocal (ats_ptr_type, tmp81) ;
ATSlocal (ats_ptr_type, tmp82) ;
// ATSlocal_void (tmp83) ;
// ATSlocal_void (tmp84) ;
ATSlocal (ats_ptr_type, tmp85) ;
ATSlocal (ats_ptr_type, tmp86) ;
ATSlocal (ats_ptr_type, tmp87) ;

__ats_lab_mod11_myint_myint_02235_intinfknd:
tmp81 = atspre_ptr_alloc_tsz (sizeof(ats_mpz_viewt0ype)) ;
tmp82 = ats_selsin_mac(tmp81, atslab_2) ;
/* tmp83 = */ atslib_mpz_init (tmp82) ;
tmp85 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp86 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp84 = */ atslib_mpz_mod3_mpz (tmp82, tmp85, tmp86) ;
tmp87 = tmp82 ;
tmp80 = ats_castfn_mac(intinfknd, tmp87) ;
return (tmp80) ;
} /* end of [mod11_myint_myint_02235_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 8498(line=321, offs=3) -- 8960(line=335, offs=2)
*/
ATSstaticdec()
intinfknd
gcd01_myint_myint_02236_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (intinfknd, tmp88) ;
ATSlocal (ats_ptr_type, tmp89) ;
ATSlocal (ats_ptr_type, tmp90) ;
// ATSlocal_void (tmp91) ;
ATSlocal (ats_ptr_type, tmp92) ;
ATSlocal (ats_ptr_type, tmp93) ;

__ats_lab_gcd01_myint_myint_02236_intinfknd:
tmp89 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp90 = ats_selsin_mac(ats_castfn_mac(ats_ptr_type, tmp89), atslab_2) ;
tmp92 = ats_varget_mac(ats_ptr_type, ats_castfn_mac(ats_ptr_type, arg0)) ;
tmp93 = ats_varget_mac(ats_ptr_type, arg1) ;
/* tmp91 = */ atslib_mpz_gcd3_mpz (tmp90, tmp92, tmp93) ;
tmp88 = ats_castfn_mac(intinfknd, ats_castfn_mac(ats_ptr_type, arg0)) ;
return (tmp88) ;
} /* end of [gcd01_myint_myint_02236_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 9065(line=341, offs=3) -- 9219(line=347, offs=2)
*/
ATSstaticdec()
ats_int_type
compare_myint_int_02243_intinfknd (intinfknd arg0, ats_int_type arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp94) ;
ATSlocal (ats_ptr_type, tmp95) ;

__ats_lab_compare_myint_int_02243_intinfknd:
tmp95 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp94 = atslib_mpz_cmp_int (tmp95, arg1) ;
return (tmp94) ;
} /* end of [compare_myint_int_02243_intinfknd] */

/*
// /home/hwxi/research/Postiats/git/src/pats_lintprgm_myint_intinf.dats: 9316(line=353, offs=3) -- 9554(line=359, offs=2)
*/
ATSstaticdec()
ats_int_type
compare_myint_myint_02248_intinfknd (intinfknd arg0, intinfknd arg1) {
/* local vardec */
ATSlocal (ats_int_type, tmp96) ;
ATSlocal (ats_ptr_type, tmp97) ;
ATSlocal (ats_ptr_type, tmp98) ;

__ats_lab_compare_myint_myint_02248_intinfknd:
tmp97 = ats_varget_mac(ats_ptr_type, arg0) ;
tmp98 = ats_varget_mac(ats_ptr_type, arg1) ;
tmp96 = atslib_mpz_cmp_mpz (tmp97, tmp98) ;
return (tmp96) ;
} /* end of [compare_myint_myint_02248_intinfknd] */

/* static load function */

extern ats_void_type ATS_2d0_2e2_2e10_2libc_2SATS_2gmp_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__staload_flag = 1 ;

ATS_2d0_2e2_2e10_2libc_2SATS_2gmp_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_intinf_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_2esats__staload () ;

return ;
} /* staload function */

/* dynamic load function */

// dynload flag declaration
// extern ats_int_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__dynload_flag ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__dynload () {
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__dynload_flag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lintprgm_myint_intinf_2edats__staload () ;

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

/* end of [pats_lintprgm_myint_intinf_dats.c] */
