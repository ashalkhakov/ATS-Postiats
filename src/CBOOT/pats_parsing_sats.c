/*
**
** The C code is generated by ATS/Anairiats
** The compilation time is: 2013-11-6: 17h:44m
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

/* prologues from statically loaded files */

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
/* external typedefs */
/* assuming abstract types */
/* sum constructor declarations */
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_AND_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_END_1) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_AS_2) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_OF_3) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_IN_4) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_IF_5) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SIF_6) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_CASE_7) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SCASE_8) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_THEN_9) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_ELSE_10) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_REC_11) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_WHEN_12) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_WITH_13) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_FOR_14) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_WHILE_15) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_TRY_16) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_BAR_17) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_COLON_18) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_COMMA_19) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SEMICOLON_20) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_LPAREN_21) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_RPAREN_22) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_LBRACKET_23) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_RBRACKET_24) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_LBRACE_25) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_RBRACE_26) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_BANG_27) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_DOT_28) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_EQ_29) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_EQGT_30) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_GT_31) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_GTDOT_32) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_GTLT_33) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SRPTHEN_34) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SRPENDIF_35) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_EOF_36) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0nt_37) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_c0har_38) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_f0loat_39) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0tring_40) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0de_41) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0dext_42) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0de_dlr_43) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0rtid_44) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_si0de_45) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_di0de_46) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_pi0de_47) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_stai0de_48) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0taq_49) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ynq_50) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_dqi0de_51) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_arrqi0de_52) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_tmpqi0de_53) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_impqi0de_54) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_l0ab_55) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_p0rec_56) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_funarrow_57) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_colonwith_58) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atme0xp_59) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_e0xp_60) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0rt_61) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atms0rt_62) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0marg_63) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_a0msrt_64) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0exp_65) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atms0exp_66) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_labs0exp_67) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0rtext_68) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0qua_69) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_q0marg_70) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_p0at_71) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atmp0at_72) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_labp0at_73) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_p0at_as_74) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_gm0at_75) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_guap0at_76) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_c0lau_77) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0exp_78) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0exp0_79) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0exp1_80) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atmd0exp_81) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_labd0exp_82) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ecl_83) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ecl_sta_84) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ecl_dyn_85) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_guad0ecl_86) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_filename_87) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_DISCARD_88) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__SYNENT2_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__SYNENT3_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__LIST12one_0) ;
ATSglobal(ats_sum_type, _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__LIST12two_1) ;

/* exn constructor declarations */
/* static load function */

extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__staload (void) ;
extern ats_void_type _2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload (void) ;

ats_void_type
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload () {
static int _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload_flag = 0 ;
if (_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload_flag) return ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__staload_flag = 1 ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_lexing_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_tokbuf_2esats__staload () ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_syntax_2esats__staload () ;

_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_AND_0.tag = 0 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_END_1.tag = 1 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_AS_2.tag = 2 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_OF_3.tag = 3 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_IN_4.tag = 4 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_IF_5.tag = 5 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SIF_6.tag = 6 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_CASE_7.tag = 7 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SCASE_8.tag = 8 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_THEN_9.tag = 9 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_ELSE_10.tag = 10 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_REC_11.tag = 11 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_WHEN_12.tag = 12 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_WITH_13.tag = 13 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_FOR_14.tag = 14 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_WHILE_15.tag = 15 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_TRY_16.tag = 16 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_BAR_17.tag = 17 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_COLON_18.tag = 18 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_COMMA_19.tag = 19 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SEMICOLON_20.tag = 20 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_LPAREN_21.tag = 21 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_RPAREN_22.tag = 22 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_LBRACKET_23.tag = 23 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_RBRACKET_24.tag = 24 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_LBRACE_25.tag = 25 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_RBRACE_26.tag = 26 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_BANG_27.tag = 27 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_DOT_28.tag = 28 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_EQ_29.tag = 29 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_EQGT_30.tag = 30 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_GT_31.tag = 31 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_GTDOT_32.tag = 32 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_GTLT_33.tag = 33 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SRPTHEN_34.tag = 34 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_SRPENDIF_35.tag = 35 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_EOF_36.tag = 36 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0nt_37.tag = 37 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_c0har_38.tag = 38 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_f0loat_39.tag = 39 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0tring_40.tag = 40 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0de_41.tag = 41 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0dext_42.tag = 42 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_i0de_dlr_43.tag = 43 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0rtid_44.tag = 44 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_si0de_45.tag = 45 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_di0de_46.tag = 46 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_pi0de_47.tag = 47 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_stai0de_48.tag = 48 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0taq_49.tag = 49 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ynq_50.tag = 50 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_dqi0de_51.tag = 51 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_arrqi0de_52.tag = 52 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_tmpqi0de_53.tag = 53 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_impqi0de_54.tag = 54 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_l0ab_55.tag = 55 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_p0rec_56.tag = 56 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_funarrow_57.tag = 57 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_colonwith_58.tag = 58 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atme0xp_59.tag = 59 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_e0xp_60.tag = 60 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0rt_61.tag = 61 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atms0rt_62.tag = 62 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0marg_63.tag = 63 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_a0msrt_64.tag = 64 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0exp_65.tag = 65 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atms0exp_66.tag = 66 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_labs0exp_67.tag = 67 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0rtext_68.tag = 68 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_s0qua_69.tag = 69 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_q0marg_70.tag = 70 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_p0at_71.tag = 71 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atmp0at_72.tag = 72 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_labp0at_73.tag = 73 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_p0at_as_74.tag = 74 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_gm0at_75.tag = 75 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_guap0at_76.tag = 76 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_c0lau_77.tag = 77 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0exp_78.tag = 78 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0exp0_79.tag = 79 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0exp1_80.tag = 80 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_atmd0exp_81.tag = 81 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_labd0exp_82.tag = 82 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ecl_83.tag = 83 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ecl_sta_84.tag = 84 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_d0ecl_dyn_85.tag = 85 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_guad0ecl_86.tag = 86 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_filename_87.tag = 87 ;
_2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__PE_DISCARD_88.tag = 88 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__SYNENT2_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__SYNENT3_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__LIST12one_0.tag = 0 ;
// _2home_2hwxi_2research_2Postiats_2git_2src_2pats_parsing_2esats__LIST12two_1.tag = 1 ;
return ;
} /* staload function */

/* external codes at mid */
/* external codes at bot */

/* ****** ****** */

/* end of [pats_parsing_sats.c] */
