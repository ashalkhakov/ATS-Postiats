/*
**
** Source: pats_ccomp_runtime2.dats
**
** The C code is generated by ATS/Postiats
** The compilation time is: 2013-10-20: 21h:48m
**
*/
/*
typedefs-for-tyrecs-and-tysums(beg)
*/
typedef
struct {
int exntag ;
char *exnmsg ;
atstkind_type(atstype_ptrk) atslab__0; 
} pats_ccomp_runtime2_tyexn_0 ;
/*
typedefs-for-tyrecs-and-tysums(end)
*/
/*
dynconlst-declaration(beg)
*/
/*
dynconlst-declaration(end)
*/
/*
dyncstlst-declaration(beg)
*/
ATSdyncst_mac(atspre_prerr_string) ;
ATSdyncst_mac(atspre_prerr_newline) ;
ATSdyncst_mac(atspre_exit) ;
ATSdyncst_extfun(atsruntime_handle_uncaughtexn_rest, (atstype_exnconptr), atsvoid_t0ype) ;
/*
dyncstlst-declaration(end)
*/
/*
dynvalist-implementation(beg)
*/
/*
dynvalist-implementation(end)
*/
/*
exnconlst-declaration(beg)
*/
#ifndef _ATS_EXCEPTION_NONE
extern void the_atsexncon_initize (atstype_exncon *d2c, char *exnmsg) ;
#endif // end of [_ATS_EXCEPTION_NONE]
/*
exnconlst-declaration(end)
*/
/*
assumelst-declaration(beg)
*/
/*
assumelst-declaration(end)
*/
#if(0)
ATSglobaldec()
atsvoid_t0ype
atsruntime_handle_uncaughtexn(atstype_exnconptr) ;
#endif // end of [QUALIFIED]

/*
/home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1539(line=43, offs=3) -- 2265(line=71, offs=4)
*/
/*
local: 
global: atsruntime_handle_uncaughtexn$0$0(level=0)
local: 
global: 
*/
ATSglobaldec()
atsvoid_t0ype
atsruntime_handle_uncaughtexn(void *arg0)
{
/* tmpvardeclst(beg) */
ATStmpdec_void(tmpret0, atsvoid_t0ype) ;
ATStmpdec(tmp1, atstkind_type(atstype_ptrk)) ;
ATStmpdec(tmp2, atstkind_type(atstype_ptrk)) ;
ATStmpdec_void(tmp3, atsvoid_t0ype) ;
ATStmpdec_void(tmp4, atsvoid_t0ype) ;
ATStmpdec_void(tmp5, atsvoid_t0ype) ;
ATStmpdec_void(tmp6, atsvoid_t0ype) ;
ATStmpdec_void(tmp7, atsvoid_t0ype) ;
ATStmpdec_void(tmp8, atsvoid_t0ype) ;
ATStmpdec_void(tmp9, atsvoid_t0ype) ;
ATStmpdec_void(tmp10, atsvoid_t0ype) ;
ATStmpdec_void(tmp11, atsvoid_t0ype) ;
ATStmpdec_void(tmp12, atsvoid_t0ype) ;
ATStmpdec_void(tmp13, atsvoid_t0ype) ;
ATStmpdec_void(tmp14, atsvoid_t0ype) ;
ATStmpdec_void(tmp15, atsvoid_t0ype) ;
ATStmpdec_void(tmp16, atsvoid_t0ype) ;
/* tmpvardeclst(end) */
/* funbodyinstrlst(beg) */
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1507(line=42, offs=1) -- 2265(line=71, offs=4)
*/
__patsflab_atsruntime_handle_uncaughtexn:
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1639(line=51, offs=1) -- 2258(line=69, offs=48)
*/
ATScaseofbeg()
/*
** ibranchlst-beg
*/
ATSbranchbeg() ;
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1654(line=52, offs=3) -- 1667(line=52, offs=16)
*/
__atstmplab0:
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1540(line=43, offs=4) -- 1543(line=43, offs=7)
*/
ATSifnot(ATSPATCKexn0(arg0, ATSLIB_056_prelude__AssertExn)) { ATSgoto(__atstmplab2) ; }
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1667(line=52, offs=16) -- 1667(line=52, offs=16)
*/
__atstmplab1:
/*
emit_instr: loc0 = : 0(line=0, offs=0) -- 0(line=0, offs=0)
*/
/*
ibranch-mbody:
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1671(line=52, offs=20) -- 1756(line=55, offs=6)
*/
/*
letpush(beg)
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1688(line=53, offs=14) -- 1701(line=53, offs=27)
*/
ATSINSmove_void(tmp3, atspre_prerr_string(ATSPMVstring("exit(ATS): uncaught exception at run-time"))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1715(line=54, offs=14) -- 1739(line=54, offs=38)
*/
ATSINSmove_void(tmp4, atspre_prerr_string(ATSPMVstring(": AssertExn"))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1715(line=54, offs=14) -- 1739(line=54, offs=38)
*/
ATSINSmove_void(tmp5, atspre_prerr_newline()) ;

/*
letpush(end)
*/

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1743(line=54, offs=42) -- 1749(line=54, offs=48)
*/
ATSINSmove_void(tmpret0, atspre_exit(ATSPMVi0nt(1))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1671(line=52, offs=20) -- 1756(line=55, offs=6)
*/
/*
INSletpop()
*/
ATSbranchend() ;

ATSbranchbeg() ;
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1783(line=56, offs=3) -- 1798(line=56, offs=18)
*/
__atstmplab2:
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1540(line=43, offs=4) -- 1543(line=43, offs=7)
*/
ATSifnot(ATSPATCKexn0(arg0, ATSLIB_056_prelude__NotFoundExn)) { ATSgoto(__atstmplab4) ; }
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1798(line=56, offs=18) -- 1798(line=56, offs=18)
*/
__atstmplab3:
/*
emit_instr: loc0 = : 0(line=0, offs=0) -- 0(line=0, offs=0)
*/
/*
ibranch-mbody:
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1802(line=56, offs=22) -- 1889(line=59, offs=6)
*/
/*
letpush(beg)
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1819(line=57, offs=14) -- 1832(line=57, offs=27)
*/
ATSINSmove_void(tmp6, atspre_prerr_string(ATSPMVstring("exit(ATS): uncaught exception at run-time"))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1846(line=58, offs=14) -- 1872(line=58, offs=40)
*/
ATSINSmove_void(tmp7, atspre_prerr_string(ATSPMVstring(": NotFoundExn"))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1846(line=58, offs=14) -- 1872(line=58, offs=40)
*/
ATSINSmove_void(tmp8, atspre_prerr_newline()) ;

/*
letpush(end)
*/

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1876(line=58, offs=44) -- 1882(line=58, offs=50)
*/
ATSINSmove_void(tmpret0, atspre_exit(ATSPMVi0nt(1))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1802(line=56, offs=22) -- 1889(line=59, offs=6)
*/
/*
INSletpop()
*/
ATSbranchend() ;

ATSbranchbeg() ;
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1916(line=60, offs=3) -- 1935(line=60, offs=22)
*/
__atstmplab4:
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1540(line=43, offs=4) -- 1543(line=43, offs=7)
*/
ATSifnot(ATSPATCKexn1(arg0, ATSLIB_056_prelude__GenerallyExn)) { ATSgoto(__atstmplab6) ; }
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1935(line=60, offs=22) -- 1935(line=60, offs=22)
*/
__atstmplab5:
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1931(line=60, offs=18) -- 1934(line=60, offs=21)
*/
ATSINSmove(tmp1, ATSSELcon(arg0, pats_ccomp_runtime2_tyexn_0, atslab__0)) ;
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1916(line=60, offs=3) -- 2034(line=63, offs=6)
*/
/*
ATSINSfreecon(arg0) ;
*/
/*
emit_instr: loc0 = : 0(line=0, offs=0) -- 0(line=0, offs=0)
*/
/*
ibranch-mbody:
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1939(line=60, offs=26) -- 2034(line=63, offs=6)
*/
/*
letpush(beg)
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1956(line=61, offs=14) -- 1969(line=61, offs=27)
*/
ATSINSmove_void(tmp9, atspre_prerr_string(ATSPMVstring("exit(ATS): uncaught exception at run-time"))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1983(line=62, offs=14) -- 2017(line=62, offs=48)
*/
ATSINSmove_void(tmp10, atspre_prerr_string(ATSPMVstring(": GenerallyExn: "))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1983(line=62, offs=14) -- 2017(line=62, offs=48)
*/
ATSINSmove_void(tmp11, atspre_prerr_string(tmp1)) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1983(line=62, offs=14) -- 2017(line=62, offs=48)
*/
ATSINSmove_void(tmp12, atspre_prerr_newline()) ;

/*
letpush(end)
*/

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2021(line=62, offs=52) -- 2027(line=62, offs=58)
*/
ATSINSmove_void(tmpret0, atspre_exit(ATSPMVi0nt(1))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1939(line=60, offs=26) -- 2034(line=63, offs=6)
*/
/*
INSletpop()
*/
ATSbranchend() ;

ATSbranchbeg() ;
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2061(line=64, offs=3) -- 2081(line=64, offs=23)
*/
__atstmplab6:
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 1540(line=43, offs=4) -- 1543(line=43, offs=7)
*/
ATSifnot(ATSPATCKexn1(arg0, ATSLIB_056_prelude__IllegalArgExn)) { ATSgoto(__atstmplab8) ; }
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2081(line=64, offs=23) -- 2081(line=64, offs=23)
*/
__atstmplab7:
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2077(line=64, offs=19) -- 2080(line=64, offs=22)
*/
ATSINSmove(tmp2, ATSSELcon(arg0, pats_ccomp_runtime2_tyexn_0, atslab__0)) ;
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2061(line=64, offs=3) -- 2181(line=67, offs=6)
*/
/*
ATSINSfreecon(arg0) ;
*/
/*
emit_instr: loc0 = : 0(line=0, offs=0) -- 0(line=0, offs=0)
*/
/*
ibranch-mbody:
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2085(line=64, offs=27) -- 2181(line=67, offs=6)
*/
/*
letpush(beg)
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2102(line=65, offs=14) -- 2115(line=65, offs=27)
*/
ATSINSmove_void(tmp13, atspre_prerr_string(ATSPMVstring("exit(ATS): uncaught exception at run-time"))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2129(line=66, offs=14) -- 2164(line=66, offs=49)
*/
ATSINSmove_void(tmp14, atspre_prerr_string(ATSPMVstring(": IllegalArgExn: "))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2129(line=66, offs=14) -- 2164(line=66, offs=49)
*/
ATSINSmove_void(tmp15, atspre_prerr_string(tmp2)) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2129(line=66, offs=14) -- 2164(line=66, offs=49)
*/
ATSINSmove_void(tmp16, atspre_prerr_newline()) ;

/*
letpush(end)
*/

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2168(line=66, offs=53) -- 2174(line=66, offs=59)
*/
ATSINSmove_void(tmpret0, atspre_exit(ATSPMVi0nt(1))) ;

/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2085(line=64, offs=27) -- 2181(line=67, offs=6)
*/
/*
INSletpop()
*/
ATSbranchend() ;

ATSbranchbeg() ;
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2214(line=69, offs=4) -- 2214(line=69, offs=4)
*/
__atstmplab8:
/*
emit_instr: loc0 = : 0(line=0, offs=0) -- 0(line=0, offs=0)
*/
/*
ibranch-mbody:
*/
/*
emit_instr: loc0 = /home/hwxi/research/Postiats/git/ccomp/runtime/pats_ccomp_runtime2.dats: 2218(line=69, offs=8) -- 2257(line=69, offs=47)
*/
ATSINSmove_void(tmpret0, atsruntime_handle_uncaughtexn_rest(arg0)) ;

ATSbranchend() ;

/*
** ibranchlst-end
*/
ATScaseofend()

/* funbodyinstrlst(end) */
ATSreturn_void(tmpret0) ;
} /* end of [atsruntime_handle_uncaughtexn] */

/* ****** ****** */

/* end of [pats_ccomp_runtime2_dats.c] */
