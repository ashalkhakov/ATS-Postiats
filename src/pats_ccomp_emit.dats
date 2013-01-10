(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-20?? Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (gmhwxi AT gmail DOT com)
// Start Time: November, 2012
//
(* ****** ****** *)

staload "./pats_errmsg.sats"
staload _(*anon*) = "./pats_errmsg.dats"
implement prerr_FILENAME<> () = prerr "pats_ccomp_emit"

(* ****** ****** *)

staload LAB = "./pats_label.sats"
staload STMP = "./pats_stamp.sats"

(* ****** ****** *)

staload FIL = "./pats_filename.sats"

(* ****** ****** *)

staload SYM = "./pats_symbol.sats"
staload SYN = "./pats_syntax.sats"

(* ****** ****** *)

staload GLOB = "./pats_global.sats"

(* ****** ****** *)

staload S2E = "./pats_staexp2.sats"
staload D2E = "./pats_dynexp2.sats"

(* ****** ****** *)

staload HSE = "./pats_histaexp.sats"
typedef hisexp = $HSE.hisexp
typedef hisexplst = $HSE.hisexplst

(* ****** ****** *)

staload "./pats_ccomp.sats"

(* ****** ****** *)

implement
emit_text
  (out, txt) = fprint_string (out, txt)
// end of [emit_text]

implement
emit_newline (out) = fprint_newline (out)

(* ****** ****** *)

implement
emit_symbol
  (out, sym) = $SYM.fprint_symbol (out, sym)
// end of [emit_symbol]

(* ****** ****** *)

local

staload
TM = "libc/SATS/time.sats"
stadef time_t = $TM.time_t

in // in of [local]

implement
emit_time_stamp (out) = let
//
var tm: time_t
val () = tm := $TM.time_get ()
val (pfopt | p_tm) = $TM.localtime (tm)
//
val () = emit_text (out, "/*\n");
val () = emit_text (out, "**\n");
val () = emit_text (out, "** The C code is generated by ATS/Postiats\n");
val () = emit_text (out, "** The compilation time is: ")
//
val () =
  if p_tm > null then let
  prval Some_v @(pf1, fpf1) = pfopt
  val tm_min = $TM.tm_get_min (!p_tm)
  val tm_hour = $TM.tm_get_hour (!p_tm)
  val tm_mday = $TM.tm_get_mday (!p_tm)
  val tm_mon = 1 + $TM.tm_get_mon (!p_tm)
  val tm_year = 1900 + $TM.tm_get_year (!p_tm)
  prval () = fpf1 (pf1)
in
  fprintf (out
  , "%i-%i-%i: %2ih:%2im\n"
  , @(tm_year, tm_mon, tm_mday, tm_hour, tm_min)
  )
end else let
  prval None_v () = pfopt
in
  emit_text (out, "**UNKNOWN**\n")
end // end of [if]
//
val () = emit_text (out, "**\n")
val () = emit_text (out, "*/\n")
//
in
  emit_newline (out)
end // end of [emit_time_stamp]

end // end of [local]

(* ****** ****** *)

implement
emit_ats_runtime_incl (out) = let
  val () = emit_text (out, "/*\n")
  val () = emit_text (out, "** include runtime header files\n")
  val () = emit_text (out, "*/\n")
  val () = emit_text (out, "#ifndef _ATS_HEADER_NONE\n")
  val () = emit_text (out, "#include \"pats_config.h\"\n")
  val () = emit_text (out, "#include \"pats_basics.h\"\n")
  val () = emit_text (out, "#include \"pats_typedefs.h\"\n")
  val () = emit_text (out, "#include \"pats_exception.h\"\n")
  val () = emit_text (out, "#include \"pats_memalloc.h\"\n")
  val () = emit_text (out, "#endif /* _ATS_HEADER_NONE */\n")
  val () = emit_newline (out)
in
  emit_newline (out)
end // end of [emit_ats_runtime_incl]

(* ****** ****** *)

implement
emit_ats_prelude_cats (out) = let
//
val () = emit_text (out, "/*\n")
val () = emit_text (out, "** include prelude cats files\n")
val () = emit_text (out, "*/\n")
//
val () = emit_text (out, "#ifndef _ATS_PRELUDE_NONE\n")
//
// HX: primary prelude cats files
//
val () = emit_text (out, "//\n")
val () = emit_text (out, "#include \"prelude/CATS/bool.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/char.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/float.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/integer.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/string.cats\"\n")
//
// HX: secondary prelude cats files
//
val () = emit_text (out, "//\n")
val () = emit_text (out, "#include \"prelude/CATS/list.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/option.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/array.cats\"\n")
val () = emit_text (out, "#include \"prelude/CATS/matrix.cats\"\n")
//
val () = emit_text (out, "//\n")
val () = emit_text (out, "#endif /* _ATS_PRELUDE_NONE */\n")
//
in
  emit_newline (out)
end // end of [emit_ats_prelude_cats]

(* ****** ****** *)

implement
emit_ident
  (out, name) = fprint_string (out, name)
// end of [emit_ident]

(* ****** ****** *)

implement
emit_label
  (out, lab) = () where {
  val () = $LAB.fprint_label (out, lab)
} // end of [emit_label]

implement
emit_atslabel
  (out, lab) = () where {
  val () = emit_text (out, "atslab$")
  val () = $LAB.fprint_label (out, lab)
} // end of [emit_atslabel]

implement
emit_labelext
  (out, knd, lab) = let
in
//
if knd > 0
  then emit_label (out, lab)
  else emit_atslabel (out, lab)
// end of [if]
//
end // end of [emit_labelext]

(* ****** ****** *)

implement
emit_filename
  (out, fil) = let
  val sym =
    $FIL.filename_get_full (fil)
  // end of [val]
  val name = $SYM.symbol_get_name (sym)
in
  emit_ident (out, name)
end // end of [emit_filename]

(* ****** ****** *)

implement
emit_d2con
  (out, d2c) = let
  val fil = $S2E.d2con_get_fil (d2c)
  val sym = $S2E.d2con_get_sym (d2c)
  val name = $SYM.symbol_get_name (sym)
  val () = emit_filename (out, fil)
  val () = fprint_string (out, "__")
  val () = emit_ident (out, name)
  val tag = $S2E.d2con_get_tag (d2c)
  val () = if
    tag >= 0 then let // HX: not exncon
    val () = fprintf (out, "_%i", @(tag))
  in
    // nothing
  end // end of [val]
in
  // nothing
end // end of [emit_d2con]

(* ****** ****** *)

implement
emit_d2cst
  (out, d2c) = let
//
val extdef = $D2E.d2cst_get_extdef (d2c)
//
in
//
case+ extdef of
| $SYN.DCSTEXTDEFnone () => let
    val fil = $D2E.d2cst_get_fil (d2c)
    val name = $D2E.d2cst_get_name (d2c)
    val () = emit_filename (out, fil)
    val () = fprint_string (out, "__")
    val () = emit_ident (out, name)
  in
    // nothing
  end // end of [DCSTEXTDEFnone]
//
| $SYN.DCSTEXTDEFsome_ext (name) => let
    var name: string = name
    val isemp = string_is_empty (name)
    val () = if isemp then name := $D2E.d2cst_get_name (d2c)
  in
    emit_ident (out, name)
  end // end of [DCSTEXTDEFsome_ext]
//
| $SYN.DCSTEXTDEFsome_mac (name) => let
    var name: string = name
    val isemp = string_is_empty (name)
    val () = if isemp then name := $D2E.d2cst_get_name (d2c)
  in
    emit_ident (out, name)
  end // end of [ // end of [DCSTEXTDEFsome_mac]
//
| $SYN.DCSTEXTDEFsome_sta (name) => let
    var name: string = name
    val isemp = string_is_empty (name)
    val () = if isemp then name := $D2E.d2cst_get_name (d2c)
  in
    emit_ident (out, name)
  end // end of [DCSTEXTDEFsome_sta]
//
end // end of [emit_d2cst]

(* ****** ****** *)

local

fun auxmain (
  out: FILEref, flab: funlab
) : void = let
//
val qopt = funlab_get_d2copt (flab)
val tmparg = funlab_get_tmparg (flab)
//
val () = (
  case+ qopt of
  | Some (d2c) => let
      val () = emit_d2cst (out, d2c)
    in
    end // end of [Some]
  | None () => let
      val () = emit_ident (out, funlab_get_name (flab))
    in
    end // end of [None]
) : void // end of [val]
//
val tmpknd =
  funlab_get_tmpknd (flab)
val () =
  if tmpknd > 0 then {
  val () =
    fprint_string (out, "$")
  val stamp = funlab_get_stamp (flab)
  val () = $STMP.fprint_stamp (out, stamp)
} // end of [val]
//
in
  // nothing
end // end of [auxmain]

in // in of [local]

implement
emit_funlab
  (out, flab) = let
//
val opt = funlab_get_origin (flab)
val () = (
  case+ opt of
  | Some (
     flab_1 // origin
    ) => emit_funlab (out, flab_1)
  | None () => auxmain (out, flab)
) // end of [val]
val sfx = funlab_get_suffix (flab)
val () = if sfx > 0 then fprintf (out, "$%i", @(sfx))
//
in
  // nothing
end // end of [emit_funlab]

end // end of [local]

(* ****** ****** *)

implement
emit_tmpvar
  (out, tmp) = let
//
val knd =
  tmpvar_get_topknd (tmp)
//
val () = (case+ 0 of
  | _ when knd = 0 => let
    in
      fprint_string (out, "tmp") // local temporary variable
    end // end of [_]
  | _ (*(static)top*) => let
    in
      fprint_string (out, "statmp") // static toplevel temporary
    end // end of [knd = 1]
) : void // end of [val]
//
val opt = tmpvar_get_origin (tmp)
//
in
//
case+ opt of
| Some (tmpp) => let
    val sfx = tmpvar_get_suffix (tmp)
    val stmp = tmpvar_get_stamp (tmpp)
    val () = $STMP.fprint_stamp (out, stmp)
    val () = fprintf (out, "$%i", @(sfx))
  in
    // nothing
  end // end of [Some]
| None () => let
    val stmp = tmpvar_get_stamp (tmp)
    val () = $STMP.fprint_stamp (out, stmp)
  in
    // nothing
  end // end of [None]
//
end // end of [emit_tmpvar]

(* ****** ****** *)

implement
emit_tmpdec
  (out, tmp) = let
  val hse = tmpvar_get_type (tmp)
  val () = emit_hisexp (out, hse)
  val () = fprint_string (out, " ")
  val () = emit_tmpvar (out, tmp)
  val () = fprint_string (out, " ; \n")
in
  // nothing
end // end of [emit_tmpdec]

implement
emit_tmpdeclst
  (out, tmps) = let
in
//
case+ tmps of
| list_cons
    (tmp, tmps) => let
    val () = emit_tmpdec (out, tmp) in emit_tmpdeclst (out, tmps)
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [emit_tmpdeclst]

(* ****** ****** *)

typedef
emit_primval_type = (FILEref, primval) -> void

(* ****** ****** *)

extern fun emit_primval_tmp : emit_primval_type
extern fun emit_primval_tmpref : emit_primval_type
extern fun emit_primval_arg : emit_primval_type
extern fun emit_primval_argref : emit_primval_type
extern fun emit_primval_d2cst : emit_primval_type
extern fun emit_primval_bool : emit_primval_type

(* ****** ****** *)

implement
emit_primval
  (out, pmv0) = let
  val loc0 = pmv0.primval_loc
in
//
case+ pmv0.primval_node of
| PMVtmp _ => emit_primval_tmp (out, pmv0)
| PMVtmpref _ => emit_primval_tmpref (out, pmv0)
| PMVarg _ => emit_primval_arg (out, pmv0)
(*
| PMVargref _ => emit_primval_argref (out, pmv0)
*)
(*
| PMVcst _ => emit_primval_d2cst (out, pmv0)
*)
//
| PMVbool _ => emit_primval_bool (out, pmv0)
//
| PMVi0nt (tok) => $SYN.fprint_i0nt (out, tok)
| PMVf0loat (tok) => $SYN.fprint_f0loat (out, tok)
//
| _ => let
(*
    val () = prerr_interror_loc (loc0)
    val () = (
      prerr ": emit_primval: pmv0 = "; prerr pmv0; prerr_newline ()
    ) // end of [val]
    val () = assertloc (false)
*)
  in
    fprint_primval (out, pmv0)
  end // end of [_]
//
end // end of [emit_primval]

(* ****** ****** *)

implement
emit_primvalist
  (out, pmvs) = let
//
fun loop (
  out: FILEref, pmvs: primvalist, i: int
) : void = let
in
//
case+ pmvs of
| list_cons
    (pmv, pmvs) => let
    val () =
      if i > 0 then fprint_string (out, ", ")
    // end of [val]
    val () = emit_primval (out, pmv)
  in
    loop (out, pmvs, i+1)
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [loop]
//
in
  loop (out, pmvs, 0)
end // end of [emit_primvalist]

(* ****** ****** *)

implement
emit_primval_tmp
  (out, pmv0) = let
//
val- PMVtmp (tmp) = pmv0.primval_node
//
in
  emit_tmpvar (out, tmp)
end // end of [emit_primval_tmp]

implement
emit_primval_tmpref
  (out, pmv0) = let
//
val- PMVtmpref (tmp) = pmv0.primval_node
//
in
  emit_tmpvar (out, tmp)
end // end of [emit_primval_tmpref]

(* ****** ****** *)

implement
emit_primval_arg
  (out, pmv0) = let
//
val- PMVarg (ind) = pmv0.primval_node
//
in
  fprintf (out, "arg%i", @(ind))
end // end of [emit_primval_arg]

(* ****** ****** *)

implement
emit_primval_d2cst
  (out, pmv0) = let
//
val- PMVcst (d2c) = pmv0.primval_node
//
in
  emit_d2cst (out, d2c)
end // end of [emit_primval_d2cst]

(* ****** ****** *)

implement
emit_primval_bool
  (out, pmv0) = let
//
val- PMVbool (b) = pmv0.primval_node
val name = (
  if b then "atsbool_true" else "atsbool_false"
) : string // end of [val]
//
in
  fprint_string (out, name)
end (* end of [emit_primval_bool] *)

(* ****** ****** *)

implement
emit_tmpvar_assgn
  (out, tmp, pmv) = {
  val () = emit_tmpvar (out, tmp)
  val () = fprint_string (out, " = ")
  val () = emit_primval (out, pmv)
} // end of [emit_tmpvar_assgn]

(* ****** ****** *)

implement
emit_s2exp
  (out, s2e) = let
in
//
case+ s2e.s2exp_node of
| $S2E.S2Etkname
    (name) => emit_ident (out, name)
  // end of [S2Etkname]
| _ => $S2E.fprint_s2exp (out, s2e)
//
end // end of [emit_s2exp]

(* ****** ****** *)

implement
emit_hisexp
  (out, hse) = let
in
//
case+
  hse.hisexp_node of
| $HSE.HSEtyptr (
  ) => emit_text (out, "atstype_ptr")
| $HSE.HSEtyabs (sym) => emit_symbol (out, sym)
| $HSE.HSEapp
    (_fun, _arg) => let
    val () = emit_hisexp (out, _fun)
    val () = emit_text (out, "(")
    val () = emit_hisexplst_sep (out, _arg, ", ")
    val () = emit_text (out, ")")
  in
    // nothing
  end // end of [HSEapp]
| $HSE.HSEs2exp (s2e) => emit_s2exp (out, s2e)
| _ => $HSE.fprint_hisexp (out, hse)
//
end // end of [emit_hisexp]

implement
emit_hisexplst_sep
  (out, hses, sep) = let
//
fun loop (
  out: FILEref
, hses: hisexplst, sep: string, i: int
) : void = let
in
  case+ hses of
  | list_cons (
      hse, hses
    ) => let
      val () =
        if i > 0 then fprint_string (out, sep)
      // end of [val]
      val () = emit_hisexp (out, hse)
    in
      loop (out, hses, sep, i+1)
    end // end of [list_cons]
  | list_nil () => ()
end // end of [loop]
//
in
  loop (out, hses, sep, 0)
end // end of [emit_hisexplst_sep]

(* ****** ****** *)

implement
emit_funtype_arg_res (
  out, hses_arg, hse_res
) = let
  val () = emit_hisexp (out, hse_res)
  val () = fprint_string (out, "(*)(")
  val () = emit_hisexplst_sep (out, hses_arg, ", ")
  val () = fprint_string (out, ")")
in
  // nothing
end // end of [emit_funtype_arg_res]

(* ****** ****** *)

typedef
emit_instr_type = (FILEref, instr) -> void

extern fun emit_instr_funcall : emit_instr_type

(* ****** ****** *)

local

fun emit_instr_move_rec
  (out: FILEref, ins: instr): void = let
//
fun loop (
  recknd: int
, extknd: int
, tmp: tmpvar
, lxs: labprimvalist
, i: int
) :<cloref1> void = let
in
//
case+ lxs of
| list_cons
    (lx, lxs) => let
    val LABPRIMVAL (l, x) = lx
    val () =
      if i > 0 then emit_text (out, "\n")
    val () =
      if recknd = 0 then emit_text (out, "ATSMACmove_fltrec_ofs (")
    val () =
      if recknd > 0 then emit_text (out, "ATSMACmove_boxrec_ofs (")
    val () = emit_tmpvar (out, tmp)
    val () = emit_text (out, ", ")
    val () = emit_labelext (out, extknd, l)
    val () = emit_text (out, ", ")
    val () = emit_primval (out, x)
    val () = emit_text (out, ") ;")
  in
    loop (recknd, extknd, tmp, lxs, i+1)
  end
| list_nil () => ()
//
end // end of [loop]
//
fun hisexp_get_extknd
  (hse: hisexp): int = (
  case+ hse.hisexp_node of
  | $HSE.HSEtyrec (knd, _) =>
      if $S2E.tyreckind_is_ext (knd) then 1 else 0
  | _ => ~1 // HX: meaningless
) // end of [hisexp_get_extknd]
//
in
//
case- ins.instr_node of
| INSmove_fltrec (
    tmp, lpmvs, hse_rec
  ) => let
    val extknd =
      hisexp_get_extknd (hse_rec)
    // end of [val]
  in
    loop (0(*recknd*), extknd, tmp, lpmvs, 0)
  end // end of [INSmove_fltrec]
| INSmove_boxrec (
    tmp, lpmvs, hse_rec
  ) => let
    val extknd =
      hisexp_get_extknd (hse_rec)
    // end of [val]
  in
    loop (1(*recknd*), extknd, tmp, lpmvs, 0)
  end // end of [INSmove_boxrec]
//
end // end of [emit_instr_move_rec]

in // in of [local]

implement
emit_instr
  (out, ins) = let
//
val loc0 = ins.instr_loc
//
// generating #line progma for debugging
//
val gline =
  $GLOB.the_DEBUGATS_dbgline_get ()
val () = (
  if gline > 0 then $LOC.fprint_line_pragma (out, loc0)
) : void // end of [val]
//
val gflag =
  $GLOB.the_DEBUGATS_dbgflag_get ()
val () = (
//
// HX: generating debug information
//
  if gflag > 0 then let
    val () = fprint_string (out, "/* ")
    val () = fprint_instr (out, ins)
    val () = fprint_string (out, " */\n")
  in
    // empty
  end // end of [if]
) : void // end of [val]
//
in
//
case+ ins.instr_node of
//
| INSfunlab (flab) => {
    val () =
      fprint_string (out, "__pats_lab_")
    val () = emit_funlab (out, flab)
    val () = fprint_string (out, ":")
  } // end of [INSfunlab]
//
| INSmove_val
    (tmp, pmv) => {
    val isvoid = primval_is_void (pmv)
    val () = if isvoid then fprint_string (out, "/* ")
    val () = emit_tmpvar_assgn (out, tmp, pmv)
    val () = if isvoid then fprint_string (out, " */")
    val () = fprint_string (out, " ;")
  } // end of [INSmove_val]
//
| INSmove_fltrec _ => emit_instr_move_rec (out, ins)
| INSmove_boxrec _ => emit_instr_move_rec (out, ins)
//
| INSfuncall _ => emit_instr_funcall (out, ins)
//
| INScond (
    pmv_cond, inss_then, inss_else
  ) => {
    val () = fprint_string (out, "if (")
    val () = emit_primval (out, pmv_cond)
    val () = fprint_string (out, ") {\n")
    val () = emit_instrlst (out, inss_then)
    val () = fprint_string (out, "\n} else {\n")
    val () = emit_instrlst (out, inss_else)
    val () =
      fprint_string (out, "\n} /* end of [if] */")
    // end of [val]
  } // end of [INScond]
//
| INSletpop () => let
    val () = fprint_string (out, "/*\n")
    val () = fprint_instr (out, ins)
    val () = fprint_string (out, "\n*/")
  in
    // nothing
  end // end of [INSletpop]
| INSletpush (pmds) => let
    val () = fprint_string (out, "/*\n")
    val () = fprint_instr (out, ins)
    val () = fprint_string (out, "\n*/\n")
    val () = emit_primdeclst (out, pmds)
  in
    // nothing
  end // end of [INSletpush]
//
| _ => let
    val () = prerr_interror_loc (loc0)
    val () = (
      prerr ": emit_instr: ins = "; prerr_instr (ins); prerr_newline ()
    ) // end of [val]
    val () = assertloc (false)
  in
    // nothing
  end // end of [_]
end // end of [emit_instr]

end // end of [local]

(* ****** ****** *)

implement
emit_instrlst
  (out, inss) = let
//
fun loop (
  out: FILEref, inss: instrlst, sep: string, i: int
) : void = let
in
//
case+ inss of
| list_cons
    (ins, inss) => let
    val () =
      if i > 0 then
        fprint_string (out, sep)
      // end of [if]
    val () = emit_instr (out, ins)
  in
    loop (out, inss, sep, i+1)
  end // end of [list_cons]
| list_nil () => let
    val () =
      if i = 0 then fprint_string (out, "/* (*nothing*) */")
    // end of [val]
  in
    // nothing
  end // end of [list_nil]
//
end // end of [loop]
//
in
  loop (out, inss, "\n", 0)
end // end of [emit_instrlst]    

implement
emit_instrlst_ln
  (out, inss) = let
  val () =
    emit_instrlst (out, inss) in fprint_string (out, "\n")
  // end of [val]
end // end of [emit_instrlst_ln]

(* ****** ****** *)

implement
emit_instr_funcall
  (out, ins) = let
//
val loc0 = ins.instr_loc
val- INSfuncall
  (tmp, pmv_fun, hse_fun, pmvs_arg) = ins.instr_node
(*
val () = (
  println! ("emit_instr_funcall: pmv_fun = ", pmv_fun)
) // end of [val]
*)
val isvoid = false
val () = if isvoid then fprint_string (out, "/* ")
val () = (
  emit_tmpvar (out, tmp); fprint_string (out, " = ")
) // end of [val]
val () = if isvoid then fprint_string (out, "*/ ")
//
in
//
case+ pmv_fun.primval_node of
//
| PMVfunlab (flab) => let
    val () = emit_funlab (out, flab)
    val () = fprint_string (out, "(")
    val () = emit_primvalist (out, pmvs_arg)
    val () = fprint_string (out, ") ;")
  in
    // nothing
  end // end of [PMVfun]
//
| PMVcst (d2c) => let
    val () = emit_d2cst (out, d2c)
    val () = fprint_string (out, "(")
    val () = emit_primvalist (out, pmvs_arg)
    val () = fprint_string (out, ") ;")
  in
    // nothing
  end // end of [PMVcst]
//
| PMVtmpltcst _ => let
    val () = emit_primval (out, pmv_fun)
    val () = fprint_string (out, "(")
    val () = emit_primvalist (out, pmvs_arg)
    val () = fprint_string (out, ") ;")
  in
    // nothing
  end // end of [PMVtmpltcst]
| PMVtmpltcstmat _ => let
    val () = emit_primval (out, pmv_fun)
    val () = fprint_string (out, "(")
    val () = emit_primvalist (out, pmvs_arg)
    val () = fprint_string (out, ") ;")
  in
    // nothing
  end // end of [PMVtmpltcstmat]
//
| PMVtmpltvar _ => let
    val () = emit_primval (out, pmv_fun)
    val () = fprint_string (out, "(")
    val () = emit_primvalist (out, pmvs_arg)
    val () = fprint_string (out, ") ;")
  in
    // nothing
  end // end of [PMVtmpltvar]
//
| _(*function variable*) => let
    val () = emit_primval (out, pmv_fun)
    val () = fprint_string (out, "(")
    val () = emit_primvalist (out, pmvs_arg)
    val () = fprint_string (out, ") ;")
  in
    // nothing
  end // end of [_]
//
(*
| _ => let
    val () = prerr_interror_loc (loc0)
    val () = (
      prerr ": emit_instr_funcall: hse_fun = "; $HSE.prerr_hisexp (hse_fun); prerr_newline ()
    ) // end of [val]
    val () = assertloc (false)
  in
    // nothing
  end // end of [_]
*)
//
end // end of [emit_instr_funcall]

(* ****** ****** *)

implement
emit_funarglst
  (out, hses) = let
//
fun loop (
  out: FILEref
, hses: hisexplst, sep: string, i: int
) : void = let
in
//
case+ hses of
| list_cons
    (hse, hses) => let
    val () =
      if i > 0 then fprint_string (out, sep)
    val () = emit_hisexp (out, hse)
    val () = fprintf (out, " arg%i", @(i))
  in
    loop (out, hses, sep, i+1)
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [loop]
//
in
  loop (out, hses, ", ", 0)
end // end of [emit_funarglst]

(* ****** ****** *)

local

fun auxfun (
  out: FILEref, fent: funent
) : void = let
//
  val flab = funent_get_lab (fent)
  val tmpknd = funlab_get_tmpknd (flab)
  val qopt = funlab_get_d2copt (flab)
  val isqua = (
    case+ qopt of Some _ => true | None _ => false
  ) : bool // end of [val]
  val flopt = funlab_get_origin (flab)
  val isext = (
    case+ flopt of Some _ => false | None () => isqua
  ) : bool // end of [val]
  val issta = not (isext)
//
  val () =
    if tmpknd > 0 then emit_text (out, "#if(0)\n")
  // end of [val]
//
  val () = if isext then emit_text (out, "extern\n")
  val () = if issta then emit_text (out, "static\n")
//
  val () =
    emit_hisexp (out, hse_res) where {
    val hse_res = funlab_get_type_res (flab)
  }
//
  val () = emit_text (out, "\n")
  val () = emit_funlab (out, flab)
  val () = emit_text (out, " (")
//
  val () =
    emit_funarglst (out, hses_arg) where {
    val hses_arg = funlab_get_type_arg (flab)
  } // end of [val]
//
  val () = emit_text (out, ") ;\n")
//
  val () =
    if tmpknd > 0 then emit_text (out, "#endif // end of [TEMPLATE]\n")
  // end of [val]
//
  val () = emit_newline (out)
//
in
  // nothing
end // end of [auxfun]

in // in of [local]

implement
emit_funent_ptype
  (out, fent) = let
//
  val () = auxfun (out, fent)
//
in
  // nothing
end // end of [emit_funentry_ptype]

end // end of [local]

(* ****** ****** *)

local

fun auxtmp (
  out: FILEref, fent: funent
) : void = let
//
val imparg = funent_get_imparg (fent)
val tmparg = funent_get_tmparg (fent)
val tsubopt = funent_get_tmpsub (fent)
//
val () = emit_text (out, "/*\n")
val () = emit_text (out, "imparg = ")
val () = $S2E.fprint_s2varlst (out, imparg)
val () = emit_text (out, "\n")
val () = emit_text (out, "tmparg = ")
val () = $S2E.fprint_s2explstlst (out, tmparg)
val () = emit_text (out, "\n")
val () = emit_text (out, "tmpsub = ")
val () = fprint_tmpsubopt (out, tsubopt)
val () = emit_text (out, "\n")
val () = emit_text (out, "*/\n")
//
in
  // nothing
end // end of [auxtmp]

in // in of [local]

implement
emit_funent_implmnt
  (out, fent) = let
//
val loc0 = funent_get_loc (fent)
//
val flab = funent_get_lab (fent)
//
val fc = funlab_get_funclo (flab)
val hses_arg = funlab_get_type_arg (flab)
val hse_res = funlab_get_type_res (flab)
//
val tmpret = funent_get_tmpret (fent)
//
// function header
//
val knd =
  funlab_get_tmpknd (flab)
val qopt =
  funlab_get_d2copt (flab)
val isqua =
  (case+ qopt of Some _ => true | None _ => false): bool
// end of [val]
val flopt = funlab_get_origin (flab)
val isext = (
  case+ flopt of Some _ => false | None () => isqua
) : bool // end of [val]
val issta = not (isext)
//
val () =
  if isext then emit_text (out, "ATSglobaldec()\n")
val () =
  if issta then emit_text (out, "ATSstaticdec()\n")
//
val istmp = funent_is_tmplt (fent)
val () = if istmp then auxtmp (out, fent)
//
val () = emit_hisexp (out, hse_res)
val () = emit_text (out, "\n")
val () = emit_funlab (out, flab)
val () = emit_text (out, " (")
val () = emit_funarglst (out, hses_arg)
val () = emit_text (out, ")\n")
//
// function body
//
val () = emit_text (out, "{\n")
val tmplst = funent_get_tmpvarlst (fent)
val () = emit_text (out, "/* tmpdeclst: beg */\n")
val () = emit_tmpdeclst (out, tmplst)
val () = emit_text (out, "/* tmpdeclst: end */\n")
val body_inss = funent_get_instrlst (fent)
val () = emit_instrlst (out, body_inss)
val () = emit_text (out, "\n")
//
// function return
//
val () = emit_text (out, "\n")
val () = emit_text (out, "return ")
val isvoid = tmpvar_is_void (tmpret)
val () =
  if isvoid then emit_text (out, "/* ")
val () = emit_tmpvar (out, tmpret)
val () =
  if isvoid then emit_text (out, " */")
val () = emit_text (out, " ;")
//
val () = emit_text (out, "\n}")
val () =
  emit_text (out, " /* end of [")
val () = emit_funlab (out, flab)
val () = emit_text (out, "] */\n")
//
in
end // end of [emit_funent_implmnt]

end // end of [local]

(* ****** ****** *)

local

staload UN = "prelude/SATS/unsafe.sats"

fun emit_primdec
  (out: FILEref, pmd: primdec) : void = let
in
//
case+ pmd.primdec_node of
//
| PMDnone () => ()
//
| PMDdatdecs _ => ()
//
| PMDfundecs _ => ()
//
| PMDvaldecs
    (knd, hvds, inss) =>
    emit_instrlst_ln (out, $UN.cast{instrlst}(inss))
| PMDvaldecs_rec (knd, hvds, inss) =>
    emit_instrlst_ln (out, $UN.cast{instrlst}(inss))
//
| PMDvardecs (hvds, inss) =>
    emit_instrlst_ln (out, $UN.cast{instrlst}(inss))
//
| PMDimpdec _ => ()
//
| PMDstaload _ => ()
//
| PMDlocal (
    pmds_head, pmds_body
  ) => {
    val () =
      emit_text (out, "/* local */\n")
    val () = emit_primdeclst (out, pmds_head)
    val () =
      emit_text (out, "/* in of [local] */\n")
    val () = emit_primdeclst (out, pmds_body)
    val () =
      emit_text (out, "/* end of [local] */\n")
    // end of [val]
  } // end of [PMDlocal]
//
end // end of [emit_primdec]

in // in of [local]

implement
emit_primdeclst
  (out, pmds) = let
in
//
case+ pmds of
| list_cons
    (pmd, pmds) => let
    val () =
      emit_primdec (out, pmd) in emit_primdeclst (out, pmds)
    // end of [val]
  end // end of [list_cons]
| list_nil () => ()
//
end // end of [emit_primdeclst]

end // end of [local]

(* ****** ****** *)

(* end of [pats_ccomp_emit.dats] *)
