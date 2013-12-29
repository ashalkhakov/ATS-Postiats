(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2010-2013 Hongwei Xi, ATS Trustful Software, Inc.
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

(*
** Source:
** $PATSHOME/prelude/DATS/CODEGEN/checkast.atxt
** Time of generation: Fri Dec 27 17:19:38 2013
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: gmhwxiATgmailDOTcom *)
(* Start time: December, 2013 *)

(* ****** ****** *)

staload "prelude/SATS/checkast.sats"

(* ****** ****** *)

implement{tk}
checkast_gintLt
  (x, i, errmsg) = let
  val x = g1ofg0_int(x)
in
//
if x < i
  then (x)
  else let
    val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
    // end of [val]
  end // end of [else]
//
end // end of [checkast_gintLt]

(* ****** ****** *)

implement{tk}
checkast_gintLte
  (x, i, errmsg) = let
  val x = g1ofg0_int(x)
in
//
if x <= i
  then (x)
  else let
    val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
    // end of [val]
  end // end of [else]
//
end // end of [checkast_gintLte]

(* ****** ****** *)

implement{tk}
checkast_gintGt
  (x, i, errmsg) = let
  val x = g1ofg0_int(x)
in
//
if x > i
  then (x)
  else let
    val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
    // end of [val]
  end // end of [else]
//
end // end of [checkast_gintGt]

(* ****** ****** *)

implement{tk}
checkast_gintGte
  (x, i, errmsg) = let
  val x = g1ofg0_int(x)
in
//
if x >= i
  then (x)
  else let
    val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
    // end of [val]
  end // end of [else]
//
end // end of [checkast_gintGte]

(* ****** ****** *)

implement{tk}
checkast_gintBtw
  (x, i, j, errmsg) = let
  val x = g1ofg0_int(x)
in
//
if x >= i
  then
    if x < j then (x)
    else let
      val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
      // end of [val]
    end // end of [else]
  else let
    val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
    // end of [val]
  end // end of [else]
//
end // end of [checkast_gintBtw]

(* ****** ****** *)

implement{tk}
checkast_gintBtwe
  (x, i, j, errmsg) = let
  val x = g1ofg0_int(x)
in
//
if x >= i
  then
    if x <= j then (x)
    else let
      val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
      // end of [val]
    end // end of [else]
  else let
    val () =
      fprint! (stderr_ref, "exit(ATS): ", errmsg) in exit(1)
    // end of [val]
  end // end of [else]
//
end // end of [checkast_gintBtwe]

(* ****** ****** *)

(* end of [checkast.dats] *)
