(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2016 Hongwei Xi, ATS Trustful Software, Inc.
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

(* Author: Hongwei Xi *)
(* Start time: November, 2016 *)
(* Authoremail: hwxiATcsDOTbuDOTedu *)

(* ****** ****** *)
//
#define
ATS_PACKNAME
"ATSLIB.libats\
.BUCS320.DivideConquer"
//
(* ****** ****** *)

#staload "./DivideConquer.dats"

(* ****** ****** *)

#staload "libats/ML/SATS/hashtblref.sats"

(* ****** ****** *)
//
extern
fun{}
DivideConquer_memo$solve
  (x0: input): output
//
(* ****** ****** *)
//
extern
fun{}
DivideConquer_memo$table_get
  ((*void*)): hashtbl(input, output)
//
(* ****** ****** *)
//
implement
DivideConquer$solve$memo_get<>
  (x0) = let
//
val
theTable =
DivideConquer_memo$table_get<>()
//
in
//
hashtbl_search<input,output>(theTable, x0)
//
end // end of [DivideConquer$solve$memo_get]

implement
DivideConquer$solve$eval$memo_set<>
  (x0, r0) = let
val
theTable =
DivideConquer_memo$table_get<>()
//
in
//
hashtbl_insert_any<input,output>(theTable, x0, r0)
//
end // end of [DivideConquer$solve$memo_get]
//
(* ****** ****** *)
//
implement
{}(*tmp*)
DivideConquer_memo$solve
  (x0) =
(
  DivideConquer$solve<>(x0)
) (* end of [DivideConquer_memo] *)
//
(* ****** ****** *)

(* end of [DivideConquer_memo.dats] *)
