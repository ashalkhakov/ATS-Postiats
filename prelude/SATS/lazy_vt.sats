(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2011-2012 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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
** $PATSHOME/prelude/SATS/CODEGEN/lazy_vt.atxt
** Time of generation: Mon Sep 30 01:01:33 2013
*)

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = vt@ype

(* ****** ****** *)
//
// HX: [lazy_vt(VT)] :
// suspended computation of viewtype VT
//
absvtype lazy_vt0ype_vtype (vt@ype+) = ptr
//
vtypedef lazy_vt (a: vt0p)= lazy_vt0ype_vtype (a)
//
(* ****** ****** *)
//
fun
lazy_vt_free{a:vt0p}
  (lazyval: lazy_vt (a)):<!wrt> void = "mac#atspre_lazy_vt_free"
overload ~ with lazy_vt_free
//
(* ****** ****** *)
//
// HX: lazy linear streams
//
datavtype
stream_vt_con (a:vt@ype+) =
  | stream_vt_nil of ((*void*)) | stream_vt_cons of (a, stream_vt(a))
where stream_vt (a:vt@ype) = lazy_vt (stream_vt_con(a))
//
(* ****** ****** *)

fun{a:vt0p}
stream2list_vt
  (xs: stream_vt (INV(a))): List0_vt (a)
// end of [stream2list_vt]

(* ****** ****** *)

fun{a:t0p}
stream_vt_free (xs: stream_vt a):<!wrt> void

(* ****** ****** *)

fun{
a:vt0p}{env:vt0p
} stream_vt_foreach$fwork
  (x: &a >> a?!, env: &env): void // lin-cleared
fun{a:vt0p}
stream_vt_foreach (xs: stream_vt (INV(a))): void
fun{
a:vt0p}{env:vt0p
} stream_vt_foreach_env (xs: stream_vt (a), &env): void

(* ****** ****** *)
//
fun{a:vt0p}
stream_vt_filter$pred (x: &a):<> bool
//
fun{a:t0p}
stream_vt_filter (xs: stream_vt (INV(a))): stream_vt (a)
//
fun{a:t0p}
stream_vt_filter_fun (
  xs: stream_vt (INV(a)), pred: (&a) -<fun> bool
) : stream_vt (a) // end of [stream_vt_filter_fun]
fun{a:t0p}
stream_vt_filter_cloptr (
  xs: stream_vt (INV(a)), pred: (&a) -<cloptr> bool
) : stream_vt (a) // end of [stream_vt_filter_cloptr]
//
fun{a:vt0p}
stream_vt_filterlin$clear (x: &a >> a?):<!wrt> void
fun{a:vt0p}
stream_vt_filterlin (xs: stream_vt (INV(a))): stream_vt (a)
//
(* ****** ****** *)
//
fun{
a:vt0p}{b:vt0p
} stream_vt_map$fopr (x: &a >> a?!): b // lin-cleared
fun{
a:vt0p}{b:vt0p
} stream_vt_map (xs: stream_vt (INV(a))): stream_vt (b)
//
fun{
a:vt0p}{b:vt0p
} stream_vt_map_fun
  (xs: stream_vt (INV(a)), f: (&a >> a?!) -<fun> b): stream_vt (b)
fun{
a:vt0p}{b:vt0p
} stream_vt_map_cloptr
  (xs: stream_vt (INV(a)), f: (&a >> a?!) -<cloptr> b): stream_vt (b)
//
(* ****** ****** *)
//
fun{
a1,a2:vt0p}{b:vt0p
} stream_vt_map2$fopr
  (x1: &a1 >> a1?!, x2: &a2 >> a2?!): b
fun{
a1,a2:vt0p}{b:vt0p
} stream_vt_map2 (
  xs1: stream_vt (INV(a1))
, xs2: stream_vt (INV(a2))
) : stream_vt (b) // end of [stream_vt_map2]
//
fun{
a1,a2:vt0p}{b:vt0p
} stream_vt_map2_fun (
  xs1: stream_vt (INV(a1))
, xs2: stream_vt (INV(a2))
, f: (&a1 >> a1?!, &a2 >> a2?!) -<fun> b
) : stream_vt (b) // end of [stream_vt_map2_fun]
fun{
a1,a2:vt0p}{b:vt0p
} stream_vt_map2_cloptr (
  xs1: stream_vt (INV(a1))
, xs2: stream_vt (INV(a2))
, f: (&a1 >> a1?!, &a2 >> a2?!) -<cloptr> b
) : stream_vt (b) // end of [stream_vt_map2_cloptr]
//
(* ****** ****** *)

(* end of [lazy_vt.sats] *)
