(* ****** ****** *)

#include
"share/atspre_staload.hats"

(* ****** ****** *)

local

#staload
"./../DATS/BUCS520-2016-Fall.dats"
(*
implement
streamize_fileref_lineto$bufsz<>() = 1024
*)

in (* in-of-local *)

fun
streamize_stdin_lineto_
  ((*void*)) =
(
streamize_fileref_lineto<>
  (stdin_ref, 3(*sec*))
)

fun
iecho_lineto
  ((*void*)): void = let
//
fun
loop
(
i0: int
,
xs: stream_vt(lineto)
) : void =
(
case+ !xs of
| ~stream_vt_nil() => ()
| ~stream_vt_cons(x0, xs) =>
  (
    case+ x0 of
    | ~LNTOline(l0) =>
      (println!(i0, '\t', l0);
       strptr_free(l0); loop(i0+1, xs))
    | ~LNTOtimeout() =>
      (lazy_vt_free(xs); println!("TIMEOUT!!!"))
  )
)
//
in
  loop(1, streamize_stdin_lineto_())
end // end of [iecho_lineto]

end // end of [local]

(* ****** ****** *)

#staload
"libats/libc/SATS/signal.sats"

(* ****** ****** *)

implement
main0(argc, argv) = () where
{
//
var
sigact: sigaction
val () =
ptr_nullize<sigaction>
  (__assert__() | sigact) where
{
  extern
  prfun
  __assert__ :
    () -> is_nullable(sigaction)
} (* end of [val] *)
//
val () =
sigact.sa_handler :=
sighandler(lam(sgn) => ((*void*)))
//
val () =
assertloc
(sigaction_null(SIGALRM, sigact) = 0)
//
val _(*solved*) = iecho_lineto((*void*))
//
} (* end of [main0] *)

(* ****** ****** *)

(* end of [test_lineto.dats] *)
