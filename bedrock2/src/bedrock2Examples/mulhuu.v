(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Macros.ident_to_string.
From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Require Import bedrock2.ZnWords.

Import Syntax BinInt String List.ListNotations.
Import coqutil.Word.Interface.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation "x += e" := (cmd.set (ident_to_string! x) (expr.op bopname.add (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr, only parsing).

(* Return the high word of the integer multiplication a * b. *)
Definition mulhuu :=
  func! (a, b) ~> r2W {
      W = $4; (* TODO: translate sizeof(uintptr_t)? *)
      M = $1 << W - $1;
      lh = (a & M) * (b >> W);
      hl = (a >> W) * (b & M);
      (* return integer expression
         [r2W + ((((lh + hl) << 32) + r0) >> 64)] *)
      sW = lh + hl;
      r2W = (a >> W) * (b >> W);
      c3W = sW < lh;
      r2W += c3W << W;
      r2W += sW >> W;
      r0 = (a & M) * (b & M);
      s0 = r0 + (sW << W);
      c2W = s0 < r0;
      r2W += c2W
    }.

(* mulhuu's functional spec, as commented above. Memory and trace are
   unchanged. *)
Local Instance spec_of_add_with_carry : spec_of "add_with_carry" :=
  fnspec! "mulhuu" a b ~> r2W,
    { requires t m := True;
      ensures T M :=
        M = m /\ T = t /\
          word.unsigned r2W = (word.unsigned a * word.unsigned b) / 2^64
    }.
