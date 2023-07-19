(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Require Import coqutil.Macros.ident_to_string.

Local Notation "x += e" := (cmd.set (ident_to_string! x) (expr.op bopname.add (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr, only parsing).

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
