(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Macros.ident_to_string.
From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Require Import bedrock2.ZnWords.
Require Import Lia ZArith.

Import Syntax BinInt String List.ListNotations.
Import coqutil.Word.Interface.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation "x += e" := (cmd.set (ident_to_string! x) (expr.op bopname.add (ident_to_string! x) e)) (in custom bedrock_cmd at level 0, x ident, e custom bedrock_expr, only parsing).

(* Return the high word of the integer multiplication a * b. *)
Definition mulhuu :=
  func! (a, b) ~> (r2W, r0) {
      W = $32;
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
Local Instance spec_of_mulhuu : spec_of "mulhuu" :=
  fnspec! "mulhuu" a b ~> r2W r0,
    { requires t m := True;
      ensures T M :=
        M = m /\ T = t /\
          2^64 * word.unsigned r2W + word.unsigned r0 =
            (word.unsigned a * word.unsigned b)
    }.

Ltac cleardisj :=
  repeat match goal with
  | H : _ -> _ |- _ => clear H
  | H : _ \/ _ |- _ => clear H
  end.
Ltac cleanby tac :=
  repeat lazymatch goal with
  | H : ?A -> ?B |- _ =>
      specialize (H ltac:(tac))
      || (assert (not A) as _ by (clear H; tac); clear H)
      || revert H
  | H : ?B |- _ =>
      (assert B as _ by (clear H; tac); clear H)
      || revert H
  end; intros; subst.
Ltac divby tac :=
  repeat lazymatch goal with
    H : 0 <= ?m * ?q + _ < ?m*?m |- _ =>
        try assert (0 <= q < m) by tac; revert H
  end; intros.

(* a * b can be decomposed into sums of products of low and high-order
 * bits of a and b. *)
Lemma mult_half_words :
  forall
    m M (Hm : 1 < m < M) (HM : M = m*m)
    (* (HH : m = 2^32) *)
    a (Ha : 0 <= a < M)
    b (Hb : 0 <= b < M)
    ll (Hll : ll = (a mod m) * (b mod m))
    hl (Hhl : hl = (a/m) * (b mod m))
    lh (Hlh : lh = (a mod m) * (b/m))
    hh (Hll : hh = (a/m) * (b/m))
    tm (Htm : tm = (ll/m) + (hl mod m) + lh)
    rh (Hrh : rh = (hl/m) + (tm/m) + hh)
    rl (Hrl : rl = (tm * m mod M) + (ll mod m)),
    rh = a * b / M /\
    rl = a * b mod M.
Proof.
  intros.
  subst M.
  rewrite Z.mul_mod_distr_r in Hrl by (cleardisj; lia).
  (* needed for last nia without HH *)
  Time Z.div_mod_to_equations.
  Time cleanby ltac:(cleardisj; lia).
  Fail progress cleanby ltac:(cleardisj; nia).
  Time progress divby ltac:(cleardisj; lia).
  Time progress divby ltac:(cleardisj; nia).
  (* Time Fail nia. (* 9s *) *)
  match goal with |- ?A /\ _ => assert A; try split; trivial end.
  (* TODO: these fail with "Expected a single focused goal but 2..."
  using Coq 8.17.0. *)
  { nia. }
  { nia. }
Qed.

(* Wrapper for `mult_half_words` *)
(* Lemma mult_half_words' *)

Lemma mulhuu_ok : program_logic_goal_for_function! mulhuu.
Proof.
  repeat straightline.
  Admitted.
