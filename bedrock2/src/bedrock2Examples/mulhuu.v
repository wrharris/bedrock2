(* Implementation of mulhuu by Andres Erbsen. *)

Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Macros.ident_to_string.
From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Require Import bedrock2.ZnWords.
Require Import Lia ZArith.

Import Syntax BinInt String List.ListNotations.
Import coqutil.Word.Interface coqutil.Word.Properties.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation "x += e" :=
  (cmd.set
     (ident_to_string! x)
     (expr.op bopname.add (ident_to_string! x) e))
    (in custom bedrock_cmd at
          level 0, x ident, e custom bedrock_expr, only parsing).

(* Return the high word of the integer multiplication a * b. *)
Definition secp256k1_umul128 :=
  func! (a, b) ~> (hi, low) {
  (* func! (a, b) ~> (hi, low) { *)
      M = $1 << $32 - $1;
      (* Casts to (uint32_t) in secp are implemented in bedrock2 using
       * word.and. *)
      ll = (a & M) * (b & M);
      lh = (a & M) * (b >> $32);
      hl = (a >> $32) * (b & M);
      hh = (a >> $32) * (b >> $32);
      mid34 = (ll >> $32) + (lh & M) + (hl & M);
      hi = hh + (lh >> $32) + (hl >> $32) + (mid34 >> $32);
      low = (mid34 << $32) + (ll & M)
    }.

Local Instance spec_of_secp256k1 : spec_of "secp256k1_umul128" :=
  fnspec! "secp256k1_umul128" a b ~> hi low,
    { requires t m := True;
      ensures T M :=
        M = m /\ T = t /\
          word.unsigned low + Z.shiftl (word.unsigned hi) 64 =
            (word.unsigned a) * (word.unsigned b)
    }.

Lemma mask_is_mod :
  forall a : BasicC64Semantics.word,
    word.unsigned
      (word.and
         a
         (word.sub (word.slu (word.of_Z 1) (word.of_Z 32)) (word.of_Z 1))) =
      (word.unsigned a) mod (2^32).
Proof.
  intros.
  erewrite <- Z.land_ones; try lia.
  specialize
    (word.unsigned_and_nowrap
       a (word.sub (word.slu (word.of_Z 1) (word.of_Z 32)) (word.of_Z 1)) ).
  Fail ZnWords.
  assert 
    (word.unsigned
      (word.sub
         (word.slu
            (word.of_Z 1 : BasicC64Semantics.word) (word.of_Z 32))
         (word.of_Z 1)) =
       (Z.ones 32)) by trivial.
  Fail ZnWords.
  rewrite H; clear H.
  trivial.
Qed.

Lemma mul32_ub :
  forall a b : BasicC64Semantics.word,
    (word.unsigned a) < 2^32 ->
    (word.unsigned b) < 2^32 ->
    word.unsigned (word.mul a b) < 2^64 - 2^33 + 2.
Proof.
  intros.
  specialize (word.unsigned_range a).
  specialize (word.unsigned_range b).
  intros.
  rewrite word.unsigned_mul.
  (* TODO(harrisw): this may be proved by applying something like *
  `Z.mul_lt_mono_r`. Suspect that this is in some library like
  Coq.ZArith.ZArith, but can't confirm because Coq refs are
  offline. *)
  Fail nia.
  Admitted.

Lemma mul_half_words :
  forall a b : BasicC64Semantics.word,
    word.unsigned a < 2^32 -> word.unsigned b < 2^32 ->
    word.unsigned (word.mul a b) = word.unsigned a * word.unsigned b.
Proof.
  intros.
  Fail ZnWords.
  Admitted.

Lemma secp256k1_umul128_ok : program_logic_goal_for_function! secp256k1_umul128.
Proof.
  repeat straightline.
  (* TODO: clean up with repeated matching *)
  specialize (mask_is_mod a).
  specialize (mask_is_mod b).
  specialize (mask_is_mod ll).
  specialize (mask_is_mod lh).
  specialize (mask_is_mod hl).
  specialize (mul_half_words (word.and a M) (word.and b M)).
  specialize (mul_half_words (word.and a M) (word.sru b (word.of_Z 32))).
  specialize (mul_half_words (word.sru a (word.of_Z 32)) (word.and b M)).
  specialize
    (mul_half_words (word.sru a (word.of_Z 32)) (word.sru b (word.of_Z 32))).
  specialize
    (mul32_ub (word.and a M) (word.sru b (word.of_Z 32))).
  specialize
    (mul32_ub (word.sru a (word.of_Z 32)) (word.and b M)).
  specialize
    (mul32_ub (word.sru a (word.of_Z 32)) (word.sru b (word.of_Z 32))).
  Time ZnWords.
Qed.

(* Return the high word of the integer multiplication a * b. *)
Definition mulhuu :=
  func! (a, b) ~> (hi, low) {
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
      low = (a & M) * (b & M);
      s0 = r0 + (sW << W);
      c2W = s0 < r0;
      hi += c2W
    }.

(* mulhuu's functional spec, as commented above. Memory and trace are
   unchanged. *)
Local Instance spec_of_mulhuu : spec_of "mulhuu" :=
  fnspec! "mulhuu" a b ~> hi low,
    { requires t m := True;
      ensures T M :=
        M = m /\ T = t /\
          2^64 * word.unsigned hi + word.unsigned low =
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

(* Alternate expression of `mult_half_words`? TODO: needs lower bounds
 * on a and b as parameters. *)
Lemma mult_half_words' 
  (m := 2^32)
  (M := m * m) 
  (a b : Z)
  (alow := a mod m) 
  (ahi := a / m)
  (blow := b mod m)
  (bhi := a / m)
  (ll := alow * blow)
  (hl := ahi * blow)
  (lh := alow * bhi)
  (hh := ahi * bhi)
  (tm := (ll / m) + (hl mod m) + lh) :
  a * b =
    ((tm * m mod M) + (ll mod m))
    + M * ((hl / m) + (tm / m) + hh).
Proof.
Admitted.

Lemma ltu_as_carry (a b : BasicC64Semantics.word)
  : word.unsigned ((if word.ltu (word.add a b) a then word.of_Z 1 else word.of_Z 0) : BasicC64Semantics.word) =
      (word.unsigned a + word.unsigned b) /  2 ^ 64.
Proof.
  Admitted.

Lemma mulhuu_ok : program_logic_goal_for_function! mulhuu.
Proof.
  repeat straightline.
  rewrite (mult_half_words' (word.unsigned a) (word.unsigned b)).
  specialize (ltu_as_carry lh hl).
  specialize (ltu_as_carry r0 (word.slu sW W)).
  (* Fails to find witness. *)
  ZnWords.
