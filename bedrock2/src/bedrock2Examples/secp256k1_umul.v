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
  rewrite <- Z.land_ones by lia.
  specialize
    (word.unsigned_and_nowrap
       a (word.sub (word.slu (word.of_Z 1) (word.of_Z 32)) (word.of_Z 1)) ).
  trivial.
Qed.

Lemma wrap_mul32_is_mul32 :
  forall a b,
    0 <= a < 2^32 ->
    0 <= b < 2^32 -> word.wrap (a * b) = (a * b).
Proof.
  intros.
  apply Zmod_small.
  nia.
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
  rewrite word.unsigned_mul.
  rewrite wrap_mul32_is_mul32 by ZnWords.
  specialize (Zmult_le_compat_r (word.unsigned a) (2^32 - 1) (word.unsigned b)).
  specialize (Zmult_le_compat_l (word.unsigned b) (2^32 - 1) (2^32 - 1)).
  ZnWords.
Qed.

Lemma mul_half_words :
  forall a b : BasicC64Semantics.word,
    word.unsigned a < 2^32 ->
    word.unsigned b < 2^32 ->
    word.unsigned (word.mul a b) = word.unsigned a * word.unsigned b.
Proof.
  intros.
  rewrite word.unsigned_mul.
  rewrite wrap_mul32_is_mul32; ZnWords.
Qed.

Lemma secp256k1_umul128_ok : program_logic_goal_for_function! secp256k1_umul128.
Proof.
  repeat straightline.
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

