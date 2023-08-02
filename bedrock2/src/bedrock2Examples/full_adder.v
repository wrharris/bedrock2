From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Require Import bedrock2.NotationsCustomEntry.
Require Import ZArith.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.ZnWords.
Import Syntax BinInt String List.ListNotations.
Import coqutil.Word.Interface.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition add_with_carry :=
  func! (x, y, carry) ~> (sum, carry_out) {
      x = x + carry;
      carry_out = x < carry;
      sum = x + y;
      carry_out = carry_out + (sum < y)
    }.


Local Instance spec_of_add_with_carry : spec_of "add_with_carry" :=
  fnspec! "add_with_carry" x y carry ~> sum carry_out,
    { (* The required upper bound on `carry` isn't necessary for the
         current `add_with_carry` to support the `ensures` clause, but
         it does formalize an expected condition that future
         implementations should be free to leverage. *)
      requires t m := word.unsigned carry < 2;
      ensures T M :=
        M = m /\ T = t /\
          word.unsigned sum + 2^64 * word.unsigned carry_out =
            word.unsigned x + word.unsigned carry + word.unsigned y
    }.

(* DEPRECATED *)
Lemma add_ltu_as_adder : forall a b : BasicC64Semantics.word,
    word.unsigned a + word.unsigned b =
      2^64 * (if word.ltu (word.add a b) b then 1 else 0) +
          word.unsigned (word.add a b).
Proof.
  intros.
  rewrite word.unsigned_ltu.
  destr (word.unsigned (word.add a b) <? word.unsigned b);
    ZnWords.
Qed.

Lemma ltu_as_carry64 (a b : BasicC64Semantics.word)
  : word.unsigned
      ((if word.ltu (word.add a b) b then word.of_Z 1 else word.of_Z 0) :
        BasicC64Semantics.word) =
      (word.unsigned a + word.unsigned b) /  2 ^ 64.
Proof.
  rewrite word.unsigned_ltu.
  destr (word.unsigned (word.add a b) <? word.unsigned b);
    ZnWords.
Qed.

Lemma full_adder_ok : program_logic_goal_for_function! add_with_carry.
Proof.
  repeat straightline.
  (* TODO(wrharris): automate this using pattern matching? *)
  specialize (ltu_as_carry64 x y).
  specialize (ltu_as_carry64 x'0 carry).
  ZnWords.
Qed.
