Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Require Import bedrock2.ZnWords.
From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Import coqutil.Word.Interface.
Require Import coqutil.Tactics.Tactics.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition full_sub :=
  func! (x, y, borrow) ~> (diff, out_borrow) {
      diff = x - y - borrow;
      out_borrow = (x < y) | (x == y) & borrow
    }.

Local Instance spec_of_full_sub : spec_of "full_sub" :=
  fnspec! "full_sub" x y borrow ~> diff out_borrow,
    { requires t m := word.unsigned borrow < 2;
      ensures T M :=
        M = m /\ T = t /\
          word.unsigned diff + 2^64 * word.unsigned out_borrow =
            word.unsigned x - word.unsigned y - word.unsigned borrow
    }.

Require Import ZArith.

Lemma full_sub_ok : program_logic_goal_for_function! full_sub.
Proof.
  (* TODO(harrisw): complete *)
  Admitted.
