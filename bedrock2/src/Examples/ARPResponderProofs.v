From Coq Require Import Strings.String Lists.List ZArith.BinInt.
From bedrock2 Require Import BasicC64Semantics ProgramLogic.

Require Import bedrock2.Examples.ARPResponder.

Import ListNotations.
Local Open Scope string_scope. Local Open Scope list_scope. Local Open Scope Z_scope.
Require Import bedrock2.NotationsInConstr.
From coqutil.Word Require Import Interface.

From bedrock2 Require Import Array Scalars Separation.
From coqutil.Tactics Require Import letexists rdelta.
Local Notation bytes := (array scalar8 (word.of_Z 1)).

Lemma word__if_zero (t:bool) (H : word.unsigned (if t then word.of_Z 1 else word.of_Z 0) = 0) : t = false. Admitted.
Lemma word__if_nonzero (t:bool) (H : word.unsigned (if t then word.of_Z 1 else word.of_Z 0) <> 0) : t = true. Admitted.

Set Printing Width 90.
Ltac seplog_use_array_load1 H i :=
  let iNat := eval cbv in (Z.to_nat i) in
  unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [exact iNat|exact (word.of_Z 0)|Lia.lia|];
  change ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in *.

Local Instance spec_of_arp : spec_of "arp" := fun functions =>
  forall t m packet ethbuf len R,
    (sep (array scalar8 (word.of_Z 1) ethbuf packet) R) m ->
    word.unsigned len = Z.of_nat (length packet) ->
  WeakestPrecondition.call functions "arp" t m [ethbuf; len] (fun T M rets => True).
Goal program_logic_goal_for_function! arp.
  repeat straightline.
  letexists; split; [solve[repeat straightline]|]; split; [|solve[repeat straightline]]; repeat straightline.
  eapply word__if_nonzero in H1.
  rewrite word.unsigned_ltu, word.unsigned_of_Z, Z.mod_small in H1 by admit.
  eapply Z.ltb_lt in H1.
  repeat (letexists || straightline).
  split.
  1: repeat (split || letexists || straightline).
  Ltac tload := 
  lazymatch goal with |- Memory.load Syntax.access_size.one ?m (word.add ?base (word.of_Z ?i)) = Some ?v =>
  lazymatch goal with H: _ m |- _ =>
    let iNat := eval cbv in (Z.to_nat i) in
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); Lia.lia|instantiate (1 := word.of_Z 0) in H];
    eapply load_one_of_sep;
    SeparationLogic.ecancel_assumption
  end end.

  1: {
  lazymatch goal with |- Memory.load Syntax.access_size.one ?m (word.add ?base (word.of_Z ?i)) = Some ?v =>
  lazymatch goal with H: _ m |- _ =>
    let iNat := eval cbv in (Z.to_nat i) in
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); Lia.lia|instantiate (1 := word.of_Z 0) in H];
    eapply load_one_of_sep;
    simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H);
    idtac
  end end.

  SeparationLogic.cancel.
  simple refine (SeparationLogic.cancel_seps_at_indices 1 0 _ _ _ _); cbn[SeparationLogic.firstn SeparationLogic.skipn SeparationLogic.app].
Abort.