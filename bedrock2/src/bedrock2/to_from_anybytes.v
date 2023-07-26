Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Datatypes.ZList. Import ZList.List.ZIndexNotations.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.

Section WithMem.
  Context {width} {BW: Bitwidth width} {word: word width} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition contiguous(P: word -> mem -> Prop)(n: Z): Prop :=
    forall addr, impl1 (P addr) (array (uint 8) n ? addr).

  (* sometimes, we don't need the actual proof, but only want to know whether it's
     contiguous to determine whether a proof step is safe, so we can save the proof effort *)
  Inductive fake_contiguous(P: word -> mem -> Prop): Prop :=
    mk_fake_contiguous.

  Lemma contiguous_to_fake P n: contiguous P n -> fake_contiguous P.
  Proof. intros. constructor. Qed.

  Lemma cast_to_anybytes: forall (P: word -> mem -> Prop) a n m,
      contiguous P n -> P a m -> (array (uint 8) n ? a) m.
  Proof. unfold contiguous, impl1. intros. eauto. Qed.

  (* the direction we care about is anybytes -> P, but it is very likely to
     also imply the converse direction, and probably also easy to prove,
     so we make it an iff1 *)
  Definition fillable{V: Type}(P: V -> word -> mem -> Prop)(n: Z): Prop :=
    forall addr, iff1 (array (uint 8) n ? addr) (ex1 (fun v => P v addr)).

  Lemma fillable_to_contiguous{V: Type} P (v: V) n: fillable P n -> contiguous (P v) n.
  Proof.
    unfold fillable, contiguous. intros. specialize (H addr).
    unfold ex1, impl1 in *.
    intros m Hm.
    eapply proj2 in H.
    eapply H.
    eauto.
  Qed.

  Lemma contiguous_implies_anyval_of_fillable{T: Type}:
    forall (P: word -> mem -> Prop) (F: T -> word -> mem -> Prop) (n: Z) (a: word),
      contiguous P n ->
      fillable F n ->
      impl1 (P a) (anyval F a).
  Proof.
    unfold contiguous, fillable, impl1, iff1, anyval. intros.
    eapply H0. eapply H. assumption.
  Qed.

  Lemma array_uint8_contiguous: forall v n, contiguous (array (uint 8) n v) n.
  Proof. unfold contiguous. intros. unfold anyval. eapply impl1_ex1_r. reflexivity. Qed.

  Lemma anybytes_contiguous: forall n, contiguous (anyval (array (uint 8) n)) n.
  Proof. unfold contiguous. intros. reflexivity. Qed.

  Lemma sepapps_nil_contiguous: contiguous (sepapps nil) 0.
  Proof.
    unfold contiguous, sepapps, anyval, Memory.anybytes, impl1.
    simpl. intros *. intros [? _]. subst.
    exists nil. unfold array.
    eapply sep_emp_l. split; [reflexivity| ].
    simpl. unfold emp. auto.
  Qed.

  Lemma sepapps_cons_contiguous: forall p tail n1 n2,
      contiguous p n1 ->
      contiguous (sepapps tail) n2 ->
      contiguous (sepapps (cons (mk_sized_predicate p n1) tail)) (n1 + n2).
  Proof.
    unfold contiguous. intros.
    rewrite sepapps_cons.
    simpl.
    intros m Hm.
    eapply merge_anyval_array.
    destruct Hm as (m1 & m2 & D & Hm1 & Hm2).
    unfold impl1 in *.
    exists m1, m2. rewrite Z.mul_1_l. eauto.
  Qed.

  Lemma uintptr_contiguous: forall v, contiguous (uintptr v) (Memory.bytes_per_word width).
  Proof.
    unfold contiguous, impl1, uintptr. intros.
    eapply Scalars.scalar_to_anybytes in H.
    eapply anybytes_from_alt.
    1: destruct width_cases as [E|E]; rewrite E; cbv; discriminate.
    assumption.
  Qed.

  Lemma uint_contiguous: forall (nbits v: Z),
      contiguous (uint nbits v) (nbits_to_nbytes nbits).
  Proof.
    unfold contiguous, impl1. intros nbits v addr m H. eapply anybytes_from_alt.
    { apply nbits_to_nbytes_nonneg. }
    unfold uint in H. eapply sep_emp_l in H. apply proj2 in H.
    unfold Scalars.littleendian, ptsto_bytes.ptsto_bytes in H.
    rewrite HList.tuple.to_list_of_list in H.
    eapply Array.array_1_to_anybytes in H.
    rewrite LittleEndianList.length_le_split in H.
    rewrite Z2Nat.id in H by apply nbits_to_nbytes_nonneg.
    exact H.
  Qed.

  Lemma uintptr_fillable: fillable uintptr (Memory.bytes_per_word width).
  Proof.
    unfold fillable, iff1, uintptr. intros a m. split; intro Hm.
    - eapply Scalars.anybytes_to_scalar. eapply anybytes_to_alt. assumption.
    - destruct Hm as [bs Hm]. eapply Scalars.scalar_to_anybytes in Hm.
      eapply anybytes_from_alt. 2: exact Hm.
      destruct width_cases as [E|E]; rewrite E; cbv; discriminate.
  Qed.

  (* TODO make non-fake *)
  Lemma array_fake_contiguous: forall T (elem: T -> word -> mem -> Prop)
                                      {sz: PredicateSize elem} n vs,
      (forall v, fake_contiguous (elem v)) ->
      fake_contiguous (array elem n vs).
  Proof. intros. constructor. Qed.

  Lemma sepapps_nil_fake_contiguous: fake_contiguous (sepapps nil).
  Proof. constructor. Qed.

  Lemma sepapps_cons_fake_contiguous: forall p sz l,
      fake_contiguous p ->
      fake_contiguous (sepapps l) ->
      fake_contiguous (sepapps (cons (mk_sized_predicate p sz) l)).
  Proof. intros. constructor. Qed.

  Lemma anyval_fake_contiguous{T: Type}: forall p: T -> word -> mem -> Prop,
      (forall v, fake_contiguous (p v)) ->
      fake_contiguous (anyval p).
  Proof. intros. constructor. Qed.
End WithMem.

Section WithMem32.
  Context {word: word 32} {BW: Bitwidth 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma uintptr32_contiguous: forall v, contiguous (uintptr v) 4.
  Proof. eapply (uintptr_contiguous (width := 32)). Qed.

  Lemma uintptr32_fillable: fillable uintptr 4.
  Proof. eapply (uintptr_fillable (width := 32)). Qed.
End WithMem32.

Section WithMem64.
  Context {word: word 64} {BW: Bitwidth 64} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma uintptr64_contiguous: forall v, contiguous (uintptr v) 8.
  Proof. eapply (uintptr_contiguous (width := 64)). Qed.

  Lemma uintptr64_fillable: fillable uintptr 8.
  Proof. eapply (uintptr_fillable (width := 64)). Qed.
End WithMem64.

Create HintDb contiguous.
#[export] Hint Resolve
  sepapps_cons_contiguous
  sepapps_nil_contiguous
  uintptr32_contiguous
  uintptr64_contiguous
  uint_contiguous
  array_uint8_contiguous
  anybytes_contiguous
  contiguous_to_fake
  array_fake_contiguous
  sepapps_nil_fake_contiguous
  sepapps_cons_fake_contiguous
  anyval_fake_contiguous
: contiguous.

Create HintDb fillable.
#[export] Hint Resolve
  uintptr32_fillable
  uintptr64_fillable
: fillable.

#[export] Hint Extern 20 (contiguous ?p ?n) =>
  let h := head p in
  (* seemingly superfluous match strips cast added by unfold *)
  lazymatch constr:(ltac:(unfold h; typeclasses eauto) : contiguous p n) with
  | ?res => exact res
  end
: contiguous.

Ltac is_contiguous P :=
  let __ := constr:(ltac:(solve [typeclasses eauto with contiguous]
                          || fail "not contiguous")
                     : contiguous P _) in idtac.

Ltac is_fake_contiguous P :=
  let __ := constr:(ltac:(solve [typeclasses eauto with contiguous]
                          || fail "not fake_contiguous")
                     : fake_contiguous P) in idtac.

Section TestsWithMem64.
  Context {word: word 64} {BW: Bitwidth 64} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Goal forall (foo: word -> mem -> Prop) (v: word), True.
    intros.
    is_contiguous (uintptr v).
    Fail is_contiguous foo.
    Fail is_fake_contiguous foo.
    assert (fake_contiguous foo) as A.
    2: {
      Fail is_contiguous foo.
      is_fake_contiguous foo.
      clear A.
      assert (contiguous foo 42) as A.
      2: {
        is_contiguous foo.
        is_fake_contiguous foo.
  Abort.
End TestsWithMem64.
