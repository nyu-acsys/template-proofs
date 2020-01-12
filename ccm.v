Require Import Coq.Logic.Decidable.

From iris Require Export base.
Set Default Proof Using "Type".

From stdpp Require Export decidable.
From stdpp Require Export gmap.
From stdpp Require Import mapset.
From stdpp Require Import finite.

(** * Commutative Cancelative Monoids (CCMs) *)

Class Cancelative {A} (R : relation A) (f : A → A → A) : Prop :=
  cancel x y z : R (f x y) (f x z) → R y z.

Class PartialInv {A} (R: relation A) (f : A → A → A) (g : A → A → A) : Prop :=
  pinv x y : R (g (f x y) y) x.

Class CCM :=
  {
    ccm_car :> Type;
    ccm_eq : EqDecision ccm_car;
    ccm_unit : ccm_car;
    ccm_op: ccm_car → ccm_car → ccm_car;
    ccm_opinv: ccm_car → ccm_car → ccm_car;
    ccm_assoc : Assoc (=) ccm_op;
    ccm_comm : Comm (=) ccm_op;
    ccm_left_id : LeftId (=) ccm_unit ccm_op;
    ccm_cancel : Cancelative (=) ccm_op;
    ccm_pinv : PartialInv (=) ccm_op ccm_opinv;
  }.

Lemma ccm_right_id {M: CCM} : RightId (=) ccm_unit ccm_op.
Proof. intros x. etrans; [apply ccm_comm|apply ccm_left_id]. Qed.

Lemma ccm_pinv_unit {M: CCM} x : ccm_opinv x ccm_unit = x.
Proof.
  rewrite <- (ccm_right_id x) at 1.
  apply ccm_pinv.
Qed.

(** * The CCM of natural numbers with addition *)

Instance nat_eq: EqDecision nat.
Proof.
  unfold EqDecision.
  intros.
  unfold Decision.
  decide equality.
Qed.

Definition nat_op (x: nat) (y: nat): nat := x + y.

Definition nat_opinv (x: nat) (y: nat) := (x - y)%nat.

Definition nat_unit := 0%nat.

Instance plus_assoc: Assoc (=) nat_op.
Proof.
  unfold Assoc.
  intros.
  unfold nat_op.
  lia.
Qed.

Instance plus_comm: Comm (=) nat_op.
Proof.
  unfold Comm.
  intros.
  unfold nat_op.
  lia.
Qed.

Instance plus_leftid: LeftId (=) nat_unit nat_op.
Proof.
  unfold LeftId.
  intros.
  unfold nat_op.
  unfold nat_unit.
  lia.
Qed.

Instance plus_cancel: Cancelative (=) nat_op.
Proof.
  unfold Cancelative.
  intros.
  unfold nat_op in H.
  lia.
Qed.

Instance plus_pinv: PartialInv (=) nat_op nat_opinv.
Proof.
  unfold PartialInv.
  intros.
  unfold nat_op, nat_opinv.
  lia.
Qed.

Instance NatCCM : CCM := { ccm_car := nat }.

(** * Lift any CCM A to functions K → option A for any countable K *)

Section lifting.
  Context `{Countable K} (C : CCM).

  Local Definition A := @ccm_car C.
  
  Local Notation "x + y" := (@ccm_op C x y).
  Local Notation "x - y" := (@ccm_opinv C x y).

  Local Notation "0" := (@ccm_unit C).
  
  Definition nzmap_wf : gmap K A → Prop :=
    map_Forall (λ _ x, ¬ (x = 0)).
  
  Instance nzmap_wf_decision m : Decision (nzmap_wf m).
  Proof.
    apply map_Forall_dec.
    intros.
    apply not_dec.
    apply ccm_eq.
  Defined.
  
  Record nzmap :=
    NZMap {
        nzmap_car : gmap K A;
        nzmap_prf : bool_decide (nzmap_wf nzmap_car)
      }.
  
  Arguments NZMap _ _ : assert.
  Arguments nzmap_car _ : assert.

  Instance c_eq: EqDecision A.
  Proof.
    apply ccm_eq.
  Qed.
  
  Lemma nzmap_eq m1 m2 :
    m1 = m2 ↔ nzmap_car m1 = nzmap_car m2.
  Proof.
    split; [by intros ->|intros]. destruct m1, m2; simplify_eq/=.
    f_equal. apply proof_irrel.
  Qed.
  Instance nzmap_eq_eq : EqDecision nzmap.
  Proof.
    refine (λ m1 m2, cast_if (decide (nzmap_car m1 = nzmap_car m2)));
      abstract (by rewrite nzmap_eq).
  Defined.

  Instance op_zero_dec `(x1 : A, x2 : A) : Decision (x1 + x2 = 0).
  Proof.
    apply ccm_eq.
  Defined.
  
  Definition merge_op (o1: option A) (o2: option A) :=
    match o1, o2 with
    | Some x1, Some x2 =>
      if decide (x1 + x2 = 0)
      then None 
      else Some (x1 + x2)
    | None, Some x2 => Some x2
    | Some x1, None => Some x1
    | None, None => None
    end.

  Lemma nzmap_lookup_wf m i : nzmap_wf m → m !! i <> Some 0.
  Proof.
    intros.
    unfold nzmap_wf, map_Forall in H0.
    firstorder.
  Qed.
  
  Lemma lift_op_wf m1 m2 : nzmap_wf m1 → nzmap_wf m2 → nzmap_wf (merge merge_op m1 m2).
  Proof.
    intros.
    unfold nzmap_wf.
    unfold map_Forall.
    intros.
    assert ((m1 !! i) <> Some 0) as Hm1i.
    apply nzmap_lookup_wf. trivial.
    assert ((m2 !! i) <> Some 0) as Hm2i.
    apply nzmap_lookup_wf. trivial.
    rewrite lookup_merge in H2.
    unfold merge_op in H2.
    repeat destruct (_ !! _);
    try destruct (decide _);
    first [discriminate |
           inversion H2; trivial; congruence ].
  Qed.
  
  Definition lift_op (m1: nzmap) (m2: nzmap) :=
    let (m1, Hm1) := m1 in
    let (m2, Hm2) := m2 in
    NZMap (merge merge_op m1 m2) (bool_decide_pack _ (lift_op_wf _ _
    (bool_decide_unpack _ Hm1) (bool_decide_unpack _ Hm2))).


  Instance opinv_zero_dec `(x1 : A, x2 : A) : Decision (x1 - x2 = 0).
  Proof.
    apply ccm_eq.
  Defined.

  Definition merge_opinv (o1: option A) (o2: option A) :=
    match o1, o2 with
    | Some x1, Some x2 =>
      if decide (x1 - x2 = 0)
      then None 
      else Some (x1 - x2)
    | None, Some x2 =>
      if decide (0 - x2 = 0)
      then None
      else Some (0 - x2)
    | Some x1, None => Some x1
    | None, None => None
    end.

  Instance diag_opinv : DiagNone merge_opinv := _.
  Proof.
    unfold DiagNone.
    auto.
  Qed.
  
  Lemma lift_opinv_wf m1 m2 : nzmap_wf m1 → nzmap_wf m2 → nzmap_wf (merge merge_opinv m1 m2).
  Proof.
    intros.
    unfold nzmap_wf.
    unfold map_Forall.
    intros.
    assert ((m1 !! i) <> Some 0) as Hm1i.
    apply nzmap_lookup_wf. trivial.
    assert ((m2 !! i) <> Some 0) as Hm2i.
    apply nzmap_lookup_wf. trivial.
    rewrite lookup_merge in H2.
    unfold merge_opinv in H2.
    repeat destruct (_ !! _);
    try destruct (decide _);
    first [discriminate |
           inversion H2; trivial; congruence ].
  Qed.

  Definition lift_opinv (m1: nzmap) (m2: nzmap) :=
    let (m1, Hm1) := m1 in
    let (m2, Hm2) := m2 in
    NZMap (merge merge_opinv m1 m2) (bool_decide_pack _ (lift_opinv_wf _ _
    (bool_decide_unpack _ Hm1) (bool_decide_unpack _ Hm2))).

  Implicit Types m : nzmap.

  Instance lift_comm: Comm (=) lift_op.
  Proof.
    unfold Comm, lift_op.
    intros.
    destruct x as [m1].
    destruct y as [m2].
    apply nzmap_eq.
    simpl.
    apply map_eq.
    intros.
    repeat rewrite lookup_merge.
    repeat destruct (_ !! i);
    simpl;
    repeat destruct (decide _);
    first [try rewrite ccm_comm; reflexivity |
           try rewrite ccm_comm in n; contradiction].
  Qed.

  Instance lift_assoc: Assoc (=) lift_op.
  Proof.
    unfold Assoc, lift_op.
    intros.
    destruct x as [m1].
    destruct y as [m2].
    destruct z as [m3].
    apply nzmap_eq.
    simpl.
    apply map_eq.
    intros.
    assert ((m1 !! i) <> Some 0) as Hm1i.
    apply nzmap_lookup_wf.
    unfold bool_decide in nzmap_prf0.
    destruct (nzmap_wf_decision m1).
    apply n.
    contradiction.
    assert ((m3 !! i) <> Some 0) as Hm3i.
    apply nzmap_lookup_wf.
    unfold bool_decide in nzmap_prf2.
    destruct (nzmap_wf_decision m3).
    apply n.
    contradiction.
    repeat rewrite lookup_merge.
    repeat destruct (_ !! i);
    simpl;
    repeat destruct (decide _);
    simpl;
    repeat destruct (decide _);
    f_equal.
    - rewrite ccm_comm in e0.
      assert (a1 + a = a1 + a0).
      rewrite e.
      apply e0.
      generalize H0.
      apply ccm_cancel.
    - rewrite <- ccm_assoc in e0.
      rewrite e in e0.
      rewrite ccm_right_id in e0.
      assert (a <> 0).
      firstorder.
      contradiction.
    - rewrite <- ccm_assoc.
      rewrite e.
        by rewrite ccm_right_id.
    - rewrite ccm_assoc in e.
      rewrite e0 in e.
      rewrite ccm_left_id in e.
      assert (a0 <> 0).
      firstorder.
      contradiction.
    - rewrite ccm_assoc in e.
      contradiction.
    - rewrite ccm_assoc.
      rewrite e.
      apply ccm_left_id.
    - rewrite ccm_assoc in n0.
      contradiction.
    - apply ccm_assoc.
  Qed.

  Definition nzmap_unit := NZMap ∅ I.
  
  Instance nzmap_empty : Empty nzmap := nzmap_unit.
  Global Opaque nzmap_empty.

  
  Instance lift_leftid: LeftId (=) nzmap_unit lift_op.
  Proof.
    unfold LeftId, lift_op.
    intros.
    destruct x as [m2].
    unfold nzmap_unit.
    apply nzmap_eq.
    simpl.
    apply map_eq.
    intros.
    simpl.
    repeat rewrite lookup_merge.
    rewrite lookup_empty.
    repeat destruct (_ !! i);
    unfold merge_op;
      simpl;
      reflexivity.
  Qed.

  Instance lift_cancel: Cancelative (=) lift_op.
  Proof.
    unfold Cancelative, lift_op.
    intros.
    destruct x as [m1].
    destruct y as [m2].
    destruct z as [m3].
    apply nzmap_eq in H0.
    apply nzmap_eq.
    simpl in H0.
    simpl.
    apply map_eq.
    intros.
    assert ((m1 !! i) <> Some 0) as Hm1i.
    apply nzmap_lookup_wf.
    unfold bool_decide in nzmap_prf0.
    destruct (nzmap_wf_decision m1).
    apply n.
    contradiction.
    assert ((m2 !! i) <> Some 0) as Hm2i.
    apply nzmap_lookup_wf.
    unfold bool_decide in nzmap_prf1.
    destruct (nzmap_wf_decision m2).
    apply n.
    contradiction.
    assert ((m3 !! i) <> Some 0) as Hm3i.
    apply nzmap_lookup_wf.
    unfold bool_decide in nzmap_prf2.
    destruct (nzmap_wf_decision m3).
    apply n.
    contradiction.
    
    assert (merge merge_op m1 m2 !! i = merge merge_op m1 m3 !! i).
    rewrite H0.
    reflexivity.
    repeat rewrite lookup_merge in H1.
    repeat unfold merge_op in H1.
    
    unfold bool_decide in nzmap_prf0.
    destruct (m1 !! i);
    destruct (m2 !! i);
    destruct (m3 !! i);
    repeat destruct (decide _);
    simpl;
    f_equal;
    first [inversion H1 | 
           assert (a + a0 = a + a1);
           firstorder;
           generalize H2;
           apply ccm_cancel].
    assert (a + a0 = a + a1).
    firstorder.
    generalize H2.
    apply ccm_cancel.
    generalize H3.
    apply ccm_cancel.
    assert (a + 0 = a).
    apply ccm_right_id.
    assert (a + a0 = a + 0).
    firstorder.
    assert (a0 = 0).
    generalize H4.
    apply ccm_cancel.
    assert (a0 <> 0).
    firstorder.
    contradiction.
    - assert (a0 <> 0).
      firstorder.
      assert (a + 0 = a).
      apply ccm_right_id.
      assert (a + a0 = a + 0).
      firstorder.
      assert (a0 = 0).
      generalize H5.
      apply ccm_cancel.
      contradiction.    
    - reflexivity.
  Qed.

  Instance lift_pinv: PartialInv (=) lift_op lift_opinv.
  Proof.
    unfold PartialInv, lift_op, lift_opinv.
    intros.
    destruct x as [m1].
    destruct y as [m2].
    apply nzmap_eq.
    simpl.
    apply map_eq.
    intros.
    assert ((m1 !! i) <> Some 0) as Hm1i.
    apply nzmap_lookup_wf.
    unfold bool_decide in nzmap_prf0.
    destruct (nzmap_wf_decision m1).
    apply n.
    contradiction.
    repeat rewrite lookup_merge.
    unfold merge_opinv, merge_op.
    repeat destruct (_ !! i).
    repeat destruct (decide _).
    - rewrite <- e in e0 at 1.
      rewrite ccm_pinv in e0.
      assert (a <> 0).
      firstorder.
      contradiction.
    - assert (a + a0 - a0 = a).
      apply ccm_pinv.
      rewrite e in H0.
        by rewrite H0.
    - rewrite ccm_pinv in e.
      assert (a <> 0).
      firstorder.
      contradiction.
    - by rewrite ccm_pinv.
    - reflexivity.
    - destruct (decide _).
      reflexivity.
      assert (0 + a = a) by apply ccm_left_id.
      rewrite <- H0 in n at 1.
      rewrite ccm_pinv in n.
      contradiction.
    - reflexivity.
  Qed.

  Program Instance lift_ccm : CCM :=
    {
      ccm_car := nzmap;
      ccm_op := lift_op;
      ccm_opinv := lift_opinv;
      ccm_unit := nzmap_unit;
    }.
  
                                
End lifting.