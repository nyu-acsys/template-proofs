Require Import Coq.Logic.Decidable.

From iris Require Export base.
(*Set Default Proof Using "Type".*)

From stdpp Require Export decidable.
From stdpp Require Export gmap.
From stdpp Require Import mapset.
From stdpp Require Import finite.

(** * Commutative Cancelative Monoids (CCMs) *)

Delimit Scope ccm_scope with CCM.

Class Cancelative {A} (R : relation A) (f : A → A → A) : Prop :=
  cancel x y z : R (f x y) (f x z) → R y z.

Class PartialInv {A} (R: relation A) (f : A → A → A) (g : A → A → A) : Prop :=
  pinv x y : R (g (f x y) y) x.

Class CcmOp (A : Type) := ccmop : A → A → A.
Hint Mode CcmOp ! : typeclass_instances.
Instance: Params (@ccmop) 2 := {}.
Infix "+" := ccmop (at level 50, left associativity) : ccm_scope.
Notation "(+)" := ccmop (only parsing) : ccm_scope.

Class CcmOpInv (A : Type) := ccmop_inv : A → A → A.
Hint Mode CcmOpInv ! : typeclass_instances.
Instance: Params (@ccmop_inv) 2 := {}.
Infix "-" := ccmop_inv (at level 50, left associativity) : ccm_scope.
Notation "(-)" := ccmop_inv (only parsing) : ccm_scope.

Class CcmUnit (A : Type) := ccmunit : A.
Arguments ccmunit {_ _}.
Notation "0" := ccmunit : ccm_scope.

Open Scope ccm_scope.

Class CCM (M: Type) :=
  {
    ccm_eq : EqDecision M;
    ccm_unit : CcmUnit M; (* 0 *)
    ccm_op: CcmOp M; (* (+) *)
    ccm_opinv: CcmOpInv M; (* (-) *)
    ccm_assoc : Assoc (=) (+);
    ccm_comm : Comm (=) (+);
    ccm_left_id : LeftId (=) 0 (+);
    ccm_cancel : Cancelative (=) (+);
    ccm_pinv : PartialInv (=) (+) (-);
  }.

Arguments ccm_op : simpl never.
Arguments ccm_opinv : simpl never.
(*Arguments ccm_unit : simpl never.*)
Hint Extern 0 (CcmOp _) => eapply (@ccm_op _) : typeclass_instances.
Hint Extern 0 (CcmOpInv _) => eapply (@ccm_opinv _) : typeclass_instances.
Hint Extern 0 (CcmUnit _) => eapply (@ccm_unit _) : typeclass_instances.

Lemma ccm_right_id `{CCM M} : RightId (=) 0 (+).
Proof. intros x. etrans; [apply ccm_comm|apply ccm_left_id]. Qed.

Lemma ccm_pinv_unit `{CCM M} (x: M) : x - 0 = x.
Proof.
  rewrite <- (ccm_right_id x) at 1.
  apply ccm_pinv.
Qed.

Close Scope ccm_scope.

(** * The CCM of natural numbers with addition *)

Instance nat_eq: EqDecision nat.
Proof.
  unfold EqDecision.
  intros.
  unfold Decision.
  decide equality.
Qed.

Instance nat_op : CcmOp nat := plus.

Instance nat_opinv : CcmOpInv nat := λ x y, (x - y)%nat.

Instance nat_unit : CcmUnit nat := 0.

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

Instance plus_leftid: LeftId (=) 0 nat_op.
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

Instance nat_ccm : CCM nat := { }.

(** * Products of CCMs are CCMs *)

Section product.
  Context A1 A2 `{CCM A1} `{CCM A2}.

  Open Scope ccm_scope.
    
  Instance c1_eq: EqDecision A1.
  Proof.
    apply ccm_eq.
  Defined.

  Instance c2_eq: EqDecision A2.
  Proof.
    apply ccm_eq.
  Defined.

  Instance prod_eq: EqDecision (A1 * A2).
  Proof.
    apply prod_eq_dec.
  Defined.

  Instance prod_op : CcmOp (A1 * A2) := λ x y, (x.1 + y.1, x.2 + y.2).

  Instance prod_op_inv : CcmOpInv (A1 * A2) := λ x y, (x.1 - y.1, x.2 - y.2).

  Instance prod_unit: CcmUnit (A1 * A2) := (0, 0).

  Instance prod_comm: Comm (=) prod_op.
  Proof.
    unfold Comm, prod_op.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    f_equal.
    all: apply ccm_comm.
  Defined.

  Instance prod_assoc: Assoc (=) prod_op.
  Proof.
    unfold Assoc, prod_op.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    destruct z as [z1 z2].
    f_equal.
    all: apply ccm_assoc.
  Defined.

  Instance prod_leftid: LeftId (=) 0 prod_op.
  Proof.
    unfold LeftId, prod_op, prod_unit.
    intros.
    destruct x as [x1 x2].
    f_equal.
    all: apply ccm_left_id.
  Defined.
  
  Instance prod_cancel: Cancelative (=) prod_op.
  Proof.
    unfold Cancelative, prod_op.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    destruct z as [z1 z2].
    inversion H1.
    f_equal.
    - generalize H3.
      apply ccm_cancel.
    - generalize H4.
      apply ccm_cancel.    
  Defined.
  
  Instance prod_pinv: PartialInv (=) prod_op prod_op_inv.
  Proof.
    unfold PartialInv, prod_op, prod_op_inv.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    f_equal.
    all: simpl; apply ccm_pinv.
  Defined.

  Instance prod_ccm : CCM (A1 * A2) := { }.

End product.

(** * Lifting any CCM A to functions f: K → A yields a CCM. Here, we assume that f k ≠ 0 for finitely many k. Moreover, K must be countable. *)

Section lifting.
  Context K `{Countable K} A `{CCM A}.

  Open Scope ccm_scope.

  (* To obtain unique representations, we represent functions f: K → A
   * as g: gmap K A where f k = 0 ↔ g !! k = None *)

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
  Defined.
  
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

  Global Instance nzmap_lookup : Lookup K A nzmap := λ i m,
  let (m, _) := m in m !! i.

  Global Instance nzmap_dom : Dom nzmap (gset K) :=
    λ m, dom (gset K) (nzmap_car m).

  Lemma nzmap_is_wf m : nzmap_wf (nzmap_car m).
  Proof.
    destruct m.
    simpl.
    unfold bool_decide, nzmap_wf_decision in nzmap_prf0.
    unfold nzmap_wf.
    destruct map_Forall_dec.
    trivial.
    contradiction.
  Qed.    
  
  (** TODO: The following lemma should really not be needed. *)
  Lemma nzmap_elem_of_dom (m : nzmap) i : i ∈ dom (gset K) m ↔ is_Some (m !! i).
  Proof.
    unfold lookup.
    unfold nzmap_lookup, nzmap_dom.
    destruct m.
    simpl.
    rewrite elem_of_dom.
    reflexivity.
  Qed.

  Lemma nzmap_lookup_wf m i : nzmap_wf m → m !! i <> Some 0.
  Proof.
    intros.
    unfold nzmap_wf, map_Forall in H0.
    firstorder.
  Qed.
  
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
    rewrite lookup_merge in H3.
    unfold merge_op in H3.
    repeat destruct (_ !! _);
    try destruct (decide _);
    first [discriminate |
           inversion H3; trivial; congruence ].
  Qed.
  
  Instance lift_op : CcmOp nzmap := λ m1 m2,
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
  Defined.
  
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
    rewrite lookup_merge in H3.
    unfold merge_opinv in H3.
    repeat destruct (_ !! _);
    try destruct (decide _);
    first [discriminate |
           inversion H3; trivial; congruence ].
  Qed.

  Instance lift_opinv : CcmOpInv nzmap := λ m1 m2,
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
  Defined.

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
      generalize H1.
      apply ccm_cancel.
    - rewrite <- ccm_assoc in e0.
      rewrite e in e0.
      rewrite ccm_right_id in e0.
      assert (a <> 0).
      clear - Hm1i. firstorder.
      contradiction.
    - rewrite <- ccm_assoc.
      rewrite e.
        by rewrite ccm_right_id.
    - rewrite ccm_assoc in e.
      rewrite e0 in e.
      rewrite ccm_left_id in e.
      assert (a0 <> 0).
      clear - Hm3i.
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
  Defined.

  Definition nzmap_unit := NZMap ∅ I.
  
  Instance nzmap_empty : Empty nzmap := nzmap_unit.
  Global Opaque nzmap_empty.

  Instance lift_unit : CcmUnit nzmap := nzmap_unit.
  
  Instance lift_leftid: LeftId (=) 0 lift_op.
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
    apply nzmap_eq in H1.
    apply nzmap_eq.
    simpl in H1.
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
    rewrite H1.
    reflexivity.
    repeat rewrite lookup_merge in H2.
    repeat unfold merge_op in H2.
    
    unfold bool_decide in nzmap_prf0.
    destruct (m1 !! i);
    destruct (m2 !! i);
    destruct (m3 !! i);
    repeat destruct (decide _);
    simpl;
    f_equal;
    inversion H2;
    first [try inversion H2; clear - H2; firstorder; done |
           generalize H4; apply ccm_cancel; done | simpl].
    
    - assert (a + a0 = a + a1).
      clear - e e0.
      firstorder.
      generalize H3.
      apply ccm_cancel.
    - inversion H2.
      assert (a0 <> 0).
      clear - Hm2i.
      firstorder.
      assert (a + 0 = a).
      apply ccm_right_id.
      assert (a + a0 = a + 0) as HC.
      clear - H5 H6.
      firstorder.
      assert (a0 = 0).
      generalize HC.
      apply ccm_cancel.
      contradiction.
    - inversion H2.
      assert (a0 <> 0).
      clear - Hm3i.
      firstorder.
      assert (a + 0 = a).
      apply ccm_right_id.
      assert (a + a0 = a + 0) as HC.
      clear - H5 H6.
      firstorder.
      assert (a0 = 0).
      generalize HC.
      apply ccm_cancel.
      contradiction.
  Defined.

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
      clear - Hm1i.
      firstorder.
      contradiction.
    - assert (a + a0 - a0 = a).
      apply ccm_pinv.
      rewrite e in H1.
        by rewrite H1.
    - rewrite ccm_pinv in e.
      assert (a <> 0).
      clear - Hm1i.
      firstorder.
      contradiction.
    - by rewrite ccm_pinv.
    - reflexivity.
    - destruct (decide _).
      reflexivity.
      assert (0 + a = a) by apply ccm_left_id.
      rewrite <- H1 in n at 1.
      rewrite ccm_pinv in n.
      contradiction.
    - reflexivity.
  Defined.

  Program Instance lift_ccm : CCM nzmap := { }.
                                
End lifting.

Arguments NZMap {_ _ _ _ _} _ _ : assert.
Arguments nzmap_car {_ _ _ _ _} _ : assert.

