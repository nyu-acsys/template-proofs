From iris.algebra Require Import gset.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export iprop.
From iris.base_logic.lib Require Export invariants.

(* Keyset RA *)

Set Default Proof Using "All".
(* Require Export search_str flows auth_ext.*)

Section keyset_ra.

  (* The set of keys. *)
  Context `{Countable K}.

  (* The keyspace is some arbitrary finite subset of K. *)
  (* Parameter KS : gset K. *)

  Inductive ksRAT :=
    prodKS : gset K*gset K → ksRAT
  | topKS : ksRAT.

  Canonical Structure ksRAC := leibnizO ksRAT.

  Global Instance ksRATValid : Valid ksRAT :=
  λ p, match p with
       | prodKS (K, C) => C ⊆ K
       | topKS => False end.
       
  Definition ksRAT_fst : ksRAT → gset K :=
    λ x, match x with prodKS (K, C) => K | topKS => ∅ end.
  
  Definition ksRAT_snd : ksRAT → gset K :=
    λ x, match x with prodKS (K, C) => C | topKS => ∅ end.

  Definition ksRAT_composable (x1 x2: ksRAT) : Prop :=
    ✓ x1 ∧ ✓ x2 ∧ ksRAT_fst x1 ## ksRAT_fst x2. 

  Global Instance ksRAT_valid_dec : ∀ x: ksRAT, Decision (✓ x).
  Proof. intros x. destruct x; try apply _. Qed.

  Global Instance ksRAT_composable_dec (x1 x2: ksRAT) : 
    Decision (ksRAT_composable x1 x2).
  Proof. try apply _. Qed.

  Global Instance ksRAT_eq_dec: EqDecision ksRAT.
  Proof.
    unfold EqDecision.
    unfold Decision.
    intros x y; destruct x, y; try apply _.
    - destruct (decide (p = p0)) as [-> | ?]; try done.
      + left; done.
      + right. intros Hp; inversion Hp. done.
    - right; done.
    - right; done.
    - left; done.
  Qed.

  Global Instance ksRATOp : Op ksRAT :=
    λ x1 x2,
    if (decide (ksRAT_composable x1 x2)) then
      prodKS (ksRAT_fst x1 ∪ ksRAT_fst x2, ksRAT_snd x1 ∪ ksRAT_snd x2)
    else if (decide (x1 = prodKS (∅, ∅))) then x2
    else if (decide (x2 = prodKS (∅, ∅))) then x1
    else topKS.

  Global Instance ksRATCore : PCore ksRAT :=
    λ p, Some (prodKS (∅, ∅)).

  Global Instance ksRATUnit : Unit ksRAT := prodKS (∅, ∅).

  Lemma ksRAT_valid_unfold (x: ksRAT) : 
    ✓ x → ∃ K C, x = prodKS (K, C) ∧ C ⊆ K.
  Proof.
    rewrite /valid /ksRATValid /=. 
    destruct x as [ (Kx, Cx) |]; try done.
    intros ?; exists Kx, Cx; try done.
  Qed.

  Lemma ksRAT_unit_valid : ✓ (prodKS (∅, ∅)).
  Proof.
    rewrite /valid /ksRATValid /=. done.
  Qed.

  Lemma ksRAT_unit_composable (x: ksRAT) : 
    ✓ x → ksRAT_composable x (prodKS (∅, ∅)).
  Proof.
    intros Vx. split; try done.
  Qed.

  Lemma ksRAT_composable_comm (x y: ksRAT) : 
    ksRAT_composable x y → ksRAT_composable y x.
  Proof.
    intros (?&?&?); repeat (split; try done).
  Qed.

  Lemma ksRAT_unit_op (x: ksRAT) :
    x ⋅ prodKS (∅, ∅) ≡ x.
  Proof.
    rewrite /op /ksRATOp /=.
    destruct (decide (✓ x)) as [Hx | Hx].
    - rewrite decide_True. apply ksRAT_valid_unfold in Hx.
      destruct Hx as [Kx [Cx [-> H']]]. simpl.
      apply f_equal. by rewrite !union_empty_r_L.
      by apply ksRAT_unit_composable.
    - rewrite decide_False. rewrite decide_False.
      rewrite decide_True; try done.
      intros ->. apply Hx; try done.
      intros (?&_); try done.
  Qed. 

  Lemma ksRAT_valid_composable (x y: ksRAT) :
    ksRAT_composable x y → ✓ (x ⋅ y).
  Proof.
    intros Hcomp. rewrite /op /ksRATOp /=.
    rewrite decide_True; try done.
    rewrite /valid /ksRATValid /=.
    destruct Hcomp as (Hx&Hy&Disj).
    apply ksRAT_valid_unfold in Hx.
    apply ksRAT_valid_unfold in Hy.
    destruct Hx as [Kx [Cx [-> Hx]]].
    destruct Hy as [Ky [Cy [-> Hy]]].
    simpl. simpl in Disj. set_solver.
  Qed.

  Lemma ksRAT_composable_valid (x y: ksRAT) :
    ✓ (x ⋅ y) → ksRAT_composable x y.
  Proof.
    intros Vxy. rewrite /op /ksRATOp /= in Vxy.
    destruct (decide (ksRAT_composable x y)) as [?|Hcomp]; try done.
    destruct (decide (x = prodKS (∅, ∅))) as [-> | Hx].
    exfalso. apply Hcomp. apply ksRAT_composable_comm. 
    by apply ksRAT_unit_composable.
    destruct (decide (y = prodKS (∅, ∅))) as [-> | Hy]; try done.
  Qed.

  Lemma ksRAT_comm (x y: ksRAT) :
    x ⋅ y ≡ y ⋅ x.
  Proof.
    rewrite /op /ksRATOp.
    destruct (decide (ksRAT_composable x y)) as [Hcomp | Hcomp].
    - rewrite decide_True. destruct Hcomp as (Hx&Hy&Disj).
      apply ksRAT_valid_unfold in Hx.
      apply ksRAT_valid_unfold in Hy.
      destruct Hx as [Kx [Cx [-> Hx]]].
      destruct Hy as [Ky [Cy [-> Hy]]].
      simpl. apply f_equal. apply f_equal2; set_solver.
      by apply ksRAT_composable_comm.
    - destruct (decide (x = prodKS (∅, ∅))) as [-> | Hx].
      + rewrite decide_False.
        destruct (decide (y = prodKS (∅, ∅))); try done.
        intros H'; apply ksRAT_composable_comm in H'. done.
      + destruct (decide (y = prodKS (∅, ∅))) as [-> | Hy].
        all: (rewrite decide_False; try done;
          intros H'; apply ksRAT_composable_comm in H'; done).
  Qed. 
  
  Lemma ksRAT_op_unit (x y: ksRAT) :
    x ⋅ y = prodKS (∅, ∅) → x = prodKS (∅, ∅).
  Proof.
    rewrite /op /ksRATOp. 
    destruct (decide (ksRAT_composable x y)) as [Hcomp | Hcomp].
    - destruct Hcomp as (Vx&Vy&Disj).
      apply ksRAT_valid_unfold in Vx.
      apply ksRAT_valid_unfold in Vy.
      destruct Vx as [Kx [Cx [-> Hx]]].
      destruct Vy as [Ky [Cy [-> Hy]]].
      simpl. intros [=].
      assert (Kx = ∅) as -> by set_solver.
      assert (Cx = ∅) as -> by set_solver. done.
    - destruct (decide (x = prodKS (∅, ∅))); try done.
      destruct (decide (y = prodKS (∅, ∅))); try done.
  Qed.

  Lemma ksRAT_composable_assoc (x y z: ksRAT) :
    ksRAT_composable (x ⋅ y)  z → ksRAT_composable x (y ⋅ z).
  Proof.
    intros Comp_xy_z.
    assert (✓ x ∧ ✓ y) as [Vx Vy]. 
    { destruct Comp_xy_z as (Vxy&_).
      apply ksRAT_composable_valid in Vxy.
      split; apply Vxy. }
    assert (✓ z) as Vz. 
    { by destruct Comp_xy_z as (_&Vz&_). }
    assert (Vx' := Vx). assert (Vy' := Vy). assert (Vz' := Vz).
    apply ksRAT_valid_unfold in Vx.
    apply ksRAT_valid_unfold in Vy.
    apply ksRAT_valid_unfold in Vz.
    destruct Vx as [Kx [Cx [Def_x Hx]]].
    destruct Vy as [Ky [Cy [Def_y Hy]]].
    destruct Vz as [Kz [Cz [Def_z Hz]]].
    assert (✓ (x ⋅ y)) as Vxy.
    { by destruct Comp_xy_z as (?&_). }
    assert (Comp_xy := Vxy).
    apply ksRAT_composable_valid in Comp_xy.
    rewrite /op /ksRATOp in Comp_xy_z.
    rewrite decide_True in Comp_xy_z; try done.
    assert (ksRAT_composable y z) as Comp_yz.
    { repeat split; try done. destruct Comp_xy as (_&_&Disj0).
      destruct Comp_xy_z as (_&_&Disj1).
      subst x y z; simpl in *. set_solver. }
    assert (Vyz := Comp_yz). apply ksRAT_valid_composable in Vyz.
    repeat split; try done. rewrite /op /ksRATOp.
    rewrite decide_True; try done. rewrite /op /ksRATOp in Vyz.
    rewrite decide_True in Vyz; try done. 
    destruct Comp_xy_z as (_&_&Disj0). destruct Comp_xy as (_&_&Disj1).
    subst x y z; simpl in *. set_solver.
  Qed.

  Lemma ksRAT_assoc (x y z: ksRAT) :
    x ⋅ (y ⋅ z) ≡ x ⋅ y ⋅ z.
  Proof.
    rewrite {1}/op /ksRATOp.
    destruct (decide (ksRAT_composable x (y ⋅ z))) as [Hcomp | Hcomp].
    - destruct Hcomp as (Vx&Vyz&Disj0).
      assert (Comp_yz := Vyz). apply ksRAT_composable_valid in Comp_yz.
      assert (Vy := Comp_yz). destruct Vy as (Vy&_).
      assert (Vz := Comp_yz). destruct Vz as (_&Vz&_).
      assert (Vx' := Vx). assert (Vy' := Vy). assert (Vz' := Vz).
      apply ksRAT_valid_unfold in Vx.
      apply ksRAT_valid_unfold in Vy.
      apply ksRAT_valid_unfold in Vz.
      destruct Vx as [Kx [Cx [Def_x Hx]]].
      destruct Vy as [Ky [Cy [Def_y Hy]]].
      destruct Vz as [Kz [Cz [Def_z Hz]]].
      assert (ksRAT_composable x y) as Comp_xy.
      { rewrite /op /ksRATOp in Disj0.
        rewrite decide_True in Disj0; try done.
        simpl in *. split; try (done || set_solver). }
      assert (✓ (x ⋅ y)) as Vxz.
      { by apply ksRAT_valid_composable. }
      rewrite {3}/op /ksRATOp. rewrite decide_True; last first.
      { split; last split; try done.
        rewrite /op /ksRATOp in Disj0.
        rewrite decide_True in Disj0; try done.
        rewrite /op /ksRATOp. rewrite decide_True; try done.
        destruct Comp_yz as (_&_&Disj1).
        subst x y z; simpl in *. set_solver. }
      rewrite /op /ksRATOp. rewrite !decide_True; try done. 
      subst x y z; simpl in *. 
      apply f_equal; apply f_equal2; set_solver.
    - destruct (decide (x = prodKS (∅, ∅))) as [-> | Hx].
      + rewrite (ksRAT_comm _ y). by rewrite ksRAT_unit_op.
      + destruct (decide (y ⋅ z = prodKS (∅, ∅))) as [Comp_yz | Comp_yz].
        * assert (y = prodKS (∅, ∅)) as ->.
          { by apply (ksRAT_op_unit y z). }
          assert (z = prodKS (∅, ∅)) as ->.
          { rewrite ksRAT_comm in Comp_yz. 
            by rewrite ksRAT_unit_op in Comp_yz. }
          by rewrite !ksRAT_unit_op.
        * rewrite {1}/op /ksRATOp.
          rewrite decide_False; last first.
          { intros Comp_xy_z. apply Hcomp.
            by apply ksRAT_composable_assoc. }
          rewrite decide_False; last first.
          { intros Hxy. apply ksRAT_op_unit in Hxy. done. }
          destruct (decide (z = prodKS (∅, ∅))) as [-> | Hz]; try done.
          rewrite ksRAT_unit_op in Hcomp Comp_yz.
          rewrite /op /ksRATOp. rewrite !decide_False; try done.
  Qed. 

  Definition ksRAT_mixin : RAMixin ksRAT.
  Proof.
    split; try apply _; try done.
    - intros ? ? cx -> ?. exists cx. done.
    - intros x y z; apply ksRAT_assoc.
    - intros x y; apply ksRAT_comm.
    - intros x cx. rewrite /pcore /ksRATCore /=.
      intros [= <-]. rewrite ksRAT_comm.
      by rewrite ksRAT_unit_op.
    - intros x cx. rewrite /pcore /ksRATCore /=.
      by rewrite leibniz_equiv_iff.
    - intros x y cx Hxy. rewrite /pcore /ksRATCore /=.
      intros [= <-]. exists (prodKS (∅, ∅)).
      split; try done. exists (prodKS (∅, ∅)).
      by rewrite ksRAT_unit_op.
    - intros x y Vxy. apply ksRAT_composable_valid in Vxy.
      by destruct Vxy as (?&_).
  Qed.
  
  Canonical Structure ksRA := discreteR ksRAT ksRAT_mixin.

  Global Instance ksRA_cmra_discrete : CmraDiscrete ksRA.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma ksRA_ucmra_mixin : UcmraMixin ksRAT.
  Proof.
    split; try apply _; try done. unfold LeftId. 
    intros x. rewrite /ε /ksRATUnit /=.
    rewrite ksRAT_comm. by rewrite ksRAT_unit_op.
  Qed.

  Canonical Structure keysetUR : ucmra := Ucmra ksRAT ksRA_ucmra_mixin.

  Lemma ksRAT_prodKS_op (a1 a2 b1 b2: gset K) :
  ✓ (prodKS (a1, b1) ⋅ prodKS (a2, b2)) →
    prodKS (a1, b1) ⋅ prodKS (a2, b2) = prodKS (a1 ∪ a2, b1 ∪ b2).
  Proof.
    intros Hv. rewrite /op /ksRATOp /=.
    rewrite decide_True; try done. by apply ksRAT_composable_valid.
  Qed. 

  Lemma auth_ks_included (a1 a2 b1 b2: gset K) :
  ✓ prodKS (a1, b1) → 
  ✓ prodKS (a2, b2) → 
  prodKS (a1, b1) ≼ prodKS (a2, b2) → 
      (∃ a0 b0, a2 = a1 ∪ a0 ∧ b2 = b1 ∪ b0 
                ∧ a1 ## a0 ∧ b1 ## b0 ∧ b1 ⊆ a1 ∧ b2 ⊆ a2 ∧ b0 ⊆ a0).
  Proof.
    intros Ha1 Ha2 Hincl. destruct Hincl as [z Hincl]. 
    assert (✓ z) as Vz. 
    { apply (cmra_valid_op_r (prodKS (a1, b1))). rewrite <- Hincl. done. } 
    assert (Ha1' := Ha1). assert (Ha2' := Ha2). 
    rewrite /valid /= in Ha1 Ha2.
    destruct z as [(a0, b0) | ]; try done.
    rewrite Hincl in Ha2'. apply ksRAT_composable_valid in Ha2'.
    rewrite /op /ksRATOp in Hincl. rewrite decide_True in Hincl; try done.
    destruct Ha2' as (_&_&Disj). simpl in *.
    inversion Hincl. set_solver.
  Qed.
  
  Lemma auth_ks_local_update_insert KS K1 C Cn k:
    ✓ prodKS (KS, C) → ✓ prodKS (K1, Cn) → 
    k ∈ K1 → k ∉ Cn → k ∈ KS →
      (prodKS (KS, C), prodKS (K1, Cn)) ~l~>  
        (prodKS (KS, C ∪ {[k]}), prodKS (K1, Cn ∪ {[k]})).
  Proof.
    intros VC VCn k_n_K1 k_notin_Cn k_in_KS. 
    apply local_update_discrete. intros z.
    intros _ HKS. split. rewrite /valid /cmra_valid /=. 
    rewrite /valid /= in VC. set_solver.
    rewrite /opM in HKS. rewrite /opM.
    destruct z as [z|]. 
    - assert (✓ z) as Hz.
      { rewrite HKS in VC. by apply cmra_valid_op_r in VC. }
      destruct z as [(Kz, Cz)|]; try done. 
      assert (ksRAT_composable (prodKS (K1, Cn)) (prodKS (Kz, Cz))) as Hcomp.
      { rewrite HKS in VC. by apply ksRAT_composable_valid. }
      rewrite /op /cmra_op /= /ksRATOp.
      rewrite decide_True; last first.
      { repeat split; rewrite /valid /=; try done.
        rewrite /valid /ksRATValid in VCn. set_solver.
        destruct Hcomp as (_&_&H'). by simpl in H'. }
      simpl. apply f_equal.
      rewrite /op /cmra_op /= /ksRATOp in HKS.
      rewrite decide_True in HKS; try done. simpl in HKS.
      inversion HKS. apply f_equal2; set_solver.
    - inversion HKS. apply f_equal. apply f_equal2; set_solver.
  Qed.  
  
  Lemma auth_ks_local_update_delete KS K1 C Cn k:
    ✓ prodKS (KS, C) → ✓ prodKS (K1, Cn) → 
    k ∈ K1 → k ∈ Cn →
      (prodKS (KS, C), prodKS (K1, Cn)) ~l~>  
        (prodKS (KS, C ∖ {[k]}), prodKS (K1, Cn ∖ {[k]})).
  Proof.
    intros VC VCn k_n_K1 k_notin_Cn. 
    apply local_update_discrete. intros z.
    intros _ HKS. split. rewrite /valid /cmra_valid /=. 
    rewrite /valid /= in VC. set_solver.
    rewrite /opM in HKS. rewrite /opM.
    destruct z as [z|]. 
    - assert (✓ z) as Hz.
      { rewrite HKS in VC. by apply cmra_valid_op_r in VC. }
      destruct z as [(Kz, Cz)|]; try done. 
      assert (ksRAT_composable (prodKS (K1, Cn)) (prodKS (Kz, Cz))) as Hcomp.
      { rewrite HKS in VC. by apply ksRAT_composable_valid. }
      rewrite /op /cmra_op /= /ksRATOp.
      rewrite decide_True; last first.
      { repeat split; rewrite /valid /=; try done.
        rewrite /valid /ksRATValid in VCn. set_solver.
        destruct Hcomp as (_&_&H'). by simpl in H'. }
      simpl. apply f_equal.
      rewrite /op /cmra_op /= /ksRATOp in HKS.
      rewrite decide_True in HKS; try done. simpl in HKS.
      assert (k ∉ Cz). 
      { destruct Hcomp as (_&_&H'). simpl in H'. 
        rewrite /valid /ksRATValid in Hz. set_solver. }
      inversion HKS. apply f_equal2; set_solver.
    - inversion HKS. apply f_equal. apply f_equal2; set_solver.
  Qed.  
  
End keyset_ra.
Arguments keysetUR _ {_ _}.

