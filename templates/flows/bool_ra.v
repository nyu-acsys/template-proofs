From iris.algebra Require Import cmra.
From iris.heap_lang Require Export lang.
Set Default Proof Using "All".

Section bool_ra.
  Local Instance bool_valid_instance : Valid bool := λ x, True.
  Local Instance bool_validN_instance : ValidN bool := λ n x, True.
  Local Instance bool_pcore_instance : PCore bool := λ x, Some true.
  Local Instance bool_op_instance : Op bool := andb.
  Definition bool_op x y : x ⋅ y = x && y := eq_refl.
  (*
  Lemma nat_included (x y : nat) : x ≼ y ↔ x ≤ y.
  Proof. by rewrite Nat.le_sum. Qed.
  *)
  Lemma bool_ra_mixin : RAMixin bool.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
    - intros x y z. apply andb_assoc.
    - intros x y. apply andb_comm.
    - intros x y. rewrite /core /=. intros _; by exists true. 
  Qed.
  Canonical Structure boolR : cmra := discreteR bool bool_ra_mixin.

  Global Instance bool_cmra_discrete : CmraDiscrete boolR.
  Proof. apply discrete_cmra_discrete. Qed.

  Local Instance bool_unit_instance : Unit bool := true.
  Lemma bool_ucmra_mixin : UcmraMixin bool.
  Proof. split; apply _ || done. Qed.
  Canonical Structure boolUR : ucmra := Ucmra bool bool_ucmra_mixin.

End bool_ra.

Section loc_ra.
  Local Instance loc_valid_instance : Valid loc := λ x, True.
  Local Instance loc_validN_instance : ValidN loc := λ n x, True.
  Local Instance loc_pcore_instance : PCore loc := λ x, Some {| loc_car := 0 |}.
  Local Instance loc_op_instance : Op loc :=
    λ x y, match x, y with {| loc_car := lx |}, {| loc_car := ly |} => 
      {| loc_car := lx + ly |} end.

  Lemma loc_ra_mixin : RAMixin loc.
  Proof.
    apply ra_total_mixin; try by (eauto || apply _).
    - intros [lx] [ly] [lz]. rewrite /op /loc_op_instance /=.
      by assert ((lx + (ly + lz))%Z = (lx + ly + lz)%Z) as -> by lia.
    - intros [lx] [ly]. rewrite /op /loc_op_instance /=. 
      by assert ((lx + ly)%Z = (ly + lx)%Z) as -> by lia.
    - intros [lx]; rewrite /core /op /loc_op_instance /=.
      by assert ((0 + lx)%Z = (lx)%Z) as -> by lia.
    - intros [lx] [ly]. rewrite /core /included /=.
      intros _. exists {| loc_car := 0 |}.
      rewrite /op /loc_op_instance. 
      by assert ((0 + 0)%Z = 0%Z) as -> by lia.
  Qed.
  
  Local Instance loc_unit_instance : Unit loc := {| loc_car := 0 |}.
  Print discreteR.
  Canonical Structure locR : cmra := discreteR loc loc_ra_mixin.

  Global Instance loc_cmra_discrete : CmraDiscrete locR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma loc_ucmra_mixin : UcmraMixin loc.
  Proof. 
    split; try apply _; try done. intros [lx].
    rewrite /ε /loc_unit_instance /op /loc_op_instance.
    by assert ((0 + lx)%Z = (lx)%Z) as -> by lia.
  Qed.
  Canonical Structure locUR : ucmra := Ucmra loc loc_ucmra_mixin.

End loc_ra.
