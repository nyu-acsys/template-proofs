Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export flows ccm.

(** Flow interface cameras and auxiliary lemmas for inset flows
  (used in the give-up template proof) *)

Section inset_flows.

Context `{Countable K}.
  
(** CCM of multisets over keys *)

Definition K_multiset := nzmap K nat.

Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

Definition dom_ms (m : K_multiset) := nzmap_dom K nat m.

Canonical Structure inset_flowint_ur : ucmraT := flowintUR K_multiset.

Implicit Type I : inset_flowint_ur.

(** Insets, outsets, and keysets of flow interfaces *)

Definition inset I n := dom_ms (inf I n).

Definition outset I n := dom_ms (out I n).

Definition in_inset k I n := k ∈ dom_ms (inf I n).

Definition in_outset k I n := k ∈ dom_ms (out I n).

Definition in_outsets k In := ∃ n, in_outset k In n.

Definition keyset I n := dom_ms (inf I n) ∖ dom_ms (out I n).

Lemma keyset_def : ∀ k I_n n, k ∈ inset I_n n → ¬ in_outsets k I_n
  → k ∈ keyset I_n n.
Proof.
  intros ? ? ? k_in_inset k_not_in_outsets.
  unfold keyset.
  unfold inset in k_in_inset.
  unfold in_outsets in k_not_in_outsets.
  rewrite elem_of_difference.
  naive_solver.
Qed.

(* The global invariant ϕ. *)
Definition globalinv root I :=
  ✓I
  ∧ (root ∈ domm I)
  ∧ (∀ k n, k ∉ outset I n) 
  ∧ ∀ n, ((n = root) → (∀ k, k ∈ inset I n))
         ∧ ((n ≠ root) → (∀ k, k ∉ inset I n)).

(** Assorted lemmas about inset flows used in the template proofs *)

Lemma flowint_step :
  ∀ I I1 I2 k n root,
    globalinv root I → I = I1 ⋅ I2 → k ∈ outset I1 n → n ∈ domm I2.
Proof.
  intros I I1 I2 k n r gInv dI kOut.
  unfold globalinv in gInv.
  destruct gInv as (vI & rI & cI & _).
  
  assert (domm I = domm I1 ∪ domm I2) as disj.
  rewrite dI in vI.
  pose proof (intComp_dom _ _ vI).
  rewrite dI.
  trivial.

  assert (✓ I1) as vI1.
  rewrite dI in vI.
  eauto using intComp_valid_proj1.

  apply flowint_valid_unfold in vI1.
  destruct vI1 as [Ir1 [dI1 [disj1 _]]].

  (* First, prove n ∉ domm I1 *)
  
  assert (is_Some (out I1 n !! k)) as out1nk.
  unfold outset, dom_ms, nzmap_dom in kOut.
    by rewrite nzmap_elem_of_dom in kOut *.
  assert (is_Some (outR Ir1 !! n)) as out1n.
  unfold out, out_map in out1nk.
  rewrite dI1 in out1nk.
  destruct (outR Ir1 !! n); eauto.
  unfold default in out1nk.
  rewrite lift_lookup_empty in out1nk.
  unfold is_Some in out1nk.
  destruct out1nk.
  inversion H0.

  assert (n ∈ dom (gset Node) (outR Ir1)) as inOut1n.
  by apply elem_of_dom.

  assert (dom (gset Node) (infR Ir1) ## dom (gset Node) (outR Ir1)) as domDisj1.
  by apply map_disjoint_dom.

  assert (n ∉ dom (gset Node) (infR Ir1)) as not_in_Inf1_n.
  set_solver.

  (* Now, prove n ∈ domm I *)

  assert (vI' := vI).
  apply flowint_valid_unfold in vI'.
  destruct vI' as [Ir [dI' [disj' _]]].

  assert (n ∈ dom (gset Node) (infR Ir)) as in_Inf_n.
  rewrite dI in vI.
  pose proof (intComp_unfold_out I1 I2 vI n).
  destruct (decide (n ∉ domm (I1 ⋅ I2))).
  apply H0 in n0.
  pose proof (cI k n) as not_k_out.
  unfold outset, dom_ms, nzmap_dom in not_k_out.
  apply not_elem_of_dom in not_k_out.
  assert (out I n !! k = out (I1 ⋅ I2) n !! k).
  rewrite dI. reflexivity.
  rewrite n0 in H1.
  unfold ccmop, ccm_op in H1.
  unfold K_multiset_ccm in H1.
  unfold lift_ccm in H1.
  unfold lift_op in H1.
  case_eq (out I1 n).
  intros ? ? out1.
  rewrite out1 in H1.
  case_eq (out I2 n).
  intros ? ? out2.
  rewrite out2 in H1.
  unfold lookup at 2 in H1.
  unfold nzmap_lookup in H1.
  rewrite lookup_merge in H1.
  unfold merge_op in H1.
  assert (out I1 n !! k = nzmap_car !! k).
  rewrite out1. unfold lookup at 1. by unfold nzmap_lookup.
  rewrite <- H2 in H1.
  unfold is_Some in out1nk.
  destruct out1nk as [x1 out1nk].
  rewrite out1nk in H1.
  assert (x1 <> 0) as x1_pos.
  pose proof (nzmap_is_wf _ _ (out I1 n)).
  rewrite out1 in H3. simpl in H3.
  pose proof (nzmap_lookup_wf _ _ _ k H3).
  rewrite <- H2 in H4.
  rewrite out1nk in H4.
  clear - H4.
  firstorder.

  destruct (nzmap_car0 !! k);
  try destruct decide in H1;
  first [
         clear - e x1_pos;
         (* TODO: There must be a better way of doing this... *)
         unfold ccm_unit, ccmunit, nat_ccm, nat_unit, ccm_op, ccmop, nat_op in e; simpl;
         lia |
         unfold ccm.nzmap_car in not_k_out;
           unfold lookup in H1;
           case_eq (out I n);
           intros;
           rewrite H3 in H1;
           rewrite H3 in not_k_out;
           unfold lookup in not_k_out;
           rewrite not_k_out in H1;
           inversion H1].

  unfold domm, dom, flowint_dom, inf_map in n0.
  rewrite <- dI in n0.
  rewrite dI' in n0.
  apply dec_stable in n0.
  trivial.
  
  (* Finally, prove n ∈ domm I2 *)
  
  unfold domm, dom, flowint_dom.
  unfold domm, dom, flowint_dom in disj.
  unfold inf_map at 1 in disj; rewrite dI' in disj.
  unfold inf_map at 1 in disj; rewrite dI1 in disj.
  rewrite elem_of_equiv_L in disj *.
  intro dom_I.
  pose proof (dom_I n) as dom_I_n.
  rewrite elem_of_union in dom_I_n *.
  naive_solver.
Qed.

Lemma outset_distinct : ∀ I n, ✓ I ∧ (∃ k, k ∈ outset I n) → n ∉ domm I.
Proof.
  intros.
  destruct H0 as (VI & Out).
  destruct Out as [k Out].

  apply flowint_valid_unfold in VI.
  destruct VI as (Ir & dI & disj & _).

  rewrite map_disjoint_spec in disj *.
  intros disj.
  
  assert (is_Some (outR Ir !! n)).
  * unfold outset, out in Out.
    case_eq (out_map I !! n).
    - intros.
      unfold out_map in H0.
      rewrite dI in H0.
      unfold is_Some.
      exists k0.
      trivial.

    - intros.
      rewrite H0 in Out.
      unfold default, dom_ms, nzmap_dom, ccmunit, lift_unit, nzmap_unit in Out.
      simpl in Out.
      rewrite dom_empty in Out *. intros Out.
      apply elem_of_empty in Out.
      contradiction.

  * case_eq (infR Ir !! n).
    - intros.
      unfold is_Some in H0.
      destruct H0.
      pose proof (disj n k0 x H1 H0).
      contradiction.

    - intros.
      unfold domm.
      unfold dom, flowint_dom.
      rewrite elem_of_dom.
      unfold not.
      intro.
      unfold is_Some in H2.
      destruct H2.
      rewrite dI in H2.
      unfold inf_map in H2.
      rewrite H2 in H1.
      inversion H1.
Qed.


Lemma inset_monotone : ∀ I I1 I2 k n,
    ✓ I → I = I1 ⋅ I2 → k ∈ inset I n → n ∈ domm I1 → k ∈ inset I1 n.
Proof.
  intros ? ? ? ? ? VI ID Inset Dom.
  rewrite ID in VI.
  pose proof (intComp_unfold_inf_1 I1 I2 VI n) as Inf1.
  apply Inf1 in Dom.
  assert (Inset1 := Inset).
  unfold inset, dom_ms, nzmap_dom in Inset.
  rewrite nzmap_elem_of_dom in Inset *.
  intros Inset.
  unfold inf, inf_map in Dom.
  pose proof (intComp_valid_proj1 I1 I2 VI) as VI1.
  apply flowint_valid_defined in VI1.
  destruct VI1 as [I1r I1D].
  pose proof (intComp_valid_proj2 I1 I2 VI) as VI2.
  apply flowint_valid_defined in VI2.
  destruct VI2 as [I2r I2D].

  apply flowint_valid_defined in VI.
  destruct VI as [I12r I12D].

  rewrite I1D in Dom.
  rewrite I1D in I12D.
  rewrite I12D in Dom.

  unfold inset, inf, dom_ms, inf_map.
  rewrite I1D.
  rewrite Dom.
  rewrite nzmap_elem_of_dom_total.
  rewrite lookup_op.
  unfold nzmap_total_lookup.
  unfold inf, is_Some, inf_map in Inset.
  destruct Inset as [x Inset].
  rewrite ID in Inset.
  rewrite I1D in Inset.
  rewrite I12D in Inset.
  rewrite Inset.
  simpl.
  
  assert (x <> 0).
  unfold inset, dom_ms in Inset1.
  rewrite nzmap_elem_of_dom_total in Inset1 *.
  intros xDef.
  rewrite ID in xDef.
  rewrite I1D in xDef.
  rewrite I12D in xDef.
  unfold inf, inf_map in xDef.
  unfold nzmap_total_lookup in xDef.
  rewrite Inset in xDef.
  simpl in xDef.
  trivial.
  
  unfold ccmop, ccm_op, nat_ccm, nat_op, out, out_map.
  unfold ccmunit, nat_unit.
  lia.
  all: apply K_multiset_ccm.
Qed.

(*
Parameter KS : gset K.

Definition nodeinv root n I_n  C_n : Prop :=
  n ∈ domm I_n
  ∧ C_n = keyset I_n n
  ∧ (∀ k, default 0 (inf I_n n !! k) ≤ 1)
  ∧ (n = root → ∀ k, k ∈ KS → in_outsets k I_n).

Lemma successor_not_first : ∀ (I I1 I2 I3 : flowintT) C root n k,
    globalinv root I →
    I = I1 ⋅ I2 ⋅ I3 →
    k ∈ outset I1 n →
    k ∈ KS →
    nodeinv root n I2 C →
    n ≠ root.
Proof.
  intros ? ? ? ? ? ? ? ? GI IDef k_in_out1 k_in_KS NI.
  destruct (decide (n = root)).
  destruct GI as (VI & root_in_I & I_closed & I_inf_out).
  rewrite <- cmra_assoc in IDef.
  (*unfold op, cmra_op, ucmra_cmraR, inset_flowint_ur, flowintUR, ucmra_op in IDef.*)
  rewrite IDef in VI.
  pose proof (intComp_valid_proj1 _ _ VI) as V1.
  pose proof (intComp_valid_proj2 _ _ VI) as V23.
  pose proof (intComp_unfold_inf_1 _ _ VI n) as inf_I1.
  pose proof (intComp_unfold_inf_1 _ _ V23) as inf_I2.
  destruct NI as (n_in_I2 & _ & inf_bound & _).
  assert (n ∈ domm I2 ∪ domm I3) as n_in_I23 by set_solver.
  pose proof (intComp_unfold_inf_2 _ _ VI n) as inf_I23.
  rewrite intComp_dom in inf_I23.
  apply inf_I23 in n_in_I23 as n_inf_I23.
  unfold cmra_op, flowintRA, cmra_car, K_multiset at 5, K_multiset at 5, K_multiset_ccm at 3 in n_inf_I23.
  pose proof (I_inf_out root) as (root_out & _).
  assert (root = root) by reflexivity.
  pose proof (root_out H0 k) as root_out_k.
  
  assert (default 0 (inf I n !! k) <> 0).
  rewrite e.
  unfold inset, dom_ms, nzmap_dom in root_out_k.
  apply elem_of_dom in root_out_k.
  unfold lookup, nzmap_lookup.
  pose proof (nzmap_is_wf _ _ (inf I root)) as inf_root_wf.
  pose proof (nzmap_lookup_wf _ _ _ k inf_root_wf).
  destruct (inf I root).
  simpl in root_out_k.
  unfold is_Some in root_out_k.
  destruct root_out_k as [x root_out_k].
  rewrite root_out_k.
  simpl in H1.
  simpl.
  naive_solver.
  pose proof (lookup_op _ _ (inf I n) (out I1 n) k) as inf_I23_def.
  
  rewrite IDef in inf_I23_def.
  unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I23_def.
  unfold ccm_op, lift_ccm in n_inf_I23.
  rewrite <- n_inf_I23 in inf_I23_def.
  unfold cmra_op, flowintRA, cmra_car in IDef.
  rewrite <- IDef in inf_I23_def.
  
  pose proof (inf_I2 n n_in_I2) as n_inf_I2.
  pose proof (lookup_op _ _ (inf (I2 ⋅ I3) n) (out I3 n) k) as inf_I2_def.
  unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I2_def.
  unfold cmra_op, flowintRA, cmra_car, K_multiset at 3, K_multiset_ccm at 2 in n_inf_I2.
  unfold ccm_op, lift_ccm in n_inf_I2.
  rewrite <- n_inf_I2 in inf_I2_def.
  rewrite inf_I23_def in inf_I2_def.
  
  assert (default 0 (out I1 n !! k) ≠ 0).
  unfold outset, dom_ms, nzmap_dom in k_in_out1.
  apply elem_of_dom in k_in_out1.
  unfold lookup, nzmap_lookup.
  pose proof (nzmap_is_wf _ _ (out I1 n)) as out_n_wf.
  pose proof (nzmap_lookup_wf _ _ _ k out_n_wf).
  destruct (out I1 n).
  simpl in k_in_out1.
  unfold is_Some in k_in_out1.
  destruct k_in_out1 as [x k_in_out1].
  rewrite k_in_out1.
  simpl in H2.
  simpl.
  naive_solver.
  unfold ccmunit, ccmop, ccm_unit, ccm_op, nat_ccm, nat_unit, nat_op in inf_I23_def.
  unfold ccmunit, ccmop, ccm_unit, ccm_op, nat_ccm, nat_unit, nat_op in inf_I2_def.
  pose proof (inf_bound k).
  remember (inf I2 n !! k) as x2.
  unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx2.
  rewrite <- Heqx2 in inf_I2_def.
  remember (inf I n !! k) as x.
  unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx.
  rewrite <- Heqx in inf_I2_def.
  remember (out I1 n !! k) as x1.
  unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx1.
  rewrite <- Heqx1 in inf_I2_def.
  lia.
  all: trivial.
Qed.
 *)
End inset_flows.

Arguments inset_flowint_ur _ {_ _} : assert.
Arguments inset _ {_ _} _ _ : assert.
Arguments outset _ {_ _} _ _ : assert.
Arguments keyset _ {_ _} _ _ : assert.
Arguments in_inset _ {_ _} _ _ _ : assert.
Arguments in_outset _ {_ _} _ _ _ : assert.
Arguments in_outsets _ {_ _} _ _ : assert.
Arguments globalinv _ {_ _} _ _ : assert.
