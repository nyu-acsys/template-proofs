Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export flows ccm keyset_ra.

(** Flow interface cameras and auxiliary lemmas for inset and linkset flows
  (used in the link template proof) *)

Section linkset_flows.

Context `{Countable K}.
  
Definition KS := @KS K _ _.

(** CCM of pairs of multisets over keys *)

Definition K_multiset := nzmap K nat.

Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

Definition dom_ms (m : K_multiset) := nzmap_dom m.

Instance K_multiset_pair_ccm : CCM (K_multiset * K_multiset) :=
  prod_ccm K_multiset K_multiset.

Canonical Structure linkset_flowint_ur : ucmraT :=
  flowintUR (K_multiset * K_multiset).

Implicit Type I : linkset_flowint_ur.

(** Insets, outsets, and keysets of flow interfaces *)

Definition inset I n := dom_ms (fst (inf I n)).

Definition linkset I n := dom_ms (snd (inf I n)).

Definition outset I n := dom_ms (fst (out I n)) ∪ dom_ms (snd (out I n)).

(* TODO these are no longer needed, just use the definition instead *)
Definition in_inset k I n := k ∈ inset I n.

Definition in_linkset k I n := k ∈ linkset I n.

Definition in_outset k I n := k ∈ outset I n.

Definition in_outsets k In := ∃ n, in_outset k In n.

Definition keyset I n := inset I n ∖ outset I n.

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
  ∧ (∀ k, k ∈ KS → k ∈ inset I root ∧ k ∈ linkset I root)
  ∧ (∀ n, (n ≠ root) → (∀ k, ¬(k ∈ inset I n ∧ k ∉ linkset I n))).

(** Assorted lemmas about inset and linkset flows used in the template proofs *)

Lemma globalinv_root_fp: ∀ I root, globalinv root I → root ∈ domm I.
Proof.
  intros I root Hglob. unfold globalinv in Hglob.
  destruct Hglob as [H1 [H2 H3]]. done.
Qed.

Lemma flowint_step :
  ∀ I I1 I2 k n root,
    globalinv root I → I = I1 ⋅ I2 → k ∈ outset I1 n → n ∈ domm I2.
Proof.
  intros I I1 I2 k n r gInv dI kOut.
  unfold globalinv in gInv.
  destruct gInv as (vI & rI & cI & _).
  rewrite dI in vI.
  
  assert (domm I = domm I1 ∪ domm I2) as disj.
  pose proof (intComp_dom _ _ vI).
  rewrite dI.
  trivial.

  (* First, prove n ∉ domm I1 *)
  destruct (decide (n ∈ domm I1)).
  pose proof (intComp_valid_proj1 I1 I2 vI) as vI1.
  pose proof (intValid_in_dom_not_out I1 n vI1 e).
  unfold outset, dom_ms in kOut.
  rewrite elem_of_union in kOut *.
  intros kOut.
  rewrite nzmap_elem_of_dom_total in kOut *.
  intros.
  (*unfold ccmunit, ccm_unit, K_multiset_ccm, lift_ccm, lift_unit in H0.*)
  rewrite H0 in H1.
  rewrite nzmap_lookup_empty in H1.
  { destruct H1.
    - contradiction.
    - unfold ccmunit, ccm_unit, K_multiset_pair_ccm, prod_ccm, prod_unit in H1.
      simpl in H1.
      rewrite nzmap_elem_of_dom_total in H1 *.
      intros.
      rewrite nzmap_lookup_empty in H1.
      contradiction.
  }
  
  (* Now, prove n ∈ domm I *)
  assert (n ∈ domm I) as in_Inf_n. 
  (*rewrite dI in vI.*)
  pose proof (intComp_unfold_out I1 I2 vI n).
  destruct (decide (n ∉ domm (I1 ⋅ I2))).
  apply H0 in n1.
  pose proof (cI k n) as not_k_out.
  unfold outset, dom_ms in not_k_out.
  rewrite not_elem_of_union in not_k_out *.
  intros not_k_out.
  unfold op, cmra_op, ucmra_cmraR, ucmra_op, linkset_flowint_ur, flowintUR in dI.
  unfold op in n1.
  rewrite <- dI in n1.
  rewrite n1 in not_k_out.
  repeat (rewrite nzmap_elem_of_dom_total in not_k_out *;
  intro not_k_out).
  unfold ccmop, ccm_op, K_multiset_pair_ccm at 1 4, K_multiset_ccm at 1 4, prod_ccm, prod_op in not_k_out.
  simpl in not_k_out.
  repeat rewrite lookup_op in not_k_out.
  unfold outset, dom_ms in kOut.
  rewrite elem_of_union in kOut *.
  intros kOut.
  repeat (rewrite nzmap_elem_of_dom_total in kOut *; intros kOut).
  unfold ccmop, ccm_op, nat_ccm at 1 4, nat_op, ccmunit, nat_unit in not_k_out.
  destruct not_k_out as (not_k_out1 & not_k_out2).
  apply dec_stable in not_k_out1.
  apply dec_stable in not_k_out2.
  remember ((out I1 n).1 ! k) as x1.
  remember ((out I1 n).2 ! k) as x2.
  unfold ccmop, ccm_op, nat_ccm, nat_op, ccm_unit, ccmunit, nat_unit in kOut.
  destruct kOut as [kOut | kOut]; lia.
  
  rewrite dI.
  apply dec_stable in n1.
  trivial.
  
  (* Finally, prove n ∈ domm I2 *)
  
  unfold domm, dom, flowint_dom.
  unfold domm, dom, flowint_dom in disj.
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

  rewrite (@map_disjoint_dom Node (gmap Node) (gset Node)) in disj *.
  intros disj.

  unfold outset, dom_ms, nzmap_dom, out, out_map in Out.
  rewrite dI in Out.
  rewrite elem_of_union in Out *.
  intros Out.
  rewrite nzmap_elem_of_dom_total in Out *.
  intros Out.
  destruct (decide (outR Ir ! n = 0%CCM)).
  rewrite e in Out.
  rewrite nzmap_lookup_empty in Out.
  { destruct Out.
    - contradiction.
    - unfold ccmunit, ccm_unit, K_multiset_pair_ccm, prod_ccm, prod_unit in H0.
      simpl in H0.
      apply dom_empty in H0.
      apply elem_of_empty in H0.
      contradiction.
  }

  rewrite <- nzmap_elem_of_dom_total in n0.
  unfold dom, nzmap_dom in n0.
  
  unfold domm, dom, flowint_dom, inf_map.
  rewrite dI.
  set_solver.
Qed.

Lemma linkset_monotone : ∀ I I1 I2 k n,
    ✓ I → I = I1 ⋅ I2 → k ∈ linkset I n → n ∈ domm I1 → k ∈ linkset I1 n.
Proof.
  intros ? ? ? ? ? VI ID Link Dom.
  rewrite ID in VI.
  pose proof (intComp_unfold_inf_1 I1 I2 VI n) as Inf1.
  apply Inf1 in Dom.
  assert (Link1 := Link).
  unfold linkset, dom_ms, nzmap_dom in Link.
  rewrite nzmap_elem_of_dom in Link *.
  intros Link.
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

  unfold linkset, inf, dom_ms, inf_map.
  rewrite I1D.
  rewrite Dom.
  rewrite nzmap_elem_of_dom_total.
  rewrite lookup_op.
  unfold nzmap_total_lookup.
  unfold inf, is_Some, inf_map in Link.
  destruct Link as [x Link].
  rewrite ID in Link.
  rewrite I1D in Link.
  rewrite I12D in Link.
  rewrite Link.
  simpl.
  
  assert (x <> 0).
  unfold linkset, dom_ms in Link1.
  rewrite nzmap_elem_of_dom_total in Link1 *.
  intros xDef.
  rewrite ID in xDef.
  rewrite I1D in xDef.
  rewrite I12D in xDef.
  unfold inf, inf_map in xDef.
  unfold nzmap_total_lookup in xDef.
  rewrite Link in xDef.
  simpl in xDef.
  trivial.
  
  unfold ccmop, ccm_op, nat_ccm, nat_op, out, out_map.
  unfold ccmunit, nat_unit.
  lia.
  all: apply K_multiset_pair_ccm.
Qed.

Lemma flowint_linkset_step : ∀ I1 I2 k n,
    ✓ (I1 ⋅ I2) → n ∈ domm I2 → k ∈ outset I1 n → k ∈ linkset I2 n ∨ k ∈ inset I2 n.
Proof.
  intros ? ? ? ? I12V Out Link.
  pose proof (intComp_valid_proj1 I1 I2 I12V) as I1V.
  pose proof (intComp_valid_proj2 I1 I2 I12V) as I2V.
  apply flowint_valid_defined in I1V.
  destruct I1V as [I1r I1Def].
  apply flowint_valid_defined in I2V.
  destruct I2V as [I2r I2Def].
  pose proof (flowint_valid_defined _ _ I12V) as I12Def.
  destruct I12Def as [I12r I12Def].

  pose proof (intComp_unfold_inf_2 I1 I2 I12V n Out) as Inf2.

  unfold outset in Link.
  unfold linkset, inset, dom_ms.
  rewrite Inf2.
  unfold out, out_map.
  rewrite I1Def.
  repeat rewrite nzmap_elem_of_dom_total.
  repeat rewrite lookup_op.

  unfold dom_ms, out, out_map in Link.
  rewrite I1Def in Link.
  rewrite elem_of_union in Link *.
  intros Link.
  repeat (rewrite nzmap_elem_of_dom_total in Link *; intros Link).
  unfold ccmop, ccm_op, nat_ccm, nat_op.
  unfold ccmop, ccm_op, nat_ccm, nat_op in Link.
  unfold ccmunit, ccm_unit, nat_unit, K_multiset_pair_ccm, prod_ccm.
  unfold ccmunit, ccm_unit, nat_unit, K_multiset_pair_ccm, prod_ccm in Link.
  destruct Link as [Link1 | Link2].
  lia.
  lia.
  all: apply K_multiset_pair_ccm.
Qed.

Lemma globalinv_root_inr : ∀ I Ir root k,
    globalinv root I ∧ Ir ≼ I ∧ domm Ir = {[root]} ∧ k ∈ KS
    → k ∈ inset Ir root ∨ k ∈ linkset Ir root.
Proof.
  intros I Ir root k ((Hv & _ & _ & Hl & _) & [I2 Hincl] & Hdom & kKS).
  right. specialize (Hl k kKS). destruct Hl.
  apply (linkset_monotone I Ir I2 k root); try done.
  set_solver.
Qed.

End linkset_flows.

Arguments linkset_flowint_ur _ {_ _} : assert.
Arguments inset _ {_ _} _ _ : assert.
Arguments linkset _ {_ _} _ _ : assert.
Arguments outset _ {_ _} _ _ : assert.
Arguments keyset _ {_ _} _ _ : assert.
Arguments in_inset _ {_ _} _ _ _ : assert.
Arguments in_linkset _ {_ _} _ _ _ : assert.
Arguments in_outset _ {_ _} _ _ _ : assert.
Arguments in_outsets _ {_ _} _ _ : assert.
Arguments globalinv _ {_ _} _ _ : assert.
