Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export flows ccm.

Section linkset_flows.

Context `{Countable K}.
  
(** CCM of multisets over keys numbers *)
Definition K_multiset := nzmap K nat.

Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

Definition dom_ms (m : K_multiset) := nzmap_dom K nat m.

Instance K_multiset_pair_ccm : CCM (K_multiset * K_multiset) :=
  prod_ccm K_multiset K_multiset.

Canonical Structure linkset_flowint_ur : ucmraT := flowintUR (K_multiset * K_multiset).

Implicit Type I : linkset_flowint_ur.

Definition inset I n := dom_ms (fst (inf I n)).

Definition linkset I n := dom_ms (snd (inf I n)).

Definition outset I n := dom_ms (fst (out I n)) ∪ dom_ms (snd (out I n)).

Definition in_inset k I n := k ∈ inset I n.
  
Definition in_linkset k I n := k ∈ linkset I n.

Definition in_outset k I n := k ∈ outset I n.

Definition keyset I n := inset I n ∖ outset I n.

Definition in_outsets k In := ∃ n, in_outset k In n.

Definition globalinv root I :=
  ✓I
  ∧ (root ∈ domm I)
  ∧ (∀ k n, k ∉ outset I n) 
  ∧ (∀ k, k ∈ inset I root ∧ k ∈ linkset I root)
  ∧ (forall n, (n ≠ root) → (∀ k, ¬(k ∈ inset I n ∧ k ∉ linkset I n))).

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
      exists p.
      trivial.

    - intros.
      rewrite H0 in Out.
      unfold default, dom_ms, nzmap_dom, ccmunit, lift_unit, nzmap_unit in Out.
      simpl in Out.
      rewrite dom_empty in Out *. intros Out.
      apply empty_union in Out.
      apply elem_of_empty in Out.
      contradiction.
      split.
      all: reflexivity.

  * case_eq (infR Ir !! n).
    - intros.
      unfold is_Some in H0.
      destruct H0.
      pose proof (disj n p x H1 H0).
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

Lemma flowint_step :
  ∀ I I1 I2 k n root,
    globalinv root I → I = I1 ⋅ I2 → k ∈ outset I1 n → n ∈ domm I2.
Proof.
  intros I I1 I2 k n r gInv dI kOut.
  unfold globalinv in gInv.
  destruct gInv as [vI [rI [cI globalInf]]].
  
  assert (domm I = domm I1 ∪ domm I2) as disj.
  rewrite dI in vI.
  pose proof (intComp_dom _ _ vI).
  rewrite dI.
  trivial.

  assert (✓ I1) as vI1.
  rewrite dI in vI.
  eauto using intComp_valid_proj1.

  assert (✓ I2) as vI2.
  rewrite dI in vI.
  eauto using intComp_valid_proj2.

  apply flowint_valid_unfold in vI1.
  destruct vI1 as [Ir1 [dI1 [disj1 _]]].
  apply flowint_valid_unfold in vI2.
  destruct vI2 as [Ir2 [dI2 [disj2 _]]].

  (* First, prove n ∉ domm I1 *)
  assert (n ∈ dom (gset Node) (outR Ir1)) as inOut1n.
  apply elem_of_dom.

  unfold outset, dom_ms, nzmap_dom in kOut.
  rewrite elem_of_union in kOut *.
  intros kOut.
  repeat (rewrite nzmap_elem_of_dom in kOut *; intros kOut).
   
  unfold out, out_map in kOut.
  rewrite dI1 in kOut.
  destruct (outR Ir1 !! n); eauto.
  unfold default in kOut.
  rewrite lift_lookup_empty in kOut.
  unfold is_Some in kOut.
  destruct kOut as [[x H0] | [x H0]].
  all: try inversion H0.

  assert (dom (gset Node) (infR Ir1) ## dom (gset Node) (outR Ir1)) as domDisj1.
  by apply map_disjoint_dom.

  assert (n ∉ dom (gset Node) (infR Ir1)) as not_in_Inf1_n.
  set_solver.

  (* Now, prove n ∈ domm I *)
  assert (n ∈ domm I) as in_Inf_n. 
  rewrite dI in vI.
  pose proof (intComp_unfold_out I1 I2 vI n).
  destruct (decide (n ∉ domm (I1 ⋅ I2))).
  apply H0 in n0.
  pose proof (cI k n) as not_k_out.
  unfold outset, dom_ms in not_k_out.
  rewrite not_elem_of_union in not_k_out *.
  intros not_k_out.
  unfold op, cmra_op, ucmra_cmraR, ucmra_op, linkset_flowint_ur, flowintUR in dI.
  unfold op in n0.
  rewrite <- dI in n0.
  rewrite n0 in not_k_out.
  repeat (rewrite nzmap_elem_of_dom_total in not_k_out *;
  intro not_k_out).
  unfold ccmop, ccm_op, K_multiset_pair_ccm, K_multiset_ccm, prod_ccm, prod_op in not_k_out.
  simpl in not_k_out.
  repeat rewrite lookup_op in not_k_out.
  unfold outset, dom_ms in kOut.
  rewrite elem_of_union in kOut *.
  intros kOut.
  repeat (rewrite nzmap_elem_of_dom_total in kOut *; intros kOut).
  remember (nzmap_total_lookup K nat k (out I1 n).1) as x1.
  remember (nzmap_total_lookup K nat k (out I1 n).2) as x2.
  unfold ccmop, ccm_op, nat_ccm, nat_op, ccmunit, nat_unit in not_k_out.
  destruct not_k_out as (not_k_out1 & not_k_out2).
  apply dec_stable in not_k_out1.
  apply dec_stable in not_k_out2.
  destruct kOut as [kOut | kOut]; unfold ccmunit, ccm_unit, nat_ccm, nat_unit in kOut; lia.
  
  rewrite dI.
  apply dec_stable in n0.
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

End linkset_flows.