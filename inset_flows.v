Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export flows ccm.

Section inset_flows.

Context `{Countable K}.
  
(** CCM of multisets over keys numbers *)
Definition K_multiset := nzmap K nat.

Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

Definition dom_ms (m : K_multiset) := nzmap_dom K nat m.

Canonical Structure inset_flowint_ur : ucmraT := flowintUR K_multiset.

Implicit Type I : inset_flowint_ur.

Definition inset I n := dom_ms (inf I n).

Definition outset I n := dom_ms (out I n).

Definition in_inset k I n := k ∈ dom_ms (inf I n).
  
Definition in_outset k I n := k ∈ dom_ms (out I n).

Definition keyset I n := dom_ms (inf I n) ∖ dom_ms (out I n).

Definition in_outsets k In := ∃ n, in_outset k In n.

Lemma keyset_def : ∀ k I_n n, k ∈ inset I_n n → ¬ in_outsets k I_n → k ∈ keyset I_n n.
Proof.
  intros ? ? ? k_in_inset k_not_in_outsets.
  unfold keyset.
  unfold inset in k_in_inset.
  unfold in_outsets in k_not_in_outsets.
  rewrite elem_of_difference.
  naive_solver.
Qed.

Definition globalinv root I :=
  ✓I
  ∧ (root ∈ domm I)
  ∧ (∀ k n, k ∉ outset I n) 
  ∧ ∀ n, ((n = root) → (∀ k, k ∈ inset I n))
         ∧ ((n ≠ root) → (∀ k, k ∉ inset I n)).  

Lemma flowint_step :
  ∀ I I1 I2 k n root,
    globalinv root I → I = I1 ⋅ I2 → k ∈ outset I1 n → n ∈ domm I2.
Proof.
  intros I I1 I2 k n r gInv dI kOut.
  unfold globalinv in gInv.
  destruct gInv as [vI [rI [cI globalInf]]].
  
  assert (domm I = domm I1 ∪ domm I2) as disj.
  eauto using intComp_dom.

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

End inset_flows.

Check inset_flowint_ur.

Arguments inset_flowint_ur _ {_ _} : assert.
Arguments inset _ {_ _} _ _ : assert.
Arguments outset _ {_ _} _ _ : assert.
Arguments keyset _ {_ _} _ _ : assert.
Arguments in_inset _ {_ _} _ _ _ : assert.
Arguments in_outset _ {_ _} _ _ _ : assert.
Arguments in_outsets _ {_ _} _ _ : assert.
Arguments globalinv _ {_ _} _ _ : assert.

