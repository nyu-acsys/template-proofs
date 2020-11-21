Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export flows ccm.

(** Flow interface cameras and auxiliary lemmas for inset flows
  (used in the give-up template proof). *)

Section inset_flows.

Context `{Countable K}.

(* Definition KS := @KS K _ _. *)

(** CCM of multisets over keys *)

Definition K_multiset := nzmap K nat.

Global Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

Definition dom_ms (m : K_multiset) := dom (gset K) m.

Global Canonical Structure inset_flowint_ur : ucmraT := flowintUR K_multiset.

Implicit Type I : inset_flowint_ur.

(** Insets, outsets, and keysets of flow interfaces *)

Definition inset I n := dom_ms (inf I n).

Definition outset I n := dom_ms (out I n).

Definition in_inset k I n := k ∈ dom_ms (inf I n).

Definition in_outset k I n := k ∈ dom_ms (out I n).

Definition in_outsets k In := ∃ n, in_outset k In n.

Definition keyset I n := dom_ms (inf I n) ∖ dom_ms (out I n).

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

Definition gmap_decrement (k: K) (m : gmap K nat) : gmap K nat := 
          if (1 <? m !!! k) then <[k := m !!! k - 1]> m
          else delete k m.

Lemma nzmap_decrement_wf (k: K) (m : gmap K nat) :
      nzmap_wf m → nzmap_wf (gmap_decrement k m).
Proof.
  unfold nzmap_wf, map_Forall. intros Hm.
  intros i x. destruct (decide (i = k)).
  - replace i. unfold gmap_decrement.
    destruct (1 <? m !!! k) eqn: Hmkt.
    + rewrite lookup_insert. intros H'; inversion H'.
      apply Nat.ltb_lt in Hmkt. 
      unfold ccmunit, ccm_unit. simpl.
      unfold nat_unit. lia.
    + rewrite lookup_delete.
      intros H'; inversion H'.
  - unfold gmap_decrement. destruct (1 <? m !!! k);
    [ rewrite lookup_insert_ne; try done | rewrite lookup_delete_ne];
    by pose proof Hm i x.       
Qed.


Definition nzmap_decrement (kt: K) (m : nzmap K nat) :=
      let (m, Hm) := m in
        NZMap (gmap_decrement kt m) (bool_decide_pack _ (nzmap_decrement_wf kt m 
    (bool_decide_unpack _ Hm))).

Definition nzmap_decrement_set (s: gset K) (m : nzmap K nat) : nzmap K nat :=
      let f := λ k m', nzmap_decrement k m' in
      set_fold f m s.

Definition nzmap_increment_set (s: gset K) (m : nzmap K nat) : nzmap K nat :=
      let f := λ k m', <<[ k := m ! k + 1 ]>>m' in
      set_fold f m s.

Lemma nzmap_lookup_total_increment_set_aux s m :
      ∀ kt, (kt ∈ s → nzmap_increment_set s m ! kt = m ! kt + 1)
          ∧ (kt ∉ s → nzmap_increment_set s m ! kt = m ! kt).
Proof.
    set (P := λ (m': nzmap K nat) (X: gset K),
                    ∀ x, (x ∈ X → m' ! x = m ! x + 1)
                         ∧ (x ∉ X → m' ! x = m ! x) ).
    apply (set_fold_ind_L P); try done.
    intros x X r Hx HP.
    unfold P in HP. unfold P.
    intros x'.
    destruct (decide (x' = x));
    split; intros Hx'.
    - rewrite e. by rewrite nzmap_lookup_total_insert.
    - assert (x ∈ X). set_solver. contradiction.
    - assert (x' ∈ X) as x'_in_X. set_solver.
      apply HP in x'_in_X.
      rewrite nzmap_lookup_total_insert_ne.
      done. done.
    - assert (x' ∉ X) as x'_nin_X. set_solver.
      apply HP in x'_nin_X.
      rewrite nzmap_lookup_total_insert_ne.
      done. done.
Qed.

Lemma nzmap_lookup_total_increment_set kt s m :
      kt ∈ s → nzmap_increment_set s m ! kt = m ! kt + 1.
Proof.
  apply nzmap_lookup_total_increment_set_aux.
Qed.

Lemma nzmap_lookup_total_increment_set_ne kt s m :
      kt ∉ s → nzmap_increment_set s m ! kt = m ! kt.
Proof.
  apply nzmap_lookup_total_increment_set_aux.
Qed.


Definition outflow_insert_set_K I (n: Node) (s: gset K) : inset_flowint_ur := 
           let I_out_n := (nzmap_increment_set s (out I n)) in
           let I'_out := (<<[n := I_out_n]>> (out_map I)) in
           (int {| infR := inf_map I ; outR := I'_out |}).



Definition outflow_delete_set_K I (n: Node) (s: gset K) : inset_flowint_ur := 
           let I_out_n := (nzmap_decrement_set s (out I n)) in
           let I'_out := (<<[n := I_out_n]>> (out_map I)) in
           (int {| infR := inf_map I ; outR := I'_out |}).

(* assumes: n ∈ domm I *)           
Definition inflow_insert_set_K I (n: Node) (s: gset K) : inset_flowint_ur := 
           let I_inf_n := (nzmap_increment_set s (inf I n)) in
           let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
           (int {| infR := I'_inf ; outR := out_map I |}).

(* assumes: n ∈ domm I *)
Definition inflow_delete_set_K I (n: Node) (s: gset K) : inset_flowint_ur := 
           let I_inf_n := (nzmap_decrement_set s (inf I n)) in
           let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
           (int {| infR := I'_inf ; outR := out_map I |}).

Lemma flowint_insert_set_eq_K (I1 I1' I2 I2': inset_flowint_ur) n S :
  I1' = outflow_insert_set_K I1 n S →
  I2' = inflow_insert_set_K I2 n S →
  I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
Admitted.

Lemma flowint_inflow_insert_set_dom_K (I: inset_flowint_ur) n S I':
    I' = inflow_insert_set_K I n S
    → domm I' = domm I ∪ {[n]}.
Proof.
  
Admitted.

Lemma outflow_insert_set_outset_K I n S I' :
      I' = outflow_insert_set_K I n S → 
           outset I' n = (outset I n) ∪ S.
Proof.
    intros Heq. unfold outset.
  unfold inset_flows.dom_ms.
  replace I'. unfold outflow_insert_set_K.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert.
  apply leibniz_equiv.
  apply elem_of_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - set_solver.
  - rewrite nzmap_lookup_total_increment_set.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    unfold ccmunit, ccm_unit. simpl.
    unfold nat_unit. lia. done.
  - rewrite nzmap_lookup_total_increment_set_ne.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    intro.
    left.
    trivial. trivial.
  - rewrite elem_of_union.
    intro.
    destruct H0.
    rewrite nzmap_lookup_total_increment_set_ne.
    rewrite nzmap_elem_of_dom_total in H0 *.
    trivial. trivial.
    contradiction.
Qed.

Lemma outflow_insert_set_outset_ne_K I n S I' n' :
      n' ≠ n → I' = outflow_insert_set_K I n S → 
           outset I' n' = outset I n'.
Proof.
  intros Hneq Heq. unfold outset.
  unfold inset_flows.dom_ms.
  replace I'. unfold outflow_insert_set_K.
  unfold out. simpl.
  apply leibniz_equiv.
  apply elem_of_equiv. intros x.
  rewrite !nzmap_elem_of_dom_total.
  rewrite nzmap_lookup_total_insert_ne.
  trivial. auto.
Qed.


Lemma inflow_insert_set_outset_ne_K I n S I' n' :
      I' = inflow_insert_set_K I n S → 
           outset I' n' = outset I n'.
Proof.
  intros Heq.
  rewrite Heq.
  unfold inflow_insert_set_K.
  unfold outset.
  unfold inf.
  simpl.
  trivial.
Qed.

Lemma outflow_insert_set_inset_K I n S I' n' :
      I' = outflow_insert_set_K I n S → 
          inset I' n' = inset I n'.
Proof.
  intros Heq.
  rewrite Heq.
  unfold outflow_insert_set_K.
  unfold inset.
  unfold inf.
  simpl.
  trivial.
Qed.

Lemma inflow_insert_set_inset_ne_K I n S I' n' :
      n' ≠ n → I' = inflow_insert_set_K I n S → 
           inset I' n' = inset I n'.
Proof.
Admitted.

Lemma nzmap_lookup_total_increment_set_aux s m :
      ∀ kt, (kt ∈ s → nzmap_increment_set s m ! kt = m ! kt + 1)
          ∧ (kt ∉ s → nzmap_increment_set s m ! kt = m ! kt).
Proof.
Admitted.  

Lemma nzmap_lookup_total_increment_set kt s m :
      kt ∈ s → nzmap_increment_set s m ! kt = m ! kt + 1.
Proof.
Admitted.

Lemma nzmap_lookup_total_increment_set_ne kt s m :
      kt ∉ s → nzmap_increment_set s m ! kt = m ! kt.
Proof.
Admitted.


Lemma nzmap_lookup_total_decrement_set kt s m :
      kt ∈ s → nzmap_decrement_set s m ! kt = m ! kt - 1.
Proof.
Admitted.

Lemma nzmap_lookup_total_decrement_set_ne kt s m :
      kt ∉ s → nzmap_decrement_set s m ! kt = m ! kt.
Proof.
Admitted.

Lemma inflow_insert_set_out_eq_K I n S I' n' :
      I' = inflow_insert_set_K I n S →
          out I' n' = out I n'.
Proof.
Admitted.



(*
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
  ∧ (∀ k, k ∈ KS → k ∈ inset I root).

(** Assorted lemmas about inset flows used in the template proofs *)

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
  rewrite nzmap_elem_of_dom_total in kOut *.
  intros.
  unfold ccmunit, ccm_unit, K_multiset_ccm, lift_ccm, lift_unit in H0.
  rewrite H0 in H1.
  rewrite nzmap_lookup_empty in H1.
  contradiction.
    
  (* Now, prove n ∈ domm I *)    
  assert (n ∈ domm (I1 ⋅ I2)) as in_Inf_n.
  pose proof (intComp_unfold_out I1 I2 vI n).
  destruct (decide (n ∉ domm (I1 ⋅ I2))).
  apply H0 in n1.
  pose proof (cI k n) as not_k_out.
  unfold outset, dom_ms in not_k_out.
  rewrite nzmap_elem_of_dom_total in not_k_out *.
  intros not_k_out.
  apply dec_stable in not_k_out.
  unfold outset, dom_ms in kOut.
  rewrite nzmap_elem_of_dom_total in kOut *.
  intros kOut.
  assert (out I n ! k = out (I1 ⋅ I2) n ! k).
  rewrite dI. reflexivity.
  rewrite n1 in H1.
  rewrite lookup_op in H1.
  unfold ccmop, ccm_op in H1.
  unfold K_multiset_ccm,ccmunit,ccm_unit,nat_ccm,nat_unit,nat_op in kOut, not_k_out, H1.
  lia.
  apply dec_stable in n1. trivial.
    
  (* Finally, prove n ∈ domm I2 *)
  apply intComp_dom in vI.
  rewrite vI in in_Inf_n.
  set_solver.
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
  rewrite nzmap_elem_of_dom_total in Out *.
  intros Out.
  destruct (decide (outR Ir ! n = ∅)).
  rewrite e in Out.
  rewrite nzmap_lookup_empty in Out.
  contradiction.
  rewrite <- nzmap_elem_of_dom_total in n0.
  unfold dom, nzmap_dom in n0.
  
  unfold domm, dom, flowint_dom, inf_map.
  rewrite dI.
  set_solver.
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

Lemma flowint_inset_step : ∀ I1 I2 k n,
    ✓ (I1 ⋅ I2) → n ∈ domm I2 → k ∈ outset I1 n → k ∈ inset I2 n.
Proof.
  intros ? ? ? ? I12V Out Inset.

  pose proof (intComp_valid_proj1 I1 I2 I12V) as I1V.
  pose proof (intComp_valid_proj2 I1 I2 I12V) as I2V.
  apply flowint_valid_defined in I1V.
  destruct I1V as [I1r I1Def].
  apply flowint_valid_defined in I2V.
  destruct I2V as [I2r I2Def].
  pose proof (flowint_valid_defined _ _ I12V) as I12Def.
  destruct I12Def as [I12r I12Def].

  pose proof (intComp_unfold_inf_2 I1 I2 I12V n Out) as Inf2.

  unfold outset in Inset.
  unfold inset, dom_ms.
  rewrite Inf2.
  unfold out, out_map.
  rewrite I1Def.
  repeat rewrite nzmap_elem_of_dom_total.
  repeat rewrite lookup_op.

  unfold dom_ms, out, out_map in Inset.
  rewrite I1Def in Inset.
  repeat (rewrite nzmap_elem_of_dom_total in Inset *; intros Inset).
  unfold ccmop, ccm_op, nat_ccm, nat_op.
  unfold ccmop, ccm_op, nat_ccm, nat_op in Inset.
  unfold ccmunit, ccm_unit, nat_unit, K_multiset_ccm, prod_ccm.
  unfold ccmunit, ccm_unit, nat_unit, K_multiset_ccm, prod_ccm in Inset.
  lia.
Qed.

Lemma contextualLeq_impl_globalinv : ∀ I I' root,
    globalinv root I →
    contextualLeq K_multiset I I' →
    (∀ n, n ∈ domm I' ∖ domm I → inset I' n = ∅) →
    globalinv root I'.
Proof.
  intros ? ? ? GI CLeq InfI'.
  unfold contextualLeq in CLeq.
  unfold globalinv in GI.
  destruct GI as (_ & DomR & OutI & InfI).
  destruct CLeq as (VI & VI' & DS & InfR & OutR).
  unfold globalinv.
  repeat split.
  - trivial.
  - set_solver.
  - intros.
    destruct (decide (n ∈ domm I')).
    * apply flowint_valid_unfold in VI'.
      destruct VI' as [Ir' (I'_def & I'_disj & _)].
      rewrite (@map_disjoint_dom Node (gmap Node) (gset Node)) in I'_disj *.
      intros.
      assert (out_map I' ! n = 0%CCM).
      { unfold out_map. rewrite I'_def.
        assert (¬ (n ∈ dom (gset Node) (out_map I'))).
        { unfold domm, dom, flowint_dom in e.
          set_solver.
        }
        rewrite I'_def in H1.
        rewrite nzmap_elem_of_dom_total in H1 *.
        intros.
        apply dec_stable in H1.
        unfold out_map in H1.
        by rewrite H1.
      }
      unfold outset, dom_ms, nzmap_dom, out.
      rewrite H1. simpl.
      rewrite dom_empty.
      apply not_elem_of_empty.
    * assert (n ∉ domm I) by set_solver.
      pose proof (OutR n n0).
      unfold outset. rewrite <- H1.
      pose proof (OutI k n).
      unfold outset in H2.
      trivial.
  - intros.
    (*destruct H2 as (H2 & _).*)
    specialize (InfI k).
    (*rewrite <- H0 in DomR.*)
    specialize (InfR root DomR).
    unfold inset.
    unfold inset in InfR.
    rewrite <- InfR.
    apply InfI in H0.
    trivial.
Qed.

Lemma globalinv_root_ins : ∀ I Ir root k,
    globalinv root I ∧ Ir ≼ I ∧ domm Ir = {[root]} ∧ k ∈ KS
    → k ∈ inset Ir root.
Proof.
  intros I Ir root k ((Hv & _ & _ & Hl) & [I2 Hincl] & Hdom & kKS).
  specialize (Hl k kKS). 
  apply (inset_monotone I Ir I2 k root); try done.
  set_solver.
Qed.

Lemma intComp_out_zero I1 I2 n : 
        ✓ (I1 ⋅ I2) → n ∉ domm (I1 ⋅ I2) → out (I1 ⋅ I2) n = 0%CCM → out I2 n = 0%CCM.
Proof.
  intros Hvld Hn Hout. apply nzmap_eq. intros k.       
  assert (out (I1 ⋅ I2) n = (out (I1) n) + (out I2 n))%CCM.
  { apply intComp_unfold_out; try done. }
  assert (out (I1 ⋅ I2) n ! k = (out (I1) n) ! k + (out I2 n) ! k)%CCM.
  { rewrite H0. by rewrite lookup_op. }
  rewrite Hout in H1. rewrite nzmap_lookup_empty in H1.
  unfold ccmunit,ccm_unit in H1. simpl in H1.
  unfold nat_unit in H1. unfold ccmop, nat_op in H1.
  assert (out I2 n ! k = 0). lia.
  rewrite H2. rewrite nzmap_lookup_empty. unfold ccmunit, ccm_unit. 
  simpl. by unfold nat_unit.
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
(*Arguments globalinv _ {_ _} _ _ : assert.*)
