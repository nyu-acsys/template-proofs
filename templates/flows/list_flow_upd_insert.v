Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
(* From Coq Require Import QArith Qcanon. *)
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export list_flow_upd.
Require Import Coq.Setoids.Setoid.

Section list_flow_upd_insert.
  Open Scope ccm_scope.
  
  Definition f_decr := λ (k x: nat), x-1.
  
  Definition list_flow_upd_insert n0 Nx Mk S I :=
    list_flow_upd f_decr n0 Nx Mk S I.

  Lemma list_flow_upd_insert_invariants Key n R Nx Mk S I I' II' nk n0 In0:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (∀ x, x ∈ dom I → Mk !!! x = true → keyset (FI I x) = ∅) →
    (∀ n1 n2, Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) →
    (∀ n1 n2, n1 ∈ dom I' → Nx !! n1 = Some n2 → 
      dom (out_map (FI I' n1)) = {[n2]}) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n0 ∈ dom I') → (n ∈ dom I') → (n0 ≠ n) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) →
    (FI I' n0 = In0) →
    (FI I' n = inflow_delete_set (FI I n) n S) →
    (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' ∖ {[n]} → Nx !! x ≠ None) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → FI I' x = 
      outflow_delete_set (inflow_delete_set (FI I x) x S) (Nx !!! x) S) →
    (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) →
    (∀ k, k ∈ S → inf (FI I n) n !!! k = 1) →
    (∀ x k, x ∈ dom I → inf (FI I x) x !!! k ≤ 1) → 
    (∀ x k, x ∈ dom I → out (FI I x) (Nx !!! x) !!! k ≤ 1) →
    (∃ k, k ∈ inset _ (FI I n) n ∧ k ∉ S) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → keyset (FI I' x) = keyset (FI I x)) →
    ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
    list_flow_upd_rec f_decr n R Nx Mk S I I' = Some (II', nk) →
          ((dom II' ⊆ dom I)
        ∧ (n0 ≠ nk)
        ∧ (n0 ∈ dom II')
        ∧ (nk ∈ dom II')
        ∧ (Mk !! nk = Some false)
        ∧ (∀ x, x ∈ dom II' ∖ {[nk]} → Nx !! x ≠ None)
        ∧ (∀ x, x ∈ dom II' → dom (FI II' x) = {[x]})
        ∧ (([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x))
        ∧ (FI II' n0 = In0)
        ∧ (FI II' nk = inflow_delete_set (FI I nk) nk S)
        ∧ (∀ x, x ∈ dom II' ∖ {[n0;nk]} → FI II' x = 
              outflow_delete_set (inflow_delete_set (FI I x) x S) (Nx !!! x) S)
        ∧ (keyset (FI II' nk) = keyset (FI I nk) ∖ S)
        ∧ (∀ x, x ∈ dom II' ∖ {[ n0; nk ]} → keyset (FI II' x) = keyset (FI I x))).
  Proof.
    intros FI. 
    intros Nx_key Hcl KS_mk Nx_dom Nx_dom0 VI Domm_I n0_in_I0 
        n_in_I0 n0_neq_n Key_I0 Key_n0 Def_I0_n0 Def_I0_n Dom_I0_in_I Nx_x 
        I0_x Domm_I0 Inf_S Inf_x Out_x Inset_k KS_I' Heq Hflow.
    repeat split.
    - by apply (list_flow_upd_dom Key f_decr n R Nx Mk S I I' II' nk).
    - by apply (list_flow_upd_neq Key f_decr n R Nx Mk S I I' II' nk).
    - by apply (list_flow_upd_n0_dom f_decr n R Nx Mk S I I' II' nk).
    - by apply (list_flow_upd_nk_dom f_decr n R Nx Mk S I I' II' nk).
    - by apply (list_flow_upd_Mk_nk f_decr n R Nx Mk S I I' II' nk).
    - by apply (list_flow_upd_Nx Key f_decr n R Nx Mk S I I' II' nk n0).
    - by apply (list_flow_upd_domm Key f_decr n R Nx Mk S I I' II' nk).
    - admit.
    - by apply (list_flow_upd_II'_n0 Key f_decr n R Nx Mk S I I' II' nk n0).
    - by apply (list_flow_upd_II'_nk f_decr n R Nx Mk S I I' II' nk).
    - by apply (list_flow_upd_II' f_decr n R Nx Mk S I I' II' nk n0).
    - admit.
    - admit.
  Admitted.

    
  Lemma insert_flow_updk_summary Key n0 Nx Mk S I res n1:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (∀ x, x ∈ dom I → Mk !!! x = true → keyset (FI I x) = ∅) →
    (∀ n1 n2, Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) →
    (Nx !! n0 = Some n1) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n0 ∈ dom I) →
    (∃ k, k ∈ outset _ (FI I n0) n1 ∧ k ∉ S) →
    (S ⊆ insets (FI I n0)) →
    (∀ x k, x ∈ dom I → inf (FI I x) x !!! k ≤ 1) →
    (∀ k, k ∈ S → out (FI I n0) n1 !!! k = 1) →
    (∀ x k, x ∈ dom I → out (FI I x) (Nx !!! x) !!! k ≤ 1) →
    list_flow_upd_insert n0 Nx Mk S I = res →
      ∃ II nk, 
        res = Some (II, nk)
      ∧ (dom II ⊆ dom I)
      ∧ (n0 ∈ dom II)
      ∧ (nk ∈ dom II)
      ∧ (Mk !! nk = Some false)
      ∧ (∀ x, x ∈ dom II ∖ {[nk]} → Nx !! x ≠ None)
      ∧ (∀ x, x ∈ dom II → dom (FI II x) = {[x]})
      ∧ (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x))
      ∧ (FI II n0 = outflow_delete_set (FI I n0) n1 S)
      ∧ (FI II nk = inflow_delete_set (FI I nk) nk S)
      ∧ (∀ x, x ∈ dom II ∖ {[ n0; nk ]} → FI II x = 
              outflow_delete_set (inflow_delete_set (FI I x) x S) (Nx !!! x) S)
      ∧ (keyset (FI II n0) = keyset (FI I n0) ∪ S)
      ∧ (keyset (FI II nk) = keyset (FI I nk) ∖ S)
      ∧ (∀ x, x ∈ dom II ∖ {[ n0; nk ]} → keyset (FI II x) = keyset (FI I x)).
  Proof.
    intros FI Nx_key Hcl KS_Mk Nx_dom Hnx_n0 VI Domm_I n0_in_I 
      Outset_k Insets_S Inf_x Outset_S Out_x Hflow.
    unfold list_flow_upd_insert, list_flow_upd in Hflow.
    rewrite Hnx_n0 in Hflow. 
    set In1 := inflow_delete_set (I !!! n1) n1 S.
    set In0 := outflow_delete_set (I !!! n0) n1 S.
    set I': gmap Node (multiset_flowint_ur nat) := {[n1 := In1; n0 := In0]}.
    rewrite -/In1 -/In0 -/I' in Hflow.
    assert (dom I' = {[n0; n1]}) as Dom_I' by set_solver.
    assert (n1 ∈ dom I') as n1_in_I' by set_solver.
    assert (n1 ∈ dom I) as n1_in_I.
    { destruct Hcl as [_ [_ Hcl]]. 
      by apply (Hcl n0). }
    assert (n0 ≠ n1) as n0_neq_n1.
    { pose proof Nx_key n0 n1 Hnx_n0. 
      destruct (decide (n0 = n1)) as [-> | ]; try done.
      lia. }
    assert (dom I = (dom I ∖ {[n0]}) ∪ dom I') as H'.
    { rewrite Dom_I'.
      assert ((dom I ∖ {[n0]}) ∪ {[n0; n1]} ⊆ dom I) as H'.
      { set_solver. }
      assert (dom I ⊆ (dom I ∖ {[n0]}) ∪ {[n0; n1]}) as H''.
      { clear -n0_in_I n1_in_I n0_neq_n1. intros x Hx. 
        destruct (decide (x = n0)); first by set_solver.
        destruct (decide (x = n1)); first by set_solver.
        by set_solver. }
      clear -H' H''; set_solver. }  
    assert ((dom I ∖ {[n0]}) ∩ dom I' = {[n1]}) as H''.
    { rewrite Dom_I'. set_solver. }
    assert (Key !!! n0 < Key !!! n1) as Key_n0_n1.
    { by apply Nx_key in Hnx_n0. }
    assert (∀ x : Node, x ∈ dom I' → Key !!! x ≤ Key !!! n1) as Key_I'.
    { rewrite Dom_I'. intros x; rewrite elem_of_union.
      intros [Hx | Hx].
      - assert (x = n0) as -> by set_solver. lia.
      - assert (x = n1) as -> by set_solver. try done. }
    
    pose proof list_flow_upd_rec_defined Key f_decr n1 (dom I ∖ {[n0]}) 
      Nx Mk S I I' Nx_key Hcl n1_in_I' H' H'' Key_I' as Hpose.
    clear H' H''.
    destruct (list_flow_upd_rec f_decr n1 (dom I ∖ {[n0]}) Nx Mk S I I') 
      as [ (II, nk) |] eqn: Hflow1; try done. clear Hpose.
    
    assert (n0 ∈ dom I') as n0_in_I'.
    { rewrite Dom_I'. clear; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) as Key_n0.
    { intros x. rewrite Dom_I'. rewrite elem_of_difference.
      rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2]; try done.
      assert (x = n1) as -> by set_solver. done. }
    assert (FI I' n1 = inflow_delete_set (FI I n1) n1 S) as Def_I'_n.
    { unfold FI. subst I'. rewrite lookup_total_insert; try done.  }    
    assert (dom I' ⊆ dom I) as Dom_I'_in_I.
    { rewrite Dom_I'; clear -n0_in_I n1_in_I; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n1]} → Nx !! x ≠ None) as Nx_x.
    { rewrite Dom_I'. intros x Hx. 
      assert (x = n0) as -> by (clear -Hx; set_solver).
      rewrite Hnx_n0. done. }
    assert (∀ x, x ∈ dom I' ∖ {[n0;n1]} → FI I' x = 
      outflow_delete_set (inflow_delete_set (FI I x) x S) (Nx !!! x) S) as I'_x.
    { rewrite Dom_I'. intros x Hx. clear -Hx; set_solver. }  
    assert (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) as Domm_I'.
    { intros x. rewrite Dom_I'. rewrite elem_of_union.
      unfold FI; subst I'. intros [Hx | Hx].
      - assert (x = n0) as -> by (clear -Hx; set_solver).
        rewrite lookup_total_insert_ne; try done.
        rewrite lookup_total_insert.
        subst In0. by apply Domm_I.
      - assert (x = n1) as -> by (clear -Hx; set_solver).
        rewrite lookup_total_insert.
        subst In1. rewrite flowint_inflow_delete_set_dom.
        rewrite Domm_I; try done. clear; set_solver. }
    assert (I' !!! n0 = In0) as Def_I'_n0.
    { subst I'. rewrite lookup_total_insert_ne; try done.
      rewrite lookup_total_insert; done. }      
    assert (✓ (I !!! n0 ⋅ I !!! n1)) as VI'.
    { assert ({[n0; n1]} ⊆ dom I) as Hsub.
      { clear -n1_in_I n0_in_I' Dom_I'_in_I. set_solver. }
      pose proof (flow_big_op_valid _ _ {[n0; n1]} Hsub VI) as VI'.
      rewrite big_opS_union in VI'.
      rewrite !big_opS_singleton in VI'.
      by unfold FI in VI'. clear -n0_neq_n1. set_solver. }
    assert (([^op set] x ∈ dom I', FI I x) = 
                ([^op set] x ∈ dom I', FI I' x)) as Heq.
    { rewrite Dom_I'. 
      rewrite !big_opS_union; [| (clear -n0_neq_n1; set_solver)..].
      rewrite !big_opS_singleton.
      rewrite /I'. unfold FI.
      rewrite lookup_total_insert_ne; try done.
      rewrite !lookup_total_insert.
      rewrite /In0 /In1. 
      apply (flowint_delete_eq _ _ _ _ n1 S); try done.
      - intros k Hk. unfold FI in Outset_S. rewrite Outset_S; try done.
      - rewrite Domm_I; set_solver.
      - rewrite Domm_I; clear -n0_in_I' Dom_I'_in_I; set_solver. }
    assert (insets In0 = insets (I !!! n0)) as H1'.
    { by rewrite outflow_delete_set_insets. }
    assert (dom (out_map In0) = dom (out_map (FI I n0))) as Domout_map.
    { rewrite /In0. unfold outflow_delete_set, outflow_map_set.
      simpl. apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero.
      unfold FI. rewrite (Nx_dom n0 n1 Hnx_n0).
      clear; set_solver.
      destruct Outset_k as [k H''].
      intros Hn. rewrite nzmap_eq in Hn.
      pose proof Hn k as Hn.
      rewrite nzmap_lookup_total_map_set_ne in Hn; last first.
      clear -H''; set_solver.
      unfold ccmunit, ccm_unit in Hn. simpl in Hn.
      unfold lift_unit in Hn.
      rewrite nzmap_lookup_empty in Hn.
      destruct H'' as [H'' _].
      unfold outset in H''. rewrite nzmap_elem_of_dom_total in H''.
      unfold FI in H''. clear -Hn H''; try done. }
    assert (outsets In0 = outsets (I !!! n0) ∖ S) as H1''.
    { unfold outsets.
      pose proof (Nx_dom n0 n1 Hnx_n0) as Nx_dom.
      unfold FI in Nx_dom. rewrite Domout_map.
      rewrite Nx_dom. apply leibniz_equiv. rewrite !big_opS_singleton.
      rewrite /In0. rewrite outflow_delete_set_outset; try done.
      unfold FI in Outset_S. intros k Hk.
      rewrite Outset_S; try done. }
    assert (S ⊆ insets (I !!! n1)) as Insets_S1.
    { intros k Hk. unfold insets. 
      rewrite (Domm_I n1 n1_in_I).
      rewrite big_opS_singleton.
      apply (flowint_inset_step (I !!! n0) (I !!! n1)); try done.
      - unfold FI in Domm_I. rewrite (Domm_I n1 n1_in_I).
        clear; set_solver.
      - unfold outset. rewrite nzmap_elem_of_dom_total; try done.
        rewrite Outset_S. unfold ccmunit, ccm_unit. simpl. 
        unfold nat_unit. clear; lia. done. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0; n1]} → 
      keyset (I' !!! x) = keyset (I !!! x)) as KS_I'.
    { rewrite Dom_I'. intros x Hx. clear -Hx; set_solver. }  

    assert (keyset In0 = keyset (I !!! n0) ∪ S) as KS_n0.
    { unfold keyset. rewrite H1' H1''. 
      apply set_eq_subseteq.
      assert (S ⊆ outsets (FI I n0)) as H'.
      { unfold outsets. rewrite (Nx_dom n0 n1 Hnx_n0).
        rewrite big_opS_singleton. intros k Hk.
        rewrite nzmap_elem_of_dom_total. 
        rewrite Outset_S; try done. } 
      clear -Insets_S H'. 
      split; try set_solver.
      intros x. rewrite !elem_of_difference.
      intros [Hx1 Hx2].
      apply not_and_r in Hx2.
      rewrite elem_of_union elem_of_difference.
      destruct Hx2 as [Hx2 | Hx2].
      - left; set_solver.
      - right; set_solver. }
    
    assert (∀ n1 n2, n1 ∈ dom I' → Nx !! n1 = Some n2 → 
      dom (out_map (FI I' n1)) = {[n2]})
      as Nx_dom'.
    { intros n' n'' Dom_n' Hnx_n'.
      rewrite Dom_I' in Dom_n'.
      rewrite elem_of_union in Dom_n'.
      rewrite /I' /FI. 
      destruct Dom_n' as [Dom_n' | Dom_n'].
      - assert (n' = n0) as -> by (clear -Dom_n'; set_solver).
        rewrite lookup_total_insert_ne.
        rewrite lookup_total_insert Domout_map.
        apply Nx_dom; try done. done.
      - assert (n' = n1) as -> by (clear -Dom_n'; set_solver).
        rewrite lookup_total_insert. rewrite /In1.
        rewrite inflow_map_set_out_eq.
        apply Nx_dom; try done. }

    assert (∀ k, k ∈ S → inf (FI I n1) n1 !!! k = 1) as Inf_n1.
    { intros k Hk. unfold insets in Insets_S1.
      unfold FI in Domm_I.
      rewrite (Domm_I n1 n1_in_I) in Insets_S1.
      rewrite big_opS_singleton in Insets_S1.
      apply Insets_S1 in Hk.
      unfold inset in Hk. rewrite nzmap_elem_of_dom_total in Hk.
      pose proof Inf_x n1 k n1_in_I as H'.
      unfold FI in H'. unfold FI.
      unfold ccmunit, ccm_unit in Hk.
      simpl in Hk. unfold nat_unit in Hk.
      set a := inf (I !!! n1) n1 !!! k.
      rewrite -/a in Hk H'. clear -Hk H'; lia. }
    assert (∃ k, k ∈ inset nat (I !!! n1) n1 ∧ k ∉ S) as Outset_k'.
    { destruct Outset_k as [k [H' H'']].  
      exists k; split; try done.
      apply (flowint_inset_step (I !!! n0) (I !!! n1)); try done.
      unfold FI in Domm_I. rewrite (Domm_I n1 n1_in_I).
      clear; set_solver. }
    
    
    pose proof list_flow_upd_insert_invariants Key n1 (dom I ∖ {[n0]}) Nx Mk S 
      I I' II nk n0 In0 Nx_key Hcl KS_Mk Nx_dom Nx_dom' VI Domm_I n0_in_I' 
      n1_in_I' n0_neq_n1 Key_I' Key_n0 Def_I'_n0 Def_I'_n Dom_I'_in_I Nx_x 
      I'_x Domm_I' Inf_n1 Inf_x Out_x Outset_k' KS_I' Heq Hflow1 
      as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 
            [HInv6 [HInv7 [HInv8 [HInv9 [HInv10 
            [HInv11 [HInv12 HInv13]]]]]]]]]]]].
    

    exists II, nk. repeat (split; try done).
    unfold FI at 1. by rewrite HInv9.
  Admitted.

End list_flow_upd_insert.
  
