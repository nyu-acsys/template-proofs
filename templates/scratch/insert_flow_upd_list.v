Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
(* From Coq Require Import QArith Qcanon. *)
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

Section insert_flow_upd.
  Open Scope ccm_scope.        

  Function insert_flow_upd_rec (n: Node) (R: gset Node)
    (Nx: gmap Node Node) (Mk : gmap Node bool) (S: gset nat)
    (I: gmap Node (multiset_flowint_ur nat))
    (I': gmap Node (multiset_flowint_ur nat))
    {measure size R} : option (gmap Node (multiset_flowint_ur nat) * Node) :=
  match (bool_decide (n ∈ R)) with
  | false => None
  | true =>
    match Mk !! n with
    | None => None
    | Some true =>
      match Nx !! n with
      | None => None
      | Some n1 =>
        (* Have to pick from I' because n's inflow is already updated *)
        let In := I' !!! n in
        (* Add S to outf(In, n1) *)
        let In' := outflow_delete_set In n1 S in
        (* Pick from I because n1 must be untouched so far *)
        let In1 := I !!! n1 in
        (* Add S to inf(In1, n1) *)
        let In1' := inflow_delete_set In1 n1 S in
        let II := <[n := In']> I' in
        let II' := <[n1 := In1']> II in  
        insert_flow_upd_rec n1 (R ∖ {[n]}) Nx Mk S I II' end
    | Some false => Some (I', n) end end.
  intros n R Nx Mk S I I' Hbool. intros.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.

  Definition insert_flow_upd n0 Nx Mk S I :=
    match Nx !! n0 with
    | None => None
    | Some n1 =>
      let In0 := I !!! n0 in
      let In0' := outflow_delete_set In0 n1 S in
      let In1 := I !!! n1 in
      let In1' := inflow_delete_set In1 n1 S in
      let I' := <[n1 := In1']> ({[n0 := In0']}) in
      insert_flow_upd_rec n1 (dom I ∖ {[n0]}) Nx Mk S I I' end.


  Definition nx_key_rel (Nx: gmap Node Node) (Key: gmap Node nat) :=
    ∀ n1 n2, Nx !! n1 = Some n2 → (Key !!! n1 < Key !!! n2). 

  Definition nx_mk_closed (Nx: gmap Node Node) (Mk: gmap Node bool)
    (N: gset Node) :=
      (dom Nx = N)
    ∧ (dom Mk = N)  
    ∧ (∀ n1 n2, Nx !! n1 = Some n2 → n2 ∈ N).

  Lemma insert_flow_upd_rec_defined Key n R Nx Mk S I I':
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (n ∈ dom I') →
    (dom I = R ∪ dom I') →
    (R ∩ dom I' = {[n]}) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
      insert_flow_upd_rec n R Nx Mk S I I' ≠ None.
  Proof.
(*  
    apply insert_flow_upd_rec_ind; try done.
    - clear n R Nx Mk S I I'. intros n R Nx Mk S I I' n_notin_R.
      rewrite bool_decide_eq_false in n_notin_R.
      intros _ _ _ _ ? _. set_solver.
    - clear n R Nx Mk S I I'. 
      intros n R Nx Mk S I I' n_in_R HMk_n Nx_key Hcl n_in_I' 
        Dom_I R_inter_I Key_I'.
      apply not_elem_of_dom_2 in HMk_n.
      destruct Hcl as (_&H'&_).
      set_solver.
    - clear n R Nx Mk S I I'. 
      intros n R Nx Mk S I I' n_in_R HMk_n Nx_n Nx_key Hcl n_in_I' 
        Dom_I R_inter_I Key_I'.
      apply not_elem_of_dom_2 in Nx_n.
      destruct Hcl as (H'&_).
      set_solver.
    - clear n R Nx Mk S I I'. 
      intros n R Nx Mk S I I0 n_in_R HMk_n.
      rewrite bool_decide_eq_true in n_in_R.
      intros n1 HNx_n In In' In1 In1' II I0' HInd Nx_key
        Hcl n_in_I0 Dom_I R_inter_I0 Key_I0.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 HNx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[n1]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct Hcl as [_ [_ Hcl]].
        by pose proof Hcl n n1 HNx_n as H'. }
      assert (n1 ∈ R) as n1_in_R.
      { rewrite Dom_I in n1_in_I. 
        clear -n1_notin_I0 n1_in_I. 
        set_solver. }
      apply HInd; try done.
      + rewrite Dom_I0'; clear; set_solver.
      + rewrite Dom_I Dom_I0'.
        clear -n_in_I0 n1_in_R R_inter_I0.
        assert (R ∖ {[n]} ∪ (dom I0 ∪ {[n1]}) ⊆ R ∪ dom I0) as H'.
        { set_solver. }
        assert (R ∪ dom I0 ⊆ R ∖ {[n]} ∪ (dom I0 ∪ {[n1]})) as H''.
        { intros x; rewrite elem_of_union.
          intros [Hx|Hx]; last first.
          - set_solver.
          - destruct (decide (x = n)) as [-> | Hxn]. 
            + set_solver.
            + set_solver. }
        clear -H' H''; set_solver.
      + rewrite Dom_I0'.
        clear -n1_in_R R_inter_I0 n1_notin_I0. set_solver. 
      + pose proof Nx_key n n1 HNx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia. 
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
*)
  Admitted.

  Lemma insert_flow_upd_invariants Key n R Nx Mk S I I' II' nk n0 In0:
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
    insert_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
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
    intros FI. apply insert_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key Hcl KS_mk Nx_dom Nx_dom0 VI Domm_I n0_in_I0 n_in_I0 n0_neq_n 
        Key_I0 Key_n0 Def_I0_n0 Def_I0_n Dom_I0_in_I Nx_x I0_x 
        Domm_I0 Inf_S Inf_x Out_x Inset_k KS_I' Heq [= -> ->].
      repeat (split; try done).
      rewrite Def_I0_n. unfold keyset.
      unfold insets.
      rewrite flowint_inflow_delete_set_dom.
      rewrite (Domm_I nk (Dom_I0_in_I _ n_in_I0)).
      assert ({[nk;nk]} = {[nk]}) as -> by (clear; set_solver).
      apply leibniz_equiv.
      rewrite !big_opS_singleton.
      rewrite inflow_delete_set_inset; last first.
      { intros k Hk; rewrite Inf_S; try done. } 
      rewrite inflow_delete_set_outsets.
      clear; set_solver.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key Hcl KS_mk Nx_dom Nx_dom0 VI Domm_I n0_in_I0 
        n_in_I0 n0_neq_n Key_I0 Key_n0 Def_I0_n0 Def_I0_n Dom_I0_in_I Nx_x 
        I0_x Domm_I0 Inf_S Inf_x Out_x Inset_k KS_I' Heq Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 Hnx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct Hcl as [_ [_ Hcl]].
        by pose proof Hcl n n1 Hnx_n as H'. }  
      assert (∀ x, x ∈ dom I0 → dom (FI (<[n:=In']> I0) x) = {[x]}) 
        as Domm_II.
      { intros x Hx. destruct (decide (n = x)) as [-> | Hxn].
        - unfold FI. rewrite lookup_total_insert.
          subst In'. rewrite flowint_outflow_map_set_domm.
          subst In. rewrite Domm_I0; try done.
        - unfold FI. rewrite lookup_total_insert_ne; try done.
          rewrite Domm_I0; try done. }
      assert (n0 ≠ n1) as n0_neq_n1.
      { clear -n0_in_I0 n1_notin_I0. set_solver. }
      assert (Mk !!! n = true) as Mk_n.
      { rewrite lookup_total_alt. by rewrite Hmk_n. }
      pose proof KS_mk n (Dom_I0_in_I _ n_in_I0) Mk_n as KS_n.
      assert (S ⊆ insets (FI I n)) as Insets_S.
      { intros k Hk. apply (inset_in_insets _ n).
        unfold inset. rewrite nzmap_elem_of_dom_total.
        rewrite Inf_S. unfold ccmunit, ccm_unit. simpl.
        unfold nat_unit. clear; lia. done. }
      assert (S ⊆ outsets (FI I n)) as Outsets_S.
      { unfold keyset in KS_n. 
        clear -KS_n Insets_S. set_solver. }
      assert (∃ k, k ∈ outset _ (FI I0 n) n1 ∧ k ∉ S) as Outset_k.
      { destruct Inset_k as [k [H1' H1'']].
        exists k. split; try done.
        rewrite Def_I0_n. unfold outset.
        rewrite nzmap_elem_of_dom_total.
        unfold inflow_delete_set, inflow_map_set.
        unfold out, out_map at 1. simpl.
        assert (k ∈ outset _ (FI I n) n1) as H'.
        { unfold keyset in KS_n.
          unfold insets, outsets in KS_n.
          rewrite (Domm_I n (Dom_I0_in_I _ n_in_I0)) in KS_n.
          rewrite (Nx_dom n n1 Hnx_n) in KS_n.
          apply leibniz_equiv_iff in KS_n.
          rewrite !big_opS_singleton in KS_n.
          clear -KS_n H1'. set_solver. }
        unfold outset in H'.
        rewrite nzmap_elem_of_dom_total in H'.
        by unfold out in H'. }
      assert (dom (out_map (In')) = dom (out_map (FI I n))) as Domout_In'.
      { rewrite /In'. unfold outflow_delete_set, outflow_map_set.
        simpl. apply leibniz_equiv. rewrite /In. 
        rewrite nzmap_dom_insert_nonzero.
        rewrite (Nx_dom0 n n1 n_in_I0 Hnx_n). rewrite (Nx_dom n n1 Hnx_n). 
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
        unfold FI in H''. try done. }
      assert (✓ (FI I n ⋅ FI I n1)) as VI'.
      { assert ({[n; n1]} ⊆ dom I) as Hsub.
        { clear -n1_in_I n_in_I0 Dom_I0_in_I. set_solver. }
        pose proof (flow_big_op_valid _ _ {[n; n1]} Hsub VI) as VI'.
        rewrite big_opS_union in VI'.
        by rewrite !big_opS_singleton in VI'.
        clear -n1_notin_I0 n_in_I0 Dom_I0_in_I. set_solver. }
      apply HInd; try done; clear HInd.
      { intros n' n'' Nx_n'. rewrite /I0' /FI.
        destruct (decide (n' = n1)) as [-> | Hn'].
        - rewrite lookup_total_insert. rewrite /In1'.
          assert (out_map (inflow_delete_set In1 n1 S) = out_map In1) as ->.
          { unfold inflow_delete_set, out_map; try done. }
          rewrite /In1. unfold FI in Nx_dom.
          by apply Nx_dom.
        - rewrite lookup_total_insert_ne; try done. rewrite /II.
          destruct (decide (n' = n)) as [-> | Hn''].
          + rewrite lookup_total_insert.
            rewrite Domout_In'. apply Nx_dom; try done.
          + rewrite lookup_total_insert_ne; try done.
            apply Nx_dom0; try done. rewrite Dom_I0' in Nx_n'.
            clear -Hn' Nx_n'; set_solver. }
      { rewrite Dom_I0'. clear -n0_in_I0.
        set_solver. }
      { rewrite Dom_I0'. clear -Dom_I0_in_I n1_in_I. set_solver. }
      { pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        - apply Key_I0 in Hx. clear -Hx H'. lia.
        - assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done. }
      { rewrite Dom_I0'. intros x. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        - apply Key_n0. clear -Hx1 Hx2; set_solver.
        - assert (x = n1) as -> by (clear -Hx1; set_solver). 
          pose proof Nx_key n n1 Hnx_n as H'.
          assert (Key !!! n0 ≤ Key !!! n) as H''.
          { by apply Key_I0. }
          clear -H' H''. lia. }
      { unfold FI; rewrite /I0'.
        rewrite lookup_total_insert_ne.
        rewrite /II. rewrite lookup_total_insert_ne; try done.
        clear -n0_neq_n1; naive_solver. }        
      { rewrite /I0' /FI. rewrite lookup_total_insert. 
        rewrite /In1'. by rewrite /In1. }
      { rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        - by apply Dom_I0_in_I.
        - assert (x = n1) as -> by (clear -Hx; set_solver).
          clear -n1_in_I; set_solver. }
      { intros x. rewrite Dom_I0'. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        - destruct (decide (x = n)) as [-> | Hxn].
          + by rewrite Hnx_n.
          + apply Nx_x. clear -Hx1 Hx2 Hxn; set_solver.
        - clear -Hx1 Hx2; set_solver. }    
      { intros x. rewrite Dom_I0'. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        - destruct (decide (x = n)) as [-> | Hxn].
          + unfold FI. subst I0'.
            rewrite lookup_total_insert_ne; 
              last by (clear -Hx2; set_solver).
            subst II. rewrite lookup_total_insert.
            subst In' In. unfold FI in Def_I0_n. rewrite Def_I0_n.
            assert (Nx !!! n = n1) as ->.
            { rewrite lookup_total_alt. rewrite Hnx_n. by simpl. }
            done.
          + unfold FI. subst I0'.
            rewrite lookup_total_insert_ne; 
              last by (clear -Hx2; set_solver).
            subst II. rewrite lookup_total_insert_ne; try done.
            apply I0_x. clear -Hx1 Hx2 Hxn; set_solver.
        - clear -Hx1 Hx2; set_solver. }
      { rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        - subst I0'. 
          assert (x ≠ n1) as H'.
          { clear -Hx n1_notin_I0. set_solver. }
          unfold FI.
          rewrite lookup_total_insert_ne; try done.
          subst II.
          apply Domm_II; try done.
        - assert (x = n1) as -> by (clear -Hx; set_solver).
          unfold FI. subst I0'.
          rewrite lookup_total_insert.
          subst In1'.
          rewrite flowint_inflow_map_set_dom.
          subst In1. rewrite Domm_I; try done.
          clear; set_solver. }
      { assert (∀ k, k ∈ S → k ∈ inset _ (FI I n1) n1) as H'.
        { intros k k_in_S. 
          apply (flowint_inset_step (FI I n) (FI I n1) k n1); try done.
          - rewrite Domm_I. clear; set_solver. done.
          - unfold outsets in Outsets_S. 
            rewrite (Nx_dom n n1 Hnx_n) in Outsets_S.
            rewrite big_opS_singleton in Outsets_S.
            apply Outsets_S; try done. }
        intros k Hk. pose proof H' k Hk as H'.
        unfold inset in H'. rewrite nzmap_elem_of_dom_total in H'.
        rewrite /ccmunit /= in H'. rewrite /nat_unit in H'.
        pose proof Inf_x n1 k n1_in_I as H''.
        clear -H' H''. 
        set a := inf (FI I n1) n1 !!! k.
        rewrite -/a in H' H''. lia. }
      { destruct Inset_k as [k [H1' H1'']].
        exists k. split; try done.
        rewrite /FI /I0'. 
        apply (flowint_inset_step (FI I n) (FI I n1) k n1); try done.
        rewrite Domm_I. clear; set_solver. done.
        unfold keyset in KS_n.
        unfold insets, outsets in KS_n.
        rewrite (Domm_I n (Dom_I0_in_I _ n_in_I0)) in KS_n.
        rewrite (Nx_dom n n1 Hnx_n) in KS_n.
        apply leibniz_equiv_iff in KS_n.
        rewrite !big_opS_singleton in KS_n.
        clear -KS_n H1'. set_solver. }
      { rewrite Dom_I0'. intros x; rewrite elem_of_difference. 
        rewrite elem_of_union. rewrite not_elem_of_union.
        intros [[Hx1 | Hx1] [Hx2 Hx3]].
        - destruct (decide (x = n)) as [-> | Hxn].
          + rewrite /FI /I0'. 
            rewrite lookup_total_insert_ne; last by (clear -Hx3; set_solver).
            rewrite /II. rewrite lookup_total_insert.
            unfold keyset.
            rewrite outflow_delete_set_insets.
            unfold outsets. rewrite Domout_In'. 
            unfold FI.
            rewrite (Nx_dom n n1 Hnx_n).
            apply leibniz_equiv.
            rewrite !big_opS_singleton.
            rewrite outflow_delete_set_outset.
            rewrite /In. unfold FI in Def_I0_n. 
            rewrite Def_I0_n.
            Search inflow_delete_set.
            unfold insets. 
            assert (dom (inflow_delete_set (I !!! n) n S) = dom (I !!! n)) as ->.
            { rewrite flowint_inflow_delete_set_dom.
              rewrite (Domm_I n (Dom_I0_in_I _ n_in_I0)).
              clear; set_solver. }
            rewrite (Domm_I n (Dom_I0_in_I _ n_in_I0)).
            rewrite !big_opS_singleton.
            assert (outset _ (inflow_delete_set (I !!! n) n S) n1 =
              outset _ (I !!! n) n1) as ->.
            { unfold inflow_delete_set, outset; try done. }
            rewrite inflow_delete_set_inset.
            unfold insets in Insets_S. 
            rewrite (Domm_I n (Dom_I0_in_I _ n_in_I0)) in Insets_S.
            rewrite big_opS_singleton in Insets_S.
            unfold FI in Insets_S.
            unfold outsets in Outsets_S. 
            rewrite (Nx_dom n n1 Hnx_n) in Outsets_S.
            rewrite big_opS_singleton in Outsets_S.
            unfold FI in Outsets_S.
            clear -Insets_S Outsets_S. set_solver.
            intros k Hk; apply Inf_x. apply Dom_I0_in_I; try done.
            rewrite /In. intros k Hk.
            unfold FI in Def_I0_n. rewrite Def_I0_n.
            assert (out (inflow_delete_set (I !!! n) n S) n1 = 
                      out (I !!! n) n1) as ->.
            { unfold out, out_map, inflow_delete_set; try done. }
            pose proof Out_x n k (Dom_I0_in_I _ n_in_I0) as H'.
            unfold FI in H'. rewrite (lookup_total_alt Nx) in H'.
            rewrite Hnx_n in H'. by simpl in H'.
          + rewrite /FI /I0'. 
            rewrite lookup_total_insert_ne; last by (clear -Hx3; set_solver). 
            rewrite /II. 
            rewrite lookup_total_insert_ne; last by (clear -Hxn; set_solver). 
            apply KS_I'. clear -Hx1 Hx2 Hxn; set_solver.
        - clear -Hx1 Hx3; try done. }
      { rewrite Dom_I0'. 
        rewrite !big_opS_union; [try done | set_solver | set_solver].
        rewrite !big_opS_singleton. 
        all: try (clear -n_notin_I0; set_solver).
        rewrite /I0'; rewrite /FI. rewrite lookup_total_insert.
        rewrite /II.
        assert (([^op set] y ∈ dom I0, FI (<[n1:=In1']> (<[n:=In']> I0)) y) = 
                  ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Def_II.
        { apply big_opS_ext. intros x Hx. unfold FI.
          rewrite lookup_total_insert_ne. done.
          clear -Hx n1_notin_I0. set_solver. }
        rewrite Def_II.
        assert (✓ ([^op set] y ∈ dom I0, FI I y)) as Valid_I.
        { apply (flow_big_op_valid _ (dom I)); try done. }
        assert (✓ ([^op set] y ∈ dom I0, FI I0 y)) as Valid_I0.
        { apply leibniz_equiv_iff in Heq. rewrite <-Heq. try done. }
        assert (✓ ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Valid_II.
        { assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) = 
                    ([^op set] y ∈ dom I0 ∖ {[n]}, FI I0 y) ⋅ In') as ->.
        { rewrite (big_opS_delete _ _ n); last done.
          unfold FI at 1. rewrite lookup_total_insert.
          rewrite intComp_comm.
          assert (([^op set] y ∈ (dom I0 ∖ {[n]}), FI (<[n:=In']> I0) y) = 
              ([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y)) as ->.
          { apply big_opS_ext. intros x Hx. unfold FI.
            rewrite lookup_total_insert_ne. done.
            clear -Hx; set_solver. }
          done. }

          apply (outflow_map_set_valid2
                        (([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y)) 
                        (I0 !!! n)  
                        (In')
                        (λ _ n, n - 1)%nat 
                        n1
                        S).
          - subst In'; try done.
          - intros Hn1. rewrite flow_big_op_dom in Hn1.
            destruct Hn1 as [x [Hx1 Hx2]].
            rewrite Domm_I0 in Hx2; last first.
            { clear -Hx1; set_solver. }
            assert (n1 = x) as <- by (clear -Hx2; set_solver).
            clear -n1_notin_I0 Hx1. set_solver.
            apply (flow_big_op_valid _ (dom I0)); try done.
            clear; set_solver.
          - rewrite Domm_I0; try done.
            assert (n1 ≠ n) as H'.
            { clear -n1_notin_I0 n_in_I0.
              set_solver. }
            clear -H'; set_solver.
          - intros H'. rewrite Domm_I0 in H'; try done.
            clear -H'; set_solver.
          - assert (([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y) ⋅ I0 !!! n =
                      ([^op set] y ∈ dom I0, FI I0 y)) as H'.
            { rewrite (big_opS_delete _ (dom I0) n); try done.
              unfold FI at 2. by rewrite intComp_comm. }
            by rewrite H'. }
        pose proof (flowint_delete_eq
                      ([^op set] y ∈ dom I0, I !!! y)
                      ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                      (I !!! n1)
                      In1' 
                      n1 
                      S) as Hpose.
        assert (n1 ∈ dom (FI I n1)) as n1_in_In1.
        { rewrite Domm_I; try done. clear; set_solver. }
        assert (flowint_dom ([^op set] y ∈ dom I0, I !!! y) ≠ ∅) as Domm_I0_notEmpty.
        { assert (n ∈ (flowint_dom ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
          { rewrite flow_big_op_dom; try done. exists n; split; try done.
            rewrite Domm_I; last first.
            { clear -n_in_I0 Dom_I0_in_I. set_solver. } 
            clear; set_solver. }
          clear -H'; set_solver. }
        assert (flowint_dom ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)) = 
                  flowint_dom ([^op set] y ∈ dom I0, (I !!! y))) as Domm_II_eq_I.
        { assert ((flowint_dom ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y))) ⊆ 
                      (flowint_dom ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
          { intros n'. rewrite !flow_big_op_dom; try done.
            intros [x [Hx1 Hx2]]. exists x. split; try done.
            rewrite Domm_II in Hx2; try done. rewrite Domm_I; try done.
            clear -Hx1 Dom_I0_in_I. set_solver. }
          assert ((flowint_dom ([^op set] y ∈ dom I0, (I !!! y))) ⊆ 
                    (flowint_dom ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)))) as H''.
          { intros n'. rewrite !flow_big_op_dom; try done.
            intros [x [Hx1 Hx2]]. exists x. split; try done.
            rewrite Domm_II. rewrite Domm_I in Hx2; try done.
            clear -Hx1 Dom_I0_in_I. set_solver. done. }
          clear -H' H''; set_solver. }
        assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) =
          outflow_delete_set ([^op set] y ∈ dom I0, I !!! y) n1 S) 
          as H0'.
        { apply intEq; try done. 
          - unfold dom. rewrite Domm_II_eq_I. try done. 
          - intros n'. unfold inf. rewrite outflow_map_set_inf.
            assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n'
              ≡ default 0 
                (inf_map ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) !! n'))
              as HL by try done.
            assert (inf ([^op set] y ∈ dom I0, FI I y) n'
              ≡ default 0 
                (inf_map ([^op set] y ∈ dom I0, I !!! y) !! n')) 
              as HR by try done.
            rewrite <-HL. rewrite <-HR.
            rewrite Heq.
            assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n' = 
                      inf ([^op set] y ∈ dom I0, FI I0 y) n') as HI0.
            { destruct (decide (n' ∈ 
                          dom ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
                as [Hn' | Hn'].
              - rewrite flow_big_op_dom in Hn'; try done.
                destruct Hn' as [n'' [n''_in_I0 n'_in_n'']].
                rewrite Domm_II in n'_in_n''; try done.
                assert (n' = n'') as <- by (clear -n'_in_n''; set_solver).
                rewrite (flow_big_op_inf _ _ n'); try done.
                + rewrite (flow_big_op_inf _ _ n'); try done.
                  * clear HL HR. 
                    assert (([^+ set] x ∈ (dom I0 ∖ {[n']}), 
                              out (FI (<[n:=In']> I0) x) n')
                            = ([^+ set] x ∈ (dom I0 ∖ {[n']}), 
                              out (FI I0 x) n')) as Hout.
                    { destruct (decide (n' = n)) as [-> | Hn'].
                      - apply ccm_big_opS_ext. intros x Hx.
                        unfold FI. rewrite lookup_total_insert_ne. done.
                        clear -Hx; set_solver.  
                      - assert (out (FI (<[n := In']> I0) n) n' 
                                  = out (FI I0 n) n') as H'.
                        { rewrite /FI. rewrite lookup_total_insert.
                          rewrite /In' /In.
                          assert (n' ≠ n1). 
                          { clear -n''_in_I0 n1_notin_I0. set_solver. }
                          unfold out. 
                          rewrite outflow_map_set_out_map_ne; try done. }
                        apply ccm_big_opS_ext. intros x Hx. unfold FI. 
                        destruct (decide (x = n)) as [-> | Hxn]; try done.
                        rewrite lookup_total_insert_ne; try done. }
                    assert (inf (FI (<[n:=In']> I0) n') n' 
                              = inf (FI I0 n') n') as Hin.
                    { destruct (decide (n' = n)) as [-> | Hn'].
                      - rewrite /FI. rewrite lookup_total_insert. 
                        subst In'. unfold inf. 
                        rewrite outflow_map_set_inf. by subst In.
                      - rewrite /FI. 
                        rewrite lookup_total_insert_ne; try done. }
                    by rewrite Hin Hout.
                  * rewrite Domm_I0; try done.
                + rewrite Domm_II; try done.
              - assert (n' ∉ dom ([^op set] y ∈ dom I0, FI I0 y)) as Hn''.
                { unfold dom in Hn'. rewrite Domm_II_eq_I in Hn'.
                  intros Hn''. rewrite flow_big_op_dom in Hn''; try done.
                  destruct Hn'' as [x0 [Hx0 Hx00]].
                  apply Hn'. rewrite flow_big_op_dom; try done.
                  exists x0. split; try done.
                  rewrite (Domm_I0 x0 Hx0) in Hx00.
                  apply Dom_I0_in_I in Hx0.
                  unfold FI in Domm_I.
                  by rewrite (Domm_I x0 Hx0). }
                unfold dom, flowint_dom in Hn''. 
                unfold dom, flowint_dom in Hn'.
                rewrite not_elem_of_dom in Hn'.
                rewrite not_elem_of_dom in Hn''.
                unfold inf. rewrite Hn' Hn''. by simpl. }
            by rewrite HI0.
          - rewrite Heq. intros n'.
            destruct (decide (n' ∈ 
                dom ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
                as [Hn' | Hn'].
            + rewrite intValid_in_dom_not_out; try done.
              rewrite intValid_in_dom_not_out; try done.
              apply outflow_map_set_valid; try done.
              intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
              destruct Hn1 as [x0 [Hx0 Hx00]].
              rewrite (Domm_I0 x0 Hx0) in Hx00.
              clear -Hx0 Hx00 n1_notin_I0. set_solver.
              assert (n ∈ dom ([^op set] x ∈ dom I0, FI I0 x)) as H'.
              { rewrite flow_big_op_dom; try done. exists n.
                rewrite (Domm_I0 n n_in_I0). split; try done.
                clear; set_solver. } clear -H'; set_solver.
              rewrite flowint_outflow_map_set_domm. 
              rewrite flow_big_op_dom; try done.
              rewrite flow_big_op_dom in Hn'; try done.
              destruct Hn' as [x0 [Hx0 Hx00]].
              destruct (decide (x0 = n)) as [-> | Hxn].
              * unfold FI in Hx00. rewrite lookup_total_insert in Hx00.
                rewrite /In' in Hx00.
                rewrite flowint_outflow_map_set_domm in Hx00.
                rewrite /In in Hx00.
                exists n; split; try done.
              * unfold FI in Hx00. 
                rewrite lookup_total_insert_ne in Hx00; try done.
                exists x0; split; try done.
            + destruct (decide (n' = n1)) as [-> | Hn1'].
              * apply nzmap_eq. intros k'. 
                destruct (decide (k' ∈ S)) as [Hk' | Hk'].
                ** rewrite outflow_lookup_total_map_set; try done.
                   rewrite !flow_big_op_out.
                   { rewrite (ccm_big_opS_delete _ _ n); try done.
                     rewrite (ccm_big_opS_delete _ (dom I0) n); try done.
                     unfold ccmop, ccm_op. simpl.
                     rewrite !lookup_total_lifting.
                     unfold ccmop, ccm_op. simpl. unfold nat_op.
                     unfold FI at 1. rewrite lookup_total_insert.
                     rewrite {1}/In'. rewrite outflow_lookup_total_map_set.
                     assert (([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI (<[n:=In']> I0) y) n1) =
                             ([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI I0 y) n1)) as ->.
                     { apply ccm_big_opS_ext. intros x Hx. unfold FI. 
                       rewrite lookup_total_insert_ne; try done.
                       clear -Hx; set_solver. }
                     rewrite /In /FI.
                     set a := out (I0 !!! n) n1 !!! k'.
                     set b := ([^+ set] y ∈ (dom I0 ∖ {[n]}), out (I0 !!! y) n1) 
                                                                          !!! k'.
                     assert (1 ≤ a) as H'.
                     { rewrite /a. apply Outsets_S in Hk'. 
                       unfold outsets in Hk'. unfold FI in Def_I0_n. 
                       rewrite Def_I0_n. unfold out. 
                       rewrite inflow_map_set_out_eq.
                       rewrite (Nx_dom n n1 Hnx_n) in Hk'.
                       rewrite big_opS_singleton in Hk'.
                       unfold outset in Hk'. 
                       rewrite nzmap_elem_of_dom_total in Hk'.
                       unfold out, FI, ccmunit, ccm_unit in Hk'.
                       simpl in Hk'. unfold nat_unit in Hk'. 
                       set c := (out_map (I !!! n) !!! n1) !!! k'.
                       rewrite -/c in Hk'.
                       clear -Hk'; lia. }
                     clear -H'; lia. done. }
                   { apply leibniz_equiv_iff in Heq. 
                     rewrite <-Heq. try done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_I0 in Hx2; try done.
                     assert (n1 = x) as -> by (clear -Hx2; set_solver).
                     clear -Hx1 n1_notin_I0. try done. }
                   { try done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_II in Hx2; try done.
                     assert (n1 = x) as -> by (clear -Hx2; set_solver).
                     clear -Hx1 n1_notin_I0. try done. }
                ** rewrite outflow_lookup_total_map_set_ne; try done.
                   rewrite !flow_big_op_out; try done.
                   { rewrite (ccm_big_opS_delete _ _ n); try done.
                     rewrite (ccm_big_opS_delete _ (dom I0) n); try done.
                     unfold ccmop, ccm_op. simpl.
                     rewrite !lookup_total_lifting.
                     unfold FI at 1. rewrite lookup_total_insert.
                     rewrite {1}/In'. 
                     rewrite outflow_lookup_total_map_set_ne; try done.
                     assert (([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI (<[n:=In']> I0) y) n1) = 
                             ([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI I0 y) n1)) as ->.
                     { apply ccm_big_opS_ext. intros x Hx. unfold FI. 
                       rewrite lookup_total_insert_ne; try done.
                       clear -Hx; set_solver. }
                     by rewrite ccm_comm. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_I0 in Hx2; try done.
                     assert (n1 = x) as -> by (clear -Hx2; set_solver).
                     clear -Hx1 n1_notin_I0. try done. }
              * unfold out at 2.
                rewrite outflow_map_set_out_map_ne; try done.
                fold (out ([^op set] x ∈ dom I0, FI I0 x) n').
                rewrite !flow_big_op_out; try done; last first.
                { intros Hn2'. rewrite flow_big_op_dom in Hn2'; try done. 
                  destruct Hn2' as [x0 [Hx0 Hx00]].
                  apply Hn'. apply flow_big_op_dom; try done.
                  rewrite (Domm_I0 x0 Hx0) in Hx00.
                  assert (n' = x0) as -> by (clear -Hx00; set_solver).
                  exists x0. unfold FI. destruct (decide (x0 = n)) as [-> | Hx0n].
                  - rewrite lookup_total_insert. rewrite /In'.
                    rewrite flowint_outflow_map_set_domm. rewrite /In.
                    rewrite (Domm_I0 n n_in_I0). split; try done.
                  - rewrite lookup_total_insert_ne; try done.
                    rewrite (Domm_I0 x0 Hx0). split; try done. }
                apply ccm_big_opS_ext. intros x Hx.
                destruct (decide (x = n)) as [-> | Hxn].
                ** unfold FI. rewrite lookup_total_insert.
                   rewrite /In'. unfold out.
                   by rewrite outflow_map_set_out_map_ne.
                ** unfold FI. rewrite lookup_total_insert_ne; try done. }
        assert (In1' = inflow_delete_set (I !!! n1) n1 S) as H0''.
        { rewrite /In1' /In1. try done. }
        assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
        { assert (dom I0 ∪ {[ n1 ]} ⊆ dom I) as Hsub.
          { clear -n1_in_I Dom_I0_in_I. set_solver. }
          pose proof (flow_big_op_valid _ _ (dom I0 ∪ {[n1]}) Hsub VI) as H'.
          rewrite big_opS_union in H'.
          by rewrite big_opS_singleton in H'.
          clear -n1_notin_I0. set_solver. }
        assert (∀ k : nat, k ∈ S → 
          1 ≤ out ([^op set] y ∈ dom I0, FI I y) n1 !!! k) as Out_1.
        { assert (out ([^op set] y ∈ dom I0, FI I y) n1 =
                ([^+ set] y ∈ dom I0, out (FI I y) n1)) as ->.
          { rewrite flow_big_op_out; try done.
            intros Hn1. rewrite flow_big_op_dom in Hn1.
            destruct Hn1 as [x0 [Hx0 Hx00]].
            rewrite Domm_I in Hx00.
            assert (n1 = x0) as <- by (clear -Hx00; set_solver).
            done. by apply Dom_I0_in_I.
            by apply (cmra_valid_op_l _ (FI I n1)) in H0'''. }
          rewrite (ccm_big_opS_delete _ _ n); try done.
          set M := ([^+ set] y ∈ (dom I0 ∖ {[n]}), out (FI I y) n1).
          intros k Hk.
          unfold ccmop, ccm_op. simpl.
          rewrite lookup_total_lifting.
          unfold ccmop, ccm_op. simpl. unfold nat_op.
          apply Outsets_S in Hk. unfold outsets in Hk.
          rewrite (Nx_dom n n1 Hnx_n) in Hk.
          rewrite big_opS_singleton in Hk.
          unfold outset in Hk. rewrite nzmap_elem_of_dom_total in Hk.
          unfold ccmunit, ccm_unit in Hk. simpl in Hk.
          unfold nat_unit in Hk.
          set a := out (FI I n) n1 !!! k.
          set b := M !!! k.
          rewrite -/a in Hk.
          clear -Hk. lia. }  
        by pose proof Hpose Out_1 n1_in_In1 Domm_I0_notEmpty H0' H0'' H0''' 
          as Hpose. }
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
    insert_flow_upd n0 Nx Mk S I = res →
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
    unfold insert_flow_upd in Hflow.
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
    
    pose proof insert_flow_upd_rec_defined Key n1 (dom I ∖ {[n0]}) 
      Nx Mk S I I' Nx_key Hcl n1_in_I' H' H'' Key_I' as Hpose.
    clear H' H''.
    destruct (insert_flow_upd_rec n1 (dom I ∖ {[n0]}) Nx Mk S I I') 
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
    
    
    pose proof insert_flow_upd_invariants Key n1 (dom I ∖ {[n0]}) Nx Mk S 
      I I' II nk n0 In0 Nx_key Hcl KS_Mk Nx_dom Nx_dom' VI Domm_I n0_in_I' 
      n1_in_I' n0_neq_n1 Key_I' Key_n0 Def_I'_n0 Def_I'_n Dom_I'_in_I Nx_x 
      I'_x Domm_I' Inf_n1 Inf_x Out_x Outset_k' KS_I' Heq Hflow1 
      as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 
            [HInv6 [HInv7 [HInv8 [HInv9 [HInv10 
            [HInv11 [HInv12 HInv13]]]]]]]]]]]].
    

    exists II, nk. repeat (split; try done).
    unfold FI at 1. by rewrite HInv9.
  Admitted.

End insert_flow_upd.
