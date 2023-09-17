Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
From Coq Require Import QArith Qcanon.
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export edgesets flows_big_op.
Require Import Coq.Setoids.Setoid.

Section marking_flow_upd.
  Context `{Countable K}.
  Open Scope ccm_scope.
  
  Parameter KS : gset K.
  
  Function marking_flow_updk_rec (es: gmap Node esT)
    (I: gmap Node (multiset_flowint_ur K)) (k: K) 
    (n: Node) (R: gset Node)
    (I': gmap Node (multiset_flowint_ur K))
    {measure size R} : option (gmap Node (multiset_flowint_ur K) * Node) :=
  match (bool_decide (n ∈ R)) with
  | false => None
  | true =>
    match (es !!! n) !! k with
    | None => Some (I', n)
    | Some n1 => 
      (* Have to pick from I' because n's inflow is already updated *)
      let In := I' !!! n in
      (* Add k to outf(In, n1) *)
      let In' := outflow_insert_set In n1 {[k]} in
      (* Pick from I because n1 must be untouched so far *)
      let In1 := I !!! n1 in
      (* Add k to inf(In1, n1) *)
      let In1' := inflow_insert_set In1 n1 {[k]} in
      let II := <[n := In']> I' in
      let II' := <[n1 := In1']> II in  
      marking_flow_updk_rec es I k n1 (R ∖ {[n]}) II' end end.
  intros es I k n R I' Hbool n1 ?.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.
  
  Definition marking_flow_updk_post (I II: gmap Node (multiset_flowint_ur K)) :=
    let f := λ m1 m2,
              match m1, m2 with 
              | Some m1, Some m2 => Some m2
              | None, Some m2 => Some m2
              | Some m1, None => Some m1
              | None, None => None end in
    merge f I II.
  

  Definition marking_flow_updk es I k n0 :=
    match (es !!! n0) !! k with
    | None => None
    | Some n1 =>
      let In0 := I !!! n0 in
      let In0' := outflow_insert_set In0 n1 {[k]} in
      let In1 := I !!! n1 in
      let In1' := inflow_insert_set In1 n1 {[k]} in
      let I' := <[n1 := In1']> ({[n0 := In0']}) in
      match marking_flow_updk_rec es I k n1 (dom I ∖ {[n0]}) I' with
      | Some (II, nk) =>
        let II' := marking_flow_updk_post I II in
        Some (II', nk)
      | None => None end end.

  Lemma marking_flow_updk_rec_defined rank es I k n R I':
    (es_rank_rel es rank) →
    (es_closed es I) →
    (n ∈ dom I') →
    (dom I = R ∪ dom I') →
    (R ∩ dom I' = {[n]}) →
    (∀ x, x ∈ dom I' → (rank x ≤ rank n)%Qc) →
      marking_flow_updk_rec es I k n R I' ≠ None.
  Proof.
    apply marking_flow_updk_rec_ind; try done.
    - clear n R. intros n R I0 n_notin_R.
      rewrite bool_decide_eq_false in n_notin_R.
      intros _ _ _ _ ? _. set_solver.
    - clear n R. intros n R I0 n_in_R.
      rewrite bool_decide_eq_true in n_in_R.
      intros n1 FN_n In In' In1 In1' II I0' HInd ES_rank
        ES_cl n_in_I0 Dom_I R_inter_I0 Rank_I0.
      assert (n1 ∈ dom_esT (es !!! n)) as n1_in_esn. { admit. }
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof ES_rank n n1 n1_in_esn as H'.
        intros n1_in_I0. apply Rank_I0 in n1_in_I0.
        clear -H' n1_in_I0. apply Qcle_ngt in n1_in_I0. 
        try done. }
      assert (dom I0' = dom I0 ∪ {[n1]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct ES_cl as [_ ES_cl].
        pose proof ES_cl n as H'. by apply H'. }
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
      + pose proof ES_rank n n1 n1_in_esn as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Rank_I0 in Hx. clear -Hx H'. 
          apply Qclt_le_weak in H'.
          apply (Qcle_trans _ _ _ Hx H').
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
  Admitted.
      
  Lemma marking_flow_updk_invariants rank es I k n R I' II' nk n0 In0:
    let FI := λ I x, I !!! x in 
    (es_rank_rel es rank) →
    (es_closed es I) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
    (∀ x, x ∈ dom I ∖ {[n0]} → es_outset_rel x (es !!! x) (FI I x)) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → es_outset_rel x (es !!! x) (FI I' x)) →
    (n0 ∈ dom I') → (n ∈ dom I') → (n0 ≠ n) →
    (∀ x, x ∈ dom I' → (rank x ≤ rank n)%Qc) →
    (∀ x, x ∈ dom I' ∖ {[n0]} → (rank n0 < rank x)%Qc) →
    (FI I' n0 = In0) →
    (FI I' n = inflow_insert_set (FI I n) n {[k]}) →
    (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → keyset (FI I' x) = keyset (FI I x)) →
    (keyset (FI I' n0) = keyset (FI I n0) ∖ {[k]}) →
    (k ∈ insets (FI I n)) →
    (∀ x, x ∈ dom I' → domm (FI I' x) = {[x]}) →
    ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
    marking_flow_updk_rec es I k n R I' = Some (II', nk) →
        ((([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x))
        ∧ (keyset (FI II' nk) = keyset (FI I nk) ∪ {[k]})
        ∧ (keyset (FI II' n0) = keyset (FI I n0) ∖ {[k]})
        ∧ (∀ x, x ∈ dom II' ∖ {[n0; nk]} → keyset (FI II' x) = keyset (FI I x))
        ∧ (∀ x, x ∈ dom II' ∖ {[n0]} → es_outset_rel x (es !!! x) (FI II' x))
        ∧ (FI II' n0 = In0)
        ∧ (dom II' ⊆ dom I)
        ∧ (n0 ≠ nk)
        ∧ (n0 ∈ dom II')
        ∧ (nk ∈ dom II')
        ∧ (∀ x, x ∈ dom II' → domm (FI II' x) = {[x]})).
  Proof.
    intros FI. apply marking_flow_updk_rec_ind.
    - intros; try done.
    - clear n R. intros n R I0 n_in_R FN_n ES_rank ES_cl VI Domm_I  
        Outflow_I Outflow_I0 n0_in_I0 n_in_I0 n0_neq_n Rank_I0 Rank_n0 
        Def_I0_n0 Def_I0_n Dom_I0_in_I KS_I0 KS_n0 k_in_Insn Domm_I0 
        Heq [= -> ->].
      assert (keyset (FI II' nk) = keyset (FI I nk) ∪ {[k]}).
      { rewrite Def_I0_n.
        rewrite /keyset. rewrite inflow_insert_set_insets.
        rewrite inflow_insert_set_outsets.
        assert (k ∉ outsets (FI I nk)) as H'.
        { admit. }
        clear -H'; set_solver. }
      assert (∀ x, x ∈ dom II' ∖ {[n0]} → es_outset_rel x (es !!! x) (FI II' x)).
      { intros x Hx. destruct (decide (x = nk)) as [-> | Hxn].
        - intros n'. rewrite Def_I0_n.
          rewrite inflow_insert_set_outset_ne.
          rewrite inflow_insert_set_inset.
          assert (nk ∈ dom I ∖ {[n0]}) as H' 
            by (clear -Hx Dom_I0_in_I n0_neq_n; set_solver).
          intros k'. destruct (decide (k' = k)) as [-> | Hk'].
          + assert (k ∉ outset K (FI I nk) n') as H''.
            { admit. }
            split; try done.
            intros [H''' _]; exfalso; clear -H''' FN_n.
            rewrite H''' in FN_n. try done.
          + pose proof Outflow_I nk H' n' k' as H''.
            split; try done. intros H'''; apply H'' in H'''.
            destruct H''' as [H1' H1''].
            split; try done.
            clear -H1'' Hk'. set_solver.
            intros [H1' H1''].
            apply H''. split; try done.
            clear -H1'' Hk'; set_solver.
        - assert (x ∈ dom II' ∖ {[n0; nk]}) as Hx' by set_solver.
          by apply Outflow_I0. }  
      split; try done.
    - clear n R. intros n R I0 n_in_R n1 FN_n.
      intros In In' In1 In1' II I0' HInd ES_rank ES_cl VI Domm_I 
        Outflow_I Outflow_I0 n0_in_I0 n_in_I0 n0_neq_n Rank_I0 Rank_n0 
        Def_I0_n0 Def_I0_n Dom_I0_in_I KS_I0 KS_n0 k_in_Insn Domm_I0 Heq Hflow.
      assert (n1 ∈ dom_esT (es !!! n)) as n1_in_esn. { admit. }
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof ES_rank n n1 n1_in_esn as H'.
        intros n1_in_I0. apply Rank_I0 in n1_in_I0.
        clear -H' n1_in_I0. apply Qcle_ngt in H'; try done. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct ES_cl as [_ ES_cl].
        pose proof ES_cl n as H'. by apply H'. }  
      assert (∀ x, x ∈ dom I0 → domm (FI (<[n:=In']> I0) x) = {[x]}) 
        as Domm_II.
      { intros x Hx. destruct (decide (n = x)) as [-> | Hxn].
        - unfold FI. rewrite lookup_total_insert.
          subst In'. rewrite flowint_outflow_map_set_domm.
          subst In. rewrite Domm_I0; try done.
        - unfold FI. rewrite lookup_total_insert_ne; try done.
          rewrite Domm_I0; try done. }
      assert (n0 ≠ n1) as n0_neq_n1.
      { clear -n0_in_I0 n1_notin_I0. set_solver. }    
      apply HInd; try done; clear HInd.
      { rewrite /FI. rewrite Dom_I0'. intros x; rewrite elem_of_difference.
        intros [Hx1 Hx2]. rewrite elem_of_union in Hx1.
        destruct Hx1 as [Hx | Hx].
        - rewrite /I0'. 
          assert (x ≠ n1) by (clear -Hx n1_notin_I0; set_solver).
          rewrite lookup_total_insert_ne; try done. rewrite /II.
          destruct (decide (x = n)) as [-> | Hxn].
          + rewrite lookup_total_insert. subst In'.
            unfold es_outset_rel. intros n' k'.
            rewrite outflow_insert_set_inset.
            assert (n ∈ dom I ∖ {[n0]}) as H' by 
              (clear -n_in_I0 Dom_I0_in_I Hx2; set_solver).
            destruct (decide (n' = n1)) as [-> | Hn'n].
            * rewrite outflow_insert_set_outset.
              rewrite /In.
              pose proof Outflow_I n H' n1 k' as H''.
              unfold FI in Def_I0_n. rewrite Def_I0_n.
              rewrite inflow_insert_set_outset_ne.
              rewrite inflow_insert_set_inset.
              unfold FI in H''.
              split. rewrite elem_of_union.
              intros [Hk' | Hk'].
              apply H'' in Hk'.
              destruct Hk' as [Hk1' Hk2'].
              split; try done. clear -Hk2'; set_solver.
              assert (k' = k) as -> by (clear -Hk'; set_solver).
              split; try done. clear; set_solver.
              intros [Hk1 Hk2]. rewrite elem_of_union in Hk2.
              destruct Hk2 as [Hk2 | Hk2]. rewrite elem_of_union.
              left. apply H''; split; try done.
              assert (k' = k) as -> by (clear -Hk2; set_solver).
              clear; set_solver.
            * rewrite outflow_insert_set_outset_ne; try done.
              rewrite /In.
              pose proof Outflow_I n H' n' as H''.
              rewrite /FI in H''. rewrite /FI in Def_I0_n.
              rewrite Def_I0_n.
              rewrite inflow_insert_set_outset_ne.
              rewrite inflow_insert_set_inset.
              split. intros Hk; apply H'' in Hk.
              destruct Hk as [Hk1 Hk2].
              split; try done. rewrite elem_of_union.
              by left.
              intros [Hk1 Hk2]. rewrite elem_of_union in Hk2.
              destruct Hk2 as [Hk2 | Hk2]. apply H''; split; try done.
              assert (k' = k) as -> by (clear -Hk2; set_solver).
              apply H''. split; try done. unfold FI in k_in_Insn. admit.
          + rewrite lookup_total_insert_ne; try done.
            apply Outflow_I0. clear -Hx Hx2 Hxn; set_solver.
        - clear -Hx Hx2; set_solver. }
      { rewrite Dom_I0'. clear -n0_in_I0.
        set_solver. }
      { rewrite Dom_I0'. clear -Dom_I0_in_I n1_in_I. set_solver. }
      { pose proof ES_rank n n1 n1_in_esn as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        - apply Rank_I0 in Hx. clear -Hx H'. apply Qclt_le_weak in H'.
          apply (Qcle_trans _ _ _ Hx H').
        - assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done. }
      { rewrite Dom_I0'. intros x. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        - apply Rank_n0. clear -Hx1 Hx2; set_solver.
        - assert (x = n1) as -> by (clear -Hx1; set_solver). 
          pose proof ES_rank n n1 n1_in_esn as H'.
          assert ((rank n0 ≤ rank n)%Qc) as H''.
          { by apply Rank_I0. }
          clear -H' H''.
          apply (Qcle_lt_trans _ _ _ H'' H'); try done. }
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
          + unfold FI. subst I0'.
            rewrite lookup_total_insert_ne; 
              last by (clear -Hx2; set_solver).
            subst II. rewrite lookup_total_insert.
            subst In'. unfold keyset.
            rewrite outflow_insert_set_insets.
            rewrite outflow_insert_set_outsets.
            subst In. unfold FI in Def_I0_n. rewrite Def_I0_n.
            rewrite inflow_insert_set_insets.
            rewrite inflow_insert_set_outsets.
            unfold FI in k_in_Insn.
            assert (k ∈ outsets (I !!! n)) as H'.
            { admit. } 
            clear -k_in_Insn H'; set_solver.
          + unfold FI. subst I0'.
            rewrite lookup_total_insert_ne; 
              last by (clear -Hx2; set_solver).
            subst II. rewrite lookup_total_insert_ne; try done.
            apply KS_I0. clear -Hx1 Hx2 Hxn; set_solver.
        - clear -Hx1 Hx2; set_solver. }
      { subst I0'. unfold FI. 
        rewrite lookup_total_insert_ne; try done.
        subst II. rewrite lookup_total_insert_ne; try done.  }  
      { assert (k ∈ inset K (FI I n1) n1) as H'. 
        { apply (flowint_inset_step (FI I n) _ _ _).
          - admit.
          - rewrite Domm_I; try done. clear; set_solver.
          - admit. }
        admit. }    
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
      { rewrite Dom_I0'. 
        rewrite !big_opS_union; [try done | set_solver | set_solver].
        rewrite !big_opS_singleton. 
        all: try (clear -n_notin_I0; set_solver).
        rewrite /I0'; rewrite /FI. rewrite lookup_total_insert.
        rewrite /II.
        assert (([^op set] y ∈ dom I0, FI (<[n1:=In1']> (<[n:=In']> I0)) y) = 
                  ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Def_II.
        { (* syntactic rewriting *) admit. }
        rewrite Def_II.
        assert (✓ ([^op set] y ∈ dom I0, FI I y)) as Valid_I.
        { apply (flow_big_op_valid _ (dom I)); try done. }
        assert (✓ ([^op set] y ∈ dom I0, FI I0 y)) as Valid_I0.
        { apply leibniz_equiv_iff in Heq. rewrite <-Heq. try done. }
        assert (✓ ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Valid_II.
        { assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) = 
                    ([^op set] y ∈ dom I0 ∖ {[n]}, FI I0 y) ⋅ In') as ->.
          { (* syntactic rewriting *) admit. }
          apply (outflow_map_set_valid2
                        (([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y)) 
                        (I0 !!! n)  
                        (In')
                        (λ _ n, n + 1)%nat 
                        n1
                        {[k]}).
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
            { (* syntactic rewriting *) admit. }
            by rewrite H'. }

        pose proof (flowint_insert_eq
                      ([^op set] y ∈ dom I0, I !!! y)
                      ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                      (I !!! n1)
                      In1' 
                      n1 
                      {[k]}) as Hpose. 
        assert (n1 ∈ domm (FI I n1)) as n1_in_In1.
        { rewrite Domm_I; try done. clear; set_solver. }
        assert (domm ([^op set] y ∈ dom I0, I !!! y) ≠ ∅) as Domm_I0_notEmpty.
        { assert (n ∈ (domm ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
          { rewrite flow_big_op_dom; try done. exists n; split; try done.
            rewrite Domm_I; last first.
            { clear -n_in_I0 Dom_I0_in_I. set_solver. } 
            clear; set_solver. }
          clear -H'; set_solver. }
        assert (domm ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)) = 
                  domm ([^op set] y ∈ dom I0, (I !!! y))) as Domm_II_eq_I.
        { assert ((domm ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y))) ⊆ 
                      (domm ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
          { intros n'. rewrite !flow_big_op_dom; try done.
            intros [x [Hx1 Hx2]]. exists x. split; try done.
            rewrite Domm_II in Hx2; try done. rewrite Domm_I; try done.
            clear -Hx1 Dom_I0_in_I. set_solver. }
          assert ((domm ([^op set] y ∈ dom I0, (I !!! y))) ⊆ 
                    (domm ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)))) as H''.
          { intros n'. rewrite !flow_big_op_dom; try done.
            intros [x [Hx1 Hx2]]. exists x. split; try done.
            rewrite Domm_II. rewrite Domm_I in Hx2; try done.
            clear -Hx1 Dom_I0_in_I. set_solver. done. }
          clear -H' H''; set_solver. }
        assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) =
          outflow_insert_set ([^op set] y ∈ dom I0, I !!! y) n1 {[k]}) 
          as H0'.
        { apply intEq; try done. 
          - rewrite Domm_II_eq_I. try done. 
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
                          domm ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
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
                      - (* forall x ∈ dom I0 ∖ {[n]}, 
                              FI (<[n:=In']> I0) x = FI I0 x *)
                        (* syntactic rewriting *)
                        admit.
                      - assert (out (FI (<[n := In']> I0) n) n' 
                                  = out (FI I0 n) n') as H'.
                        { rewrite /FI. rewrite lookup_total_insert.
                          rewrite /In' /In.
                          assert (n' ≠ n1). 
                          { clear -n''_in_I0 n1_notin_I0. set_solver. }
                          unfold out. 
                          rewrite outflow_map_set_out_map_ne; try done. }
                        (* break the big sum *)
                        (* syntactic rewriting + above assert *)
                        admit. }
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
              - (* syntactic rewriting + flow_inf lemma *) admit.
            }
            by rewrite HI0.
          - rewrite Heq. intros n'.
            destruct (decide (n' ∈ 
                domm ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
                as [Hn' | Hn'].
            + (* syntactic rewriting + flow_outf lemma *) admit.     
            + destruct (decide (n' = n1)) as [-> | Hn1'].
              * apply nzmap_eq. intros k'. 
                destruct (decide (k' ∈ ({[k]}: gset K))) as [Hk' | Hk'].
                ** rewrite outflow_lookup_total_map_set; try done.
                   rewrite !flow_big_op_out.
                   (* break the big sum + lookup_total_lifting *)
                   admit.
                   { apply leibniz_equiv_iff in Heq. 
                     rewrite <-Heq. try done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_I0 in Hx2; try done.
                     assert (n1 = x) as -> by set_solver.
                     clear -Hx1 n1_notin_I0. try done. }
                   { try done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_II in Hx2; try done.
                     assert (n1 = x) as -> by set_solver.
                     clear -Hx1 n1_notin_I0. try done. }
                ** rewrite outflow_lookup_total_map_set_ne; try done.
                   rewrite !flow_big_op_out.
                   (* break the big sum + lookup_total_lifting *)
                   admit.
                   { try done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_I0 in Hx2; try done.
                     assert (n1 = x) as -> by set_solver.
                     clear -Hx1 n1_notin_I0. try done. }
                   { try done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_II in Hx2; try done.
                     assert (n1 = x) as -> by set_solver.
                     clear -Hx1 n1_notin_I0. try done. }
              * unfold out. rewrite outflow_map_set_out_map_ne; try done.
                (* syntactic rewriting *)
                admit. }                           
        assert (In1' = inflow_insert_set (I !!! n1) n1 {[k]}) as H0''.
        { rewrite /In1' /In1. try done. }
        assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
        {  admit. }
        by pose proof Hpose n1_in_In1 Domm_I0_notEmpty H0' H0'' H0''' 
          as Hpose. }
  Admitted.

  Lemma marking_flow_updk_defined rank es I k n0:
    (es_rank_rel es rank) →
    (es_closed es I) →
    ((es !!! n0) !! k ≠ None) →
    (n0 ∈ dom I) →
      marking_flow_updk es I k n0 ≠ None.
  Proof.
    intros ES_rank ES_cl FN_n0_k n0_in_I.
    unfold marking_flow_updk.
    destruct ((es !!! n0) !! k) as [n1 | ]; try done.
    set In1 := inflow_insert_set (I !!! n1) n1 {[k]}.
    set In0 := outflow_insert_set (I !!! n0) n1 {[k]}.
    set I': gmap Node (multiset_flowint_ur K) := {[n1 := In1; n0 := In0]}.
    assert (In1 = inflow_insert_set (I !!! n1) n1 {[k]}) as Def_In1.
    { try done. }
    assert (In0 = outflow_insert_set (I !!! n0) n1 {[k]}) as Def_In0.
    { try done. }
    assert (I' = {[n1 := In1; n0 := In0]}) as Def_I'.
    { try done. }
    assert (n1 ∈ dom I') as n1_in_I' by set_solver.
    assert (dom I' = {[n0; n1]}) as Dom_I' by set_solver.
    assert (n1 ∈ dom_esT (es !!! n0)) as n1_in_esn0. { admit. }
    assert (n1 ∈ dom I) as n1_in_I.
    { destruct ES_cl as [_ ES_cl].
      pose proof ES_cl n0 as H'. by apply H'. }
    assert (dom I = (dom I ∖ {[n0]}) ∪ dom I') as H'.
    { rewrite Dom_I'.
      assert ((dom I ∖ {[n0]}) ∪ {[n0; n1]} ⊆ dom I) as H'.
      { set_solver. }
      assert (dom I ⊆ (dom I ∖ {[n0]}) ∪ {[n0; n1]}) as H''.
      { clear -n0_in_I n1_in_I. intros x Hx. 
        destruct (decide (x = n0)); first by set_solver.
        destruct (decide (x = n1)); first by set_solver.
        by set_solver. }
      set_solver. }  
    assert (n0 ≠ n1) as n0_neq_n1.
    { admit. }
    assert ((dom I ∖ {[n0]}) ∩ dom I' = {[n1]}) as H''.
    { rewrite Dom_I'. set_solver. }
    assert ((rank n0 < rank n1)%Qc) as Rank_n0_n1.
    { by apply ES_rank. }
    assert (∀ x : Node, x ∈ dom I' → (rank x ≤ rank n1)%Qc) as Rank_I0.
    { rewrite Dom_I'. intros x; rewrite elem_of_union.
      intros [Hx | Hx].
      - assert (x = n0) as -> by set_solver.
        by apply Qclt_le_weak in Rank_n0_n1.
      - assert (x = n1) as -> by set_solver. try done. }
    pose proof marking_flow_updk_rec_defined rank es I k n1 (dom I ∖ {[n0]}) I'
      ES_rank ES_cl n1_in_I' H' H'' Rank_I0.
    destruct (marking_flow_updk_rec es I k n1 (dom I ∖ {[n0]}) I') 
      as [(II,nk)|]; try done.    
  Admitted.    

  Lemma marking_flow_updk_post_dom I II I' :
    (dom II ⊆ dom I) →
    I' = marking_flow_updk_post I II →
      dom I' = dom I.
  Proof.
    intros Hdom Hflow.
    assert (dom I' ⊆ dom I).
    { intros x. rewrite elem_of_dom.
      subst I'. intros [m Hx].
      unfold marking_flow_updk_post in Hx.
      rewrite lookup_merge in Hx.
      unfold diag_None in Hx.
      destruct (I !! x) as [mI |] eqn: HIx.
      - rewrite elem_of_dom; try done.
      - destruct (II !! x) as [mII |] eqn: HIIx; try done.
        apply Hdom. rewrite elem_of_dom; try done. }
    assert (dom I ⊆ dom I').
    { intros x. rewrite !elem_of_dom.
      intros [mx Hx]. subst I'.
      unfold marking_flow_updk_post.
      rewrite lookup_merge.
      unfold diag_None.
      rewrite Hx.
      destruct (II !! x) as [mII |]; try done. }
    set_solver.      
  Qed.          

  Lemma marking_flow_updk_post_intfEq I II I' :
    let FI := λ I x, I !!! x in
    (dom II ⊆ dom I) →
    (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x)) → 
    I' = marking_flow_updk_post I II →
      (([^op set] x ∈ dom I, FI I x) = ([^op set] x ∈ dom I, FI I' x)).
  Proof.
  Admitted.

  Lemma marking_flow_updk_post_lookup I II I' :
    (dom II ⊆ dom I) →
    I' = marking_flow_updk_post I II →
      (∀ x, x ∈ dom II → I' !! x = II !! x).
  Proof.
    intros Dom_II_in_I Hflow. intros x Hx.
    rewrite Hflow. unfold marking_flow_updk_post.
    rewrite lookup_merge. unfold diag_None.
    destruct (I !! x) as [mI |] eqn: HmI.
    - destruct (II !! x) as [mII |] eqn: HmII; try done.
      apply not_elem_of_dom_2 in HmII.
      set_solver.
    - assert (II !! x = None) as H'.
      { apply not_elem_of_dom. 
        apply not_elem_of_dom_2 in HmI.
        set_solver. }
      by rewrite H'.
  Qed.    

  Lemma marking_flow_updk_post_lookup_total I II I' :
    (dom II ⊆ dom I) →
    I' = marking_flow_updk_post I II →
      (∀ x, x ∈ dom II → I' !!! x = II !!! x).
  Proof.
    intros ? H' ? ?; rewrite !lookup_total_alt.
    rewrite (marking_flow_updk_post_lookup _ _ _ _ H'); try done.
  Qed.  

  Lemma marking_flow_updk_post_lookup_ne I II I' :
    (dom II ⊆ dom I) →
    I' = marking_flow_updk_post I II →
      (∀ x, x ∈ dom I ∖ dom II → I' !! x = I !! x).
  Proof.
    intros Dom_II_in_I Hflow. intros x Hx.
    rewrite elem_of_difference in Hx.
    destruct Hx as [Hx1 Hx2].
    rewrite Hflow. unfold marking_flow_updk_post.
    rewrite lookup_merge. unfold diag_None.
    rewrite elem_of_dom in Hx1.
    destruct Hx1 as [mI Hx1].
    rewrite Hx1.
    rewrite not_elem_of_dom in Hx2.
    by rewrite Hx2.
  Qed.  

  Lemma marking_flow_updk_post_lookup_total_ne I II I' :
    (dom II ⊆ dom I) →
    I' = marking_flow_updk_post I II →
      (∀ x, x ∈ dom I ∖ dom II → I' !!! x = I !!! x).
  Proof.
    intros ? H' ? ?; rewrite !lookup_total_alt.
    rewrite (marking_flow_updk_post_lookup_ne _ _ _ _ H'); try done.
  Qed.
  
  Lemma marking_flow_updk_post_summary (es: gmap Node esT)
    (k: K) (I II I': gmap Node (multiset_flowint_ur K))  
    (n0 nk: Node) :
    let FI := λ I x, I !!! x in
    (dom II ⊆ dom I) →
    (n0 ∈ dom II) → (nk ∈ dom II) →
    (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
    (∀ x, x ∈ dom II → domm (FI II x) = {[x]}) →
    (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x)) → 
    (keyset (FI II nk) = keyset (FI I nk) ∪ {[k]}) →
    (keyset (FI II n0) = keyset (FI I n0) ∖ {[k]}) →
    (∀ x, x ∈ dom II ∖ {[n0; nk]} → keyset (FI II x) = keyset (FI I x)) →
    (∀ x, x ∈ dom I ∖ {[n0]} → es_outset_rel x (es !!! x) (FI I x)) →
    (∀ x, x ∈ dom II ∖ {[n0]} → es_outset_rel x (es !!! x) (FI II x)) →
    I' = marking_flow_updk_post I II →
          ((dom I' = dom I)
        ∧ (∀ x, x ∈ dom I' → domm (FI I' x) = {[x]})  
        ∧ (([^op set] x ∈ dom I, FI I x) = ([^op set] x ∈ dom I, FI I' x))
        ∧ (keyset (FI I' nk) = keyset (FI I nk) ∪ {[k]})
        ∧ (keyset (FI I' n0) = keyset (FI I n0) ∖ {[k]})
        ∧ (∀ x, x ∈ dom I' ∖ {[n0; nk]} → keyset (FI I' x) = keyset (FI I x))
        ∧ (∀ x, x ∈ dom I' ∖ {[n0]} → es_outset_rel x (es !!! x) (FI I' x))).
  Proof.
    intros FI Dom_II_in_I n0_in_II nk_in_II Domm_I Domm_II Heq 
      KS_nk KS_n0 KS_II Outflow_I Outflow_II Hflow.
    pose proof marking_flow_updk_post_dom I II I' Dom_II_in_I Hflow as Dom_I'_eq_I.
    pose proof marking_flow_updk_post_intfEq I II I' Dom_II_in_I Heq Hflow as Heq'.
    split; try done. split; try done.
    { intros x Hx.  
      destruct (decide (x ∈ dom II)) as [Hx1 | Hx1].
      + unfold FI.
        rewrite (marking_flow_updk_post_lookup_total _ _ _ _ Hflow); try done.
        apply Domm_II; try done.
      + unfold FI.
        rewrite (marking_flow_updk_post_lookup_total_ne _ _ _ _ Hflow); try done.
        apply Domm_I; try done.
        all: clear -Dom_I'_eq_I Hx1 Hx; set_solver. }
    split; try done.
    split; try done.    
    { assert (FI I' nk = FI II nk) as H'.
      { unfold FI.
        by rewrite (marking_flow_updk_post_lookup_total _ _ _ _ Hflow). }
      rewrite H'; try done. }
    split; try done.  
    { assert (FI I' n0 = FI II n0) as H'.
      { unfold FI. 
        by rewrite (marking_flow_updk_post_lookup_total _ _ _ _ Hflow). }
      rewrite H'; try done. }
    split; try done.  
    { intros x. rewrite elem_of_difference.
      intros [Hx1 Hx2].
      destruct (decide (x ∈ dom II)) as [Hx3 | Hx3].
      + unfold FI.
        rewrite (marking_flow_updk_post_lookup_total _ _ _ _ Hflow); try done.
        apply KS_II. clear -Hx3 Hx2; set_solver.
      + unfold FI.
        rewrite (marking_flow_updk_post_lookup_total_ne _ _ _ _ Hflow); try done.
        rewrite Dom_I'_eq_I in Hx1. clear -Hx1 Hx3; set_solver. }
    { intros x Hx.  
      destruct (decide (x ∈ dom II)) as [Hx1 | Hx1].
      + unfold FI.
        rewrite (marking_flow_updk_post_lookup_total _ _ _ _ Hflow); try done.
        apply Outflow_II; try done.
        clear -Hx Hx1; set_solver.
      + unfold FI.
        rewrite (marking_flow_updk_post_lookup_total_ne _ _ _ _ Hflow); try done.
        apply Outflow_I; try done.
        by rewrite <-Dom_I'_eq_I.
        rewrite Dom_I'_eq_I in Hx. clear -Hx1 Hx; set_solver. }
  Qed.

  Lemma marking_flow_updk_summary rank n0 es I k res n1:
    let FI := λ I x, I !!! x in 
    (es_rank_rel es rank) →
    (es_closed es I) →
    ((es !!! n0) !! k = Some n1) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
    (∀ x, x ∈ dom I ∖ {[n0]} → es_outset_rel x (es !!! x) (FI I x)) →
    (∀ n' k, k ∈ outset _ (FI I n0) n' → 
              (es !!! n0) !! k = Some n' ∧ k ∈ inset _ (FI I n0) n0) →
    (k ∈ inset _ (FI I n0) n0) →
    (n0 ∈ dom I) →
    marking_flow_updk es I k n0 = res →
      ∃ II' nk, 
        res = Some (II', nk)
      ∧ (dom II' = dom I)
      ∧ (n0 ≠ nk)
      ∧ (n0 ∈ dom II')
      ∧ (nk ∈ dom II')
      ∧ (∀ x, x ∈ dom II' → domm (FI II' x) = {[x]})
      ∧ (([^op set] x ∈ dom I, FI I x) = ([^op set] x ∈ dom I, FI II' x))
      ∧ (∀ x, x ∈ dom II' ∖ {[n0]} → es_outset_rel x (es !!! x) (FI II' x))
      ∧ (inset _ (FI II' n0) n0 = inset _ (FI I n0) n0)
      ∧ (outset _ (FI II' n0) n1 = outset _ (FI I n0) n1 ∪ {[k]})
      ∧ (∀ n', n' ≠ n1 → outset K (FI I n0) n' = outset K (FI II' n0) n')
      ∧ (∀ n' k, k ∈ outset _ (FI II' n0) n' → 
              (es !!! n0) !! k = Some n' ∧ k ∈ inset _ (FI II' n0) n0)
      ∧ (keyset (FI II' nk) = keyset (FI I nk) ∪ {[k]})
      ∧ (keyset (FI II' n0) = keyset (FI I n0) ∖ {[k]})
      ∧ (∀ x, x ∈ dom II' ∖ {[n0; nk]} → keyset (FI II' x) = keyset (FI I x)).
  Proof.
    intros FI ES_rank ES_cl FN_n0 VI Domm_I Outflow_I Outset_n0 k_in_inset 
      n0_in_I Hflow.
    unfold marking_flow_updk in Hflow.
    rewrite FN_n0 in Hflow. 
    set In1 := inflow_insert_set (I !!! n1) n1 {[k]}.
    set In0 := outflow_insert_set (I !!! n0) n1 {[k]}.
    set I': gmap Node (multiset_flowint_ur K) := {[n1 := In1; n0 := In0]}.
    assert (In1 = inflow_insert_set (I !!! n1) n1 {[k]}) as Def_In1.
    { try done. }
    assert (In0 = outflow_insert_set (I !!! n0) n1 {[k]}) as Def_In0.
    { try done. }
    assert (I' = {[n1 := In1; n0 := In0]}) as Def_I'.
    { try done. }
    rewrite <-Def_In1 in Hflow.
    rewrite <-Def_In0 in Hflow.
    rewrite <-Def_I' in Hflow.
    assert (dom I' = {[n0; n1]}) as Dom_I' by set_solver.
    assert ((es !!! n0) !! k ≠ None) as Hes.
    { rewrite FN_n0; clear; try done. }
    assert (n1 ∈ dom_esT (es !!! n0)) as n1_in_esn0. 
    { admit. }
    assert (n1 ∈ dom I') as n1_in_I' by set_solver.
    assert (n1 ∈ dom I) as n1_in_I.
    { by apply ES_cl in n1_in_esn0. }
    assert (n0 ≠ n1) as n0_neq_n1.
    { admit. }
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
    assert ((rank n0 < rank n1)%Qc) as Rank_n0_n1.
    { by apply ES_rank in n1_in_esn0. }
    assert (∀ x : Node, x ∈ dom I' → (rank x ≤ rank n1)%Qc) as Rank_I'.
    { rewrite Dom_I'. intros x; rewrite elem_of_union.
      intros [Hx | Hx].
      - assert (x = n0) as -> by set_solver.
        by apply Qclt_le_weak.
      - assert (x = n1) as -> by set_solver. try done. }
    
    pose proof marking_flow_updk_rec_defined rank es I k n1 (dom I ∖ {[n0]}) I' 
      ES_rank ES_cl n1_in_I' H' H'' Rank_I' as Hpose.
    clear H' H''.
    destruct (marking_flow_updk_rec es I k n1 (dom I ∖ {[n0]}) I') 
      as [ (II', nk) |] eqn: Hflow1; try done. clear Hpose.

    assert (∀ x, x ∈ dom I' ∖ {[n0; n1]} → 
                es_outset_rel x (es !!! x) (FI I' x)) as Outflow_I'.
    { intros x Hx. rewrite Dom_I' in Hx.
      clear -Hx; set_solver. }
    assert (n0 ∈ dom I') as n0_in_I'.
    { rewrite Dom_I'. clear; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0]} → (rank n0 < rank x)%Qc) as Rank_n0.
    { intros x. rewrite Dom_I'. rewrite elem_of_difference.
      rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2]; try done.
      assert (x = n1) as -> by set_solver. done. }
    assert (FI I' n1 = inflow_insert_set (FI I n1) n1 {[k]}) as Def_I'_n.
    { unfold FI. subst I'. rewrite lookup_total_insert; try done.  }    
    assert (dom I' ⊆ dom I) as Dom_I'_in_I.
    { rewrite Dom_I'; clear -n0_in_I n1_in_I; set_solver. }
    assert (∀ x, x ∈ dom I' ∖ {[n0; n1]} → 
                  keyset (FI I' x) = keyset (FI I x)) as KS_I'.
    { rewrite Dom_I'. intros x Hx. clear -Hx; set_solver. }
    assert (keyset (FI I' n0) = keyset (FI I n0) ∖ {[k]}) as KS_n0.
    { unfold FI; subst I'. rewrite lookup_total_insert_ne; try done.
      rewrite lookup_total_insert. subst In0.
      unfold keyset. rewrite outflow_insert_set_insets.
      rewrite outflow_insert_set_outsets. clear; set_solver. }  
    assert (k ∈ insets (FI I n1)) as k_in_Insn1.
    { admit. }
    assert (∀ x, x ∈ dom I' → domm (FI I' x) = {[x]}) as Domm_I'.
    { intros x. rewrite Dom_I'. rewrite elem_of_union.
      unfold FI; subst I'. intros [Hx | Hx].
      - assert (x = n0) as -> by (clear -Hx; set_solver).
        rewrite lookup_total_insert_ne; try done.
        rewrite lookup_total_insert.
        subst In0. by apply Domm_I.
      - assert (x = n1) as -> by (clear -Hx; set_solver).
        rewrite lookup_total_insert.
        subst In1. rewrite flowint_inflow_insert_set_dom.
        rewrite Domm_I; try done. clear; set_solver. }
    assert (I' !!! n0 = In0) as Def_I'_n0.
    { subst I'. rewrite lookup_total_insert_ne; try done.
      rewrite lookup_total_insert; done. }      
    assert (([^op set] x ∈ dom I', FI I x) = 
                ([^op set] x ∈ dom I', FI I' x)) as Heq.
    { admit. }
    pose proof marking_flow_updk_invariants rank es I k n1 (dom I ∖ {[n0]}) 
      I' II' nk n0 In0 ES_rank ES_cl VI Domm_I Outflow_I Outflow_I' 
      n0_in_I' n1_in_I' n0_neq_n1 Rank_I' Rank_n0 Def_I'_n0 Def_I'_n 
      Dom_I'_in_I KS_I' KS_n0 k_in_Insn1 Domm_I' Heq Hflow1 
      as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 
            [HInv6 [HInv7 [HInv8 [HInv9 [HInv10 HInv11]]]]]]]]]].

    set III := marking_flow_updk_post I II'.
    assert (III = marking_flow_updk_post I II') as Def_III.
    { try done. }
    pose proof marking_flow_updk_post_summary es k I II' III n0 nk 
      HInv7 HInv9 HInv10 Domm_I HInv11 HInv1 HInv2 
      HInv3 HInv4 Outflow_I HInv5 Def_III
      as [HInv1' [HInv2' [HInv3' [HInv4' [HInv5' [HInv6' HInv7']]]]]].
    exists III, nk. rewrite <-HInv1'.
    assert (nk ∈ dom III).
    { rewrite HInv1'. by apply HInv7. }
    assert (FI III n0 = outflow_insert_set (I !!! n0) n1 {[k]}) as Def_III_n0.
    { unfold FI. 
      rewrite (marking_flow_updk_post_lookup_total _ _ _ _ Def_III); try done. } 
    assert (inset K (FI III n0) n0 = inset K (FI I n0) n0) as Inset_n0.
    { rewrite Def_III_n0.
      by rewrite outflow_insert_set_inset. }
    assert (outset K (FI III n0) n1 = outset K (FI I n0) n1 ∪ {[k]}) 
      as Outset_n0'.
    { rewrite Def_III_n0.
      by rewrite outflow_insert_set_outset. }
    assert (∀ n', n' ≠ n1 → outset K (FI I n0) n' = outset K (FI III n0) n')
      as Outset_n0_ne.
    { rewrite Def_III_n0.
      intros n' Hn'.
      by rewrite outflow_insert_set_outset_ne. }  
    assert (∀ n' k0, k0 ∈ outset K (FI III n0) n' → 
                  (es !!! n0) !! k0 = Some n' ∧ k0 ∈ inset K (FI III n0) n0).
    { intros n' k'. rewrite Inset_n0. 
      destruct (decide (n' = n1)) as [-> | Hn'].
      - rewrite Outset_n0'. rewrite elem_of_union.
        intros [Hk' | Hk'].
        + by apply Outset_n0 in Hk'.
        + assert (k' = k) as -> by (clear -Hk'; set_solver).
          split; try done.
      - rewrite <-Outset_n0_ne; try done. apply Outset_n0. }
    split; try done. split; try done.
    split; try done. split; try done. by rewrite HInv1'.
    split; try done. split; try done.
    split; try done. by rewrite HInv1'.
  Admitted.

  Definition add_k (KM: gmap Node (gset K)) (n: Node) (k: K) :=
    let f := λ s, match s with None => Some {[k]} 
                            | Some s => Some (s ∪ {[k]}) end in
    partial_alter f n KM.

  Lemma dom_add_k KM n k:
    dom (add_k KM n k) = dom KM ∪ {[n]}.
  Proof.
    apply set_eq_subseteq.
    unfold add_k. split.
    - intros x. rewrite elem_of_dom.
      destruct (decide (x = n)) as [-> | Hxn].
      + set_solver.
      + rewrite lookup_partial_alter_ne; try done.
        rewrite <-elem_of_dom. set_solver.
    - intros x. destruct (decide (x = n)) as [-> | Hxn].
      + intros _. rewrite elem_of_dom. 
        rewrite lookup_partial_alter. 
        destruct (KM !! n); try done. 
      + rewrite elem_of_dom. rewrite lookup_partial_alter_ne; try done.
        rewrite <-elem_of_dom. set_solver.
  Qed.

  Lemma lookup_add_k KM n k:
    add_k KM n k !!! n = KM !!! n ∪ {[k]}.
  Proof.
    unfold add_k.
    rewrite !lookup_total_alt.
    rewrite lookup_partial_alter; try done.
    destruct (KM !! n); try done.
    set_solver.
  Qed.  

  Lemma lookup_add_k_ne KM n k:
    ∀ x, x ≠ n → add_k KM n k !!! x = KM !!! x.
  Proof.
    intros x Hxn. unfold add_k.
    rewrite lookup_total_alt.
    rewrite lookup_partial_alter_ne; try done.
  Qed.

  Function marking_flow_upd_rec es' n0 I (KM: gmap Node (gset K)) 
    (A R: gset K) {measure size R} :=
    match (elements R) with 
    | [] => Some (I, KM)
    | k :: _ => 
      match marking_flow_updk es' I k n0 with
      | Some (I', nk) =>
        let KM' := add_k KM nk k in
        marking_flow_upd_rec es' n0 I' KM' (A ∪ {[k]}) (R ∖ {[k]})
      | None => None end end.
  intros es' n0 I KM A R k l HR ? I' nk -> ?.
  assert (k ∈ R).
  { apply elem_of_elements. rewrite HR. set_solver. }
  apply subset_size. set_solver.
  Defined.

  Definition marking_flow_upd es n0 I0 (es_n0': esT) :=
    let es' := <[n0 := es_n0']> es in
    let es_n0 := es !!! n0 in
    let S := (dom es_n0' ∖ dom es_n0) ∩ inset K (I0 !!! n0) n0 in
    marking_flow_upd_rec es' n0 I0 ∅ ∅ S.

  Lemma marking_flow_updk_dom es I k n0 I' nk : 
    marking_flow_updk es I k n0 = Some (I', nk) → dom I' = dom I.
  Proof.
  Admitted.  

  Lemma marking_flow_upd_rec_defined rank es n0 I KM A R :
    (es_rank_rel es rank) →
    (es_closed es I) →
    (∀ k, k ∈ R → (es !!! n0) !! k ≠ None) →
    (n0 ∈ dom I) →
      marking_flow_upd_rec es n0 I KM A R ≠ None.
  Proof.
    apply marking_flow_upd_rec_ind; try done.
    - clear I KM A R. intros I KM A R k ks HR I' nk Hflow KM' HInd. 
      intros ES_rank ES_cl FN_n0 n0_in_I. apply HInd; try done; clear HInd.
      + unfold es_closed. apply marking_flow_updk_dom in Hflow.
        rewrite Hflow. apply ES_cl.
      + intros k' Hk'; apply FN_n0. set_solver.  
      + apply marking_flow_updk_dom in Hflow. by rewrite Hflow.  
    - clear I KM A R. intros I KM A R k ks HR Hflow ES_rank ES_cl 
        FN_n0 n0_in_I _.
      assert ((es !!! n0) !! k ≠ None) as Hk.
      { apply FN_n0. apply elem_of_elements. rewrite HR. clear; set_solver. }  
      pose proof marking_flow_updk_defined rank es I k n0 ES_rank ES_cl Hk n0_in_I.
      try done.
  Qed.

  Lemma marking_flow_upd_invariants rank n0 es es_n0' I KM A R I' KM' I0:
    let FI := λ I x, I !!! x in
    let es' := <[n0 := es_n0']> es in
    let es_n0 := es !!! n0 in
    let S := (dom es_n0' ∖ dom es_n0) ∩ inset K (I0 !!! n0) n0 in    
    (es_rank_rel es rank) →
    (es_closed es I) →
    (es_marking_upd es_n0 es_n0') →
    (∀ k, k ∈ R → es_n0' !! k ≠ None) →  
    (A ## R) →
    (S = A ∪ R) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
    (∀ x, x ∈ dom I ∖ {[n0]} → es_outset_rel x (es !!! x) (FI I x)) →
    (es_outset_rel n0 (es !!! n0) (FI I0 n0)) →
    (insets (FI I n0) = insets (FI I0 n0)) →
    (outsets (FI I n0) = outsets (FI I0 n0) ∪ A) →
    (∀ n', outset _ (FI I0 n0) n' ⊆ outset _ (FI I n0) n') →
    (∀ n' k, k ∈ outset _ (FI I n0) n' → 
              es_n0' !! k = Some n' ∧ k ∈ inset _ (FI I n0) n0) →
    (∀ n' k, k ∈ A → 
              es_n0' !! k = Some n' ∧ k ∈ inset _ (FI I n0) n0 →
                k ∈ outset _ (FI I n0) n') →
    (n0 ∈ dom I) → (dom I = dom I0) →
    (dom KM ⊆ dom I) → (n0 ∉ dom KM) →
    (([^op set] x ∈ dom I, FI I0 x) = ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom KM → keyset (FI I x) = keyset (FI I0 x) ∪ (KM !!! x)) →
    (∀ x, x ∈ dom I ∖ dom KM → x ≠ n0 → keyset (FI I x) = keyset (FI I0 x)) → 
    marking_flow_upd_rec es' n0 I KM A R = Some (I', KM') →
        ((dom I' = dom I0)
      ∧ (dom KM' ⊆ dom I')
      ∧ (n0 ∉ dom KM')  
      ∧ ([^op set] x ∈ dom I', FI I0 x) = ([^op set] x ∈ dom I', FI I' x)
      ∧ (keyset (FI I' n0) = keyset (FI I0 n0) ∖ (A ∪ R))
      ∧ (∀ x, x ∈ dom KM' → keyset (FI I' x) = keyset (FI I0 x) ∪ (KM' !!! x))
      ∧ (∀ x, x ∈ dom I' ∖ dom KM' → x ≠ n0 → 
                          keyset (FI I' x) = keyset (FI I0 x))
      ∧ (∀ x, x ∈ dom I' → es_outset_rel x (es' !!! x) (FI I' x))).
  Proof.
    intros FI es' es_n0 S. apply marking_flow_upd_rec_ind; try done.
    - clear I KM A R. intros I KM A R HR ES_rank ES_cl ES_upd FN_n0 A_disj_R 
        A_union_R VI Domm_I Outflow_I Outflow_I0_n0 Insets_n0 Outsets_n0 
        Outset_n0 Outflow_I_n0_1 Outflow_I_n0_2 n0_in_I Dom_I_eq_I0 
        Dom_KM_in_I n0_notin_KM Heq KS_I0 KS_KM [= -> ->].
      assert (keyset (FI I' n0) = keyset (FI I0 n0) ∖ (A ∪ R)) as H'.
      { assert (R = ∅) as ->.
        { apply leibniz_equiv. by apply elements_empty_inv. }
        rewrite union_empty_r_L. 
        unfold keyset. 
        rewrite Insets_n0 Outsets_n0.
        clear; set_solver. }
      assert (∀ x, x ∈ dom I' → es_outset_rel x (es' !!! x) (FI I' x)) as H''.
      { intros x Hx. destruct (decide (x = n0)) as [-> | Hxn0].
        - rewrite /es'. rewrite lookup_total_insert.
          split.
          + intros Hk. assert (k ∈ outsets (FI I' n0)) as Hk'.
            { admit. }
            rewrite Outsets_n0 in Hk'.
            rewrite elem_of_union in Hk'.
            destruct Hk' as [Hk' | Hk'].
            * admit.
            * by apply Outflow_I_n0_1.
          + intros [Hes_n0' k_in_inset]. 
            destruct (decide (k ∈ dom es_n0)) as [Hk | Hk].
            * assert (es_n0 !! k = Some n') as Hes_n0.
              { admit. }
              assert (inset K (FI I' n0) n0 = inset K (FI I0 n0) n0) as Inset_n0.
              { admit. }
              rewrite Inset_n0 in k_in_inset.
              destruct (Outflow_I0_n0 n' k) as [_ H''].
              apply Outset_n0; apply H''. split; try done.
            * assert (k ∈ A) as k_in_A.
              { admit. }
              apply Outflow_I_n0_2; try done.
        - subst es'. rewrite lookup_total_insert_ne; try done.
          apply Outflow_I. clear -Hx Hxn0; set_solver. }
      split; try done.
    - clear I KM A R. intros I KM A R k ks HR II nk Hflowk KMM HInd. 
      intros ES_rank ES_cl ES_upd FN_n0 A_disj_R 
        A_union_R VI Domm_I Outflow_I Outflow_I0_n0 Insets_n0 Outsets_n0 
        Outset_n0 Outflow_I_n0_1 Outflow_I_n0_2 n0_in_I Dom_I_eq_I0 
        Dom_KM_in_I n0_notin_KM Heq KS_I0 KS_KM Hflow.  
      assert (k ∈ R) as k_in_R.
      { apply elem_of_elements. rewrite HR. clear; set_solver. }
      assert ((es' !!! n0) !! k ≠ None) as FN_n0_k.
      { subst es'. rewrite lookup_total_insert.
        apply FN_n0; try done. }
      assert (A ∪ {[k]} ∪ (R ∖ {[k]}) = A ∪ R) as H'.
      { assert (k ∉ A) as H'.
        { clear -A_disj_R k_in_R. set_solver. }
        apply set_eq_subseteq. split.
        - clear -H' k_in_R. set_solver.
        - clear -H' k_in_R. intros x Hx.
          destruct (decide (x = k)) as [-> |Hxk].
          + set_solver.
          + set_solver. }
      rewrite H' in HInd; clear H'.
      assert (n0 ∈ dom es) as n0_in_es.
      { destruct ES_cl as [H' _]. by rewrite H'. }
      pose proof es_closed_upd n0 es es_n0' I n0_in_es ES_upd ES_cl as ES_cl'. 
      pose proof es_rank_upd n0 es es_n0' rank ES_upd ES_rank as ES_rank'.
      
      assert (∀ x, x ∈ dom I ∖ {[n0]} → 
                    es_outset_rel x (es' !!! x) (FI I x)) as Outflow_I'.
      { intros x. rewrite elem_of_difference. intros [Hx1 Hx2].
        subst es'. rewrite lookup_total_insert_ne. 
        apply Outflow_I. all: clear -Hx1 Hx2; set_solver. }
      assert (∀ n' k', k' ∈ outset K (FI I n0) n' → 
                (es' !!! n0) !! k' = Some n' ∧ k' ∈ inset K (FI I n0) n0) as H'.
      { subst es'. rewrite lookup_total_insert; try done. }
      assert (k ∈ inset K (I !!! n0) n0) as H''.
      { assert (k ∈ S) as k_in_S.
        { rewrite A_union_R. clear -k_in_R. set_solver. }
        subst S.
        assert (inset K (I !!! n0) n0 = inset K (I0 !!! n0) n0) as H''.
        { admit. }
        rewrite H''. clear -k_in_S; set_solver. }
      destruct ((es' !!! n0) !! k) as [n1 |] eqn: FN_n0_k'; try done.
      pose proof marking_flow_updk_summary rank n0 es' I k (Some (II, nk)) n1
        ES_rank' ES_cl' FN_n0_k' VI Domm_I Outflow_I' H' H'' n0_in_I Hflowk
        as [? [? [[= <- <-] Hsum]]].
      clear H' H''.  
      destruct Hsum as [Dom_II_eq_I [n0_neq_nk [n0_in_II [nk_in_II 
        [Domm_II [Heq' [Outflow_II [Inset_II_n0 [Outset_II_n0 [Outset_n0' 
        [Outflow_I_n0_1' [KS_nk [KS_II_n0 KS_II ]]]]]]]]]]]]].
      assert (([^op set] x ∈ dom I, FI I0 x) =
                ([^op set] x ∈ dom I, FI II x)) as Heq''.
      { rewrite Heq. by unfold FI. }          
      rewrite Dom_II_eq_I in HInd.
      assert (outsets (FI II n0) = outsets (FI I n0) ∪ {[k]}) as Outsets_II.
      { admit. }
      assert (∀ n', outset _ (FI I n0) n' ⊆ outset _ (FI II n0) n') as Outset_sub.
      { intros n'. destruct (decide (n' = n1)) as [-> | Hn'].
        * rewrite Outset_II_n0. clear -Outset_n0. set_solver.
        * rewrite <-Outset_n0'; try done. }
      assert (dom KMM = dom KM ∪ {[nk]}) as Dom_KMM.
      { rewrite /KMM. apply dom_add_k. }
      assert (∀ x, x ≠ nk → KMM !!! x = KM !!! x) as KMM_x.
      { rewrite /KMM. apply lookup_add_k_ne. }
      assert (KMM !!! nk = KM !!! nk ∪ {[k]}) as KMM_nk.
      { rewrite /KMM. apply lookup_add_k. }

      apply HInd; clear HInd; try done.
      + unfold es_closed. rewrite Dom_II_eq_I. apply ES_cl.   
      + intros k' Hk'. apply FN_n0.
        clear -Hk'; set_solver.
      + clear -A_disj_R k_in_R. set_solver.
      + by rewrite <-Heq''; rewrite Heq.
      + by rewrite <-Dom_II_eq_I.
      + (* Outflow minus n0 *) admit. 
      + admit.
      + rewrite Outsets_II. rewrite Outsets_n0. clear; set_solver.
      + intros n' k' Hk'. apply Outset_sub. by apply Outset_n0.
      + rewrite /es' in Outflow_I_n0_1'. 
        rewrite lookup_total_insert in Outflow_I_n0_1'.
        try done.
      + intros n' k'. rewrite elem_of_union.
        intros [Hk' | Hk'].
        * intros [Hes_n0' k'_in_inset]. 
          apply (Outflow_I_n0_2 n') in Hk'.
          clear -Outset_sub Hk'. set_solver.
          split; try done. unfold FI. rewrite <-Inset_II_n0. done.
        * assert (k' = k) as -> by (clear -Hk'; set_solver).
          intros [Hes_n0' k'_in_inset].
          assert (n' = n1) as ->.
          { subst es'. rewrite lookup_total_insert in FN_n0_k'. 
            rewrite FN_n0_k' in Hes_n0'.
            by inversion Hes_n0'. }
          rewrite Outset_II_n0. clear; set_solver.
      + rewrite Dom_KMM. rewrite Dom_II_eq_I in nk_in_II. 
        clear -Dom_KM_in_I nk_in_II. set_solver.
      + rewrite Dom_KMM. clear -n0_notin_KM n0_neq_nk.
        set_solver.
      + intros x. destruct (decide (x = nk)) as [-> | Hx].
        * intros Hnk. rewrite KMM_nk.
          unfold FI. rewrite KS_nk. 
          unfold FI in KS_I0.
          destruct (decide (nk ∈ dom KM)) as [Hnk1 | Hnk1].
          ** rewrite KS_I0; try done. clear; set_solver.
          ** assert (KM !!! nk = ∅) as H'.
             { rewrite lookup_total_alt. rewrite not_elem_of_dom in Hnk1.
               rewrite Hnk1. try done. }
             rewrite H'. unfold FI in KS_KM.
             rewrite KS_KM; try done. clear; set_solver.
             clear -Hnk1 nk_in_II Dom_II_eq_I.
             set_solver.
        * rewrite Dom_KMM. rewrite elem_of_union.
          intros [Hx1 | Hx1].
          ** rewrite KMM_x; try done.
             assert (x ∈ dom II ∖ {[n0; nk]}) as H'.
             { rewrite Dom_II_eq_I. clear -Hx Hx1 Dom_KM_in_I n0_notin_KM.
               set_solver. }
             rewrite KS_II; try done.
             apply KS_I0; try done.
          ** clear -Hx Hx1; set_solver.
      + rewrite Dom_KMM. intros x Hx1 Hx2.
        assert (x ∈ dom II ∖ {[n0; nk]}) as H'.
        { rewrite Dom_II_eq_I. clear -Hx2 Hx1 Dom_KM_in_I n0_notin_KM.
          set_solver. }
        rewrite KS_II; try done.
        apply KS_KM; try done. clear -Hx1; set_solver.
  Admitted.

  Lemma marking_flow_upd_summary rank n0 es I0 es_n0' res:
    let FI := λ I x, I !!! x in
    let es' := <[n0 := es_n0']> es in
    let es_n0 := es !!! n0 in
    let S := (dom es_n0' ∖ dom es_n0) ∩ inset K (I0 !!! n0) n0 in
    (es_rank_rel es rank) →
    (es_closed es I0) →
    (es_marking_upd es_n0 es_n0') →
    (✓ ([^op set] x ∈ dom I0, FI I0 x)) →
    (∀ x, x ∈ dom I0 → domm (FI I0 x) = {[x]}) →
    (∀ x, x ∈ dom I0 → es_outset_rel x (es !!! x) (FI I0 x)) →
    (n0 ∈ dom I0) →
    marking_flow_upd es n0 I0 es_n0' = res →
    ∃ I' (KM': gmap Node (gset K)),
        ((res = Some (I', KM'))
      ∧ (dom I' = dom I0)
      ∧ (dom KM' ⊆ dom I')
      ∧ (n0 ∉ dom KM')  
      ∧ ([^op set] x ∈ dom I', FI I0 x) = ([^op set] x ∈ dom I', FI I' x)
      ∧ (keyset (FI I' n0) = keyset (FI I0 n0) ∖ S)
      ∧ (∀ x, x ∈ dom KM' → keyset (FI I' x) = keyset (FI I0 x) ∪ (KM' !!! x))
      ∧ (∀ x, x ∈ dom I' ∖ dom KM' → x ≠ n0 → 
                          keyset (FI I' x) = keyset (FI I0 x))
      ∧ (∀ x, x ∈ dom I' → es_outset_rel x (es' !!! x) (FI I' x))).
  Proof.
    intros FI es' es_n0 S ES_rank ES_cl ES_upd VI0 Domm_I0 
      Outflow_I0 n0_in_I0 Hflow.
    unfold marking_flow_upd in Hflow.
    assert (es_n0 = es !!! n0) as Def_es_n0.
    { try done. }
    assert (S = (dom es_n0' ∖ dom es_n0) ∩ inset K (I0 !!! n0) n0) as Def_S.
    { try done. }
    rewrite <-Def_es_n0 in Hflow.
    rewrite <-Def_S in Hflow.
    assert (n0 ∈ dom es) as n0_in_es.
    { destruct ES_cl as [H' _]. by rewrite H'. }
    pose proof es_closed_upd n0 es es_n0' I0 n0_in_es ES_upd ES_cl as ES_cl'. 
    pose proof es_rank_upd n0 es es_n0' rank ES_upd ES_rank as ES_rank'. 
    assert (∀ k : K, k ∈ S → (es' !!! n0) !! k ≠ None) as FN_n0.
    { intros k Hk. rewrite Def_S in Hk. rewrite elem_of_intersection in Hk.
      destruct Hk as [Hk _]. rewrite elem_of_difference in Hk.
      destruct Hk as [Hk _]. rewrite elem_of_dom in Hk.
      rewrite /es'. rewrite lookup_total_insert.
      destruct Hk as [n Hk]. rewrite Hk. try done. }
    pose proof marking_flow_upd_rec_defined rank es' n0 I0 ∅ ∅ S ES_rank' 
      ES_cl' FN_n0 n0_in_I0 as Hflow'.
    destruct (marking_flow_upd_rec es' n0 I0 ∅ ∅ S) as [ (I', KM') | ] eqn:Hflow''; 
      try done. 
    assert (∅ ## S) as H1'. { clear; set_solver. }
    assert (dom I0 = dom I0) as H1''. { try done. }
    assert (dom (∅: gmap Node (gset K)) ⊆ dom I0) as H2'. 
    { clear; set_solver. }
    assert (n0 ∉ dom (∅: gmap Node (gset K))) as H2''. 
    { clear; set_solver. }
    assert (([^op set] x ∈ dom I0, FI I0 x) = 
      ([^op set] x ∈ dom I0, FI I0 x)) as H3'.
    { try done. }
    assert (keyset (FI I0 n0) = keyset (FI I0 n0) ∖ ∅) as H3''.
    { clear; set_solver. }
    assert (∀ x, x ∈ dom (∅: gmap Node (gset K)) → 
                keyset (FI I0 x) = keyset (FI I0 x) ∪ 
                  ((∅: gmap Node (gset K)) !!! x)) as H4'.
    { clear; set_solver. }              
    assert (∀ x, x ∈ dom I0 ∖ dom (∅: gmap Node (gset K)) → 
                  x ≠ n0 → 
                    keyset (FI I0 x) = keyset (FI I0 x)) as H4''.
    { clear; set_solver. }
    assert ((∀ x, x ∈ dom I0 ∖ {[n0]} → es_outset_rel x (es !!! x) (FI I0 x)))
      as Outflow_I0'.
    { intros x Hx; apply Outflow_I0. clear -Hx; set_solver. }
    assert (es_outset_rel n0 (es !!! n0) (FI I0 n0)) as Outflow_I0_n0.
    { by apply Outflow_I0. }
    assert (insets (FI I0 n0) = insets (FI I0 n0)) as H5'.
    { done. }
    assert (outsets (FI I0 n0) = outsets (FI I0 n0) ∪ ∅) as H5''.
    { clear; set_solver. }
    assert ((dom es_n0' ∖ dom (es !!! n0)) ∩ inset K (I0 !!! n0) n0 = ∅ ∪ S) 
      as H6''.
    { subst S. clear; set_solver. }
    assert (∀ n', outset K (FI I0 n0) n' ⊆ outset K (FI I0 n0) n') as H7'.
    { clear; set_solver. }
    assert (∀ n' k, k ∈ outset K (FI I0 n0) n' → 
                      es_n0' !! k = Some n' ∧ k ∈ inset _ (FI I0 n0) n0) as H7''.
    { intros n' k Hk. pose proof (Outflow_I0_n0 n' k) as H'.
      apply H' in Hk. destruct Hk as [Hk1 Hk2].
      split; try done. admit. }
    assert (∀ n' k, k ∈ (∅: gset K) →
                      es_n0' !! k = Some n' ∧ k ∈ inset _ (FI I0 n0) n0 →
                        k ∈ outset _ (FI I0 n0) n') as H8'.
    { intros n' k Hk. clear -Hk; set_solver. }                                      
    rewrite /es' in FN_n0. rewrite lookup_total_insert in FN_n0.
    pose proof marking_flow_upd_invariants rank n0 es es_n0' I0 ∅ ∅ S I' KM' I0
      ES_rank ES_cl ES_upd FN_n0 H1' H6'' VI0 Domm_I0 Outflow_I0' Outflow_I0_n0 
      H5' H5'' H7' H7'' H8'  n0_in_I0 H1'' H2' H2'' H3' H4' H4'' Hflow''
      as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 [HInv6 [HInv7 HInv8]]]]]]].
    exists I', KM'. split; try done.
    rewrite <-Hflow. rewrite <-Hflow''. done.
    assert (∅ ∪ S = S) as H8''. { clear; set_solver. }
    rewrite H8'' in HInv5. try done.
  Admitted.   
  
End marking_flow_upd.