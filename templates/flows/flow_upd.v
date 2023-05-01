Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

Section list_flow_upd.
  Context `{Countable K}.
  Open Scope ccm_scope.
  
  Parameter KS : gset K.
  
  Definition edgeset (es: gmap Node (gmap Node (gset K))) n1 n2 : gset K :=
    (es !!! n1) !!! n2.

  Definition find_next (esn: gmap Node (gset K)) (k: K) : option Node := 
    let f := λ (n': Node) (esn': gset K) res, 
              match res with
              | Some n'' => Some n''
              | None => if (bool_decide (k ∈ esn'))
                        then Some n'
                        else None end in
    map_fold f (None: option Node) esn.

  Definition edge_rank_rel (es: gmap Node (gmap Node (gset K))) 
    (rank: Node → nat) :=
    ∀ n1 n2, edgeset es n1 n2 ≠ ∅ → rank n1 < rank n2. 

  Definition outflow_edge_rel (n: Node) (esn: gmap Node (gset K)) In :=
    ∀ n', outset K In n' = esn !!! n' ∩ inset K In n.

  Function flow_updk_rec (es: gmap Node (gmap Node (gset K)))
    (I: gmap Node (multiset_flowint_ur K)) (k: K) 
    (n: Node) (R: gset Node)
    (I': gmap Node (multiset_flowint_ur K))
    {measure size R} : option (gmap Node (multiset_flowint_ur K) * Node) :=
  match (bool_decide (n ∈ R)) with
  | false => None
  | true =>
    match find_next (es !!! n) k with
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
      flow_updk_rec es I k n1 (R ∖ {[n]}) II' end end.
  intros es I k n R I' Hbool n1 ?.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.
  
  Definition flow_updk_post (I II: gmap Node (multiset_flowint_ur K)) :=
    let f := λ m1 m2,
              match m1, m2 with 
              | Some m1, Some m2 => Some m2
              | None, Some m2 => Some m2
              | Some m1, None => Some m1
              | None, None => None end in
    merge f I II.
  

  Definition flow_updk es I k n0 :=
    match find_next (es !!! n0) k with
    | None => None
    | Some n1 =>
      let In0 := I !!! n0 in
      let In0' := outflow_insert_set In0 n1 {[k]} in
      let In1 := I !!! n1 in
      let In1' := inflow_insert_set In1 n1 {[k]} in
      let I' := <[n1 := In1']> ({[n0 := In0']}) in
      match flow_updk_rec es I k n1 (dom I ∖ {[n0]}) I' with
      | Some (II, nk) =>
        let II' := flow_updk_post I II in
        Some (II', nk)
      | None => None end end.

    
  Lemma flow_updk_rec_defined rank es I k n R I':
    (edge_rank_rel es rank) →
    (∀ n1 n2, edgeset es n1 n2 ≠ ∅ → n2 ∈ dom I) →
    (n ∈ dom I') →
    (dom I = R ∪ dom I') →
    (R ∩ dom I' = {[n]}) →
    (∀ x, x ∈ dom I' → rank x ≤ rank n) →
      flow_updk_rec es I k n R I' ≠ None.
  Proof.
    apply flow_updk_rec_ind; try done.
    - clear n R. intros n R I0 n_notin_R.
      rewrite bool_decide_eq_false in n_notin_R.
      intros _ _ _ _ ? _; set_solver.
    - clear n R. intros n R I0 n_in_R.
      rewrite bool_decide_eq_true in n_in_R.
      intros n1 FN_n In In' In1 In1' II I0' HInd EdgeRank
        ES_I n_in_I0 Dom_I R_inter_I0 Rank_I0.
      assert (edgeset es n n1 ≠ ∅) as ES_n_n1. { admit. }
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof EdgeRank n n1 ES_n_n1 as H'.
        intros n1_in_I0. apply Rank_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[n1]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { by pose proof ES_I n n1 ES_n_n1. }  
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
      + pose proof EdgeRank n n1 ES_n_n1 as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Rank_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; lia.
  Admitted.
      
      
      

  Lemma flow_updk_invariants rank es I k n R I' II' nk n0:
    let FI := λ I x, I !!! x in 
      (edge_rank_rel es rank) →
      (✓ ([^op set] x ∈ dom I, FI I x)) →
      (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
      (∀ n1 n2, edgeset es n1 n2 ≠ ∅ → n2 ∈ dom I) →
      (∀ x, x ∈ dom I → outflow_edge_rel x (es !!! x) (FI I x)) →
      (∀ x, x ∈ dom I' ∖ {[n]} → outflow_edge_rel x (es !!! x) (FI I' x)) →
      (n0 ∈ dom I') → (n ∈ dom I') → (n0 ≠ n) →
      (∀ x, x ∈ dom I' → rank x ≤ rank n) →
      (∀ x, x ∈ dom I' ∖ {[n0]} → rank n0 < rank x) →
      (FI I' n = inflow_insert_set (FI I n) n {[k]}) →
      (dom I' ⊆ dom I) →
      (∀ x, x ∈ dom I' ∖ {[n0; n]} → keyset (FI I' x) = keyset (FI I x)) →
      (keyset (FI I' n0) = keyset (FI I n0) ∖ {[k]}) →
      (k ∈ insets (FI I n)) →
      (∀ x, x ∈ dom I' → domm (FI I' x) = {[x]}) →
      ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
      flow_updk_rec es I k n R I' = Some (II', nk) →
          ((([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x))
          ∧ (keyset (FI II' nk) = keyset (FI I nk) ∪ {[k]})
          ∧ (keyset (FI II' n0) = keyset (FI I n0) ∖ {[k]})
          ∧ (∀ x, x ∈ dom II' ∖ {[n0; nk]} → keyset (FI II' x) = keyset (FI I x))
          ∧ (∀ x, x ∈ dom II' → outflow_edge_rel x (es !!! x) (FI II' x))
          ∧ (dom II' ⊆ dom I)
          ∧ (n0 ≠ nk)
          ∧ (n0 ∈ dom II')
          ∧ (nk ∈ dom II')
          ∧ (∀ x, x ∈ dom II' → domm (FI II' x) = {[x]})).
  Proof.
    (*
    intros FI. apply flow_updk_rec_ind.
    - intros; try done.
    - clear n R. intros n R I0 n_in_R FN_n EdgeRank VI Domm_I ES_I 
        Outflow_I Outflow_I0 n0_in_I0 n_in_I0 n0_neq_n Rank_I0 Rank_n0 
        Def_I0_n Dom_I0_in_I KS_I0 KS_n0 k_in_Insn Domm_I0 Heq [= -> ->]. 
      repeat split; try done.
      + rewrite Def_I0_n.
        rewrite /keyset. rewrite inflow_insert_set_insets.
        rewrite inflow_insert_set_outsets.
        assert (k ∉ outsets (FI I nk)) as H'.
        { admit. }
        clear -H'; set_solver.
      + intros x Hx. destruct (decide (x = nk)) as [-> | Hxn].
        * intros n'. rewrite Def_I0_n.
          rewrite inflow_insert_set_outset_ne.
          rewrite inflow_insert_set_inset.
          assert (nk ∈ dom I) as H' by (clear -Hx Dom_I0_in_I; set_solver).
          pose proof Outflow_I nk H' n' as H''.
          assert (k ∉ (es !!! nk) !!! n') as Hk.
          { admit. }
          assert (k ∉ outset K (FI I nk) n') as H'''.
          { clear -H'' Hk. set_solver. }
          clear -Hk H'' H'''; set_solver.
        * assert (x ∈ dom II' ∖ {[nk]}) as Hx' by set_solver.
          by apply Outflow_I0.      
    - clear n R. intros n R I0 n_in_R n1 FN_n.
      intros In In' In1 In1' II I0' HInd EdgeRank VI Domm_I ES_I Outflow_I 
        Outflow_I0 n0_in_I0 n_in_I0 n0_neq_n Rank_I0 Rank_n0 Def_I0_n 
        Dom_I0_in_I KS_I0 KS_n0 k_in_Insn Domm_I0 Heq Hflow.
      assert (edgeset es n n1 ≠ ∅) as ES_n_n1. { admit. }
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof EdgeRank n n1 ES_n_n1 as H'.
        intros n1_in_I0. apply Rank_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { by pose proof ES_I n n1 ES_n_n1. }  
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
            unfold outflow_edge_rel. intros n'.
            rewrite outflow_insert_set_inset.
            assert (n ∈ dom I) as H' by 
              (clear -n_in_I0 Dom_I0_in_I; set_solver).
            destruct (decide (n' = n1)) as [-> | Hn'n].
            * rewrite outflow_insert_set_outset.
              rewrite /In.
              pose proof Outflow_I n H' n1 as H''.
              unfold FI in Def_I0_n. rewrite Def_I0_n.
              rewrite inflow_insert_set_outset_ne.
              rewrite inflow_insert_set_inset.
              unfold FI in H''.
              assert (k ∈ (es !!! n) !!! n1) as Hk.
              { admit. }
              clear -Hk H''. set_solver.
            * rewrite outflow_insert_set_outset_ne; try done.
              rewrite /In.
              pose proof Outflow_I n H' n' as H''.
              rewrite /FI in H''. rewrite /FI in Def_I0_n.
              rewrite Def_I0_n.
              rewrite inflow_insert_set_outset_ne.
              rewrite inflow_insert_set_inset.
              assert (k ∉ (es !!! n) !!! n') as Hk.
              { admit. }
              assert (k ∉ outset K (FI I n) n') as H'''.
              { clear -H'' Hk. set_solver. }
              clear -Hk H''. set_solver.
          + rewrite lookup_total_insert_ne; try done.
            apply Outflow_I0. clear -Hx Hxn; set_solver.
        - clear -Hx Hx2; set_solver. }
      { rewrite Dom_I0'. clear -n0_in_I0.
        set_solver. }
      { rewrite Dom_I0'. clear -Dom_I0_in_I n1_in_I. set_solver. }
      { pose proof EdgeRank n n1 ES_n_n1 as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        - apply Rank_I0 in Hx. clear -Hx H'. lia.
        - assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; lia. }
      { rewrite Dom_I0'. intros x. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        - apply Rank_n0. clear -Hx1 Hx2; set_solver.
        - assert (x = n1) as -> by (clear -Hx1; set_solver). 
          pose proof EdgeRank n n1 ES_n_n1 as H'.
          assert (rank n0 ≤ rank n) as H''.
          { by apply Rank_I0. }
          clear -H' H''. lia. }    
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
      rewrite Dom_I0'. 
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
        as Hpose.
  *)      
  Admitted.
  
  Lemma flow_updk_post_dom I II I' :
    (dom II ⊆ dom I) →
    I' = flow_updk_post I II →
      dom I' = dom I.
  Proof.
    intros Hdom Hflow.
    assert (dom I' ⊆ dom I).
    { intros x. rewrite elem_of_dom.
      subst I'. intros [m Hx].
      unfold flow_updk_post in Hx.
      rewrite lookup_merge in Hx.
      unfold diag_None in Hx.
      destruct (I !! x) as [mI |] eqn: HIx.
      - rewrite elem_of_dom; try done.
      - destruct (II !! x) as [mII |] eqn: HIIx; try done.
        apply Hdom. rewrite elem_of_dom; try done. }
    assert (dom I ⊆ dom I').
    { intros x. rewrite !elem_of_dom.
      intros [mx Hx]. subst I'.
      unfold flow_updk_post.
      rewrite lookup_merge.
      unfold diag_None.
      rewrite Hx.
      destruct (II !! x) as [mII |]; try done. }
    set_solver.      
  Qed.          

  Lemma flow_updk_post_intfEq I II I' :
    let FI := λ I x, I !!! x in
    (dom II ⊆ dom I) →
    (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x)) → 
    I' = flow_updk_post I II →
      (([^op set] x ∈ dom I, FI I x) = ([^op set] x ∈ dom I, FI I' x)).
  Proof.
  Admitted.

  Lemma flow_updk_post_lookup I II I' :
    (dom II ⊆ dom I) →
    I' = flow_updk_post I II →
      (∀ x, x ∈ dom II → I' !! x = II !! x).
  Proof.
    intros Dom_II_in_I Hflow. intros x Hx.
    rewrite Hflow. unfold flow_updk_post.
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

  Lemma flow_updk_post_lookup_total I II I' :
    (dom II ⊆ dom I) →
    I' = flow_updk_post I II →
      (∀ x, x ∈ dom II → I' !!! x = II !!! x).
  Proof.
    intros ? H' ? ?; rewrite !lookup_total_alt.
    rewrite (flow_updk_post_lookup _ _ _ _ H'); try done.
  Qed.  

  Lemma flow_updk_post_lookup_ne I II I' :
    (dom II ⊆ dom I) →
    I' = flow_updk_post I II →
      (∀ x, x ∈ dom I ∖ dom II → I' !! x = I !! x).
  Proof.
    intros Dom_II_in_I Hflow. intros x Hx.
    rewrite elem_of_difference in Hx.
    destruct Hx as [Hx1 Hx2].
    rewrite Hflow. unfold flow_updk_post.
    rewrite lookup_merge. unfold diag_None.
    rewrite elem_of_dom in Hx1.
    destruct Hx1 as [mI Hx1].
    rewrite Hx1.
    rewrite not_elem_of_dom in Hx2.
    by rewrite Hx2.
  Qed.  

  Lemma flow_updk_post_lookup_total_ne I II I' :
    (dom II ⊆ dom I) →
    I' = flow_updk_post I II →
      (∀ x, x ∈ dom I ∖ dom II → I' !!! x = I !!! x).
  Proof.
    intros ? H' ? ?; rewrite !lookup_total_alt.
    rewrite (flow_updk_post_lookup_ne _ _ _ _ H'); try done.
  Qed.
  
  Lemma flow_updk_post_summary (es: gmap Node (gmap Node (gset K)))
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
    (∀ x, x ∈ dom I → outflow_edge_rel x (es !!! x) (FI I x)) →
    (∀ x, x ∈ dom II → outflow_edge_rel x (es !!! x) (FI II x)) →
    I' = flow_updk_post I II →
          ((dom I' = dom I)
        ∧ (n0 ∈ dom I')
        ∧ (nk ∈ dom I')  
        ∧ (∀ x, x ∈ dom I' → domm (FI I' x) = {[x]})  
        ∧ (([^op set] x ∈ dom I, FI I x) = ([^op set] x ∈ dom I, FI I' x))
        ∧ (keyset (FI I' nk) = keyset (FI I nk) ∪ {[k]})
        ∧ (keyset (FI I' n0) = keyset (FI I n0) ∖ {[k]})
        ∧ (∀ x, x ∈ dom I' ∖ {[n0; nk]} → keyset (FI I' x) = keyset (FI I x))
        ∧ (∀ x, x ∈ dom I' → outflow_edge_rel x (es !!! x) (FI I' x))).
  Proof.
    intros FI Dom_II_in_I n0_in_II nk_in_II Domm_I Domm_II Heq 
      KS_nk KS_n0 KS_II Outflow_I Outflow_II Hflow.
    pose proof flow_updk_post_dom I II I' Dom_II_in_I Hflow as Dom_I'_eq_I.
    pose proof flow_updk_post_intfEq I II I' Dom_II_in_I Heq Hflow as Heq'.
    repeat split; try done.
    - rewrite Dom_I'_eq_I. by apply Dom_II_in_I.
    - rewrite Dom_I'_eq_I. by apply Dom_II_in_I.
    - intros x Hx.  
      destruct (decide (x ∈ dom II)) as [Hx1 | Hx1].
      + unfold FI.
        rewrite (flow_updk_post_lookup_total _ _ _ _ Hflow); try done.
        apply Domm_II; try done.
      + unfold FI.
        rewrite (flow_updk_post_lookup_total_ne _ _ _ _ Hflow); try done.
        apply Domm_I; try done.
        all: clear -Dom_I'_eq_I Hx1 Hx; set_solver.
    - assert (FI I' nk = FI II nk) as H'.
      { unfold FI.
        by rewrite (flow_updk_post_lookup_total _ _ _ _ Hflow). }
      rewrite H'; try done.
    - assert (FI I' n0 = FI II n0) as H'.
      { unfold FI. 
        by rewrite (flow_updk_post_lookup_total _ _ _ _ Hflow). }
      rewrite H'; try done.
    - intros x. rewrite elem_of_difference.
      intros [Hx1 Hx2].
      destruct (decide (x ∈ dom II)) as [Hx3 | Hx3].
      + unfold FI.
        rewrite (flow_updk_post_lookup_total _ _ _ _ Hflow); try done.
        apply KS_II. clear -Hx3 Hx2; set_solver.
      + unfold FI.
        rewrite (flow_updk_post_lookup_total_ne _ _ _ _ Hflow); try done.
        rewrite Dom_I'_eq_I in Hx1. clear -Hx1 Hx3; set_solver.
    - intros x Hx.  
      destruct (decide (x ∈ dom II)) as [Hx1 | Hx1].
      + unfold FI.
        rewrite (flow_updk_post_lookup_total _ _ _ _ Hflow); try done.
        apply Outflow_II; try done.
      + unfold FI.
        rewrite (flow_updk_post_lookup_total_ne _ _ _ _ Hflow); try done.
        apply Outflow_I; try done.
        by rewrite <-Dom_I'_eq_I.
        rewrite Dom_I'_eq_I in Hx. clear -Hx1 Hx; set_solver.
  Qed.

  Lemma flow_updk_defined rank es I k n0:
(*     let FI := λ I x, I !!! x in  *)
    (edge_rank_rel es rank) →
    (∀ n1 n2, edgeset es n1 n2 ≠ ∅ → n2 ∈ dom I) →
    (n0 ∈ dom I) →    
    (find_next (es !!! n0) k ≠ None) →
    flow_updk es I k n0 ≠ None.
  Proof.
    intros EdgeRank ES_I n0_in_I FN_n0.
    unfold flow_updk.
    destruct (find_next (es !!! n0) k) as [n1 |]; try done.
    set In1 := inflow_insert_set (I !!! n1) n1 {[k]}.
    set In0 := outflow_insert_set (I !!! n0) n1 {[k]}.
    set I': gmap Node (multiset_flowint_ur K) := {[n1 := In1; n0 := In0]}.
    assert (In1 = inflow_insert_set (I !!! n1) n1 {[k]}) as Def_In1.
    { try done. }
    assert (In0 = outflow_insert_set (I !!! n0) n1 {[k]}) as Def_In0.
    { try done. }
    assert (I' = {[n1 := In1; n0 := In0]}) as Def_I'.
    { try done. }
    assert (dom I' = {[n0; n1]}) as Dom_I' by set_solver.
    assert (n1 ∈ dom I') as n1_in_I' by set_solver.
    assert (n1 ∈ dom I) as n1_in_I.
    { apply (ES_I n0). admit. }
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
      set_solver. }  
    assert ((dom I ∖ {[n0]}) ∩ dom I' = {[n1]}) as H''.
    { rewrite Dom_I'. set_solver. }
    assert (rank n0 < rank n1) as Rank_n0_n1.
    { assert (edgeset es n0 n1 ≠ ∅) as Hes.
      { admit. } 
      by pose proof EdgeRank n0 n1 Hes. }
    assert (∀ x : Node, x ∈ dom I' → rank x ≤ rank n1) as Rank_I0.
    { rewrite Dom_I'. intros x; rewrite elem_of_union.
      intros [Hx | Hx].
      - assert (x = n0) as -> by set_solver.
        lia.
      - assert (x = n1) as -> by set_solver.
        lia. }
    pose proof flow_updk_rec_defined rank es I k n1 (dom I ∖ {[n0]}) I'
      EdgeRank ES_I n1_in_I' H' H'' Rank_I0 as Hdef.
    destruct (flow_updk_rec es I k n1 (dom I ∖ {[n0]}) I') 
      as [(II,nk)|]; try done.
  Admitted.  

  Lemma flow_updk_summary rank es I k n0 res:
    let FI := λ I x, I !!! x in 
    (edge_rank_rel es rank) →
    (∀ n1 n2, edgeset es n1 n2 ≠ ∅ → n2 ∈ dom I) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
    (∀ x, x ∈ dom I → outflow_edge_rel x (es !!! x) (FI I x)) →
    (n0 ∈ dom I) →
    (find_next (es !!! n0) k ≠ None) →
    flow_updk es I k n0 = res →
      ∃ II' nk, 
        res = Some (II', nk)
      ∧ (dom II' = dom I)
      ∧ (n0 ≠ nk)
      ∧ (n0 ∈ dom II')
      ∧ (nk ∈ dom II')
      ∧ (∀ x, x ∈ dom II' → domm (FI II' x) = {[x]})
      ∧ (([^op set] x ∈ dom I, FI I x) = ([^op set] x ∈ dom I, FI II' x))
      ∧ (keyset (FI II' nk) = keyset (FI I nk) ∪ {[k]})
      ∧ (keyset (FI II' n0) = keyset (FI I n0) ∖ {[k]})
      ∧ (∀ x, x ∈ dom II' ∖ {[n0; nk]} → keyset (FI II' x) = keyset (FI I x))
      ∧ (∀ x, x ∈ dom II' → outflow_edge_rel x (es !!! x) (FI II' x)).
  Proof.
    intros FI EdgeRank ES_I VI Domm_I Outflow_I n0_in_I FN_n0 Hflow_upd.
    unfold flow_updk in Hflow_upd.
    destruct (find_next (es !!! n0) k) as [n1 |]; try done.
    set In1 := inflow_insert_set (I !!! n1) n1 {[k]}.
    set In0 := outflow_insert_set (I !!! n0) n1 {[k]}.
    set I': gmap Node (multiset_flowint_ur K) := {[n1 := In1; n0 := In0]}.
    assert (In1 = inflow_insert_set (I !!! n1) n1 {[k]}) as Def_In1.
    { try done. }
    assert (In0 = outflow_insert_set (I !!! n0) n1 {[k]}) as Def_In0.
    { try done. }
    assert (I' = {[n1 := In1; n0 := In0]}) as Def_I'.
    { try done. }
    rewrite <-Def_In1 in Hflow_upd.
    rewrite <-Def_In0 in Hflow_upd.
    rewrite <-Def_I' in Hflow_upd.
    assert (dom I' = {[n0; n1]}) as Dom_I' by set_solver.
    assert (n1 ∈ dom I') as n1_in_I' by set_solver.
    assert (n1 ∈ dom I) as n1_in_I.
    { apply (ES_I n0). admit. }
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
      set_solver. }  
    assert ((dom I ∖ {[n0]}) ∩ dom I' = {[n1]}) as H''.
    { rewrite Dom_I'. set_solver. }
    assert (rank n0 < rank n1) as Rank_n0_n1.
    { assert (edgeset es n0 n1 ≠ ∅) as Hes.
      { admit. } 
      by pose proof EdgeRank n0 n1 Hes. }
    assert (∀ x : Node, x ∈ dom I' → rank x ≤ rank n1) as Rank_I0.
    { rewrite Dom_I'. intros x; rewrite elem_of_union.
      intros [Hx | Hx].
      - assert (x = n0) as -> by set_solver.
        lia.
      - assert (x = n1) as -> by set_solver.
        lia. }
    pose proof flow_updk_rec_defined rank es I k n1 (dom I ∖ {[n0]}) I'
      EdgeRank ES_I n1_in_I' H' H'' Rank_I0 as Hdef.
    clear H' H''.
    destruct (flow_updk_rec es I k n1 (dom I ∖ {[n0]}) I') 
      as [ (II', nk) |] eqn: Hflow_upd1; try done.
    assert (∀ x, x ∈ dom I' ∖ {[n1]} → outflow_edge_rel x (es !!! x) (FI I' x)) 
      as Outflow_I'.
    { admit. }
    assert (n0 ∈ dom I') as n0_in_I'.
    { rewrite Dom_I'. clear; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0]} → rank n0 < rank x) as Rank_n0.
    { intros x. rewrite Dom_I'. rewrite elem_of_difference.
      rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2]; try done.
      assert (x = n1) as -> by set_solver. lia. }
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
    assert (([^op set] x ∈ dom I', FI I x) = 
                ([^op set] x ∈ dom I', FI I' x)) as Heq.
    { admit. }
    pose proof flow_updk_invariants rank es I k n1 (dom I ∖ {[n0]}) 
      I' II' nk n0 EdgeRank VI Domm_I ES_I Outflow_I Outflow_I' 
      n0_in_I' n1_in_I' n0_neq_n1 Rank_I0 Rank_n0 Def_I'_n 
      Dom_I'_in_I KS_I' KS_n0 k_in_Insn1 Domm_I' Heq Hflow_upd1 
      as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 
            [HInv6 [HInv7 [HInv8 [HInv9 HInv10]]]]]]]]].
    set III := flow_updk_post I II'.
    assert (III = flow_updk_post I II') as Def_III.
    { try done. }
    assert (dom II' ⊆ dom I) as Dom_II'_in_I.
    { admit. }
    pose proof flow_updk_post_summary es k I II' III n0 nk 
      Dom_II'_in_I HInv8 HInv9 Domm_I HInv10 HInv1 HInv2 HInv3 HInv4 Outflow_I 
      HInv5 Def_III 
      as [HInv1' [HInv2' [HInv3' [HInv4' [HInv5' [HInv6' 
      [HInv7' [HInv8' HInv9']]]]]]]].
    exists III, nk. rewrite <-HInv1'. repeat split; try done.
    by rewrite HInv1'.
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

  Function flow_upd_rec es n0 I (KM: gmap Node (gset K)) 
    (A R: gset K) {measure size R} :=
    match (elements R) with 
    | [] => Some (I, KM)
    | k :: _ => 
      match flow_updk es I k n0 with
      | Some (I', nk) =>
        let KM' := add_k KM nk k in
        flow_upd_rec es n0 I' KM' (A ∪ {[k]}) (R ∖ {[k]})
      | None => None end end.
  intros es n0 I KM A R k l HR ? I' nk -> ?.
  assert (k ∈ R).
  { apply elem_of_elements. rewrite HR. set_solver. }
  apply subset_size. set_solver.
  Defined.

  Definition flow_upd es n0 I0 (S: gset K) :=
    flow_upd_rec es n0 I0 ∅ ∅ S.

  Lemma flow_upd_rec_defined rank es n0 I KM A R :
    let FI := λ I x, I !!! x in 
    (edge_rank_rel es rank) →
    (∀ n1 n2, edgeset es n1 n2 ≠ ∅ → n2 ∈ dom I) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
    (∀ x, x ∈ dom I → outflow_edge_rel x (es !!! x) (FI I x)) →    
    (n0 ∈ dom I) →
    (∀ k, k ∈ R → find_next (es !!! n0) k ≠ None) →  
    flow_upd_rec es n0 I KM A R ≠ None.
  Proof.
    apply flow_upd_rec_ind; try done.
    - clear I KM A R. intros I KM A R k ks HR I' nk Hflow KM' HInd.
      intros FI EdgeRank ES_I VI Domm_I Outflow_I n0_in_I FN_n0.
      assert (k ∈ R) as k_in_R. 
      { clear -HR. rewrite <-elem_of_elements. rewrite HR; set_solver. }
      pose proof flow_updk_summary rank es I k n0 (Some (I', nk)) 
        EdgeRank ES_I VI Domm_I Outflow_I n0_in_I (FN_n0 k k_in_R)
        Hflow as [II' [nk' Hsum]].
      destruct Hsum as [[= <- <-] Hsum].
      destruct Hsum as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 
        [HInv6 [HInv7 [HInv8 [HInv9 HInv10]]]]]]]]].
      apply HInd; try done; clear HInd.
      + rewrite HInv1. try done.
      + rewrite HInv1. by rewrite <-HInv6. 
      + intros k' Hk'; apply FN_n0.
        clear -Hk'; set_solver.
    - clear I KM A R. intros I KM A R k ks HR Hflow.
      intros FI EdgeRank ES_I VI Domm_I Outflow_I n0_in_I FN_n0.
      assert (k ∈ R) as k_in_R.
      { clear -HR. rewrite <-elem_of_elements. rewrite HR; set_solver. }
      pose proof flow_updk_summary rank es I k n0 (None) 
        EdgeRank ES_I VI Domm_I Outflow_I n0_in_I (FN_n0 k k_in_R)
        Hflow as [II' [nk' Hsum]]. 
      destruct Hsum as [? Hsum].
      exfalso; try done.
  Qed.

  Lemma flow_upd_invariants rank es n0 I KM A R I' KM' I0:
    let FI := λ I x, I !!! x in
    (edge_rank_rel es rank) →
    (∀ n1 n2, edgeset es n1 n2 ≠ ∅ → n2 ∈ dom I) →
    (A ## R) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
    (∀ x, x ∈ dom I → outflow_edge_rel x (es !!! x) (FI I x)) →
    (n0 ∈ dom I) → (dom I = dom I0) →
    (dom KM ⊆ dom I) → (n0 ∉ dom KM) →
    (∀ k, k ∈ R → find_next (es !!! n0) k ≠ None) →
    (([^op set] x ∈ dom I, FI I0 x) = ([^op set] x ∈ dom I, FI I x)) →
    (keyset (FI I n0) = keyset (FI I0 n0) ∖ A) →
    (∀ x, x ∈ dom KM → keyset (FI I x) = keyset (FI I0 x) ∪ (KM !!! x)) →
    (∀ x, x ∈ dom I ∖ dom KM → x ≠ n0 → keyset (FI I x) = keyset (FI I0 x)) → 
    flow_upd_rec es n0 I KM A R = Some (I', KM') →
        ((dom I' = dom I0)
      ∧ (dom KM' ⊆ dom I')
      ∧ (n0 ∉ dom KM')  
      ∧ ([^op set] x ∈ dom I', FI I0 x) = ([^op set] x ∈ dom I', FI I' x)
      ∧ (keyset (FI I' n0) = keyset (FI I0 n0) ∖ (A ∪ R))
      ∧ (∀ x, x ∈ dom KM' → keyset (FI I' x) = keyset (FI I0 x) ∪ (KM' !!! x))
      ∧ (∀ x, x ∈ dom I' ∖ dom KM' → x ≠ n0 → 
                          keyset (FI I' x) = keyset (FI I0 x))
      ∧ (∀ x, x ∈ dom I' → outflow_edge_rel x (es !!! x) (FI I' x))).
  Proof.
  (*
    intros FI. apply flow_upd_rec_ind; try done.
    - clear I KM A R. intros I KM A R HR EdgeRank ES_I A_disj_R VI Domm_I 
        Outflow_I n0_in_I Dom_I_eq_I0 Dom_KM_in_I n0_notin_KM FN_n0 Heq 
        KS_n0 KS_I0 KS_KM [= -> ->]. 
        repeat split; try done.
        assert (R = ∅) as ->.
        { apply leibniz_equiv. by apply elements_empty_inv. }
        by rewrite union_empty_r_L. 
    - clear I KM A R. intros I KM A R k ks HR II nk Hflowk KMM HInd. 
      intros EdgeRank ES_I A_disj_R VI Domm_I Outflow_I n0_in_I Dom_I_eq_I0 
        Dom_KM_in_I n0_notin_KM FN_n0 Heq KS_n0 KS_I0 KS_KM Hflow.
      assert (k ∈ R) as k_in_R.
      { apply elem_of_elements. rewrite HR. clear; set_solver. }
      assert (find_next (es !!! n0) k ≠ None) as FN_n0_k.
      { apply FN_n0; try done. } 
      pose proof flow_updk_summary rank es I k n0 (Some (II, nk))
        EdgeRank ES_I VI Domm_I Outflow_I n0_in_I FN_n0_k Hflowk 
        as [? [? [[= <- <-] Hsum]]].
      destruct Hsum as [Dom_II_eq_I [n0_neq_nk [n0_in_II [nk_in_II 
        [Domm_II [Heq' [KS_nk [KS_II_n0 [KS_II Outflow_II]]]]]]]]].
      assert (([^op set] x ∈ dom I, FI I0 x) =
                ([^op set] x ∈ dom I, FI II x)) as Heq''.
      { rewrite Heq. by unfold FI. }          
      rewrite Dom_II_eq_I in HInd.
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
      assert (dom KMM = dom KM ∪ {[nk]}) as Dom_KMM.
      { rewrite /KMM. apply dom_add_k. }
      assert (∀ x, x ≠ nk → KMM !!! x = KM !!! x) as KMM_x.
      { rewrite /KMM. apply lookup_add_k_ne. }
      assert (KMM !!! nk = KM !!! nk ∪ {[k]}) as KMM_nk.
      { rewrite /KMM. apply lookup_add_k. }
      apply HInd; try done; clear HInd.
      + clear -A_disj_R k_in_R. set_solver.
      + by rewrite <-Heq''; rewrite Heq.
      + by rewrite <-Dom_II_eq_I.
      + by rewrite <-Dom_II_eq_I.
      + rewrite Dom_KMM. rewrite Dom_II_eq_I in nk_in_II. 
        clear -Dom_KM_in_I nk_in_II. set_solver.
      + rewrite Dom_KMM. clear -n0_notin_KM n0_neq_nk.
        set_solver.  
      + intros k' Hk'. apply FN_n0.
        clear -Hk'; set_solver.
      + unfold FI. rewrite KS_II_n0.
        rewrite KS_n0. unfold FI.
        clear; set_solver.
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
  Qed.
  *)
  Admitted.
  
      
  Lemma flow_upd_summary rank es n0 I0 S res:
    let FI := λ I x, I !!! x in
    (edge_rank_rel es rank) →
    (∀ n1 n2, edgeset es n1 n2 ≠ ∅ → n2 ∈ dom I0) →
    (✓ ([^op set] x ∈ dom I0, FI I0 x)) →
    (∀ x, x ∈ dom I0 → domm (FI I0 x) = {[x]}) →
    (∀ x, x ∈ dom I0 → outflow_edge_rel x (es !!! x) (FI I0 x)) →
    (n0 ∈ dom I0) →
    (∀ (k: K), k ∈ S → find_next (es !!! n0) k ≠ None) →
    flow_upd es n0 I0 S = res →
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
      ∧ (∀ x, x ∈ dom I' → outflow_edge_rel x (es !!! x) (FI I' x))).
  Proof.
    intros FI EdgeRank ES_I0 VI0 Domm_I0 Outflow_I0 n0_in_I0
      FN_n0 Hflow.
    unfold flow_upd in Hflow.
    pose proof flow_upd_rec_defined rank es n0 I0 ∅ ∅ S EdgeRank 
      ES_I0 VI0 Domm_I0 Outflow_I0 n0_in_I0 FN_n0 as Hflow'.
    destruct (flow_upd_rec es n0 I0 ∅ ∅ S) as [ (I', KM') | ] eqn:Hflow''; 
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
    pose proof flow_upd_invariants rank es n0 I0 ∅ ∅ S I' KM' I0 
      EdgeRank ES_I0 H1' VI0 Domm_I0 Outflow_I0 n0_in_I0 
      H1'' H2' H2'' FN_n0 H3' H3'' H4' H4'' Hflow'' 
      as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 [HInv6 [HInv7 HInv8]]]]]]].
    exists I', KM'. repeat split; try done.
    assert (∅ ∪ S = S) as H5'. { clear; set_solver. }
    rewrite H5' in HInv5.
    done.
  Qed.  
    

End list_flow_upd.    
