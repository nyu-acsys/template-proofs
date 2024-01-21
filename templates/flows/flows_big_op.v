(* Big op over flows *)

Set Default Proof Using "All".
From iris.algebra Require Export big_op.
Require Export flows ccm_big_op.

Section flow_big_op.
  Context `{CCM M}.
  Context `{Countable A}.
  Implicit Types S : gset A.
  Implicit Types I : A → flowintUR M.
  Open Scope ccm_scope.
  
  
  Lemma flow_big_op_dom I S n :
    ✓ ([^op set] x ∈ S, I x) → 
        (n ∈ dom ([^op set] x ∈ S, I x) ↔ ∃ x0, x0 ∈ S ∧ n ∈ dom (I x0)). 
  Proof.
    induction S as [|s S ? IH] using set_ind_L.
    - intros _. split.
      + intros Hn. rewrite big_opS_empty in Hn.
        unfold monoid_unit in Hn. simpl in Hn.
        unfold dom in Hn.
        exfalso; set_solver.
      + intros [x0 [? ?]]. set_solver.
    - intros valid. split.
      + intros Hn. rewrite big_opS_insert in Hn; try done.
        rewrite big_opS_insert in valid; try done.
        rewrite intComp_dom in Hn; try done.
        rewrite elem_of_union in Hn.
        destruct Hn as [Hn | Hn].
        * exists s. split; try done. set_solver.
        * pose proof (cmra_valid_op_r _ _ valid) as valid'.
          pose proof IH valid' as H'. destruct H' as [H' _]. 
          pose proof H' Hn as H'. destruct H' as [x [x_in_S n_in_x]].
          exists x; split; try done. clear -x_in_S; set_solver.
      + intros Hx. destruct Hx as [x [x_in_S n_in_x]].
        rewrite big_opS_insert; try done.
        rewrite big_opS_insert in valid; try done.
        rewrite intComp_dom; try done. 
        rewrite elem_of_union in x_in_S.
        rewrite elem_of_union.
        destruct x_in_S as [x_eq_S | x_in_S].
        * left. by assert (x = s) as <- by set_solver.
        * right. apply IH. by pose proof (cmra_valid_op_r _ _ valid) as valid'.
          exists x; split; try done.
  Qed.

  Lemma flow_big_op_out I S n :
    ✓ ([^op set] x ∈ S, I x) →
    n ∉ dom ([^op set] x ∈ S, I x) → 
    out ([^op set] x ∈ S, I x) n = ([^+ set] x ∈ S, out (I x) n).
  Proof.
    induction S as [|s S ? IH] using set_ind_L.
    - intros _ _.
      rewrite big_opS_empty. unfold monoid_unit.
      simpl. rewrite intEmp_out.
      by rewrite ccm_big_opS_empty.
    - intros valid n_notin_dom.
      rewrite big_opS_insert in valid; try done.
      rewrite big_opS_insert in n_notin_dom; try done.
      rewrite big_opS_insert; try done.
      rewrite intComp_unfold_out; try done.
      rewrite ccm_big_opS_insert; try done.
      rewrite intComp_dom in n_notin_dom; try done.
      rewrite not_elem_of_union in n_notin_dom.
      destruct n_notin_dom as [_ n_notin_dom].
      pose proof (cmra_valid_op_r _ _ valid) as valid'.
      by rewrite (IH valid' n_notin_dom).
  Qed.

  Lemma flow_big_op_valid I S :
    ∀ S', S' ⊆ S → ✓ ([^op set] x ∈ S, I x) → ✓ ([^op set] x ∈ S', I x).
  Proof.
    induction S as [| s S ? IH] using set_ind_L.
    - intros. assert (S' = ∅) as -> by set_solver.
      rewrite big_opS_empty. unfold monoid_unit.
      simpl. try done.
    - intros S' HS' Valid.
      set S'' := S' ∖ {[s]}. 
      assert (S'' = S' ∖ {[s]}) as Def_S'' by try done. 
      assert (S'' ⊆ S) as HS'' by set_solver.
      assert (✓ ([^op set] y ∈ S'', I y)) as Valid_S''.
      { apply IH; try done.
        rewrite big_opS_insert in Valid; try done.
        by apply (cmra_valid_op_r (I s) _) in Valid. }
      assert (Valid' := Valid).
      rewrite big_opS_insert in Valid; try done.  
      assert (✓ ([^op set] x ∈ S, (I x))) as Valid_S.
      { by apply (cmra_valid_op_r (I s) _) in Valid. }
      assert (dom ([^op set] y ∈ S'', I y) ⊆ 
                    dom ([^op set] y ∈ S, I y)) as Dom_sub.
      { intros x Hx. rewrite flow_big_op_dom in Hx; try done.
        rewrite flow_big_op_dom; try done.
        destruct Hx as [x0 [Hx1 Hx2]].
        exists x0; split; try done. set_solver. }
      assert (✓ (I s)) as Valid_s.
      { by apply (cmra_valid_op_l (I s) _) in Valid. }  
      destruct (decide (s ∈ S')) as [Hs | Hs].
      + rewrite (big_opS_delete _ _ s); try done.
        apply intValid_composable. repeat split; try done.
        * assert (Dom_disj := Valid). 
          apply intComp_dom_disjoint in Dom_disj.
          rewrite <-Def_S''.
          set_solver.
        * apply map_Forall_lookup.
          intros n x Hx. unfold inf. rewrite Hx. simpl.
          assert (n ∉ (dom ([^op set] x ∈ S'', (I x)))) as n_notin_S''.
          { assert (n ∈ dom (I s)).
            { apply (flowint_contains _ _ _ x); try done. }
            apply intComp_dom_disjoint in Valid.
            set_solver. }
          rewrite <-Def_S''.
          pose proof (flow_big_op_out I S'' n Valid_S'' n_notin_S'') as ->.
          assert (Valid'' := Valid).
          apply intComposable_valid in Valid''.
          destruct Valid'' as [_ [_ [_ [H' _]]]].
          rewrite map_Forall_lookup in H'.
          pose proof H' n x Hx as H'.
          unfold inf in H'. rewrite Hx in H'. simpl in H'.
          assert (n ∉ (dom ([^op set] x ∈ S, (I x)))) as n_notin_S.
          { assert (n ∈ dom (I s)).
            { apply (flowint_contains _ _ _ x); try done. }
            apply intComp_dom_disjoint in Valid.
            set_solver. }
          pose proof (flow_big_op_out I S n Valid_S n_notin_S) as H''.
          rewrite H'' in H'.
          assert (([^+ set] x ∈ S, (out (I x) n)) = 
                    ([^+ set] x ∈ S'', (out (I x) n)) + 
                      ([^+ set] x ∈ S∖S'', (out (I x) n))) as H'''.
          { assert (S = S'' ∪ (S ∖ S'')) as H1'.
            { rewrite set_eq_subseteq. split.
              - clear -HS''. intros m Hm.
                rewrite elem_of_union.
                destruct (decide (m ∈ S'')).
                + by left.
                + set_solver.
              - clear -HS''. set_solver. }
            rewrite {1}H1'.  
            rewrite ccm_big_opS_union; try done.
            set_solver. }
          rewrite H''' in H'.
          by apply (ccm_op_incl x ([^+ set] x0 ∈ S'', (out (I x0) n)) 
                    ([^+ set] x ∈ (S ∖ S''), (out (I x) n))).
        * apply map_Forall_lookup.
          intros n x Hx. unfold inf. rewrite Hx. simpl.
          rewrite <-Def_S'' in Hx.
          assert (S = S ∖ S'' ∪ S'') as HS.
          { apply set_eq_subseteq. split. 
            - intros m Hm. destruct (decide (m ∈ S'')).
              + set_solver. 
              + set_solver.
            - set_solver. }
          rewrite HS in Valid'.
          assert (Valid'' := Valid'). 
          assert ({[s]} ∪ (S ∖ S'' ∪ S'') = ({[s]} ∪ S ∖ S'') ∪ S'') as H1'.
          { clear; set_solver. }
          rewrite H1' in Valid'.
          rewrite big_opS_union in Valid'; last first.
          { set_solver. }
          rewrite big_opS_union in Valid'; last first.
          { set_solver. }
          rewrite -big_opS_union in Valid'; last by set_solver.
          apply intComposable_valid in Valid'.
          destruct Valid' as (_&_&_&_&H').
          pose proof H' n x Hx as H'. simpl in H'.
          unfold inf in H'. rewrite Hx in H'. simpl in H'.
          assert (out ([^op set] y ∈ ({[s]} ∪ S ∖ S''), I y) n =
            out (I s) n + ([^+ set] x ∈ (S ∖ S''), out (I x) n)) as H''.
          { rewrite flow_big_op_out; try done. 
            rewrite ccm_big_opS_union. by rewrite ccm_big_opS_singleton.
            set_solver.
            rewrite H1' in Valid''.
            rewrite big_opS_union in Valid''.
            by apply (cmra_valid_op_l ([^op set] y ∈ ({[s]} ∪ S ∖ S''), I y) _) 
              in Valid''.
            set_solver.
            intros Hn. rewrite H1' in Valid''. 
            rewrite big_opS_union in Valid''.
            apply intComp_dom_disjoint in Valid''.
            assert (n ∈ dom ([^op set] y ∈ S'', I y)) as H''.
            { apply (flowint_contains _ _ _ x); try done. }
            clear -H'' Hn Valid''. set_solver.
            set_solver. }
          rewrite H'' in H'.
          by apply (ccm_op_incl x (out (I s) n) 
            ([^+ set] x ∈ (S ∖ S''), out (I x) n)).  
      + assert (S' ⊆ S) as S'_sub_S by set_solver.
        apply IH; try done.
  Qed.  
  
  Lemma flow_big_op_inf I S x0 n :
    ✓ ([^op set] x ∈ S, I x) →
    x0 ∈ S → n ∈ dom (I x0) → 
    inf ([^op set] x ∈ S, I x) n = 
      inf (I x0) n - ([^+ set] x ∈ S ∖ {[x0]}, out (I x) n).
  Proof.
    induction S as [|s S ? IH] using set_ind_L.
    - intros _ Hx. clear -Hx; set_solver.
    - intros valid x0_in_S n_in_dom.
      rewrite big_opS_insert; try done.
      rewrite elem_of_union in x0_in_S.
      destruct x0_in_S as [x0_eq_s | x0_in_S].
      + assert (x0 = s) as -> by set_solver.
        rewrite big_opS_insert in valid; try done.
        rewrite intComp_inf_1; try done.
        assert (({[s]} ∪ S) ∖ {[s]} = S) as -> by set_solver.
        assert (n ∉ dom ([^op set] y ∈ S, I y)) as n_notin_dom.
        { apply intComp_dom_disjoint in valid.
          clear -n_in_dom valid; set_solver. }
        pose proof (cmra_valid_op_r _ _ valid) as valid'.  
        pose proof flow_big_op_out I S n valid' n_notin_dom as H'.
        by rewrite H'.
      + assert (valid' := valid). 
        rewrite big_opS_insert in valid'; try done.
        apply (cmra_valid_op_r (I s) _) in valid'.
        rewrite intComp_inf_2; try done; last first.
        { rewrite flow_big_op_dom; try done.
          exists x0; split; try done. }
        { rewrite big_opS_insert in valid; try done. }  
        rewrite (IH valid' x0_in_S n_in_dom).
        
        assert (valid'' := valid).
        rewrite (big_opS_delete _ _ x0) in valid; last first.
        { set_solver. }
        apply intComposable_valid in valid.
        destruct valid as (_&_&_&H'&_).
        assert (Hn := n_in_dom).
        unfold dom, flowint_dom in Hn.
        rewrite elem_of_dom in Hn.
        destruct Hn as [m Hm].
        pose proof H' n m Hm as H'. simpl in H'.
        unfold inf in H'. rewrite Hm in H'. simpl in H'.
        
        unfold inf. rewrite Hm. simpl.
        assert (({[s]} ∪ S) ∖ {[x0]} = {[s]} ∪ (S ∖ {[x0]})) as HS.
        { set_solver. }
        rewrite HS.
        rewrite ccm_big_opS_union; last first.
        { clear -H1 x0_in_S. set_solver. }
        rewrite ccm_big_opS_singleton.
        rewrite ccm_comm.
        assert (out ([^op set] y ∈ (({[s]} ∪ S) ∖ {[x0]}), I y) n
            = ([^+ set] x ∈ (S ∖ {[x0]}), out (I x) n) + out (I s) n) as H''.
        { rewrite flow_big_op_out; try done. 
          rewrite HS. rewrite ccm_big_opS_union. 
          rewrite ccm_comm. by rewrite ccm_big_opS_singleton.
          set_solver.
          assert (({[s]} ∪ S) ∖ {[x0]} ⊆ {[s]} ∪ S) as H''.
          { set_solver. }
          by pose proof flow_big_op_valid I ({[s]} ∪ S) (({[s]} ∪ S) ∖ {[x0]}) 
            H'' valid''.
          rewrite (big_opS_delete _ _ x0) in valid''; last first.
          { set_solver. }
          apply intComp_dom_disjoint in valid''.
          intros Hn.
          clear -Hn n_in_dom valid''.
          set_solver. }
        rewrite H'' in H'. 
        rewrite ccm_pinv_op; try done.
  Qed.

End flow_big_op.