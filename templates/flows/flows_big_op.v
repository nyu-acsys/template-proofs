Set Default Proof Using "All".
From iris.algebra Require Export big_op.
Require Export flows ccm_big_op.

Section flow_big_op.
  Context `{CCM M}.
  Context `{Countable A}.
  Implicit Types S : gset A.
  Implicit Types I : A → flowintUR M.
  Open Scope ccm_scope.
  
(*  
  Definition intComposable_big_op I S := 
    ∀ S', S' ⊂ S → intComposable ([^op set] x ∈ S', I x) ([^op set] x ∈ S ∖ S', I x).
    
  Global Instance intComposable_big_op_dec I S : Decision (intComposable_big_op I S).
  Proof.
    unfold intComposable_big_op.
  Admitted.
            
  Lemma intValid_composable_big_op_valid I S :
    intComposable_big_op I S → ✓ ([^op set] x ∈ S, I x).
  Proof.
  Admitted.  
*)    
  
  Lemma flow_big_op_dom I S n :
    ✓ ([^op set] x ∈ S, I x) → 
        (n ∈ domm ([^op set] x ∈ S, I x) ↔ ∃ x0, x0 ∈ S ∧ n ∈ domm (I x0)). 
  Proof.
    induction S as [|s S ? IH] using set_ind_L.
    - intros _. split.
      + intros Hn. rewrite big_opS_empty in Hn.
        unfold monoid_unit in Hn. simpl in Hn.
        unfold domm in Hn.
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
    n ∉ domm ([^op set] x ∈ S, I x) → 
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
  
  
  Lemma flow_big_op_inf I S x0 n :
    ✓ ([^op set] x ∈ S, I x) →
    x0 ∈ S → n ∈ domm (I x0) → 
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
        assert (n ∉ domm ([^op set] y ∈ S, I y)) as n_notin_dom.
        { apply intComp_dom_disjoint in valid.
          clear -n_in_dom valid; set_solver. }
        pose proof (cmra_valid_op_r _ _ valid) as valid'.  
        pose proof flow_big_op_out I S n valid' n_notin_dom as H'.
        by rewrite H'.
      + rewrite big_opS_insert in valid; try done.
        rewrite intComp_inf_2; try done.
        pose proof (cmra_valid_op_r _ _ valid) as valid'.
        rewrite (IH valid' x0_in_S n_in_dom).
        assert (({[s]} ∪ S) ∖ {[x0]} = {[s]} ∪ (S ∖ {[x0]})) as ->.
        { set_solver. } rewrite ccm_big_opS_insert.
        rewrite ccm_misc2. by rewrite ccm_misc3.
        set_solver. apply flow_big_op_dom.
        by pose proof (cmra_valid_op_r _ _ valid) as valid'.
        exists x0; split; try done.
  Qed.

  Lemma intValid_big_op I S :
    ∀ S', S' ⊆ S → ✓ ([^op set] x ∈ S, I x) → ✓ ([^op set] x ∈ S', I x).
  Proof.
    induction S as [| s S ? IH] using set_ind_L.
    - intros. assert (S' = ∅) as -> by set_solver.
      rewrite big_opS_empty. unfold monoid_unit.
      simpl. try done.
    - intros S' HS' Valid.
      destruct (decide (s ∈ S')) as [Hs | Hs].
      + rewrite big_opS_insert in Valid; try done.
        rewrite (big_opS_delete _ _ s); try done.
        apply intValid_composable. repeat split; try done.
        * admit.
        * admit.
        * admit.
        * apply map_Forall_lookup.
          intros n x Hx. unfold inf. rewrite Hx. simpl.
          set S'' := S' ∖ {[s]}.
          assert (✓ ([^op set] y ∈ S'', (I y))) as Valid_S''.
          { admit. }
          assert (n ∉ (domm ([^op set] x ∈ S'', (I x)))) as n_notin_S''.
          { admit. }
          pose proof (flow_big_op_out I S'' n Valid_S'' n_notin_S'') as ->.
          apply intComposable_valid in Valid.
          destruct Valid as [_ [_ [_ [H' _]]]].
          rewrite map_Forall_lookup in H'.
          pose proof H' n x Hx as H'.
          unfold inf in H'. rewrite Hx in H'. simpl in H'.
          assert (✓ ([^op set] x ∈ S, (I x))) as Valid_S.
          { admit. }
          assert (n ∉ (domm ([^op set] x ∈ S, (I x)))) as n_notin_S.
          { admit. }
          pose proof (flow_big_op_out I S n Valid_S n_notin_S) as H''.
          rewrite H'' in H'.
          assert (([^+ set] x ∈ S, (out (I x) n)) = 
                    ([^+ set] x ∈ S'', (out (I x) n)) + ([^+ set] x ∈ S∖S'', (out (I x) n))) as H'''.
          { admit. }          
          rewrite H''' in H'.
          by apply (ccm_misc5 x ([^+ set] x0 ∈ S'', (out (I x0) n)) 
                    ([^+ set] x ∈ (S ∖ S''), (out (I x) n))).
        * apply map_Forall_lookup.
          set S'' := S' ∖ {[s]}.
          intros n x Hx. unfold inf. rewrite Hx. simpl.
          assert (✓ ((I s) ⋅ ([^op set] y ∈ S'', (I y)))) as Valid'.
          { admit. }
          apply intComposable_valid in Valid'.
          destruct Valid' as [_ [_ [_ [_ H']]]].
          pose proof H' n x Hx as H'.
          unfold inf in H'. rewrite Hx in H'. by simpl in H'.
      + assert (S' ⊆ S) as S'_sub_S by set_solver.
        apply IH; try done.
        rewrite big_opS_insert in Valid; try done.
        by apply (cmra_valid_op_r (I s)).
  Admitted.

End flow_big_op.