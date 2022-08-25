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


End flow_big_op.

Section list_flow_upd.
  Context `{CCM M}.
  Open Scope ccm_scope.
  
  Lemma list_marking_flow_upd (S: gset Node) (nf nl: Node) (I I': Node → flowintUR M) e:
    nf ≠ nl →
    {[nf; nl]} ⊆ S →
    ✓ ([^op set] x ∈ S, I x) →
    ✓ ([^op set] x ∈ S, I' x) →
    (∀ x, x ∈ S → domm (I x) = {[ x ]}) →
    (∀ x, x ∈ S → domm (I x) = domm (I' x)) →
    (inf (I nf) nf = inf (I' nf) nf) →
    (([^+ set] x ∈ (S ∖ {[nf]}), out (I x) nf) = 
        ([^+ set] x ∈ (S ∖ {[nf]}), out (I' x) nf)) →
    (∀ n, n ∈ S ∖ {[nf]} → inf (I' n) n = inf (I n) n + e) →
    (∀ n, n ∈ S ∖ {[nf]} → 
      ([^+ set] x ∈ (S ∖ {[n]}), out (I' x) n) = 
        ([^+ set] x ∈ (S ∖ {[n]}), out (I x) n) + e) →
    (∀ n, n ∉ S → ([^+ set] x ∈ S, out (I x) n) = ([^+ set] x ∈ S, out (I' x) n)) →
    ([^op set] x ∈ S, I x) = ([^op set] x ∈ S, I' x).
  Proof.
    intros nf_neq_nl nf_nl_in_S valid_I valid_I' domm_S domm_eq 
      inf_nf out_S_nf inf_n out_S_n out_I_eq_I'. 
    destruct (([^op set] x ∈ S, I x)) as [i | ] eqn: def_I;
    destruct (([^op set] x ∈ S, I' x)) as [i' | ] eqn: def_I'; last done.
    - destruct i as [inf_i out_i]; destruct i' as [inf_i' out_i'].
      assert (domm ([^op set] x ∈ S, I' x) ⊆ domm ([^op set] x ∈ S, I x)) as I'_in_I.
      { intros x Hx. apply flow_big_op_dom in Hx.
        destruct Hx as [x0 [x0_in_S x_in_I'x0]].
        pose proof domm_eq x0 x0_in_S as domm_eq.
        apply flow_big_op_dom. by rewrite <-def_I in valid_I.
        exists x0; split; try done. by rewrite domm_eq. 
        by rewrite <-def_I' in valid_I'. }
      assert (domm ([^op set] x ∈ S, I x) ⊆ domm ([^op set] x ∈ S, I' x)) as I_in_I'.
      { intros x Hx. apply flow_big_op_dom in Hx.
        destruct Hx as [x0 [x0_in_S x_in_Ix0]].
        pose proof domm_eq x0 x0_in_S as domm_eq.
        apply flow_big_op_dom. by rewrite <-def_I' in valid_I'.
        exists x0; split; try done. by rewrite <-domm_eq. 
        by rewrite <-def_I in valid_I. }
      assert (domm ([^op set] x ∈ S, I x) = domm ([^op set] x ∈ S, I' x)) as domm_eq2.
      { clear -I'_in_I I_in_I'. set_solver. }
      assert (inf_i = inf_i') as inf_i_eq_i'.
      { apply map_eq. intros n.
        destruct (decide (n ∈ domm ([^op set] x ∈ S, I x))) 
          as [n_in_domm | n_notin_domm].
        - assert (is_Some (inf_i !! n)) as Some_i.
          { rewrite def_I in n_in_domm. unfold domm, dom, flowint_dom in n_in_domm.
            unfold inf_map in n_in_domm. simpl in n_in_domm.
            by apply elem_of_dom in n_in_domm. }
          assert (is_Some (inf_i' !! n)) as Some_i'.
          { assert (n ∈ domm ([^op set] x ∈ S, I' x)) as H'.
            { apply flow_big_op_dom. by rewrite <-def_I' in valid_I'.
              apply flow_big_op_dom in n_in_domm.
              destruct n_in_domm as [x0 [x0_in_S n_in_domm]].
              exists x0. split; try done. 
              pose proof domm_eq x0 x0_in_S as H'.
              by rewrite <-H'. by rewrite <-def_I in valid_I. }
            rewrite def_I' in H'. unfold domm, dom, flowint_dom in H'.
            unfold inf_map in H'. simpl in H'.
            by apply elem_of_dom in H'. }
          destruct Some_i as [m Some_i].
          destruct Some_i' as [m' Some_i'].    
          apply flow_big_op_dom in n_in_domm; last first.
          by rewrite <-def_I in valid_I.
          destruct n_in_domm as [x0 [x0_in_S n_in_domm]].
          rewrite <-def_I in valid_I.
          pose proof flow_big_op_inf I S x0 n valid_I x0_in_S n_in_domm as H'.
          rewrite def_I in H'. unfold inf at 1 in H'. unfold inf_map in H'.
          simpl in H'.
          assert (n ∈ domm (I' x0)) as n_in_domm'.
          { pose proof domm_eq x0 x0_in_S as H''.
            by rewrite H'' in n_in_domm. }
          rewrite <-def_I' in valid_I'.
          pose proof flow_big_op_inf I' S x0 n valid_I' x0_in_S n_in_domm' as H''.
          rewrite def_I' in H''. unfold inf at 1 in H''. unfold inf_map in H''.
          simpl in H''.
          rewrite Some_i in H'. rewrite Some_i' in H''.
          simpl in H'. simpl in H''.
          rewrite Some_i Some_i'. apply f_equal.
          rewrite H' H''. clear H' H''.
          assert (n = x0) as <-.
          { pose proof domm_S x0 x0_in_S as H'.
            rewrite H' in n_in_domm. clear -n_in_domm. set_solver. }
          destruct (decide (n = nf)) as [ -> | ].
          + by rewrite inf_nf out_S_nf.
          + assert (n ∈ S ∖ {[nf]}) as H' by (clear -n0 x0_in_S; set_solver).
            pose proof inf_n n H' as inf_n.
            pose proof out_S_n n H' as out_S_n.
            rewrite inf_n out_S_n.
            by rewrite ccm_misc.
        - assert (n ∉ domm ([^op set] x ∈ S, I' x)) as n_notin_domm'.
          { by rewrite <-domm_eq2. }           

          unfold domm, dom, flowint_dom, inf_map in n_notin_domm.
          rewrite def_I in n_notin_domm. simpl in n_notin_domm.
          apply not_elem_of_dom in n_notin_domm.
          
          unfold domm, dom, flowint_dom, inf_map in n_notin_domm'.
          rewrite def_I' in n_notin_domm'. simpl in n_notin_domm'.
          apply not_elem_of_dom in n_notin_domm'.
          
          by rewrite n_notin_domm n_notin_domm'. }
          
      assert (out_i = out_i') as out_i_eq_i'.
      { apply nzmap_eq. intros n.
        destruct (decide (n ∈ domm ([^op set] x ∈ S, I x))) 
          as [n_in_domm | n_notin_domm].
        - unfold valid, flowint_valid in valid_I.
          destruct valid_I as [valid_I _].
          simpl in valid_I. apply map_disjoint_dom in valid_I. 
          rewrite def_I in n_in_domm.
          unfold domm, dom, flowint_dom in n_in_domm.
          unfold inf_map in n_in_domm. simpl in n_in_domm.
          assert (n ∉ nzmap_dom out_i) as H'.
          { unfold nzmap_dom. clear -n_in_domm valid_I. set_solver. }
          rewrite nzmap_elem_of_dom_total in H'.
          apply dec_stable in H'.

          unfold valid, flowint_valid in valid_I'.
          destruct valid_I' as [valid_I' _].
          simpl in valid_I'. apply map_disjoint_dom in valid_I'. 
          assert (n ∉ nzmap_dom out_i') as H''.
          { unfold nzmap_dom. rewrite inf_i_eq_i' in n_in_domm.
            clear -n_in_domm valid_I'. set_solver. }
          rewrite nzmap_elem_of_dom_total in H''.
          apply dec_stable in H''.
          by rewrite H' H''.
        - rewrite <-def_I in valid_I.
          pose proof flow_big_op_out I S n valid_I n_notin_domm as H'.
          rewrite def_I in H'. unfold out, out_map at 1 in H'.
          simpl in H'. rewrite domm_eq2 in n_notin_domm.
          rewrite <-def_I' in valid_I'.
          pose proof flow_big_op_out I' S n valid_I' n_notin_domm as H''.
          rewrite def_I' in H''. unfold out, out_map at 1 in H''.
          rewrite H' H''.
          apply out_I_eq_I'. intros n_in_S.
          rewrite <-domm_eq2 in n_notin_domm.
          rewrite flow_big_op_dom in n_notin_domm.
          apply n_notin_domm. exists n. split; try done. 
          rewrite domm_S; try done. clear; set_solver.
          done. } 
      by rewrite inf_i_eq_i' out_i_eq_i'.
    - exfalso. by apply intUndef_not_valid.
    - exfalso. by apply intUndef_not_valid.
  Qed.
  
End list_flow_upd.  
