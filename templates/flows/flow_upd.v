Require Import Coq.Numbers.NatInt.NZAddOrder.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

Section list_flow_upd.
  Context `{Countable K}.
  Open Scope ccm_scope.
  
  Lemma list_marking_flow_upd0 (S: gset Node) (nf nl: Node) (I I': Node → multiset_flowint_ur K) e:
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
(*
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
          assert (n ∉ nzmap_dom _ _ out_i) as H'.
          { unfold nzmap_dom. clear -n_in_domm valid_I. set_solver. }
          rewrite nzmap_elem_of_dom_total in H'.
          apply dec_stable in H'.

          unfold valid, flowint_valid in valid_I'.
          destruct valid_I' as [valid_I' _].
          simpl in valid_I'. apply map_disjoint_dom in valid_I'. 
          assert (n ∉ nzmap_dom _ _ out_i') as H''.
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
*)
  Admitted.    

  Lemma list_marking_flow_upd1 (S: gset Node) (n: Node) (I: Node → multiset_flowint_ur K) 
    (es: Node → option Node):
    n ∈ S →
    ✓ ([^op set] x ∈ S, I x) →
    (∀ x, x ∈ S → domm (I x) = {[ x ]}) →
    ∃ (I': Node → multiset_flowint_ur K),
        ✓ ([^op set] x ∈ S, I' x)
      ∧ (∀ x, x ∈ S → domm (I x) = domm (I' x))
      ∧ keyset (I' n) n = ∅
      ∧ ∀ n', n' ∈ S → keyset (I n') n' = ∅ → keyset (I' n') n' = ∅.
  Proof.

  
End list_flow_upd.  

