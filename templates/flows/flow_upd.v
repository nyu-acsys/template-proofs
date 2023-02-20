Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

Section list_flow_upd.
  Context `{Countable K}.
  Open Scope ccm_scope.
    
(*
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
  Admitted.    
*)
  
  Parameter KS : gset K.
    
  
  (* 
    h --> 4 --> 7 --> 10x --> 15x --> 20  
    h --> 4 --> 7x --> 10x --> 15x --> 20 
  *)
  
  Function prepare_upd_rec 
    (S: gset Node) (es: gmap Node (Node * (gset K)))
    (n: Node) (R: gset Node) (res: list Node)
    (X: gset K) (A: gmap Node (gset K * option (Node * gset K)))
    {measure size R} : list Node * gmap Node (gset K * option (Node * gset K)) :=
    match (bool_decide (n ∈ R)) with
    | false => ([], ∅)
    | true =>
      match es !! n with
      | Some (n1, esn) =>
        let Xk := esn ∩ X in
        match (bool_decide (Xk = ∅)) with
        | true => (res ++ [n], <[n := (X, None)]> A)
        | false => 
          prepare_upd_rec S es n1 (R ∖ {[n]}) (res ++ [n]) Xk (<[n := (X, Some (n1, Xk))]> A) end
      | None => (res ++ [n], <[n := (X, None)]> A) end end.
  intros S es n R res X A Hbool (n1, esn) n' esn' H'; inversion H'.
  subst n' esn'. intros Hesn Hbool1.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.
  
  Definition prepare_upd S es n0 X : list Node * gmap Node (gset K * option (Node * gset K)) :=
    prepare_upd_rec S es n0 S [] X ∅.
    
   Definition edge_rel (es: gmap Node (Node * (gset K))) (n n': Node) : Prop := 
    ∃ esn, es !! n = Some (n', esn).   
    
  Lemma prepare_upd_rec_edge S es n R res X A l A':
    (match (last res) with None => res = [] | Some ln => edge_rel es ln n end) → 
    (∀ i, 0 ≤ i < ((length res) - 1)%nat → edge_rel es (res !!! i) (res !!! (i+1)%nat)) →
      prepare_upd_rec S es n R res X A = (l, A') → 
        (∀ i, 0 ≤ i < ((length l) - 1)%nat → edge_rel es (l !!! i) (l !!! (i+1)%nat)).
  Proof.
    apply prepare_upd_rec_ind.
    - intros n0 R0 res0 X0 A0 n0_in_R0 Hlast HInd [= <- <-]. admit.
    - intros n0 R0 res0 X0 A0 n0_in_R0 n1 esn Hesn Xk HXk Hlast HInd [= <- <-] i Hi.
      rewrite app_length in Hi; repeat simpl in Hi.
      assert (∀ x, (x + 1 - 1)%nat = x) as Hplusminus. 
      { lia. } rewrite Hplusminus in Hi.
      destruct (decide (i = (length res0 - 1)%nat)) as [H' | H'].
      + subst i. 
        admit.
      + admit.
    - intros n0 R0 res0 X0 A0 n0_in_R0 n1 esn Hesn Xk HXk HInd0 Hlast HInd Hprepare.
      apply HInd0. 
      + assert (last (res0 ++ [n0]) = Some n0) as H'.
        { admit. }
        rewrite H'.
        unfold edge_rel. by exists esn.
      + admit.
      + done.
    - intros n0 R0 res0 X0 A0 n0_in_R0 Hesn Hlast HInd [= <- <-].
      admit.
  Admitted.
        
        
      

  Fixpoint flow_upd_helper (I I': gmap Node (multiset_flowint_ur K))
    (A: gmap Node (gset K * option (Node * gset K)))
    (l: list Node) : gmap Node (multiset_flowint_ur K) :=
    match l with
    | [] => I'
    | [n] =>
      match A !! n with
      | None => ∅
      | Some (_, Some _) => ∅
      | Some (_, None) => I' end
    | n :: ns =>
      match A !! n with
      | None => ∅
      | Some (_, None) => ∅
      | Some (_, Some (n1, Xk)) =>
        (* Have to pick from I' because its inflow is already updated *)
        let In := I' !!! n in
        (* Add Xk to outf(In, n1) *)
        let In' := outflow_map_set (λ k x, x+1) In n1 Xk in
        (* Pick from I because n1 is untouched so far *)
        let In1 := I !!! n1 in
        (* Add Xk to inf(In1, n1) *)
        let In1' := inflow_map_set (λ k x, x+1) In1 n1 Xk in
        let II := <[n := In']> I' in
        let II' := <[n1 := In1']> II in  
        flow_upd_helper I II' A ns end end.
  
  Functional Scheme flow_upd_helper_ind := Induction for flow_upd_helper Sort Prop.
        
  Check flow_upd_helper_ind.
  
  Definition flow_upd S es I n0 : gmap Node (multiset_flowint_ur K) :=
    match es !! n0 with
    | None => ∅
    | Some (n1, es_n0) =>
      let In0 := I !!! n0 in
      let inf_n0 := inset K In0 n0 in
      let X := inf_n0 ∩ (KS ∖ es_n0) in      
      let (l, A) := prepare_upd S es n1 X in
      let In0' := outflow_map_set (λ k x, x+1) In0 n1 X in
      let In1 := I !!! n1 in
      let In1' := inflow_map_set (λ k x, x+1) In1 n1 X in
      let II := <[n0 := In0']> ∅ in
      let I' := <[n1 := In1']> II in  
      flow_upd_helper I I' A l end.
      
  Lemma flow_upd_intfEq I I' A l II' :
    let intf := λ I x, I !!! x in 
    ([^op set] x ∈ dom I', intf I x) = ([^op set] x ∈ dom I', intf I' x) →
      flow_upd_helper I I' A l = II' → 
        ([^op set] x ∈ dom II', intf I x) = ([^op set] x ∈ dom II', intf II' x).
  Proof.
    intros intf. apply flow_upd_helper_ind.
    - intros I0 II0 ? -> HInd ->. done.
    - intros I0 A0 ? n ns -> -> ? HA0 es_n opt_n1 -> ? ? ? <-.
      rewrite dom_empty_L. by rewrite !big_opS_empty.
    - intros I0 A0 ? n ? -> -> ? HA0_n es_n ? -> -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> HA0_n HInd <-.
      rewrite dom_empty_L. by rewrite !big_opS_empty.
    - intros I0 A0 ? n ? -> n1' ns' -> ? HA0_n inf_n ? -> (n1, out_n) -> ? ? [= <- <-].
      intros In In' In1 In1' II I0' HInd Heq Hflow. apply HInd; try done.
      assert (n ∈ dom I0) as dom_I0.
      { admit. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as dom_I0'.
      { admit. }
      assert (n1 ∉ dom I0) as n_notin_I0.
      { admit. }
      rewrite dom_I0'. rewrite !big_opS_union.
      rewrite !big_opS_singleton. 
      all: try (clear -n_notin_I0; set_solver).
      rewrite /I0'; rewrite /intf. rewrite lookup_total_insert.
      symmetry.
      apply (intCompose_add _ ([^op set] y ∈ dom I0, I !!! y) (I !!! n1) 
        ([^op set] y ∈ dom I0, <[n1:=In1']> II !!! y) In1' n1 ∅).
      + admit.
      + admit.
      + admit.
      + (* Use flow_big_op_out and Heq; unfold both sides *)
        admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - intros I0 A0 ? n ? -> n1' ns' -> ? HA0_n inf_n ? -> -> HInd <-.
      rewrite dom_empty_L. by rewrite !big_opS_empty.
    - intros I0 A0 ? n ? -> n1' ns' -> ? HA0_n <-.
      rewrite dom_empty_L. by rewrite !big_opS_empty.
  Admitted.      
        
  Definition extract_inf (x: gset K * option (Node * gset K)) : gset K :=
    x.1.
    
  Lemma flow_upd_inflow I I' A l II' :
    let intf := λ I x, I !!! x in
    (∀ n, n ∈ dom A → 
      (inset _ (intf I' n) n) = (inset _ (intf I n) n) ∪ (extract_inf (A !!! n))) →
      flow_upd_helper I I' A l = II' → 
        (∀ n, n ∈ dom A → 
          (inset _ (intf II' n) n) = (inset _ (intf I n) n) ∪ (extract_inf (A !!! n))).
  Proof.
    intros intf. apply flow_upd_helper_ind.
    - intros ? A0 ? -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> ? HA0_n X_n ? -> (n1, X_n1) -> HInd <-.
      (* Contradiction from Some(n1, X_n1) = None *)
      admit.
    - intros I0 A0 ? n ? -> -> ? HA0_n ? ? -> -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
    - intros I0 A0 ? n ? -> n1' ns -> ? HA0_n X_n opt_n -> (n1, X_n1) ->.
      intros ? ? [= <- <-]. intros In In' In1 In1' II I0' HInd'.
      intros HInd Hflow. apply HInd'; try done.
      intros n0 Hn0. pose proof HInd n0 Hn0 as HInd.
      (* Case analysis on n0 *)
      admit.
      
      
    - intros I0 A0 ? n ? -> n1' ns -> (?, ?) HA0_n X_n ? [= -> ->] -> HInd <-.
      (* Contradiction: only for last element of l should A0 !!! n = (_, None) *)
      (* n is not the last element of l here *)
      admit.
    - intros I0 A0 ? n ? -> n1 ns -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
  Admitted.
    
  Definition extract_outf (x: gset K * option (Node * gset K)) : gset K :=
    match x with
    | (_, None) => ∅
    | (_, Some (_, X)) => X end. 
    
  Lemma flow_upd_outflow I I' A l II' :
    let intf := λ I x, I !!! x in
    (∀ n, n ∈ dom A → 
      (outset _ (intf I' n) n) = (outset _ (intf I n) n) ∪ (extract_outf (A !!! n))) →
      flow_upd_helper I I' A l = II' → 
        (∀ n, n ∈ dom A → 
          (outset _ (intf II' n) n) = (outset _ (intf I n) n) ∪ (extract_outf (A !!! n))).
  Proof.
    intros intf. apply flow_upd_helper_ind.
    - intros ? A0 ? -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> ? HA0_n X_n ? -> (n1, X_n1) -> HInd <-.
      (* Contradiction from Some(n1, X_n1) = None *)
      admit.
    - intros I0 A0 ? n ? -> -> ? HA0_n ? ? -> -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
    - intros I0 A0 ? n ? -> n1' ns -> ? HA0_n X_n opt_n -> (n1, X_n1) ->.
      intros ? ? [= <- <-]. intros In In' In1 In1' II I0' HInd'.
      intros HInd Hflow. apply HInd'; try done.
      intros n0 Hn0. pose proof HInd n0 Hn0 as HInd.
      (* Case analysis on n0 *)
      admit.
      
      
    - intros I0 A0 ? n ? -> n1' ns -> (?, ?) HA0_n X_n ? [= -> ->] -> HInd <-.
      (* Contradiction: only for last element of l should A0 !!! n = (_, None) *)
      (* n is not the last element of l here *)
      admit.
    - intros I0 A0 ? n ? -> n1 ns -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
  Admitted.

  Definition extract_ks (x: gset K * option (Node * gset K)) : gset K :=
    match x with
    | (X, None) => X
    | (X, Some (_, Xk)) => X ∖ Xk end. 

  Lemma flow_upd_keyset I I' A l II' :
    let intf := λ I x, I !!! x in
    (match l with
      | [] => (∀ n, n ∈ dom A → keyset (intf I' n) n = extract_ks (A !!! n))
      | [n0] => (∀ n, n ∈ dom A → keyset (intf I' n) n = extract_ks (A !!! n))
      | n0 :: ns => 
        (∀ n, n ∈ dom A ∧ n ∉ ns → keyset (intf I' n) n = extract_ks (A !!! n)) end) →
      flow_upd_helper I I' A l = II' → 
        (∀ n, n ∈ dom A → keyset (intf II' n) n = extract_ks (A !!! n)).
  Proof.
    intros intf. apply flow_upd_helper_ind.
    - intros ? A0 ? -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> ? HA0_n X_n ? -> (n1, X_n1) -> HInd <-.
      (* Contradiction from Some(n1, X_n1) = None *)
      admit.
    - intros I0 A0 ? n ? -> -> ? HA0_n ? ? -> -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
    - intros I0 A0 ? n ? -> n1' ns -> ? HA0_n X_n opt_n -> (n1, X_n1) ->.
      intros ? ? [= <- <-]. intros In In' In1 In1' II I0' HInd'.
      intros HInd Hflow. apply HInd'; try done.
      destruct ns as [| ?].
      + admit.
      + admit.
      
      
    - intros I0 A0 ? n ? -> n1' ns -> (?, ?) HA0_n X_n ? [= -> ->] -> HInd <-.
      (* Contradiction: only for last element of l should A0 !!! n = (_, None) *)
      (* n is not the last element of l here *)
      admit.
    - intros I0 A0 ? n ? -> n1 ns -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
  Admitted.

  Definition outflow (I: multiset_flowint_ur K) (n: Node) (es: Node * gset K) := 
    ∀ n' k, k ∈ KS → (k ∈ outset K I n' ↔ n' = es.1 ∧ k ∈ es.2 ∧ k ∈ inset K I n).

  Lemma list_marking_flow_upd1 (S: gset Node) (n: Node) (II: gmap Node (multiset_flowint_ur K))
    (es: gmap Node (Node * gset K)) (es': gmap Node (Node * gset K)) (rank: Node -> nat) :
    let I : Node → multiset_flowint_ur K := λ x, II !!! x in 
    n ∈ S →
    ✓ ([^op set] x ∈ S, I x) →
    (∀ x, x ∈ S → domm (I x) = {[ x ]}) →
    (∀ x, x ∈ S → outflow (I x) x (es !!! x)) →
    es' = <[n := ((es !!! n).1, KS) ]> es →
    (∀ n', rank(n') < rank((es !!! n').1)) →
    ∃ (II': gmap Node (multiset_flowint_ur K)),
      let I' : Node → multiset_flowint_ur K := λ x, II' !!! x in
        ✓ ([^op set] x ∈ S, I' x)
      ∧ (∀ x, x ∈ S → domm (I x) = domm (I' x))
      ∧ keyset (I' n) n = ∅
      ∧ ∀ n', n' ∈ S → keyset (I n') n' = ∅ → keyset (I' n') n' = ∅
      ∧ (∀ x, x ∈ S → outflow (I' x) x (es' !!! x)).
  Proof.
    intros I n_in_S Valid Domm Outf Def_es Rank.
    destruct (decide (keyset (I n) n = ∅)).
    - exists II. intros I'.
      subst I I'. split; try done.
      split; try done. split; try done.
      split; try done. split; try done.
    
  Admitted.
  
End list_flow_upd.  

