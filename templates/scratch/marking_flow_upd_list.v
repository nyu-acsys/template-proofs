Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
(* From Coq Require Import QArith Qcanon. *)
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

Section marking_flow_upd.
  Open Scope ccm_scope.

  Function marking_flow_upd_rec (n: Node) (R: gset Node)
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
        let In' := outflow_insert_set In n1 S in
        (* Pick from I because n1 must be untouched so far *)
        let In1 := I !!! n1 in
        (* Add S to inf(In1, n1) *)
        let In1' := inflow_insert_set In1 n1 S in
        let II := <[n := In']> I' in
        let II' := <[n1 := In1']> II in  
        marking_flow_upd_rec n1 (R ∖ {[n]}) Nx Mk S I II' end
    | Some false => Some (I', n) end end.
  intros n R Nx Mk S I I' Hbool. intros.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.

  Definition marking_flow_updk_post (I I': gmap Node (multiset_flowint_ur nat)) :=
    let f := λ m1 m2,
              match m1, m2 with 
              | Some m1, Some m2 => Some m1
              | None, Some m2 => Some m2
              | Some m1, None => Some m1
              | None, None => None end in
    merge f I I'.

  Definition marking_flow_upd n0 Nx Mk S I :=
    match Nx !! n0 with
    | None => None
    | Some n1 =>
      let In0 := I !!! n0 in
      let In0' := outflow_insert_set In0 n1 S in
      let In1 := I !!! n1 in
      let In1' := inflow_insert_set In1 n1 S in
      let I' := <[n1 := In1']> ({[n0 := In0']}) in
      marking_flow_upd_rec n1 (dom I ∖ {[n0]}) Nx Mk S I I' end.

  Definition nx_key_rel (Nx: gmap Node Node) (Key: gmap Node nat) :=
    ∀ n1 n2, Nx !! n1 = Some n2 → (Key !!! n1 < Key !!! n2). 

  Definition nx_mk_closed (Nx: gmap Node Node) (Mk: gmap Node bool)
    (I: gmap Node (multiset_flowint_ur nat)) :=
      (dom Nx = dom I)
    ∧ (dom Mk = dom I)  
    ∧ (∀ n1 n2, Nx !! n1 = Some n2 → n2 ∈ dom I).

  Lemma marking_flow_upd_rec_defined Key n R Nx Mk S I I':
    (nx_key_rel Nx Key) → 
    (nx_mk_closed Nx Mk I) →
    (n ∈ dom I') →
    (dom I = R ∪ dom I') →
    (R ∩ dom I' = {[n]}) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
      marking_flow_upd_rec n R Nx Mk S I I' ≠ None.
  Proof.
    apply marking_flow_upd_rec_ind; try done.
    - clear n R Nx Mk S I I'. intros n R Nx Mk S I I' n_notin_R.
      rewrite bool_decide_eq_false in n_notin_R.
      intros _ _ _ _ ? _. set_solver.
    - clear n R Nx Mk S I I'. 
      intros n R Nx Mk S I I' n_in_R HMk_n Nx_key Hcl n_in_I' 
        Dom_I R_inter_I Key_I'.
      admit.  
    - clear n R Nx Mk S I I'. 
      intros n R Nx Mk S I I' n_in_R HMk_n Nx_key Hcl n_in_I' 
        Dom_I R_inter_I Key_I'.
      admit.
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
  Admitted.

  Lemma marking_flow_upd_dom Key n R Nx Mk S I I' II' nk:
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk I) →
    (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (dom I' ⊆ dom I) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
          (dom II' ⊆ dom I).
  Proof.
    apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key Hcl n_in_I0 Key_I0 Dom_I0_in_I [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key Hcl n_in_I0 Key_I0 Dom_I0_in_I Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 Hnx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0. set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct Hcl as [_ [_ Hcl]].
        by pose proof Hcl n n1 Hnx_n as H'. }  
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'; set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
      + rewrite Dom_I0'; set_solver.
  Qed.

  Lemma marking_flow_upd_neq Key n R Nx Mk S I I' II' nk n0:
    (nx_key_rel Nx Key) →
    (n0 ∈ dom I') → (n ∈ dom I') → (n0 ≠ n) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (n0 ≠ nk).
  Proof.
    apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key n0_in_I0 n_in_I0 n0_neq_n Key_I0 [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key n0_in_I0 n_in_I0 n0_neq_n Key_I0 Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 Hnx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (n0 ≠ n1) as n0_neq_n1.
      { clear -n0_in_I0 n1_notin_I0. set_solver. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'; set_solver.
      + rewrite Dom_I0'; set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
  Qed.
  
  Lemma marking_flow_upd_n0_dom n R Nx Mk S I I' II' nk n0:
    (n0 ∈ dom I') → (n ∈ dom I') →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (n0 ∈ dom II').
  Proof.
    apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros n0_in_I0 n_in_I0 [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd n0_in_I0 n_in_I0 Hflow.
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'; set_solver.
      + rewrite Dom_I0'; set_solver.
  Qed.
  
  Lemma marking_flow_upd_nk_dom n R Nx Mk S I I' II' nk:
    (n ∈ dom I') →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (nk ∈ dom II').
  Proof.
    apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros n_in_I0 [= -> ->]. 
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd n_in_I0 Hflow.
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
  Qed.

  Lemma marking_flow_upd_Mk_nk n R Nx Mk S I I' II' nk:
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (Mk !! nk = Some false).
  Proof.
    apply marking_flow_upd_rec_ind; try done; last first.
    clear n R Nx Mk S I I'.
    intros n R Nx Mk S I I0 n_in_R Hmk_n [= -> ->].
    done.
  Qed.
  
  Lemma marking_flow_upd_Nx Key n R Nx Mk S I I' II' nk n0:
    (nx_key_rel Nx Key) →
    (n0 ∈ dom I') → (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) →
    (∀ x, x ∈ dom I' ∖ {[n]} → Nx !! x ≠ None) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
          (∀ x, x ∈ dom II' ∖ {[nk]} → Nx !! x ≠ None).
  Proof.
    apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key n0_in_I0 n_in_I0 Key_I0 Key_n0 Nx_x [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key n0_in_I0 n_in_I0 Key_I0 Key_n0 Nx_x Hflow.
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
      + rewrite Dom_I0'. intros x. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        * apply Key_n0. clear -Hx1 Hx2; set_solver.
        * assert (x = n1) as -> by (clear -Hx1; set_solver). 
          pose proof Nx_key n n1 Hnx_n as H'.
          assert (Key !!! n0 ≤ Key !!! n) as H''.
          { by apply Key_I0. }
          clear -H' H''. lia.
      + intros x. rewrite Dom_I0'. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        * destruct (decide (x = n)) as [-> | Hxn].
          -- by rewrite Hnx_n.
          -- apply Nx_x. clear -Hx1 Hx2 Hxn; set_solver.
        * clear -Hx1 Hx2; set_solver.
  Qed.
  
  Lemma marking_flow_upd_domm Key n R Nx Mk S I I' II' nk:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk I) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (∀ x, x ∈ dom II' → dom (FI II' x) = {[x]}).
  Proof.
    intros FI. apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key Hcl Domm_I n_in_I0 Key_I0 Domm_I0 [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key Hcl Domm_I n_in_I0 Key_I0 Domm_I0 Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 Hnx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      assert (∀ x, x ∈ dom I0 → dom (FI (<[n:=In']> I0) x) = {[x]}) 
        as Domm_II.
      { intros x Hx. destruct (decide (n = x)) as [-> | Hxn].
        - unfold FI. rewrite lookup_total_insert.
          subst In'. rewrite flowint_outflow_map_set_domm.
          subst In. rewrite Domm_I0; try done.
        - unfold FI. rewrite lookup_total_insert_ne; try done.
          rewrite Domm_I0; try done. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct Hcl as [_ [_ Hcl]].
        by pose proof Hcl n n1 Hnx_n as H'. }  
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
      + rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * subst I0'. 
          assert (x ≠ n1) as H'.
          { clear -Hx n1_notin_I0. set_solver. }
          unfold FI.
          rewrite lookup_total_insert_ne; try done.
          subst II.
          apply Domm_II; try done.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          unfold FI. subst I0'.
          rewrite lookup_total_insert.
          subst In1'.
          rewrite flowint_inflow_map_set_dom.
          subst In1. rewrite Domm_I; try done.
          clear; set_solver.
  Qed.
  
  Lemma marking_flow_upd_II'_n0 Key n R Nx Mk S I I' II' nk n0 In0:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (n0 ∈ dom I') → (n ∈ dom I') → (n0 ≠ n) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (FI I' n0 = In0) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (FI II' n0 = In0).
  Proof.
    intros FI. apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key n0_in_I0 n_in_I0 n0_neq_n Key_I0 Def_I0_n0 [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key n0_in_I0 n_in_I0 n0_neq_n Key_I0 Def_I0_n0 Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 Hnx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      assert (n0 ≠ n1) as n0_neq_n1.
      { clear -n0_in_I0 n1_notin_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
      + unfold FI; rewrite /I0'.
        rewrite lookup_total_insert_ne.
        rewrite /II. rewrite lookup_total_insert_ne; try done.
        clear -n0_neq_n1; naive_solver.
  Qed.

  Lemma marking_flow_upd_II'_nk n R Nx Mk S I I' II' nk:
    let FI := λ I x, I !!! x in 
    (FI I' n = inflow_insert_set (FI I n) n S) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (FI II' nk = inflow_insert_set (FI I nk) nk S).
  Proof.
    intros FI. apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Def_I0_n [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Def_I0_n Hflow.
      apply HInd; try done; clear HInd.
      + rewrite /I0' /FI. rewrite lookup_total_insert. 
        rewrite /In1'. by rewrite /In1.
  Qed.

  Lemma marking_flow_upd_II' n R Nx Mk S I I' II' nk n0:
    let FI := λ I x, I !!! x in 
    (n ∈ dom I') →
    (FI I' n = inflow_insert_set (FI I n) n S) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → FI I' x = 
      outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (∀ x, x ∈ dom II' ∖ {[n0;nk]} → FI II' x = 
              outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S).
  Proof.
    intros FI. apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros n_in_I0 Def_I0_n I0_x [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd n_in_I0 Def_I0_n I0_x Hflow.
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + rewrite /I0'. unfold FI. rewrite lookup_total_insert.
        by rewrite /In1' /In1.
      + intros x. rewrite Dom_I0'. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        * destruct (decide (x = n)) as [-> | Hxn].
          -- unfold FI. subst I0'.
             rewrite lookup_total_insert_ne; 
             last by (clear -Hx2; set_solver).
             subst II. rewrite lookup_total_insert.
             subst In' In. unfold FI in Def_I0_n. rewrite Def_I0_n.
             assert (Nx !!! n = n1) as ->.
             { rewrite lookup_total_alt. rewrite Hnx_n. by simpl. }
             done.
          -- unfold FI. subst I0'.
             rewrite lookup_total_insert_ne; 
             last by (clear -Hx2; set_solver).
             subst II. rewrite lookup_total_insert_ne; try done.
             apply I0_x. clear -Hx1 Hx2 Hxn; set_solver.
        * clear -Hx1 Hx2; set_solver.
  Qed.

  Lemma marking_flow_upd_intfEq Key n R Nx Mk S I I' II' nk n0:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk I) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n0 ∈ dom I') → (n ∈ dom I') → (* (n0 ≠ n) → *)
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (FI I' n = inflow_insert_set (FI I n) n S) →
    (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) →
    ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x)).
  Proof.
    intros FI. apply marking_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key Hcl VI Domm_I n0_in_I0 n_in_I0 Key_I0 Def_I0_n 
        Dom_I0_in_I Domm_I0 Heq [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key Hcl VI Domm_I n0_in_I0 n_in_I0 Key_I0 Def_I0_n 
        Dom_I0_in_I Domm_I0 Heq Hflow.
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
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
      + rewrite /I0' /FI. rewrite lookup_total_insert. 
        rewrite /In1'. by rewrite /In1.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * subst I0'. 
          assert (x ≠ n1) as H'.
          { clear -Hx n1_notin_I0. set_solver. }
          unfold FI.
          rewrite lookup_total_insert_ne; try done.
          subst II.
          apply Domm_II; try done.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          unfold FI. subst I0'.
          rewrite lookup_total_insert.
          subst In1'.
          rewrite flowint_inflow_map_set_dom.
          subst In1. rewrite Domm_I; try done.
          clear; set_solver.
      + rewrite Dom_I0'.
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
            { (* syntactic rewriting *) admit. }
            by rewrite H'. }
        pose proof (flowint_insert_eq
                      ([^op set] y ∈ dom I0, I !!! y)
                      ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                      (I !!! n1)
                      In1' 
                      n1 
                      S) as Hpose. 
        assert (n1 ∈ dom (FI I n1)) as n1_in_In1.
        { rewrite Domm_I; try done. clear; set_solver. }
        assert (flowint_dom ([^op set] y ∈ dom I0, I !!! y) ≠ ∅) 
          as Domm_I0_notEmpty.
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
                    (flowint_dom ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y))))
            as H''.
          { intros n'. rewrite !flow_big_op_dom; try done.
            intros [x [Hx1 Hx2]]. exists x. split; try done.
            rewrite Domm_II. rewrite Domm_I in Hx2; try done.
            clear -Hx1 Dom_I0_in_I. set_solver. done. }
          clear -H' H''; set_solver. }
        assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) =
          outflow_insert_set ([^op set] y ∈ dom I0, I !!! y) n1 S) 
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
                dom ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
                as [Hn' | Hn'].
            + (* syntactic rewriting + flow_outf lemma *) admit.     
            + destruct (decide (n' = n1)) as [-> | Hn1'].
              * apply nzmap_eq. intros k'. 
                destruct (decide (k' ∈ S)) as [Hk' | Hk'].
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
        assert (In1' = inflow_insert_set (I !!! n1) n1 S) as H0''.
        { rewrite /In1' /In1. try done. }
        assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
        {  admit. }
        by pose proof Hpose n1_in_In1 Domm_I0_notEmpty H0' H0'' H0''' 
          as Hpose.
  Admitted.


  (*
  Lemma marking_flow_upd_nk_dom Key n R Nx Mk S I I' II' nk n0 In0:
    let FI := λ I x, I !!! x in 
    (* (nx_key_rel Nx Key) → *)
    (* (nx_mk_closed Nx Mk I) → *)
    (* (∀ x, x ∈ dom I → Mk !!! x = true → keyset (FI I x) = ∅) → *)
    (* (∀ n1 n2, Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) → *)
    (* (∀ n1 n2, n1 ∈ dom I' → Nx !! n1 = Some n2 → 
      dom (out_map (FI I' n1)) = {[n2]}) → *)
    (* (✓ ([^op set] x ∈ dom I, FI I x)) → *)
    (* (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) → *)
    (* (n0 ∈ dom I') → *) (* (n ∈ dom I') → *) (* (n0 ≠ n) → *)
    (* (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) → *)
    (* (∀ x, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) → *)
    (* (FI I' n0 = In0) → *)
    (* (FI I' n = inflow_insert_set (FI I n) n S) → *)
    (* (dom I' ⊆ dom I) → *)
    (* (∀ x, x ∈ dom I' ∖ {[n]} → Nx !! x ≠ None) → *)
    (* (∀ x, x ∈ dom I' ∖ {[n0; n]} → FI I' x = 
      outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S) → *)
    (* (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) → *)
    (* (∀ x, x ∈ dom I' ∖ {[n0; n]} → keyset (FI I' x) = keyset (FI I x)) → *)
    (* ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) → *)
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
        (nk ∈ dom II').
  Proof.
  Admitted.
  *)
    
  Lemma marking_flow_upd_invariants Key n R Nx Mk S I I' II' nk n0 In0:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk I) →
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
    (FI I' n = inflow_insert_set (FI I n) n S) →
    (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' ∖ {[n]} → Nx !! x ≠ None) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → FI I' x = 
      outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S) →
    (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → keyset (FI I' x) = keyset (FI I x)) →
    ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
    marking_flow_upd_rec n R Nx Mk S I I' = Some (II', nk) →
          ((dom II' ⊆ dom I)
        ∧ (n0 ≠ nk)
        ∧ (n0 ∈ dom II') 
        ∧ (nk ∈ dom II')
        ∧ (Mk !! nk = Some false)
        ∧ (∀ x, x ∈ dom II' ∖ {[nk]} → Nx !! x ≠ None)
        ∧ (∀ x, x ∈ dom II' → dom (FI II' x) = {[x]})
        ∧ (([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x))
        ∧ (FI II' n0 = In0)
        ∧ (FI II' nk = inflow_insert_set (FI I nk) nk S)
        ∧ (∀ x, x ∈ dom II' ∖ {[n0;nk]} → FI II' x = 
              outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S)
        ∧ (∀ x, x ∈ dom II' ∖ {[ n0; nk ]} → keyset (FI II' x) = keyset (FI I x))).
  Proof.
    intros FI. 
    intros Nx_key Hcl KS_mk Nx_dom Nx_dom0 VI Domm_I n0_in_I0 
        n_in_I0 n0_neq_n Key_I0 Key_n0 Def_I0_n0 Def_I0_n Dom_I0_in_I 
        Nx_x I0_x Domm_I0 KS_I' Heq Hflow.
    repeat split.
    - apply (marking_flow_upd_dom Key n R Nx Mk S I I' II' nk); try done.
    - apply (marking_flow_upd_neq Key n R Nx Mk S I I' II' nk); try done.
    - apply (marking_flow_upd_n0_dom n R Nx Mk S I I' II' nk); try done.
    - apply (marking_flow_upd_nk_dom n R Nx Mk S I I' II' nk); try done.
    - apply (marking_flow_upd_Mk_nk n R Nx Mk S I I' II' nk); try done.
    - apply (marking_flow_upd_Nx Key n R Nx Mk S I I' II' nk n0); try done.
    - apply (marking_flow_upd_domm Key n R Nx Mk S I I' II' nk); try done.
    - apply (marking_flow_upd_intfEq Key n R Nx Mk S I I' II' nk n0); try done.
    - apply (marking_flow_upd_II'_n0 Key n R Nx Mk S I I' II' nk n0); try done.
    - apply (marking_flow_upd_II'_nk n R Nx Mk S I I' II' nk); try done.
    - apply (marking_flow_upd_II' n R Nx Mk S I I' II' nk n0); try done.
    - admit.
  Admitted.

  Lemma marking_flow_upd_summary Key n0 Nx Mk S I res n1:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk I) →
    (∀ x, x ∈ dom I → Mk !!! x = true → keyset (FI I x) = ∅) →
    (∀ n1 n2, Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) →
    (Nx !! n0 = Some n1) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n0 ∈ dom I) →
    (S ⊆ insets (FI I n0)) →
    (S ## outsets (FI I n0)) →
    marking_flow_upd n0 Nx Mk S I = res →
      ∃ II nk, 
        res = Some (II, nk)
      ∧ (dom II ⊆ dom I)
      ∧ (n0 ∈ dom II)
      ∧ (nk ∈ dom II)
      ∧ (n0 ≠ nk)
      ∧ (Mk !! nk = Some false)
      ∧ (∀ x, x ∈ dom II ∖ {[n0;nk]} → Mk !! x = Some true)
      ∧ (∀ x, x ∈ dom II ∖ {[nk]} → Nx !! x ≠ None)
      ∧ (∀ x, x ∈ dom II ∖ {[n0]} → Key !!! n0 < Key !!! x)
      ∧ (∀ x, x ∈ dom II → dom (FI II x) = {[x]})
      ∧ (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x))
      ∧ (FI II n0 = outflow_insert_set (FI I n0) n1 S)
      ∧ (FI II nk = inflow_insert_set (FI I nk) nk S)
      ∧ (∀ x, x ∈ dom II ∖ {[ n0; nk ]} → FI II x = 
              outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S)
      ∧ (keyset (FI II n0) = keyset (FI I n0) ∖ S)
      ∧ (∀ x, x ∈ dom II ∖ {[ n0; nk ]} → keyset (FI II x) = keyset (FI I x)).
  Proof.
    intros FI Nx_key Hcl KS_mk Nx_dom Hnx_n0 VI Domm_I n0_in_I 
      Insets_S Outsets_S Hflow.
    unfold marking_flow_upd in Hflow.
    rewrite Hnx_n0 in Hflow. 
    set In1 := inflow_insert_set (I !!! n1) n1 S.
    set In0 := outflow_insert_set (I !!! n0) n1 S.
    set I': gmap Node (multiset_flowint_ur nat) := {[n1 := In1; n0 := In0]}.
    assert (In1 = inflow_insert_set (I !!! n1) n1 S) as Def_In1 by done.
    assert (In0 = outflow_insert_set (I !!! n0) n1 S) as Def_In0 by done.
    assert (I' = {[n1 := In1; n0 := In0]}) as Def_I' by done.
    rewrite <-Def_In1 in Hflow.
    rewrite <-Def_In0 in Hflow.
    rewrite <-Def_I' in Hflow.
    assert (dom I' = {[n0; n1]}) as Dom_I' by set_solver.
    assert (n1 ∈ dom I') as n1_in_I' by set_solver.
    assert (n1 ∈ dom I) as n1_in_I.
    { destruct Hcl as [_ [_ Hcl]]. 
      by apply (Hcl n0). }
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
    assert (Key !!! n0 < Key !!! n1) as Key_n0_n1.
    { by apply Nx_key in Hnx_n0. }
    assert (∀ x : Node, x ∈ dom I' → Key !!! x ≤ Key !!! n1) as Key_I'.
    { rewrite Dom_I'. intros x; rewrite elem_of_union.
      intros [Hx | Hx].
      - assert (x = n0) as -> by set_solver. lia.
      - assert (x = n1) as -> by set_solver. try done. }
    
    pose proof marking_flow_upd_rec_defined Key n1 (dom I ∖ {[n0]}) 
      Nx Mk S I I' Nx_key Hcl n1_in_I' H' H'' Key_I' as Hpose.
    clear H' H''.
    destruct (marking_flow_upd_rec n1 (dom I ∖ {[n0]}) Nx Mk S I I') 
      as [ (II, nk) |] eqn: Hflow1; try done. clear Hpose.
    
    assert (n0 ∈ dom I') as n0_in_I'.
    { rewrite Dom_I'. clear; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) as Key_n0.
    { intros x. rewrite Dom_I'. rewrite elem_of_difference.
      rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2]; try done.
      assert (x = n1) as -> by set_solver. done. }
    assert (FI I' n1 = inflow_insert_set (FI I n1) n1 S) as Def_I'_n.
    { unfold FI. subst I'. rewrite lookup_total_insert; try done.  }    
    assert (dom I' ⊆ dom I) as Dom_I'_in_I.
    { rewrite Dom_I'; clear -n0_in_I n1_in_I; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n1]} → Nx !! x ≠ None) as Nx_x.
    { rewrite Dom_I'. intros x Hx. 
      assert (x = n0) as -> by (clear -Hx; set_solver).
      rewrite Hnx_n0. done. }
    assert (∀ x, x ∈ dom I' ∖ {[n0;n1]} → FI I' x = 
      outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S) as I'_x.
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
        subst In1. rewrite flowint_inflow_insert_set_dom.
        rewrite Domm_I; try done. clear; set_solver. }
    assert (I' !!! n0 = In0) as Def_I'_n0.
    { subst I'. rewrite lookup_total_insert_ne; try done.
      rewrite lookup_total_insert; done. }      
    assert (([^op set] x ∈ dom I', FI I x) = 
                ([^op set] x ∈ dom I', FI I' x)) as Heq.
    { admit. }
    assert (✓ (I !!! n0 ⋅ I !!! n1)) as VI'.
    { assert ({[n0; n1]} ⊆ dom I) as Hsub.
      { clear -n1_in_I n0_in_I' Dom_I'_in_I. set_solver. }
      pose proof (flow_big_op_valid _ _ {[n0; n1]} Hsub VI) as VI'.
      rewrite big_opS_union in VI'.
      rewrite !big_opS_singleton in VI'.
      by unfold FI in VI'. clear -n0_neq_n1. set_solver. }

    assert (insets In0 = insets (I !!! n0)) as H1'.
    { by rewrite outflow_insert_set_insets. }
    assert (dom (out_map In0) = dom (out_map (FI I n0))) as Domout_map.
    { rewrite /In0. unfold outflow_insert_set, outflow_map_set.
      simpl. apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero.
      unfold FI. rewrite (Nx_dom n0 n1 Hnx_n0).
      clear; set_solver.
      (*
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
      unfold FI in H''. clear -Hn H''; try done.
      *) admit. }
    assert (outsets In0 = outsets (I !!! n0) ∪ S) as H1''.
    { unfold outsets.
      pose proof (Nx_dom n0 n1 Hnx_n0) as Nx_dom.
      unfold FI in Nx_dom. rewrite Domout_map.
      rewrite Nx_dom. apply leibniz_equiv. rewrite !big_opS_singleton.
      rewrite /In0. rewrite outflow_insert_set_outset; try done. }
    (*
    assert (S  insets (I !!! n1)) as Insets_S1.
    { intros k Hk. unfold insets. 
      rewrite (Domm_I n1 n1_in_I).
      rewrite big_opS_singleton.
      apply (flowint_inset_step (I !!! n0) (I !!! n1)); try done.
      - unfold FI in Domm_I. rewrite (Domm_I n1 n1_in_I).
        clear; set_solver.
      - unfold outset. rewrite nzmap_elem_of_dom_total; try done.
        (*
        rewrite Outset_S. unfold ccmunit, ccm_unit. simpl. 
        unfold nat_unit. clear; lia. done. *)
        admit. }
    *)
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0; n1]} →  
      keyset (I' !!! x) = keyset (I !!! x)) as KS_I'.
    { rewrite Dom_I'. intros x Hx. clear -Hx; set_solver. }  

    assert (keyset In0 = keyset (I !!! n0) ∖ S) as KS_n0.
    { unfold keyset. rewrite H1' H1''. 
      apply set_eq_subseteq.
      split; clear -Insets_S Outsets_S; set_solver. }
    assert (∀ n1 n2, n1 ∈ dom I' → Nx !! n1 = Some n2 → 
      dom (out_map ((I' !!! n1: multiset_flowint_ur nat))) = {[n2]}) as Nx_dom'.
    { admit. }
      
    
    
    pose proof marking_flow_upd_invariants Key n1 (dom I ∖ {[n0]}) Nx Mk S 
      I I' II nk n0 In0 Nx_key Hcl KS_mk Nx_dom Nx_dom' VI Domm_I 
      n0_in_I' n1_in_I' n0_neq_n1 Key_I' Key_n0 Def_I'_n0 Def_I'_n 
      Dom_I'_in_I Nx_x I'_x Domm_I' KS_I' Heq Hflow1 
      as [HInv1 [HInv2 [HInv3 [HInv4 [HInv5 
            [HInv6 [HInv7 [HInv8 [HInv9 [HInv10 [HInv11 HInv13]]]]]]]]]]].

    exists II, nk. repeat (split; try done). admit. admit.
    unfold FI at 1. by rewrite HInv9.
  Admitted.

End marking_flow_upd.