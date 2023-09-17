Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
(* From Coq Require Import QArith Qcanon. *)
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

Section list_flow_upd.
  Open Scope ccm_scope.

  Function list_flow_upd_rec f (n: Node) (R: gset Node)
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
        let In' := outflow_map_set f In n1 S in
        (* Pick from I because n1 must be untouched so far *)
        let In1 := I !!! n1 in
        (* Add S to inf(In1, n1) *)
        let In1' := inflow_map_set f In1 n1 S in
        let II := <[n := In']> I' in
        let II' := <[n1 := In1']> II in  
        list_flow_upd_rec f n1 (R ∖ {[n]}) Nx Mk S I II' end
    | Some false => Some (I', n) end end.
  intros f n R Nx Mk S I I' Hbool. intros.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.

  Definition list_flow_upd f n0 Nx Mk S I :=
    match Nx !! n0 with
    | None => None
    | Some n1 =>
      let In0 := I !!! n0 in
      let In0' := outflow_map_set f In0 n1 S in
      let In1 := I !!! n1 in
      let In1' := inflow_map_set f In1 n1 S in
      let I' := <[n1 := In1']> ({[n0 := In0']}) in
      list_flow_upd_rec f n1 (dom I ∖ {[n0]}) Nx Mk S I I' end.
  
  Definition nx_key_rel (Nx: gmap Node Node) (Key: gmap Node nat) :=
    ∀ n1 n2, Nx !! n1 = Some n2 → (Key !!! n1 < Key !!! n2). 

  Definition nx_mk_closed (Nx: gmap Node Node) (Mk: gmap Node bool)
    (N: gset Node) :=
      (dom Nx = N)
    ∧ (dom Mk = N)  
    ∧ (∀ n1 n2, Nx !! n1 = Some n2 → n2 ∈ N).

  Lemma list_flow_upd_rec_defined Key f n R Nx Mk S I I':
    (nx_key_rel Nx Key) → 
    (nx_mk_closed Nx Mk (dom I)) →
    (n ∈ dom I') →
    (dom I = R ∪ dom I') →
    (R ∩ dom I' = {[n]}) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
      list_flow_upd_rec f n R Nx Mk S I I' ≠ None.
  Proof.
    apply list_flow_upd_rec_ind; try done.
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
  Qed.
  
  Lemma list_flow_upd_dom Key f n R Nx Mk S I I' II' nk:
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (dom I' ⊆ dom I) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
          (dom II' ⊆ dom I).
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_neq Key f n R Nx Mk S I I' II' nk n0:
    (nx_key_rel Nx Key) →
    (n0 ∈ dom I') → (n ∈ dom I') → (n0 ≠ n) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (n0 ≠ nk).
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_n0_dom f n R Nx Mk S I I' II' nk n0:
    (n0 ∈ dom I') → (n ∈ dom I') →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (n0 ∈ dom II').
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_nk_dom f n R Nx Mk S I I' II' nk:
    (n ∈ dom I') →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (nk ∈ dom II').
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_Mk_nk f n R Nx Mk S I I' II' nk:
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (Mk !! nk = Some false).
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
    clear n R Nx Mk S I I'.
    intros n R Nx Mk S I I0 n_in_R Hmk_n [= -> ->].
    done.
  Qed.
  
  Lemma list_flow_upd_Nx Key f n R Nx Mk S I I' II' nk n0:
    (nx_key_rel Nx Key) →
    (n0 ∈ dom I') → (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) →
    (∀ x, x ∈ dom I' ∖ {[n]} → Nx !! x ≠ None) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
          (∀ x, x ∈ dom II' ∖ {[nk]} → Nx !! x ≠ None).
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_domm Key f n R Nx Mk S I I' II' nk:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (∀ x, x ∈ dom II' → dom (FI II' x) = {[x]}).
  Proof.
    intros FI. apply list_flow_upd_rec_ind; try done; last first.
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
  
  Lemma list_flow_upd_II'_n0 Key f n R Nx Mk S I I' II' nk n0 In0:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (n0 ∈ dom I') → (n ∈ dom I') → (n0 ≠ n) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (FI I' n0 = In0) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (FI II' n0 = In0).
  Proof.
    intros FI. apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_II'_nk f n R Nx Mk S I I' II' nk:
    let FI := λ I x, I !!! x in 
    (FI I' n = inflow_map_set f (FI I n) n S) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (FI II' nk = inflow_map_set f (FI I nk) nk S).
  Proof.
    intros FI. apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_II' f n R Nx Mk S I I' II' nk n0:
    let FI := λ I x, I !!! x in 
    (n ∈ dom I') →
    (FI I' n = inflow_map_set f (FI I n) n S) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → FI I' x = 
      outflow_map_set f (inflow_map_set f (FI I x) x S) (Nx !!! x) S) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (∀ x, x ∈ dom II' ∖ {[n0;nk]} → FI II' x = 
              outflow_map_set f (inflow_map_set f (FI I x) x S) (Nx !!! x) S).
  Proof.
    intros FI. apply list_flow_upd_rec_ind; try done; last first.
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

  Lemma list_flow_upd_intfEq Key f n R Nx Mk S I I' II' nk n0:
    let FI := λ I x, I !!! x in 
    (∀ k x y : nat, x ≤ y → f k x ≤ f k y) →
    (∀ k x y : nat, k ∈ S → (x - y)%nat = (f k x - f k y)%nat) →
    (∀ k x y : nat, k ∈ S → (f k x + y)%nat = (f k (x + y))%nat) →
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n0 ∈ dom I') → (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (FI I' n = inflow_map_set f (FI I n) n S) →
    (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) →
    ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x)).
  Proof.
    intros FI. apply list_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Hf1 Hf2 Hf3 Nx_key Hcl VI Domm_I n0_in_I0 n_in_I0 Key_I0 Def_I0_n 
        Dom_I0_in_I Domm_I0 Heq [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Hf1 Hf2 Hf3 Nx_key Hcl VI Domm_I n0_in_I0 n_in_I0 Key_I0 
        Def_I0_n Dom_I0_in_I Domm_I0 Heq Hflow.
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
                        (I0 !!! n) (In') f n1 S).
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
        pose proof (flowint_map_set_eq f
                      ([^op set] y ∈ dom I0, I !!! y)
                      ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                      (I !!! n1) In1' n1 S) as Hpose.
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
          outflow_map_set f ([^op set] y ∈ dom I0, I !!! y) n1 S) 
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
                   rewrite !flow_big_op_out; try done.
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
                     rewrite /In. rewrite -/(FI I0 n).
                     apply Hf3; try done. done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_I0 in Hx2; try done.
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
        assert (In1' = inflow_map_set f (I !!! n1) n1 S) as H0''.
        { rewrite /In1' /In1. try done. }
        assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
        { assert (dom I0 ∪ {[ n1 ]} ⊆ dom I) as Hsub.
          { clear -n1_in_I Dom_I0_in_I. set_solver. }
          pose proof (flow_big_op_valid _ _ (dom I0 ∪ {[n1]}) Hsub VI) as H'.
          rewrite big_opS_union in H'.
          by rewrite big_opS_singleton in H'.
          clear -n1_notin_I0. set_solver. }
        apply Hpose; try done. intros k. apply Hf2.
  Qed.
  
End list_flow_upd.
  
  
  
  
