Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
(* From Coq Require Import QArith Qcanon. *)
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

(* Unbounded (multiset) flow update over a list *)

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
  
  Implicit Types I II : gmap Node (multiset_flowint_ur nat).
  Implicit Types S : gset nat.  
  Implicit Types R : gset Node.
  Implicit Type Key : gmap Node nat.
  Implicit Type n : Node.
  Implicit Type Nx : gmap Node Node.
  Implicit Type Mk : gmap Node bool.
  
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
      (dom Nx ⊆ N)
    ∧ (dom Mk = N)  
    ∧ (∀ n1 n2, Nx !! n1 = Some n2 → n2 ∈ N)
    ∧ (∀ n, Mk !! n = Some true → Nx !! n ≠ None).

  Lemma list_flow_upd_Key_I0_rec Key Nx n n1 
    (I0 I0': gmap Node (multiset_flowint_ur nat)) :
    (nx_key_rel Nx Key) →
    Nx !! n = Some n1 →
    (n ∈ dom I0) →
    (dom I0' = dom I0 ∪ {[n1]}) →
    (∀ x, x ∈ dom I0 → Key !!! x ≤ Key !!! n) →
          (∀ x, x ∈ dom I0' → Key !!! x ≤ Key !!! n1).
  Proof.
    intros Nx_key Hnx_n n_in_I0 Dom_I0' Key_I0.
    pose proof Nx_key n n1 Hnx_n as H'. 
    rewrite Dom_I0'. intros x; rewrite elem_of_union.
    intros [Hx | Hx].
    - apply Key_I0 in Hx. clear -Hx H'. lia.
    - assert (x = n1) as -> by (clear -Hx; set_solver).
      clear; try done.
  Qed.

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
      destruct Hcl as (_&H'&_). clear -H' HMk_n n_in_I' Dom_I; set_solver.
    - clear n R Nx Mk S I I'. 
      intros n R Nx Mk S I I' n_in_R HMk_n Nx_n Nx_key Hcl n_in_I' 
        Dom_I R_inter_I Key_I'.
      destruct Hcl as (_&_&_&H'). exfalso. apply (H' n); try done.
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
      { destruct Hcl as (_&_&Hcl&_).
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
      + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done. 
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
      { destruct Hcl as (_&_&Hcl&_).
        by pose proof Hcl n n1 Hnx_n as H'. }  
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'; set_solver.
      + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done.
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
      + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done.
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

  Lemma list_flow_upd_Key_n0_rec Key Nx n n1 n0
    (I0 I0': gmap Node (multiset_flowint_ur nat)) :
    (nx_key_rel Nx Key) →
    Nx !! n = Some n1 →
    (n ∈ dom I0) → (n0 ∈ dom I0) →
    (dom I0' = dom I0 ∪ {[n1]}) →
    (∀ x, x ∈ dom I0 → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I0 ∖ {[n0]} → Key !!! n0 < Key !!! x) →
          (∀ x, x ∈ dom I0' ∖ {[n0]} → Key !!! n0 < Key !!! x).
  Proof.
    intros Nx_key Hnx_n n_in_I0 n0_in_I0 Dom_I0' Key_I0 Key_n0.
    rewrite Dom_I0'. intros x. rewrite elem_of_difference.
    rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
    + apply Key_n0. clear -Hx1 Hx2; set_solver.
    + assert (x = n1) as -> by (clear -Hx1; set_solver). 
      pose proof Nx_key n n1 Hnx_n as H'.
      assert (Key !!! n0 ≤ Key !!! n) as H''.
      { by apply Key_I0. }
      clear -H' H''. lia.
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
      + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done.
      + apply (list_flow_upd_Key_n0_rec Key Nx n n1 n0 I0 I0'); try done.
      + intros x. rewrite Dom_I0'. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        * destruct (decide (x = n)) as [-> | Hxn].
          -- by rewrite Hnx_n.
          -- apply Nx_x. clear -Hx1 Hx2 Hxn; set_solver.
        * clear -Hx1 Hx2; set_solver.
  Qed.

  Lemma list_flow_upd_Mk f n R Nx Mk S I I' II' nk n0:
    (n0 ∈ dom I') → (n ∈ dom I') →
    (∀ x, x ∈ dom I' ∖ {[n0;n]} → Mk !! x = Some true) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
          (∀ x, x ∈ dom II' ∖ {[n0;nk]} → Mk !! x = Some true).
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros n0_in_I0 n_in_I0 Mk_x [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd n0_in_I0 n_in_I0 Mk_x Hflow.
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. set_solver.
      + intros x. rewrite Dom_I0'. rewrite elem_of_difference.
        rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2].
        * destruct (decide (x = n)) as [-> | Hxn].
          -- by rewrite Hmk_n.
          -- apply Mk_x. clear -Hx1 Hx2 Hxn; set_solver.
        * clear -Hx1 Hx2; set_solver.
  Qed.

  Lemma list_flow_upd_Key_n0 Key f n R Nx Mk S I I' II' nk n0:
    (nx_key_rel Nx Key) →
    (n0 ∈ dom I') → (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
          (∀ x, x ∈ dom II' ∖ {[n0]} → Key !!! n0 < Key !!! x).
  Proof.
    apply list_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key n0_in_I0 n_in_I0 Key_I0 Key_n0 [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key n0_in_I0 n_in_I0 Key_I0 Key_n0 Hflow.
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II. repeat rewrite dom_insert_L.
        clear -n_in_I0. set_solver. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. set_solver.
      + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done.
      + apply (list_flow_upd_Key_n0_rec Key Nx n n1 n0 I0 I0'); try done.
  Qed.

  
  Lemma list_flow_upd_domm_rec Key f S Nx n n1 
    (I I0: gmap Node (multiset_flowint_ur nat)) :
    let FI := λ I x, I !!! x in
    let In := I0 !!! n in
    let In' := outflow_map_set f In n1 S in
    let In1 := I !!! n1 in
    let In1' := inflow_map_set f In1 n1 S in
    let II := <[n:=In']> I0 in
    let I0' := <[n1:=In1']> II in
    (n ∈ dom I0) → (n1 ∉ dom I0) → (n1 ∈ dom I) → 
    (dom I0' = dom I0 ∪ {[n1]}) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (∀ x, x ∈ dom I0 → dom (FI I0 x) = {[x]}) →
          (∀ x, x ∈ dom I0' → dom (FI I0' x) = {[x]}).
  Proof.
    intros FI In In' In1 In1' II I0'.
    intros n_in_I0 n1_notin_I0 n1_in_I Dom_I0' Domm_I Domm_I0.
    rewrite Dom_I0'. intros x; rewrite elem_of_union. intros [Hx | Hx].
    - assert (x ≠ n1) as H'.
      { clear -Hx n1_notin_I0. set_solver. }
      rewrite /I0' /FI lookup_total_insert_ne; try done.
      rewrite /II. destruct (decide (n = x)) as [-> | Hxn].
      + rewrite /FI lookup_total_insert /In' flowint_outflow_map_set_domm.
        rewrite /In Domm_I0; try done.
      + rewrite /FI lookup_total_insert_ne; try done. rewrite Domm_I0; try done.
    - rewrite elem_of_singleton in Hx. subst x.
      rewrite /FI /I0' lookup_total_insert /In1' flowint_inflow_map_set_dom.
      rewrite /In1 Domm_I; try done. clear; set_solver. 
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
      { destruct Hcl as (_&_&Hcl&_).
        by pose proof Hcl n n1 Hnx_n as H'. }  
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done.
      + apply (list_flow_upd_domm_rec Key f S Nx n n1 I I0); try done.
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
      + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done.
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

  Lemma list_flow_upd_Insets_ne Key f n R Nx Mk S I I' II' nk:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (∀ x, x ∈ dom I → Mk !!! x = true → keyset (I !!! x) = ∅) →    
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (∀ n1 n2, insets (FI I n1) ≠ ∅ → 
      Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) →
    (n ∈ dom I') → (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (∀ x, x ∈ dom I' → insets (FI I x) ≠ ∅) →
    list_flow_upd_rec f n R Nx Mk S I I' = Some (II', nk) →
        (∀ x, x ∈ dom II' → insets (FI I x) ≠ ∅).
  Proof.
  intros FI. apply list_flow_upd_rec_ind; try done; last first.
  - clear n R Nx Mk S I I'.
    intros n R Nx Mk S I I0 n_in_R Hmk_n.
    intros Nx_key Hcl KS_mk VI Domm_I Nx_dom n_in_I0 
      Dom_I0_in_I Key_I0 Insets_ne [= -> ->].
    done.
  - clear n R Nx Mk S I I'.
    intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
    intros HInd Nx_key Hcl KS_mk VI Domm_I Nx_dom n_in_I0 
      Dom_I0_in_I Key_I0 Insets_ne Hflow.
    assert (n1 ∉ dom I0) as n1_notin_I0.
    { pose proof Nx_key n n1 Hnx_n as H'.
      intros n1_in_I0. apply Key_I0 in n1_in_I0.
      clear -H' n1_in_I0. lia. }
    assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
    { rewrite /I0' /II. repeat rewrite dom_insert_L.
      clear -n_in_I0 n1_notin_I0. set_solver. }
    assert (n1 ∈ dom I) as n1_in_I.
    { destruct Hcl as (_&_&Hcl&_).
      by pose proof Hcl n n1 Hnx_n as H'. }
    assert (n ∈ dom I) as n_in_I.
    { by apply Dom_I0_in_I. }
    assert (n ≠ n1) as n_neq_n1.
    { clear -n_in_I0 n1_notin_I0. set_solver. }

    assert (insets (FI I n) ≠ ∅) as Insets_ne'.
    { by apply Insets_ne. }
    assert (outsets (FI I n) ≠ ∅) as H'.
    { apply lookup_total_correct in Hmk_n. apply KS_mk in Hmk_n; try done.
      rewrite /keyset in Hmk_n. clear -Hmk_n Insets_ne'. set_solver. } 
    assert (insets (FI I n1) ≠ ∅) as Insets_ne''.
    { apply set_choose_L in H'. destruct H' as [k H'].
      apply (non_empty_inhabited_L k).
      rewrite /insets Domm_I. rewrite big_opS_singleton.
      rewrite /outsets in H'.
      rewrite (Nx_dom n n1 Insets_ne' Hnx_n) big_opS_singleton in H'.
      apply (flowint_inset_step (FI I n)); try done.
      assert ({[n;n1]} ⊆ dom I) as H''.
      { clear -n1_in_I n_in_I; set_solver. }
      pose proof flow_big_op_valid _ _ _ H'' VI  as H1'.
      rewrite (big_opS_delete _ _ n) in H1'.
      assert ({[n;n1]} ∖ {[n]} = ({[n1]}: gset Node)) as H1''.
      { clear -n_neq_n1; set_solver. }
      by rewrite H1'' big_opS_singleton in H1'.
      clear; set_solver. rewrite Domm_I. clear; set_solver. done. done. }

    apply HInd; clear HInd; try done.
    + rewrite Dom_I0'; clear; set_solver.
    + rewrite Dom_I0'; clear -Dom_I0_in_I n1_in_I; set_solver.
    + apply (list_flow_upd_Key_I0_rec Key Nx n n1 I0 I0'); try done.
    + intros x. rewrite Dom_I0' elem_of_union. intros [Hx | Hx].
      * apply Insets_ne; try done.
      * rewrite elem_of_singleton in Hx; subst x. by apply Insets_ne''. 
  Qed.


End list_flow_upd.

  
  
  
