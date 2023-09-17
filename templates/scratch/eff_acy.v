(** Formalization of Effective Acyclicity Framework *)

From iris.algebra Require Export monoid auth updates local_updates.
From stdpp Require Export gmap.
From stdpp Require Import mapset finite.
Require Export flow_graph.
Require Import Coq.Setoids.Setoid.

Section flow_graph.

(* The underlying flow domain. *)
Context `{CCM flow_dom} `{Countable flow_dom}.

Open Scope ccm_scope.


(* Relating flow graph to flow interface *)

Definition inf_fg (h: flow_graphT) : gmap Node flow_dom :=
  match h with
  | fgUndef => ∅
  | fg {| edgeR := ef; flowR := fl |} => 
    let f1 := λ n m inf', <[n := m - (edgeflow h n)]> inf' in
    map_fold f1 ∅ fl end.

Definition outf_fg (h: flow_graphT) : nzmap Node flow_dom :=
  match h with
  | fgUndef => ∅
  | fg {| edgeR := ef; flowR := fl |} => 
    let f1 := λ n n' e_nn' res_n, 
              if (decide (n' ∈ dom fl)) then res_n 
              else <<[n' := (res_n ! n') + (e_nn' ! (fl !!! n))]>> res_n in  
    let f2 := λ n map_n res, 
              map_fold (f1 n) res (nzmap_car map_n) in
    map_fold f2 (∅: nzmap Node flow_dom) (nzmap_car ef) end.

Definition flowint_of_fg (h: flow_graphT) : flowintT :=
  match h with
  | fgUndef => intUndef
  | _ => int {| infR := inf_fg h; outR := outf_fg h |} end.

Lemma flowint_of_fg_valid h : ✓ h → ✓ (flowint_of_fg h).
Proof.
Admitted.
    
Definition delta (n n': Node) (m: flow_dom) : flow_dom :=
  if (decide (n = n')) then m else 0.
  
Fixpoint cap_i (i: nat) (h: flow_graphT) (n n': Node) (m: flow_dom) : flow_dom :=
  match i with
  | 0 => delta n n' m
  | S i' => delta n n' m + (fg_edge h n n' ! (cap_i i' h n n' m)) end.
  
Definition cap (h: flow_graphT) (n n': Node) (m: flow_dom) : flow_dom :=
  cap_i (size (domm h)) h n n' m.

(* Contextual extension of flow interfaces. *)
Definition subflow_ext (h h': flow_graphT) : Prop := 
  ✓ h ∧ ✓ h'
  ∧ contextualLeq _ (flowint_of_fg h) (flowint_of_fg h')
  ∧ (∀ n n' m, n ∈ domm h → n' ∉ domm h' → 
                (inf_fg h !!! n) = (inf_fg h !!! n) + (m - (inf_fg h !!! n)) → 
                  cap h n n' m = cap h' n n' m)
  ∧ (∀ n n' m, n ∈ domm h' ∖ domm h → n' ∉ domm h' → 
                (inf_fg h !!! n) = (inf_fg h !!! n) + (m - (inf_fg h !!! n)) → 
                  cap h' n n' m = 0).

Fixpoint chain (f: Node → Node → flow_dom → flow_dom) 
  (xs : list Node) (n: Node) (m: flow_dom) : flow_dom :=
  match xs with
  | [] => m
  | n1 :: [] => f n1 n m
  | n1 :: (n2 :: _ as xs') => chain f (xs') n (f n1 n2 m) end.

(*
Fixpoint chains (e: efT) (xss : list (list Node)) (n: Node) (m: flow_dom) : flow_dom :=
  match xss with
  | [] => m
  | xs :: [] => chain e xs n m
  | xs1 :: (xs2 :: _ as xss') => chains e (xss') n (chain e xs1 (hd 0 xs2) m) end.
*)

Fixpoint chains' (F: list Node → Node → flow_dom → flow_dom) 
  (xss: list (list Node)) (n: Node) (m: flow_dom) : flow_dom :=
  match xss with
  | [] => m
  | xs :: [] => F xs n m
  | xs1 :: (xs2 :: _ as xss') => chains' F xss' n (F xs1 (hd 0 xs2) m) end.

Definition chains (f: Node → Node → flow_dom → flow_dom) 
  (xss : list (list Node)) (n: Node) (m: flow_dom) : flow_dom :=
  chains' (λ xs n' m', chain f xs n' m') xss n m.  

Definition eff_acy_aux (h: flow_graphT) ns : Prop := 
  let hd_ns ns := hd 0 ns in
  let flow_n n := flow_map h !!! n in
  let f n n' m := (edge_map h) ! n ! n' ! m in 
  chain f ns (hd_ns ns) (flow_n (hd_ns ns)) = 0.

(* Fix hd default *)  
Definition eff_acy (h: flow_graphT) : Prop := 
  let hd_ns ns := hd 0 ns in
  let k_paths k := k_lists k (elements (domm h)) in
  let flow_n n := flow_map h !!! n in  
  let seq_h := seq 1 (size (domm h)) in
  Forall (λ k, Forall (λ ns, eff_acy_aux h ns) (k_paths k)) seq_h.

Global Instance eff_acy_aux_dec: ∀ h ns, Decision (eff_acy_aux h ns).
Proof.
  intros h ns; unfold eff_acy_aux; try done.
Qed.  

Global Instance eff_acy_dec: ∀ h, Decision (eff_acy h).
Proof.
  intros h; unfold eff_acy; apply Forall_dec.
  intros k; apply Forall_dec; intros ns; 
  unfold eff_acy_aux; try done.
Qed.

Lemma eff_acy_neg h : 
  let hd_ns ns := hd 0 ns in
  let k_paths k := k_lists k (elements (domm h)) in
  let flow_n n := flow_map h !!! n in
  let f n n' m := (edge_map h) ! n ! n' ! m in   
  ¬ eff_acy h → ∃ ns, chain f ns (hd_ns ns) (flow_n (hd_ns ns)) ≠ 0.
Proof.
  intros hd_ns k_paths flow_n f Heff.
  assert (∀ k, {Forall (λ ns, eff_acy_aux h ns) (k_paths k)} + 
    {~ Forall (λ ns, eff_acy_aux h ns) (k_paths k)}) as H'.
  { intros k; apply Forall_dec. apply eff_acy_aux_dec. }
  unfold eff_acy in Heff.
  pose proof (neg_Forall_Exists_neg H' Heff) as H''.
  apply Exists_exists in H''.
  destruct H'' as [k [Hk H'']]. clear H'.
  assert (∀ ns, {eff_acy_aux h ns} + {~ eff_acy_aux h ns}) as H'.
  { apply eff_acy_aux_dec. }
  pose proof (neg_Forall_Exists_neg H' H'') as H'''.
  apply Exists_exists in H'''.
  destruct H''' as [ns [Hns H''']]. clear H'.
  exists ns. apply H'''.
Qed.

Lemma domm_int_fg h : flows.domm (flowint_of_fg h) = domm h.
Proof.
Admitted.

(* Assumes x in X1 *)  
Definition k_alternating (h1 h2: flow_graphT) (k: nat) (n: Node)  :=
  let P n := bool_decide (n ∈ domm h1) in
  let Q n := bool_decide (n ∈ domm h2) in
  let f xs := alternating P Q xs in
  let res' := filter f (k_lists (k-1) (elements (domm h1 ∖ {[n]} ∪ domm h2))) in
  let f' xs := n :: xs in
  map f' res'.  

Lemma cap_comp_chain_aux (h1 h2: flow_graphT) :
  let inf n := inf_fg (h1 ⋅ h2) !!! n in
  let F n n' m := if bool_decide (n ∈ domm h1) then cap h1 n n' m 
                  else if bool_decide (n ∈ domm h2) then cap h2 n n' m else 0 in 
  ✓ (h1 ⋅ h2) → eff_acy (h1 ⋅ h2) →
    ∀ n n' m, 
      n ∈ domm h1 → n' ∉ domm (h1 ⋅ h2) → 
        inf n = inf n + (m - inf n) →
          cap (h1 ⋅ h2) n n' m = 
            ([^+ list] _ ↦ k ∈ seq 1 (size (domm (h1 ⋅ h2))),
              ([^+ list] _ ↦ xs ∈ k_alternating h1 h2 k n,
                chain F xs n' m
              ) 
            ).
Proof.
  intros inf F; subst inf F; simpl.
Admitted.                

Lemma cap_comp_chain (h1 h1' h2: flow_graphT) :
  let inf n := inf_fg (h1 ⋅ h2) !!! n in
  ✓ (h1 ⋅ h2) → eff_acy (h1 ⋅ h2) →
    ✓ (h1' ⋅ h2) → domm h1' = domm h1 →
    ∀ n n' m, 
      n ∈ domm (h1 ⋅ h2) → n' ∉ domm (h1' ⋅ h2) → 
        inf n = inf n + (m - inf n) →
          cap (h1 ⋅ h2) n n' m = cap (h1' ⋅ h2) n n' m.
Proof.
  intros inf; subst inf; simpl.
Admitted.                


Lemma fg_update_valid (h1 h1' h2: flow_graphT) :
  ✓ (h1 ⋅ h2) → subflow_ext h1 h1' → 
    domm h1' ∩ domm h2 = ∅ →
        ✓ (h1' ⋅ h2).
Proof.
  intros V12 [V1 [V1' [HcontL [Hcap Hcap_out]]]] Domm.
  assert (✓ h2) as V2 by (apply fgComp_valid_proj2 in V12; done).
  apply fgValid_composable. unfold fgComposable.
  split; first done. split; first done.
  split; first by (clear -Domm; set_solver). split.
  - unfold fgComp_eqn_check. apply map_Forall_lookup.
    intros n m' Hnm. unfold fgComp_edgeflow. 
    assert (n ∈ domm h1') as n_in_h1'. { admit. }
    destruct HcontL as [VI1 [VI2 [DommI1 [Inf Outf]]]].
    case_eq h1; last by (intros ->; exfalso; try done).
    intros fg1. intros Def_h1.
    case_eq h1'; last by (intros ->; exfalso; try done).
    intros fg1'. intros Def_h1'.
    case_eq fg1; intros ef1 fl1 Def_fg1.
    case_eq fg1'; intros ef1' fl1' Def_fg1'.
    rewrite <-Def_fg1'. rewrite <-Def_h1'.
    destruct (decide (n ∈ domm h1)) as [n_in_h1 | n_nin_h1].
    + rewrite !domm_int_fg in Inf DommI1 Outf.
      pose proof Inf n n_in_h1 as Inf.
      assert (inf (flowint_of_fg h1) n = fl1 !!! n - edgeflow h1 n) as Hinf1.
      { admit. }
      assert (inf (flowint_of_fg h1') n = fl1' !!! n - edgeflow h1' n) as Hinf1'.
      { admit. }
      rewrite Hinf1 Hinf1' in Inf.
      assert (fl1' !!! n = m') as Hfl1'_n. 
      { unfold flow_map in Hnm. rewrite Def_h1' in Hnm.
        rewrite Def_fg1' in Hnm. simpl in Hnm.
        rewrite lookup_total_alt. rewrite Hnm.
        try done. }
      rewrite Hfl1'_n in Inf.
      apply fgComposable_valid in V12.
      destruct V12 as [_ [_ [_ [H' _]]]].
      unfold fgComp_eqn_check in H'.
      rewrite map_Forall_lookup in H'.
      assert (is_Some (flow_map h1 !! n)) as Hfl1_n. { admit. }
      destruct Hfl1_n as [m Hfl1_n].
      pose proof H' n m Hfl1_n as H'.
      unfold fgComp_edgeflow in H'.
      (* CCM manipulation from this point on *)
      (* Use H'; Inf *)
      admit.
    + assert (edgeflow h2 n = 0) as Hef2_n. { admit. }
      rewrite Hef2_n. rewrite ccm_right_id.
      (* Use validity of h1' *)
      admit.
  - unfold fgComp_eqn_check. apply map_Forall_lookup.
    intros n m Hnm. unfold fgComp_edgeflow.
    assert (edgeflow h1' n = edgeflow h1 n) as Hef1'_n.
    { admit. }
    (* Use validity of h1 ⋅ h2 *)       
    admit.
Admitted.

Lemma fg_update_subflow_ext (h1 h1' h2: flow_graphT) :
  ✓ (h1 ⋅ h2) → eff_acy (h1 ⋅ h2) → 
    subflow_ext h1 h1' → domm h1' = domm h1 →
      (∀ n, n ∈ domm h1'∖domm h1 → outf_fg h2 ! n = 0) →
        subflow_ext (h1 ⋅ h2) (h1' ⋅ h2).
Proof.
  intros V12 EA12 [V1 [V1' [HcontL [Hcap Hcap_out]]]] Domm_eq Out.
  assert (domm h1' ∩ domm h2 = ∅) as Domm.
  { rewrite Domm_eq. pose proof (fgComp_dom_disjoint h1 h2 V12) as H'.
    clear -H'; set_solver. }
  assert (✓ h2) as V2 by (apply fgComp_valid_proj2 in V12; done).
  assert (✓ (h1' ⋅ h2)) as V12'. 
  { apply (fg_update_valid h1 h1' h2); try done. }
  unfold subflow_ext.
  split; last split; try done.
  split; last split.
  - unfold contextualLeq. 
    case_eq (h1 ⋅ h2); last by (intros H'; rewrite H' in V12; exfalso; try done).
    intros fg12 Def_h12. rewrite <-Def_h12.
    case_eq (h1' ⋅ h2); last by (intros H'; rewrite H' in V12'; exfalso; try done).
    intros fg12' Def_h12'. rewrite <-Def_h12'.
    case_eq fg12; intros ef12 fl12 Def_fg12.
    case_eq fg12'; intros ef12' fl12' Def_fg12'.
    case_eq h1; last by (intros ->; exfalso; try done).
    intros fg1. intros Def_h1. rewrite <-Def_h1.
    case_eq h1'; last by (intros ->; exfalso; try done).
    intros fg1'. intros Def_h1'. rewrite <-Def_h1'.
    case_eq h2; last by (intros ->; exfalso; try done).
    intros fg2. intros Def_h2. rewrite <-Def_h2.
    case_eq fg1; intros ef1 fl1 Def_fg1.
    case_eq fg1'; intros ef1' fl1' Def_fg1'.        
    case_eq fg2; intros ef2 fl2 Def_fg2.
    rewrite !domm_int_fg.
    split; first by apply flowint_of_fg_valid.
    split; first by apply flowint_of_fg_valid.
    split; last split.
    + rewrite !fgComp_domm; try done.
      assert (domm h1 ⊆ domm h1') as H'.
      { admit. }
      clear -H'; set_solver.
    + intros n Domm_n.
      unfold flowint_of_fg.
      rewrite Def_h12 Def_h12'.
      unfold inf, inf_map.
      rewrite <-Def_h12. rewrite <-Def_h12'. simpl.
      assert (inf_fg (h1 ⋅ h2) !! n = Some (fl12 !!! n - edgeflow (h1 ⋅ h2) n)) as H'.
      { admit. }
      assert (inf_fg (h1' ⋅ h2) !! n = Some (fl12' !!! n - edgeflow (h1' ⋅ h2) n)) as H''.
      { admit. }
      rewrite H' H''. simpl. clear H' H''.
      assert (edgeflow (h1 ⋅ h2) n = edgeflow h1 n + edgeflow h2 n) as H'.
      { admit. }
      assert (edgeflow (h1' ⋅ h2) n = edgeflow h1' n + edgeflow h2 n) as H''.
      { admit. }
      rewrite H' H''. clear H' H''.
      rewrite fgComp_domm in Domm_n; last done.
      rewrite elem_of_union in Domm_n. destruct Domm_n as [Domm_n | Domm_n].
      * assert (fl12 !!! n = fl1 !!! n) as H'. { admit. }
        assert (fl12' !!! n = fl1' !!! n) as H''. { admit. }
        rewrite H' H''. clear H' H''.
        (* From inf (h1 ⋅ h2) n = inf (h1' ⋅ h2) n *)
        assert (fl1 !!! n - edgeflow h1 n = fl1' !!! n - edgeflow h1' n) as H'.
        { admit. }
        (* CCM manipulations from this point on *)
        admit.
      * assert (fl12 !!! n = fl2 !!! n) as H'. { admit. }
        assert (fl12' !!! n = fl2 !!! n) as H''. { admit. }
        rewrite H' H''. clear H' H''.
        (* ∀ n, n ∉ domm h1' → edgeflow h1 n = edgeflow h1' n *)
        assert (edgeflow h1 n = edgeflow h1' n) as H'.
        { admit. }
        by rewrite H'.
    + intros n Domm_n. unfold flowint_of_fg.
      rewrite Def_h12 Def_h12'. unfold out, out_map.
      rewrite <-Def_h12. rewrite <-Def_h12'. simpl.
      assert (outf_fg (h1 ⋅ h2) ! n = edgeflow h1 n + edgeflow h2 n) as H'.
      { admit. }
      assert (outf_fg (h1' ⋅ h2) ! n = edgeflow h1' n + edgeflow h2 n) as H''.
      { admit. }
      (* ∀ n, n ∉ domm h1' → edgeflow h1 n = edgeflow h1' n *)
      assert (edgeflow h1 n = edgeflow h1' n) as H'''.
      { admit. }
      by rewrite H' H'' H'''.
  - intros n n' m Domm_n Domm_n' Hm.
    pose proof (cap_comp_chain h1 h1' h2 V12 EA12 V12' Domm_eq n n' m Domm_n Domm_n') as Cap.
    simpl in Cap. by pose proof Cap Hm as Cap.
  - intros n n' m Domm_n.
    rewrite !fgComp_domm in Domm_n; try done. rewrite Domm_eq in Domm_n.
    exfalso; clear -Domm_n; set_solver.  
Admitted.

Lemma fg_update_eff_acy (h1 h1' h2: flow_graphT) :
  ✓ (h1 ⋅ h2) → eff_acy (h1 ⋅ h2) → 
    subflow_ext h1 h1' → domm h1' = domm h1 →
      (∀ n, n ∈ domm h1'∖domm h1 → outf_fg h2 ! n = 0) →
        eff_acy (h1' ⋅ h2).
Proof.
  intros V12 EA12 [V1 [V1' [HcontL [Hcap Hcap_out]]]] Domm_eq Out.
  destruct (decide (eff_acy (h1' ⋅ h2))) as [? | Heff]; try done.
  apply eff_acy_neg in Heff.
  

















        
