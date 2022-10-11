(** Theory of Flow Graphs *)

(* This formalization builds on the paper:
   
   Local Reasoning for Global Graph Properties: Siddharth Krishna and Alexander J. Summers and Thomas Wies, ESOP'20.
*)

From iris.algebra Require Export monoid auth updates local_updates.
From stdpp Require Export gmap.
From stdpp Require Import mapset finite.
Require Export ccm ccm_big_op gmap_more.
Require Import Coq.Setoids.Setoid.

(* The set of nodes over which graphs are built. *)
Definition Node := nat.

Section flow_graph.

(* The underlying flow domain. *)
Context `{CCM flow_dom} `{Countable flow_dom}.

Open Scope ccm_scope.

Definition efT : Type := nzmap (Node*Node) (nzmap flow_dom flow_dom).
Canonical Structure efRAC := leibnizO efT.


(* Representation of flow interfaces: 
   - The domain of the interface is the domain of its inflow infR. 
   - The outflow function is defined using nzmap so that interface composition is cancelable. 
*)
Record flow_graphR :=
  {
    edgeR : efT;
    flowR : gmap Node flow_dom;
  }.

Inductive flow_graphT :=
| fg: flow_graphR → flow_graphT
| fgUndef: flow_graphT. (* used when flow graph composition is undefined *)

(* The empty flow graph *)
Definition FG_emptyR := {| edgeR := ∅; flowR := ∅ |}.
Definition FG_empty := fg FG_emptyR.
Global Instance fg_empty : Empty flow_graphT := FG_empty.

Definition flow_map (h : flow_graphT) : gmap Node flow_dom :=
  match h with
    | fg hr => flowR hr
    | fgUndef => ∅
  end.

Definition edge_map (h : flow_graphT) : efT :=
  match h with
    | fg hr => edgeR hr
    | fgUndef => ∅
  end.

Global Instance flow_graph_dom : Dom flow_graphT (gset Node) :=
  λ h, dom (flow_map h).

Definition domm (h : flow_graphT) := dom h.

Global Instance flow_graph_elem_of : ElemOf Node flow_graphT :=
  λ n h, n ∈ domm h.

(* Some useful implicit type classes *)

Canonical Structure flow_graphRAC := leibnizO flow_graphT.

Global Instance fg_eq_dec: EqDecision flow_graphT.
Proof.
  unfold EqDecision.
  unfold Decision.
  repeat decide equality.
  - apply gmap_eq_eq.
  - apply nzmap_eq_eq.
Qed.

(** Interface validity *)

Definition flow_eq (h : flow_graphT) (i : gmap Node flow_dom) := 
  map_Forall
    (λ (n: Node) (m: flow_dom), 
      m = (default 0 (i !! n)) + 
          ([^+ set] n' ∈ domm h, (((edge_map h) ! (n, n')) ! (default 0 ((flow_map h) !! n'))))) 
    (flow_map h).

Global Instance fgValid : Valid flow_graphT :=
  λ h, match h with
       | fg hr =>
          (∃ i, flow_eq h i) ∧
          (∀ n n', (n, n') ∈ dom (edgeR hr) → n ∈ dom (flowR hr))  
       | fgUndef => False
       end.

Global Instance flow_eq_dec : ∀ h, Decision (∃ i, flow_eq h i).
Proof.
  intros.
Admitted.

Global Instance flow_graph_valid_dec : ∀ h : flow_graphT, Decision (✓ h).
Proof.
  intros.
  unfold valid; unfold fgValid.
  destruct _; last by solve_decision.
  apply and_dec.
  apply flow_eq_dec.
  (* Search Decision. *)
Admitted.

(*
Lemma flow_eq_unique h i1 i2 : ✓ h → flow_eq h i1 → flow_eq h i2 → i1 = i2.
*)

Definition fgComposable (h1 h2: flow_graphT) :=
  ✓ h1 ∧ ✓ h2 ∧
  domm h1 ## domm h2.

Global Instance fgComposable_dec (h1 h2: flow_graphT) : Decision (fgComposable h1 h2).
Proof.
  solve_decision.
Qed.

Definition edgeComp h1 h2 :=
  nzmap_imerge (λ _ m1 m2, m1 + m2) (edge_map h1) (edge_map h2).

Definition flowComp_op (h1 h2: flow_graphT) (o1 o2 : option flow_dom) :=
  match o1, o2 with
  | Some m1, _ => Some (m1)
  | _, Some m2 => Some (m2)
  | _, _ => None
  end.

(* make this gmap_merge *)
Definition flowComp h1 h2 :=
  gmap_imerge (λ _ m1 m2, flowComp_op h1 h2 m1 m2) (flow_map h1) (flow_map h2).

Global Instance fgComp : Op flow_graphT :=
  λ h1 h2, if decide (fgComposable h1 h2) then
             fg {| edgeR := edgeComp h1 h2 ; flowR := flowComp h1 h2 |}
           else if decide (h1 = ∅) then h2
           else if decide (h2 = ∅) then h1
           else fgUndef.

(** Auxiliary definitions for setting up flow interface camera. *)

Global Instance flow_graphRAcore : PCore flow_graphT :=
  λ h, match h with
       | fg hr => Some FG_empty
       | fgUndef => Some fgUndef
       end.

Global Instance flow_graphRAunit : cmra.Unit flow_graphT := FG_empty.

(* Composing with the undefined flow graph is undefined. *)
Lemma fgComp_undef_op : ∀ h, fgUndef ⋅ h ≡ fgUndef.
Proof.
  intros h. unfold op, fgComp.
  rewrite decide_False; last first.
  unfold fgComposable. unfold valid, fgValid at 1. 
  by intros [H' _].
  rewrite decide_False; last try done.
  destruct (decide (h = ∅)); try done.
Qed.

Lemma fgComp_undef_op2 : ∀ h, h ⋅ fgUndef ≡ fgUndef.
Proof.
  intros h. unfold op, fgComp.
  rewrite decide_False; last first.
  unfold fgComposable. unfold valid, fgValid at 1. 
  by intros [ _ [H' _]].
  destruct (decide (h = ∅)); try done.
  by rewrite decide_False; last try done.
Qed.

(* The fgComposable predicate is commutative. *)
Lemma fgComposable_comm_1 : ∀ (h1 h2 : flow_graphT), fgComposable h1 h2 → fgComposable h2 h1.
Proof.
  intros h1 h2 [Valid1 [Valid2 Domm]].
  repeat split; try done.
Qed.

Lemma fgComposable_comm : ∀ (h1 h2 : flow_graphT), fgComposable h1 h2 ↔ fgComposable h2 h1.
Proof.
  intros. split.
  all: refine (fgComposable_comm_1 _ _).
Qed.

(* The components of valid composite flow graphs are valid. *)
Lemma fgComp_valid_proj1 : ∀ (h1 h2: flow_graphT), ✓ (h1 ⋅ h2) → ✓ h1.
Proof.
  intros h1 h2 Valid. unfold valid, fgValid.
  destruct h1 as [ fg1 | ]; last first.
  - rewrite fgComp_undef_op in Valid.
    by unfold valid, fgValid in Valid.
  -   
Admitted.

Lemma fgComp_valid_proj2 : ∀ (h1 h2: flow_graphT), ✓ (h1 ⋅ h2) → ✓ h2.
Proof.
Admitted.

(* The components of valid composite flow graphs are composable. *)
Lemma fgComposable_valid : ∀ (h1 h2: flow_graphT), ✓ (h1 ⋅ h2) → fgComposable h1 h2.
Proof.
  intros h1 h2 Valid.
  split 
Admitted.


(* The composition of composable flow graphs is valid. *)
Lemma fgValid_composable : ∀ (h1 h2: flow_graphT), fgComposable h1 h2 → ✓ (h1 ⋅ h2).
Proof.
Admitted.

Lemma fgComp_dom_disjoint : ∀ h1 h2, ✓ (h1 ⋅ h2) → domm h1 ## domm h2.
Proof.
Admitted.

Lemma fgComp_dom : ∀ h1 h2, ✓ (h1 ⋅ h2) → domm (h1 ⋅ h2) = domm h1 ∪ domm h2.
Proof.
Admitted.


(* Flow graph composition is commutative. *)
Lemma fgComp_comm : ∀ (h1 h2: flow_graphT), h1 ⋅ h2 ≡ h2 ⋅ h1.
Proof.
  intros h1 h2.
  destruct h1 as [ fg1 | ]; last first.
  - by rewrite fgComp_undef_op fgComp_undef_op2.
  - destruct h2 as [ fg2 | ]; last first.
    + by rewrite fgComp_undef_op fgComp_undef_op2.
    + unfold op, fgComp. destruct (decide (fgComposable (fg fg1) (fg fg2))).
      * rewrite decide_True; last first.
        { by apply fgComposable_comm. }
        apply f_equal.
        assert (edgeComp (fg fg1) (fg fg2) = edgeComp (fg fg2) (fg fg1)) as H'.
        { unfold edgeComp. apply nzmap_eq.
          intros (n, n'). repeat rewrite nzmap_lookup_imerge.
          apply ccm_comm. }
        assert (flowComp (fg fg1) (fg fg2) = flowComp (fg fg2) (fg fg1)) as H''.
        { unfold flowComp. apply map_eq. intros n.
          repeat rewrite gmap_imerge_prf; try done.
          apply fgValid_composable in f.
          apply fgComp_dom_disjoint in f.
          destruct (decide (n ∈ domm (fg fg1))).
          - unfold domm, dom, flow_graph_dom in e.
            assert (n ∉ domm (fg fg2)) as n_notin_h2. set_solver.
            rewrite elem_of_dom in e. destruct e as [m e].
            unfold domm, dom, flow_graph_dom in n_notin_h2.
            rewrite not_elem_of_dom in n_notin_h2.
            unfold flowComp_op.
            by rewrite e n_notin_h2.
          - unfold domm, dom, flow_graph_dom in n0.  
            rewrite not_elem_of_dom in n0.
            destruct (decide (n ∈ domm (fg fg2))).
            + unfold domm, dom, flow_graph_dom in e.
              rewrite elem_of_dom in e. destruct e as [m e].
              unfold flowComp_op. rewrite n0.
              by rewrite e.
            + unfold domm, dom, flow_graph_dom in n1.  
              rewrite not_elem_of_dom in n1.  
              unfold flowComp_op. by rewrite n0 n1. }
        by rewrite H' H''.
      * destruct (decide (fg fg1 = ∅)).
        ** rewrite decide_False; first last.
           { by rewrite fgComposable_comm. }
           destruct (decide (fg fg2 = ∅)); try done.
           by rewrite e e0.
        ** destruct (decide (fg fg2 = ∅)); try done.
           *** rewrite decide_False; first last.
               { by rewrite fgComposable_comm. }
               done.
           *** rewrite decide_False; first last.
               { by rewrite fgComposable_comm. }
               done.
Qed.



(* Flow graph composition is associative (valid case). *)
Lemma fgComp_assoc_valid (h1 h2 h3 : flow_graphT) : ✓ (h1 ⋅ (h2 ⋅ h3)) → h1 ⋅ (h2 ⋅ h3) ≡ h1 ⋅ h2 ⋅ h3.
Proof.
  intros Valid.
  destruct h1 as [ fg1 | ]; last first.
  - rewrite (fgComp_undef_op (h2 ⋅ h3)).
    rewrite (fgComp_undef_op h2).
    by rewrite (fgComp_undef_op h3).
  - destruct h2 as [ fg2 | ]; last first.
    + rewrite (fgComp_undef_op h3).
      rewrite fgComp_comm.
      by repeat rewrite fgComp_undef_op.
    + destruct h3 as [ fg3 | ]; last first.
      * rewrite (fgComp_comm (fg fg2) fgUndef). rewrite fgComp_undef_op.
        rewrite fgComp_comm. rewrite fgComp_undef_op.
        rewrite (fgComp_comm (fg fg1 ⋅ fg fg2)).
        by rewrite (fgComp_undef_op (fg fg1 ⋅ fg fg2)).
      * assert (✓ (fg fg1)) as Valid1.
        { apply (fgComp_valid_proj1 _ _ Valid). }
        assert (✓ (fg fg2 ⋅ fg fg3)) as Valid23.
        { apply (fgComp_valid_proj2 _ _ Valid). }
        assert (✓ (fg fg2)) as Valid2.
        { by apply fgComp_valid_proj1 in Valid23. }
        assert (✓ (fg fg3)) as Valid3.
        { by apply fgComp_valid_proj2 in Valid23. }
        assert (domm (fg fg2 ⋅ fg fg3) = domm (fg fg2) ∪ domm (fg fg3)) as Domm23.
        { by apply fgComp_dom. }
        assert (✓ (fg fg1 ⋅ fg fg2)) as Valid12.
        { apply fgValid_composable. unfold fgComposable.
          split; try done. split; try done.
          apply fgComp_dom_disjoint in Valid.
          clear -Valid Domm23. set_solver. }
        assert (✓ ((fg fg1 ⋅ fg fg2) ⋅ fg fg3)) as Valid123.
        { apply fgValid_composable. unfold fgComposable.
          split; try done. split; try done.
          rewrite fgComp_dom; try done.
          apply fgComp_dom_disjoint in Valid.
          apply fgComp_dom_disjoint in Valid23.
          clear -Valid Domm23 Valid23. set_solver. }
        unfold op, fgComp.
        repeat (rewrite decide_True; last by apply fgComposable_valid).
        apply f_equal. 
        
        assert (edgeComp 
                  (fg fg1) 
                  (fg {| edgeR := edgeComp (fg fg2) (fg fg3); 
                         flowR := flowComp (fg fg2) (fg fg3) |})
              = edgeComp 
                  (fg {| edgeR := edgeComp (fg fg1) (fg fg2); 
                         flowR := flowComp (fg fg1) (fg fg2) |}) 
                  (fg fg3)) as H'.
        { apply nzmap_eq. intros (n, n'). unfold edgeComp.
          repeat rewrite nzmap_lookup_imerge. apply ccm_assoc. }
        assert (flowComp 
                  (fg fg1) 
                  (fg {| edgeR := edgeComp (fg fg2) (fg fg3); 
                         flowR := flowComp (fg fg2) (fg fg3) |})  
              = flowComp 
                  (fg {| edgeR := edgeComp (fg fg1) (fg fg2); 
                         flowR := flowComp (fg fg1) (fg fg2) |}) 
                  (fg fg3)) as H''.
        { apply map_eq. intros n. unfold flowComp.
          repeat (rewrite gmap_imerge_prf; try done).
          unfold flowComp_op.
          destruct (flow_map (fg fg1) !! n); try done.
          destruct (flow_map (fg fg2) !! n); try done.
          destruct (flow_map (fg fg3) !! n); try done. }
        by rewrite H' H''.                
Qed.




Definition flow_graphRA_mixin : RAMixin flow_graphT.
Proof.
  split; try apply _; try done.
  - (* Core is unique? *)
    intros ? ? cx -> ?. exists cx. done.
  - (* Associativity *)
    unfold Assoc.
    eauto using intComp_assoc.
  - (* Commutativity *)
    unfold Comm. eauto using intComp_comm.
  - (* Core-ID *)
    intros x cx.
    destruct cx eqn:?; unfold pcore, flowintRAcore; destruct x eqn:?;
      try (intros H1; inversion H1).
    + rewrite intComp_comm.
      apply intComp_unit.
    + apply intComp_undef_op.
  - (* Core-Idem *)
    intros x cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x;
      try (intros H0; inversion H0); try done.
  - (* Core-Mono *)
    intros x y cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x; intros H0;
      intros H1; inversion H1; destruct y; try eauto.
    + exists I_empty. split; try done.
      exists (int I_emptyR). by rewrite intComp_unit.
    + exists intUndef. split; try done. exists intUndef.
      rewrite intComp_comm. by rewrite intComp_unit.
    + exists I_empty. split; try done.
      destruct H0 as [a H0].
      assert (intUndef ≡ intUndef ⋅ a); first by rewrite intComp_undef_op.
      rewrite <- H0 in H2.
      inversion H2.
  - (* Valid-Op *)
    intros x y. unfold valid. apply intComp_valid_proj1.
Qed. 




