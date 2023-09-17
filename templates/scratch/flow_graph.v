(** Theory of Flow Graphs *)

(* This formalization builds on the paper:
   
   Local Reasoning for Global Graph Properties: Siddharth Krishna and 
    Alexander J. Summers and Thomas Wies, ESOP'20.
*)

From iris.algebra Require Export monoid auth updates local_updates.
From stdpp Require Export gmap.
From stdpp Require Import mapset finite.
Require Export ccm ccm_big_op gmap_more flows auxiliary.
Require Import Coq.Setoids.Setoid.

(* The set of nodes over which graphs are built. *)
(* Definition Node := nat. *)

Section flow_graph.

(* The underlying flow domain. *)
Context `{CCM flow_dom} `{Countable flow_dom}.

Open Scope ccm_scope.

Definition efT : Type := nzmap Node (nzmap Node (nzmap flow_dom flow_dom)).
Canonical Structure efRAC := leibnizO efT.

Definition edgeFn (e : efT) (n n' : Node) := e ! n ! n'.

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
  decide equality. decide equality.
  apply gmap_eq_eq. apply nzmap_eq_eq.
Qed.

(** Interface validity *)

Definition fg_flow (h : flow_graphT) n := default 0 ((flow_map h) !! n).

Definition fg_edge (h : flow_graphT) n n' := edgeFn (edge_map h) n n'.

Definition edgeflow (h1: flow_graphT) n := 
  ([^+ set] n' ∈ domm h1, (fg_edge h1 n' n) ! (fg_flow h1 n')).

Definition fg_eqn_sat (h: flow_graphT) :=
  map_Forall (λ (n: Node) (m: flow_dom), m = edgeflow h n + (m - edgeflow h n)) (flow_map h).

(*
Definition flow_eqn (h : flow_graphT) (i : gmap Node flow_dom) :=
  let inf n := default 0 (i !! n) in
  let flow_to n := ([^+ set] n' ∈ domm h, (fg_edge h n n') ! (fg_flow h n')) in
  map_Forall (λ (n: Node) (m: flow_dom), m = inf n + flow_to n) (flow_map h).

Global Instance fgValid : Valid flow_graphT :=
  λ h, match h with
       | fg hr =>
          (∃ i, flow_eqn h i) ∧
          dom (edgeR hr) ⊆ dom (flowR hr)  
       | fgUndef => False
       end.
*)

Global Instance fgValid : Valid flow_graphT :=
  λ h, match h with
       | fg hr =>
          fg_eqn_sat h ∧
          dom (edgeR hr) ⊆ dom (flowR hr)  
       | fgUndef => False
       end.

(*
Global Instance flow_eqn_dec : ∀ h, Decision (∃ i, flow_eqn h i).
Proof.
  intros. 
Admitted.
*)

Global Instance flow_graph_valid_dec : ∀ h : flow_graphT, Decision (✓ h).
Proof.
  intros.
  unfold valid; unfold fgValid.
  destruct _; by solve_decision.
Qed.

(*
Lemma flow_eq_unique h i1 i2 : ✓ h → flow_eq h i1 → flow_eq h i2 → i1 = i2.
*)



Definition fgComp_edgeflow (h1 h2: flow_graphT) n := edgeflow h1 n + edgeflow h2 n.

(* Not symmetric : checks if flow in h1 is valid for composition h1 ⋅ h2 *)
Definition fgComp_eqn_check (h1 h2: flow_graphT) :=
    map_Forall 
    (λ (n: Node) (m: flow_dom), m = fgComp_edgeflow h1 h2 n + (m - fgComp_edgeflow h1 h2 n))
    (flow_map h1).

Definition fgComposable (h1 h2: flow_graphT) :=
  ✓ h1 ∧ ✓ h2 ∧
  domm h1 ## domm h2 ∧
  fgComp_eqn_check h1 h2 ∧
  fgComp_eqn_check h2 h1.

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


(* The empty flow graph is the right identity of flow graph composition. *)
Lemma fgComp_unit : ∀ (h: flow_graphT), h ⋅ FG_empty ≡ h.
Proof.
  intros h. unfold op, fgComp.
  destruct (decide (fgComposable h FG_empty)) as [Hcomp | _].
  - destruct h as [[he hf] | ].
    + f_equal.
      assert (edgeComp (fg {| edgeR := he; flowR := hf |}) FG_empty = he) as H'.
      { unfold edgeComp. apply nzmap_eq. intros n.
        rewrite nzmap_lookup_imerge.
        unfold edge_map. simpl. rewrite nzmap_lookup_empty.
        by rewrite ccm_right_id. }
      assert (flowComp (fg {| edgeR := he; flowR := hf |}) FG_empty = hf) as H''.
      { unfold flowComp. apply map_eq. intros n. rewrite gmap_imerge_prf; try done.
        unfold flowComp_op, flow_map. simpl.
        destruct (hf !! n); try done. }
      by rewrite H' H''.
    + destruct Hcomp as [? _]; try done.
  - destruct (decide (h = ∅)); try done.
    rewrite decide_True; try done.
Qed.           

(* The fgComposable predicate is commutative. *)
Lemma fgComposable_comm_1 : ∀ (h1 h2 : flow_graphT), fgComposable h1 h2 → fgComposable h2 h1.
Proof.
  intros h1 h2 [Valid1 [Valid2 [Domm [Flow_h1 Flow_h2]]]].
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
  intros h1 h2 Valid. unfold op, fgComp in Valid.
  destruct (decide (fgComposable h1 h2)) as [Hcomp | _]; last first.
  - destruct (decide (h1 = ∅)) as [-> | _]; try done.
    destruct (decide (h2 = ∅)); try done.
  - by destruct Hcomp as [Hcomp _].
Qed.

Lemma fgComp_valid_proj2 : ∀ (h1 h2: flow_graphT), ✓ (h1 ⋅ h2) → ✓ h2.
Proof.
  intros h1 h2 Valid. unfold op, fgComp in Valid.
  destruct (decide (fgComposable h1 h2)) as [Hcomp | _]; last first.
  - destruct (decide (h1 = ∅)); try done.
    destruct (decide (h2 = ∅)) as [-> | ]; try done.
  - by destruct Hcomp as [_ [Hcomp _]].  
Qed.

Lemma fgEmpty_dom : domm (∅: flow_graphT) = ∅.
Proof.
  unfold domm, dom, flow_graph_dom, flow_map, 
    empty at 1, fg_empty, FG_empty, FG_emptyR.
  simpl. set_solver.
Qed. 

Lemma fgComp_dom_disjoint : ∀ h1 h2, ✓ (h1 ⋅ h2) → domm h1 ## domm h2.
Proof.
  intros h1 h2 Valid.
  unfold op, fgComp in Valid.
  destruct (decide (fgComposable h1 h2)) as [HComp | _].
  - by destruct HComp as [_ [_ [H' _]]].
  - destruct (decide (h1 = ∅)) as [-> | _].
    + by rewrite fgEmpty_dom.
    + destruct (decide (h2 = ∅)) as [-> | _].
      * by rewrite fgEmpty_dom.
      * by unfold valid, fgValid in Valid.  
Qed.

Lemma fgComp_domm : ∀ h1 h2, ✓ (h1 ⋅ h2) → domm (h1 ⋅ h2) = domm h1 ∪ domm h2.
Proof.
  intros h1 h2 Valid. unfold op, fgComp.
  unfold op, fgComp in Valid.
  destruct (decide (fgComposable h1 h2)) as [HComp | _].
  - unfold domm at 1, dom, flow_graph_dom, flow_map. simpl.
    assert (dom (flowComp h1 h2) ⊆ domm h1 ∪ domm h2) as H'.
    { intros x. unfold flowComp. rewrite elem_of_dom.
      unfold is_Some. intros [x0 Hmerge].
      rewrite gmap_imerge_prf in Hmerge; try done.
      unfold flowComp_op in Hmerge.
      destruct (flow_map h1 !! x) as [x1 | ] eqn: H''.
      - inversion Hmerge. subst x1.
        rewrite elem_of_union; left.
        unfold domm, dom, flow_graph_dom. rewrite elem_of_dom.
        by exists x0. 
      - clear H''; destruct (flow_map h2 !! x) as [x1 | ] eqn: H''. 
        inversion Hmerge. subst x1.
        rewrite elem_of_union; right.
        unfold domm, dom, flow_graph_dom. rewrite elem_of_dom.
        by exists x0.
        inversion Hmerge. }
    assert (domm h1 ∪ domm h2 ⊆ dom (flowComp h1 h2)) as H''.
    { intros x. rewrite elem_of_union.
      intros [Hdom | Hdom].
      - unfold flowComp. rewrite elem_of_dom.
        rewrite gmap_imerge_prf; try done.
        unfold flowComp, flowComp_op.
        unfold domm, dom, flow_graph_dom in Hdom.
        rewrite elem_of_dom in Hdom.
        destruct Hdom as [x0 Hdom].
        rewrite Hdom. try done.
      - unfold flowComp. rewrite elem_of_dom.
        rewrite gmap_imerge_prf; try done.
        unfold flowComp, flowComp_op.
        unfold domm, dom, flow_graph_dom in Hdom.
        rewrite elem_of_dom in Hdom.
        destruct Hdom as [x0 Hdom].
        rewrite Hdom. destruct (flow_map h1 !! x); try done. }
      set_solver.
  - destruct (decide (h1 = ∅)) as [H' | _].
    + subst h1. rewrite fgEmpty_dom.
      set_solver.
    + destruct (decide (h2 = ∅)) as [H' | _].
      * subst h2. rewrite fgEmpty_dom.
        set_solver.
      * try done.   
Qed.

Lemma fgComp_edgeflow_empty : ∀ (h: flow_graphT) (n: Node), 
  n ∈ domm h → ✓ h → fgComp_edgeflow h ∅ n = edgeflow h n.
Proof.
  intros h n Domm Valid. unfold fgComp_edgeflow, edgeflow at 2. rewrite fgEmpty_dom.
  rewrite ccm_big_opS_empty. by rewrite ccm_right_id.
Qed.  

Lemma fgComposable_empty : ∀ (h: flow_graphT), ✓ h → fgComposable h ∅.
Proof.
  intros h Valid. unfold fgComposable. repeat split; try done.
  unfold fgComp_eqn_check.
  apply map_Forall_lookup. intros n m Hnm.
  assert (n ∈ domm h) as H'.
  { unfold domm, dom, flow_graph_dom. by rewrite elem_of_dom. }
  pose proof (fgComp_edgeflow_empty h n H' Valid) as H''.
  rewrite H''. unfold valid, fgValid in Valid.
  case_eq h; last by (intros ->; try done).
  intros hr Hr. rewrite Hr in Valid.
  destruct Valid as [Valid _]. unfold fg_eqn_sat in Valid.  
  rewrite Hr in Hnm. 
  pose proof map_Forall_lookup_1 _ _ _ _ Valid Hnm as H'''.
  by simpl in H'''.
Qed.

(* The components of valid composite flow graphs are composable. *)
Lemma fgComposable_valid : ∀ (h1 h2: flow_graphT), ✓ (h1 ⋅ h2) → fgComposable h1 h2.
Proof.
  intros h1 h2 Valid.
  unfold op, fgComp in Valid.
  destruct (decide (fgComposable h1 h2)) as [Hcomp | Hcomp]; try done.
  destruct (decide (h1 = ∅)) as [-> | H1_empty]; try done.
  apply fgComposable_comm; apply fgComposable_empty. done.
  destruct (decide (h2 = ∅)) as [-> | H2_empty]; try done.
  by apply fgComposable_empty.
Qed.


Lemma flowComp_domm : ∀ (h1 h2: flow_graphT), dom (flowComp h1 h2) = domm h1 ∪ domm h2.
Proof.
  intros h1 h2. unfold domm, dom at 2 3, flow_graph_dom.
  assert (dom (flowComp h1 h2) ⊆ dom (flow_map h1) ∪ dom (flow_map h2)) as H'.
  { intros x Hx. rewrite elem_of_dom in Hx.
    destruct Hx as [mx Hx]. unfold flowComp in Hx.
    rewrite gmap_imerge_prf in Hx; try done.
    unfold flowComp_op in Hx.
    destruct (flow_map h1 !! x) as [mx1 | ] eqn: H1x.
    - inversion Hx. subst mx1. clear Hx.
      rewrite elem_of_union. left.
      rewrite elem_of_dom. by exists mx.
    - destruct (flow_map h2 !! x) as [mx2 | ] eqn: H2x.
      + inversion Hx. subst mx2. clear Hx.    
        rewrite elem_of_union. right.
        rewrite elem_of_dom. by exists mx.
      + inversion Hx. }
  assert (dom (flow_map h1) ∪ dom (flow_map h2) ⊆ dom (flowComp h1 h2)) as H''.
  { intros x. rewrite elem_of_union. intros [Hx | Hx].
    - unfold flowComp. rewrite elem_of_dom. rewrite gmap_imerge_prf; try done.
      unfold flowComp_op. rewrite elem_of_dom in Hx.
      destruct Hx as [mx Hx]. rewrite Hx. try done.
    - unfold flowComp. rewrite elem_of_dom. rewrite gmap_imerge_prf; try done.
      unfold flowComp_op. rewrite elem_of_dom in Hx.
      destruct Hx as [mx Hx]. destruct (flow_map h1 !! x); try done.
      by rewrite Hx. }
  clear -H' H''. set_solver.
Qed.    

Lemma edgeflow_empty : ∀ n, edgeflow ∅ n = 0.
Proof.
  intros n. unfold edgeflow. rewrite fgEmpty_dom. by rewrite ccm_big_opS_empty.
Qed.

Lemma edgeflow_Comp : ∀ n (h1 h2: flow_graphT), 
  fgComposable h1 h2 → edgeflow (h1 ⋅ h2) n = edgeflow h1 n + edgeflow h2 n.
Proof.
  intros n h1 h2 HComp. unfold op, fgComp.
  rewrite decide_True; try done.
  unfold edgeflow at 1, fg_edge, edge_map. unfold domm, dom, flow_graph_dom, flow_map. simpl.
  rewrite flowComp_domm. 
  destruct HComp as [V1 [V2 [Disj [Check1 Check2]]]].
  rewrite ccm_big_opS_union; try done. unfold fg_flow, flow_map. simpl.
  assert (edgeflow h1 n = ([^+ set] y ∈ domm h1, ((edgeComp h1 h2 ! y) ! n)
                   ! default 0 (flowComp h1 h2 !! y))) as Hef1.
  { unfold edgeflow. unfold fg_edge.
    assert (∀ y, y ∈ domm h1 → edgeComp h1 h2 ! y = edge_map h1 ! y) as H'.
    { intros y Hy. unfold edgeComp. rewrite nzmap_lookup_imerge.
      assert (edge_map h2 ! y = 0) as H''.
      { assert (y ∉ domm h2) as H' by set_solver.
        unfold valid, fgValid in V2. destruct h2; try done.
        unfold edge_map. destruct V2 as [_ V2].
        unfold domm, dom, flow_graph_dom, flow_map in H'.
        assert (y ∉ dom (edgeR f)) as H'' by set_solver.
        rewrite nzmap_elem_of_dom_total in H''. by apply dec_stable in H''. } 
    rewrite H''. by rewrite ccm_right_id. }
    assert (∀ y, y ∈ domm h1 → 
      ((edgeComp h1 h2 ! y) ! n) ! default 0 (flowComp h1 h2 !! y) =
      ((edge_map h1 ! y) ! n) ! default 0 (flowComp h1 h2 !! y)) as H''.
    { intros y Hy. by rewrite (H' y Hy). }  
    rewrite (ccm_big_opS_ext _ _ (domm h1) H'').
    clear H' H''.
    assert (∀ y, y ∈ domm h1 → fg_flow h1 y = default 0 (flowComp h1 h2 !! y)) as Hflow1.
    { intros y Hy. unfold flowComp. rewrite gmap_imerge_prf; try done.
      unfold flowComp_op. unfold domm, dom, flow_graph_dom in Hy.
      rewrite elem_of_dom in Hy. destruct Hy as [my Hy].
      unfold fg_flow. by rewrite Hy. }
      assert (∀ y, y ∈ domm h1 → 
                ((edge_map h1 ! y) ! n) ! fg_flow h1 y = 
                ((edge_map h1 ! y) ! n) ! default 0 (flowComp h1 h2 !! y)) as H''.
      { intros y Hy. by rewrite (Hflow1 y Hy). }
      by rewrite (ccm_big_opS_ext _ _ (domm h1) H''). }
   assert (edgeflow h2 n = ([^+ set] y ∈ domm h2, ((edgeComp h1 h2 ! y) ! n)
                   ! default 0 (flowComp h1 h2 !! y))) as Hef2.
  { unfold edgeflow. unfold fg_edge.
    assert (∀ y, y ∈ domm h2 → edgeComp h1 h2 ! y = edge_map h2 ! y) as H'.
    { intros y Hy. unfold edgeComp. rewrite nzmap_lookup_imerge.
      assert (edge_map h1 ! y = 0) as H''.
      { assert (y ∉ domm h1) as H' by set_solver.
        unfold valid, fgValid in V1. destruct h1; try done.
        unfold edge_map. destruct V1 as [_ V1].
        unfold domm, dom, flow_graph_dom, flow_map in H'.
        assert (y ∉ dom (edgeR f)) as H'' by set_solver.
        rewrite nzmap_elem_of_dom_total in H''. by apply dec_stable in H''. } 
    rewrite H''. by rewrite ccm_left_id. }
    assert (∀ y, y ∈ domm h2 → 
      ((edgeComp h1 h2 ! y) ! n) ! default 0 (flowComp h1 h2 !! y) =
      ((edge_map h2 ! y) ! n) ! default 0 (flowComp h1 h2 !! y)) as H''.
    { intros y Hy. by rewrite (H' y Hy). }  
      rewrite (ccm_big_opS_ext _ _ (domm h2) H'').
      clear H' H''.
    assert (∀ y, y ∈ domm h2 → fg_flow h2 y = default 0 (flowComp h1 h2 !! y)) as H'.
    { intros y Hy. unfold flowComp. rewrite gmap_imerge_prf; try done.
      unfold flowComp_op. unfold domm, dom, flow_graph_dom in Hy.
      rewrite elem_of_dom in Hy. destruct Hy as [my Hy].
      unfold fg_flow. destruct (flow_map h1 !! y) eqn: H'.
      - assert (y ∈ domm h1 ∩ domm h2) as H''.
        { rewrite elem_of_intersection. split; apply elem_of_dom; try done. }
        clear -Disj H''; set_solver.
      - by rewrite Hy. }
    assert (∀ y, y ∈ domm h2 → 
              ((edge_map h2 ! y) ! n) ! fg_flow h2 y = 
              ((edge_map h2 ! y) ! n) ! default 0 (flowComp h1 h2 !! y)) as H''.
    { intros y Hy. by rewrite (H' y Hy). }
    by rewrite (ccm_big_opS_ext _ _ (domm h2) H''). }
    by rewrite Hef1 Hef2.        
Qed.


(* The composition of composable flow graphs is valid. *)
Lemma fgValid_composable : ∀ (h1 h2: flow_graphT), fgComposable h1 h2 → ✓ (h1 ⋅ h2).
Proof.
  intros h1 h2 HComp.
  unfold valid, fgValid. unfold op, fgComp.
  rewrite decide_True; try done; simpl.
  split; last first.
  - intros n. rewrite elem_of_dom. intros Hnm.
    assert (Hnm' := Hnm). rewrite nzmap_elem_of_dom_total in Hnm'. 
    rewrite nzmap_elem_of_dom in Hnm.
    destruct Hnm as [m Hnm]. assert (edgeComp h1 h2 ! n = m) as H'.
    { unfold nzmap_total_lookup. by rewrite Hnm. }
    rewrite H' in Hnm'.
    rewrite nzmap_lookup_imerge in H'.
    destruct (decide (n ∈ dom (edge_map h1))) as [Hn1 | Hn1].
    + destruct HComp as [V1 HComp]. 
      unfold valid, fgValid in V1.
      destruct h1 as [hr1 | ]; try done. rewrite gmap_imerge_prf; try done.
      unfold flowComp_op, flow_map. destruct V1 as [_ V1].
      apply V1 in Hn1. rewrite elem_of_dom in Hn1. destruct Hn1 as [m' Hn1].
      by rewrite Hn1.
    + destruct (decide (n ∈ dom (edge_map h2))) as [Hn2 | Hn2].
      * destruct HComp as [_ [V2 HComp]]. 
        unfold valid, fgValid in V2.
        destruct h2 as [hr2 | ]; try done. rewrite gmap_imerge_prf; try done.
        unfold flowComp_op, flow_map. destruct V2 as [_ V2].
        apply V2 in Hn2. rewrite elem_of_dom in Hn2. destruct Hn2 as [m' Hn2].
        rewrite Hn2. destruct h1 as [fg1 | ]; try done. destruct (flowR fg1 !! n); try done.
      * rewrite nzmap_elem_of_dom_total in Hn1. apply dec_stable in Hn1.
        rewrite nzmap_elem_of_dom_total in Hn2. apply dec_stable in Hn2.
        unfold edgeComp in Hnm. rewrite Hn1 Hn2 in H'. rewrite ccm_left_id in H'.
        done.
  - unfold fg_eqn_sat. apply map_Forall_lookup. unfold flow_map. simpl.
    intros n m Hnm. unfold flowComp in Hnm.
    rewrite gmap_imerge_prf in Hnm; try done.
    pose proof (edgeflow_Comp n h1 h2 HComp) as Hef.
    unfold op, fgComp in Hef. rewrite decide_True in Hef; try done.
    rewrite Hef. unfold flowComp_op in Hnm. 
    destruct HComp as [V1 [V2 [Disj [Check1 Check2]]]].
    destruct (flow_map h1 !! n) as [m1 | ] eqn: H1n. 
    + inversion Hnm. subst m1. clear Hnm.
      unfold fgComp_eqn_check in Check1.
      rewrite map_Forall_lookup in Check1.
      pose proof Check1 n m H1n as Check1.
      by unfold fgComp_edgeflow in Check1.
    + destruct (flow_map h2 !! n) as [m2 | ] eqn: H2n.
      * inversion Hnm; subst m2; clear Hnm.
        unfold fgComp_eqn_check in Check2.
        rewrite map_Forall_lookup in Check2.
        pose proof Check2 n m H2n as Check2.
        unfold fgComp_edgeflow in Check2.
        by rewrite (ccm_comm (edgeflow h1 n) (edgeflow h2 n)).
      * inversion Hnm.    
Qed.

(* Flow graph composition is commutative. *)
Lemma fgComp_comm : ∀ (h1 h2: flow_graphT), h1 ⋅ h2 ≡ h2 ⋅ h1.
Proof.
  intros h1 h2.
  destruct h1 as [ fg1 | ]; last first.
  - by rewrite fgComp_undef_op fgComp_undef_op2.
  - destruct h2 as [ fg2 | ]; last first.
    + by rewrite fgComp_undef_op fgComp_undef_op2.
    + unfold op, fgComp. destruct (decide (fgComposable (fg fg1) (fg fg2))).
      * rewrite decide_True; last by apply fgComposable_comm.
        apply f_equal.
        assert (edgeComp (fg fg1) (fg fg2) = edgeComp (fg fg2) (fg fg1)) as H'.
        { unfold edgeComp. apply nzmap_eq.
          intros n. repeat rewrite nzmap_lookup_imerge.
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

Lemma fgComp_eqn_proj : ∀ h1 h2 h3, ✓ (h1 ⋅ h2) → fgComp_eqn_check (h1 ⋅ h2) h3 → fgComp_eqn_check h1 h3.
Proof.
  intros h1 h2 h3 Valid Heqn.
  unfold fgComp_eqn_check. apply map_Forall_lookup.
  intros n m Hnm. unfold fgComp_edgeflow.
  unfold fgComp_eqn_check in Heqn. rewrite map_Forall_lookup in Heqn.
  assert (flow_map (h1 ⋅ h2) !! n = flow_map h1 !! n) as H'.
  { unfold op, fgComp. rewrite decide_True; last by apply fgComposable_valid.
    unfold flow_map. simpl. unfold flowComp. rewrite gmap_imerge_prf; try done.
    unfold flowComp_op. by rewrite Hnm. }
  pose proof Heqn n m as Heqn. rewrite H' in Heqn.
  pose proof Heqn Hnm as Heqn. unfold fgComp_edgeflow in Heqn.
  rewrite edgeflow_Comp in Heqn; last by apply fgComposable_valid.
  rewrite <-(ccm_assoc (edgeflow h1 n) (edgeflow h2 n) (edgeflow h3 n)) in Heqn.
  rewrite (ccm_comm (edgeflow h2 n) (edgeflow h3 n)) in Heqn.
  rewrite ccm_assoc in Heqn. 
  by apply ccm_misc5 in Heqn.
Qed.


Lemma fgComp_flow : ∀ h1 h2 n, n ∈ domm h1 → ✓ (h1 ⋅ h2) → flow_map (h1 ⋅ h2) !! n = flow_map h1 !! n.
Proof.
  intros h1 h2 n Hdomm Valid. unfold op, fgComp. 
  rewrite decide_True; last by apply fgComposable_valid.
  unfold flow_map. simpl. unfold flowComp. 
  rewrite gmap_imerge_prf; try done.
  unfold flowComp_op. unfold domm, dom, flow_graph_dom in Hdomm.
  rewrite elem_of_dom in Hdomm. destruct Hdomm as [m Hdomm].
  by rewrite Hdomm.
Qed.   

(* Flow graph composition is associative (valid case). *)
Lemma fgComp_assoc_valid (h1 h2 h3 : flow_graphT) : 
  ✓ (h1 ⋅ (h2 ⋅ h3)) → h1 ⋅ (h2 ⋅ h3) ≡ h1 ⋅ h2 ⋅ h3.
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
        { by apply fgComp_domm. }
        assert (✓ (fg fg1 ⋅ fg fg2)) as Valid12.
        { apply fgValid_composable. unfold fgComposable.
          split; try done. split; try done. split.
          apply fgComp_dom_disjoint in Valid.
          clear -Valid Domm23. set_solver. split.
          - apply fgComposable_valid in Valid.
            unfold fgComposable in Valid. 
            destruct Valid as [_ [_ [Disj1_23 [Check1_23 Check23_1]]]].
            unfold fgComp_eqn_check. apply map_Forall_lookup.
            intros n m Hnm. unfold fgComp_edgeflow.
            unfold fgComp_eqn_check in Check1_23.
            rewrite map_Forall_lookup in Check1_23.
            pose proof Check1_23 n m Hnm as Check1_23.
            unfold fgComp_edgeflow in Check1_23.
            rewrite edgeflow_Comp in Check1_23; last by apply fgComposable_valid.
            rewrite ccm_assoc in Check1_23.
            by apply ccm_misc5 in Check1_23.
          - apply fgComposable_valid in Valid.
            unfold fgComposable in Valid. 
            destruct Valid as [_ [_ [Disj1_23 [Check1_23 Check23_1]]]].
            apply (fgComp_eqn_proj (fg fg2) (fg fg3) (fg fg1)); try done. }
        assert (✓ ((fg fg1 ⋅ fg fg2) ⋅ fg fg3)) as Valid123.
        { apply fgValid_composable. unfold fgComposable.
          split; try done. split; try done.
          rewrite fgComp_domm; try done. split; last split.
          - apply fgComp_dom_disjoint in Valid.
            apply fgComp_dom_disjoint in Valid23.
            clear -Valid Domm23 Valid23; set_solver.
          - unfold fgComp_eqn_check. apply map_Forall_lookup.
            intros n m Hnm. unfold fgComp_edgeflow.
            rewrite edgeflow_Comp; last by apply fgComposable_valid.
            apply fgComposable_valid in Valid. 
            destruct Valid as [_ [_ [_ [Check1_23 Check23_1]]]].
            assert (n ∈ domm (fg fg1 ⋅ fg fg2)) as Hdomm.
            { apply elem_of_dom; try done. }
            rewrite fgComp_domm in Hdomm; try done.
            apply elem_of_union in Hdomm.
            destruct Hdomm as [Hdomm | Hdomm].
            + unfold fgComp_eqn_check in Check1_23. 
              rewrite map_Forall_lookup in Check1_23.
              pose proof fgComp_flow (fg fg1) (fg fg2) n Hdomm Valid12 as H'.
              pose proof Check1_23 n m as Check1_23.
              rewrite H' in Hnm.
              pose proof Check1_23 Hnm as Check1_23.
              unfold fgComp_edgeflow in Check1_23.
              rewrite edgeflow_Comp in Check1_23; last by apply fgComposable_valid.
              by rewrite <-(ccm_assoc (edgeflow (fg fg1) n) (edgeflow (fg fg2) n) (edgeflow (fg fg3) n)).
            + unfold fgComp_eqn_check in Check23_1. 
              rewrite map_Forall_lookup in Check23_1.
              rewrite fgComp_comm in Hnm. rewrite fgComp_comm in Valid12.
              pose proof fgComp_flow (fg fg2) (fg fg3) n Hdomm Valid23 as H'.
              pose proof fgComp_flow (fg fg2) (fg fg1) n Hdomm Valid12 as H''.
              pose proof Check23_1 n m as Check23_1.
              rewrite H'' in Hnm. rewrite <-H' in Hnm.
              pose proof Check23_1 Hnm as Check23_1.
              unfold fgComp_edgeflow in Check23_1.
              rewrite edgeflow_Comp in Check23_1; last by apply fgComposable_valid.
              rewrite (ccm_comm (edgeflow (fg fg1) n) (edgeflow (fg fg2) n)).
              rewrite <-(ccm_assoc (edgeflow (fg fg2) n) (edgeflow (fg fg1) n) (edgeflow (fg fg3) n)).
              rewrite (ccm_comm (edgeflow (fg fg1) n) (edgeflow (fg fg3) n)).
              by rewrite (ccm_assoc (edgeflow (fg fg2) n) (edgeflow (fg fg3) n) (edgeflow (fg fg1) n)).
          - unfold fgComp_eqn_check. apply map_Forall_lookup.
            intros n m Hnm. unfold fgComp_edgeflow.
            rewrite edgeflow_Comp; last by apply fgComposable_valid.
            apply fgComposable_valid in Valid. 
            destruct Valid as [_ [_ [_ [Check1_23 Check23_1]]]].
            unfold fgComp_eqn_check in Check23_1. 
            rewrite map_Forall_lookup in Check23_1.
            rewrite fgComp_comm in Valid23.
            assert (n ∈ domm (fg fg3)) as Hdomm.
            { apply elem_of_dom; try done. }
            pose proof fgComp_flow (fg fg3) (fg fg2) n Hdomm Valid23 as H'.
            pose proof Check23_1 n m as Check23_1.
            rewrite <-H' in Hnm. rewrite fgComp_comm in Hnm.
            pose proof Check23_1 Hnm as Check23_1.
            unfold fgComp_edgeflow in Check23_1.
            rewrite fgComp_comm in Valid23.
            rewrite edgeflow_Comp in Check23_1; last by apply fgComposable_valid.
            rewrite (ccm_comm (edgeflow (fg fg1) n) (edgeflow (fg fg2) n)).
            rewrite (ccm_assoc (edgeflow (fg fg3) n) (edgeflow (fg fg2) n) (edgeflow (fg fg1) n)).
            by rewrite (ccm_comm (edgeflow (fg fg3) n) (edgeflow (fg fg2) n)).
        }
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
        { apply nzmap_eq. intros n. unfold edgeComp.
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

(* The empty flow graph is valid. *)
Lemma fgEmpty_valid : ✓ FG_empty.
Proof.
  unfold valid. unfold fgValid, FG_empty.
  split; try done.
Qed.

(* The empty flow graph is the unique valid flow graph whose domain is empty. *)
Lemma fgEmp_unique h : ✓ h → domm h ≡ ∅ → h = ∅.
Proof.
  intros V D.
  unfold valid, fgValid in V.
  destruct h as [[he hf] |]; last done.
  unfold empty, fg_empty, FG_empty, FG_emptyR.
  unfold domm, dom, flow_graph_dom, flow_map in D. 
  simpl in D. f_equal.
  assert (hf = ∅) as H'.
  { by apply dom_empty_inv. }
  destruct V as (? & V).
  simpl in V. rewrite D in V.
  assert (dom he = ∅) as He_domm.
  { set_solver. }
  assert (he = ∅) as H''.
  { apply nzmap_eq. intros n.
    rewrite nzmap_lookup_empty.
    destruct (decide (he ! n = 0)) as [? | He_n]; try done.
    rewrite <-nzmap_elem_of_dom_total in He_n.
    set_solver. }
  by rewrite H' H''.
Qed.

(* If a composite flow graph is empty then its components must have been empty. *)
Lemma fgComp_positive : ∀ (h1 h2: flow_graphT), h1 ⋅ h2 = ∅ → h1 = ∅.
Proof.
  intros h1 h2 C.
  pose proof fgEmpty_valid as V.
  unfold empty, fg_empty in C.
  rewrite <- C in V.
  pose proof (fgComp_valid_proj1 _ _ V) as V1.
  pose proof (fgComp_valid_proj2 _ _ V) as V2.
  assert (flow_map h1 = ∅) as D1.
  apply map_eq.
  intros n.
  assert (flow_map (h1 ⋅ h2) !! n = flow_map (FG_empty) !! n) as CL.
    by rewrite C; reflexivity.
  unfold op, fgComp in CL.
  unfold op, fgComp in C.
  destruct (decide (fgComposable h1 h2)).
  - unfold flow_map at 1 in CL. simpl in CL.
    rewrite gmap_imerge_prf in CL.
    rewrite lookup_empty.
    rewrite lookup_empty in CL.
    destruct (flow_map h1 !! n);
      destruct (flow_map h2 !! n);
      inversion CL.
    reflexivity. try done.
  - destruct (decide (h1 = ∅)) as [H1_empty | H1_empty].
    * rewrite H1_empty.
      unfold flow_map, empty at 1, fg_empty, FG_empty, FG_emptyR.
      simpl.
      reflexivity.
    * destruct (decide (h2 = ∅)) as [H2_empty | H2_empty].
      + unfold empty, fg_empty in H2_empty.
        contradiction.
      + unfold FG_empty in C.
        inversion C.
  - assert (domm h1 ≡ ∅).
    unfold domm, dom, flow_graph_dom.
    rewrite D1.
    rewrite dom_empty.
    reflexivity.
    pose proof (fgEmp_unique _ V1 H1).
    trivial.
Qed.

(* Flow graph composition is associative (invalid case). *)
Lemma fgComp_assoc_invalid (h1 h2 h3 : flow_graphT) : 
        ¬ ✓ (h1 ⋅ (h2 ⋅ h3)) → ¬ ✓ (h1 ⋅ h2 ⋅ h3) → h1 ⋅ (h2 ⋅ h3) ≡ h1 ⋅ h2 ⋅ h3.
Proof.
  intros IV1 IV2.
  pose proof (fgValid_composable h1 (h2 ⋅ h3)) as NC1.
  rewrite <- Decidable.contrapositive in NC1.
  pose proof (NC1 IV1) as Hcomp1.
  pose proof (fgValid_composable (h1 ⋅ h2) h3) as NC2.
  rewrite <- Decidable.contrapositive in NC2.
  pose proof (NC2 IV2)  as Hcomp2.
  all: try (unfold Decidable.decidable; auto).

  destruct (decide (h1 = ∅)) as [-> | H1_empty].
  - rewrite fgComp_comm.
    rewrite fgComp_unit.
    rewrite (fgComp_comm _ h2).
    rewrite fgComp_unit.
    reflexivity.
  - destruct (decide (h2 = ∅)) as [-> | H2_empty].
    + rewrite (fgComp_comm _ h3).
      repeat rewrite fgComp_unit.
      reflexivity.
    + destruct (decide ((h1 ⋅ h2) = ∅)) as [H12_empty | H12_empty].
      apply fgComp_positive in H12_empty.
      contradiction.
      * destruct (decide ((h2 ⋅ h3) = ∅)) as [H23_empty | H23_empty].
        ** apply fgComp_positive in H23_empty.
           contradiction.
        ** destruct (decide (h3 = empty)) as [H3_empty | H3_empty].
           rewrite H3_empty.
           repeat rewrite fgComp_unit.
           reflexivity.
           unfold op at 1, fgComp at 1.
           destruct (decide (fgComposable h1 (h2 ⋅ h3))).
           try done.
           unfold op at 6, fgComp.
           destruct (decide (fgComposable (h1 ⋅ h2) h3)).
           try done.
           destruct (decide (h1 = ∅)); try contradiction.
           destruct (decide (h2 ⋅ h3 = ∅)); try contradiction.
           destruct (decide (h1 ⋅ h2 = ∅)); try contradiction.
           destruct (decide (h3 = ∅)); try contradiction.
           reflexivity.
Qed.

Global Instance fgRAcore : PCore flow_graphT :=
  λ h, match h with
       | fg hr => Some FG_empty
       | fgUndef => Some fgUndef
       end.

Global Instance fgRAunit : cmra.Unit flow_graphT := FG_empty.

Definition flow_graphRA_mixin : RAMixin flow_graphT.
Proof.
  split; try apply _; try done.
  - (* Core is unique? *)
    intros ? ? cx -> ?. exists cx. done.
  - (* Associativity *)
    unfold Assoc. intros h1 h2 h3.
    destruct (decide (✓ (h1 ⋅ (h2 ⋅ h3)))).
    + by apply fgComp_assoc_valid.
    + destruct (decide (✓ (h1 ⋅ h2 ⋅ h3))) as [Valid | Invalid].
      * rewrite (fgComp_comm h1) in Valid.
        rewrite (fgComp_comm _ h3) in Valid.
        apply fgComp_assoc_valid in Valid.
        rewrite fgComp_comm in Valid.
        rewrite (fgComp_comm h3) in Valid.
        rewrite (fgComp_comm h2) in Valid.
        rewrite (fgComp_comm _ h1) in Valid.
        trivial.
      * by apply fgComp_assoc_invalid. 
  - (* Commutativity *)
    unfold Comm. apply fgComp_comm.
  - (* Core-ID *)
    intros x cx.
    destruct cx eqn:?; unfold pcore, fgRAcore; destruct x eqn:?;
      try (intros H1; inversion H1).
    + rewrite fgComp_comm.
      apply fgComp_unit.
    + apply fgComp_undef_op.
  - (* Core-Idem *)
    intros x cx.
    destruct cx; unfold pcore, fgRAcore; destruct x;
      try (intros H0; inversion H0); try done.
      intros H'; inversion H'. f_equal.
  - (* Core-Mono *)
    intros x y cx.
    destruct cx; unfold pcore, fgRAcore; destruct x; intros H';
      intros H''; inversion H''; destruct y; try eauto.
    + exists FG_empty. split; try done.
      exists (fg FG_emptyR). by rewrite fgComp_unit.
    + exists fgUndef. split; try done. exists fgUndef.
      rewrite fgComp_comm. by rewrite fgComp_unit.
    + exists FG_empty. split; try done.
      destruct H' as [a H'].
      assert (fgUndef ≡ fgUndef ⋅ a) as H'''; first by rewrite fgComp_undef_op.
      rewrite <- H' in H'''.
      inversion H'''.
  - (* Valid-Op *)
    intros x y. unfold valid. apply fgComp_valid_proj1.
Qed.

End flow_graph.            
  
  
  
  
  
  
  
  
  