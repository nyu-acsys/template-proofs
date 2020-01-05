From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Export auth agree.

From stdpp Require Export gmap.
From stdpp Require Import mapset.
From stdpp Require Import finite.
Require Export ccm gmap_more.

Require Import Coq.Setoids.Setoid.

(* ---------- Flow Interface encoding and camera definitions ---------- *)

Definition Node := positive.

Parameter FlowDom: CCM.

Definition flowdom := @ccm_car FlowDom.
Local Notation "x + y" := (@ccm_op FlowDom x y).
Local Notation "x - y" := (@ccm_opinv FlowDom x y).
Local Notation "0" := (@ccm_unit FlowDom).


Record flowintR :=
  {
    infR : gmap Node flowdom;
    outR : gmap Node flowdom;
  }.

Inductive flowintT :=
| int: flowintR → flowintT
| intUndef: flowintT.

Definition I_emptyR := {| infR := ∅; outR := ∅ |}.
Definition I_empty := int I_emptyR.
Instance flowint_empty : Empty flowintT := I_empty.


Definition out_map (I: flowintT) :=
  match I with
    | int Ir => outR Ir
    | intUndef => ∅
  end.

Definition inf_map (I: flowintT) :=
  match I with
    | int Ir => infR Ir
    | intUndef => ∅
  end.

Definition inf (I: flowintT) (n: Node) := default 0 (inf_map I !! n).
Definition out (I: flowintT) (n: Node) := default 0 (out_map I !! n).

Instance flowint_dom : Dom flowintT (gset Node) :=
  λ I, dom (gset Node) (inf_map I).
Definition domm (I : flowintT) := dom (gset Node) I.

Instance flowint_elem_of : ElemOf Node flowintT :=
  λ n I, n ∈ domm I.

(* Composition and proofs - some of these have counterparts in flows.spl in GRASShopper *)

Instance flowdom_eq_dec: EqDecision flowdom.
Proof.
  apply (@ccm_eq FlowDom).
Qed.

Canonical Structure flowintRAC := leibnizO flowintT.

Instance int_eq_dec: EqDecision flowintT.
Proof.
  unfold EqDecision.
  unfold Decision.
  repeat decide equality.
  all: apply gmap_eq_eq.
Qed.

Instance flowint_valid : Valid flowintT :=
  λ I, match I with
       | int Ir =>
         infR Ir ##ₘ outR Ir
         ∧ (infR Ir = ∅ → outR Ir = ∅)
       | intUndef => False
       end.

Instance flowint_valid_dec : ∀ I: flowintT, Decision (✓ I).
Proof.
  intros.
  unfold valid; unfold flowint_valid.
  destruct I; last first.
  all: solve_decision.
Qed.

Definition intComposable (I1: flowintT) (I2: flowintT) :=
  ✓ I1 ∧ ✓ I2 ∧
  domm I1 ## domm I2 ∧
  map_Forall (λ (n: Node) (m: flowdom), inf I1 n = out I2 n + (inf I1 n - out I2 n)) (inf_map I1) ∧
  map_Forall (λ (n: Node) (m: flowdom), inf I2 n = out I1 n + (inf I2 n - out I1 n)) (inf_map I2).

Instance intComposable_dec (I1 I2: flowintT) : Decision (intComposable I1 I2).
Proof. solve_decision. Qed.

Instance intComp : Op flowintT :=
  λ I1 I2, if decide (intComposable I1 I2) then
             let f_inf n o1 o2 :=
                 match o1, o2 with
                 | Some m1, _ => Some (m1 - out I2 n)
                 | _, Some m2 => Some (m2 - out I1 n)
                 | _, _ => None
                 end
             in
             let inf12 := gmap_imerge flowdom flowdom flowdom f_inf (inf_map I1) (inf_map I2) in
             let f_out n o1 o2 : option flowdom :=
                 match o1, o2 with
                 | Some m1, None =>
                   if gset_elem_of_dec n (domm I2) then None else Some m1
                 | None, Some m2 =>
                   if gset_elem_of_dec n (domm I1) then None else Some m2
                 | Some m1, Some m2 => Some (m1 + m2)
                 | _, _ => None
                 end
             in
             let out12 := gmap_imerge flowdom flowdom flowdom f_out (out_map I1) (out_map I2) in
             int {| infR := inf12; outR := out12 |}
           else if decide (I1 = ∅) then I2
           else if decide (I2 = ∅) then I1
           else intUndef.

Lemma intEmp_valid : ✓ I_empty.
Proof.
  unfold valid.
  unfold flowint_valid.
  unfold I_empty.
  simpl.
  split.
  refine (map_disjoint_empty_l _).
  trivial.
Qed.

Lemma intComp_undef_op : ∀ I, intUndef ⋅ I ≡ intUndef.
Proof.
  intros.
  unfold op; unfold intComp.
  rewrite decide_False.
  unfold empty.
  unfold flowint_empty.
  rewrite decide_False.
  destruct (decide (I = I_empty)).
  1, 2: trivial.
  discriminate.
  unfold intComposable.
  cut (¬ (✓ intUndef)); intros.
  rewrite LeftAbsorb_instance_0.
  trivial.
  unfold valid; unfold flowint_valid.
  auto.
Qed.

Lemma intComp_unit : ∀ (I: flowintT), ✓ I → I ⋅ I_empty ≡ I.
Proof.
  intros.
  unfold op, intComp.
  simpl.
  repeat rewrite gmap_imerge_empty.
  destruct I as [Ir|].
  destruct (decide (intComposable (int Ir) I_empty)).
  - (* True *)
    destruct Ir.
    simpl.
    auto.
  - (* False *)
    unfold empty, flowint_empty.
    destruct (decide (int Ir = I_empty)).
    auto.
    rewrite decide_True.
    all: auto.
  - unfold intComposable.
    rewrite decide_False.
    rewrite decide_False.
    rewrite decide_True.
    all: auto.
  - intros.
    case y.
    2: auto.
    intros.
    case (gset_elem_of_dec i (domm I_empty)).
    2: auto.
    intros H_false; contradict H_false.
    unfold domm.
    replace I_empty with (empty : flowintT).
    replace (dom (gset Node) empty) with (empty : gset Node).
    apply not_elem_of_empty.
    symmetry.
    apply dom_empty_L.
    unfold empty.
    unfold flowint_empty.
    reflexivity.
  - intros.
    case y.
    intros.
    unfold out.
    rewrite lookup_empty.
    simpl.
    rewrite ccm_pinv_unit.
    all: easy.
Qed.

Lemma intComposable_comm_1 : ∀ (I1 I2 : flowintT), intComposable I1 I2 → intComposable I2 I1.
Proof.
  intros.
  unfold intComposable.
  repeat split.
  3: apply disjoint_intersection; rewrite intersection_comm_L; apply disjoint_intersection.
  unfold intComposable in H.
  all: try apply H.
Qed.

Lemma intComposable_comm : ∀ (I1 I2 : flowintT), intComposable I1 I2 ↔ intComposable I2 I1.
Proof.
  intros. split.
  all: refine (intComposable_comm_1 _ _).
Qed.

Lemma intComp_dom : ∀ I1 I2 I, ✓ I → I = I1 ⋅ I2 → domm I = domm I1 ∪ domm I2.
Proof.
  intros I1 I2 I H_valid H_comp_eq.
  unfold domm.
  set_unfold.
  intros.
  split.
  - case_eq (decide (intComposable I1 I2)).
    + intros H_comp _.
      rewrite H_comp_eq.
      unfold op, intComp.
      unfold dom, flowint_dom; simpl.
      rewrite elem_of_dom.
      unfold gmap_imerge; simpl.
      unfold lookup, gmap_lookup; simpl.
      destruct (inf_map I1) as [m1 m1_wf], (inf_map I2) as [m2 m2_wf].
      intros H_some.
      rewrite decide_True in H_some. 2: auto.
      simpl in H_some.
      rewrite lookup_imerge in H_some.
      set (pos := encode x) in H_some.
      case_eq (m1 !! pos).
      * intros.
        left.
        rewrite elem_of_dom.
        unfold lookup, gmap_lookup.
        rewrite H.
        now apply (mk_is_Some (Some f)) with (x := f).
      * case_eq (m2 !! pos).
        intros.
        right.
        rewrite elem_of_dom.
        unfold lookup, gmap_lookup.
        rewrite H.
        now apply (mk_is_Some (Some f)) with (x := f).
        intros H1_none H2_none.
        contradict H_some.
        rewrite H1_none H2_none.
        exact is_Some_None.
      * auto.
    + intros H_not_comp H_not_comp_dec.
      unfold dom, flowint_dom; simpl.
      rewrite elem_of_dom.
      intros H_some.
      unfold op, intComp in H_comp_eq.
      rewrite H_not_comp_dec in H_comp_eq.
      case_eq (decide (I1 = ∅)).
      * intros H1_empty.
        rewrite decide_True in H_comp_eq; last by assumption.
        right.
        rewrite elem_of_dom.
        now rewrite <- H_comp_eq.
      * intros.
        rewrite decide_False in H_comp_eq; last by assumption.
        case (decide (I2 = ∅)).
        intros.
        rewrite decide_True in H_comp_eq; last by assumption.
        left.
        rewrite elem_of_dom.
        now rewrite <- H_comp_eq.
        intros.
        rewrite decide_False in H_comp_eq; last by assumption.
        contradict H_some.
        rewrite H_comp_eq.
        simpl.
        rewrite lookup_empty.
        exact is_Some_None.
    - intros.
      rewrite H_comp_eq.
      unfold op, intComp.
      case_eq (decide (intComposable I1 I2)).
      + intros H_comp H_comp_dec.
        unfold dom, flowint_dom; simpl.
        rewrite elem_of_dom.
        unfold gmap_imerge; simpl.
        unfold lookup, gmap_lookup; simpl.
        destruct (inf_map I1) as [m1 m1_wf] eqn:H1_rem, (inf_map I2) as [m2 m2_wf] eqn:H2_rem.
        rewrite lookup_imerge; last auto.
        set (pos := encode x).
        case_eq (m1 !! pos).
        intros.
        rewrite is_Some_alt; auto.
        case_eq (m2 !! pos).
        intros.
        rewrite is_Some_alt; auto.
        intros.
        contradict H.
        unfold not.
        rewrite Decidable.not_or_iff.
        split.
        all: intros tmp; contradict tmp.
        all: unfold dom, flowint_dom; rewrite elem_of_dom.
        all: try rewrite H1_rem; try rewrite H2_rem.
        all: unfold lookup, gmap_lookup.
        rewrite H1; exact is_Some_None.
        rewrite H0; exact is_Some_None.
      + intros H_not_comp H_not_comp_dec.
        case_eq (decide (I1 = ∅)).
        intros H1_empty.
        destruct H.
        contradict H.
        rewrite H1_empty.
        unfold dom, flowint_dom; simpl.
        rewrite elem_of_dom.
        rewrite lookup_empty.
        exact is_Some_None.
        intros _; assumption.
        intros H1_not_empty H1_not_empty_dec.
        case_eq (decide (I2 = ∅)).
        intros H2_empty.
        destruct H.
        intros; assumption.
        intros _.
        contradict H.
        rewrite H2_empty.
        unfold dom, flowint_dom; simpl.
        rewrite elem_of_dom.
        rewrite lookup_empty.
        exact is_Some_None.
        intros H2_not_empty H2_not_empty_dec.
        contradict H_valid.
        rewrite H_comp_eq.
        unfold op, intComp.
        rewrite H_not_comp_dec.
        rewrite H1_not_empty_dec.
        rewrite H2_not_empty_dec.
        now unfold valid, flowint_valid.
Qed.

Hypothesis intComp_valid2 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I1.

Hypothesis intComp_comm : ∀ (I1 I2: flowintT), I1 ⋅ I2 ≡ I2 ⋅ I1.

Hypothesis intComp_assoc : ∀ (I1 I2 I3: flowintT), I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.

Instance flowintRAcore : PCore flowintT :=
  λ I, match I with
       | int Ir => Some I_empty
       | intUndef => Some intUndef
       end.

Instance flowintRAunit : cmra.Unit flowintT := I_empty.

Definition flowintRA_mixin : RAMixin flowintT.
Proof.
  split; try apply _; try done.
  - (* Core is unique? *)
    intros ? ? cx -> ?. exists cx. done.
  - (* Associativity *)
    unfold Assoc. eauto using intComp_assoc.
  - (* Commutativity *)
    unfold Comm. eauto using intComp_comm.
  - (* Core-ID *)
    intros x cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x;
      try (intros H; inversion H).
    + rewrite intComp_comm. apply intComp_unit.
    + apply intComp_undef_op.
  - (* Core-Idem *)
    intros x cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x;
      try (intros H; inversion H); try done.
  - (* Core-Mono *)
    intros x y cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x; intros H;
      intros H1; inversion H1; destruct y; try eauto.
    + exists I_empty. split; try done.
      exists (int I_emptyR). by rewrite intComp_unit.
    + exists intUndef. split; try done. exists intUndef.
      rewrite intComp_comm. by rewrite intComp_unit.
    + exists I_empty. split; try done.
      destruct H as [a H].
      assert (intUndef ≡ intUndef ⋅ a); first by rewrite intComp_undef_op.
      rewrite <- H0 in H.
      inversion H.
  - (* Valid-Op *)
    intros x y. unfold valid. apply intComp_valid2.
Qed.


Canonical Structure flowintRA := discreteR flowintT flowintRA_mixin.

Instance flowintRA_cmra_discrete : CmraDiscrete flowintRA.
Proof. apply discrete_cmra_discrete. Qed.

Instance flowintRA_cmra_total : CmraTotal flowintRA.
Proof.
  rewrite /CmraTotal. intros. destruct x.
  - exists I_empty. done.
  - exists intUndef. done.
Qed.

Lemma flowint_ucmra_mixin : UcmraMixin flowintT.
Proof.
  split; try apply _; try done.
  - unfold ε, flowintRAunit, valid. apply intEmp_valid.
  - unfold LeftId. intros x. unfold ε, flowintRAunit. simpl.
    destruct x.
    + rewrite intComp_comm. by rewrite intComp_unit.
    + rewrite intComp_comm. by rewrite intComp_unit.
Qed.

Canonical Structure flowintUR : ucmraT := UcmraT flowintT flowint_ucmra_mixin.

Parameter contextualLeq : flowintUR → flowintUR → Prop.

Definition flowint_update_P (I I_n I_n': flowintUR) (x : authR flowintUR) : Prop :=
  match (auth_auth_proj x) with
  | Some (q, z) => ∃ I', (z = to_agree(I')) ∧ q = 1%Qp ∧ (I_n' = auth_frag_proj x)
                        ∧ contextualLeq I I' ∧ ∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o
  | _ => False
  end.

Hypothesis flowint_update : ∀ I I_n I_n',
  contextualLeq I_n I_n' → (● I ⋅ ◯ I_n) ~~>: (flowint_update_P I I_n I_n').

Lemma flowint_comp_fp : ∀ I1 I2 I, ✓I → I = I1 ⋅ I2 → domm I = domm I1 ∪ domm I2.
Proof.
  apply intComp_dom.
Qed.
