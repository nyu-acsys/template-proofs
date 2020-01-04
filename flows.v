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
  reflexivity.
  unfold intComposable.
  cut (¬ (✓ intUndef)); intros.
  rewrite LeftAbsorb_instance_0.
  trivial.
  unfold valid; unfold flowint_valid.
  auto.
Qed.

Hypothesis intComp_unit : ∀ (I: flowintT), ✓ I → I ⋅ I_empty ≡ I.

Hypothesis intComp_assoc : ∀ (I1 I2 I3: flowintT), I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.

Hypothesis intComp_comm : ∀ (I1 I2: flowintT), I1 ⋅ I2 ≡ I2 ⋅ I1.

Hypothesis intComp_valid2 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I1.

Hypothesis intComp_dom : ∀ I1 I2 I, ✓ I → I = I1 ⋅ I2 → domm I = domm I1 ∪ domm I2.

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

(* Lemma flowint_comp_fp : ∀ I1 I2 I, ✓I → I = I1 ⋅ I2 → dom I = dom I1 ∪ dom I2. *)
(* Proof. *)
  (* apply intComp_dom. *)
(* Qed. *)
