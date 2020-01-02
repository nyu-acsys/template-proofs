From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Export auth agree.
From stdpp Require Import mapset finite.


(* ---------- Flow Interface encoding and camera definitions ---------- *)

(* All hypotheses in this file are proved as lemmas of the same name
   in the flows.spl file in GRASShopper *)

Definition key := nat.

Definition Node := nat.

Definition flowdom := nat.

Definition domZero : flowdom := O.

Record flowintR :=
  {
    inf : gmap Node flowdom;
    out : gmap Node flowdom;
  }.

Inductive flowintT :=
| int: flowintR → flowintT
| intUndef: flowintT.

Definition I_emptyR := {| inf := ∅; out := ∅ |}.

Definition I_empty := int I_emptyR.

Definition default_Ir (I : flowintT) : flowintR :=
  match I with
  | int Ir => Ir
  | intUndef => I_emptyR
  end.

Definition inf' (I : flowintT) := inf (default_Ir I).
Definition out' (I : flowintT) := out (default_Ir I).

Definition inf_lookup (I : flowintT) (n : Node) := (inf' I !! n).
Definition out_lookup (I : flowintT) (n : Node) := (out' I !! n).

Notation "I ◁ n" := (inf_lookup I n) (no associativity, at level 20).
Notation "I ▷ n" := (out_lookup I n) (no associativity, at level 20).

Canonical Structure flowintRAC := leibnizO flowintT.

(** The following hypotheses are proved in GRASShopper. See flows.spl *)
Instance int_eq_dec: EqDecision flowintT.
Proof.
  unfold EqDecision.
  unfold Decision.
  repeat decide equality.
  all: apply gmap_eq_eq.
Qed.

Instance int_elem_of : ElemOf Node flowintT :=
  λ n I, n ∈ mapset_dom (inf' I).

Instance int_dom : Dom flowintT (gset Node) :=
  λ I, mapset_dom (inf' I).

Lemma int_elem_of_dec : RelDecision (∈@{flowintT}).
Proof.
  unfold RelDecision.
  intros.
  unfold elem_of; unfold int_elem_of.
  apply gset_elem_of_dec.
Qed.

Instance intValid : Valid flowintT :=
  λ I,
  I ≠ intUndef
  (* outflow is valid on proper domain *)
  ∧ (∀ n, n ∉ I -> ∃ f, (I ▷ n) = Some f)
  (* Inflow and outflow are properly defined *)
  ∧ (∀ n, n ∈ I -> (I ▷ n) = None)
  ∧ (∀ n, n ∉ I -> (I ◁ n) = None).

Hypothesis node_finite : Finite Node.

Lemma gmap_lookup_eq_dec {A} `{Countable K, EqDecision A} :
  ∀ (m : gmap K A) (k : K) (oa : option A), Decision (m !! k = oa).
Proof.
  intros.
  exact (option_eq_dec (m !! k) oa).
Qed.

Instance intValid_dec : ∀ I: flowintT, Decision (✓ I).
Proof.
  intros.
  unfold valid; unfold intValid.
  repeat apply and_dec.
  apply not_dec; apply int_eq_dec.
  all: apply forall_dec; intros; apply impl_dec.
  1,5: apply not_dec.
  1,2,4: apply int_elem_of_dec.
  apply exists_dec; intros.
  all: (unfold out_lookup || unfold inf_lookup); apply option_eq_dec.
Qed.

Definition option_apply {A} {B} {C} (f : A -> B -> C) (x : option A) (y : option B) : option C :=
  match x, y with
  | Some x', Some y' => Some (f x' y')
  | _, _ => None
  end.

Definition option_add := option_apply Init.Nat.add.
Definition option_sub := option_apply Init.Nat.sub.
Notation "x ⊕ y" := (option_add x y) (at level 50).
Notation "x ⊖ y" := (option_sub x y) (at level 50).

Definition intComposable (I1 I2 : flowintT) : Prop :=
  (✓ I1) ∧ (✓ I2)
  ∧ (dom _ I1 ## dom (gset Node) I2)
  ∧ (∀ n, n ∈ I1 → I1 ◁ n = I2 ▷ n ⊕ (I1 ◁ n ⊖ I2 ▷ n))
  ∧ (∀ n, n ∈ I2 → I2 ◁ n = I1 ▷ n ⊕ (I2 ◁ n ⊖ I1 ▷ n))
  ∧ (∀ n, n ∈ I1 → ∃ x, (I1 ◁ n ⊕ I2 ▷ n) = Some x)
  ∧ (∀ n, n ∈ I2 → ∃ x, (I2 ◁ n ⊕ I1 ▷ n) = Some x).

Instance intComposable_dec : ∀ I1 I2, Decision (intComposable I1 I2).
Proof.
  intros.
  unfold intComposable.
  repeat apply and_dec.
  all: try apply forall_dec; intros.
  1,5: apply not_dec; apply int_eq_dec.
  all: apply impl_dec.
  all: try ((apply gset_elem_of_dec) || (try apply not_dec; apply gset_elem_of_dec)).
  all: try apply exists_dec; intros; apply option_eq_dec.
Qed.

Definition func_to_gmap `{Countable K} {A} (f : K → option A) (ks : list K) : gmap K A :=
  foldr (λ k map, match f k with Some a => insert k a map | None => map end) ∅ ks.

Definition nodes (I1 I2 : flowintT) : list Node :=
  elements $
  mapset_dom (inf' I1)
  ∪ mapset_dom (inf' I2)
  ∪ mapset_dom (out' I1)
  ∪ mapset_dom (out' I2).

Definition infComp (n : Node) (I1 I2 : flowintT) : option flowdom :=
  if decide (n ∈ I1) then ((I1 ◁ n) ⊖ (I2 ▷ n))
  else if decide (n ∈ I2) then ((I2 ◁ n) ⊖ (I1 ▷ n))
  else None.

Instance intComp : Op flowintT :=
  λ I1 I2,
  in
  let outCompFunc := λ n,
                     None
      (* if decide (n ∉ I1 ∧ n ∉ I2) then (I1 ▷ n ⊕ I2 ▷ n) *)
      (* else None *)
  in
  if decide (intComposable I1 I2) then
    int {|
      inf := func_to_gmap infCompFunc nodes;
      out := func_to_gmap outCompFunc nodes
    |}
  else
    intUndef.

Lemma intEmp_valid : ✓ I_empty.
Proof.
  unfold valid; unfold intValid.
  repeat split.
  unfold I_empty; discriminate.
  intros.
Admitted.

Hypothesis intComp_unit : ∀ (I: flowintT), I ⋅ I_empty ≡ I.

Hypothesis intComp_assoc : ∀ (I1 I2 I3: flowintT), I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.

Hypothesis intComp_comm : ∀ (I1 I2: flowintT), I1 ⋅ I2 ≡ I2 ⋅ I1.

Hypothesis intComp_undef_op : ∀ I, intUndef ⋅ I ≡ intUndef.

Hypothesis intComp_valid2 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I1.

Hypothesis intComp_dom : ∀ I1 I2 I, ✓ I → I = I1 ⋅ I2 → dom I = dom I1 ∪ dom I2.

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

Lemma flowint_comp_fp : ∀ I1 I2 I, ✓I → I = I1 ⋅ I2 → dom I = dom I1 ∪ dom I2.
Proof.
  apply intComp_dom.
Qed.
