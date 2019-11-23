From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Export auth agree.


(* ---------- Flow Interface encoding and camera definitions ---------- *)

(* All hypotheses in this file are proved as lemmas of the same name
   in the flows.spl file in GRASShopper *)

Definition key := nat. (* TODO put this in the templates file *)

Definition Node := nat.

Definition flowdom := nat.

Record flowintR :=
  {
    inf : gmap Node flowdom;
    out : gmap Node flowdom;
    domm : gset Node;  (* This is dom in GRASShopper, but Coq doesn't let me overload *)
  }.

Definition I_emptyR := {| inf := ∅; out := ∅; domm := ∅ |}.

Inductive flowintT :=
| int: flowintR → flowintT
| intUndef: flowintT.

Definition dom (I: flowintT) :=
  match I with
  | int Ir => domm Ir
  | intUndef => ∅
  end.

Definition I_empty := int I_emptyR.

Canonical Structure flowintRAC := leibnizO flowintT.

(** The following hypotheses are proved in GRASShopper. See flows.spl *)
Hypothesis intComp : Op flowintT.

Hypothesis intComp_unit : ∀ (I: flowintT), I ⋅ I_empty ≡ I.

Hypothesis intComp_assoc : ∀ (I1 I2 I3: flowintT), I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.

Hypothesis intComp_comm : ∀ (I1 I2: flowintT), I1 ⋅ I2 ≡ I2 ⋅ I1.

Hypothesis intComp_undef_op : ∀ I, intUndef ⋅ I ≡ intUndef.

Hypothesis intValid : Valid flowintT.

Hypothesis intComp_valid2 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I1.

Hypothesis intEmp_valid : intValid I_empty.

Hypothesis intComp_dom : ∀ I1 I2 I, ✓I → I = I1 ⋅ I2 → dom I = dom I1 ∪ dom I2.

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

(* TODO: let's rename this to intLeq to be consistent with Grasshopper *)
(* TODO these need to be updated after coupling is updated. *)
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