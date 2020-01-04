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

Definition Node := positive.

Parameter FlowDom: CCM.

Compute ccm_unit.

Definition M := @ccm_car FlowDom.
Local Notation "x + y" := (@ccm_op FlowDom x y).
Local Notation "x - y" := (@ccm_opinv FlowDom x y).
Local Notation "0" := (@ccm_unit FlowDom).

Record flowintR :=
  {
    infR : gmap Node M;
    outR : gmap Node M;
  }.

Definition I_emptyR := {| infR := ∅; outR := ∅ |}.

Inductive flowintT :=
| int: flowintR → flowintT
| intUndef: flowintT.

Instance flowdom_eq_dec: EqDecision M.
Proof.
  apply (@ccm_eq FlowDom).
Qed.


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

Definition dom (I: flowintT) :=
  match I with
  | int Ir => mapset_dom (infR Ir)
  | intUndef => ∅
  end.

Definition I_empty := int I_emptyR.

Canonical Structure flowintRAC := leibnizO flowintT.

Instance flowint_valid : Valid flowintT :=
  λ I, match I with
       | int Ir =>
         infR Ir ##ₘ outR Ir
         ∧ (infR Ir = ∅ → outR Ir = ∅)
       | intUndef => False
       end.

Instance int_eq_dec: EqDecision flowintT.
Proof.
  unfold EqDecision.
  unfold Decision.
  repeat decide equality.
  all: apply gmap_eq_eq.
Qed.

Instance flowint_valid_dec (I: flowintT) : Decision (flowint_valid I).
Proof.
  intros.
  unfold Decision.
  unfold flowint_valid.
  destruct I.
  admit.
Admitted.

Definition intComposable (I1: flowintT) (I2: flowintT) :=
  flowint_valid I1 ∧ flowint_valid I2 ∧
  dom I1 ## dom I2 ∧
  map_Forall (λ (n: Node) (m: M), inf I1 n = out I2 n + (inf I1 n - out I2 n)) (inf_map I1) ∧
  map_Forall (λ (n: Node) (m: M), inf I2 n = out I1 n + (inf I2 n - out I1 n)) (inf_map I2).

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
             let inf12 := gmap_imerge M M M f_inf (inf_map I1) (inf_map I2) in
             let f_out n o1 o2 : option M :=
                 match o1, o2 with
                 | Some m1, None =>
                   if gset_elem_of_dec n (dom I2) then None else Some m1
                 | None, Some m2 =>
                   if gset_elem_of_dec n (dom I1) then None else Some m2
                 | Some m1, Some m2 => Some (m1 + m2)
                 | _, _ => None
                 end
             in
             let out12 := gmap_imerge M M M f_out (out_map I1) (out_map I2) in
             int {| infR := inf12; outR := out12 |}
           else if decide (I1 = I_empty) then I2
                else if decide (I2 = I_empty) then I1
                     else intUndef.
