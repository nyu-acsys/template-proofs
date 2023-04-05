(*
Differences compared to hindsight.v:

1) History needs to be updated anytime a snapshot is 
  updated (and not just when the abstract state is udpated).
2) M !!! T = s -> M !!! T ≡ s
*)

From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants fancy_updates.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
From diaframe.heap_lang Require Import proof_automation atomic_specs wp_auto_lob.
Require Export hindsight_mod.

Module SEARCH_STRUCTURE <: ABSTRACT_DATA_TYPE with Definition absTUR := gsetUR nat.

  Parameter search : val.
  Parameter insert : val.
  Parameter delete : val.

  Definition dsOp : val :=
    λ: "OP" "r" "k",     
      if: "OP" = #0 
      then search "r" "k"
      else if: "OP" = #1 
      then insert "r" "k"
      else delete "r" "k".

  (* Definition K := Z. *)
  Inductive Opp := searchOp : nat → Opp | insertOp : nat → Opp | deleteOp : nat → Opp.
  Definition Op := Opp.

  Definition Op_to_val (op: Op) : val :=
    match op with
    | searchOp _ => #0
    | insertOp _ => #1
    | deleteOp _ => #2 
    end.
    
  Definition absTUR := gsetUR nat.
  Definition absT := ucmra_car absTUR.

  Definition resT := bool.
  Definition resT_to_base_lit (b: resT) : base_lit := LitBool b.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Definition resT_from_val (v : val) : option bool :=
    match v with
    | LitV(LitBool b) => Some b
    | _               => None
    end.
  Definition resT_to_val (b : bool) : val := LitV(LitBool b).
  
  Lemma resT_inj_prop : ∀ (b : bool), bool_from_val (bool_to_val b) = Some b.
  Proof. done. Qed.

  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.

  Lemma resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  Proof. try done. Qed.

  Definition seq_spec (op: Op) (C: absT) (C': absT) (res: bool) : Prop :=
    match op with
    | searchOp k => C' = C ∧ (if res then k ∈ C else k ∉ C)
    | insertOp k => C' = C ∪ {[k]} ∧ (if res then k ∉ C else k ∈ C)
    | deleteOp k => C' = C ∖ {[k]} ∧ (if res then k ∈ C else k ∉ C)
    end.

  Global Instance seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Proof.
    intros op c c' res. unfold seq_spec. 
    destruct op; try apply and_dec; try destruct res; try apply _.
  Qed.

  Definition updater_thread (op: Op) (res: resT) : bool := 
    match op, res with
    | searchOp _, _ => false
    | _, false => false
    | _, _ => true
    end.

  Global Instance updater_thread_dec: ∀ op res b, 
    Decision (updater_thread op res = b).
  Proof.
    intros op res b. unfold updater_thread.
    destruct op; destruct res; try apply _.
  Qed.  

  Global Instance Op_inhabited : Inhabited Op := populate (searchOp 0).
  Global Instance absTUR_discrete : CmraDiscrete absTUR.
  Proof. try apply _. Qed.
  Global Instance resT_inhabited : Inhabited resT.
  Proof. try apply _. Qed.

End SEARCH_STRUCTURE.
