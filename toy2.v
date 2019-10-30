From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "Type*".

Definition lockNode : val :=
  rec: "lockN" "x" :=
    if: CAS "y" #false #true
    then #()
    else "lockN" "x".

Definition unlockNode : val :=
  λ: "x",
  "y" <- #false.

Definition prog : val := 
  λ: "x" "v",
  lockNode "x";;
  "x" <- "v";;
  unlockNode "x";; "v".

Section Toy_Template.
  Context `{!heapG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

(*
  Definition toyN : namespace := N .@ "toy".

  Definition main_inv x y (b: bool) d := (y ↦ #b ∗ if b then True else x ↦ d)%I.

  Definition is_toy x y := inv toyN (∃ b d, main_inv x y b d)%I.

  Instance main_inv_timeless x y b d: Timeless (main_inv x y b d).
  Proof.
    rewrite /main_inv. repeat apply bi.sep_timeless; try apply _.
    destruct b; try apply _.
  Qed.

  Lemma lockNode_spec (x y: loc):
      is_toy x y -∗
      <<< True >>> lockNode #x @ ⊤∖↑toyN <<< y ↦ #true, RET #() >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind (CmpXchg _ _ _)%E.
    iInv "HInv" as "HI".
*)

  Definition main_inv x y := (∃ (b:bool) d, y ↦ #b ∗ if b then True else x ↦ d)%I.

  Lemma lockNode_spec (x y: loc):
      <<< main_inv x y >>> lockNode #x @ ⊤ <<< main_inv x y ∗ y ↦ #true, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind (CmpXchg _ _ _)%E.
    iMod "AU" as "[hoho [_ HClose]]".
