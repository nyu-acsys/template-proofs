From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "Type*".

Definition write: val := 
  λ: "x" "v",
      "x" <- "v".

Definition write2: val :=
  λ: "x" "y" "v1" "v2",
      write "x" "v1" ;;
      write "y" "v2" ;; "v1".

Section Give_Up_Template.
  Context `{!heapG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Lemma write_spec (x: loc) v:
         <<< ∃ d, x ↦ #d >>> write #x #v @ ⊤ <<< x ↦ #v, RET #() >>>.
  Proof. 
    iIntros (Φ) "AU". wp_lam. wp_let.
    iMod "AU" as "[Hx [_ Hcl]]". iDestruct "Hx" as (d)"Hx". 
    wp_store. iMod ("Hcl" with "Hx") as "HΦ".
    iModIntro. done.
  Qed.

  Lemma write2_spec (x y:loc) v1 v2:
        ((∃ d, x ↦ #d) ∗ (∃ d', y ↦ #d'))%I -∗ 
              <<< True >>> write2 #x #y #v1 #v2 @ ⊤ <<< x ↦ #v1, RET #v1 >>>.
  Proof. 
    iIntros "(Hx & Hy)". iIntros (Φ) "AU". wp_lam.
    wp_pures. wp_bind (write _ _)%E.
    awp_apply (write_spec x v1).
    iAaccIntro with "Hx". eauto with iFrame.
    iIntros "H". iMod "AU" as "[Ht [_ Hcl]]".
    iMod ("Hcl" with "H") as "HΦ".
    iModIntro. wp_pures. wp_bind (write _ _)%E.
    (* iDestruct "Hy" as "_". iDestruct "Ht" as "_". iDestruct "HΦ" as "_". *)
    awp_apply (write_spec y v2).