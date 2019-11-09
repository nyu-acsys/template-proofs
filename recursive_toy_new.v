From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "Type*".

Variable findNext : val.

Definition traverse : val :=
  rec: "tr" "l" :=
    match: (findNext !"l") with
      NONE => !"l"
    | SOME "n'" => "l" <- "n'";; "tr" "l"
    end.

Definition searchStrOp (root: loc) : val :=
  λ: "",
    let: "l" := ref (#root) in
    let: "n" := traverse "l" in
    !"n".

Section stack_model.
  Context `{!heapG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  
  Variable root: loc.

  Lemma findNext_spec (X: gset loc) (x: loc):
    <<< ([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜x ∈ X⌝ >>>
      findNext #x @ ⊤
    <<< ∃ (b: bool) (y: loc), ([∗ set] n ∈ X, ∃ v: val, n ↦ v)
        ∗ ⌜b → y ∈ X⌝,
        RET (match b with true => SOMEV #y | false => NONEV end)
    >>>.
  Proof. Admitted. (* Omitting this proof for clarity *)

  Lemma traverse_spec (X: gset loc) (l: loc):
    (∃ (x: loc), l ↦ #x ∗ ⌜x ∈ X⌝) -∗ <<< ([∗ set] n ∈ X, ∃ v: val, n ↦ v) >>>
        traverse #l @ ⊤
    <<< ∃ (y: loc), ([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜y ∈ X⌝, RET #y >>>.
  Proof.
    iLöb as "IH". iIntros "Hl". iDestruct "Hl" as (x)"(Hl & #Hin)".
    iIntros (Φ) "AU". wp_lam. wp_bind (! _)%E. wp_load.
    wp_bind (findNext _ )%E. awp_apply (findNext_spec X x).
    iApply (aacc_aupd_abort with "AU"); first done. iIntros "Hset".
    iAssert (([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜x ∈ X⌝)%I with "[$]" as "Haacc".
    iAaccIntro with "Haacc"; first by iIntros "(HNs & _)"; eauto with iFrame.
    iIntros (b y) "(Hset & #Hy)". destruct b.
    - iModIntro. iSplitL "Hset". { done. }
      iIntros "AU". iModIntro. wp_match. wp_store.
      iApply ("IH" with "[Hl]"); last done. iExists y. iFrame.
      iDestruct "Hy" as %Hy. iPureIntro. apply Hy. done.
    - iModIntro. iSplitL "Hset"; first done. iIntros "AU".
      iModIntro. wp_match.
      iMod "AU" as "[HNs [_ HClose]]". wp_load.
      iMod ("HClose" with "[$]") as "HΦ".
      iModIntro. done.
  Qed.

  Theorem searchStrOp_spec (X: gset loc):
      ⌜root ∈ X⌝ -∗ <<< ([∗ set] n ∈ X, ∃ v: val, n ↦ v) >>>
            searchStrOp root #()
                  @ ⊤
      <<< ∃ (y: loc) (v: val), y ↦ v ∗ ⌜y ∈ X⌝ , RET v >>>.
  Proof.
    iIntros "#Hinr". iIntros (Φ) "AU". wp_lam. wp_alloc l as "Hl". 
    wp_let. wp_bind (traverse _)%E. awp_apply (traverse_spec X l with "[Hl]").
    iExists root. eauto with iFrame.
    iApply (aacc_aupd_abort with "AU"); first done. iIntros "Hset".
    iAssert (([∗ set] n ∈ X, ∃ v: val, n ↦ v))%I with "[$]" as "Haacc".
    iAaccIntro with "Haacc". eauto with iFrame.
    iIntros (y) "(Hset & #Hiny)". iModIntro. iFrame. iIntros "AU".
    iModIntro. wp_let. iMod "AU" as "[HNs [_ HClose]]".
    iDestruct "Hiny" as %Hiny.
    rewrite (big_sepS_elem_of_acc _ (X) y); last done.
    iDestruct "HNs" as "(Hy & Hr)". iDestruct "Hy" as (v) "Hy".
    wp_load. iMod ("HClose" with "[Hy]") as "HΦ".
    iFrame; iPureIntro; done. iModIntro. done.
  Qed.

      
  
  
  
  
  
  
  
  
  
