From iris.heap_lang Require Export lifting notation locations lang.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type*".

Variable findNext : val.

Definition traverse : val :=
  rec: "tr" "n" :=
    match: (findNext "n") with
      NONE => "n"
    | SOME "n'" => "tr" "n'"
    end.

Section stack_model.
  Context `{!heapG Σ}.
  Notation iProp := (iProp Σ).

  (* TODO this should be a non-atomic Hoare triple *)
  Lemma findNext_spec (X: gset loc) (x: loc):
    <<< ([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜x ∈ X⌝ >>>
      findNext #x @ ⊤
    <<< ∃ (b: bool) (y: loc), ([∗ set] n ∈ X, ∃ v: val, n ↦ v)
        ∗ ⌜b → y ∈ X⌝,
        RET (match b with true => SOMEV #y | false => NONEV end)
    >>>.
  Proof. Admitted. (* Omitting this proof for clarity *)

  Lemma traverse_spec (X: gset loc) (x: loc):
    ⌜x ∈ X⌝ -∗
    <<< ([∗ set] n ∈ X, ∃ v: val, n ↦ v) >>>
      traverse #x @ ⊤
    <<< ∃ (y: loc), ([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜y ∈ X⌝, RET #y >>>.
  Proof.
    iLöb as "IH" forall (x). iIntros "#Hx". iIntros (Φ) "AU".
    wp_lam. wp_bind (findNext _ )%E. awp_apply (findNext_spec X x).
    iApply (aacc_aupd_abort with "AU"); first done. iIntros "HNs".
    iAssert (([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜x ∈ X⌝)%I with "[$]" as "Haacc".
    iAaccIntro with "Haacc".
    { iIntros "(HNs & _)". iModIntro. eauto with iFrame. }
    iIntros (b y) "(HNs & %)". destruct b.
    - iModIntro. iSplitL. { eauto with iFrame. }
      iIntros "AU". iModIntro. wp_match. iApply "IH"; first by auto.
      iFrame.
    - iModIntro. iSplitL. eauto with iFrame. iIntros "AU".
      iMod "AU" as "[HNs [_ HClose]]". 
      iMod ("HClose" with "[$]") as "HΦ".
      iModIntro. wp_match. done.
  Qed.
