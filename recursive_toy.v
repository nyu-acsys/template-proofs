From iris.heap_lang Require Export lifting notation locations lang.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type*".

Variable findNext : val.

Definition traverse : val :=
  rec: "tr" "n" "v" :=
    match: (findNext "n" "v") with
      NONE => "n"
    | SOME "n'" => "tr" "n'" "v"
    end.

Section stack_model.

  Context `{!heapG Σ}.
  Notation iProp := (iProp Σ).

  Parameter findNext_spec : ∀ (x: loc) (X: gset loc) v,
    (<<< ∀ w, ⌜x ∈ X⌝ ∗ x ↦ #w >>>
         findNext #x #v @ ⊤
     <<< ∃(b:bool) (y:loc), x ↦ #w ∗ match b with true => ⌜#v = #w⌝ |
                                        false => ∃ c, y ↦ c ∗ ⌜y ∈ X⌝ end,
                           RET (match b with true => NONEV |
                                      false => SOMEV #y end) >>>)%I.


  Lemma traverse_spec (x: loc) v (X: gset loc):
    <<< ∀ w, ⌜x ∈ X⌝ ∗ x ↦ #w >>>
              traverse #x #v
                    @ ⊤
         <<< ∃ (y: loc), y ↦ #v ∗ ⌜y ∈ X⌝, RET #y >>>.
  Proof.
    iLöb as "IH" forall (x). iIntros (Φ) "AU".
    wp_lam. wp_let. wp_bind (findNext _ _)%E. awp_apply (findNext_spec x X v).
    iApply (aacc_aupd_abort with "AU"); first done. iIntros (w) "(#Hin & Hx)".
    iAssert (⌜x ∈ X⌝ ∗ x ↦ #w)%I with "[Hx]" as "Haac". eauto with iFrame.
    iAaccIntro with "Haac". eauto with iFrame. 
    iIntros (b y) "(Hx & Hb)". destruct b.
    - admit.
    - iModIntro. iSplitL "Hx". eauto with iFrame. iIntros "AU".
      iModIntro. wp_match. iApply "IH".
  Admitted.