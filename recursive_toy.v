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

  Lemma findNext_spec (X: gset loc) (x: loc):
    <<< ([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜x ∈ X⌝ >>>
      findNext #x @ ⊤
    <<< ∃ (b: bool) (y: loc), ([∗ set] n ∈ X, ∃ v: val, n ↦ v)
        ∗ ⌜b → y ∈ X⌝,
        RET (match b with true => SOMEV #y | false => NONEV end)
    >>>.
  Proof. Admitted. (* Omitting this proof for clarity *)

  Lemma traverse_spec (X: gset loc) (x: loc):
    <<< ([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜x ∈ X⌝ >>>
      traverse #x @ ⊤
    <<< ∃ (y: loc), ([∗ set] n ∈ X, ∃ v: val, n ↦ v) ∗ ⌜y ∈ X⌝, RET #y >>>.
  Proof.
    iLöb as "IH" forall (x). iIntros (Φ) "AU".
    wp_lam. wp_bind (findNext _ )%E. awp_apply (findNext_spec X x).
    iApply (aacc_aupd_abort with "AU"); first done. iIntros "(HNs & #Hin)".
    (* Sid: can you update the proof from here on? *)
    iAssert (⌜x ∈ X⌝ ∗ x ↦ #w)%I with "[Hx]" as "Haac". eauto with iFrame.
    iAaccIntro with "Haac". eauto with iFrame. 
    iIntros (b y) "(Hx & Hb)". destruct b.
    - admit.
      (* Sid: we know how to prove the b == true case right? If so, add a 
        comment saying so. *)
    - iModIntro. iSplitL "Hx". eauto with iFrame. iIntros "AU".
      iModIntro. wp_match. iApply "IH".
  Admitted.