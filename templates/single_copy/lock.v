(** Implementation of lock module (shared between all templates) *)

From iris.heap_lang Require Export notation locations lang.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode par.
Set Default Proof Using "All".
Require Export flows.

Section Lock_module.

  Context `{!heapG Σ}.

  (** Assumed functions to retrieve lock bit from a node *)
  Parameter lockLoc : Node → loc.
  Parameter getLockLoc : val.

  Parameter getLockLoc_spec : ∀ (n: Node),
    ⊢ ({{{ True }}}
        getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.
  
  (* Lock node x *)
  Definition lockNode : val :=
    rec: "lockN" "x" :=
      let: "l" := getLockLoc "x" in
      if: CAS "l" #false #true
      then #()
      else "lockN" "x".

  (* Unlock node x *)
  Definition unlockNode : val :=
    λ: "x",
    let: "l" := getLockLoc "x" in
    "l" <- #false.
    
  (** Lock module proofs *)

  Definition lockR (b: bool) (n: Node) (R: iProp Σ) : iProp Σ :=
    ((lockLoc n) ↦ #b ∗ (if b then True else R))%I.
  
  Lemma lockNode_spec (n: Node) (R: iProp Σ):
    ⊢ <<< ∀ b, lockR b n R >>>
      lockNode #n    @ ⊤
    <<< lockR true n R ∗ R, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind(getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "#Hl". wp_let. wp_bind (CmpXchg _ _ _)%E.
    iMod "AU" as (b) "[Hb HAU]". iDestruct "Hl" as %Hl.
    unfold lockR.
    iEval (rewrite Hl) in "Hb". destruct b.
    - iDestruct "Hb" as "[Hb Htrue]".
      wp_cmpxchg_fail. iDestruct "HAU" as "[HAU _]".
      iEval (rewrite Hl) in "HAU".
      iMod ("HAU" with "[$Hb $Htrue]") as "H".
      iModIntro. wp_pures. iApply "IH".
      iEval (rewrite <-Hl) in "H". done.
    - iDestruct "Hb" as "[Hb HR]".
      wp_cmpxchg_suc. iDestruct "HAU" as "[_ HAU]".
      iEval (rewrite Hl) in "HAU".
      iMod ("HAU" with "[Hb HR]") as "HΦ". iFrame; done.
      iModIntro. wp_pures. done.
  Qed.

  Lemma unlockNode_spec (n: Node) :
    ⊢ <<< lockLoc n ↦ #true >>>
      unlockNode #n    @ ⊤
    <<< lockLoc n ↦ #false, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". wp_lam. wp_bind(getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "#Hl". wp_let.
    iMod "AU" as "[Hy [_ Hclose]]".
    iDestruct "Hl" as %Hl.
    iEval (rewrite Hl) in "Hy".
    wp_store. iEval (rewrite Hl) in "Hclose".
    iMod ("Hclose" with "Hy") as "HΦ".
    iModIntro. done.
  Qed.
  
End Lock_module.  
