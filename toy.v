From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
Set Default Proof Using "Type*".

Definition lock : val :=
  rec: "lockN" "x" :=
    if: CAS "y" #false #true
    then #()
    else "lockN" "x".

Definition unlock : val :=
  λ: "x",
  "y" <- #false.

Definition prog : val := 
  λ: "x" "v",
  lock "x";;
  "x" <- "v";;
  unlock "x".

Section Toy_Template.
  Context `{!heapG Σ} (N : namespace).
  Notation iProp := (iProp Σ).


  Definition toyN : namespace := N .@ "toy".

  Definition main_inv x y (b: bool) d := (y ↦ #b ∗ if b then True else x ↦ d)%I.

  Definition is_toy y := inv toyN (∃ (b:bool), y ↦ #b)%I.

  Instance main_inv_timeless x y b d: Timeless (main_inv x y b d).
  Proof.
    rewrite /main_inv. repeat apply bi.sep_timeless; try apply _.
    destruct b; try apply _.
  Qed.

  Lemma lock_spec (x y: loc):
        <<< ∀ (b: bool), y ↦ #b >>> 
          lock #x @ ⊤ 
        <<< y ↦ #true ∗ if b then False else True, RET #() >>>.
  Proof.
  Admitted.

  Lemma unlock_spec (x y: loc) :
        <<< y ↦ #true >>>
          unlock #x @ ⊤
        <<< y ↦ #false, RET #() >>>.
  Proof.
  Admitted.
    
  Lemma prog_spec (x y: loc) v:
        is_toy y -∗ <<< ∀ d, x ↦ #d >>>
                      prog #x #v @ ⊤ ∖ ↑N
                      <<< x ↦ #v, RET #() >>>.
  Proof.
    iIntros "HInv". iIntros (Φ) "AU". wp_lam.
    wp_pures. wp_bind (lock _)%E.
    
    (* ---------- If you don't move HInv to persistent context,
             then following awp_apply gives an error ----------- *) 
    iDestruct "HInv" as "#HInv".    
    awp_apply (lock_spec x y).
    (* --------------------------------------------------------- *)
    
    iInv "HInv" as ">H". iDestruct "H" as (b) "Hy".
    iAaccIntro with "Hy". { iIntros. iModIntro.
    iFrame. iNext. iExists b. iFrame. }
    iIntros "(Hy & Hb)". destruct b.
    { iExFalso. done. } iClear "Hb".
    iModIntro. iSplitL "Hy".
    iNext. iExists true. iFrame.
    wp_pures. wp_bind (_ <- _)%E.
    iMod "AU" as (d) "[Hx [_ Hclose]]".
    wp_store. iMod ("Hclose" with "Hx") as "HΦ".
    iModIntro. wp_pures.
    
    (* --------- Need to clear HΦ for the awp_appy ---------- *)
    iClear "HΦ".
    awp_apply (unlock_spec x y).
    (* ------------------------------------------------------ *)
         
    iInv "HInv" as ">H". iDestruct "H" as (b) "Hy".
    destruct b; last admit. 
    iAaccIntro with "Hy". { iIntros "H". iModIntro.
    iSplitL "H". iNext. iExists true. done. done. }
    iIntros "Hy". iModIntro. iSplitL "Hy".
    iNext. iExists false. done.
    (* ------ admit HΦ ------- *)
    admit.
  Admitted. 
  
  
  
  
  
  
  
  
  
  
     
