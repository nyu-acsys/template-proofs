(* Herlihy Skiplist with a single level : Search *)

From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Export skiplist_v0 skiplist_v0_search.

Section skiplist_v0_delete.
  Context {Σ} `{!heapGS Σ, !skG Σ}.
  Notation iProp := (iProp Σ).
  
  Lemma delete_spec N γ_s γ_t γ_m γ_td γ_ght r t_id (k: K) :
    ⌜k ∈ KS⌝ -∗
      searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r -∗
        thread_id γ_t γ_ght t_id -∗
          <<< ∀ C, SearchStr γ_s C >>>
            delete r #k @ ⊤ ∖ (↑(sstrN N))
          <<< ∃ (res: bool) (C': gset K), 
                SearchStr γ_s C' 
              ∗ ⌜Ψ deleteOp k C C' res⌝, 
                RET #res >>>.
  Proof.
    iIntros "%k_in_KS #HInv #Htid" (Φ) "AU".
    wp_lam. awp_apply traverse_spec; try eauto with iFrame.
    iApply (aacc_aupd_abort with "AU"). admit.
    iIntros (C0) "SStr". iAaccIntro with ""; try done.
    { iIntros "_". iModIntro. iFrame. 
      iIntros "AU"; iFrame. try done. }
    iIntros (p c s) "(Past & %FP_p & %FP_c & %Unmarked_p & 
      %k_in_insetp & %k_in_p2c & %Unmarked_c & %k_in_keysetc)".
    iModIntro. iFrame "SStr". iIntros "AU".
    iModIntro. wp_pures.    

      
  Admitted.    
  
  
  
  
  
End skiplist_v0_delete.