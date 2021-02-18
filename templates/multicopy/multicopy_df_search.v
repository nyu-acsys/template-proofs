From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy_df.

Section multicopy_df_search.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_dfG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).
  
  Lemma search_recency N γ_te γ_he γ_s Prot 
                       γ_t γ_cr γ_cd γ_d lc r d (k: K) t0 :
    ⊢ ⌜k ∈ KS⌝ -∗ 
        mcs_inv N γ_te γ_he γ_s Prot
           (Inv_DF γ_s γ_t γ_cr γ_cd γ_d lc r d) -∗
          SR γ_s (k, t0) -∗
              <<< True >>> 
                  search r d #k @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ (t': nat), SR γ_s (k, t') ∗ ⌜t0 ≤ t'⌝ , RET #t' >>>.
  Proof.
    iIntros "% #HInv #mcs_sr" (Φ) "AU".
    rename H into k_in_KS. 
    iApply fupd_wp. 
    iInv "HInv" as (T H)"(mcs_high & >Inv_DF)".
    iDestruct "Inv_DF" as (Cr' Cd')"(Ho & Hstar)".
    iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
    iDestruct "Hstar" as "(Hrnotd & #Hcir & Hset & Hlockbr 
            & Hycr & Hlockbd & Hycd)".
    rewrite (big_sepS_delete _ (KS) k); last by eauto.
    iDestruct "Hset" as "(HnS_stark & HnS_star')".
    iMod (own_update (γ_d !!! k) (● MaxNat (Cd' !!! k)) 
          (● (MaxNat (Cd' !!! k)) ⋅ ◯ (MaxNat (Cd' !!! k))) 
            with "[$HnS_stark]") as "HnS_stark".
    { apply (auth_update_frac_alloc); try done.
      unfold CoreId, pcore, cmra_pcore. simpl.
      unfold ucmra_pcore. simpl. by unfold max_nat_pcore. }
    iDestruct "HnS_stark" as "(HnS_stark & mcs_sr')".
    iAssert (⌜(k,t0) ∈ H⌝)%I as %kt0_in_H.
    { iPoseProof (own_valid_2 _ _ _ with "[$HH] [$mcs_sr]") as "H'".
      iDestruct "H'" as %H'.
      apply auth_both_valid_discrete in H'.
      destruct H' as [H' _].
      apply gset_included in H'.
      iPureIntro; clear -H'; set_solver. }

    iModIntro. iSplitR "AU". iNext.
    iExists T, H. iFrame. iFrame "#".
    iExists Cr', Cd'. iFrame. iFrame "#".
    rewrite (big_sepS_delete _ (KS) k); last by eauto.
    iFrame "#∗". iModIntro. wp_lam.

      (* Might need something here *)

    awp_apply lockNode_spec_high; try done.
    iPureIntro. left. done. 
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (γ_cn Cn T1)"HnP_n". iModIntro. wp_pures. 
    iDestruct "HnP_n" as "(HnP_n & #HRorD)".
    iDestruct "HnP_n" as "(Hnode & #Hγ_s & Hγ_c & Hdecide)".
    wp_apply (inContents_spec with "Hnode").
    iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val.
    wp_pures.
    (** Case analysis on whether k in contents of n **)
    destruct t as [t |]; last first.
    - (** Case : k not in contents of n **)
    wp_pures.
    +  (* k is not in the data structure. *)
      wp_pures.
      (** Unlock node n **)
      awp_apply (unlockNode_spec_high with "[] []
      [Hγ_c Hdecide node_n]"); try done. iFrame "∗#".
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. wp_pures.

      awp_apply lockNode_spec_high; try done. iPureIntro.
      right. done. iAaccIntro with ""; try eauto with iFrame.
      iIntros (γ_cn' Cr T2)"HnP_n". iModIntro. wp_pures. 
      iDestruct "HnP_n" as "(HnP_n & #HRorD')".
      iDestruct "HnP_n" as "(Hnode' & #Hγ_s' & Hγ_c' & Hdecide')".

      wp_apply (inContents_spec with "Hnode'").
      iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val'.
      wp_pures.
      destruct t as [t |]; last first. wp_pures.

      (** Unlock node n **)       
      awp_apply (unlockNode_spec_high with "[] [] 
      [Hγ_c' Hdecide' node_n]"); try done. iFrame "∗#". 
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". 

    iAssert (⌜t0 = 0⌝)%I as %t0_zero. 
      { iPureIntro. admit. } subst t0.
    iMod "AU" as "[_ [_ Hclose]]". 
    iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)". {admit. }
    iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
    iAssert (⌜(k,0) ∈ H'⌝)%I as "%".
      { iDestruct "Hist" as %Hist. iPureIntro.
        by pose proof Hist k k_in_KS as Hist. }
    iSpecialize ("Hclose" $! 0).
    iMod (own_update γ_s (● H') (● H' ⋅ ◯ {[(k,0)]}) with "[$HH]") as "HH".
        { apply (auth_update_frac_alloc _ H' ({[(k,0)]})).
          apply gset_included. set_solver. }
    iDestruct "HH" as "(HH & #mcs_sr'')".
    iModIntro. 
    iSplitR "HInv Hclose". iNext. 
    iExists T', H'. iFrame. 
    iMod ("Hclose" with "[]") as "HΦ". iFrame "mcs_sr''". by iPureIntro. 
    (** Closing the invariant **)
    iModIntro. wp_pures. iFrame. wp_pures.
    awp_apply (unlockNode_spec_high with "[] [] [Hγ_c' Hdecide' node_n]"); try  done.
    iFrame. iFrame "#".
    iAaccIntro with ""; try done.
    { eauto with iFrame. } iIntros "_".
    iMod "AU" as "[_ [_ Hclose]]".
    iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)". {admit. }
    iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
    iAssert (⌜(k,0) ∈ H'⌝)%I as "%".
    { iDestruct "Hist" as %Hist. iPureIntro.
      by pose proof Hist k k_in_KS as Hist. }
    iAssert (⌜t0 ≤ t⌝)%I as %t0_lt_t.
      {admit. } 
    iSpecialize ("Hclose" $! t0).
    iMod (own_update γ_s (● H') (● H' ⋅ ◯ {[(k,0)]}) with "[$HH]") as "HH".
        { apply (auth_update_frac_alloc _ H' ({[(k,0)]})).
          apply gset_included. set_solver. }
    iDestruct "HH" as "(HH & mcs_sr'')". iModIntro.
    iSplitR "HInv Hclose". iNext. 
    iExists T', H'. iFrame. 
    iMod ("Hclose" with "[]") as "HΦ".
    iFrame "mcs_sr". by iPureIntro. 
    iModIntro. wp_pures. 
    { admit. }

  - (* Case 2: k is in the root node. *)  
      wp_pures.
      awp_apply (unlockNode_spec_high with "[] [] [Hγ_c Hdecide node_n]"); try done.
      iFrame. iFrame "#".
      iAaccIntro with ""; try done.
      { eauto with iFrame. }
      iMod "AU" as "[_ [_ Hclose]]".
      iSpecialize ("Hclose" $! t0).
      iMod ("Hclose" with "[]") as "HΦ".
      iAssert (⌜t0 ≤ t⌝)%I as %t0_lt_t.
      {admit. } 
      iFrame "mcs_sr". by iPureIntro.
      iIntros "_". 
      iModIntro. wp_pures. 
      {admit. }
  
  Qed.