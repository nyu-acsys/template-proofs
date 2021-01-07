From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Import general_multicopy util general_multicopy_upsert.

Section upsert_proof_high.
  Context {Σ} `{!heapG Σ, !multicopyG Σ}.
  Notation iProp := (iProp Σ).  
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).
  
  Lemma ghost_update_registered (k: K) (T: nat) (N: namespace) 
                (γ_te γ_he γ_ght: gname) 
                (H1: gset KT) (TD: gset proph_id)  :
        ⌜map_of_set (H1 ∪ {[k, T]}) !!! k = T⌝ -∗
           MCS_auth γ_te γ_he (T+1) (H1 ∪ {[(k, T)]}) -∗          
      ([∗ set] t_id ∈ TD, registered N γ_te γ_he γ_ght H1 t_id) 
        ={⊤ ∖ ↑(mcsN N) ∖ ↑(helpN N)}=∗ 
      ([∗ set] t_id ∈ TD, registered N γ_te γ_he γ_ght 
                                      (H1 ∪ {[(k, T)]}) t_id)
       ∗ MCS_auth γ_te γ_he (T+1) (H1 ∪ {[(k, T)]}).
  Proof.
    iIntros "H1_k MCS_auth".
    iDestruct "H1_k" as %H1_k.
    iInduction TD as [|x TD' x_notin_TD IH] "HInd" using set_ind_L; 
      auto using big_sepS_empty'.
    rewrite (big_sepS_delete _ ({[x]} ∪ TD') x); last by set_solver.
    rewrite (big_sepS_delete _ ({[x]} ∪ TD') x); last by set_solver.
    assert (({[x]} ∪ TD') ∖ {[x]} = TD') as HTD'. set_solver.
    rewrite HTD'.
    iIntros "(Hx & Hbigstar)". 
    iMod ("HInd" with "[$MCS_auth] Hbigstar") as "(H' & MCS_auth)".
    iFrame "H'".
    iDestruct "Hx" as (P Q k' vp vt γ_tk γ_sy)
              "(Hreg_proph & Hreg_gh & Hreg_sy & #Pau & #Hthinv)".
    iInv "Hthinv" as (H1')"Hstate".
    iDestruct "Hstate" as "(>Hth_sy & Hstate)".
    iAssert (⌜H1' = H1⌝)%I as "%". 
    { iPoseProof (own_valid_2 _ _ _ with "[$Hth_sy] [$Hreg_sy]") as "V_H".
      iDestruct "V_H" as %V_H.
      apply frac_agree_op_valid in V_H. destruct V_H as [_ V_H].
      apply leibniz_equiv_iff in V_H.
      by iPureIntro. } subst H1'.
    
    iCombine "Hreg_sy Hth_sy" as "H'". 
    iEval (rewrite <-frac_agree_op) in "H'". 
    iEval (rewrite Qp_half_half) in "H'".
    iMod ((own_update (γ_sy) (to_frac_agree 1 H1) 
                  (to_frac_agree 1 (H1 ∪ {[(k, T)]}))) with "[$H']") as "H'".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "H'".
    iEval (rewrite frac_agree_op) in "H'".  
    iDestruct "H'" as "(Hreg_sy & Hth_sy)".            

    iDestruct "Hstate" as "[Hpending | Hdone]".
    - iDestruct "Hpending" as "(P & >%)".
      rename H into vp_notin_H.
      destruct (decide ((k', vp) ∈ H1 ∪ {[(k, T)]})).
      + assert ((k',vp) = (k,T)) as H'. 
        { clear -vp_notin_H e. set_solver. }
        inversion H'. subst k' vp.
        iDestruct ("Pau" with "P") as ">AU".
        iMod "AU" as (t H1')"[MCS [_ Hclose]]". set_solver.
        iAssert (⌜H1' = H1 ∪ {[(k, T)]}⌝)%I as "%".
        { iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
          unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
          by iDestruct "MCS" as "(_ & H')". by iPureIntro. } subst H1'.
        iMod ("Hclose" with "[MCS]") as "HQ".
        { iFrame "%∗". }
        iModIntro. iSplitL "Hth_sy HQ".
        iNext. iExists (H1 ∪ {[(k, T)]}). iFrame.
        iRight. iSplitL. iLeft. done.
        iPureIntro. clear; set_solver.
        iModIntro. iFrame.
        iExists P, Q, k, T, vt, γ_tk, γ_sy.
        iFrame "∗#".
      + iModIntro. iSplitR "Hreg_proph Hreg_sy Hreg_gh MCS_auth".
        iNext. iExists (H1 ∪ {[(k, T)]}). iFrame.
        iLeft. iFrame. by iPureIntro.
        iModIntro. iFrame.             
        iExists P, Q, k', vp, vt, γ_tk, γ_sy.
        iFrame "∗#".
    - iModIntro.
      iSplitR "Hreg_proph Hreg_sy Hreg_gh MCS_auth".
      iNext. iExists (H1 ∪ {[(k, T)]}). iFrame.
      iRight. iDestruct "Hdone" as "(HQ & %)".
      iFrame "HQ". iPureIntro. set_solver.
      iModIntro. iFrame. 
      iExists P, Q, k', vp, vt, γ_tk, γ_sy.
      iFrame "∗#". 
  Qed.  
      
  Lemma upsert_spec_high N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                         lc r γ_td γ_ght (k: K) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
            <<< ∀ t M, MCS_high N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                      lc r γ_td γ_ght t M >>> 
                   upsert lc r #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N))
            <<< MCS_high N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                      lc r γ_td γ_ght (t + 1) (<[k := t]> M), RET #() >>>.
  Proof.
    iIntros "%" (Φ) "AU". rename H into k_in_KS.
    iApply fupd_wp. 
    iMod "AU" as (t' M')"[H [Hab _]]".
    iDestruct "H" as (H')"(MCS & M_eq_H & #HInv & #HInv_h)".
    iMod ("Hab" with "[MCS M_eq_H]") as "AU".
    iExists H'. iFrame "∗#". iModIntro.
    iAssert (ghost_update_protocol N γ_te γ_he 
                (protocol_conc N γ_te γ_he γ_fr γ_td γ_ght) k)%I 
                  as "Ghost_updP".
    { iIntros (H1 T)"H1_k MCS_auth".
      iDestruct "H1_k" as %H1_k.
      iIntros "Protocol_conc". 
      iDestruct "Protocol_conc" as (TD hγt)"(HTD & Hγt & Domm_hγt & Hstar_reg)".
      iMod (ghost_update_registered k T with 
              "[] [MCS_auth] [$Hstar_reg]") 
                 as "(Hstar_reg & MCS_auth)"; try done.
      iModIntro. iFrame "MCS_auth".
      iExists TD, hγt. iFrame. }
    awp_apply upsert_spec; try done.
    iApply (aacc_aupd_commit with "AU"). set_solver.
    iIntros (t M)"MCS_high".
    iDestruct "MCS_high" as (H)"(MCS & M_eq_H & _)".
    iDestruct "M_eq_H" as %M_eq_H.
    iAaccIntro with "MCS".
    { iIntros "MCS". iModIntro.
      iSplitL; try eauto with iFrame.
      iExists H; iFrame "∗#%". } 
    iIntros "(MCS & %)". rename H0 into maxTS.
    iModIntro. iSplitL.
    iExists (H ∪ {[k, t]}). iFrame "∗#".
    { iPureIntro. apply symmetry. 
      apply map_of_set_insert_eq; try done.
      apply maxTS. }
    iIntros "HΦ"; iModIntro; try done.
  Qed.


End upsert_proof_high.