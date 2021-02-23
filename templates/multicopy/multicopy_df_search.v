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
    iDestruct "Hrnotd" as %Hrnotd.
            
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
    iFrame "#∗". iPureIntro. done.
    iModIntro. wp_lam.

      (* Might need something here *)

    awp_apply lockNode_spec_high; try done.
    iPureIntro. left. done.
    iAaccIntro with ""; try eauto with iFrame.
    iIntros (γ_cn Cr T1)"HnP_n". iModIntro. wp_pures.
    iDestruct "HnP_n" as "(HnP_n & #HRorD)".
    iDestruct "HnP_n" as "(Hnode & #Hγ_s & Hγ_c & Hdecide)".
    wp_apply (inContents_spec with "Hnode").
    iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val.
    wp_pures.
    (** Case analysis on whether k in contents of r **)
    destruct t as [t |]; last first.
    - (* Case 1: k not in r. *)
      wp_pures.
      (** Unlock node r **)
      awp_apply (unlockNode_spec_high with "[] []
      [Hγ_c Hdecide node_n]"); try done. iFrame "∗#".
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. wp_pures.

      awp_apply lockNode_spec_high; try done. iPureIntro.
      right. done. iAaccIntro with ""; try eauto with iFrame.
      iIntros (γ_cn' Cd T2)"HnP_n". iModIntro. wp_pures.
      iDestruct "HnP_n" as "(HnP_n & #HRorD')".
      iDestruct "HnP_n" as "(Hnode' & #Hγ_s' & Hγ_c' & Hdecide')".

      iAssert (⌜γ_cn = γ_cr⌝)%I as "%".
      {
        iDestruct "HRorD" as %HRorD.
        destruct HRorD; destruct H0; iPureIntro; done.
      } subst γ_cn.

      iAssert (⌜γ_cn' = γ_cd⌝)%I as "%".
      {
        iDestruct "HRorD'" as %HRorD'.
        destruct HRorD'; destruct H0; iPureIntro; done.
      } subst γ_cn'.

      wp_apply (inContents_spec with "Hnode'").
      iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val'.
      wp_pures.
      destruct t as [t | ]; last first.
      (** Case analysis on whether k is in the contents of d. **)
      + (** Case 1.a : k not in datastructure. **)
        wp_pures.
        (* Reopen the invariant. *)
        iApply fupd_wp.
        iInv "HInv" as (T_1a H_1a)"(mcs_high & >Inv_DF)". 
        iDestruct "Inv_DF" as (Cr_1a Cd_1a)"(Ho & Hstar)".
        iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
        iDestruct "Hstar" as "(Hrnotd & #Hcir_1a & Hset & Hlockbr
            & Hycr & Hlockbd & Hycd)".
        
        iAssert (⌜(k,0) ∈ H_1a⌝)%I as "%".
          { iDestruct "Hist" as %Hist. iPureIntro.
            by pose proof Hist k k_in_KS as Hist. }

        iAssert (⌜Cd = Cd_1a⌝)%I as "%".
        {
          iPoseProof (own_valid_2 _ _ _ with "[$Hycd] [$Hγ_c']") as "#HCr_equiv".
          iDestruct "HCr_equiv" as %HCr_equiv.
          apply frac_agree_op_valid in HCr_equiv.
          destruct HCr_equiv as [_ HCr_equiv].
          apply leibniz_equiv_iff in HCr_equiv.
          iPureIntro. done.
        } subst Cd_1a.

        iAssert (⌜(map_of_set H_1a) !!! k = 0⌝)%I as %Hk_eq_0.
        {

          iDestruct "Hist" as %Hist.
          unfold init in Hist.
          specialize (Hist k).
          apply Hist in k_in_KS as k0_in_H1.
          admit.
        }
        iAssert (⌜t0 ≤ (map_of_set H_1a) !!! k⌝)%I as %lb_t0.
        {

          iDestruct "Hcir_1a" as %Hcir_1a.
          unfold cir in Hcir_1a.
          specialize (Hcir_1a k t0).
          destruct Hcir_1a.
          admit.
        }
        iAssert (⌜t0 = 0⌝)%I as %t0_zero.
        { 
          iPureIntro. admit. 
        } subst t0.
        (** Unlock node d **)
        awp_apply (unlockNode_spec_high with "[] []
        [Hγ_c' Hdecide' node_n]"); try done. iFrame "∗#".
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_".

        iMod "AU" as "[_ [_ Hclose]]".
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
        iModIntro. wp_pures. iFrame. done.
      + (** Case 1.b : k is not in r, but is in d. **)
        wp_pures.
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
        iAssert (⌜t0 = t⌝)%I as %t0_eq_t.
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
        iModIntro. subst t. done.

  - (* Case 2: k is in the root node. *)
      wp_pures.
      awp_apply (unlockNode_spec_high with "[] [] [Hγ_c Hdecide node_n]"); try done.
      iFrame. iFrame "#".
      iAaccIntro with ""; try done.
      { eauto with iFrame. }
      iMod "AU" as "[_ [_ Hclose]]".
      iSpecialize ("Hclose" $! t0).
      iAssert (⌜t0 = t⌝)%I as %t0_eq_t.
      {admit. }
      iMod ("Hclose" with "[]") as "HΦ".
      iFrame "mcs_sr". by iPureIntro.
      iIntros "_".
      iModIntro. wp_pures. subst t. done.

  Qed.