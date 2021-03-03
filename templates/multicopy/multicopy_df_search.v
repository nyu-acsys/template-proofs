
From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy_df multicopy_util auth_ext.

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
    wp_lam.

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

      (* Open the invariant. *)
      iApply fupd_wp.
      iInv "HInv" as (T H)"(mcs_high & >Inv_DF)".
      iDestruct "Inv_DF" as (Cr' Cd)"(Ho & Hstar)".
      iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
      iDestruct "Hstar" as "(Hrnotd & #Hcir & Hset & Hlockbr
          & Hycr & Hlockbd & Hycd)".
      rewrite (big_sepS_delete _ (KS) k); last by eauto.
      iDestruct "Hset" as "(HnS_stark & HnS_star')".
     iAssert (⌜Cr = Cr'⌝)%I as %Cr_eq_Cr'.
        { admit. } subst Cr'.
      iAssert (⌜map_of_set H !! k = Cd !! k⌝)%I as %MapCd.
        { iDestruct "Hcir" as %Hcir.
          pose proof Hcir k as [_ H'].
          iPureIntro. pose proof H' Cn_val as H'.
          by rewrite H'. }
      iAssert (⌜(k,t0) ∈ H⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HH] [$mcs_sr]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro; clear -H'; set_solver. }
      iAssert (⌜(k,t0) ∈ H → t0 ≤ map_of_set H !!! k⌝)%I as "%".
      {
        iPureIntro. by apply map_of_set_lookup_lb.
      }
      iAssert (⌜t0 ≤ map_of_set H !!! k⌝)%I as "%".
      {
        iPureIntro. pose proof H1 H0 as H1. done.
      }
      iAssert (⌜t0 ≤ Cd !!! k⌝)%I as "%".
      {
        iPureIntro. unfold lookup_total. 
        unfold finmap_lookup_total.
        rewrite /(Cd !!! k) in MapCd.
        unfold finmap_lookup_total, inhabitant in MapCd.
        simpl in MapCd.
        destruct (Cd !! k) as [cnk | ] eqn: Hcnk.
        - try done. 
          by inversion MapCd. 
        - try done. by inversion MapCd.
      }
      iMod (own_update (γ_d !!! k) (● MaxNat (Cd !!! k))
          (● (MaxNat (Cd !!! k)) ⋅ ◯ (MaxNat (Cd !!! k)))
            with "[$HnS_stark]") as "HnS_stark".
    { apply (auth_update_frac_alloc); try done.
      unfold CoreId, pcore, cmra_pcore. simpl.
      unfold ucmra_pcore. simpl. by unfold max_nat_pcore. }
    iDestruct "HnS_stark" as "(HnS_stark & #mcs_sr')".

    iModIntro. iSplitR "AU". iNext.
    iExists T, H. iFrame. iFrame "#".
    iExists Cr, Cd. iFrame. iFrame "#".
    rewrite (big_sepS_delete _ (KS) k); last by eauto.
    iFrame "#∗". iModIntro.

      awp_apply lockNode_spec_high; try done. iPureIntro.
      right. done. iAaccIntro with ""; try eauto with iFrame.
      iIntros (γ_cd' Cd'' T2)"HnP_n". iModIntro. wp_pures.
      iDestruct "HnP_n" as "(HnP_n & #HRorD')".
      iDestruct "HnP_n" as "(Hnode' & #Hγ_s' & Hγ_c' & Hdecide')".

      wp_apply (inContents_spec with "Hnode'").
      iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val'.
      wp_pures.
      destruct t as [t |]; last first.
      (** Case analysis on whether k is in the contents of d. **)
      + (** Case 1.a : k not in datastructure. **)
        wp_pures.

        (* Reopen the invariant. *)
        iApply fupd_wp.
        iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)".
        iDestruct "Inv_DF" as (Cr1 Cd1)"(Ho & Hstar)".
        iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
        iDestruct "Hstar" as "(Hrnotd & #Hcir' & Hset & Hlockbr
            & Hycr & Hlockbd & Hycd)".
        
        iAssert(⌜γ_cd' = γ_cd⌝)%I as "%".
        {
          iDestruct "HRorD'" as %HRorD'.
          iDestruct "Hrnotd" as %Hrnotd.
          destruct HRorD' as [temp | temp];
          destruct temp; iPureIntro; try done.
        } subst γ_cd'.

          iAssert (⌜Cd'' = Cd1⌝)%I as %Cd'_eq_Cd1.
            { 
              iPoseProof (own_valid_2 _ _ _ with "[$Hycd] [$Hγ_c']") as "#HCr_equiv".
              iDestruct "HCr_equiv" as %HCr_equiv.
              apply frac_agree_op_valid in HCr_equiv.
              destruct HCr_equiv as [_ HCr_equiv].
              apply leibniz_equiv_iff in HCr_equiv.
              iPureIntro. done.
            } subst Cd''.
    
            iAssert (⌜map_of_set H' !! k = Cd1 !! k⌝)%I as %MapCdH'.
            { iDestruct "Hcir'" as %Hcir'.
              pose proof Hcir' k as [_ H''].
              iPureIntro. admit. }

            iAssert (⌜(map_of_set H') !! k = None⌝)%I as %H'_eq_None.
            {
              iDestruct "Hist" as %Hist.
              unfold init in Hist.
              specialize (Hist k).
              apply Hist in k_in_KS as k0_in_H1.
              iPureIntro.
              rewrite -> MapCdH'.
              done.
            }
            iAssert (⌜(map_of_set H') !!! k = 0⌝)%I as %H'_eq_0.
            {
              iPureIntro.
              unfold lookup_total. unfold finmap_lookup_total.
              rewrite -> H'_eq_None. done. }

            iAssert (⌜(k,t0) ∈ H'⌝)%I as %kt0_in_H'.
            { 
              iPoseProof (own_valid_2 _ _ _ with "[$HH] [$mcs_sr]") as "H'".
              iDestruct "H'" as %H''.
              apply auth_both_valid_discrete in H''.
              destruct H'' as [H'' _].
              apply gset_included in H''.
              iPureIntro; clear -H''; set_solver. 
            }
            iAssert (⌜t0 ≤ (map_of_set H') !!! k⌝)%I as %lb_t0.
            {
              iDestruct "Hcir'" as %Hcir_1a.
              unfold cir in Hcir_1a.
              specialize (Hcir_1a k t0).
              destruct Hcir_1a.
              pose proof map_of_set_lookup_lb as H_lb.
              specialize H_lb with H' k t0.
              apply H_lb in kt0_in_H'.
              iPureIntro.
              done.
            }
            iAssert (⌜t0 = 0⌝)%I as %t0_zero.
            { iPureIntro. lia.
            }  subst t0.

        iMod (own_update γ_s (● H') (● H' ⋅ ◯ {[(k,0)]}) with "[$HH]") as "HH".
          { apply (auth_update_frac_alloc _ H' ({[(k,0)]})).
            apply gset_included. set_solver. }
        iDestruct "HH" as "(HH & #mcs_sr'')".
        iModIntro. iSplitR "HInv AU Hγ_c' Hdecide' node_n". iNext.
        iExists T', H'. iFrame.
        iExists Cr1, Cd1. iFrame. iFrame "Hcir'".

        (** Unlock node d **)
        iModIntro. wp_pures.
        awp_apply (unlockNode_spec_high with "[] []
        [Hγ_c' Hdecide' node_n]"); try done. iFrame "∗#".
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_".

        iMod "AU" as "[_ [_ Hclose]]".
        iSpecialize ("Hclose" $! 0).
        iMod ("Hclose" with "[]") as "HΦ". iFrame "mcs_sr''".
        by iPureIntro.

        (** Closing the invariant **)
        iModIntro. wp_pures. iFrame. 

      + (** Case 1.b : k is not in r, but is in d. **)
        wp_pures.

        (* Reopen the invariant. *)
        iApply fupd_wp.
        iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)".
        iDestruct "Inv_DF" as (Cr' Cd')"(Ho & Hstar)".
        iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
        iDestruct "Hstar" as "(Hrnotd & #Hcir' & Hset & Hlockbr
            & Hycr & Hlockbd & Hycd)".
        rewrite (big_sepS_delete _ (KS) k); last by eauto.
        iDestruct "Hset" as "(HnS_stark & HnS_star')".

        iAssert(⌜γ_cd' = γ_cd⌝)%I as "%".
        {
          iDestruct "HRorD'" as %HRorD'.
          iDestruct "Hrnotd" as %Hrnotd.
          destruct HRorD' as [temp | temp];
          destruct temp; iPureIntro; try done.
        } subst γ_cd'.

        iAssert (⌜Cd' = Cd''⌝)%I as %Cd'_eq_Cd''.
        { 
          iPoseProof (own_valid_2 _ _ _ with "[$Hycd] [$Hγ_c']") as "#HCr_equiv".
          iDestruct "HCr_equiv" as %HCr_equiv.
          apply frac_agree_op_valid in HCr_equiv.
          destruct HCr_equiv as [_ HCr_equiv].
          apply leibniz_equiv_iff in HCr_equiv.
          iPureIntro. done.
        } subst Cd''.
     
        iAssert (⌜set_of_map Cd' ⊆ H'⌝)%I as %Cd_Sub_H.
          { iPoseProof ((auth_own_incl γ_s H' _) with "[$HH $Hγ_s']") as "%".
          rename H0 into H''. by apply gset_included in H4. }  

        iAssert (⌜(k,t) ∈ set_of_map Cd'⌝)%I as %kt_in_Cd.
         { iPureIntro. apply set_of_map_member.
              rewrite /(Cd !!! k) in Cn_val.
              unfold finmap_lookup_total, inhabitant in Cn_val.
              simpl in Cn_val. 
              destruct (Cd !! k) as [cnk | ] eqn: Hcnk.
              - try done.
              - try done.  }
  
        iAssert (⌜(k,t) ∈ H'⌝)%I as "%".
          { iPureIntro. set_solver. }
            
        iMod (own_update (γ_d !!! k) (● MaxNat (Cd' !!! k))
          (● (MaxNat (Cd' !!! k)) ⋅ ◯ (MaxNat (Cd' !!! k)))
              with "[$HnS_stark]") as "HnS_stark".
        { apply (auth_update_frac_alloc); try done.
          unfold CoreId, pcore, cmra_pcore. simpl.
          unfold ucmra_pcore. simpl. by unfold max_nat_pcore. }
        iDestruct "HnS_stark" as "(HnS_stark & mcs_sr'')".

        iAssert (⌜(Cd !!! k) ≤ (Cd' !!! k)⌝)%I as "%".
        { iPoseProof (own_valid_2 _ _ _ with "[$HnS_stark]  [$mcs_sr']") as "H'".
        iDestruct "H'" as %H''.
        apply auth_both_valid_discrete in H''.
        destruct H'' as [H'' _].
        apply max_nat_included in H''.
        simpl in H''.
        by iPureIntro. }
    
        (* Need Help Here *)
        iAssert (⌜Cd' !!! k = t⌝)%I as "%". 
        { iPureIntro. 
          unfold lookup_total. 
          unfold finmap_lookup_total. 
          (*rewrite -> Cn_val'.
           done.*)
        admit. }  
        
        iAssert (⌜t0 ≤ (Cd' !!! k)⌝)%I as %t0_leq_Cd.
         {iPureIntro. rewrite <-H3 in H5. done. }

         (* Need Help Here *)
        iAssert (⌜t0 = t⌝)%I as %t0_eq_t.
         {iPureIntro.
         (* lia. *)
          admit. }

        iMod (own_update γ_s (● H') (● H' ⋅ ◯ {[(k,t)]}) with "[$HH]") as "HH".
            { apply (auth_update_frac_alloc _ H' ({[(k,t)]})).
              apply gset_included. clear -kt_in_Cd Cd_Sub_H. set_solver. }
        iDestruct "HH" as "(HH & #mcs_sr1)".
        iModIntro. iSplitR "HInv AU Hγ_c' Hdecide' node_n". iNext.
        iExists T', H'. iFrame.
        iExists Cr', Cd'. iFrame. iFrame "Hcir'".
        rewrite (big_sepS_delete _ (KS) k); last by eauto. iFrame. 

        iModIntro. wp_pures.
        awp_apply (unlockNode_spec_high with "[] [] [Hγ_c' Hdecide' node_n]"); try  done.
        iFrame. iFrame "#".
        iAaccIntro with ""; try done.
        { eauto with iFrame. } iIntros "_".
        iMod "AU" as "[_ [_ Hclose]]".
        iSpecialize ("Hclose" $! t0).
        iMod ("Hclose" with "[]") as "HΦ".
        iFrame "mcs_sr". by iPureIntro.
        iModIntro. wp_pures.
        subst t0.
        done.

  - (* Case 2: k is in the root node. *)
      wp_pures.

      (* Reopen the invariant. *)
      iApply fupd_wp.
      iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)".
      iDestruct "Inv_DF" as (Cr' Cd')"(Ho & Hstar)".
      iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
      iDestruct "Hstar" as "(Hrnotd & #Hcir' & Hset & Hlockbr
          & Hycr & Hlockbd & Hycd)".
      rewrite (big_sepS_delete _ (KS) k); last by eauto.
      iDestruct "Hset" as "(HnS_stark & HnS_star')".

      iAssert(⌜γ_cn = γ_cr⌝)%I as "%".
      {
        iDestruct "HRorD" as %HRorD.
        iDestruct "Hrnotd" as %HRnotD.
        destruct HRorD as [temp | temp];
        destruct temp; iPureIntro; try done.
      } subst γ_cr.
     iAssert (⌜Cr = Cr'⌝)%I as %Cr_eq_Cr'.
      { iPoseProof (own_valid_2 _ _ _ with "[$Hycr] [$Hγ_c]") as "#HCr_equiv".
      iDestruct "HCr_equiv" as %HCr_equiv.
      apply frac_agree_op_valid in HCr_equiv.
      destruct HCr_equiv as [_ HCr_equiv].
      apply leibniz_equiv_iff in HCr_equiv.
      iPureIntro. done. } subst Cr'.
      iAssert (⌜map_of_set H' !! k = Some t⌝)%I as %MapCd'.
        { iDestruct "Hcir'" as %Hcir.
          pose proof Hcir k t as [H1 _].
          iPureIntro. pose proof H1 Cn_val as H1.
          by rewrite H1. }
      iAssert (⌜(k,t0) ∈ H'⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HH] [$mcs_sr]") as "H'".
        iDestruct "H'" as %H.
        apply auth_both_valid_discrete in H.
        destruct H as [H _].
        apply gset_included in H.
        iPureIntro; clear -H; set_solver. }
      iAssert (⌜(k,t0) ∈ H' → t0 ≤ map_of_set H' !!! k⌝)%I as "%".
      {
        iPureIntro. by apply map_of_set_lookup_lb.
      }
      iAssert (⌜map_of_set H' !!! k = t⌝)%I as "%".
      {
        iPureIntro. unfold lookup_total. 
        unfold finmap_lookup_total. rewrite -> MapCd'. try done.
      }
      iAssert (⌜t0 ≤ (map_of_set H' !!! k)⌝)%I as "%".
      {
        iPureIntro. pose proof H0 H as H0. done.
      }
      iAssert (⌜t0 = t⌝)%I as %t0_eq_t.
      { iPureIntro. admit. }
        
    iModIntro. iSplitR "HInv AU Hγ_c Hdecide node_n". iNext.
    iExists T', H'. iFrame.
    iExists Cr, Cd'. iFrame. iFrame "Hcir'".   
    rewrite (big_sepS_delete _ (KS) k); last by eauto.
    iSplitL "HnS_stark". done. done.

    iModIntro. wp_pures.
    awp_apply (unlockNode_spec_high with "[] [] [Hγ_c Hdecide node_n]"); try done.
    iFrame. iFrame "#".
    iAaccIntro with ""; try done.
      { eauto with iFrame. }
    iMod "AU" as "[_ [_ Hclose]]".
    iSpecialize ("Hclose" $! t0).
    iMod ("Hclose" with "[]") as "HΦ".
    iFrame "mcs_sr". by iPureIntro.
    iIntros "_".
    iModIntro. wp_pures. subst t. rewrite -> t0_eq_t. done.
  
  Admitted.

End multicopy_df_search.
  