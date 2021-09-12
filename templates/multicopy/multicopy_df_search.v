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
                       γ_cr γ_cd γ_d r d (k: K) v0 t0 :
    ⊢ ⌜k ∈ KS⌝ -∗
        mcs_inv N γ_te γ_he γ_s Prot
           (Inv_DF γ_s γ_cr γ_cd γ_d r d) -∗
          SR γ_s (k, (v0, t0)) -∗
              <<< True >>>
                  search r d #k @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ (v: V) (t': T), SR γ_s (k, (v, t')) ∗ ⌜t0 ≤ t'⌝, 
                                                    RET #v >>>.
  Proof.
    iIntros "% #HInv #mcs_sr" (Φ) "AU".
    rename H into k_in_KS.
    wp_lam.

    awp_apply lockNode_spec_high; try done.
    iPureIntro. left. done.
    iAaccIntro with ""; try eauto with iFrame.
    iIntros (γ_cn Cr Vr Tr)"HnP_n". iModIntro. wp_pures.
    iDestruct "HnP_n" as "(HnP_n & #HRorD)".
    iDestruct "HnP_n" as "(Hnode & #Hγ_s & Hγ_c)".
    wp_apply (inContents_spec with "Hnode").
    iIntros (v) "(node_n & H)". iDestruct "H" as %Vr_val.
    wp_pures.
    (** Case analysis on whether k in contents of r **)
    destruct v as [v |]; last first.
    - (* Case 1: k not in r. *)
      wp_pures.
      (** Unlock node r **)

      (* Open the invariant. *)
      iApply fupd_wp.
      iInv "HInv" as (T H)"(mcs_high & >Inv_DF)".
      iDestruct "Inv_DF" as (Cr' Vr' Tr' Cd Vd Td) "(r_neq_d & Hcir 
            & Hset & HlockR_r & Half_r & Hcts_r 
            & HlockR_d & Half_d & Hcts_d)".
      iDestruct "mcs_high" as "(>MCS_auth & >HH & >HInit 
        & >HClock & >HUniq & Prot)".
      rewrite (big_sepS_delete _ (KS) k); last by eauto.
      iDestruct "Hset" as "(HnS_stark & HnS_star')".

      iAssert(⌜γ_cn = γ_cr⌝)%I as "%".
      {
        iDestruct "HRorD" as %HRorD.
        iDestruct "r_neq_d" as %HRnotD.
        destruct HRorD as [temp | temp];
        destruct temp; iPureIntro; try done.
      } subst γ_cr.
      iAssert (⌜Cr = Cr'⌝∗ ⌜Vr = Vr'⌝ ∗ ⌜Tr = Tr'⌝)%I as "(%&%&%)".
      { iPoseProof (own_valid_2 _ _ _ with "[$Half_r] [$Hγ_c]") 
                as "#HCr_equiv".
        iDestruct "HCr_equiv" as %HCr_equiv.
        apply frac_agree_op_valid in HCr_equiv.
        destruct HCr_equiv as [_ HCr_equiv].
        apply leibniz_equiv_iff in HCr_equiv.
        inversion HCr_equiv. iPureIntro. done. } subst Cr' Vr' Tr'.

      iAssert (⌜map_of_set H !! k = Cd !! k⌝)%I as %MapCd.
      { iDestruct "Hcir" as %Hcir.
        iDestruct "Hcts_r" as "(% & _)".
        rename H0 into dom_Cr_Vr.
        apply not_elem_of_dom in Vr_val.
        rewrite <-dom_Cr_Vr in Vr_val.
        apply not_elem_of_dom in Vr_val.
        pose proof Hcir k as [_ H'].
        iPureIntro. pose proof H' Vr_val as H'.
        by rewrite H'. }
      iDestruct "r_neq_d" as %r_neq_d.
      iAssert (⌜r ≠ d⌝)%I as "Hrnotd".
      {
        iPureIntro; done.
      }

      iAssert (⌜(k, (v0, t0)) ∈ H⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HH] [$mcs_sr]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro; clear -H'; set_solver. }
      iAssert (⌜(k, (v0, t0)) ∈ H → t0 ≤ (map_of_set H !!! k).2⌝)%I 
                                                              as "%".
      {
        iPureIntro. by apply map_of_set_lookup_lb.
      }
      iAssert (⌜t0 ≤ (map_of_set H !!! k).2⌝)%I as "%".
      {
        iPureIntro. pose proof H1 H0 as H1. done.
      }
      iAssert (⌜t0 ≤ Td !!! k⌝)%I as "%".
      { iDestruct "Hcts_d" as "(_&_& %)".
        iPureIntro. unfold lookup_total, map_lookup_total in H2. 
        rewrite MapCd in H2.
        destruct (Cd !! k) as [[vd td] | ] eqn: Hcdk.
        - simpl in H2. apply H3 in Hcdk. 
          destruct Hcdk as [_ Hcdk].
          rewrite lookup_total_alt.
          rewrite Hcdk. by simpl.
        - simpl in H2. clear -H2; lia. }
      iMod (own_update (γ_d !!! k) (● MaxNat (Td !!! k))
          (● (MaxNat (Td !!! k)) ⋅ ◯ (MaxNat (Td !!! k)))
            with "[$HnS_stark]") as "HnS_stark".
      { apply (auth_update_frac_alloc); try done.
        unfold CoreId, pcore, cmra_pcore. simpl.
        unfold ucmra_pcore. simpl. by unfold max_nat_pcore_instance. }
      iDestruct "HnS_stark" as "(HnS_stark & #mcs_sr')".

      iModIntro. iSplitR "AU Hγ_c node_n". iNext.
      iExists T, H. iFrame. iFrame "#".
      iExists Cr, Vr, Tr, Cd, Vd, Td. iFrame. iFrame "#".
      rewrite (big_sepS_delete _ (KS) k); last by eauto.
      iFrame "#∗". iModIntro.


       (** Unlock node r **)
      wp_pures. awp_apply (unlockNode_spec_high with "[] []
      [Hγ_c node_n]"); try done. iFrame "∗#".
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. wp_pures.

      awp_apply lockNode_spec_high; try done. iPureIntro.
      right. done. iAaccIntro with ""; try eauto with iFrame.
      iIntros (γ_cd' Cd' Vd' Td')"HnP_n". iModIntro. wp_pures.
      iDestruct "HnP_n" as "(HnP_n & #HRorD')".
      iDestruct "HnP_n" as "(Hnode' & #Hγ_s' & Hγ_c')".

      wp_apply (inContents_spec with "Hnode'").
      iIntros (v) "(node_n & H)". iDestruct "H" as %Vd'_val.
      wp_pures.
      destruct v as [v |]; last first.
      (** Case analysis on whether k is in the contents of d. **)
      + (** Case 1.a : k not in datastructure. **)
        wp_pures.

        (* Reopen the invariant. *)
        iApply fupd_wp.
        iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)".
        iDestruct "Inv_DF" as (Cr1 Vr1 Tr1 Cd1 Vd1 Td1) "(r_neq_d & Hcir 
            & Hset & HlockR_r & Half_r & Hcts_r 
            & HlockR_d & Half_d & Hcts_d)".
        iDestruct "mcs_high" as "(>MCS_auth & >HH & >HInit 
          & >HClock & >HUniq & Prot)".

        iAssert(⌜γ_cd' = γ_cd⌝)%I as "%".
        {
          iDestruct "HRorD'" as %HRorD'.
          destruct HRorD' as [temp | temp];
          destruct temp; iPureIntro; try done.
        } subst γ_cd'.

        iAssert (⌜Cd1 = Cd'⌝∗⌜Vd1 = Vd'⌝∗⌜Td1 = Td'⌝)%I as "(%&%&%)".
        {
          iPoseProof (own_valid_2 _ _ _ with "[$Half_d] [$Hγ_c']") 
            as "#HCr_equiv".
          iDestruct "HCr_equiv" as %HCr_equiv.
          apply frac_agree_op_valid in HCr_equiv.
          destruct HCr_equiv as [_ HCr_equiv].
          apply leibniz_equiv_iff in HCr_equiv.
          iPureIntro. inversion HCr_equiv. done.
        } subst Cd' Vd' Td'.

        iAssert (⌜set_of_map Cd1 ⊆ H'⌝)%I as %Cd1_Sub_H.
          { iPoseProof ((auth_own_incl γ_s H' _) with "[$HH $Hγ_s']") as "%".
          rename H0 into H''. by apply gset_included in H4. }

        rewrite (big_sepS_delete _ (KS) k); last by eauto.
        iDestruct "Hset" as "(Hd_k_own & Hd_not_k_own)".

        iMod (own_update (γ_d !!! k) (● MaxNat (Td1 !!! k))
          (● (MaxNat (Td1 !!! k)) ⋅ ◯ (MaxNat (Td1 !!! k)))
              with "[$Hd_k_own]") as "Hd_k_own".
        { apply (auth_update_frac_alloc); try done.
          unfold CoreId, pcore, cmra_pcore. simpl.
          unfold ucmra_pcore. simpl. by unfold max_nat_pcore_instance. }
        iDestruct "Hd_k_own" as "(Hd_k_own & d_k_frac_own)".

        iAssert (⌜(Td !!! k) ≤ (Td1 !!! k)⌝)%I as "%".
        {
          iPoseProof (own_valid_2 _ _ _ with "[$Hd_k_own]  [$mcs_sr']") as "H'".
          iDestruct "H'" as %H''.
          apply auth_both_valid_discrete in H''.
          destruct H'' as [H'' _].
          apply max_nat_included in H''.
          simpl in H''.
          by iPureIntro.
        } rename H4 into td_k_monotonic.

        iAssert (⌜Td1 !!! k = 0⌝)%I as %Td1_zero.
        {
          iDestruct "Hcts_d" as "(%&%&%)".
          iPureIntro.
          apply not_elem_of_dom in Vd'_val.
          rewrite <-H4 in Vd'_val.
          rewrite H5 in Vd'_val.
          apply not_elem_of_dom in Vd'_val.
          rewrite lookup_total_alt.
          rewrite Vd'_val.
          by simpl.
        }
        iAssert (⌜Td !!! k = 0⌝)%I as %Td_zero.
        {

          iPureIntro.
          replace (Td1 !!! k) with (0) in td_k_monotonic.
          destruct (Td !!! k) as [| ]; try done.
          pose proof zerop as zerop.
          specialize zerop with y.
          destruct zerop as [z | x]; lia.
        }
        iAssert (⌜t0 = 0⌝)%I as %t0_zero.
        { iPureIntro. lia.
        }  subst t0.
        iAssert (⌜(k, (bot, 0)) ∈ H'⌝)%I as "%".
        {
          iDestruct "HInit" as %HInit.
          iPureIntro; apply HInit; try done.
        }
        iMod (own_update γ_s (● H') (● H' ⋅ ◯ {[(k, (bot, 0))]}) 
          with "[$HH]") as "HH".
        {
          apply (auth_update_frac_alloc _ H' ({[(k, (bot, 0))]})).
          apply gset_included. set_solver.
        }
        iDestruct "HH" as "(HH & #mcs_sr'')".
        iModIntro. iSplitR "HInv AU Hγ_c' node_n". iNext.
        iExists T', H'. iFrame.
        iExists Cr1, Vr1, Tr1, Cd1, Vd1, Td1. iFrame. 
        rewrite (big_sepS_delete _ (KS) k); last by eauto. iFrame.
        (** Unlock node d **)
        iModIntro. wp_pures.
        awp_apply (unlockNode_spec_high with "[] []
        [Hγ_c' node_n]"); try done. iFrame "∗#".
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_".

        iMod "AU" as "[_ [_ Hclose]]".
        iSpecialize ("Hclose" $! bot 0).
        iMod ("Hclose" with "[]") as "HΦ". iFrame "mcs_sr''".
        by iPureIntro.

        (** Closing the invariant **)
        iModIntro. wp_pures. iFrame.
        iModIntro. done.

      + (** Case 1.b : k is not in r, but is in d. **)
        wp_pures.

        (* Reopen the invariant. *)
        iApply fupd_wp.
        iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)".
        iDestruct "Inv_DF" as (Cr1 Vr1 Tr1 Cd1 Vd1 Td1) "(r_neq_d & Hcir 
            & Hset & HlockR_r & Half_r & Hcts_r 
            & HlockR_d & Half_d & Hcts_d)".
        iDestruct "mcs_high" as "(>MCS_auth & >HH & >HInit 
          & >HClock & >HUniq & Prot)".


        rewrite (big_sepS_delete _ (KS) k); last by eauto.
        iDestruct "Hset" as "(HnS_stark & HnS_star')".

        iAssert(⌜γ_cd' = γ_cd⌝)%I as "%".
        {
          iDestruct "HRorD'" as %HRorD'.
          destruct HRorD' as [temp | temp];
          destruct temp; iPureIntro; try done.
        } subst γ_cd'.

        iAssert (⌜Cd1 = Cd'⌝∗⌜Vd1 = Vd'⌝∗⌜Td1 = Td'⌝)%I as "(%&%&%)".
        {
          iPoseProof (own_valid_2 _ _ _ with "[$Half_d] [$Hγ_c']") as "#HCr_equiv".
          iDestruct "HCr_equiv" as %HCr_equiv.
          apply frac_agree_op_valid in HCr_equiv.
          destruct HCr_equiv as [_ HCr_equiv].
          apply leibniz_equiv_iff in HCr_equiv.
          iPureIntro. inversion HCr_equiv. done.
        } subst Cd1 Vd1 Td1.

        iAssert (⌜set_of_map Cd' ⊆ H'⌝)%I as %Cd_Sub_H.
          { iPoseProof ((auth_own_incl γ_s H' _) with "[$HH $Hγ_s']") as "%".
          rename H0 into H''. by apply gset_included in H4. }
          
        iAssert (⌜is_Some(Td' !! k)⌝)%I as %Td'_k.
        { iDestruct "Hcts_d" as "(%&%&%)". 
          iPureIntro.  
          apply elem_of_dom_2 in Vd'_val.
          rewrite <-H4 in Vd'_val.
          rewrite H5 in Vd'_val.
          by apply elem_of_dom in Vd'_val. }
        
        destruct Td'_k as [t Td'_k].  

        iAssert (⌜(k, (v, t)) ∈ set_of_map Cd'⌝)%I as %kt_in_Cd.
        { iDestruct "Hcts_d" as "(%&%&%)".
          iPureIntro. apply set_of_map_member.
          apply H6. split; try done. }

        iAssert (⌜(k, (v, t)) ∈ H'⌝)%I as "%".
        { iPureIntro. set_solver. }

        iMod (own_update (γ_d !!! k) (● MaxNat (Td' !!! k))
          (● (MaxNat (Td' !!! k)) ⋅ ◯ (MaxNat (Td' !!! k)))
              with "[$HnS_stark]") as "HnS_stark".
        { apply (auth_update_frac_alloc); try done.
          unfold CoreId, pcore, cmra_pcore. simpl.
          unfold ucmra_pcore. simpl. by unfold max_nat_pcore_instance. }
        iDestruct "HnS_stark" as "(HnS_stark & mcs_sr'')".

        iAssert (⌜(Td !!! k) ≤ (Td' !!! k)⌝)%I as "%".
        { iPoseProof (own_valid_2 _ _ _ with "[$HnS_stark]  [$mcs_sr']") as "H'".
          iDestruct "H'" as %H''.
          apply auth_both_valid_discrete in H''.
          destruct H'' as [H'' _].
          apply max_nat_included in H''.
          simpl in H''.
          by iPureIntro. }
    
        iAssert (⌜Td' !!! k = t⌝)%I as "%". 
        { iPureIntro. 
          unfold lookup_total. 
          unfold map_lookup_total. 
          replace (Td' !! k) with (Some t).
          simpl. done. }  
        
        iAssert (⌜t0 ≤ t⌝)%I as %t0_leq_t.
        { iPureIntro. rewrite <-H3 in H5. 
          by rewrite H6 in H5. }

        iMod (own_update γ_s (● H') (● H' ⋅ ◯ {[(k, (v, t))]}) 
                            with "[$HH]") as "HH".
        { apply (auth_update_frac_alloc _ H' ({[(k,(v, t))]})).
          apply gset_included. clear -kt_in_Cd Cd_Sub_H. set_solver. }
        iDestruct "HH" as "(HH & #mcs_sr1)".
        iModIntro. iSplitR "HInv AU Hγ_c' node_n". iNext.
        iExists T', H'. iFrame.
        iExists Cr1, Vr1, Tr1, Cd', Vd', Td'. iFrame.
        rewrite (big_sepS_delete _ (KS) k); last by eauto. iFrame.

        iModIntro. wp_pures.
        awp_apply (unlockNode_spec_high with "[] [] [Hγ_c' node_n]"); 
                                                    try  done.
        iFrame. iFrame "#".
        iAaccIntro with ""; try done.
        { eauto with iFrame. } iIntros "_".
        iMod "AU" as "[_ [_ Hclose]]".
        iSpecialize ("Hclose" $! v t).
        iMod ("Hclose" with "[]") as "HΦ".
        iSplitL "mcs_sr". iFrame "#". by iPureIntro.
        iModIntro. wp_pures.
        done.

  - (* Case 2: k is in the root node. *)
      wp_pures.

      (* Reopen the invariant. *)
      iApply fupd_wp.
      iInv "HInv" as (T' H')"(mcs_high & >Inv_DF)".
      iDestruct "Inv_DF" as (Cr' Vr' Tr' Cd' Vd' Td') "(r_neq_d & Hcir 
            & Hset & HlockR_r & Half_r & Hcts_r 
            & HlockR_d & Half_d & Hcts_d)".
      iDestruct "mcs_high" as "(>MCS_auth & >HH & >HInit 
        & >HClock & >HUniq & Prot)".
        
      rewrite (big_sepS_delete _ (KS) k); last by eauto.
      iDestruct "Hset" as "(HnS_stark & HnS_star')".

      iAssert(⌜γ_cn = γ_cr⌝)%I as "%".
      {
        iDestruct "HRorD" as %HRorD.
        iDestruct "r_neq_d" as %r_neq_d.
        destruct HRorD as [temp | temp];
        destruct temp; iPureIntro; try done.
      } subst γ_cr.

      iAssert (⌜Cr = Cr'⌝∗ ⌜Vr = Vr'⌝ ∗ ⌜Tr = Tr'⌝)%I as "(%&%&%)".
      { iPoseProof (own_valid_2 _ _ _ with "[$Half_r] [$Hγ_c]") 
                as "#HCr_equiv".
        iDestruct "HCr_equiv" as %HCr_equiv.
        apply frac_agree_op_valid in HCr_equiv.
        destruct HCr_equiv as [_ HCr_equiv].
        apply leibniz_equiv_iff in HCr_equiv.
        inversion HCr_equiv. iPureIntro. done. } subst Cr' Vr' Tr'.

      iAssert (⌜is_Some(Tr !! k)⌝)%I as %Tr_k.
      { iDestruct "Hcts_r" as "(%&%&%)". 
        iPureIntro.  
        apply elem_of_dom_2 in Vr_val.
        rewrite <-H in Vr_val.
        rewrite H0 in Vr_val.
        by apply elem_of_dom in Vr_val. }
        
      destruct Tr_k as [t Tr_k].  

      iAssert (⌜map_of_set H' !! k = Some (v, t)⌝)%I as %MapCd'.
      { iDestruct "Hcts_r" as "(_&_&%)".
        iDestruct "Hcir" as %Hcir.
        pose proof Hcir k v t as [H1 _].
        iPureIntro. apply H1.
        apply H; split; try done. }

      iAssert (⌜set_of_map Cr ⊆ H'⌝)%I as %Cr_Sub_H.
        { iPoseProof ((auth_own_incl γ_s H' _) with "[$HH $Hγ_s]") as "%".
          rename H into H''. by apply gset_included in H''. }  

      iAssert (⌜(k, (v, t)) ∈ set_of_map Cr⌝)%I as %kt_in_Cr.
      { iDestruct "Hcts_r" as "(_&_&%)".
        iPureIntro. apply set_of_map_member.
        apply H; split; try done. }
  
      iAssert (⌜(k, (v, t)) ∈ H'⌝)%I as "%".
      { iPureIntro. set_solver. }

      iAssert (⌜(k, (v0, t0)) ∈ H'⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HH] [$mcs_sr]") as "H'".
        iDestruct "H'" as %H3.
        apply auth_both_valid_discrete in H3.
        destruct H3 as [H3 _].
        apply gset_included in H3.
        iPureIntro; clear -H3; set_solver. }
      iAssert (⌜(k, (v0, t0)) ∈ H' → t0 ≤ (map_of_set H' !!! k).2⌝)%I as "%".
      {
        iPureIntro. by apply map_of_set_lookup_lb.
      }
      iAssert (⌜(map_of_set H' !!! k).2 = t⌝)%I as "%".
      {
        iPureIntro. unfold lookup_total. 
        unfold map_lookup_total. rewrite -> MapCd'. try done.
      }
      iAssert (⌜t0 ≤ (map_of_set H' !!! k).2⌝)%I as "%".
      {
        iPureIntro. pose proof H1 H0 as H1. done.
      }
      iAssert (⌜t0 ≤ t⌝)%I as %t0_leq_t.
      { iPureIntro. rewrite H2 in H3. done. }

      iMod (own_update γ_s (● H') (● H' ⋅ ◯ {[(k,(v, t))]}) 
        with "[$HH]") as "HH".
      { apply (auth_update_frac_alloc _ H' ({[(k, (v, t))]})).
        apply gset_included. clear -kt_in_Cr Cr_Sub_H. set_solver. }
      iDestruct "HH" as "(HH & #mcs_sr1)".

      iModIntro. iSplitR "HInv AU Hγ_c node_n". iNext.
      iExists T', H'. iFrame.
      iExists Cr, Vr, Tr, Cd', Vd', Td'. iFrame.   
      rewrite (big_sepS_delete _ (KS) k); last by eauto.
      iSplitL "HnS_stark"; done.

     iModIntro. wp_pures.
     awp_apply (unlockNode_spec_high with "[] [] [Hγ_c node_n]"); try done.
     iFrame. iFrame "#".
     iAaccIntro with ""; try done.
     { eauto with iFrame. }
     iMod "AU" as "[_ [_ Hclose]]".
     iSpecialize ("Hclose" $! v t).
     iMod ("Hclose" with "[]") as "HΦ".
     iSplitL "mcs_sr". iFrame "#".
     by iPureIntro.
     iIntros "_".
     iModIntro. wp_pures. done.
     Unshelve. done. done.
  Qed.

End multicopy_df_search.