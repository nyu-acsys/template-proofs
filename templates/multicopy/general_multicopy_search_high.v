From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Import general_multicopy util general_multicopy_search.

Section search_proof_high.
  Context {Σ} `{!heapG Σ, !multicopyG Σ}.
  Notation iProp := (iProp Σ).  
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  Lemma search_spec_intermediate N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                                  lc r γ_td γ_ght (k: K) :
  ⊢ ⌜k ∈ KS⌝ -∗ 
      mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr lc r -∗
        helping_inv N γ_fr (protocol_conc N γ_te γ_he γ_fr γ_td γ_ght) -∗ 
          <<< ∀ t H, MCS γ_te γ_he t H >>>
                search' r #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N))
          <<<  ∃ (t': nat), MCS γ_te γ_he t H 
                            ∗ ⌜map_of_set H !!! k = t'⌝, RET #t' >>>.
  Proof.
    iIntros "% #HInv #HInv_h" (Φ) "AU". wp_lam.
    rename H into k_in_KS.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vt)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 NatTypedProph); first done.
    iIntros (tp p)"Hproph". wp_pures. 
    iApply fupd_wp.
    iInv "HInv" as ">H".
    iDestruct "H" as (T H hγ I R) "(Hglob & Hstar)".
    iAssert (⌜∃ t0, ((k,t0) ∈ H ∧ (∀ t, (k,t) ∈ H → t ≤ t0) 
                ∧ map_of_set H !! k = Some t0)⌝)%I as "%".
    { iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & Ht & HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & #FP_r & Max_ts & domm_IR & domm_Iγ)".
      iAssert (⌜r ∈ domm I⌝)%I as "%". 
      { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
      rename H0 into r_in_I.
      rewrite (big_sepS_delete _ (domm I) r); last by eauto.
      iDestruct "Hstar" as "(H_r & Hstar')".
      iDestruct "H_r" as (br Cr Br Qr)"(Hl_r & Hlif_r & HnS_r)".
      iDestruct "HnS_r" as (γ_er γ_cr γ_br γ_qr γ_cirr es Ir Rr) 
                        "(#HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                  & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
      iEval (rewrite decide_True) in "HnS_H".
      iDestruct "HnS_H" as "(% & %)".
      rename H0 into Br_eq_H. rename H1 into Infz_Ir.
      pose proof (map_of_set_lookup_cases H k) as H'.
      destruct H' as [H' | H'].
      - destruct H' as [t0 [H' [H'' H''']]].
        iPureIntro. exists t0; split; try done.
      - iDestruct "Hist" as %Hist.
        destruct H' as [H' _].
        pose proof H' 0 as H'.
        pose proof Hist k k_in_KS as Hist.
        contradiction. }  

    destruct H0 as [t0 [kt0_in_H [Max_t0 H_k]]].
    iDestruct "Hglob" as "(MCS_auth & HH & Hglob')".
    iMod (own_update γ_s (● H) (● H ⋅ ◯ {[(k,t0)]}) with "[$HH]") as "HH".
    { apply (auth_update_frac_alloc _ H ({[(k,t0)]})).
      apply gset_included. clear -kt0_in_H. set_solver. }
    iDestruct "HH" as "(HH & #mcs_sr)".
    iAssert (global_state γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                     r T H hγ I R)%I with "[$MCS_auth $HH $Hglob']" as "Hglob".
                     
    destruct (decide (tp ≤ t0)).
    - assert ((tp < t0) ∨ tp = t0) as H' by lia.
      destruct H' as [Hcase' | Hcase'].
      + iModIntro. iSplitR "AU Hproph".
        iNext; iExists T, H, hγ, I, R; iFrame.
        iModIntro.
        awp_apply search_recency; try done.
        iAaccIntro with ""; try done.
        { iIntros "_". iModIntro; try eauto with iFrame. } 
        iIntros (t) "(Hkt & %)". rename H0 into t0_le_t.
        iModIntro. wp_pures.
        wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); try done.
        wp_pures. iModIntro. iIntros "%". rename H0 into tp_eq_t.
        clear -tp_eq_t Hcase' t0_le_t. exfalso; lia.
      + iMod "AU" as (T' H') "[MCS [_ Hcomm]]".
        set_solver.
        iAssert (⌜T' = T ∧ H' = H⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & Ht & HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".  
          iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
          unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
          by iDestruct "MCS" as "(_ & H')". subst H'.
          iPoseProof ((auth_agree γ_te) with "[MCS_auth] [MCS]") as "%".
          unfold MCS_auth. by iDestruct "MCS_auth" as "(H'' & _)".
          by iDestruct "MCS" as "(H' & _)".
          by iPureIntro. } 
        destruct H0 as [H'' H''']. subst T' H'.
        assert (map_of_set H !!! k = t0) as M_k.
        { rewrite lookup_total_alt. rewrite H_k.
          by simpl. }
        iSpecialize ("Hcomm" $! t0). 
        iMod ("Hcomm" with "[MCS]") as "HΦ".
        { iFrame. by iPureIntro. } 
        iModIntro. iSplitR "HΦ Hproph".
        iNext; iExists T, H, hγ, I, R; iFrame.
        iModIntro.
        awp_apply search_recency without "HΦ"; try done.
        iAaccIntro with ""; try done.
        { iIntros "_". iModIntro; try eauto with iFrame. } 
        iIntros (t) "(Hkt & %)". rename H0 into t0_le_t.
        iModIntro. iIntros "HΦ". wp_pures.
        wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); try done.
        wp_pures. iModIntro. iIntros "%". rename H0 into tp_eq_t. 
        wp_pures. iModIntro.
        assert (tp = t) as H' by lia.
        rewrite <-H'. by rewrite Hcase'.
    - assert (tp > t0) by lia. rename H0 into tp_ge_t0.
      iInv "HInv_h" as (H')"(>Hfr & Protocol_conc)".
      iDestruct "Protocol_conc" as (TD hγt)"(>HTD & >Hγt 
                                      & >Domm_hγt & Hstar_reg)".
      iAssert (⌜H' = H⌝)%I as "%". 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & _ )". 
        iPoseProof (own_valid_2 _ _ _ with "[$HfrH] [$Hfr]") as "V_H".
        iDestruct "V_H" as %V_H.
        apply frac_agree_op_valid in V_H. destruct V_H as [_ V_H].
        apply leibniz_equiv_iff in V_H.
        by iPureIntro. } subst H'.
      iAssert (▷ (⌜tid ∉ TD⌝ 
                ∗ ([∗ set] t_id ∈ TD, registered N γ_te γ_he γ_ght H t_id) 
                ∗ proph1 tid vt))%I with "[Hstar_reg Htid]" 
                as "(>% & Hstar_reg & Htid)".
      { destruct (decide (tid ∈ TD)); try done.
        - iEval (rewrite (big_sepS_elem_of_acc _ (TD) tid); 
                                last by eauto) in "Hstar_reg".
          iDestruct "Hstar_reg" as "(Hreg & Hstar_reg')".
          iDestruct "Hreg" as (? ? ? ? ? ? ?)"(H' & _)".
          iAssert (▷ False)%I with "[H' Htid]" as "HF".
          iApply (proph1_exclusive tid with "[Htid]"); try done.
          iNext. iExFalso; try done.
        - iFrame. iNext. by iPureIntro. }
      rename H0 into tid_notin_TD.
      iMod (own_update γ_td (● TD) (● (TD ∪ {[tid]})) with "[$HTD]") as "HTD".
      { apply (auth_update_auth _ _ (TD ∪ {[tid]})).
        apply gset_local_update. set_solver. }
      iMod (own_update γ_td (● (TD ∪ {[tid]})) (● (TD ∪ {[tid]}) ⋅ ◯ {[tid]}) 
                with "[$HTD]") as "(HTD & #FP_t)".
      { apply (auth_update_frac_alloc _ (TD ∪ {[tid]}) ({[tid]})).
        apply gset_included. clear; set_solver. }

      iMod (own_alloc (to_frac_agree (1) (H))) 
              as (γ_sy)"Hfr_t". { try done. }        
      iEval (rewrite <-Qp_half_half) in "Hfr_t".      
      iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
      iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".
      
      iDestruct "Domm_hγt" as %Domm_hγt.
      set (<[ tid := to_agree γ_sy ]> hγt) as hγt'.
      iDestruct (own_update _ _ 
        (● hγt' ⋅ ◯ {[ tid := to_agree γ_sy ]})
               with "Hγt") as ">Hγt".
      { apply auth_update_alloc. 
        rewrite /hγt'.
        apply alloc_local_update; last done.
        rewrite <-Domm_hγt in tid_notin_TD.
        by rewrite not_elem_of_dom in tid_notin_TD*; 
        intros tid_notin_TD. }
      iDestruct "Hγt" as "(Hγt & #Hreg_gh)".  
                  
      iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
      iMod (own_alloc (Excl ())) as (γ_tk') "Token"; first try done.
      assert ((k,tp) ∉ H) as ktp_notin_H. 
      { destruct (decide ((k, tp) ∈ H)); try done.
        pose proof Max_t0 tp e as H'.
        clear -H' tp_ge_t0. lia. } 
      iMod (inv_alloc (threadN N) _
              (∃ H, get_op_state γ_sy tid γ_tk' AU_later (Φ) H k tp) 
                                    with "[AU Hreg_sy1]") as "#HthInv".
      { iNext. iExists H. unfold get_op_state. iFrame "Hreg_sy1".
        iLeft. unfold state_lin_pending. iFrame. by iPureIntro. }

      iModIntro. iSplitL "Htid Hfr Hstar_reg HTD Hγt Hreg_sy2". iNext.
      iExists H. iFrame "Hfr". iExists (TD ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (TD ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold registered.
      iExists AU_later, Φ, k, tp, vt, γ_tk', γ_sy. iFrame "∗#".
      assert ((TD ∪ {[tid]}) ∖ {[tid]} = TD) as H' 
                  by (clear -tid_notin_TD; set_solver).
      by rewrite H'.
      
      iModIntro. iSplitR "Token Hproph".
      iNext. iExists T, H, hγ, I, R; iFrame.
      
      iModIntro. awp_apply search_recency; try done.
      iAaccIntro with ""; try done.
      { iIntros "_". iModIntro; try eauto with iFrame. } 
      iIntros (t) "(#Hkt & %)". rename H0 into t0_le_t.
      iModIntro. wp_pures.
      wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); try done.
      wp_pures. iModIntro. iIntros "%". rename H0 into tp_eq_t.
      iApply fupd_wp.
      iInv "HthInv" as (H1)"(>Hth_sy & Hth_or)".
      iInv "HInv_h" as (H1')"(>Hfr & Protocol_conc)".
      iDestruct "Protocol_conc" as (TD1 hγt1)"(>HTD & >Hγt 
                                      & >Domm_hγt & Hstar_reg)".
      iAssert (⌜tid ∈ TD1⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HTD] [$FP_t]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro. set_solver. }
        
      iAssert (▷ (⌜H1' = H1⌝
               ∗ ([∗ set] t_id ∈ TD1, registered N γ_te γ_he γ_ght H1' t_id)
               ∗ own (γ_sy) (to_frac_agree (1 / 2) H1) ))%I
                with "[Hstar_reg Hth_sy]" as "(>% & Hstar_reg & >Hth_sy)". 
      { iEval (rewrite (big_sepS_elem_of_acc _ (TD1) tid); 
                                last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg_t & Hstar_reg')".
        iDestruct "Hreg_t" as (P' Q' k' vp' vt' γ_tk'' γ_sy')
                          "(Hreg_proph & >Hreg_gh' & >Hreg_sy & Ht_reg')".

        iCombine "Hreg_gh" "Hreg_gh'" as "H".
        iPoseProof (own_valid with "H") as "Valid".
        iDestruct "Valid" as %Valid.
        rewrite auth_frag_valid in Valid *; intros Valid.
        apply singleton_valid in Valid.
        apply to_agree_op_inv in Valid.
        apply leibniz_equiv in Valid.
        subst γ_sy'.
                  
        iAssert (⌜H1' = H1⌝)%I as "%".
        { iPoseProof (own_valid_2 _ _ _ with "[$Hth_sy] [$Hreg_sy]") as "V_H".
          iDestruct "V_H" as %V_H.
          apply frac_agree_op_valid in V_H. destruct V_H as [_ V_H].
          apply leibniz_equiv_iff in V_H.
          by iPureIntro. } subst H1'.
        iSplitR. iNext; by iPureIntro.
        iSplitR "Hth_sy". iApply "Hstar_reg'".
        iNext. iExists P', Q', k', vp', vt', γ_tk'', γ_sy.
        iFrame "∗#". by iNext. } subst H1'.
      iInv "HInv" as ">H".
      iDestruct "H" as (T1 H1' hγ1 I1 R1) "(Hglob & Hstar)".
      iAssert (⌜H1' = H1⌝)%I as "%". 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & _ )". 
        iPoseProof (own_valid_2 _ _ _ with "[$HfrH] [$Hfr]") as "V_H".
        iDestruct "V_H" as %V_H.
        apply frac_agree_op_valid in V_H. destruct V_H as [_ V_H].
        apply leibniz_equiv_iff in V_H.
        by iPureIntro. } subst H1'.
      assert (tp = t) as H' by lia. 
      iAssert (⌜(k,tp) ∈ H1⌝)%I as "%". 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hglob')".
        iPoseProof (own_valid_2 _ _ _ with "[$HH] [$Hkt]") as "H'".
        iDestruct "H'" as %H''.
        apply auth_both_valid_discrete in H''.
        destruct H'' as [H'' _].
        apply gset_included in H''.
        rewrite <-H' in H''.
        iPureIntro; clear -H''; set_solver. }
      rename H0 into ktp_in_H1.
      iDestruct "Hth_or" as "[Hth_or | Hth_or]".
      { iDestruct "Hth_or" as "(? & >%)".
        exfalso. try done. }
      iDestruct "Hth_or" as "(Hth_or & >%)".  
      iDestruct "Hth_or" as "[Hth_or | >Hth_or]"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Hth_or]") as "%".
        exfalso; try done. }
      
      iModIntro. iSplitL "Hglob Hstar".
      iExists T1, H1, hγ1, I1, R1; iFrame.

      iModIntro. iSplitL "Hstar_reg HTD Hfr Hγt Domm_hγt".
      iNext. iExists H1. iFrame "Hfr".
      iExists TD1, hγt1; iFrame.
      
      iModIntro. iSplitL "Token Hth_sy".
      iNext. iExists H1. iFrame "Hth_sy". 
      iRight. iFrame "∗%".
      
      iModIntro. wp_pures. by rewrite H'.
  Qed.
    
  Lemma search_spec_high N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                                  lc r γ_td γ_ght (k: K) :
  ⊢ ⌜k ∈ KS⌝ -∗ 
      <<< ∀ t M, MCS_high N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                      lc r γ_td γ_ght t M >>>
            search' r #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N))
      <<<  ∃ (t': nat), MCS_high N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                                 lc r γ_td γ_ght t M 
                        ∗ ⌜M !!! k = t'⌝, RET #t' >>>.
  Proof.
    iIntros "%" (Φ) "AU". rename H into k_in_KS.
    iApply fupd_wp. 
    iMod "AU" as (t' M')"[H [Hab _]]".
    iDestruct "H" as (H')"(MCS & M_eq_H & #HInv & #HInv_h)".
    iMod ("Hab" with "[MCS M_eq_H]") as "AU".
    iExists H'. iFrame "∗#". iModIntro.
    awp_apply search_spec_intermediate; try done.
    rewrite /atomic_acc /=. iMod "AU" as (t M)"[H HAU]".
    iDestruct "H" as (H)"(MCS & M_eq_H & _)".
    iModIntro. iExists t, H. iFrame "MCS". iSplit.
    { iIntros "MCS". iDestruct "HAU" as "[Hab _]".
      iMod ("Hab" with "[MCS M_eq_H]") as "AU".
      iExists H. iFrame "∗#". by iModIntro. }
    iIntros (tr)"(MCS & %)". rename H0 into H_k.   
    iDestruct "M_eq_H" as %M_eq_H.
    iAssert (⌜M !!! k = tr⌝)%I as "M_k".
    { iPureIntro. by rewrite <-M_eq_H. }
    iDestruct "HAU" as "[_ Hcomm]".
    iSpecialize ("Hcomm" $! tr).
    iMod ("Hcomm" with "[MCS]") as "HΦ". 
    iFrame "M_k". iExists H. iFrame "∗#%".
    by iModIntro.
  Qed.

End search_proof_high.