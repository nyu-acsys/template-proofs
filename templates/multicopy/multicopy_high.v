From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy multicopy_util auth_ext.

(** Multicopy operations *)

Parameter search : val.
Parameter upsert : val.

Definition search' : val :=
  λ: "k",
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "v" := search "k" in
    resolve_proph: "p" to: "v";;
    "v".  

Section multicopy_high.
  Context {Σ} `{heapG Σ, !multicopyG Σ}.
  Notation iProp := (iProp Σ).

  (** Low-level specs of multicopy operations *)

  Parameter search_recency: ∀ N γ_te γ_he γ_s γ_fr mcs k t0, 
    ⊢ ⌜k ∈ KS⌝ -∗ 
        mcs_inv N γ_te γ_he γ_s γ_fr mcs -∗
          mcs_sr γ_s (k, t0) -∗
              <<< True >>> 
                  search #k @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ (t': nat), mcs_sr γ_s (k, t') ∗ ⌜t0 ≤ t'⌝ , RET #t' >>>.

  Parameter upsert_spec: ∀ N γ_te γ_he γ_s γ_fr mcs k protocol_abs,
    ⊢ ⌜k ∈ KS⌝ -∗ 
        (ghost_update_protocol N γ_te γ_he protocol_abs k) -∗ 
          mcs_inv N γ_te γ_he γ_s γ_fr mcs -∗
            helping_inv N γ_fr protocol_abs -∗
              <<< ∀ t H, MCS γ_te γ_he t H >>> 
                     upsert #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N))
              <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k,t)]})
                  ∗ ⌜maxTS t H⌝, RET #() >>>.
                
  (** Proof of high-level specs for multicopy opeartions *)                

  Lemma search_spec_intermediate N γ_te γ_he γ_s γ_fr mcs_abs γ_td γ_ght (k: K) :
  ⊢ ⌜k ∈ KS⌝ -∗ 
      mcs_inv N γ_te γ_he γ_s γ_fr mcs_abs -∗
        helping_inv N γ_fr (protocol_conc N γ_te γ_he γ_fr γ_td γ_ght) -∗ 
          <<< ∀ t H, MCS γ_te γ_he t H >>>
                search' #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N))
          <<<  ∃ (t': nat), MCS γ_te γ_he t H 
                            ∗ ⌜map_of_set H !!! k = t'⌝, RET #t' >>>.
  Proof.
    iIntros "% #HInv #HInv_h" (Φ) "AU". wp_lam.
    rename H0 into k_in_KS.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vt)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 NatTypedProph); first done.
    iIntros (tp p)"Hproph". wp_pures. 
    iApply fupd_wp.
    iInv "HInv" as (T0 H0) "(>mcs_high & mcs_abs)".
    iAssert (⌜∃ t0, ((k,t0) ∈ H0 ∧ (∀ t, (k,t) ∈ H0 → t ≤ t0) 
                ∧ map_of_set H0 !! k = Some t0)⌝)%I as "%".
    { iDestruct "mcs_high" as "(MCS_auth & HH & Hist & HfrH & MaxTS)".
      pose proof (map_of_set_lookup_cases H0 k) as H'.
      destruct H' as [H' | H']; try done.
      iDestruct "Hist" as %Hist.
      destruct H' as [H' _].
      pose proof H' 0 as H'.
      pose proof Hist k k_in_KS as Hist.
      contradiction. }

    destruct H1 as [t0 [kt0_in_H [Max_t0 H_k]]].
    iDestruct "mcs_high" as "(MCS_auth & HH & mcs_high')".
    iMod (own_update γ_s (● H0) (● H0 ⋅ ◯ {[(k,t0)]}) with "[$HH]") as "HH".
    { apply (auth_update_frac_alloc _ H0 ({[(k,t0)]})).
      apply gset_included. clear -kt0_in_H. set_solver. }
    iDestruct "HH" as "(HH & #mcs_sr)".
    iCombine "MCS_auth HH mcs_high'" as "mcs_high".
                     
    destruct (decide (tp ≤ t0)).
    - assert ((tp < t0) ∨ tp = t0) as H' by lia.
      destruct H' as [Hcase' | Hcase'].
      + iModIntro. iSplitR "AU Hproph".
        iNext; iExists T0, H0; iFrame.
        iModIntro.
        awp_apply search_recency; try done.
        iAaccIntro with ""; try done.
        { iIntros "_". iModIntro; try eauto with iFrame. } 
        iIntros (t) "(Hkt & %)". rename H1 into t0_le_t.
        iModIntro. wp_pures.
        wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); try done.
        wp_pures. iModIntro. iIntros "%". rename H1 into tp_eq_t.
        clear -tp_eq_t Hcase' t0_le_t. exfalso; lia.
      + iMod "AU" as (T' H') "[MCS [_ Hcomm]]".
        set_solver.
        iAssert (⌜T' = T0 ∧ H' = H0⌝)%I as "%". 
        { iDestruct "mcs_high" as "(MCS_auth & HH & Hist & HfrH & MaxTS)".  
          iPoseProof (MCS_agree with "[$MCS_auth] [$MCS]") as "(% & %)".
          by iPureIntro. }
        destruct H1 as [H'' H''']. subst T' H'.
        assert (map_of_set H0 !!! k = t0) as M_k.
        { rewrite lookup_total_alt. rewrite H_k.
          by simpl. }
        iSpecialize ("Hcomm" $! t0). 
        iMod ("Hcomm" with "[MCS]") as "HΦ".
        { iFrame. by iPureIntro. } 
        iModIntro. iSplitR "HΦ Hproph".
        iNext; iExists T0, H0; iFrame.
        iModIntro.
        awp_apply search_recency without "HΦ"; try done.
        iAaccIntro with ""; try done.
        { iIntros "_". iModIntro; try eauto with iFrame. } 
        iIntros (t) "(Hkt & %)". rename H1 into t0_le_t.
        iModIntro. iIntros "HΦ". wp_pures.
        wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); try done.
        wp_pures. iModIntro. iIntros "%". rename H1 into tp_eq_t. 
        wp_pures. iModIntro.
        assert (tp = t) as H' by lia.
        rewrite <-H'. by rewrite Hcase'.
    - assert (tp > t0) by lia. rename H1 into tp_ge_t0.
      iInv "HInv_h" as (H')"(>Hfr & Protocol_conc)".
      iDestruct "Protocol_conc" as (TD hγt)"(>HTD & >Hγt 
                                      & >Domm_hγt & Hstar_reg)".
      iAssert (⌜H' = H0⌝)%I as "%". 
      { iDestruct "mcs_high" as "(MCS_auth & HH & Hist & HfrH & MaxTS)". 
        iPoseProof (own_valid_2 _ _ _ with "[$HfrH] [$Hfr]") as "V_H".
        iDestruct "V_H" as %V_H.
        apply frac_agree_op_valid in V_H. destruct V_H as [_ V_H].
        apply leibniz_equiv_iff in V_H.
        by iPureIntro. } subst H'.
      iAssert (▷ (⌜tid ∉ TD⌝ 
                ∗ ([∗ set] t_id ∈ TD, registered N γ_te γ_he γ_ght H0 t_id) 
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
      rename H1 into tid_notin_TD.
      iMod (own_update γ_td (● TD) (● (TD ∪ {[tid]})) with "[$HTD]") as "HTD".
      { apply (auth_update_auth _ _ (TD ∪ {[tid]})).
        apply gset_local_update. set_solver. }
      iMod (own_update γ_td (● (TD ∪ {[tid]})) (● (TD ∪ {[tid]}) ⋅ ◯ {[tid]}) 
                with "[$HTD]") as "(HTD & #FP_t)".
      { apply (auth_update_frac_alloc _ (TD ∪ {[tid]}) ({[tid]})).
        apply gset_included. clear; set_solver. }

      iMod (own_alloc (to_frac_agree (1) (H0))) 
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
      assert ((k,tp) ∉ H0) as ktp_notin_H. 
      { destruct (decide ((k, tp) ∈ H0)); try done.
        pose proof Max_t0 tp e as H'.
        clear -H' tp_ge_t0. lia. } 
      iMod (inv_alloc (threadN N) _
              (∃ H, get_op_state γ_sy tid γ_tk' AU_later (Φ) H k tp) 
                                    with "[AU Hreg_sy1]") as "#HthInv".
      { iNext. iExists H0. unfold get_op_state. iFrame "Hreg_sy1".
        iLeft. unfold state_lin_pending. iFrame. by iPureIntro. }

      iModIntro. iSplitL "Htid Hfr Hstar_reg HTD Hγt Hreg_sy2". iNext.
      iExists H0. iFrame "Hfr". iExists (TD ∪ {[tid]}), hγt'. iFrame.
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
      iNext. iExists T0, H0; iFrame.
      
      iModIntro. awp_apply search_recency; try done.
      iAaccIntro with ""; try done.
      { iIntros "_". iModIntro; try eauto with iFrame. } 
      iIntros (t) "(#Hkt & %)". rename H1 into t0_le_t.
      iModIntro. wp_pures.
      wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); try done.
      wp_pures. iModIntro. iIntros "%". rename H1 into tp_eq_t.
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
      iInv "HInv" as (T1 H1') "(>mcs_high & mcs_abs)".
      iAssert (⌜H1' = H1⌝)%I as "%". 
      { iDestruct "mcs_high" as "(MCS_auth & HH & Hist & HfrH & MaxTS)". 
        iPoseProof (own_valid_2 _ _ _ with "[$HfrH] [$Hfr]") as "V_H".
        iDestruct "V_H" as %V_H.
        apply frac_agree_op_valid in V_H. destruct V_H as [_ V_H].
        apply leibniz_equiv_iff in V_H.
        by iPureIntro. } subst H1'.
      assert (tp = t) as H' by lia. 
      iAssert (⌜(k,tp) ∈ H1⌝)%I as "%". 
      { iDestruct "mcs_high" as "(MCS_auth & HH & mcs_high')".
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
      
      iModIntro. iSplitL "mcs_high mcs_abs".
      iExists T1, H1; iFrame.

      iModIntro. iSplitL "Hstar_reg HTD Hfr Hγt Domm_hγt".
      iNext. iExists H1. iFrame "Hfr".
      iExists TD1, hγt1; iFrame.
      
      iModIntro. iSplitL "Token Hth_sy".
      iNext. iExists H1. iFrame "Hth_sy". 
      iRight. iFrame "∗%".
      
      iModIntro. wp_pures. by rewrite H'.
  Qed.
  
  Lemma search_spec_high N γ_te γ_he γ_s γ_fr mcs_abs γ_td γ_ght (k: K) :
  ⊢ ⌜k ∈ KS⌝ -∗ 
      <<< ∀ t M, MCS_high N γ_te γ_he γ_s γ_fr mcs_abs γ_td γ_ght t M >>>
            search' #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N))
      <<<  ∃ (t': nat), MCS_high N γ_te γ_he γ_s γ_fr mcs_abs γ_td γ_ght t M 
                        ∗ ⌜M !!! k = t'⌝, RET #t' >>>.
  Proof.
    iIntros "%" (Φ) "AU". rename H0 into k_in_KS.
    iApply fupd_wp. 
    iMod "AU" as (T0 M0)"[H [Hab _]]".
    iDestruct "H" as (H0)"(MCS & M_eq_H & #HInv & #HInv_h)".
    iMod ("Hab" with "[MCS M_eq_H]") as "AU".
    iExists H0. iFrame "∗#". iModIntro.
    awp_apply search_spec_intermediate; try done.
    rewrite /atomic_acc /=. iMod "AU" as (T1 M1)"[H HAU]".
    iDestruct "H" as (H1)"(MCS & M_eq_H & _)".
    iModIntro. iExists T1, H1. iFrame "MCS". iSplit.
    { iIntros "MCS". iDestruct "HAU" as "[Hab _]".
      iMod ("Hab" with "[MCS M_eq_H]") as "AU".
      iExists H1. iFrame "∗#". by iModIntro. }
    iIntros (tr)"(MCS & %)". rename H2 into H_k.   
    iDestruct "M_eq_H" as %M_eq_H.
    iAssert (⌜M1 !!! k = tr⌝)%I as "M_k".
    { iPureIntro. by rewrite <-M_eq_H. }
    iDestruct "HAU" as "[_ Hcomm]".
    iSpecialize ("Hcomm" $! tr).
    iMod ("Hcomm" with "[MCS]") as "HΦ". 
    iFrame "M_k". iExists H1. iFrame "∗#%".
    by iModIntro.
  Qed.
  
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
      rename H0 into vp_notin_H.
      destruct (decide ((k', vp) ∈ H1 ∪ {[(k, T)]})).
      + assert ((k',vp) = (k,T)) as H'. 
        { clear -vp_notin_H e. set_solver. }
        inversion H'. subst k' vp.
        iDestruct ("Pau" with "P") as ">AU".
        iMod "AU" as (t H1')"[MCS [_ Hclose]]". set_solver.
        iAssert (⌜H1' = H1 ∪ {[(k, T)]}⌝)%I as "%".
        { iPoseProof (MCS_agree with "[$MCS_auth] [$MCS]") as "(% & %)".
          by iPureIntro. } subst H1'.
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
  
  
  Lemma upsert_spec_high N γ_te γ_he γ_s γ_fr mcs_abs γ_td γ_ght (k: K) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
            <<< ∀ t M, MCS_high N γ_te γ_he γ_s γ_fr mcs_abs γ_td γ_ght t M >>> 
                   upsert #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N))
            <<< MCS_high N γ_te γ_he γ_s γ_fr mcs_abs γ_td γ_ght 
                        (t + 1) (<[k := t]> M), RET #() >>>.
  Proof.
    iIntros "%" (Φ) "AU". rename H0 into k_in_KS.
    iApply fupd_wp. 
    iMod "AU" as (T0 M0)"[H [Hab _]]".
    iDestruct "H" as (H0)"(MCS & M_eq_H & #HInv & #HInv_h)".
    iMod ("Hab" with "[MCS M_eq_H]") as "AU".
    iExists H0. iFrame "∗#". iModIntro.
    iAssert (ghost_update_protocol N γ_te γ_he 
                (protocol_conc N γ_te γ_he γ_fr γ_td γ_ght) k)%I 
                  as "Ghost_updP".
    { iIntros (T' H')"H1_k MCS_auth".
      iDestruct "H1_k" as %H1_k.
      iIntros "Protocol_conc". 
      iDestruct "Protocol_conc" as (TD hγt)"(HTD & Hγt & Domm_hγt & Hstar_reg)".
      iMod (ghost_update_registered k T' with 
              "[] [MCS_auth] [$Hstar_reg]") 
                 as "(Hstar_reg & MCS_auth)"; try done.
      iModIntro. iFrame "MCS_auth".
      iExists TD, hγt. iFrame. }
    awp_apply upsert_spec; try done.
    iApply (aacc_aupd_commit with "AU"). set_solver.
    iIntros (T1 M1)"MCS_high".
    iDestruct "MCS_high" as (H1)"(MCS & M_eq_H & _)".
    iDestruct "M_eq_H" as %M_eq_H.
    iAaccIntro with "MCS".
    { iIntros "MCS". iModIntro.
      iSplitL; try eauto with iFrame.
      iExists H1; iFrame "∗#%". } 
    iIntros "(MCS & %)". rename H2 into maxTS.
    iModIntro. iSplitL.
    iExists (H1 ∪ {[k, T1]}). iFrame "∗#".
    { iPureIntro. apply symmetry. 
      apply map_of_set_insert_eq; try done.
      apply maxTS. }
    iIntros "HΦ"; iModIntro; try done.
  Qed.
              
End multicopy_high.
              
              




