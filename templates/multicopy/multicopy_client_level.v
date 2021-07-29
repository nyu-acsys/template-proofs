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

(** \overline{search} in the paper *)
Definition search' : val :=
  λ: "k",
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "vt'" := search "k" in
    resolve_proph: "p" to: "vt'";;
    "vt'".  

Section multicopy_client_level.
  Context {Σ} `{heapG Σ, !multicopyG Σ}.
  Notation iProp := (iProp Σ).

  (** Low-level specs of multicopy operations *)

  Parameter search_recency: ∀ N γ_te γ_he γ_s Prot Inv_tpl k v0 t0, 
    ⊢ ⌜k ∈ KS⌝ -∗ 
        mcs_inv N γ_te γ_he γ_s Prot Inv_tpl -∗
          SR γ_s (k, v0, t0) -∗
              <<< True >>> 
                  search #k @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ (v: V) (t: TS), SR γ_s (k, v, t) ∗ ⌜t0 ≤ t⌝ , RET (#v, #t) >>>.

  Parameter upsert_spec: ∀ N γ_te γ_he γ_s Prot Inv_tpl k (v: V),
    ⊢ ⌜k ∈ KS⌝ -∗ 
        (ghost_update_protocol N γ_te γ_he Prot k) -∗ 
          mcs_inv N γ_te γ_he γ_s Prot Inv_tpl -∗
              <<< ∀ t H, MCS γ_te γ_he t H >>> 
                     upsert #k #v @ ⊤ ∖ (↑(mcsN N))
              <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k, v, t)]}), RET #() >>>.
                
  (** Proof of high-level specs for multicopy opeartions *)                

  Lemma search_spec_intermediate N γ_te γ_he γ_s Inv_tpl γ_td γ_ght (k: K) :
  ⊢ ⌜k ∈ KS⌝ -∗ 
      mcs_inv N γ_te γ_he γ_s (Prot_help N γ_te γ_he γ_td γ_ght) Inv_tpl -∗ 
          <<< ∀ t H, MCS γ_te γ_he t H >>>
                search' #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(threadN N))
          <<<  ∃ (vt: V * TS), MCS γ_te γ_he t H 
                            ∗ ⌜map_of_set H !!! k = vt⌝, RET (#vt.1, #vt.2) >>>.
  Proof.
    iIntros "% #HInv" (Φ) "AU". wp_lam.
    rename H0 into k_in_KS.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vt)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 VTTypedProph); first done.
    iIntros (vtp p)"Hproph". wp_pures. 
    iApply fupd_wp.
    iInv "HInv" as (T0 H0) "(mcs_high & Htpl)".
    iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & >Uniq & Prot)".
    iAssert (⌜∃ v0 t0, ((k, v0, t0) ∈ H0 ∧ (∀ v t, (k, v, t) ∈ H0 → t ≤ t0) 
                ∧ map_of_set H0 !! k = Some (v0, t0))⌝)%I as "%".
    { pose proof (map_of_set_lookup_cases H0 k) as H'.
      destruct H' as [H' | H']; try done.
      iDestruct "Hist" as %Hist.
      destruct H' as [H' _].
      pose proof H' 0%Z 0 as H'.
      pose proof Hist k k_in_KS as Hist.
      contradiction. }

    destruct H1 as [v0 [t0 [kt0_in_H [Max_t0 H_k]]]].
    iMod (own_update γ_s (● H0) (● H0 ⋅ ◯ {[(k, v0, t0)]}) with "[$HH]") as "HH".
    { apply (auth_update_frac_alloc _ H0 ({[(k, v0, t0)]})).
      apply gset_included. clear -kt0_in_H. set_solver. }
    iDestruct "HH" as "(HH & #mcs_sr)".
                     
    destruct (decide (vtp.2 ≤ t0)).
    - assert ((vtp.2 < t0) ∨ vtp.2 = t0) as H' by lia.
      destruct H' as [Hcase' | Hcase'].
      + iModIntro. iSplitR "AU Hproph".
        iNext; iExists T0, H0; iFrame.
        iModIntro.
        awp_apply search_recency; try done.
        iAaccIntro with ""; try done.
        { iIntros "_". iModIntro; try eauto with iFrame. } 
        iIntros (v t) "(Hkt & %)". rename H1 into t0_le_t.
        iModIntro. wp_pures.
        wp_apply (typed_proph_wp_resolve1 VTTypedProph with "Hproph"); try done.
        wp_pures. iModIntro. iIntros "%". rename H1 into tp_eq_t.
        clear -tp_eq_t Hcase' t0_le_t. rewrite tp_eq_t in Hcase'.
        simpl in Hcase'. exfalso; lia.
      + iMod "AU" as (T' H') "[MCS [_ Hcomm]]".
        set_solver.
        iAssert (⌜T' = T0 ∧ H' = H0⌝)%I as "%". 
        { iPoseProof (MCS_agree with "[$MCS_auth] [$MCS]") as "(% & %)".
          by iPureIntro. }
        destruct H1 as [H'' H''']. subst T' H'.
        assert (map_of_set H0 !!! k = (v0, t0)) as M_k.
        { rewrite lookup_total_alt. rewrite H_k.
          by simpl. }
        iSpecialize ("Hcomm" $! (v0, t0)). 
        iMod ("Hcomm" with "[MCS]") as "HΦ".
        { iFrame. by iPureIntro. } 
        iModIntro. iSplitR "HΦ Hproph".
        iNext; iExists T0, H0; iFrame.
        iModIntro.
        awp_apply search_recency without "HΦ"; try done.
        iAaccIntro with ""; try done.
        { iIntros "_". iModIntro; try eauto with iFrame. } 
        iIntros (v t) "(#Hkt & %)". rename H1 into t0_le_t.
        iModIntro. iIntros "HΦ". wp_pures.
        wp_apply (typed_proph_wp_resolve1 VTTypedProph with "Hproph"); try done.
        wp_pures. iModIntro. iIntros "%". rename H1 into tp_eq_t. 
        wp_pures.
        iInv "HInv" as (T1 H1) "(mcs_high & Htpl)".
        iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & >Uniq & Prot)".
        iDestruct "Uniq" as %Uniq.
        iPoseProof (auth_own_incl γ_s H1 _ with "[$HH $mcs_sr]") as "%".
        rename H2 into vt0_sub_H1.
        apply gset_included in vt0_sub_H1.
        assert ((k,v0,t0) ∈ H1) as vt0_in_H1 by set_solver.
        iPoseProof (auth_own_incl γ_s H1 _ with "[$HH $Hkt]") as "%".
        rename H2 into vt_sub_H1.
        apply gset_included in vt_sub_H1.
        assert ((k,v,t) ∈ H1) as vt_in_H1 by set_solver.
        iModIntro. iSplitR "HΦ".
        iNext; iExists T1, H1; iFrame"∗%". iModIntro.
        
        assert (vtp.2 = t) as H'.
        { rewrite tp_eq_t. simpl. by lia. }
        rewrite <-H'. rewrite Hcase'.
        rewrite <-H' in vt_in_H1; rewrite Hcase' in vt_in_H1.
        pose proof Uniq k v0 v t0 vt0_in_H1 vt_in_H1 as Uniq.
        by rewrite Uniq.
    - assert (vtp.2 > t0) by lia. rename H1 into tp_gr_t0.
      iDestruct "Prot" as (R hγt)"(>HR & >Hγt 
                                      & >Domm_hγt & Hstar_reg)".
      iAssert (▷ (⌜tid ∉ R⌝ 
                ∗ ([∗ set] t_id ∈ R, Reg N γ_te γ_he γ_ght H0 t_id) 
                ∗ proph1 tid vt))%I with "[Hstar_reg Htid]" 
                as "(>% & Hstar_reg & Htid)".
      { destruct (decide (tid ∈ R)); try done.
        - iEval (rewrite (big_sepS_elem_of_acc _ (R) tid); 
                                last by eauto) in "Hstar_reg".
          iDestruct "Hstar_reg" as "(Hreg & Hstar_reg')".
          iDestruct "Hreg" as (? ? ? ? ? ? ?)"(H' & _)".
          iAssert (▷ False)%I with "[H' Htid]" as "HF".
          iApply (proph1_exclusive tid with "[Htid]"); try done.
          iNext. iExFalso; try done.
        - iFrame. iNext. by iPureIntro. }
      rename H1 into tid_notin_R.
      iMod (own_update γ_td (● R) (● (R ∪ {[tid]})) with "[$HR]") as "HR".
      { apply (auth_update_auth _ _ (R ∪ {[tid]})).
        apply gset_local_update. set_solver. }
      iMod (own_update γ_td (● (R ∪ {[tid]})) (● (R ∪ {[tid]}) ⋅ ◯ {[tid]}) 
                with "[$HR]") as "(HR & #FP_t)".
      { apply (auth_update_frac_alloc _ (R ∪ {[tid]}) ({[tid]})).
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
        rewrite <-Domm_hγt in tid_notin_R.
        by rewrite not_elem_of_dom in tid_notin_R*; 
        intros tid_notin_R. }
      iDestruct "Hγt" as "(Hγt & #Hreg_gh)".  
                  
      iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
      iMod (own_alloc (Excl ())) as (γ_tk') "Token"; first try done.
      assert (∀ v, (k, v, vtp.2) ∉ H0) as ktp_notin_H. 
      { intros v. destruct (decide ((k, v, vtp.2) ∈ H0)); try done.
        pose proof Max_t0 v vtp.2 e as H'.
        clear -H' tp_gr_t0. lia. } 
      iMod (inv_alloc (threadN N) _
              (∃ H, State γ_sy tid γ_tk' AU_later (Φ) H k vtp) 
                                    with "[AU Hreg_sy1]") as "#HthInv".
      { iNext. iExists H0. iFrame "Hreg_sy1". iLeft. 
        unfold Pending. iFrame. by iPureIntro. }

      iModIntro. iSplitR "Hproph Token". iNext.
      iExists T0, H0. iFrame "Htpl". iFrame.
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists AU_later, Φ, k, vtp, vt, γ_tk', γ_sy. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.
            
      iModIntro. awp_apply search_recency; try done.
      iAaccIntro with ""; try done.
      { iIntros "_". iModIntro; try eauto with iFrame. } 
      iIntros (v t) "(#Hkt & %)". rename H1 into t0_le_t.
      iModIntro. wp_pures.
      wp_apply (typed_proph_wp_resolve1 VTTypedProph with "Hproph"); try done.
      wp_pures. iModIntro. iIntros "%". rename H1 into tp_eq_t.
      iApply fupd_wp.
      iInv "HthInv" as (H1)"(>Hth_sy & Hth_or)".
      iInv "HInv" as (T1 H1') "(mcs_high & Htpl)".
      iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & >Uniq & Prot)".
      iDestruct "Prot" as (R1 hγt1)"(>HR & >Hγt 
                                      & >Domm_hγt & Hstar_reg)".
      iAssert (⌜tid ∈ R1⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HR] [$FP_t]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro. set_solver. }
        
      iAssert (▷ (⌜H1' = H1⌝
               ∗ ([∗ set] t_id ∈ R1, Reg N γ_te γ_he γ_ght H1' t_id)
               ∗ own (γ_sy) (to_frac_agree (1 / 2) H1) ))%I
                with "[Hstar_reg Hth_sy]" as "(>% & Hstar_reg & >Hth_sy)". 
      { iEval (rewrite (big_sepS_elem_of_acc _ (R1) tid); 
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
      assert (vtp.2 = t) as H' by (rewrite tp_eq_t; simpl; lia). 
      iAssert (⌜(k, vtp.1, vtp.2) ∈ H1⌝)%I as "%". 
      { iPoseProof (own_valid_2 _ _ _ with "[$HH] [$Hkt]") as "H'".
        iDestruct "H'" as %H''.
        apply auth_both_valid_discrete in H''.
        destruct H'' as [H'' _].
        apply gset_included in H''.
        rewrite tp_eq_t; simpl.
        rewrite tp_eq_t in H'; simpl in H'.
        rewrite H'.
        iPureIntro; clear -H''; set_solver. }
      rename H0 into ktp_in_H1.
      iDestruct "Hth_or" as "[Hth_or | Hth_or]".
      { iDestruct "Hth_or" as "(? & >%)".
        exfalso. try done. }
      iDestruct "Hth_or" as "(Hth_or & >%)".  
      iDestruct "Hth_or" as "[Hth_or | >Hth_or]"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Hth_or]") as "%".
        exfalso; try done. }
      
      iModIntro. iSplitR "Hth_or Hth_sy Token".
      iExists T1, H1; iFrame.
      iNext. iExists R1, hγt1; iFrame.
      
      iModIntro. iSplitL "Token Hth_sy".
      iNext. iExists H1. iFrame "Hth_sy". 
      iRight. iFrame "∗%".
      
      iModIntro. wp_pures. iModIntro.
      iEval (rewrite tp_eq_t; simpl) in "Hth_or".
      assert (Z.to_nat t = t) as Ht by lia.
      by iEval (rewrite Ht) in "Hth_or".
  Qed.
  
  Lemma search_spec_high N γ_te γ_he γ_s Inv_tpl γ_td γ_ght (k: K) :
  ⊢ ⌜k ∈ KS⌝ -∗ 
      <<< ∀ t M, MCS_high N γ_te γ_he γ_s Inv_tpl γ_td γ_ght t M >>>
            search' #k @ ⊤ ∖ (↑(mcsN N) ∪ ↑(threadN N))
      <<<  ∃ (vt: V*TS), MCS_high N γ_te γ_he γ_s Inv_tpl γ_td γ_ght t M 
                        ∗ ⌜M !!! k = vt⌝, RET (#vt.1, #vt.2) >>>.
  Proof.
    iIntros "%" (Φ) "AU". rename H0 into k_in_KS.
    iApply fupd_wp. 
    iMod "AU" as (T0 M0)"[H [Hab _]]".
    iDestruct "H" as (H0)"(MCS & M_eq_H & #HInv)".
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
  
  Lemma ghost_update_registered (k: K) (v: V) (T: TS) (N: namespace) 
                (γ_te γ_he γ_ght: gname) 
                (H1: gset KVT) (R: gset proph_id)  :
        ⌜map_of_set (H1 ∪ {[k, v, T]}) !!! k = (v, T)⌝ -∗
           MCS_auth γ_te γ_he (T+1) (H1 ∪ {[(k, v, T)]}) -∗          
      ([∗ set] t_id ∈ R, Reg N γ_te γ_he γ_ght H1 t_id) 
        ={⊤ ∖ ↑(mcsN N)}=∗ 
      ([∗ set] t_id ∈ R, Reg N γ_te γ_he γ_ght 
                                      (H1 ∪ {[(k, v, T)]}) t_id)
       ∗ MCS_auth γ_te γ_he (T+1) (H1 ∪ {[(k, v, T)]}).
  Proof.
    iIntros "H1_k MCS_auth".
    iDestruct "H1_k" as %H1_k.
    iInduction R as [|x R' x_notin_R IH] "HInd" using set_ind_L; 
      auto using big_sepS_empty'.
    rewrite (big_sepS_delete _ ({[x]} ∪ R') x); last by set_solver.
    rewrite (big_sepS_delete _ ({[x]} ∪ R') x); last by set_solver.
    assert (({[x]} ∪ R') ∖ {[x]} = R') as HR'. set_solver.
    rewrite HR'.
    iIntros "(Hx & Hbigstar)". 
    iMod ("HInd" with "[$MCS_auth] Hbigstar") as "(H' & MCS_auth)".
    iFrame "H'".
    iDestruct "Hx" as (P Q k' vtp vt γ_tk γ_sy)
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
                  (to_frac_agree 1 (H1 ∪ {[(k, v, T)]}))) with "[$H']") as "H'".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid_instance.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "H'".
    iEval (rewrite frac_agree_op) in "H'".  
    iDestruct "H'" as "(Hreg_sy & Hth_sy)".

    iDestruct "Hstate" as "[Hpending | Hdone]".
    - iDestruct "Hpending" as "(P & >%)".
      rename H0 into vp_notin_H.
      destruct (decide ((k', vtp.1, vtp.2) ∈ H1 ∪ {[(k, v, T)]})).
      + assert ((k',vtp.1, vtp.2) = (k, v, T)) as H'. 
        { clear -vp_notin_H e. set_solver. }
        inversion H'. subst k'. rename H3 into Hv; rename H4 into Ht. 
        rewrite Hv Ht.
        iDestruct ("Pau" with "P") as ">AU".
        iMod "AU" as (t H1')"[MCS [_ Hclose]]". set_solver.
        iAssert (⌜H1' = H1 ∪ {[(k, v, T)]}⌝)%I as "%".
        { iPoseProof (MCS_agree with "[$MCS_auth] [$MCS]") as "(% & %)".
          by iPureIntro. } subst H1'.
        iSpecialize ("Hclose" $! (v,T)).  
        iMod ("Hclose" with "[MCS]") as "HQ".
        { iFrame "%∗". }
        iModIntro. iSplitL "Hth_sy HQ".
        iNext. iExists (H1 ∪ {[(k, v, T)]}). iFrame.
        iRight. iSplitL. iLeft. rewrite Hv Ht.
        by iEval (simpl) in "HQ".
        iPureIntro. rewrite Hv Ht. clear; set_solver.
        iModIntro. iFrame.
        iExists P, Q, k, vtp, vt, γ_tk, γ_sy.
        iFrame "∗#".
      + iModIntro. iSplitR "Hreg_proph Hreg_sy Hreg_gh MCS_auth".
        iNext. iExists (H1 ∪ {[(k, v, T)]}). iFrame.
        iLeft. iFrame. by iPureIntro.
        iModIntro. iFrame.             
        iExists P, Q, k', vtp, vt, γ_tk, γ_sy.
        iFrame "∗#".
    - iModIntro.
      iSplitR "Hreg_proph Hreg_sy Hreg_gh MCS_auth".
      iNext. iExists (H1 ∪ {[(k, v, T)]}). iFrame.
      iRight. iDestruct "Hdone" as "(HQ & %)".
      iFrame "HQ". iPureIntro. set_solver.
      iModIntro. iFrame. 
      iExists P, Q, k', vtp, vt, γ_tk, γ_sy.
      iFrame "∗#". 
  Qed.  
  
  
  Lemma upsert_spec_high N γ_te γ_he γ_s Inv_tpl γ_td γ_ght (k: K) (v: V):
    ⊢ ⌜k ∈ KS⌝ -∗ 
            <<< ∀ T M, MCS_high N γ_te γ_he γ_s Inv_tpl γ_td γ_ght T M >>> 
                   upsert #k #v @ ⊤ ∖ (↑(mcsN N) ∪ ↑(threadN N))
            <<< MCS_high N γ_te γ_he γ_s Inv_tpl γ_td γ_ght 
                        (T + 1) (<[k := (v,T)]> M), RET #() >>>.
  Proof.
    iIntros "%" (Φ) "AU". rename H0 into k_in_KS.
    iApply fupd_wp. 
    iMod "AU" as (T0 M0)"[H [Hab _]]".
    iDestruct "H" as (H0)"(MCS & M_eq_H & #HInv)".
    iMod ("Hab" with "[MCS M_eq_H]") as "AU".
    iExists H0. iFrame "∗#". iModIntro.
    iAssert (ghost_update_protocol N γ_te γ_he 
                (Prot_help N γ_te γ_he γ_td γ_ght) k)%I 
                  as "Ghost_updP".
    { iIntros (v' T' H')"H1_k MCS_auth".
      iDestruct "H1_k" as %H1_k.
      iIntros "Prot". 
      iDestruct "Prot" as (R hγt)"(HR & Hγt & Domm_hγt & Hstar_reg)".
      iMod (ghost_update_registered k v' T' with 
              "[] [MCS_auth] [$Hstar_reg]") 
                 as "(Hstar_reg & MCS_auth)"; try done.
      iModIntro. iFrame "MCS_auth".
      iExists R, hγt. iFrame. }
    awp_apply upsert_spec; try done.
    iApply (aacc_aupd_commit with "AU"). set_solver.
    iIntros (T1 M1)"MCS_high".
    iDestruct "MCS_high" as (H1)"(MCS & M_eq_H & _)".
    iDestruct "M_eq_H" as %M_eq_H.
    iAssert (⌜maxTS T1 H1⌝)%I as %maxTS.
    { by iDestruct "MCS" as "(_ & _ & % & _)". }
    iAssert (⌜unique_val H1⌝)%I as %Uniq.
    { by iDestruct "MCS" as "(_ & _ & _ & %)". }
    iAaccIntro with "MCS".
    { iIntros "MCS". iModIntro.
      iSplitL; try eauto with iFrame.
      iExists H1; iFrame "∗#%". } 
    iIntros "MCS". 
    iModIntro. iSplitL.
    iExists (H1 ∪ {[k, v, T1]}). iFrame "∗#".
    { iPureIntro. apply symmetry. 
      apply map_of_set_insert_eq; try done.
      apply maxTS. }
    iIntros "HΦ"; iModIntro; try done.
  Qed.
              
End multicopy_client_level.
