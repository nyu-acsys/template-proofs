From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Import general_multicopy util.

Section upsert_proof.
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
        iMod "AU" as (t M)"[MCS_high [_ Hclose]]". set_solver.
        iDestruct "MCS_high" as (H1')"(MCS & %)".
        rename H into Def_M.
        iAssert (⌜H1' = H1 ∪ {[(k, T)]}⌝)%I as "%".
        { iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
          unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
          by iDestruct "MCS" as "(_ & H')". by iPureIntro. } subst H1'.
        iAssert (⌜M !!! k = T⌝)%I as "%".
        { iPureIntro. by rewrite <-Def_M. }
        iMod ("Hclose" with "[MCS]") as "HQ".
        { iFrame "%". iExists (H1 ∪ {[(k, T)]}).
          iFrame "∗%". }
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


  Lemma upsert_spec N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr lc r 
                    (k: K) γ_td γ_ght :
    ⊢ (*⌜N1 ## N2⌝ -∗ ⌜N2 ## thN⌝ -∗ ⌜N1 ## thN⌝ -∗*) ⌜k ∈ KS⌝ -∗ 
        mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr lc r -∗
          helping_inv N γ_te γ_he γ_fr γ_td γ_ght -∗
            <<< ∀ t M, MCS_high γ_te γ_he t M >>> 
                   upsert lc r #k @ ⊤ ∖ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N))
            <<< MCS_high γ_te γ_he (t + 1) (<[k := t]> M), RET #() >>>.
  Proof.
    iIntros "%". iLöb as "IH".
(*    rename H into Disj_ns1. rename H0 into Disj_ns2.
    rename H1 into Disj_ns3. *) 
    rename H into k_in_KS.    
    iIntros "#HInv #HInv_h" (Φ) "AU". wp_lam.
    iApply fupd_wp. 
    (** Open invariant to establish root node in footprint **)
    iInv "HInv" as ">H".
    iDestruct "H" as (T0 H0 hγ0 I0 J0) "(Hglob & Hstar)".
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & Ht & HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & #FP_r & Max_ts & domm_IR & domm_Iγ)".
    iModIntro. iSplitR "AU". iNext. 
    iExists T0, H0, hγ0, I0, J0. iFrame "∗ #". iModIntro.
    (** Lock the node r **)
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cr Br Qr)"HnP_n". iModIntro. wp_pures.
    iDestruct "HnP_n" as (γ_er γ_cr γ_br γ_qr γ_cirr es T)
                      "(node_r & HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iEval (rewrite decide_True) in "HnP_t".
    wp_apply (readClock_spec with "[HnP_t]"); try done.
    iIntros "HnP_t". wp_pures.
    wp_apply (addContents_spec with "node_r").
    iIntros (b Cr')"(node_r & Hif)".
    (** Case analysis on whether addContents is successful **)
    destruct b; last first.
    - (** Case : addContents fails. Unlock root node and apply 
                 inductive hypothesis IH **) 
      iDestruct "Hif" as %HCr. replace Cr'. wp_pures.
      awp_apply (unlockNode_spec_high with "[] [] [-AU]"); try done.
      { iExists γ_er, γ_cr, γ_br, γ_qr, γ_cirr, es, T.
        iFrame. iEval (rewrite decide_True); try done. }
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. wp_pures.
      by iApply "IH".
    - (** Case : addContent successful **)
      (** Linearization Point: open invariant and update the resources **)
      wp_pures. wp_bind (incrementClock _)%E.
      wp_lam. iDestruct "HnP_t" as "(HnP_T & HnP_lc)".
      unfold clock. wp_load. wp_pures. 
      iInv "HInv" as ">H". 
      iDestruct "H" as (T1 H1 hγ1 I1 J1) "(Hglob & Hstar)".
      iInv "HInv_h" as (H1' TD hγt)"(>Hfr & >HTD & >Hγt & >Domm_hγt & Hstar_reg)".
      wp_store. 
      
      iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & Ht & HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & _ & Max_ts & domm_IR & domm_Iγ)".
      iDestruct "Hif" as %HCr.
      iAssert (⌜T = T1⌝)%I as %HT. 
      { iPoseProof ((own_valid_2 _ _ _) with "[$HnP_T] [$Ht]") as "H'".
        iDestruct "H'" as %H'. 
        pose proof (auth_auth_frac_op_inv _ _ _ _ H') as H''.
        inversion H''. by iPureIntro. } replace T1.
      iCombine "Ht HnP_T" as "HT".  
      iMod (own_update (γ_t) (● (MaxNat (T))) 
               (● (MaxNat (T+1))) with "HT") as "HT".
      { apply (auth_update_auth _ _ (MaxNat (T+1))).
        apply max_nat_local_update. simpl. lia. }
      iDestruct "HT" as "(Ht & HnP_T)".  

      iAssert (own γ_t (●{1 / 2} MaxNat (T + 1)) ∗ clock lc (T + 1))%I
        with "[HnP_T HnP_lc]" as "HnP_t".
      { iFrame "HnP_T". unfold clock.
        assert (#(T+1)%nat = #(T+1)) as H'.
        apply f_equal. apply f_equal. lia. 
        by rewrite H'. }  

      iPoseProof ((auth_own_incl γ_s H1 _) with "[$HH $HnP_C]") as "%".
      rename H into Cr_sub_H1. apply gset_included in Cr_sub_H1.
      iDestruct "Max_ts" as %Max_tsH1.
      (** Re-establish maxTS for updated T and H **)
      assert (maxTS (T+1) (H1 ∪ {[(k, T)]})) as Max_ts.
      { split. intros k' t' H.
        assert (((k',t') ∈ H1) ∨ (k' = k ∧ t' = T)) as Hor by set_solver.
        destruct Hor as [Hor | Hor]. 
        destruct Max_tsH1 as [Max_tsH1 _].
        pose proof Max_tsH1 k' t' Hor as Hres. lia.
        destruct Hor as [_ Hor]. replace t'. lia.
        destruct Max_tsH1 as [_ Max_tsH1]. lia. }       
      iAssert (⌜set_of_map Cr' ⊆ H1 ∪ {[(k,T)]}⌝)%I as %Cr_sub_H1'.
      { iPureIntro. replace Cr'.
        pose proof (set_of_map_insert_subseteq Cr k T) as H'.
        assert (set_of_map Cr = set_of_map Cr) as H'' by done. 
        set_solver. }
      (** Update the (● H) resource **)  
      iMod (own_update γ_s (● H1) (● (H1 ∪ {[(k,T)]})) with "[$HH]") as "HH".
      { apply (auth_update_auth _ _ (H1 ∪ {[(k,T)]})).
        apply gset_local_update. set_solver. }
      iMod (own_update γ_s (● (H1 ∪ {[(k, T)]})) 
             (● (H1 ∪ {[(k, T)]}) ⋅ ◯ (set_of_map Cr')) with "[$HH]") as "HH".
      { apply (auth_update_alloc _ (H1 ∪ {[(k,T)]}) (set_of_map Cr')).
        apply local_update_discrete. intros m Valid_H1 H1_eq.
        split; try done. rewrite /(ε ⋅? m) in H1_eq.
        destruct m. rewrite gset_op_union in H1_eq. 
        rewrite left_id in H1_eq *; intros H1_eq.
        rewrite <-H1_eq. 
        rewrite /(set_of_map Cr' ⋅? Some (H1 ∪ {[k, T]})).
        rewrite gset_op_union.
        rewrite /(ε) in H1_eq. unfold ucmra_unit in H1_eq.
        simpl in H1_eq.
        assert ((k,T) ∈ set_of_map Cr') as H'.
        { replace Cr'. apply set_of_map_member.
          apply lookup_insert. } 
        clear - H' Cr_sub_H1 Cr_sub_H1'. set_solver.
        exfalso. clear -H1_eq. set_solver. }
      (** Re-establish history_init **)   
      iAssert (⌜history_init (H1 ∪ {[(k, T)]})⌝)%I with "[Hist]" as "Hist".
      { iDestruct "Hist" as %Hist.
        unfold history_init. iPureIntro.
        clear -Hist k_in_KS. intros k' Hk'.
        pose proof Hist k' Hk' as H'. set_solver. }  
      iDestruct "HnP_C" as "_".  
      iDestruct "HH" as "(HH & HnP_C)".   
      iAssert (⌜r ∈ domm I1⌝)%I as %r_in_I.
      { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
      iDestruct "Hstar" as "(H_r & Hstar')".
      iDestruct "H_r" as (br Cr'' Br'' Qr'')"(Hl_r & Hlif_r & HnS_r)".
      iAssert (⌜br = true⌝)%I as %Hbr.
      { destruct br; try done.
        iDestruct "Hlif_r" as 
            (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T')"(node' & _)".
        iPoseProof ((node_sep_star r r) with "[$]") as "%".
        contradiction. } replace br.
      iDestruct "HnS_r" as (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' Ir Jr) 
                    "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                              & HnS_cl & HnS_oc & HnS_if & HnS_star & Hφ)".
      iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                as "(% & % & % & % & %)".
      subst γ_er'. subst γ_cr'. subst γ_br'. subst γ_qr'. subst γ_cirr'.
      iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
      destruct H as [Hes [Hc [Hb Hq]]]. 
      subst es'. subst Cr''. subst Br''. subst Qr''.
      (** Update contents-in-reach of r **)
      set (Br' := <[k := T]>Br).
      assert (Br' = <[k := T]>Br) as HBr'. try done.
      iEval (rewrite decide_True) in "HnS_if".
      iDestruct "HnS_if" as "(% & %)". 
      rename H into Br_eq_H1. rename H2 into Infz_Ir.
      iAssert (⌜Br' = map_of_set (H1 ∪ {[(k, T)]})⌝)%I as %Br'_eq_H1.
      { iPureIntro.
        apply map_of_set_insert_eq; try done.
        intros t. 
        destruct Max_tsH1 as [Max_tsH1 _].
        by pose proof Max_tsH1 k t. }
      iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto) in "HnS_star".
      iDestruct "HnS_star" as "(Hk & HnS_star')".
      iAssert (⌜Br !!! k ≤ T⌝)%I as %Br_le_T. 
      { iDestruct "Hφ" as "(_&_&_&_&_&_&%&_)".
        iPureIntro. rename H into H'.
        by pose proof H' k k_in_KS. }
      iMod (own_update (γ_cirr !!! k) (● (MaxNat (Br !!! k))) 
                (● (MaxNat (Br' !!! k))) with "Hk") as "Hk".
      { apply (auth_update_auth _ _ (MaxNat (Br' !!! k))).
        apply max_nat_local_update.
        simpl. rewrite HBr'.
        by rewrite lookup_total_insert. }        
      iAssert ([∗ set] k0 ∈ KS, own (γ_cirr !!! k0) 
                  (● {| max_nat_car := Br' !!! k0 |}))%I 
          with "[HnS_star' Hk]" as "HnS_star".
      { iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto).
        iFrame "Hk".        
        iApply (big_opS_proper 
             (λ y, own (γ_cirr !!! y) (● {| max_nat_car := Br' !!! y |}))
             (λ y, own (γ_cirr !!! y) (● {| max_nat_car := Br !!! y |})) 
             (KS ∖ {[k]})).
        intros x Hx. assert (x ≠ k) as H' by set_solver.
        iFrame. iSplit. 
        iIntros "H". iEval (rewrite HBr') in "H".
        assert (<[k:=T]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'') in "H".       
        iIntros "H". iEval (rewrite HBr').
        assert (<[k:=T]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'').
        done. }
      iMod ((frac_update γ_er γ_cr γ_br γ_qr es Cr Br Qr es Cr' Br' Qr) 
                  with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".
      iDestruct "Inf_J" as %Inf_J.
      iPoseProof ((auth_own_incl γ_J J1 Jr) with "[HR HnS_si]")
                                    as (Ro) "%". 
      { unfold singleton_interfaces_ghost_state.
        iDestruct "HnS_si" as "(_ & H' & _)". 
        iFrame. } rename H into Incl_J1.
      iPoseProof (own_valid with "HR") as "%".
      rename H into Valid_J1.
      iAssert (⌜domm Jr = {[r]}⌝)%I as "%".
      { by iDestruct "HnS_si" as "(_&_&_&H')". }
      rename H into Domm_Jr.
      iAssert (⌜φ0 es Qr⌝ ∗ ⌜φ1 Br' Cr' Qr⌝ ∗ ⌜φ2 r Br' Ir⌝ 
        ∗ ⌜φ3 r Br' Jr⌝ ∗ ⌜φ4 r Jr⌝ ∗ ⌜φ5 Br' Qr⌝ 
        ∗ ⌜φ6 Br' (T+1)⌝ ∗ ⌜φ7 r es Jr Qr⌝ ∗ ⌜φ8 r Ir⌝)%I 
            with "[Hφ]" as "Hφ".
      { iDestruct "Hφ" as %Hφ. 
        destruct Hφ as [Hφ0 [Hφ1 [Hφ2 [Hφ3 [Hφ4 [Hφ5 [Hφ6 [Hφ7 Hφ8]]]]]]]].
        iPureIntro. repeat split; try done.
        - destruct (decide (k0 = k)).
          + subst k0. subst Cr' Br'.
            rewrite !lookup_insert. try done.
          + subst Cr' Br'. 
            rewrite !lookup_insert_ne; try done.
            by pose proof Hφ1 k0 as [H' _].
        - destruct (decide (k0 = k)).
          + subst k0. subst Cr' Br'.
            rewrite !lookup_insert.
            destruct Max_tsH1 as [_ H'].
            intros H''; inversion H''.
          + subst Cr' Br'. 
            rewrite !lookup_insert_ne; try done.
            by pose proof Hφ1 k0 as [_ H'].
        - intros k' t' HKS Hins.
          pose proof Infz_Ir r as Infz_Ir.
          rewrite Infz_Ir in Hins.
          exfalso. clear -Hins. set_solver.
        - intros k' HKS. right.
          apply (inset_monotone J1 Jr Ro); try done.
          by rewrite <-auth_auth_valid.
          pose proof Inf_J r k' HKS as Inf_J.
          by rewrite decide_True in Inf_J.
          rewrite Domm_Jr. clear. set_solver.
        - intros k' HKS. subst Br'. destruct (decide (k' = k)).
          + subst k'. rewrite lookup_total_insert.
            apply (Nat.le_trans _ (Br !!! k) _); try done.
            apply Hφ5; try done.
          + rewrite lookup_total_insert_ne; try done.
            apply Hφ5; try done.    
        - intros k' HKS. destruct (decide (k' = k)).
          + subst k' Br'. rewrite lookup_total_insert; lia.
          + subst Br'. rewrite lookup_total_insert_ne; try done.
            pose proof Hφ6 k' HKS. clear -H. 
            apply (Nat.le_trans _ T _); try done. lia. }
            
      iAssert (⌜H1' = H1⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$Hfr] [$HfrH]") as "%".
        rename H into H'. 
        apply frac_agree_op_valid in H'. destruct H' as [_ H'].
        apply leibniz_equiv_iff in H'. by iPureIntro. } subst H1'.
      iCombine "Hfr HfrH" as "H'". 
      iEval (rewrite <-frac_agree_op) in "H'". 
      iEval (rewrite Qp_half_half) in "H'".
      iMod ((own_update (γ_fr) (to_frac_agree 1 H1) 
                  (to_frac_agree 1 (H1 ∪ {[(k,T)]}) )) with "[$H']") as "H'".
      { apply cmra_update_exclusive. 
        unfold valid, cmra_valid. simpl. unfold prod_valid.
        split; simpl; try done. }
      iEval (rewrite <-Qp_half_half) in "H'".
      iEval (rewrite frac_agree_op) in "H'".  
      iDestruct "H'" as "(HfrH & Hfr)".
            
      (** Linearization **)    
      iMod "AU" as (t' M)"[MCS_high [_ Hclose]]".
      iDestruct "MCS_high" as (H1')"(MCS & %)". 
      rename H into H1_eq_M.
      iAssert (⌜t' = T⌝)%I as %Ht'. 
      { iPoseProof ((auth_agree γ_te) with "[MCS_auth] [MCS]") as "%".
        unfold MCS_auth. by iDestruct "MCS_auth" as "(H' & _)".
        by iDestruct "MCS" as "(H' & _)".
        by iPureIntro. } subst t'.
      iAssert (⌜H1' = H1⌝)%I as "%".
      { iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
        unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
        by iDestruct "MCS" as "(_ & H')".
        by iPureIntro. } subst H1'.
      iDestruct "MCS" as "(MCS◯t & MCS◯h)".
      iDestruct "MCS_auth" as "(MCS●t & MCS●h)".
      iMod ((auth_excl_update γ_te (T+1) T T) with "MCS●t MCS◯t") 
                                          as "(MCS●t & MCS◯t)".
      iMod ((auth_excl_update γ_he (H1 ∪ {[(k, T)]}) H1 H1) with "MCS●h MCS◯h") 
                                          as "(MCS●h & MCS◯h)".
      iCombine "MCS◯t MCS◯h" as "MCS".
      iCombine "MCS●t MCS●h" as "MCS_auth".
      iAssert (MCS_high γ_te γ_he (T + 1) (<[k:=T]> M))%I
        with "[MCS]" as "MCS_high".
      { iExists (H1 ∪ {[(k, T)]}). iFrame.
        iPureIntro. apply map_eq. 
        intros k'. destruct (decide (k' = k)).
        - subst k'. rewrite (map_of_set_lookup _ _ T).
          by rewrite lookup_insert. set_solver.
          intros t. rewrite elem_of_union.
          intros [H' | H'].
          destruct Max_tsH1 as [Max_tsH1 _].
          pose proof Max_tsH1 k t H' as H''; clear -H''; lia.
          rewrite elem_of_singleton in H'*; intros H'.
          inversion H'. lia.          
        - rewrite map_of_set_union_ne; try done.
          rewrite lookup_insert_ne.
          rewrite map_eq_iff in H1_eq_M*; intros H1_eq_M.
          try done. done. }      
      iMod ("Hclose" with "MCS_high") as "HΦ".

      iMod (ghost_update_registered k T with 
            "[] [MCS_auth] [$Hstar_reg]") 
                as "(Hstar_reg & MCS_auth)"; try done.
      { pose proof map_of_set_lookup (H1 ∪ {[k, T]}) k T as H'.
        iPureIntro. rewrite lookup_total_alt.
        rewrite H'. by simpl. clear; set_solver.
        intros t. rewrite elem_of_union.
        clear H'. intros [H' | H'].
        destruct Max_tsH1 as [Max_tsH1 _].
        pose proof Max_tsH1 k t H' as H''; clear -H''; lia.
        rewrite elem_of_singleton in H'*; intros H'.
        inversion H'. lia. }          
      
      
      iModIntro.
      iSplitL "Hfr HTD Hγt Domm_hγt Hstar_reg".
      { iNext. iExists (H1 ∪ {[(k, T)]}), TD, hγt. iFrame. } 
      
      iModIntro.
      iSplitR "HΦ node_r HnP_gh HnP_t HnP_C HnP_frac".
      { iNext. iExists (T+1), (H1 ∪ {[(k, T)]}), hγ1, I1, J1.
        iFrame "∗ %".   
        rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
        iSplitR "Hstar'".
        { iExists true, Cr', Br', Qr. iFrame.
          iExists γ_er, γ_cr, γ_br, γ_qr, γ_cirr, es, Ir, Jr.
          iFrame "∗#". iEval (rewrite decide_True). 
          iFrame "%∗". }        
        iApply (big_sepS_mono 
                  (λ y, ∃ (bn : bool) (Cn Bn Qn : gmap K natUR),
                          general_multicopy.lockLoc y ↦ #bn
                        ∗ (if bn then True
                           else nodePred γ_gh γ_t γ_s lc r y Cn Bn Qn)
                        ∗ nodeShared γ_I γ_J γ_f γ_gh r y Cn Bn Qn H1 T )%I
                  (λ y, ∃ (bn : bool) (Cn Bn Qn : gmap K natUR),
                          general_multicopy.lockLoc y ↦ #bn
                        ∗ (if bn then True
                           else nodePred γ_gh γ_t γ_s lc r y Cn Bn Qn)
                        ∗ nodeShared γ_I γ_J γ_f γ_gh r y Cn Bn Qn 
                                                (H1 ∪ {[(k, T)]}) (T + 1))%I
                  (domm I1 ∖ {[r]})); try done.
        intros y y_dom. assert (y ≠ r) as Hy by set_solver. iFrame.
        iIntros "Hstar". iDestruct "Hstar" as (b C B Q)"(Hl & Hlif & HnS)".
        iExists b, C, B, Q. iFrame. 
        iDestruct "HnS" as (γ_e γ_c γ_b γ_q γ_cir esy Iy Ry)
                    "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
                              & HnS_cl & HnS_oc & HnS_if & HnS_star 
                              & Hφ0 & Hφ1 & Hφ2 & Hφ3 & Hφ4 & Hφ6 & Hφ7)".
        iExists γ_e, γ_c, γ_b, γ_q, γ_cir, esy, Iy, Ry. iFrame.
        iDestruct "Hφ6" as %Hφ6.
        destruct (decide (y = r)); try done. 
        iPureIntro. split; try done.
        intros k' HKS. pose proof Hφ6 k' HKS. 
        apply (Nat.le_trans _ T _); try done. lia. } 
      wp_pures. 
      (** Unlock node r **) 
      awp_apply (unlockNode_spec_high with "[] [] 
        [HnP_gh HnP_t HnP_C HnP_frac node_r]") without "HΦ"; try done. 
      iExists γ_er, γ_cr, γ_br, γ_qr, γ_cirr, es, (T + 1).
      iFrame. by iEval (rewrite decide_True).
      iAaccIntro with ""; try done.
      iIntros "_". iModIntro; iIntros "HΦ"; try done.
      Unshelve. try done.
  Qed.      

End upsert_proof.
