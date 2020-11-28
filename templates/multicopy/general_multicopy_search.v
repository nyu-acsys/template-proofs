From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Import general_multicopy.

Section search_proof.
  Context {Σ} `{!heapG Σ, !multicopyG Σ}.
  Notation iProp := (iProp Σ).  
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  Lemma traverse_spec N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r 
                          γ_en γ_cn γ_bn γ_qn γ_cirn n (k: K) t0 t1 :
    ⊢ ⌜k ∈ KS⌝ -∗ mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
        inFP γ_f n -∗ 
          own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]}) -∗ 
            own (γ_cirn !!! k) (◯ MaxNat t1) -∗ ⌜t0 ≤ t1⌝ -∗
              <<< ∀ t H, MCS γ_te γ_he t H >>> 
                  traverse #n #k @ ⊤ ∖ ↑N
              <<< ∃ (t': nat), MCS γ_te γ_he t H ∗ ⌜(k, t') ∈ H⌝ 
                                             ∗ ⌜t0 ≤ t'⌝ , RET #t' >>>.
  Proof.
    iIntros "k_in_KS #HInv". 
    iLöb as "IH" forall (n t1 γ_en γ_cn γ_bn γ_qn γ_cirn).
    iIntros "#FP_n #Hgh #Hlb H". iDestruct "H" as %t0_le_t1.
    iDestruct "k_in_KS" as %k_in_KS.
    iIntros (Φ) "AU". wp_lam. wp_pures.
    (** Lock node n **)
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cn Bn Qn)"HnP_n". iModIntro. wp_pures. 
    iDestruct "HnP_n" as (γ_en' γ_bn' γ_cn' γ_qn' γ_cirn' es T)
                    "(node_n & HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iPoseProof (ghost_heap_sync with "[$HnP_gh] [$Hgh]") 
                                  as "(% & % & % & % & %)".
    subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
    (** Check contents of n **)
    wp_apply (inContents_spec with "node_n").
    iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val.
    wp_pures.
    (** Case analysis on whether k in contents of n **)
    destruct t as [t |]; last first.
    - (** Case : k not in contents of n **)
      wp_pures.
      (** Find next node to visit **)
      wp_apply (findNext_spec with "node_n").
      iIntros (b n1) "(node_n & Hif)". 
      (** Case analysis on whether there exists a next node **)
      destruct b.
      + (** Case : exists next node n' **)
        wp_pures. iDestruct "Hif" as %k_in_es.
        iApply fupd_wp.
        (** Open invariant to establish resources
            required to apply induction hypothesis IH
            on node n' **)
        iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn'. subst Bn'. subst Qn'.
        iAssert (inFP γ_f n1)%I as "#FP_n1".
        { iApply "HnS_cl". iPureIntro. 
          clear -k_in_es. set_solver. }
             
        iAssert (⌜n1 ∈ domm I⌝)%I as %n_in_I.
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n1] [$Hf]") as "H'". }
        iAssert (⌜n ≠ n1⌝)%I as %n_neq_n1.
        { destruct (decide (n = n1)); try done.
          iPoseProof (node_edgeset_empty_root_self with "node_n") as "%".
          destruct H1 as [_ Es_n]. rewrite <-e in k_in_es.
          clear -k_in_es Es_n. set_solver. } 
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n1); last by set_solver.
        iDestruct "Hstar'" as "(H_n1 & Hstar'')".
        iDestruct "H_n1" as (bn1 Cn1 Bn1 Qn1)"(Hl_n1 & Hlif_n1 & HnS_n1)".
        iDestruct "HnS_n1" as (γ_en1 γ_cn1 γ_bn1 γ_qn1 γ_cirn1 es1 In1 Rn1) 
                  "(HnS_gh1 & HnS_frac1 & HnS_si1 & HnS_FP1 
                       & HnS_cl1 & HnS_oc1 & HnS_H1 & HnS_star1 & Hφ1)".

        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); 
                              last by eauto) in "HnS_star".
        iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k);
                                     last by eauto) in "HnS_star1".
        iDestruct "HnS_star1" as "(Hcirk_n1 & HnS_star1')".
        iMod (own_update (γ_cirn1 !!! k) (● MaxNat (Bn1 !!! k)) 
              ((● MaxNat (Bn1 !!! k)) ⋅ (◯ MaxNat (Bn1 !!! k))) 
                  with "[Hcirk_n1]") as "(Hcirk_n1 & #Hlb_1)".
        { apply (auth_update_alloc _ (MaxNat (Bn1 !!! k)) 
                              (MaxNat (Bn1 !!! k))).
          apply max_nat_local_update. 
          simpl. lia. } { iFrame. }

        iAssert (⌜t0 ≤ Bn1 !!! k⌝)%I as "%".
        { iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
          { iPoseProof (own_valid_2 with "[$Hcirk_n] [$Hlb]") as "%".
            rename H1 into Valid_Bnt.
            apply auth_both_valid_discrete in Valid_Bnt.
            destruct Valid_Bnt as [H' _].
            apply max_nat_included in H'.
            simpl in H'. by iPureIntro. }
          destruct (Qn !! k) as [tq | ] eqn: Hqn.
          - iAssert (⌜(k, Qn !!! k) ∈ outset KT In n1⌝)%I as %outflow_n_n1.
            { iDestruct "HnS_oc" as "(H' & _)".
              iDestruct "H'" as %H'. iPureIntro.    
              apply (H' n1 k (Qn !!! k)).
              unfold outflow_constraint_I in H'.
              done. repeat split; try done. 
              rewrite lookup_total_alt. 
              rewrite Hqn. by simpl. }
            iAssert (⌜(k, Qn !!! k) ∈ inset KT In1 n1⌝)%I as %inflow_n1.
            { iDestruct "HnS_si" as "(H'&_)".
              iDestruct "HnS_si1" as "(H1'&_&%&_)".
              rename H1 into Domm_In1.
              assert (n1 ∈ domm In1) as H''. 
              { clear -Domm_In1. set_solver. }
              iCombine "H'" "H1'" as "H'".
              iPoseProof (own_valid with "[$H']") as "%".
              rename H1 into Valid_InIn1.
              rewrite auth_frag_valid in Valid_InIn1 *; intros Valid_InIn1.
              pose proof intComp_unfold_inf_2 In In1 Valid_InIn1 n1 H''.
              rename H1 into H'. unfold ccmop, ccm_op in H'.
              simpl in H'. unfold lift_op in H'.
              iPureIntro. rewrite nzmap_eq in H' *; intros H'.
              pose proof H' (k, Qn !!! k) as H'.
              rewrite nzmap_lookup_merge in H'.
              unfold ccmop, ccm_op in H'. simpl in H'.
              unfold nat_op in H'.
              assert (1 ≤ out In n1 !1 (k, Qn !!! k)) as Hout.
              { unfold outset, dom_ms in outflow_n_n1.
                rewrite nzmap_elem_of_dom_total in outflow_n_n1 *; 
                intros outflow_n_n1.
                unfold ccmunit, ccm_unit in outflow_n_n1.
                simpl in outflow_n_n1. unfold nat_unit in outflow_n_n1.
                clear - outflow_n_n1. lia. }
              assert (1 ≤ inf In1 n1 !1 (k, Qn !!! k)) as Hin.
              { clear -H' Hout. 
                assert (∀ (x y z: nat), 1 ≤ y → x = z + y → 1 ≤ x) as H''.
                lia. by pose proof H'' _ _ _ Hout H'. }
              unfold inset. rewrite nzmap_elem_of_dom_total.
              unfold ccmunit, ccm_unit. simpl. unfold nat_unit.
              clear -Hin. lia. }
            iAssert (⌜Bn1 !!! k = Qn !!! k⌝)%I as %Bn1_eq_Bn.
            { iDestruct "Hφ1" as "(_ & _& % & _)". 
              rename H1 into Hφ2. 
              pose proof Hφ2 k (Qn !!! k) k_in_KS inflow_n1 as H'.
              iPureIntro. done. } 
            iAssert (⌜Bn !!! k = Qn !!! k⌝)%I as %Bn_eq_Qn.
            { iDestruct "Hφ" as "(_ & % & _)". rename H1 into Hφ1.
              pose proof Hφ1 k as [_ H']. done.
              iPureIntro. pose proof H' Cn_val as H'. 
              rewrite /(Bn !!! k). unfold finmap_lookup_total.
              by rewrite H'.  } 
            iPureIntro. rewrite Bn1_eq_Bn.
            rewrite <-Bn_eq_Qn. clear -lb_t1 t0_le_t1.
            apply (Nat.le_trans _ t1 _); try done.
          - iDestruct "Hφ" as "(_ & % & _)".
            rename H1 into Hφ1. apply Hφ1 in Cn_val.
            rewrite <-Cn_val in Hqn.
            rewrite lookup_total_alt in lb_t1.
            rewrite Hqn in lb_t1.
            simpl in lb_t1. iPureIntro.
            clear -lb_t1 t0_le_t1. lia.
            try done. done. }
 
        iAssert (own γ_gh (◯ {[n1 := 
                      ghost_loc γ_en1 γ_cn1 γ_bn1 γ_qn1 γ_cirn1]}))%I
                            with "HnS_gh1" as "#Hgh1".  
        (** Closing the invariant **)
        iModIntro. iSplitR "node_n HnP_gh HnP_frac HnP_C HnP_t AU". iNext.
        iExists T', H, hγ, I, R. iFrame "Hglob".
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n1); last set_solver.
        iFrame "Hstar''". iSplitL "Hl_n Hlif_n HnS_gh HnS_frac 
                    HnS_si HnS_FP HnS_cl HnS_oc HnS_H Hcirk_n HnS_star' Hφ".
        iExists bn, Cn, Bn, Qn. iFrame "Hl_n Hlif_n".
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, In, Rn.
        iFrame. by iApply "HnS_star'".                  
        iExists bn1, Cn1, Bn1, Qn1. iFrame "Hl_n1 Hlif_n1".
        iExists γ_en1, γ_cn1, γ_bn1, γ_qn1, γ_cirn1, es1, In1, Rn1.
        iFrame. by iApply "HnS_star1'".
        iModIntro.
        (** Unlock node n **)       
        awp_apply (unlockNode_spec_high with "[] [] 
            [HnP_gh HnP_frac HnP_C HnP_t node_n]"); try done.
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, T.
        iFrame.                
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_". iModIntro. wp_pures.
        (** Apply IH on node n' **)
        iApply "IH"; try done. 
      + (** Case : no next node from n **)
        wp_pures. iDestruct "Hif" as %Not_in_es.
        iApply fupd_wp. 
        (** Linearization Point: key k has not been found in the 
            data structure. Open invariant to obtain resources 
            required to establish post-condition **)
        iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn'. subst Bn'. subst Qn'.
        iAssert (⌜Bn !!! k = 0⌝)%I as %Bn_eq_0.
        { iDestruct "Hφ" as "(Hφ0 & Hφ1 & _)".
          iDestruct "Hφ0" as %Hφ0.
          iDestruct "Hφ1" as %Hφ1.
          pose proof Hφ0 k k_in_KS Not_in_es as Hφ0.
          pose proof Hφ1 k as [_ H']. done.
          pose proof H' Cn_val as H'. 
          iPureIntro.
          rewrite lookup_total_alt.
          rewrite H' Hφ0. by simpl. }          
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                       in "HnS_star".
        iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
        iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
        { iPoseProof (own_valid_2 with "[$Hcirk_n] [$Hlb]") as "%".
          rename H1 into Valid_Bnt.
          apply auth_both_valid_discrete in Valid_Bnt.
          destruct Valid_Bnt as [H' _].
          apply max_nat_included in H'.
          simpl in H'. by iPureIntro. }
        iAssert (⌜t0 = 0⌝)%I as %t0_zero. 
        { iPureIntro. rewrite Bn_eq_0 in lb_t1. 
          clear -lb_t1 t0_le_t1. lia. } subst t0.
        (** Linearization **)  
        iMod "AU" as (t' H') "[MCS [_ Hclose]]". 
        iAssert (⌜H' = H⌝)%I as %H1. 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
          unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
          by iDestruct "MCS" as "(_ & H')".
          by iPureIntro. } subst H'.
        iAssert (⌜(k,0) ∈ H⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          iDestruct "Hist" as %Hist. iPureIntro. 
          by pose proof Hist k k_in_KS as Hist. }
        rename H1 into k0_in_H.  
        iSpecialize ("Hclose" $! 0).
        iMod ("Hclose" with "[MCS]") as "HΦ". iFrame. 
        iPureIntro. split; try done.
        (** Closing the invariant **)
        iModIntro. iSplitR "node_n HnP_gh HnP_frac HnP_C HnP_t HΦ". iNext.
        iExists T', H, hγ, I, R. iFrame "Hglob".
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iFrame "Hstar'". iExists bn, Cn, Bn, Qn.
        iFrame "Hl_n Hlif_n". 
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, In, Rn.
        iFrame "∗%". by iApply "HnS_star'". iModIntro.
        (** Unlock node n **)
        awp_apply (unlockNode_spec_high with "[] [] 
               [HnP_gh HnP_frac HnP_C HnP_t node_n]") without "HΦ"; try done. 
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, T. iFrame.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_". iModIntro. iIntros "HΦ". by wp_pures.
    - (** Case : k in contents of n **)
      wp_pures.                                         
      iApply fupd_wp. 
      (** Linearization Point: key k has been found. Open 
          invariant to obtain resources required to 
          establish post-condition **)
      iInv "HInv" as ">H".
      iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
      iAssert (⌜n ∈ domm I⌝)%I as "%". 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iDestruct "Hstar" as "(H_n & Hstar')".
      iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
      iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                    "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                              & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
      iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                as "(% & % & % & % & %)".
      subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
      iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
      destruct H1 as [Hes [Hc [Hb Hq]]]. 
      subst es'. subst Cn'. subst Bn'. subst Qn'.
      iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                      in "HnS_star".
      iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
      iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
      { iPoseProof (own_valid_2 with "[$Hcirk_n] [$Hlb]") as "%".
        rename H1 into Valid_Bnt.
        apply auth_both_valid_discrete in Valid_Bnt.
        destruct Valid_Bnt as [H' _].
        apply max_nat_included in H'.
        simpl in H'. by iPureIntro. }
      iAssert (⌜Bn !!! k = Cn !!! k⌝)%I as %Bn_eq_Cn.
      { iDestruct "Hφ" as "(_ & Hφ1 & _)".
        iDestruct "Hφ1" as %Hφ1.
        pose proof Hφ1 k t as [H' _].
        done. iPureIntro.
        rewrite !lookup_total_alt.
        pose proof H' Cn_val as H'.
        by rewrite Cn_val H'. }          
      iAssert (⌜set_of_map Cn ⊆ H⌝)%I as %Cn_Sub_H.
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        iPoseProof ((auth_own_incl γ_s H _) with "[$HH $HnP_C]") as "%".
        rename H1 into H'. by apply gset_included in H'. }  
      iAssert (⌜(k,t) ∈ set_of_map Cn⌝)%I as %kt_in_Cn.
      { iPureIntro. apply set_of_map_member.
        rewrite /(Cn !!! k) in Cn_val.
        unfold finmap_lookup_total, inhabitant in Cn_val.
        simpl in Cn_val. 
        destruct (Cn !! k) as [cnk | ] eqn: Hcnk.
        - rewrite Hcnk. apply f_equal.
          by inversion Cn_val. 
        - try done.  }
      (** Linearization **)      
      iMod "AU" as (t' H') "[MCS [_ Hclose]]". 
      iSpecialize ("Hclose" $! t).
      iAssert (⌜H' = H⌝)%I as %H1. 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
        unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
        by iDestruct "MCS" as "(_ & H')".
        by iPureIntro. } replace H'.
      iMod ("Hclose" with "[MCS]") as "HΦ". iFrame. 
      iPureIntro. split. set_solver. rewrite Bn_eq_Cn in lb_t1.
      rewrite lookup_total_alt in lb_t1.
      rewrite Cn_val in lb_t1. simpl in lb_t1. lia.
      (** Closing the invariant **)
      iModIntro. iSplitR "node_n HnP_gh HnP_frac HnP_C HnP_t HΦ".
      iNext. iExists T', H, hγ, I, R. iFrame "Hglob".
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iFrame "Hstar'". iExists bn, Cn, Bn, Qn.
      iFrame "Hl_n Hlif_n". 
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, In, Rn.
      iFrame "∗%". by iApply "HnS_star'". iModIntro.
      (** Unlock node n **)
      awp_apply (unlockNode_spec_high with "[] [] 
                [HnP_gh HnP_frac HnP_C HnP_t node_n]") without "HΦ"; 
                      try done.
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, T. iFrame.
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. iIntros "HΦ". by wp_pures.
      Unshelve. try done. try done.
  Qed.

End search_proof.
