From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy_lsm multicopy_lsm_util.

Section multicopy_lsm_upsert.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_lsmG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).
  
  Lemma upsert_spec N γ_te γ_he γ_s Prot γ_I γ_J γ_f γ_gh r (k: K) (v: V) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
        (ghost_update_protocol N γ_te γ_he Prot k) -∗ 
        mcs_inv N γ_te γ_he γ_s Prot 
          (Inv_LSM γ_s γ_I γ_J γ_f γ_gh r) -∗
            <<< ∀ t H, MCS γ_te γ_he t H >>> 
                   upsert r #k #v @ ⊤ ∖ (↑(mcsN N))
            <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k, (v, t))]}), RET #() >>>.
  Proof.
    iIntros "%". iLöb as "IH".
    rename H into k_in_KS.    
    iIntros "Ghost_updP #HInv" (Φ) "AU". wp_lam. wp_pures.
    iApply fupd_wp. 
    (** Open invariant to establish root node in footprint **)
    iInv "HInv" as (t0 H0)"(mcs_high & >Inv_LSM)".
    iDestruct "Inv_LSM" as (hγ0 I0 J0)"(Hglob & Hstar)".
    iDestruct "Hglob" as "(HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & #FP_r & domm_IR & domm_Iγ)".
    iModIntro. iSplitR "AU Ghost_updP". iNext. 
    iExists t0, H0. iFrame "mcs_high". 
    iExists hγ0, I0, J0. iFrame "∗ #". iModIntro.
    (** Lock the node r **)
    awp_apply lockNode_spec_high without "Ghost_updP"; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cr Qr)"HnP_n". iModIntro. 
    iIntros "Ghost_updP". wp_pures.
    iDestruct "HnP_n" as (γ_er γ_cr γ_qr γ_cirr es Vr Tr)
                      "(node_r & #HnP_gh & HnP_frac & HnP_C & HnP_cts)".
    wp_apply (addContents_spec with "[$node_r]"); try done.
    iIntros (b Vr')"(node_r & Hif)".
    (** Case analysis on whether addContents is successful **)
    destruct b; last first.
    - (** Case : addContents fails. Unlock root node and apply 
                 inductive hypothesis IH **) 
      iDestruct "Hif" as %HVr. replace Vr'. wp_pures.
      awp_apply (unlockNode_spec_high 
          with "[] [] [HnP_gh HnP_frac HnP_C HnP_cts node_r]") 
            without "Ghost_updP" ; try done.
      { iExists γ_er, γ_cr, γ_qr, γ_cirr, es, Vr, Tr.
        iFrame "∗#". }
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro.
      iIntros "Ghost_updP". wp_pures.
      iApply ("IH" with "Ghost_updP"); try done.
    - (** Case : addContent successful **)
      (** Linearization Point: open invariant and update the resources **)
      wp_pures. 
      
      (* Need to unfold unlockNode here in order to apply 
         ghost_udpate_protocol, which requires stripping off
         a later modality. This requires a physical step in heapLang,
         which is available by unfolding the unlockNode *)

      unfold unlockNode.
      wp_pures. wp_bind(getLockLoc _)%E.
      wp_apply getLockLoc_spec; first done.
      iIntros (l) "%"; subst l; wp_pures.

      iInv "HInv" as (t1 H1)"(mcs_high & >Inv_LSM)".
      iDestruct "Inv_LSM" as (hγ1 I1 J1)"(Hglob & Hstar)".
      iDestruct "mcs_high" as "(>MCS_auth & >HH & >HInit & >HClock & >HUniq & Prot)".
      iDestruct "Hglob" as "(HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & _ & domm_IR & domm_Iγ)".
      iDestruct "Hif" as %HVr'.
      
      set (Tr' := <[k := t1]> Tr).
      set (Cr' := <[k := (v, t1)]> Cr).
      set (H1' := H1 ∪ {[(k, (v, t1))]}).
      
      iPoseProof ((auth_own_incl γ_s H1 _) with "[$HH $HnP_C]") as "%".
      rename H into Cr_sub_H1. apply gset_included in Cr_sub_H1.
      iDestruct "HClock" as %HClock_H1.
      (** Re-establish maxTS for updated T and H **)
      assert (HClock (t1 + 1) H1') as HClock_H1'.
      { subst H1'. intros k' v' t' H'.
        assert (((k', (v', t')) ∈ H1) ∨ (k' = k ∧ v' = v ∧ t' = t1)) 
              as Hor by set_solver.
        destruct Hor as [Hor | Hor]. 
        pose proof HClock_H1 k' v' t' Hor as Hres. lia.
        destruct Hor as [_ [_ Hor]]. replace t'. lia. }       
      iAssert (⌜set_of_map Cr' ⊆ H1'⌝)%I as %Cr'_sub_H1'.
      { subst H1'. iPureIntro. subst Cr'.
        pose proof (set_of_map_insert_subseteq Cr k v t1) as H'.
        assert (set_of_map Cr = set_of_map Cr) as H'' by done. 
        set_solver. }
      (** Update the (● H) resource **)  
      iMod (own_update γ_s (● H1) (● H1') 
          with "[$HH]") as "HH".
      { apply (auth_update_auth _ _ H1').
        apply gset_local_update. set_solver. }
      iMod (own_update γ_s (● H1') 
             (● H1' ⋅ ◯ (set_of_map Cr')) 
              with "[$HH]") as "HH".
      { subst H1'.
        apply (auth_update_alloc _ (H1 ∪ {[(k, (v, t1))]}) (set_of_map Cr')).
        apply local_update_discrete. intros m Valid_H1 H1_eq.
        split; try done. rewrite /(ε ⋅? m) in H1_eq.
        destruct m. rewrite gset_op in H1_eq. 
        rewrite left_id in H1_eq *; intros H1_eq.
        rewrite <-H1_eq. 
        rewrite /(set_of_map Cr' ⋅? Some (H1 ∪ {[k, (v, t1)]})).
        rewrite gset_op.
        rewrite /(ε) in H1_eq. unfold ucmra_unit in H1_eq.
        simpl in H1_eq.
        assert ((k, (v, t1)) ∈ set_of_map Cr') as H'.
        { subst Cr'. apply set_of_map_member.
          apply lookup_insert. } 
        clear - H' Cr_sub_H1 Cr'_sub_H1'. set_solver.
        exfalso. clear -H1_eq. set_solver. }
      (** Re-establish HInit **)   
      iAssert (⌜HInit H1'⌝)%I with "[HInit]" as "HInit".
      { subst H1'. iDestruct "HInit" as %HInit.
        unfold multicopy.HInit. iPureIntro.
        clear -HInit k_in_KS. intros k' Hk'.
        pose proof HInit k' Hk' as H'. set_solver. }  
      iDestruct "HnP_C" as "_".  
      iDestruct "HH" as "(HH & HnP_C)".   
      iAssert (⌜r ∈ domm I1⌝)%I as %r_in_I.
      { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
      iDestruct "Hstar" as "(H_r & Hstar')".
      iDestruct "H_r" as (br Cr'' Qr'')"(Hl_r & HnS_r)".
      iPoseProof (nodePred_lockR_true with "[$node_r] [$Hl_r]")
         as "%". subst br.
      iDestruct "HnS_r" as (γ_er' γ_cr' γ_qr' γ_cirr' es' Tr'' Br Ir Jr) "HnS_r'".
      iPoseProof (nodePred_nodeShared_eq with "[$HnP_gh] [$HnP_frac] [$HnS_r']")
           as "(HnP_frac & HnS_r' &%&%&%)". subst es' Tr'' Qr''.   
      iDestruct "HnS_r'" as "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                            & HnS_cl & HnS_oc & HnS_Bn & HnS_H & HnS_star & Hφ)".


      (** Update contents-in-reach of r **)
      set (Br' := <[k := t1]>Br).
      assert (Br' = <[k := t1]>Br) as HBr'. try done.
      iEval (rewrite decide_True) in "HnS_H".
      iDestruct "HnS_H" as "(% & %)". 
      rename H into Br_eq_H1. rename H2 into Infz_Ir.

      iAssert (⌜contents_in_reach Br' Tr' Qr⌝)%I with "[HnS_Bn]" as "HnS_Bn".
      { iDestruct "HnS_Bn" as %H'. iPureIntro. 
        intros k' t' HKS. destruct (decide (k' = k)).
        - subst k'. subst Tr' Br'.
          rewrite !lookup_insert.
          split; try done.
        - subst Tr' Br'. 
          rewrite !lookup_insert_ne; try done.
          pose proof H' k' t' HKS; try done. }

      
      iAssert (⌜∀ k : K, Br' !!! k = (map_of_set H1' !!! k).2⌝)%I as %Br'_eq_H1'.
      { iDestruct "HUniq" as %HUniq. 
        iPureIntro. subst Br' H1'. intros k'.
        rewrite <-map_of_set_insert_eq; try done.
        destruct (decide (k' = k)).
        - subst k'. rewrite !lookup_total_insert; by simpl.
        - rewrite !lookup_total_insert_ne; try done. }
      iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto) in "HnS_star".
      iDestruct "HnS_star" as "(Hk & HnS_star')".
      iAssert (⌜Br !!! k ≤ t1⌝)%I as %Br_le_t1. 
      { iPureIntro. rewrite lookup_total_alt.
        destruct (Br !! k) eqn: Hbrk; last first.
        - rewrite Hbrk. simpl; clear; lia.
        - rewrite Hbrk. simpl.
          pose proof Br_eq_H1 k as Br_eq_H1. 
          (* rewrite Br_eq_H1 in Hbrk. *)
          pose proof map_of_set_lookup_cases H1 k as H'.
          destruct H' as [H' | [_ H']]; last first.
          + rewrite !lookup_total_alt in Br_eq_H1.
            rewrite H' Hbrk in Br_eq_H1. simpl in Br_eq_H1. 
            subst t; clear; lia.
          + destruct H' as [v' [t' [H' [H'' H''']]]].
            rewrite !lookup_total_alt in Br_eq_H1.
            rewrite H''' Hbrk in Br_eq_H1. simpl in Br_eq_H1.
            subst t'. 
            pose proof HClock_H1 k v' t H' as H''''.
            clear -H''''; lia. }  
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
        assert (<[k := t1]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'') in "H".       
        iIntros "H". iEval (rewrite HBr').
        assert (<[k:= t1]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'').
        done. }
      iMod ((frac_update γ_er γ_cr γ_qr es Tr Qr es Tr' Qr) 
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
      iAssert (⌜φ1 es Qr⌝ ∗ ⌜φ2 r Br' Ir⌝ ∗ ⌜φ3 Br' Qr⌝ 
                ∗ ⌜φ4 r Br' Jr⌝ ∗ ⌜φ5 r Jr⌝ 
                ∗ ⌜φ6 r es Jr Qr⌝ ∗ ⌜φ7 r Ir⌝)%I
            with "[Hφ]" as "Hφ".
      { iDestruct "Hφ" as %Hφ. 
        destruct Hφ as [Hφ1 [Hφ2 [Hφ3 [Hφ4 [Hφ5 [Hφ6 Hφ7]]]]]].
        iPureIntro. repeat split; try done.
        - intros k' t' HKS Hins.
          pose proof Infz_Ir r as Infz_Ir.
          rewrite Infz_Ir in Hins.
          exfalso. clear -Hins. set_solver.
        - intros k' HKS. subst Br'. destruct (decide (k' = k)).
          + subst k'. rewrite lookup_total_insert.
            apply (Nat.le_trans _ (Br !!! k) _); try done.
            apply Hφ3; try done.
          + rewrite lookup_total_insert_ne; try done.
            apply Hφ3; try done.
        - intros k' HKS. right.
          apply (inset_monotone J1 Jr Ro); try done.
          by rewrite <-auth_auth_valid.
          pose proof Inf_J r k' HKS as Inf_J.
          by rewrite decide_True in Inf_J.
          rewrite Domm_Jr. clear. set_solver. }
            
      iAssert (⌜HUnique H1'⌝)%I with "[HUniq]" as %HUniq.
      { iDestruct "HUniq" as %HUniq.
        iPureIntro. subst H1'.
        intros k' t' v' v'' H' H''.
        assert (((k', (v', t')) ∈ H1) ∨ (k' = k ∧ v' = v ∧ t' = t1)) 
              as Hor by set_solver.
        assert (((k', (v'', t')) ∈ H1) ∨ (k' = k ∧ v'' = v ∧ t' = t1)) 
              as Hor' by set_solver.
        destruct Hor as [Hor | Hor]. 
        - destruct Hor' as [Hor' | Hor'].
          + apply (HUniq k' t' v' v'' Hor Hor'); try done.
          + destruct Hor' as [? [? ?]]. subst k' v'' t'.
            apply (HClock_H1 k v' t1) in Hor.
            clear -Hor; lia.
        - destruct Hor as [? [? ?]]. subst k' v' t'.
          destruct Hor' as [Hor' | Hor'].
          + apply (HClock_H1 k v'' t1) in Hor'.
            clear -Hor'; lia.
          + destruct Hor' as [? [? ?]]. by subst v''. }  
          
      iAssert (contents_proj Cr' Vr' Tr')%I with "[HnP_cts]" as "HnP_cts".
      { iDestruct "HnP_cts" as "(% & % & %)".
        rename H into dom_Cr_Vr; rename H2 into dom_Cr_Tr;
        rename H3 into Cr_eq_Vr_Tr. 
        iPureIntro. subst Cr' Vr' Tr'. split; last split.
        - apply leibniz_equiv. rewrite !dom_insert.
          rewrite dom_Cr_Vr. clear; set_solver.
        - apply leibniz_equiv. rewrite !dom_insert.
          rewrite dom_Cr_Tr. clear; set_solver.
        - intros k' v' t'. destruct (decide (k' = k)).
          + subst k'. rewrite !lookup_insert. split.
            * intros H'; by inversion H'.
            * intros [H' H'']; inversion H'; by inversion H''.
          + rewrite !lookup_insert_ne; try done. }

      iDestruct "Hl_r" as "(Hlockr & _)". wp_store.
        
          
            
      (** Linearization **)    
      iMod "AU" as (t' H1'')"[MCS [_ Hclose]]".
      iAssert (⌜t' = t1 ∧ H1'' = H1⌝)%I as "(% & %)". 
      { iPoseProof (MCS_agree with "[$MCS_auth] [$MCS]") as "(% & %)".
        by iPureIntro. } subst t' H1''. 
      iDestruct "MCS" as "(MCS◯t & MCS◯h & _)".
      iDestruct "MCS_auth" as "(MCS●t & MCS●h)".
      iMod ((auth_excl_update γ_te (t1+1) t1 t1) with "MCS●t MCS◯t") 
                                          as "(MCS●t & MCS◯t)".
      iMod ((auth_excl_update γ_he (H1 ∪ {[(k, (v, t1))]}) H1 H1) with "MCS●h MCS◯h") 
                                          as "(MCS●h & MCS◯h)".
      iCombine "MCS◯t MCS◯h" as "(MCS_t & MCS_h)".
      iCombine "MCS●t MCS●h" as "MCS_auth".
      iMod ("Hclose" with "[MCS_t MCS_h]") as "HΦ".
      iFrame. by iPureIntro.
      
      (** Use ghost_update_protocol to update Prot(H) **)
      iSpecialize ("Ghost_updP" $! v t1 H1).
      

      iMod ("Ghost_updP" with "[] [$MCS_auth] [$Prot]") 
                        as "(Prot & MCS_auth)". 
      { assert ((k, (v, t1)) ∈ H1') as H' by set_solver.
        assert ((∀ (v' : V) (t' : nat), (k, (v', t')) ∈ H1' → t' ≤ t1))
          as H''.
        { intros v' t' Hvt'. subst H1'. 
          rewrite elem_of_union in Hvt'*; intros Hvt'.
          destruct Hvt' as [Hvt' | Hvt'].
          - apply HClock_H1 in Hvt'. clear -Hvt'; lia.
          - assert (t' = t1) by (clear -Hvt'; set_solver).
            subst t'; clear; lia. }  
        pose proof map_of_set_lookup H1' k v t1 HUniq H' H'' as H'''.
        iPureIntro. rewrite lookup_total_alt.
        rewrite H'''. by simpl. }          
      
      
      iModIntro. iFrame "HΦ". iNext.
      iExists (t1+1), (H1 ∪ {[(k, (v, t1))]}).
      
      iSplitL "MCS_auth Prot HInit HH".
      { iFrame "∗". iPureIntro. done. }
      iExists hγ1, I1, J1. iFrame "∗ %".   
      rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
      iSplitR "Hstar'"; last first.
      { iApply (big_sepS_mono 
                (λ y, ∃ (bn : bool) (Cn : gmap K (V * T)) (Qn : gmap K T),
                        lockR bn y (nodePred γ_gh γ_s r y Cn Qn)
                      ∗ nodeShared γ_I γ_J γ_f γ_gh r y Qn H1)%I
                (λ y, ∃ (bn : bool) (Cn : gmap K (V * T)) (Qn : gmap K T),
                        lockR bn y (nodePred γ_gh γ_s r y Cn Qn)
                      ∗ nodeShared γ_I γ_J γ_f γ_gh r y Qn (H1 ∪ {[k, (v, t1)]}))%I
                (domm I1 ∖ {[r]})); try done.
      intros y y_dom. assert (y ≠ r) as Hy by set_solver. iFrame.
      iIntros "Hstar". iDestruct "Hstar" as (b C Q)"(Hl & HnS)".
      iExists b, C, Q. iFrame. 
      iDestruct "HnS" as (γ_e γ_c γ_q γ_cir esy Ty By Iy Jy)
                  "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
                            & HnS_cl & HnS_oc & HnS_Bn & HnS_H & HnS_star 
                            & Hφ0 & Hφ2 & Hφ3 & Hφ4 & Hφ5 & Hφ7)".
      iExists γ_e, γ_c, γ_q, γ_cir, esy, Ty, By, Iy. iExists Jy. iFrame.
      destruct (decide (y = r)); try done. } 
      { iExists false, Cr', Qr. 
        iSplitL "node_r Hlockr HnP_C HnP_frac HnP_cts".
        iFrame. iExists γ_er, γ_cr, γ_qr, γ_cirr, es, Vr', Tr'. iFrame "∗#". 
        iExists γ_er, γ_cr, γ_qr, γ_cirr, es, Tr', Br', Ir. iExists Jr.
        iFrame "∗#". iEval (rewrite decide_True). 
        iFrame "%∗". }
  Qed.                  


End multicopy_lsm_upsert.
