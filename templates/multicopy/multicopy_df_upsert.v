From iris.algebra Require Import excl auth frac cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy_df auth_ext.
Require Export multicopy_util.

Section multicopy_df_upsert.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_dfG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  Lemma nodePred_lockR_true γ_s γ_cn r n Cn Vn Vn' Tn bn : 
    node r n Vn' -∗ 
      lockR bn n (nodePred γ_s γ_cn r n Cn Vn Tn) -∗
        ⌜bn = true⌝.
  Proof.
    iIntros "node Hl_n".
    destruct bn; try done.
    iDestruct "Hl_n" as "(Hl & HnP')".
    iDestruct "HnP'" as "(n' & _)".
    iExFalso. iApply (node_sep_star r n). iFrame.
  Qed.          

  Lemma upsert_spec N γ_te γ_he γ_s Prot γ_cr γ_cd γ_d r d (k: K) (v: V) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
        (ghost_update_protocol N γ_te γ_he Prot k) -∗ 
        mcs_inv N γ_te γ_he γ_s Prot 
          (Inv_DF γ_s γ_cr γ_cd γ_d r d) -∗
            <<< ∀ (t: T) H, MCS γ_te γ_he t H >>> 
                   upsert r #k #v @ ⊤ ∖ (↑(mcsN N))
            <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k, (v, t))]}), RET #() >>>.
  Proof.
    iIntros "%".
    rename H into k_in_KS.
    (* perform Löb induction by generating a hypothesis IH : ▷ goal *)
    iLöb as "IH".
    iIntros "Ghost_updP #HInv" (Φ) "AU". wp_lam. wp_pures.
    iApply fupd_wp. 
    (** Open invariant to establish root node in footprint **)
    iInv "HInv" as (t0 H0)"(mcs_high & >Inv_DF)".
    iDestruct "Inv_DF" as (Cr0 Vr0 Tr0 Cd0 Vd0 Td0) "(r_neq_d & Hcir 
            & Hset & HlockR_r & Half_r & Hcts_r 
            & HlockR_d & Half_d & Hcts_d)".
    iModIntro. iSplitR "AU Ghost_updP". iNext. 
    iExists t0, H0. iFrame "mcs_high". 
    iExists Cr0, Vr0, Tr0, Cd0, Vd0, Td0. iFrame "∗ #".
    
    iModIntro.
    awp_apply lockNode_spec_high without "Ghost_updP"; try done.
    iPureIntro. auto.
    (** Lock the node r **)
    iAaccIntro with ""; try eauto with iFrame.
     
    iIntros (γ_cn Cr Vr Tr) "HnP_n". iModIntro. 
    iIntros "Ghost_updP". wp_pures.
    iDestruct "HnP_n" as "(HnP_n & #r_is_locked)".
    iDestruct "HnP_n" as "(node_r & HnP_C & HnP_frac)".
    wp_apply (addContents_spec with "[$node_r]"); try done.
    iIntros (b Vr') "(node_r & Hif)".


    (** Case analysis on whether addContents is successful **)
    destruct b; last first.
    - (** Case : addContents fails. Unlock root node and apply 
                 inductive hypothesis IH **) 
      iDestruct "Hif" as %HVr. replace Vr'. wp_pures.
      awp_apply (unlockNode_spec_high 
          with "[] [] [HnP_frac HnP_C node_r ]") 
            without "Ghost_updP" ; try done.
      { 
        iFrame.
      }
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

      iInv "HInv" as (t1 H1)"(mcs_high & >Inv_DF)".
      iDestruct "Inv_DF" as (Cr1 Vr1 Tr1 Cd1 Vd1 Td1) "(r_neq_d & Hcir 
            & Hset & HlockR_r & Half_r & Hcts_r 
            & HlockR_d & Half_d & Hcts_d)".

      iDestruct "mcs_high" as "(>MCS_auth & >HH & >HInit 
        & >HClock & >HUniq & Prot)".

      iDestruct "HlockR_r" as (br) "HlockR_r".
      iDestruct "HlockR_d" as (bd) "HlockR_d".      
      iDestruct "Hif" as %HCr.

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
      iDestruct "HnP_C" as "Hown_Cr".  
      iDestruct "HH" as "(HH & HnP_C)".   

      rewrite (big_sepS_delete _ KS k); last by eauto.
      iDestruct "HInit" as %HInit.

      iPoseProof (nodePred_lockR_true with "[$node_r] [HlockR_r]")
         as "%". iFrame. subst br.
        
      (** Update contents-in-reach of r **)
      iAssert (⌜map_of_set H1' = 
                        <[k:= (v, t1)]> (map_of_set H1)⌝)%I as %Htrans_union.
      { 
        iDestruct "HUniq" as %HUniq. 
        iPureIntro.
        pose proof map_of_set_insert_eq k v t1 H1 HUniq HClock_H1 as mos_eq.
        by subst H1'. 
      }

      iAssert (⌜γ_cn = γ_cr⌝)%I as %gamma_cn_cr.
      {

        iDestruct "r_is_locked" as %r_is_locked.
        iDestruct "r_neq_d" as %r_neq_d.
        destruct r_is_locked as [ r_is_locked | r_not_locked].
        destruct r_is_locked as [ r_is_r  gh_cn_cr ]. done.
        destruct r_not_locked as [ r_is_d  gh_cn_cr ]. done.
      }
      subst γ_cn.
      
      iAssert (⌜Cr = Cr1⌝∗ ⌜Vr = Vr1⌝ ∗ ⌜Tr = Tr1⌝)%I as "(%&%&%)".
      { iPoseProof (own_valid_2 _ _ _ with "[$Half_r] [$HnP_frac]") 
                as "#HCr_equiv".
        iDestruct "HCr_equiv" as %HCr_equiv.
        apply frac_agree_op_valid in HCr_equiv.
        destruct HCr_equiv as [_ HCr_equiv].
        apply leibniz_equiv_iff in HCr_equiv.
        inversion HCr_equiv. iPureIntro. done. } subst Cr1 Vr1 Tr1.

      iAssert (⌜cir H1' Cr' Cd1⌝)%I with "[Hcir]" as "Hcir".
      { 
        iDestruct "Hcir" as %Hcir.
        iPureIntro. 
        intros k' v' t'.
        rewrite -> Htrans_union.
        destruct (decide (k' = k)).
        - subst k'. subst Cr'.
          rewrite !lookup_insert.
          split; try done. 
        - subst Cr'. 
          rewrite !lookup_insert_ne; try done.
      }

      (*
      iAssert (⌜(map_of_set H1) !!! k ≤ T⌝)%I as %H_le_T. 
      {
        iPureIntro.
        rewrite lookup_total_alt.
        destruct ((map_of_set H1) !! k) eqn: hist_has_k.
        - simpl.
          unfold maxTS in MaxTS_H1.
          destruct MaxTS_H1 as [MaxTS_H1 T_not_zero].
          pose proof map_of_set_lookup_cases H1 k as H'.
          destruct H' as [H' | [_ H']]; last first.
          + rewrite H' in hist_has_k. inversion hist_has_k.
          + destruct H' as [Tk [H' [_ H'']]].
            rewrite H'' in hist_has_k. inversion hist_has_k.
            subst Tk.
            pose proof MaxTS_H1 k n H' as H'''.
            clear -H'''; lia.
        - simpl. lia.
      }
      *)

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
          
      iAssert (contents_proj Cr' Vr' Tr')%I with "[Hcts_r]" as "Hcts_r".
      { iDestruct "Hcts_r" as "(% & % & %)".
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

      iDestruct "HlockR_r" as "(Hlockr & _)". wp_store.


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
      

      (* Combine fractional ownerships of Cr. *)
      iCombine "HnP_frac Half_r" as "Half_r".
      iEval (rewrite <-frac_agree_op) in "Half_r".
      iEval (rewrite Qp_half_half) in "Half_r".

      (* Use combined ownerships to update Cr -> Cr'. *)
      iMod ((own_update (γ_cr) (to_frac_agree 1 (Cr, Vr, Tr))
              (to_frac_agree 1 (Cr', Vr', Tr'))) with "[$Half_r]") 
              as "Half_r".
      { apply cmra_update_exclusive.
        unfold valid, cmra_valid. simpl. unfold prod_valid_instance.
        split; simpl; try done. }

      (* Break apart ownerships to be used separately. *)
      iEval (rewrite <- Qp_half_half) in "Half_r".
      iEval (rewrite frac_agree_op) in "Half_r".
      iDestruct "Half_r" as "(HnP_frac & Half_r)".
        
      iModIntro. iFrame "HΦ".
      iNext. iExists (t1+1), H1'. iFrame "∗".
      iSplitR; first by iPureIntro.
      iExists Cr', Vr', Tr', Cd1, Vd1, Td1. 
      iFrame "Hcir".
      rewrite (big_sepS_delete _ (KS) k); last by eauto.
      iFrame.
      iSplitR "HlockR_d"; last first.
      { by iExists bd. }
      iExists false; iFrame.
  Qed.
  
End multicopy_df_upsert.