From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants fancy_updates.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Require Export hindsight flows.

Module Type HINDSIGHT_SPEC (DS : DATA_STRUCTURE).
  Module DEFS := HINDSIGHT_DEFS DS.
  Import DS DEFS.

  Definition is_updating (pvs : list (val * val)) : Prop :=
    Exists (λ x, ∃ v1, x.1 = (v1, #true)%V) pvs.
  
  Global Instance is_updating_dec : ∀ pvs, Decision (is_updating pvs).
  Proof.
    intros pvs. rewrite /is_updating. apply Exists_dec. intros [x1 x2].
    rewrite /=. destruct x1.
    - right; intros [v1 H']; try done.
    - right; intros [v1 H']; try done.
    - destruct (decide (x1_2 = #true)) as [-> | Hx1]. 
      + left. by exists x1_1.
      + right. intros [v1 H']. inversion H'. done.
    - right; intros [v1 H']; try done.
    - right; intros [v1 H']; try done.
  Qed.

  Parameter dsOp_spec: ∀ N γ_t γ_r γ_m γ_ght op r (p: proph_id) pvs 
    γ_sy t_id t0 Q,
          main_inv N γ_t γ_r γ_m γ_ght -∗
          □ update_helping_protocol N γ_t γ_r γ_ght -∗
            {{{ proph p pvs ∗ 
                (⌜is_updating pvs⌝ ∗ au N γ_r op Q ∨
                  ⌜¬ is_updating pvs⌝ ∗ thread_vars γ_t γ_ght γ_sy t_id t0) }}} 
                  dsOp (Op_to_val op) #r #p
            {{{ (res: resT), RET #res; 
                  ⌜is_updating pvs⌝ ∗ Q #res
                ∨ ⌜¬ is_updating pvs⌝ ∗ past_lin_witness γ_m op res t0 }}}.

End HINDSIGHT_SPEC.

Module CLIENT_SPEC (DS : DATA_STRUCTURE) (HS: HINDSIGHT_SPEC DS).
  Import DS HS.DEFS HS.
    
  (** Proofs *)
    
  Lemma history_sync γ_m (M: gmap nat (agreeR (ucmra_ofeO snapshotUR))) 
    (s: snapshot) t: 
    own γ_m (● M) -∗ own γ_m (◯ {[t := to_agree s]}) -∗
      ⌜M !! t ≡ Some (to_agree s)⌝.
  Proof.
    iIntros "HM Hs". iCombine "HM" "Hs" as "H'".
    iPoseProof (own_valid with "H'") as "Hv".
    iDestruct "Hv" as %Hv.
    rewrite auth_both_valid_discrete in Hv.
    destruct Hv as [H' Hv].
    rewrite lookup_included in H'.
    pose proof H' t as H'.
    rewrite lookup_insert in H'.
    unfold included in H'.
    iPureIntro.
    destruct H' as [z H'].
    destruct z as [z | ].
    - rewrite /op /cmra_op /= in H'. 
      pose proof lookup_valid_Some M t (to_agree s ⋅ z) Hv H' as H''.
      apply agree_op_inv in H''.
      rewrite <-H'' in H'.
      by rewrite agree_idemp in H'.
    - by rewrite /op /cmra_op /= in H'. 
  Qed.
  

  Definition dsOp' : val :=
    λ: "OP" "r",     
      let: "t_id" := NewProph in
      let: "p_upd" := NewProph in
      let: "p" := NewProph in
      let: "v" := dsOp "OP" "r" "p_upd" in
      resolve_proph: "p" to: "v";;
      "v".


  Lemma dsOp'_spec N γ_t γ_r γ_m γ_ght op (r: loc) :
          main_inv N γ_t γ_r γ_m γ_ght -∗
              <<< ∀∀ a, dsRep γ_r a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N) ∪ ↑(threadN N)
              <<< ∃∃ a' res, dsRep γ_r a' ∗ ⌜seq_spec op a a' res⌝, 
                  RET #res >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pure credit:"Hc'". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (pvs p1)"Hproph1". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 resTTypedProph); first done.
    iIntros (vp p2) "Hproph2". wp_pures.
    
    iAssert (update_helping_protocol N γ_t γ_r γ_ght)%I 
        as "Upd_help". 
    { iIntros (M T s)"%Dom_M Ds Prot".
      iDestruct "Prot" as (R G)"(HG & Domm_G & Hstar)".
      iAssert (dsRep γ_r (abs s) -∗
        ([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_ght t_id M) ={⊤ ∖ ↑cntrN N}=∗
        (([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_ght t_id (<[T+1:=s]> M))
        ∗ dsRep γ_r (abs s)))%I as "H'".
      { iIntros "Ds". 
        iInduction R as [|tid' R' tid_notin_R IH] "HInd" using set_ind_L; 
          auto using big_sepS_empty'.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        assert (({[tid']} ∪ R') ∖ {[tid']} = R') as HR'. set_solver. rewrite HR'.
        iIntros "(Htid & Hbigstar)". 
        iMod ("HInd" with "[$Ds] Hbigstar") as "(H' & Ds)". iFrame "H'". 
        iDestruct "Htid" as (γ_tk' γ_sy' Q' op' vp' t0' vtid')
          "(Hproph & #Hthd & Hsy & #HthInv)".
        iInv "HthInv" as (M'' T'')"Hstate".
        iDestruct "Hstate" as "(>Hsy' & >%Dom_M'' & >%Ht0 & Hstate)".
        iAssert (⌜M'' = M⌝)%I as %->.
        { iPoseProof (own_valid_2 _ _ _ with "[$Hsy] [$Hsy']") as "%H'".
          rewrite frac_agree_op_valid_L in H'. iPureIntro; symmetry; apply H'. }
        assert (T'' = T) as ->.
        { rewrite Dom_M in Dom_M''. apply gset_seq_eq in Dom_M''. done. }
        iAssert (|={⊤ ∖ ↑cntrN N ∖ ↑threadN N}=> 
            own γ_sy' (to_frac_agree (1 / 2) (<[T+1:=s]> M))
          ∗ own γ_sy' (to_frac_agree (1 / 2) (<[T+1:=s]> M)))%I
          with "[Hsy Hsy']" as ">(Hsy & Hsy')".
        { iCombine "Hsy Hsy'" as "H'". 
          iEval (rewrite <-frac_agree_op) in "H'".
          iEval (rewrite Qp.half_half) in "H'".
          iMod ((own_update (γ_sy') (to_frac_agree 1 M) 
                        (to_frac_agree 1 (<[T+1 := s]> M))) with "[$H']") as "H'".
          { apply cmra_update_exclusive. 
            rewrite /valid /cmra_valid /= /prod_valid_instance.
            split; simpl; try done. }
          iEval (rewrite <-Qp.half_half) in "H'".
          iEval (rewrite frac_agree_op) in "H'".  
          iDestruct "H'" as "(Hsy & Hsy')". by iFrame. }
        assert (dom (<[(T + 1)%nat:=s]> M) = gset_seq 0 (T + 1)) as Dom_M'.
        { rewrite dom_insert_L Dom_M. apply set_eq_subseteq. split.
          all: intros x; rewrite elem_of_union elem_of_singleton 
            !elem_of_gset_seq; lia. }
        assert (t0' ≤ T+1) as Ht0' by lia.
        iDestruct "Hstate" as "[HPending | HDone]".
        - iDestruct "HPending" as "(AU & >Hc & >%Past_W)".
          destruct (decide (seq_spec op' (abs s) (abs s) vp'))
            as [Hss | Hss].
          + iApply (lc_fupd_add_later with "Hc"). iNext.
            iMod "AU" as (c) "[DsR [_ Hcomm]]".
            iAssert (⌜c = abs s⌝)%I as "%". 
            { unfold dsRep, dsRepI.
              iDestruct (own_valid_2 with "[$Ds] [$DsR]") as %H'.
              rewrite frac_agree_op_valid_L in H'.
              destruct H' as [_ H']; by iPureIntro. } subst c. 
            iSpecialize ("Hcomm" $! (abs s) vp'). 
            iMod ("Hcomm" with "[DsR]") as "HΦ".
            { iFrame. by iPureIntro. }
            iModIntro. iSplitL "Hsy HΦ". iNext. iExists (<[T+1:=s]> M), (T+1).
            iFrame "∗%". iRight. iSplitL; last first. iPureIntro. exists (T+1). 
            split. split; try done. by rewrite lookup_total_insert. by iLeft.
            iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
            iFrame "∗#%".
          + iModIntro. iSplitL "AU Hc Hsy". iNext. iExists (<[T+1:=s]> M), (T+1).
            iFrame "∗%". iLeft. iFrame. iPureIntro. 
            { intros [t [Ht1 Ht2]]. destruct (decide (t = T+1)) as [-> | Ht].
              rewrite lookup_total_insert in Ht2. done.
              apply Past_W. exists t. split. lia. 
              rewrite lookup_total_insert_ne in Ht2; try done. } 
            iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
            iFrame "∗#%".
        - iDestruct "HDone" as "(HDone & >%PastW)".
          iModIntro. iSplitL "HDone Hsy". iNext. iExists (<[T+1:=s]> M), (T+1).
          iFrame "∗%". iRight. iSplitL; last first. iPureIntro.
          { destruct PastW as [t [Ht1 Ht2]]. exists t. split. lia.
            rewrite lookup_total_insert_ne. done. lia. } iFrame.
          iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
          iFrame "∗#%". }
      iPoseProof ("H'" with "[$Ds] [$Hstar]") as ">(Hstar & Ds)".
      iModIntro. iFrame. iExists R, G. iFrame. }
    
    destruct (decide (is_updating pvs)) as [Hpvs | Hpvs].
    - wp_apply (dsOp_spec with "[] [] [AU Hproph1]"); try done.
      { iFrame "Hproph1". iLeft. iFrame "AU %". }
      iIntros (res)"Hor". iDestruct "Hor" as "[Hor | Hor]"; last first.
      { iDestruct "Hor" as "(% & _)". exfalso; try done. }
      iDestruct "Hor" as "(_&HΦ)". wp_pures. 
      wp_apply (typed_proph_wp_resolve1 resTTypedProph with "Hproph2"); try done.
      { rewrite /typed_proph_from_val /=. by rewrite resT_proph_resolve. }
      wp_pures. iModIntro. iIntros "_". wp_pures. done.
    - iApply fupd_wp. 
      iInv "HInv" as (M0 T0 s0) "(Ds & >%Habs0 & Hist & Help & Templ)".
      iApply (lc_fupd_add_later with "Hc"). iNext. 
      iDestruct "Help" as (R0 G0)"(HG & %Domm_G0 & Hstar)".
      
      iAssert (¬ ⌜tid ∈ R0⌝)%I as %tid_notin_R0.
      { iIntros "%H'". 
        iEval (rewrite (big_sepS_elem_of_acc _ (R0) tid); 
          last by eauto) in "Hstar".
        iDestruct "Hstar" as "(H' & _)".
        iDestruct "H'" as (? ? ? ? ? ? ?)"(H' & _)".
        iApply (proph1_exclusive tid with "[Htid]"); try done. }
            
      iMod (own_alloc (to_frac_agree (1) (M0))) 
              as (γ_sy)"Hfr_t". { try done. }        
      iEval (rewrite <-Qp.half_half) in "Hfr_t".      
      iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
      iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  

      iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.

      set (<[ tid := to_agree (T0, γ_sy) ]> G0) as G0'.
      iDestruct (own_update _ _ 
        (● G0' ⋅ ◯ {[ tid := to_agree (T0, γ_sy) ]})
               with "HG") as ">HG".
      { apply auth_update_alloc. rewrite /G0'.
        apply alloc_local_update; last done. apply not_elem_of_dom.
        by rewrite Domm_G0 in tid_notin_R0. }
      iDestruct "HG" as "(HG & #Hreg_gh)".

      iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
      { by iDestruct "Hist" as (M0') "(_&_&%&_)". }
      iDestruct "Hist" as (M0')"(H'&H'')".
      iDestruct (own_update _ _ (● (MaxNat T0) ⋅ ◯ (MaxNat T0)) with "H'") 
        as ">H1'".
      { apply auth_update_alloc. apply max_nat_local_update. try done. }
      iDestruct "H1'" as "(H' & #HfragT0)".
      iAssert (hist γ_t γ_m M0 T0) with "[H' H'']" as "Hist".
      { iExists M0'; iFrame. }
      
      iAssert (|={⊤ ∖ ↑cntrN N}=> dsRepI γ_r (abs s0) ∗ 
        (inv (threadN N) (∃ M T, State γ_sy γ_tk (au N γ_r op Φ) Φ M T op vp T0)))%I
        with "[Ds AU Hc' Hreg_sy1]" as "H'".
      { destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))
          as [Hss | Hss].
        - iMod "AU" as (c) "[DsR [_ Hcomm]]".
          iAssert (⌜c = abs s0⌝)%I as "%". 
          { unfold dsRep, dsRepI.
            iDestruct (own_valid_2 with "[$Ds] [$DsR]") as %H'.
            rewrite frac_agree_op_valid_L in H'.
            destruct H' as [_ H']; by iPureIntro. } subst c. 
          iSpecialize ("Hcomm" $! (abs s0) vp). 
          iMod ("Hcomm" with "[DsR]") as "HΦ".
          { iFrame. apply leibniz_equiv in Habs0. 
            rewrite Habs0 in Hss. by iPureIntro. }
        
          iAssert (past_lin M0 T0 op vp T0)%I as "Hpast".
          { iPureIntro. exists T0. split; try done. }
          
          iMod (inv_alloc (threadN N) _ 
            (∃ M T, State γ_sy γ_tk (au N γ_r op Φ) Φ M T op vp T0) 
            with "[HΦ Hreg_sy1]") as "#HthInv".
          { iNext. iExists M0, T0. iFrame "∗%". iSplitR. by iPureIntro.
            iRight. iSplitL. by iLeft. iFrame "#". }
          iModIntro; iFrame "∗#".
        - iMod (inv_alloc (threadN N) _ 
           (∃ M T, State γ_sy γ_tk (au N γ_r op Φ) Φ M T op vp T0) 
            with "[AU Hc' Hreg_sy1]") as "#HthInv".
          { iNext. iExists M0, T0. iFrame "∗%". iSplitR. by iPureIntro.
            iLeft. iFrame "AU Hc'". iPureIntro. intros [t [Ht Hss']].
            assert (t = T0) as -> by lia. done. }
          iModIntro; iFrame "∗#". }
      iDestruct "H'" as ">(Ds & #HthInv)".

      iModIntro. iSplitR "Hproph1 Hproph2 Token". iNext.
      iExists M0, T0, s0. iFrame "∗%".
      iExists (R0 ∪ {[tid]}), G0'. iFrame.
      iSplitR. iPureIntro. subst G0'. rewrite dom_insert_L.
      clear -Domm_G0; set_solver.
      rewrite (big_sepS_delete _ (R0 ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar". 
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. iFrame "∗#".
      assert ((R0 ∪ {[tid]}) ∖ {[tid]} = R0) as H' 
                by (clear -tid_notin_R0; set_solver).
      by rewrite H'.
      
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thd".
      { iFrame "#". }
    
      iModIntro. wp_apply (dsOp_spec with "[] [] [Hproph1]"); try done.
      { iFrame "Hproph1". iRight. iFrame "#%". }
      
      iIntros (res)"Hor". iDestruct "Hor" as "[Hor | Hor]".
      { iDestruct "Hor" as "(%&_)"; exfalso; try done. }
      
      iDestruct "Hor" as "(_&#PastW)". wp_pures. 
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                _ _ _ _ _ _ _ (res))
        with "Hproph2"); try done.
      { rewrite /typed_proph_from_val /= resT_proph_resolve. done. }
    
      wp_pures. iModIntro. iIntros "<-". wp_pure credit: "Hc1". 
      wp_pure credit: "Hc2". 
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & Templ)".
      iApply (lc_fupd_add_later with "Hc1"). iNext. 
      iDestruct "Help" as (R1 G1)"(HG & %Domm_G1 & Hstar)".
      
      iAssert (⌜tid ∈ R1⌝)%I as "%tid_in_R1".
      { iPoseProof (own_valid_2 _ _ _ with "[$HG] [$Hreg_gh]") as "%H'".
        apply auth_both_valid_discrete in H'. destruct H' as [H' _].
        apply dom_included in H'. rewrite dom_singleton_L -Domm_G1 in H'.
        iPureIntro. clear -H'; set_solver. }
    
      iAssert (⌜dom M1 = gset_seq 0 T1⌝)%I as %Dom_M1. 
      { by iDestruct "Hist" as (M1') "(_&_&%&_)". }

      iInv "HthInv" as (M1_th T1_th)"(>Hth_sy & >%Dom_M1' & >%Ht0 & Hth_or)".
      iApply (lc_fupd_add_later with "Hc2"). iNext. 
      iAssert (⌜M1_th = M1⌝)%I as %->.
      { rewrite (big_sepS_delete _ R1 tid); try done.
        iDestruct "Hstar" as "(H' & _)". 
        iDestruct "H'" as (? γ_sy' ?????)"(_&#H'&H''&_)".
        iDestruct "Thd" as "(H1'&_)". iDestruct "H'" as "(H1''&_)".
        iCombine "H1'" "H1''" as "H2'".
        iPoseProof (own_valid with "H2'") as "%HV".
        rewrite auth_frag_valid in HV. 
        apply singleton_valid, to_agree_op_inv, leibniz_equiv in HV. 
        inversion HV. subst γ_sy'.
        iPoseProof (own_valid_2 _ _ _ with "[$H''] [$Hth_sy]") as "%H'".
        rewrite frac_agree_op_valid_L in H'. iPureIntro; symmetry; apply H'. }
      assert (T1_th = T1) as ->.
      { rewrite Dom_M1' in Dom_M1. by apply gset_seq_eq. }
      iDestruct "Hth_or" as "[HPending | HDone]".
      { iExFalso. iDestruct "HPending" as "(_&_&%HPending)".
        iDestruct "PastW" as (s) "(#PastW & %Hseq)".
        iDestruct "PastW" as (t)"(%T0_le_t & Ht)".
        iDestruct "Hist" as (M1') "(H'&H''&H''')".
        iPoseProof (history_sync with "[$H''] [$Ht]") as "%H'".
        iDestruct "H'''" as "(_&%H''&_)". apply H'' in H'.
        iPureIntro. apply HPending. exists t. split. split; try done.
        apply elem_of_dom_2 in H'. rewrite Dom_M1 elem_of_gset_seq in H'. lia.
        apply lookup_total_correct in H'. by rewrite H'. }
    
      iDestruct "HDone" as "(HDone & #PastW')".
      iDestruct "HDone" as "[HΦ | Token']"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Token']") as "%".
        exfalso; try done. }
      
      iModIntro. iSplitL "Hth_sy Token".
      iNext. iExists M1, T1. iFrame "Hth_sy %". iRight. iFrame "#". by iRight.
      iModIntro. iSplitR "HΦ". iNext. iExists M1, T1, s1; iFrame "∗%".
      iExists R1, G1; iFrame "∗%".
      done. Unshelve. all: try done. admit.
  Admitted.
  
End CLIENT_SPEC.
