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
  Import DS.

  Parameter dsOp_upd_spec: ∀ N γ_r γ_t γ_m γ_td1 γ_td2 γ_ght op (r: Node) 
                          γ_sy t_id t0 Q,
          DEFS.main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
          □ DEFS.update_helping_protocol N γ_t γ_r γ_td1 γ_td2 γ_ght -∗
          DEFS.thread_vars γ_t γ_ght γ_sy t_id t0 -∗
            {{{ DEFS.au N γ_r op Q }}} 
                  dsOp (Op_to_val op) #r
            {{{ (res: resT), RET #res; 
                  if updater_thread op res then Q #res
                  else DEFS.past_lin_witness γ_m op res t0 }}}.

(*
  Parameter dsOp_nupd_spec: ∀ N γ_r γ_t γ_m γ_td1 γ_td2 γ_ght op (r: Node) 
                          γ_sy t_id t0,
          DEFS.main_inv N γ_t γ_r γ_m γ_td γ_ght -∗
          □ DEFS.update_helping_protocol N γ_t γ_r γ_td γ_ght -∗
          DEFS.thread_vars γ_t γ_ght γ_sy t_id t0 -∗
            {{{ True }}} 
                  dsOp (Op_to_val op) #r
            {{{ res, RET #res; DEFS.past_lin_witness γ_m op res t0 }}}.
*)

End HINDSIGHT_SPEC.

Module CLIENT_SPEC (DS : DATA_STRUCTURE) (HS: HINDSIGHT_SPEC DS).
  Import DS HS.DEFS HS.
  
  (* Test zone *)
  
  Lemma test_and (P: iProp) : P -∗ P ∧ P.
  Proof.
    iIntros "HP". iSplit; try done.
  Qed.
  
  Definition test_fn : val :=
    λ: "l",
      let: "p" := NewProph in
      Resolve (!"l") "p" #1 ;;
      #().
      
  Definition test_inv N l : iProp := inv (cntrN N) (l ↦ #2).
  
  Lemma test_spec N l :
    test_inv N l -∗
      <<< True >>> test_fn #l @ ⊤ <<< True, RET #() >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam.
    wp_apply wp_new_proph1; first done.
    iIntros (p vp)"Hproph". wp_pures. wp_bind (Resolve _ _ _)%E.
    iInv "HInv" as ">H'".
    wp_apply (wp_resolve1 with "Hproph"); try done.  
    wp_load. iModIntro.
    iIntros "%". Search proph.
    iModIntro. iSplitL "H'"; try iFrame.
    wp_pures. iMod "AU" as "[_ [_ Hcl]]".
    by iApply "Hcl".
  Qed.
    
    
  (* Test zone end *)
  

  Definition dsOp' : val :=
    λ: "OP" "r",     
      let: "t_id" := NewProph in
      let: "p" := NewProph in
      let: "v" := dsOp "OP" "r" in
      resolve_proph: "p" to: "v";;
      "v".
        
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
  

  Lemma dsOp'_spec N γ_s γ_t γ_m γ_td1 γ_td2 γ_ght op (r: Node) :
          DEFS.main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
              <<< ∀∀ a, dsRep γ_s a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N)
              <<< ∃∃ a' res, dsRep γ_s a' ∗ ⌜seq_spec op a a' res⌝, 
                  RET #res >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pure credit:"Hc1". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 resTTypedProph); first done.
    iIntros (vp p)"Hproph". wp_pures.
    
    destruct (decide (updater_thread op vp = true)) as [Upd_thr | Upd_thr].
    - 
    iApply fupd_wp. 
    iInv "HInv" as (M0 T0 s0) "(>HCntr & >%Habs0 & >Hist & Help & Templ)".
    iApply (lc_fupd_add_later with "Hc1"). iNext. 
    iDestruct "Help" as (R1 R2 hγt)"(HR1 & HR2 & Hγt & 
      Domm_hγt & Hstar1 & Hstar2)".
    
    iAssert (¬ ⌜tid ∈ R1 ∪ R2⌝)%I as %H'.
    { admit. }
    assert (tid ∉ R1 ∪ R2) as tid_notin_R12 by done.
    clear H'.
    (*
    iAssert (▷ (⌜tid ∉ R⌝ 
            ∗ ([∗ set] t_id ∈ R, Reg N γ_t γ_s γ_ght t_id M0) 
            ∗ proph1 tid vtid))%I with "[Hstar_reg Htid]" 
            as "(>%tid_notin_R & Hstar_reg & Htid)".
    { destruct (decide (tid ∈ R)); try done.
      - iEval (rewrite (big_sepS_elem_of_acc _ (R) tid); 
                            last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg & Hstar_reg')".
        iDestruct "Hreg" as (? ? ? ? ? ? ?)"(H' & _)".
        iAssert (▷ False)%I with "[H' Htid]" as "HF".
        iApply (proph1_exclusive tid with "[Htid]"); try done.
        iNext. iExFalso; try done.
      - iNext. iFrame. by iPureIntro. }
    *)
    
    iMod (own_update γ_td1 (● R1) (● (R1 ∪ {[tid]})) with "[$HR1]") as "HR1".
    { apply (auth_update_auth _ _ (R1 ∪ {[tid]})).
      apply gset_local_update. set_solver. }
    iMod (own_update γ_td1 (● (R1 ∪ {[tid]})) (● (R1 ∪ {[tid]}) ⋅ ◯ {[tid]}) 
              with "[$HR1]") as "(HR1 & #FP_t)".
    { apply (auth_update_dfrac_alloc _ (R1 ∪ {[tid]}) ({[tid]})).
      apply gset_included. clear; set_solver. }
      
    iMod (own_alloc (1)%Qp) as (γ_fr)"Hfr". { try done. }
    iEval (rewrite <-Qp.half_half) in "Hfr".      
    iEval (rewrite -(frac_op (1/2) (1/2))) in "Hfr". 
    iDestruct "Hfr" as "(Hfr1 & Hfr2)". 

    (*
    iMod (own_alloc (to_frac_agree (1) (M0))) 
            as (γ_sy)"Hfr_t". { try done. }        
    iEval (rewrite <-Qp.half_half) in "Hfr_t".      
    iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
    iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  
    *)
    
    iDestruct "Domm_hγt" as %Domm_hγt.
    set (<[ tid := to_agree (T0, γ_fr) ]> hγt) as hγt'.
    iDestruct (own_update _ _ 
      (● hγt' ⋅ ◯ {[ tid := to_agree (T0, γ_fr) ]})
             with "Hγt") as ">Hγt".
    { apply auth_update_alloc. 
      rewrite /hγt'.
      apply alloc_local_update; last done.
      rewrite <-Domm_hγt in tid_notin_R12.
      by rewrite not_elem_of_dom in tid_notin_R12. }
    iDestruct "Hγt" as "(Hγt & #Hreg_gh)".
    (*  
    iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.
    *)
    iAssert (⌜map_max M0 = T0⌝)%I as %M_max. 
    { by iDestruct "Hist" as (M0') "(_&_&%&_)". }
    iDestruct "Hist" as (M0')"(H'&H'')". Check own_update.
    iDestruct (own_update _ _ (● (MaxNat T0) ⋅ ◯ (MaxNat T0)) with "H'") 
      as ">H1'".
    { apply auth_update_alloc. apply max_nat_local_update. 
      try done. }
    iDestruct "H1'" as "(H' & #HfragT0)".
    iAssert (hist γ_t γ_m M0 T0) with "[H' H'']" as "Hist".
    { iExists M0'; iFrame. }
    
    iModIntro. iSplitR "Hproph Hfr1". iNext.
    iExists M0, T0, s0. iFrame "∗%".
      iExists (R1 ∪ {[tid]}), R2, hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R1 ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar1". unfold Reg_upd.
      iExists γ_fr, Φ, op, vp, T0, vtid.
      rewrite Upd_thr; iFrame "∗#". iSplitR. { by iPureIntro. }
      iLeft. iFrame.
      assert ((R1 ∪ {[tid]}) ∖ {[tid]} = R1) as H' 
                  by (clear -tid_notin_R12; set_solver).
      by rewrite H'.
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td1 γ_td2 γ_ght)%I 
        as "Upd_help". { admit. }
      iAssert (thread_vars γ_t γ_ght γ_fr tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_upd_spec with "[] [] [] []"); try done.
      
      iIntros (res)"HpastW". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }  
      wp_pures. iModIntro. iIntros "%vp_eq_res". subst vp.
      rewrite Upd_thr. wp_pures; try done.
    
    destruct (decide (updater_thread op vp = true)) as [Upd_thr | Upd_thr].
    - iModIntro. iSplitR "AU Hproph". iNext.
      iExists M0, T0, s0. iFrame "∗%".
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid.
      rewrite Upd_thr; iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_upd_spec with "[] [] [] [AU]"); try done.
      
      iIntros (res)"HpastW". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }  
      wp_pures. iModIntro. iIntros "%vp_eq_res". subst vp.
      rewrite Upd_thr. wp_pures; try done.
    - rewrite not_true_iff_false in Upd_thr.
      assert (∀ op c c' res, Decision (seq_spec op c c' res)) 
        as seq_spec_dec. { apply seq_spec_dec. }
      destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))
        as [Hss | Hss].
      + 
      iMod "AU" as (c) "[Cntr [_ Hcomm]]".
      iAssert (⌜c = abs s0⌝)%I as "%". 
      { unfold dsRep, dsRepI. Search own valid.
        iDestruct (own_valid_2 with "[$Cntr] [$HCntr]") as %H'.
        rewrite frac_agree_op_valid_L in H'.
        destruct H' as [_ H']; by iPureIntro. } subst c. 
      iSpecialize ("Hcomm" $! (abs s0) vp). 
      iMod ("Hcomm" with "[Cntr]") as "HΦ".
      { iFrame. apply leibniz_equiv in Habs0. 
        rewrite Habs0 in Hss. by iPureIntro. }
   
      iAssert (past_lin M0 T0 op vp T0)%I as "Hpast".
      { iPureIntro. exists T0. split; try done. }
        
      iMod (inv_alloc (threadN N) _
            (∃ M T, State γ_sy γ_tk (au N γ_s op Φ) Φ M T op vp T0) 
                                  with "[Hreg_sy1 Token]") as "#HthInv".
      { iNext. iExists M0, T0. iFrame "Hreg_sy1".
        iSplitR. by iPureIntro.
        iRight. unfold Done. iFrame "Hpast".
        by iRight. }
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". }
  
      
      iModIntro. iSplitR "Hproph HΦ". iNext.
      iExists M0, T0, s0.  iFrame "∗%".
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. rewrite Upd_thr. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                by (clear -tid_notin_R; set_solver).
      by rewrite H'.  
        
      iModIntro.
      wp_apply (dsOp_nupd_spec); try done.
      iIntros (res)"Hres". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }
      wp_pures. iModIntro. iIntros "->".
      wp_pures. iModIntro. done.
      + 
      iMod (inv_alloc (threadN N) _
              (∃ M T, State γ_sy γ_tk (au N γ_s op Φ) Φ M T op vp T0) 
                                    with "[AU Hc Hreg_sy1]") as "#HthInv".
      { iNext. iExists M0, T0. iFrame "Hreg_sy1".
        iSplitR. { by iPureIntro. }
        iLeft. unfold Pending. iFrame "AU Hc". 
        unfold past_lin. iIntros "%Hpast". 
        destruct Hpast as [t [H' Hss']].
        assert (t = T0) as -> by lia. contradiction. }

      iModIntro. iSplitR "Hproph Token". iNext.
      iExists M0, T0, s0. iFrame "∗%".
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. rewrite Upd_thr. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_nupd_spec); try done.
      iIntros (res)"HpastW".
      
      wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }  
      wp_pures. iModIntro. iIntros "%vp_eq_res". subst vp.
       
      iApply fupd_wp.
      iDestruct "HpastW" as "(%Upd_thr' & HpastW)".
      
      iInv "HthInv" as (M1_th T1_th)"(>Hth_sy & >% & Hth_or)".
      iInv "HInv" as (M1 T1 s1) "(>HCntr & >%Habs1 & >Hist & Help & Templ)".
      iDestruct "Help" as (R1 hγt1)"(>HR & >Hγt 
                                  & >Domm_hγt & Hstar_reg)".
      
      iAssert (⌜tid ∈ R1⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HR] [$FP_t]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro. set_solver. }
      rename H into tid_in_R1.
      
      iAssert (⌜map_max M1 = T1⌝)%I as %M_max1. 
      { by iDestruct "Hist" as (M1') "(_&_&%&_)". }

      iAssert (▷ (⌜M1_th = M1⌝ ∗ ⌜T1_th = T1⌝ 
               ∗ ([∗ set] t_id ∈ R1, Reg N γ_t γ_s γ_ght t_id M1)
               ∗ own (γ_sy) (to_frac_agree (1 / 2) M1_th) ))%I
                with "[Hstar_reg Hth_sy]" as "(>% & >% & Hstar_reg & >Hth_sy)". 
      { 
        iEval (rewrite (big_sepS_elem_of_acc _ (R1) tid); 
                                last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg_t & Hstar_reg')".
        iDestruct "Hreg_t" as (γ_tk' γ_sy' Q' op' vp' t0' vtid')
                          "(Hreg_proph & >Hreg_gh' & >Hreg_sy & H')".
        iDestruct "Hreg_gh'" as "(Hreg_gh' & #?)".
        iCombine "Hreg_gh" "Hreg_gh'" as "H''".
        iPoseProof (own_valid with "H''") as "Valid".
        iDestruct "Valid" as %Valid.
        rewrite auth_frag_valid in Valid.
        apply singleton_valid in Valid.
        apply to_agree_op_inv in Valid.
        apply leibniz_equiv in Valid.
        injection Valid; intros <- <-.


        iAssert (⌜M1_th = M1 ∧ T1_th = T1⌝)%I as "(% & %)".
        { iPoseProof (own_valid_2 _ _ _ with "[$Hth_sy] [$Hreg_sy]") 
              as "V_M".
          iDestruct "V_M" as %V_M.
          apply frac_agree_op_valid in V_M. destruct V_M as [_ V_M].
          iPureIntro. split; first by apply leibniz_equiv.
          rewrite tid_in_R1. apply leibniz_equiv in V_M. by rewrite V_M. } 
        subst M1_th T1_th.
          
        iSplitR. { by iPureIntro. } 
        iSplitR. iNext; by iPureIntro.
        iSplitR "Hth_sy". iApply "Hstar_reg'".
        iNext. iExists γ_tk', γ_sy, Q', op', vp', T0, vtid'.
        iFrame "∗#". by iNext. 
      } subst M1_th T1_th.
      
      iEval (unfold past_lin_witness) in "HpastW".
      (* iEval (rewrite Upd_thr) in "HpastW".*)

      iDestruct "Hth_or" as "[HPending | HDone]".
      { iDestruct "HPending" as "(AU & Hc & >%HPending)".
        iDestruct "HpastW" as (s) "(HpastW & %Hseq)".
          iDestruct "HpastW" as (t)"(%T0_le_t & Ht)".
          iDestruct "Hist" as (M1') "(H'&H''&H''')".
          iDestruct (history_sync with "[$H''] [$Ht]") as "%M1'_t".
          iDestruct "H'''" as %(H1' & _ & H1'' & H1''').
          apply (H1'' t s) in M1'_t.
          exfalso. apply HPending. exists t.
          split.
          + split; try done. apply elem_of_dom_2 in M1'_t.
            by apply map_max_dom in M1'_t.
          + rewrite !lookup_total_alt. rewrite M1'_t. by simpl. }
      
      iDestruct "HDone" as "(HDone & Hpast)".  
      iDestruct "HDone" as "[HDone | >Hth_or]"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Hth_or]") as "%".
        exfalso; try done. }
        
      iModIntro. iSplitR "HDone Hth_sy Token Hpast".
      iExists M1, T1, s1; iFrame "∗%".
      iNext. iExists R1, hγt1; iFrame.     

      iModIntro. iSplitL "Token Hth_sy Hpast".
      iNext. iExists M1, T1. iFrame "Hth_sy". 
      iSplitR. by iPureIntro. iRight. iFrame "∗%".
      by subst T1.
      
      iModIntro. by wp_pures.
  Admitted.
  
End CLIENT_SPEC.
