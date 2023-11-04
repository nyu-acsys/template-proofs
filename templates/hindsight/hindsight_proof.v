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

  
  Parameter dsOp_spec: ∀ N γ_t γ_r γ_m γ_mt γ_msy op r (p: proph_id) pvs 
     tid t0 Q,
          main_inv N γ_t γ_r γ_m γ_mt γ_msy  -∗
          thread_start γ_t γ_mt tid t0 -∗
          □ update_helping_protocol N γ_t γ_r γ_mt γ_msy -∗
          □ update_helping_protocol2 N γ_t γ_r γ_mt γ_msy -∗
            {{{ proph p pvs ∗ 
                (match process_proph tid pvs with
                  None => au N γ_r op Q
                | Some (i, None) => True
                | Some (i, Some j) => au N γ_r op Q end) }}}
                  dsOp (Op_to_val op) #r #p @ ⊤
            {{{ (res: resT) pvs', RET #res;
                proph p pvs' ∗
                (match process_proph tid pvs with
                  None => ⌜process_proph tid pvs' = None⌝ 
                | Some (i, None) => past_lin_witness γ_m op res t0
                | Some (i, Some j) => Q #res ∨ 
                    ⌜∃ i' j', process_proph tid pvs' = Some(i', Some (j'))⌝ end) }}}.
  
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
      resolve_proph: "p_upd" to: "t_id";;
      resolve_proph: "p" to: "v";;
      "v".


  Lemma dsOp'_spec N γ_t γ_r γ_m γ_mt γ_msy op (r: loc) :
          main_inv N γ_t γ_r γ_m γ_mt γ_msy -∗
              <<{ ∀∀ a, dsRep γ_r a }>> 
                     dsOp' (Op_to_val op) #r @ ↑N
              <<{ ∃∃ a' res, dsRep γ_r a' ∗ ⌜seq_spec op a a' res⌝ 
                  | RET #res }>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pure credit:"Hc'". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (pvs p1)"Hproph1". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 resTTypedProph); first done.
    iIntros (vp p2) "Hproph2". wp_pures.
    
    iAssert (update_helping_protocol N γ_t γ_r γ_mt γ_msy)%I 
        as "Upd_help". 
    { iIntros (M T s)"%Dom_M Ds Prot".
      iDestruct "Prot" as (Mt Msy)"(HMt & HMsy & %Domm_Mt & Hstar_t & Hstar_sy)".
      set R := dom Msy.
      iAssert (dsRep γ_r (abs s) -∗
        ([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_mt γ_msy t_id M) ={⊤ ∖ ↑cntrN N}=∗
        (([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_mt γ_msy t_id (<[T+1:=s]> M))
        ∗ dsRep γ_r (abs s)))%I as "H'".
      { iIntros "Ds". 
        iInduction R as [|tid' R' tid_notin_R IH] "HInd" using set_ind_L; 
          auto using big_sepS_empty'.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        assert (({[tid']} ∪ R') ∖ {[tid']} = R') as HR'. set_solver. rewrite HR'.
        iIntros "(Htid & Hbigstar)". 
        iMod ("HInd" with "[$Ds] Hbigstar") as "(H' & Ds)". iFrame "H'". 
        iDestruct "Htid" as (γ_tk' γ_sy' Q' op' vp' t0')
          "(#Hthst & #Hthsy & Hsy & #HthInv)".
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
            iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0'.
            iFrame "∗#%".
          + iModIntro. iSplitL "AU Hc Hsy". iNext. iExists (<[T+1:=s]> M), (T+1).
            iFrame "∗%". iLeft. iFrame. iPureIntro. 
            { intros [t [Ht1 Ht2]]. destruct (decide (t = T+1)) as [-> | Ht].
              rewrite lookup_total_insert in Ht2. done.
              apply Past_W. exists t. split. lia. 
              rewrite lookup_total_insert_ne in Ht2; try done. } 
            iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0'.
            iFrame "∗#%".
        - iDestruct "HDone" as "(HDone & >%PastW)".
          iModIntro. iSplitL "HDone Hsy". iNext. iExists (<[T+1:=s]> M), (T+1).
          iFrame "∗%". iRight. iSplitL; last first. iPureIntro.
          { destruct PastW as [t [Ht1 Ht2]]. exists t. split. lia.
            rewrite lookup_total_insert_ne. done. lia. } iFrame.
          iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0'.
          iFrame "∗#%". }
      iPoseProof ("H'" with "[$Ds] [$Hstar_sy]") as ">(Hstar_sy & Ds)".
      iModIntro. iFrame. iExists Mt, Msy. iFrame "∗%". }

    iAssert (update_helping_protocol2 N γ_t γ_r γ_mt γ_msy)%I 
        as "Upd_help2". 
    { iIntros (M T s')"%Dom_M %Habs Prot".
      iDestruct "Prot" as (Mt Msy)"(HMt & HMsy & %Domm_Mt & Hstar_t & Hstar_sy)".
      set R := dom Msy.
      iAssert (([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_mt γ_msy t_id M) ={⊤ ∖ ↑cntrN N}=∗
        (([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_mt γ_msy t_id (<[T+1:=s']> M))))%I as "H'".
      { iInduction R as [|tid' R' tid_notin_R IH] "HInd" using set_ind_L; 
          auto using big_sepS_empty'.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        assert (({[tid']} ∪ R') ∖ {[tid']} = R') as HR'. set_solver. rewrite HR'.
        iIntros "(Htid & Hbigstar)". 
        iMod ("HInd" with "Hbigstar") as "H'". iFrame "H'". 
        iDestruct "Htid" as (γ_tk' γ_sy' Q' op' vp' t0')
          "(#Hthst & #Hthsy & Hsy & #HthInv)".
        iInv "HthInv" as (M'' T'')"Hstate".
        iDestruct "Hstate" as "(>Hsy' & >%Dom_M'' & >%Ht0 & Hstate)".
        iAssert (⌜M'' = M⌝)%I as %->.
        { iPoseProof (own_valid_2 _ _ _ with "[$Hsy] [$Hsy']") as "%H'".
          rewrite frac_agree_op_valid_L in H'. iPureIntro; symmetry; apply H'. }
        assert (T'' = T) as ->.
        { rewrite Dom_M in Dom_M''. apply gset_seq_eq in Dom_M''. done. }
        iAssert (|={⊤ ∖ ↑cntrN N ∖ ↑threadN N}=> 
            own γ_sy' (to_frac_agree (1 / 2) (<[T+1:=s']> M))
          ∗ own γ_sy' (to_frac_agree (1 / 2) (<[T+1:=s']> M)))%I
          with "[Hsy Hsy']" as ">(Hsy & Hsy')".
        { iCombine "Hsy Hsy'" as "H'". 
          iEval (rewrite <-frac_agree_op) in "H'".
          iEval (rewrite Qp.half_half) in "H'".
          iMod ((own_update (γ_sy') (to_frac_agree 1 M) 
                        (to_frac_agree 1 (<[T+1 := s']> M))) with "[$H']") as "H'".
          { apply cmra_update_exclusive. 
            rewrite /valid /cmra_valid /= /prod_valid_instance.
            split; simpl; try done. }
          iEval (rewrite <-Qp.half_half) in "H'".
          iEval (rewrite frac_agree_op) in "H'".  
          iDestruct "H'" as "(Hsy & Hsy')". by iFrame. }
        assert (dom (<[(T + 1)%nat:=s']> M) = gset_seq 0 (T + 1)) as Dom_M'.
        { rewrite dom_insert_L Dom_M. apply set_eq_subseteq. split.
          all: intros x; rewrite elem_of_union elem_of_singleton 
            !elem_of_gset_seq; lia. }
        assert (t0' ≤ T+1) as Ht0' by lia.
        iDestruct "Hstate" as "[HPending | HDone]".
        - iDestruct "HPending" as "(AU & >Hc & >%Past_W)".
          iModIntro. iSplitL "AU Hc Hsy". iNext. iExists (<[T+1:=s']> M), (T+1).
          iFrame "∗%". iLeft. iFrame. iPureIntro. 
          { intros [t [Ht1 Ht2]]. destruct (decide (t = T+1)) as [-> | Ht].
            rewrite lookup_total_insert Habs in Ht2. 
            apply Past_W. exists T. split. lia. done.
            rewrite lookup_total_insert_ne in Ht2; try done.
            apply Past_W. exists t. split. lia. done. } 
          iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0'.
          iFrame "∗#%".
        - iDestruct "HDone" as "(HDone & >%PastW)".
          iModIntro. iSplitL "HDone Hsy". iNext. iExists (<[T+1:=s']> M), (T+1).
          iFrame "∗%". iRight. iSplitL; last first. iPureIntro.
          { destruct PastW as [t [Ht1 Ht2]]. exists t. split. lia.
            rewrite lookup_total_insert_ne. done. lia. } iFrame.
          iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0'.
          iFrame "∗#%". }
      iPoseProof ("H'" with "[$Hstar_sy]") as ">Hstar_sy".
      iModIntro. iFrame. iExists Mt, Msy. iFrame "∗%". }

    iApply fupd_wp. 
    iInv "HInv" as (M0 T0 s0) "(Ds & >%Habs0 & Hist & Help & Templ)".
    iApply (lc_fupd_add_later with "Hc"). iNext. 
    iDestruct "Help" as (Mt0 Msy0)"(HMt & HMsy & %Domm_Mt0 & Hstar_t & Hstar_sy)".
  
    iAssert (¬ ⌜tid ∈ dom Mt0⌝)%I as %tid_notin_Mt0.
    { iIntros "%H'". 
      iEval (rewrite (big_sepS_elem_of_acc _ (dom Mt0) tid); 
        last by eauto) in "Hstar_t".
      iDestruct "Hstar_t" as "(H' & _)". iDestruct "H'" as (?)"H'".
      iApply (proph1_exclusive tid with "[Htid]"); try done. }
    
    iPoseProof (own_update _ (● Mt0) 
      (● (<[tid := to_agree T0]> Mt0) ⋅ ◯ {[tid := to_agree T0]}) with "HMt")
      as ">(HMt & Thd_st')".
    { apply auth_update_alloc, alloc_local_update; last done.
      apply not_elem_of_dom. done. }
    
    iDestruct "Hist" as (M0')"(H'&H'')".
    iPoseProof (own_update _ (● MaxNat T0) (● MaxNat T0 ⋅ ◯ MaxNat T0) 
      with "H'") as ">(H' & Thd_st'')".
    { apply (auth_update_alloc _ _ (MaxNat T0)), max_nat_local_update. lia. }
    iAssert (hist γ_t γ_m M0 T0) with "[H' H'']" as "Hist".
    { iExists M0'. iFrame. } clear M0'.
    iAssert (thread_start γ_t γ_mt tid T0) with "[Thd_st'' Thd_st']" as "#Thd_st".
    { iFrame. } iClear "Thd_st' Thd_st''".

    set pres := process_proph tid pvs.
    assert (process_proph tid pvs = pres) as Def_pres by done.
    destruct pres as [[i o] | ]; last first; last (destruct o as [j |]).

    - iModIntro. iSplitR "AU Hproph1 Hproph2". iNext. 
      iExists M0, T0, s0. iFrame "∗%".
      iExists (<[tid := to_agree T0]> Mt0), Msy0. iFrame. iSplitR. iPureIntro.
      rewrite dom_insert_L. clear -Domm_Mt0; set_solver. rewrite dom_insert_L.
      rewrite big_sepS_union. iFrame. rewrite big_sepS_singleton. by iExists vtid.
      set_solver. iModIntro.

      wp_apply (dsOp_spec with "[] [] [] [] [AU Hproph1]"); try done.
      { iFrame "Hproph1". rewrite Def_pres. iFrame "AU". }
      iIntros (res pvs')"(Hproph1 & Hmatch)". rewrite Def_pres. wp_pures.
      iDestruct "Hmatch" as %Hpvs'. 
      wp_apply (wp_resolve_proph with "[Hproph1]"); try done.
      iIntros (pvs'')"(%Def_pvs' & Hproph1)". exfalso. 
      apply process_proph_case1 in Hpvs'. rewrite Forall_lookup in Hpvs'.
      assert (pvs' !! 0 = Some (#(), #tid)) as H'. rewrite Def_pvs'. set_solver.
      pose proof Hpvs' 0 _ H' as H''. by simpl in H''.
    
    - iModIntro. iSplitR "AU Hproph1 Hproph2". iNext. 
      iExists M0, T0, s0. iFrame "∗%".
      iExists (<[tid := to_agree T0]> Mt0), Msy0. iFrame. iSplitR. iPureIntro.
      rewrite dom_insert_L. clear -Domm_Mt0; set_solver. rewrite dom_insert_L.
      rewrite big_sepS_union. iFrame. rewrite big_sepS_singleton. by iExists vtid.
      set_solver. iModIntro.

      wp_apply (dsOp_spec with "[] [] [] [] [AU Hproph1]"); try done.
      { iFrame "Hproph1". rewrite Def_pres. iFrame "AU". }
      iIntros (res pvs')"(Hproph1 & Hmatch)". rewrite Def_pres. wp_pures.
      wp_apply (wp_resolve_proph with "[Hproph1]"); try done.
      iIntros (pvs'')"(%Def_pvs' & Hproph1)". wp_pures.
      iDestruct "Hmatch" as "[HΦ | %H']"; last first.
      { exfalso. destruct H' as [i' [j' H']].
        assert (pvs' !! 0 = Some (#(), #tid)) as Hp0. rewrite Def_pvs'; set_solver.
        apply process_proph_case3 in H'. destruct H' as (Hi'&Hj'&Hji'&_).
        destruct (decide (i' = 0)) as [-> | Hi0]; try (done || lia).
        apply list_lookup_total_correct in Hp0. assert (0 < i') as H'' by lia.
        pose proof Hj' 0 H'' as H1'. rewrite Hp0 in H1'. done. }
      
      wp_apply (typed_proph_wp_resolve1 resTTypedProph with "Hproph2"); try done.
      { rewrite /typed_proph_from_val /=. by rewrite resT_proph_resolve. }
      wp_pures. iModIntro. iIntros "_". wp_pures. done.
    
    - iMod (own_alloc (to_frac_agree (1) (M0))) 
              as (γ_sy)"Hfr_t". { try done. }        
      iEval (rewrite <-Qp.half_half) in "Hfr_t".      
      iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
      iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  

      iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.

      iPoseProof (own_update _ (● Msy0) 
        (● (<[tid := to_agree γ_sy]> Msy0) ⋅ ◯ {[tid := to_agree γ_sy]}) 
        with "HMsy") as ">(HMsy & #Thd_sy)".
      { apply auth_update_alloc, alloc_local_update; last done.
        apply not_elem_of_dom. clear -tid_notin_Mt0 Domm_Mt0. set_solver. }

      iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
      { by iDestruct "Hist" as (M0') "(_&_&%&_)". }

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
      iExists (<[tid:=to_agree T0]> Mt0), (<[tid:=to_agree γ_sy]> Msy0). iFrame.
      iSplitR. iPureIntro. rewrite !dom_insert_L. clear -Domm_Mt0; set_solver.
      rewrite !dom_insert_L. rewrite !big_sepS_union. rewrite !big_sepS_singleton.
      iFrame. iSplitL "Htid". by iExists vtid.
      iExists γ_tk, γ_sy, Φ, op, vp, T0. iFrame "∗#". set_solver. set_solver.
      
      iModIntro. wp_apply (dsOp_spec with "[] [] [] [] [Hproph1]"); try done.
      { iFrame "Hproph1". by rewrite Def_pres. }

      iIntros (res pvs')"(Hproph1 & Hmatch)". rewrite Def_pres. wp_pures.
      wp_apply (wp_resolve_proph with "[Hproph1]"); try done.
      iIntros (pvs'')"(%Def_pvs' & Hproph1)". wp_pures.
      
      iDestruct "Hmatch" as "#PastW". wp_pures. 
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                _ _ _ _ _ _ _ (res))
        with "Hproph2"); try done.
      { rewrite /typed_proph_from_val /= resT_proph_resolve. done. }
    
      wp_pures. iModIntro. iIntros "<-". wp_pure credit: "Hc1". 
      wp_pure credit: "Hc2". 
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & Templ)".
      iApply (lc_fupd_add_later with "Hc1"). iNext. 
      iDestruct "Help" as (Mt1 Msy1)"(HMt & HMsy & %Domm_Mt1 & Hstar_t & Hstar_sy)".
      
      iAssert (⌜tid ∈ dom Msy1⌝)%I as "%tid_in_Msy1".
      { iPoseProof (own_valid_2 _ _ _ with "[$HMsy] [$Thd_sy]") as "%H'".
        apply auth_both_valid_discrete in H'. destruct H' as [H' _].
        apply dom_included in H'. rewrite dom_singleton_L in H'.
        iPureIntro. clear -H'; set_solver. }
    
      iAssert (⌜dom M1 = gset_seq 0 T1⌝)%I as %Dom_M1. 
      { by iDestruct "Hist" as (M1') "(_&_&%&_)". }

      iInv "HthInv" as (M1_th T1_th)"(>Hth_sy & >%Dom_M1' & >%Ht0 & Hth_or)".
      iApply (lc_fupd_add_later with "Hc2"). iNext. 
      iAssert (⌜M1_th = M1⌝)%I as %->.
      { rewrite (big_sepS_delete _ (dom Msy1) tid); try done.
        iDestruct "Hstar_sy" as "(H' & _)". 
        iDestruct "H'" as (? γ_sy' ????)"(_&#H'&H''&_)".
        iCombine "H'" "Thd_sy" as "H1'".
        iPoseProof (own_valid with "H1'") as "%HV".
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
      iExists Mt1, Msy1; iFrame "∗%". done. Unshelve. done.
  Qed.
  
End CLIENT_SPEC.
