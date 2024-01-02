From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
(* Require Import list_flow_upd_marking. *)
Require Export traverse_spec_module flows.
Require Import skiplist_util.

  Export TR.NODE SK DEFS.

  Lemma maintenanceOp_insert_rec_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r 
    tid t0 k (n: Node) preds succs (ps ss: list Node) perm vs xs (h i: nat) (hd tl: Node):
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
    r ↦□ (#hd, #tl) -∗
      {{{   preds ↦∗ ((λ n0 : loc, #n0) <$> ps)
          ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss)
          ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝ ∗ ⌜h < L⌝
          ∗ ⌜ps !!! (L - 1) = hd⌝ ∗ ⌜ss !!! (L - 1) = tl⌝
          ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜n ∈ FP s⌝ ∗ ⌜Height s n = h⌝)
          ∗ (∀ i, ⌜i < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k (ps !!! i) (ss !!! i))
          ∗ perm ↦∗ vs
          ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
          ∗ ⌜xs ≡ₚ seq 1 (h-1)⌝ }}}
         maintenanceOp_insert_rec #i #k #h #perm #preds #succs #n
      {{{ (ps' ss': list Node),
          RET #();
            preds ↦∗ ((λ n0 : loc, #n0) <$> ps')
          ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss')
          ∗ perm ↦∗ vs }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k] #HR'". iLöb as "IH" forall (i ps ss). 
    iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & %Len_ps & %Len_ss & %HhL 
      & %HpsL & %HssL & #FP_n & #Htr & Hperm & %Def_vs & %Perm_xs)".
    wp_lam. wp_pure credit: "Hc". wp_pures. 
    destruct (bool_decide (Z.lt i (h - 1)%Z)) eqn: Hbool; wp_pures.
    - rewrite bool_decide_eq_true in Hbool.
      assert (is_Some (xs !! i)) as [idx Hidx].
      { assert (i < length xs) as H'. rewrite Perm_xs seq_length. lia.
        by rewrite lookup_lt_is_Some. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i) (vs) #idx
        with "[Hperm]"); try done.
      { rewrite Def_vs. rewrite list_lookup_fmap. rewrite Hidx.
        by simpl. }
      iIntros "Hperm". wp_pures.
      assert (0 < idx < L-1) as HidxL.
      { apply elem_of_list_lookup_2 in Hidx. rewrite Perm_xs in Hidx.
        rewrite elem_of_seq in Hidx. lia. }
      assert (is_Some (ps !! idx)) as [p Hp].
      { rewrite lookup_lt_is_Some Len_ps. lia. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (idx) _ #p
        with "[Hpreds]"); try done.
      { by rewrite list_lookup_fmap Hp /=. }
      iIntros "Hpreds". wp_pures.
      assert (is_Some (ss !! idx)) as [c Hc].
      { rewrite lookup_lt_is_Some Len_ss. lia. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (idx) _ #c
        with "[Hsuccs]"); try done.
      { by rewrite list_lookup_fmap Hc /=. }
      iIntros "Hsuccs". wp_pures.
      awp_apply changeNext_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
      iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
      { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (traversal_inv _ _ _ _ γ_m t0 idx k p c) as "#Htr'".
      { apply list_lookup_total_correct in Hp. 
        apply list_lookup_total_correct in Hc.
        rewrite -Hp -Hc. iApply "Htr". iPureIntro. lia. }
      iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
      { apply leibniz_equiv in Habs0. rewrite -Habs0.
        iDestruct "Htr'" as "(Htr'&_)". 
        iDestruct "Htr'" as (s)"(Past_s & % & _)".
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done.  }
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAssert (⌜idx < Height s0 p⌝)%I as %Height_p0.
      { apply leibniz_equiv in Habs0. rewrite -Habs0.
        iDestruct "Htr'" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sc)".
        destruct Htr_sc as (H'&H''&_).
        iPoseProof (height_eq_2 _ _ _ _ p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. }
      iAssert ((node Σ p (Height s0 p) (Mark s0 p) (Next s0 p) (Key s0 p)) 
        ∗ ⌜idx < Height s0 p⌝)%I with "[Node_p]" as "Hpre".
      { iFrame "∗%". }
      iAaccIntro with "Hpre".
      { iIntros "(Node_p & _)". iModIntro. iFrame "Hpost Hc Hperm Hpreds Hsuccs".
        iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
      iIntros (success next')"(Node_p & Hif)".
      iApply (lc_fupd_add_later with "Hc"). iNext.

      iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
      { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
      iAssert (⌜Key s0 p < W⌝)%I as %Key_pW. 
      { iDestruct "Htr'" as "(Htr'&_)". 
        iDestruct"Htr'" as (s)"(Past_s & %FP_ps & _ & %Key_ps)".
        apply leibniz_equiv in Habs0. rewrite -Habs0.
        iPoseProof (key_eq_2 _ _ _ _ p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. iPureIntro. clear -Key_ps Range_k. lia. }
      assert (p ≠ tl) as p_neq_tl. 
      { intros ->. destruct PT_s0 as ((_&_&H'&_)&_).
        rewrite H' in Key_pW. clear -Key_pW. lia. }

      destruct success; last first; 
        last destruct (decide (n = c)) as [<- | n_neq_c].
      + iDestruct "Hif" as %[H' ->]. 
        iModIntro. iSplitR "Hpost Hperm Hpreds Hsuccs".
        { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
        wp_pures. 
        wp_apply (traverse_rec_spec with "[] [] [] [] [] [Hpreds Hsuccs]"); 
          try done.
        { iFrame "Hpreds Hsuccs".
          iSplitL. iPureIntro. apply Len_ps.
          iSplitL. iPureIntro. apply Len_ss.
          iSplitL. iPureIntro. lia. iSplitL. by iPureIntro. 
          iSplitL. by iPureIntro. iIntros (j)"%Hj".
          assert (j = L-1) as -> by lia. rewrite HpsL HssL. admit. }
        iIntros (ps' ss' b) "(Hpreds & Hsuccs & %Lep_ps' & %Len_ss' 
          & %HpsL' & %HssL' & #Htr'' & _)". wp_pures.
        iSpecialize ("IH" $! i ps' ss').
        iApply ("IH" with "[-Hpost]"); try done. iFrame "#∗%".
      + iDestruct "Hif" as %[Next_p0' [Mark_p0 Def_next']].
        assert (Next s0 p !! idx = Some n) as Next_p0.
        { rewrite lookup_lookup_total. by rewrite Next_p0'. rewrite -elem_of_dom.
          apply PT_s0 in FP_p0. destruct FP_p0 as (_&H'&_). rewrite H'; try done.
          rewrite elem_of_gset_seq. lia. }
        assert (next' = Next s0 p) as Hnext'. 
        { rewrite Def_next'. apply map_eq. intros i'. 
          destruct (decide (i' = idx)) as [-> | Hi].
          by rewrite lookup_insert Next_p0. by rewrite lookup_insert_ne. }
        rewrite Hnext'.
        iModIntro. iSplitR "Hpost Hperm Hsuccs Hpreds".
        { iNext. iExists M0, T0, s0. iFrame "∗#%". iExists hd, tl. iFrame "∗#%".
          rewrite (big_sepS_delete _ (FP s0) p); try done. iFrame. }
        wp_pures. iSpecialize ("IH" $! (i+1) ps ss).
        assert (Z.add i 1 = (i+1)%nat) as ->. clear; lia.
        iApply ("IH" with "[-Hpost]"); try done. 
        { iFrame "Hpreds Hsuccs".
          iSplitR. iPureIntro. apply Len_ps.
          iSplitR. iPureIntro. apply Len_ss.
          iSplitR. iPureIntro. lia. iSplitR. by iPureIntro. 
          iSplitR. by iPureIntro. iFrame "#". iFrame "Hperm".
          by iPureIntro. }
      + iDestruct "Hif" as %[Next_p0' [Mark_p0 Def_next']].
        iDestruct "SShot0" as %[FP0 [C0 [Ht0 [Mk0 [Nx0 [Ky0 [I0 
            [Hs0 [Dom_Ht0 [Dom_Mk0 [Dom_Nx0 [Dom_Ky0 Dom_I0]]]]]]]]]]]].
        set Nx0' := <[p := next']> Nx0.
        set s0' := (FP0, C0, Ht0, Mk0, Nx0', Ky0, I0): snapshot.
        set M0' := <[T0 + 1 := s0']> M0.
        
        assert (Next s0 p !! idx = Some c) as Next_p0.
        { rewrite lookup_lookup_total. by rewrite Next_p0'. rewrite -elem_of_dom.
          apply PT_s0 in FP_p0. destruct FP_p0 as (_&H'&_). rewrite H'; try done.
          rewrite elem_of_gset_seq. lia. }

        assert (FP s0' = FP s0) as FP_s0'.
        { by rewrite /FP /s0' Hs0. }
        assert (abs s0' = abs s0) as Habs'.
        { by rewrite /abs /s0' Hs0. }
        iAssert (dsRepI _ _ _ _ γ_r (abs s0'))%I with "[Ds]" as "Ds".
        { by rewrite Habs'. }
        iAssert (own γ_ks (● prodKS (KS, abs s0')))%I with "[GKS]" as "GKS".
        { by rewrite Habs'. }
        assert (∀ n, n ≠ p → Next s0' n = Next s0 n) as HN.
        { intros n' Hnp. 
          rewrite /Next /s0' Hs0 /= /Nx0' lookup_insert_ne; try done. }
        assert (Next s0' p = <[idx:=n]> (Next s0 p)) as HNp.
        { by rewrite /s0' Hs0 /Next /Nx0' lookup_insert Def_next' /Next Hs0. }
        assert (∀ n, Key s0' n = Key s0 n) as HK.
        { by rewrite /Key /s0' Hs0 /=. }
        assert (∀ n, FI s0' n = FI s0 n) as HI.
        { by rewrite /FI /s0' Hs0 /=. }
        assert (∀ n, Mark s0' n = Mark s0 n) as HM.
        { by rewrite /FI /s0' Hs0. }
        assert (∀ n, Height s0' n = Height s0 n) as HT.
        { by rewrite /FI /s0' Hs0. }

        iAssert (⌜snapshot_constraints s0'⌝)%I as "SShot1'".
        { iPureIntro. exists FP0, C0, Ht0, Mk0, Nx0', Ky0, I0.
          repeat split; try done.
          rewrite /Nx0'. rewrite dom_insert_L.
          assert (p ∈ dom Nx0). 
          { rewrite Hs0 in FP_p0. rewrite Dom_Nx0. by unfold FP in FP_p0. }
          clear -H Dom_Nx0. set_solver. }

        iAssert (resources _ _ γ_ks s0')%I 
          with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
        { iFrame "GKS". rewrite FP_s0'. iSplitR "Nodes_KS".
          rewrite (big_opS_delete _ (FP s0) p); try done.
          iSplitL "Node_p". rewrite Def_next' HNp HT HM HK. done.
          iApply (big_sepS_mono with "Nodes_rest"); try done.
          intros x Hx. iIntros "Hn". rewrite HK HT HM HN. done.
          clear -Hx; set_solver.
          iApply (big_sepS_mono with "Nodes_KS"); try done.
          intros x Hx. iIntros "Hn". rewrite HI.
          assert (Content s0' x = Content s0 x) as ->.
          rewrite /Content HK /Marki HM. done. done. }
        
        iAssert (⌜n ∈ FP s0⌝)%I as %FP_n0.
        { apply leibniz_equiv in Habs0. rewrite -Habs0. 
          iDestruct "FP_n" as (s)"(Past_s & %H' & _)".
          iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
        iAssert (⌜idx < Height s0 n⌝)%I as %Hidxn. 
        { apply leibniz_equiv in Habs0. rewrite -Habs0. 
          iDestruct "FP_n" as (s)"(Past_s & %H' & %H'')".
          iPoseProof (height_eq_2 with "[%] [$Hist] [$Past_s] [%]") as "->"; 
            try done. rewrite H''. iPureIntro. 
          apply elem_of_list_lookup_2 in Hidx. rewrite Perm_xs in Hidx.
          rewrite elem_of_seq in Hidx. lia. }
        
        assert (per_tick_inv hd tl s0') as PT_s0'.
        { destruct PT_s0 as (PT1'&PT2'&PT3'&PT4'&PT5'&PT6'&PT7').
          split; last split; last split; last split; last split; last split.
          - rewrite FP_s0' !HK !HM !HT. repeat split; try apply PT1'. 
            destruct (decide (p = hd)) as [-> | Hphd]. 
            rewrite HNp. rewrite lookup_insert_ne. apply PT1'. clear -HidxL; lia.
            all: rewrite HN; try done; apply PT1'.
          - rewrite /s0' /GFI /FP /FI. by rewrite Hs0 /GFI /FP /FI in PT2'.
          - intros n' k'. rewrite FP_s0' HI Habs' /Content /Marki HM HK.
            apply PT3'.
          - intros n' Hn. rewrite FP_s0' in Hn. apply PT4' in Hn.
            destruct (decide (n' = p)) as [-> | Hnp].
            + rewrite HNp HK HI HT HM.
              destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
              split; last split; last split; last split; last split; try done.
              * intros H'. assert (H1' := H'). apply Hn2 in H1'. 
                rewrite dom_insert_L H1'.
                assert (idx ∈ gset_seq 0 (Height s0 p - 1)) as H''.
                rewrite elem_of_gset_seq. split; try lia.
                clear -H''; set_solver.
              * rewrite lookup_insert_ne; try done. lia.
            + rewrite HK HT HI HM. rewrite HN; try done.
          - intros n1 n2. destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite /Nexti HNp !HK. 
              rewrite lookup_insert_ne; try done. apply PT5'. lia.
            + rewrite !HK /Nexti HN; try done. apply PT5'. 
          - intros n1 n2 i'. rewrite FP_s0'. 
            destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite /Nexti HNp. destruct (decide (i' = idx)) as [-> | Hi'i].
              rewrite lookup_insert. intros [=<-]. done. 
              rewrite lookup_insert_ne; try done. apply PT6'.
            + rewrite /Nexti HN; try done. apply PT6'.
          - intros n1 n2 i'. rewrite /Nexti. 
            destruct (decide (n1 = p)) as [-> | Hn1p]; last first.
            { rewrite HT HN; try done. apply PT7'. }
            rewrite HNp. destruct (decide (i' = idx)) as [-> | Hii'].
            + rewrite lookup_insert HT. intros [=<-]. done.
            + rewrite HT lookup_insert_ne; try done. apply PT7'. }
        assert (transition_inv s0 s0') as Trans_s0.
        { repeat split; try rewrite FP_s0'; try done; last first.
          - intros n' i' Hfp. rewrite /Marki HM. done.
          - intros n'. rewrite /Marki HM. intros H' H''. 
            rewrite H' in H''; try done.
          - intros n' i' Hn'. destruct (decide (n' = p)) as [-> | Hnp].
            + rewrite /Marki HM /Nexti HNp. 
              destruct (decide (i' = idx)) as [-> | Hi].
              rewrite Mark_p0. clear; try done.
              rewrite lookup_insert_ne; try done.
            + rewrite /Marki /Nexti HM HN; try done. }

        iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
        { by iDestruct "Hist" as (M0'') "(_&_&%&_)". }
              
        iAssert (|==> hist _ _ _ _ γ_t γ_m M0' (T0+1))%I with "[Hist]" as ">Hist".
        { iPoseProof (hist_upd _ _ _ _ _ _ _ _ _ s0' with "[%] [%] [$Hist]") as ">H'".
          apply  Habs0. intros <-. rewrite map_eq_iff in HNp.
          pose proof HNp idx as HNp. rewrite Next_p0 lookup_insert in HNp.
          inversion HNp; try done. by rewrite /M0'. }
        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> 
          helping_inv _ _ _ _ N γ_t γ_r γ_mt γ_msy M0' ∗ dsRep _ _ _ _ γ_r (abs s0'))%I with
          "[Help Ds]" as ">(Help & Ds)".
        { iMod (fupd_mask_subseteq (⊤ ∖ ↑cntrN N)) as "H'". { clear; set_solver. }
          iPoseProof ("Upd" with "[%] [Ds] [Help]") as ">Help"; try done.
          apply leibniz_equiv in Habs0. iMod "H'" as "_". by iModIntro. }
        iModIntro. iSplitR "Hpost Hperm Hpreds Hsuccs".
        { iNext. iExists M0', (T0+1), s0'. iFrame "∗#%".
          iSplitR. iPureIntro. by rewrite lookup_total_insert.
          iExists hd, tl. iFrame.
          iPureIntro; rewrite /M0'; split.
          - intros t Ht. destruct (decide (t = T0+1)) as [-> | Ht'].
            + by rewrite lookup_total_insert.
            + rewrite lookup_total_insert_ne; try done. apply PT0.
              clear -Ht' Ht; lia.
          - intros t Ht. destruct (decide (t = T0)) as [-> | Ht'].
            + rewrite lookup_total_insert. rewrite lookup_total_insert_ne.
              apply leibniz_equiv in Habs0. by rewrite Habs0. clear; lia.
            + rewrite !lookup_total_insert_ne. apply Trans_M0.
              all: clear -Ht Ht'; lia. }
        wp_pures. iSpecialize ("IH" $! (i+1) ps ss).
        assert (Z.add i 1 = (i+1)%nat) as ->. clear; lia.
        iApply ("IH" with "[-Hpost]"); try done. 
        { iFrame "Hpreds Hsuccs".
          iSplitR. iPureIntro. apply Len_ps.
          iSplitR. iPureIntro. apply Len_ss.
          iSplitR. iPureIntro. lia. iSplitR. by iPureIntro. 
          iSplitR. by iPureIntro. iFrame "#". iFrame "Hperm".
          by iPureIntro. }
  Admitted.


  Lemma maintenanceOp_insert_spec Σ Hg1 Hg2 Hg3 ps ss N γ_t γ_r γ_m γ_mt γ_msy r 
    tid t0 k (n:Node) preds succs (hd tl: Node):
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
    r ↦□ (#hd, #tl) -∗
        {{{   preds ↦∗ ((λ n0 : loc, #n0) <$> ps)
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss)
            ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜n ∈ FP s⌝)
            ∗ ⌜n ≠ hd⌝ ∗ ⌜n ≠ tl⌝
            ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
            ∗ ⌜ps !!! (L - 1) = hd⌝ ∗ ⌜ss !!! (L - 1) = tl⌝
            ∗ (∀ i, ⌜i < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k (ps !!! i) (ss !!! i)) }}}
           maintenanceOp_insert #k #preds #succs #n
        {{{ (ps' ss': list Node),
            RET #();
              preds ↦∗ ((λ n0 : loc, #n0) <$> ps')
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss') }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k] #HR'". 
    iIntros (Φ) "!# (Hpreds & Hsuccs & #FP_n & %n_neq_hd & %n_neq_tl & 
      %Len_ps & %Len_ss & %HpsL & %HssL & #Htr) Hpost".
    wp_lam. wp_pures. awp_apply getHeight_spec; try done.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
    { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜n ∈ FP s0⌝)%I as %FP_n0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "FP_n" as (s)"(Past_s & %)".
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
    rewrite (big_sepS_delete _ (FP s0) n); last by eauto.
    iDestruct "Nodes" as "(Node_n & Nodes_rest)".
    iAaccIntro with "Node_n".
    { iIntros "Node_n". iModIntro. iFrame.
      iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl. iFrame "∗%#".
      rewrite (big_sepS_delete _ (FP s0) n); try done. iFrame. }
    iIntros "Node_n". 
    set h := Height s0 n. 
    iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    assert (h < L). 
    { apply PT_s0 in FP_n0. destruct FP_n0 as (_&_&_&H'&_). by apply H'. }
    iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
      as ">(#Past_s0&Hist)"; try done.
    iSplitR "Hpreds Hsuccs Hpost".
    { iModIntro. iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl. iFrame "∗%#".  
      rewrite (big_sepS_delete _ (FP s0) n); try done. iFrame. } 
    iModIntro. wp_pures. 
    wp_apply permute_levels_spec; try done.
    iIntros (perm vs xs)"(Hperm & %Def_vs & %Perm_xs)". wp_pures. 
    wp_apply (maintenanceOp_insert_rec_spec with "[] [] [] [] [HR']
      [$Hperm $Hpreds $Hsuccs]"); try done.
    { iFrame "#%". iExists s0. iFrame "#". by iPureIntro. }
    iIntros (ps' ss')"(Hpreds & Hsuccs & Hperm)". 
    iApply "Hpost". iFrame.
  Qed.


  