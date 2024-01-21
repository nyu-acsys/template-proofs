(* Skiplist Template : Maintenance Operation for delete *)

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
Require Import skiplist_util.
Require Export traverse_spec_module flows.

Module Type SKIPLIST_DELETE_MAINTENANCE.
  Declare Module TR_SPEC : TRAVERSE_SPEC.
  Export TR_SPEC TR_SPEC.SK_UTIL. Export DEFS DEFS.DS.
  Export TR TR.NODE.

  Lemma maintenanceOp_delete_rec_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r tid t0 c
    perm vs xs i h (hd tl : Node):
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
    r ↦□ (#hd, #tl) -∗ 
        {{{   perm ↦∗ vs
            ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
            ∗ ⌜xs ≡ₚ seq 1 (h-1)⌝
            ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜c ∈ FP s⌝ ∗ ⌜h = Height s c⌝
                    ∗ ⌜∀ j, j < i → Marki s c (xs !!! j) = true⌝)
            ∗ ⌜c ≠ hd⌝ ∗ ⌜c ≠ tl⌝ }}}
           maintenanceOp_delete_rec #i #h #perm #c @ ⊤
        {{{ RET #();
              (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜c ∈ FP s⌝ ∗ ⌜h = Height s c⌝
                    ∗ ⌜∀ j, j < h-1 → Marki s c (xs !!! j) = true⌝)
            ∗ perm ↦∗ vs }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd #HR'". iLöb as "IH" forall (i).
    iIntros (Φ) "!# (Hperm&%Def_vs&%Perm_xs&#Hmark&%c_neq_hd&%c_neq_tl) Hpost". 
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
      awp_apply markNode_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      iDestruct "Templ" as (hd' tl' γ_ks)"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
      iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
      { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
      { apply leibniz_equiv in Habs0. rewrite -Habs0.
        iDestruct "Hmark" as (s)"(Past_s & % & _)".
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iDestruct "Nodes" as "(Node_c & Nodes_rest)".
      iAssert (⌜Height s0 c = h⌝)%I as %Ht_c0. 
      { apply leibniz_equiv in Habs0. rewrite -Habs0.
        iDestruct "Hmark" as (s)"(Past_s & % & -> & _)".
        iPoseProof (height_eq_2 _ _ _ _ c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
        try done. }
      assert (idx < h) as idx_lt_h. 
      { assert (idx ∈ seq 1 (h-1)) as H'. 
        { rewrite -Perm_xs elem_of_list_lookup. exists i; try done. }
        rewrite elem_of_seq in H'. clear -H'; lia. }
      iAssert ((node Σ _ c (Height s0 c) (Mark s0 c) (Next s0 c) (Key s0 c)) 
        ∗ ⌜idx < Height s0 c⌝)%I with "[Node_c]" as "Hpre".
      { rewrite Ht_c0. iFrame "Node_c". by iPureIntro. }
      iAaccIntro with "Hpre".
      { iIntros "(Node_c & _)". iModIntro. iFrame "Hpost Hc Hperm".
        iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl, γ_ks. iFrame "∗%#".
        rewrite (big_sepS_delete _ (FP s0) c); try done. iFrame. }
      iAssert (∀ j, ⌜j < i⌝ → ⌜Marki s0 c (xs !!! j) = true⌝)%I as %Hj0.
      { iIntros (j)"%Hj". 
        iDestruct "Hmark" as (s) "(Past_s & %FP_c' & %Ht_c & %Hj')".
        apply Hj' in Hj. apply leibniz_equiv in Habs0. rewrite -Habs0.
        iPoseProof (marking_mono_2 _ _ _ _ c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
            try done. }
      iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
      { by iDestruct "Hist" as (M0'') "(_&_&%&_)". }
      iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
        as ">(#Past_s0&Hist)"; try done.
      
      iIntros (success mark')"(Node_c & Hif)". 
      iApply (lc_fupd_add_later with "Hc"). iNext.
      destruct success.
      + iDestruct "Hif" as %[Mark_c0 Def_mark'].
        iDestruct "SShot0" as %[FP0 [C0 [Ht0 [Mk0 [Nx0 [Ky0 [I0 
          [Hs0 [Dom_Ht0 [Dom_Mk0 [Dom_Nx0 [Dom_Ky0 Dom_I0]]]]]]]]]]]].
        set Mk0' := <[c := mark']> Mk0.
        set s0' := (FP0, C0, Ht0, Mk0', Nx0, Ky0, I0): snapshot.
        set M0' := <[T0 + 1 := s0']> M0.
        iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
        { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
        assert (FP s0' = FP s0) as FP_s0'.
        { by rewrite /FP /s0' Hs0. }
        assert (abs s0' = abs s0) as Habs'.
        { by rewrite /abs /s0' Hs0. }
        iAssert (dsRepI _ _ _ _ γ_r (abs s0'))%I with "[Ds]" as "Ds".
        { by rewrite Habs'. }
        iAssert (own γ_ks (● prodKS (KS, abs s0')))%I with "[GKS]" as "GKS".
        { by rewrite Habs'. }
        assert (idx ≠ 0) as Hidx0.
        { intros ->. assert (0 ∈ seq 1 (h-1)) as H'.
          rewrite -Perm_xs. rewrite elem_of_list_lookup.
          by exists i. rewrite elem_of_seq in H'.
          clear -H'; lia. }
        assert (∀ n, Next s0' n = Next s0 n) as HN.
        { by rewrite /Next /s0' Hs0 /=. }
        assert (∀ n, Height s0' n = Height s0 n) as HT.
        { by rewrite /s0' Hs0 /=. }
        assert (∀ n, Key s0' n = Key s0 n) as HK.
        { by rewrite /Key /s0' Hs0 /=. }
        assert (∀ n, FI s0' n = FI s0 n) as HI.
        { by rewrite /FI /s0' Hs0 /=. }
        assert (∀ n, n ≠ c → Mark s0' n = Mark s0 n) as HM.
        { intros n Hnc. by rewrite /FI /s0' Hs0 /Mk0' /= lookup_insert_ne. }
        assert (Mark s0' c = <[idx := true]> (Mark s0 c)) as HMc.
        { rewrite /FI /s0' Hs0 /Mk0' /= lookup_insert Def_mark'.
          by rewrite Hs0 /Mark. }
        iAssert (⌜snapshot_constraints s0'⌝)%I as "SShot0'".
        { iPureIntro. exists FP0, C0, Ht0, Mk0', Nx0, Ky0, I0.
          repeat split; try done.
          rewrite /Mk0'. rewrite dom_insert_L.
          assert (c ∈ dom Mk0). 
          { rewrite Hs0 in FP_c0. rewrite Dom_Mk0. by unfold FP in FP_c0. }
          clear -H Dom_Mk0. set_solver. }
        assert (per_tick_inv hd tl s0') as PT_s0'.
        { destruct PT_s0 as (PT1&PT2&PT3&PT4&PT5&PT6&PT7).
          split; last split; last split; last split; last split; last split.
          - rewrite FP_s0' !HK !HN !HT !HM; try done.
          - rewrite /s0' /GFI /FP /FI. by rewrite Hs0 /GFI /FP /FI in PT2.
          - intros n k. rewrite FP_s0' HI Habs' /Content /Marki HK.
            destruct (decide (n = c)) as [-> | Hnc].
            + rewrite HMc lookup_total_insert_ne; try done.
              apply PT3.
            + rewrite HM; try done. apply PT3.
          - intros n Hn. rewrite FP_s0' in Hn. apply PT4 in Hn.
            destruct (decide (n = c)) as [-> | Hnc].
            + rewrite HT HN HK HI HMc.
              destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
              split; last split; last split; last split; last split; try done.
              * intros [i' Hi']. destruct (decide (i' = idx)) as [-> | Hi].
                by rewrite lookup_total_insert in Hi'.
                rewrite lookup_total_insert_ne in Hi'; try done.
                rewrite lookup_total_insert_ne; try done. apply Hn1.
                exists i'; try done.
              * rewrite dom_insert_L Hn3. 
                assert (idx ∈ gset_seq 0 (Height s0 c - 1)) as H'.
                rewrite elem_of_gset_seq. split; try lia.
                clear -H'; set_solver.
              * rewrite lookup_total_insert_ne; try done.
            + rewrite HT HN HK HI HM; try done.
          - intros n1 n2. rewrite /Nexti. rewrite HN !HK. apply PT5.
          - intros n1 n2 i'. rewrite /Nexti. rewrite HN FP_s0'. apply PT6.
          - intros n1 n2 i'. rewrite /Nexti HT HN. apply PT7. }
        assert (transition_inv s0 s0') as Trans_s0.
        { repeat split; try rewrite FP_s0'; try done; last first.
          intros n i' Hn; rewrite /Marki; intros Hm.
          destruct (decide (n = c)) as [-> | Hnc].
          - rewrite HMc. destruct (decide (i' = idx)) as [-> | Hi'].
            + by rewrite lookup_total_insert.
            + by rewrite lookup_total_insert_ne.
          - by rewrite HM.
          - intros n. destruct (decide (n = c)) as [-> | Hnc].
            rewrite /Marki HMc lookup_total_insert_ne; try done.
            intros Hn1 Hn2. rewrite Hn1 in Hn2. clear -Hn2; done.
            rewrite /Marki HM; try done.
            intros Hn1 Hn2. rewrite Hn1 in Hn2. clear -Hn2; done.
          - intros n i'. rewrite /Nexti HN. clear; try done. }
        iAssert (resources _ _ _ γ_ks s0')%I 
          with "[GKS Nodes_KS Node_c Nodes_rest]" as "Res".
        { iFrame "GKS". rewrite FP_s0'. iSplitR "Nodes_KS".
          rewrite (big_opS_delete _ (FP s0) c).
          iSplitL "Node_c". rewrite Def_mark' HT HMc HN HK. done.
          iApply (big_sepS_mono with "Nodes_rest"); try done.
          intros x Hx. iIntros "Hn". rewrite HN HT HK HM. done.
          clear -Hx; set_solver. done. 
          iApply (big_sepS_mono with "Nodes_KS"); try done.
          intros x Hx. iIntros "Hn". rewrite HI.
          assert (Content s0' x = Content s0 x) as ->.
          rewrite /Content HK. destruct (decide (x = c)) as [-> | Hxc].
          rewrite /Marki HMc lookup_total_insert_ne; try done.
          rewrite /Marki HM; try done. done. }
        iAssert (|==> hist _ _ _ _ γ_t γ_m M0' (T0+1))%I with "[Hist]" as ">Hist".
        { iPoseProof (hist_upd _ _ _ _ _ _ _ _ _ s0' with "[%] [%] [$Hist]") as ">H'".
          apply Habs0. intros <-. rewrite map_eq_iff in HMc.
          pose proof HMc idx as HMc. rewrite lookup_insert in HMc.
          apply lookup_total_correct in HMc. by rewrite Mark_c0 in HMc.
          by rewrite /M0'. }
        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> 
          helping_inv _ _ _ _ N γ_t γ_r γ_mt γ_msy M0' ∗ dsRep _ _ _ _ γ_r (abs s0'))%I with
          "[Help Ds]" as ">(Help & Ds)".
        { iMod (fupd_mask_subseteq (⊤ ∖ ↑cntrN N)) as "H'". { clear; set_solver. }
          iPoseProof ("Upd" with "[%] [Ds] [Help]") as ">Help"; try done.
          apply leibniz_equiv in Habs0. iMod "H'" as "_". by iModIntro. }
        iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
          as ">(#Past_s0'&Hist)"; try done.
        iEval (rewrite /M0' lookup_total_insert) in "Past_s0'".
        iAssert (∃ s : snapshot, past_state _ _ _ _ γ_m t0 s ∗ ⌜c ∈ FP s⌝ ∗ ⌜h = Height s c⌝
          ∗ ⌜∀ j : nat, j < i + 1 → Marki s c (xs !!! j) = true⌝)%I as "#Hmark'".
        { iDestruct "Hmark" as (s) "(Hpast_s & %FP_c' & %Ht_c & %Hj)".
          iAssert (⌜Marki s0' c (xs !!! i) = true⌝)%I as %Hi.
          { iPureIntro. rewrite list_lookup_total_alt Hidx /=.
            rewrite /s0' /Marki /Mark /Mk0' lookup_insert Def_mark'.
            by rewrite lookup_total_insert. }
          iExists s0'. iFrame "Past_s0'". iPureIntro.
          split. rewrite /s0' /FP. by rewrite Hs0 /FP in FP_c0.
          split. rewrite /s0' /Height. rewrite Hs0 /Height in Ht_c0. done.
          intros j Hj'. destruct (decide (j = i)) as [-> | Hji]; try done.
          rewrite /s0' /Marki /Mark /Mk0' lookup_insert Def_mark'.
          rewrite lookup_total_insert_ne. rewrite /Marki in Hj0.
          apply Hj0. lia. 
          clear -Hji Hj' Hidx Hbool Perm_xs. intros H'. apply Hji.
          assert (is_Some (xs !! j)) as [idx' Hidx'].
          apply lookup_lt_is_Some. rewrite Perm_xs seq_length. lia.
          assert (idx' = idx) as ->. by rewrite H' list_lookup_total_alt Hidx' /=. 
          assert (NoDup xs) as H''. rewrite Perm_xs. apply NoDup_seq.
          by pose proof NoDup_lookup xs i j idx H'' Hidx Hidx'. }

        iModIntro. iSplitR "Hperm Hpost".
        { iNext. iExists M0', (T0+1), s0'. iFrame "∗#%".
          iSplitR. iPureIntro. by rewrite lookup_total_insert.
          iExists hd, tl, γ_ks. iFrame.
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
        wp_pures.
        iSpecialize ("IH" $! (i+1)).
        assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
        iEval (rewrite H') in "IH". iApply ("IH" with "[Hperm]"); try done.
        iFrame "Hperm Hmark' %".
      + iDestruct "Hif" as %[Mark_c0 ->].
        iAssert (∃ s : snapshot, past_state _ _ _ _ γ_m t0 s ∗ ⌜c ∈ FP s⌝ ∗ ⌜h = Height s c⌝
          ∗ ⌜∀ j : nat, j < i + 1 → Marki s c (xs !!! j) = true⌝)%I as "#Hmark'".
        { iAssert (⌜Marki s0 c (xs !!! i) = true⌝)%I as %Hi.
          { iPureIntro. rewrite list_lookup_total_alt Hidx /=. done. }
          iExists s0. iFrame "Past_s0". 
          iPureIntro; split; try done. split. done.
          intros j Hj. destruct (decide (j = i)) as [-> | Hji]; try done.
          apply Hj0. lia. }
        iModIntro. iSplitR "Hperm Hpost".
        { iNext. iExists M0, T0, s0. iFrame "∗#%". iExists hd, tl, γ_ks. iFrame "∗#%".
          rewrite (big_opS_delete _ (FP s0) c); try done.
          iFrame "Nodes_rest". iFrame. }
        wp_pures.
        iSpecialize ("IH" $! (i+1)).
        assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
        iEval (rewrite H') in "IH". iApply ("IH" with "[Hperm]"); try done.
        iFrame "Hperm Hmark' %".
    - rewrite bool_decide_eq_false in Hbool.
      iApply "Hpost". iFrame "Hperm". 
      iDestruct "Hmark" as (s) "(Hpast_s & %FP_c' & %HT_c & %Hj)".
      iModIntro. iExists s. iFrame "#%". iPureIntro.
      intros j Hj'. apply Hj. lia.
  Qed.


  Lemma maintenanceOp_delete_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r tid 
    t0 c (hd tl: Node):
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    r ↦□ (#hd, #tl) -∗
      {{{ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜c ∈ FP s⌝) ∗ ⌜c ≠ hd⌝ ∗ ⌜c ≠ tl⌝ }}}
           maintenanceOp_delete #c @ ⊤
        {{{ RET #();
              (∃ s h, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜c ∈ FP s⌝ ∗ ⌜h = Height s c⌝
                    ∗ ⌜∀ i, 1 ≤ i < h → Marki s c i = true⌝) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd #HR'". iIntros (Φ) "!# (#FP_c&%c_neq_hd&%c_neq_tl) Hpost".
    wp_lam. wp_pures. awp_apply getHeight_spec; try done. 
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl' γ_ks)"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
    { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "FP_c" as (s)"(Past_s & %)".
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Nodes" as "(Node_c & Nodes_rest)".
    iAaccIntro with "Node_c".
    { iIntros "Node_c". iModIntro. iFrame "Hpost".
      iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl, γ_ks. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); try done. iFrame. }
    iIntros "Node_c". 
    iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
      as ">(#Past_s0&Hist)"; try done.
    iSplitR " Hpost".
    { iModIntro. iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl, γ_ks. 
      iFrame "∗%#". rewrite (big_sepS_delete _ (FP s0) c); try done. iFrame. }  
    iModIntro. wp_pures. set h := Height s0 c. 
    wp_apply permute_levels_spec; try done.
    iIntros (perm vs xs)"(Hperm & %Def_vs & %Perm_xs)". wp_pures. 
    wp_apply (maintenanceOp_delete_rec_spec with "[] [] [] [] [Hperm]"); try done.
    { iFrame "Hperm %". iExists s0. iFrame "Past_s0".
      iPureIntro. repeat split; try done. lia. }
    iIntros "(Hs & Hperm)". iDestruct "Hs" as (s)"(Hs & %H' & %H'' & %H1')".
    iApply "Hpost". iExists s, h; iFrame. iPureIntro; repeat split; try done.
    intros i Hi. assert (∃ j, j < h - 1 ∧ (xs !!! j = i)) as [j [H1'' <-]].
    { assert (i ∈ xs) as Hixs. rewrite Perm_xs elem_of_seq. lia.
      rewrite elem_of_list_lookup in Hixs. destruct Hixs as [j Hjxs].
      exists j; split. apply lookup_lt_Some in Hjxs. 
      by rewrite Perm_xs seq_length in Hjxs. 
      by rewrite list_lookup_total_alt Hjxs. }
    apply H1'; try done.
  Qed.

End SKIPLIST_DELETE_MAINTENANCE.