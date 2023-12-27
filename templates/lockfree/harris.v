From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Import list_flow_upd_unlink.
From flows Require Import array_util node_module.
From flows Require Import traverse_module traverse_spec_module skiplist_util.

Module HARRIS <: TRAVERSE.
  Declare Module NODE : NODE_IMPL.
  
  Definition traverse_i : heap_lang.val :=
    rec: "tri" "i" "pred" "predn" "curr" "k" :=
      let: "fn_curr" := findNext "curr" "i" in
      let: "m" := Fst "fn_curr" in
      let: "succ" := Snd "fn_curr" in
      if: "m" then
        "tri" "i" "pred" "predn" "succ" "k"
      else
        let: "res" := compareKey "curr" "k" in
        if: "res" = #0 then 
          "tri" "i" "curr" "succ" "succ" "k"
        else
          if: "predn" = "curr" then
            if: "res" = #1 then
              SOME ("pred", "curr", #true)
            else
              SOME ("pred", "curr", #false)
          else
            match: changeNext "pred" "predn" "curr" "i" with
              NONE => NONE
            | SOME "_" => 
              let: "fn_curr" := findNext "curr" "i" in
              let: "m'" := Fst "fn_curr" in
              if: "m'" then
                NONE
              else
                if: "res" = #1 then
                  SOME ("pred", "curr", #true)
                else
                  SOME ("pred", "curr", #false) end.

  Definition traverse_pop : heap_lang.val :=
    λ: "k" "preds" "succs" "i",
      let: "pred" := ! ("preds" +ₗ ("i" + #1)) in
      let: "fn_pred" := findNext "pred" "i" in
      let: "curr" := Snd "fn_pred" in
      let: "ores" := traverse_i "i" "pred" "curr" "curr" "k" in
      match: "ores" with
        NONE => NONE
      | SOME "pred_succ_res" =>
        let: "pred" := Fst (Fst "pred_succ_res") in
        let: "succ" := Snd (Fst "pred_succ_res") in
        let: "res" := Snd "pred_succ_res" in
        "preds" +ₗ "i" <- "pred";;
        "succs" +ₗ "i" <- "succ";;
        SOME ("preds", "succs", "res") end.

  Definition traverse_rec : heap_lang.val :=
    rec: "trec" "k" "preds" "succs" "i" :=
      let: "ores" := traverse_pop "k" "preds" "succs" "i" in
      match: "ores" with 
        NONE => "trec" "k" "preds" "succs" #(L-2)%nat
      | SOME "res" => 
        if: "i" = #0 then
          "res"
        else
          "trec" "k" "preds" "succs" ("i" - #1) end.
  
  Definition traverse : heap_lang.val :=
    λ: "h" "t" "k",
      let: "preds" := AllocN #L "h" in
      let: "succs" := AllocN #L "t" in
      traverse_rec "k" "preds" "succs" #(L-2)%nat.  

End HARRIS.

Module HARRIS_SPEC <: TRAVERSE_SPEC.
  Module TR := HARRIS.
  Import HARRIS.

  Definition traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k p c : iProp Σ :=
    (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜p ∈ FP s ∧ Key s p < k ∧ 
      Marki s p 0 = false ∧ i < Height s p ∧ (i = 0 → Nexti s p i = Some c)⌝)
  ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜c ∈ FP s ∧ i < Height s c⌝).

  Lemma traversal_inv_hd_tl Σ Hg1 Hg2 Hg3 γ_m γ_t γ_mt hd tl M T s tid t0 k:
    ⌜M !!! T ≡ s⌝ -∗ 
    ⌜per_tick_inv hd tl s⌝ -∗
    ⌜1 < L⌝ -∗
    ⌜0 < k < W⌝ -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
      |==> traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 (L-1) k hd tl ∗ hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T.
  Proof.
    iIntros "%Habs %PT %HL %Range_k #Thd_st Hist".
    iPoseProof (snapshot_current with "[%] [#] [$]") 
      as ">(#Past_s&Hist)"; try done.
    destruct PT as ((H1'&H2'&H3'&H4'&H5'&H6'&H7'&H8'&H9')&_).
    iModIntro. iFrame. iSplit; iExists s; iFrame "Past_s".
    - iPureIntro; repeat split; try (done || lia).
      set_solver. apply H4'. lia.
    - iPureIntro; repeat split; try (done || lia). set_solver.
  Qed. 

  Definition past_marked_segment Σ Hg1 Hg2 Hg3 γ_m t0 i pn ls c : iProp Σ :=
    match ls with 
    | [] => (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ 
      ⌜pn ∈ FP s ∧ Marki s pn i = true ∧ Nexti s pn i = Some c⌝)
    | n :: _ => 
    (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ 
      ⌜pn ∈ FP s ∧ Marki s pn i = true ∧ Nexti s pn i = Some n⌝)
    ∗ (∀ j, ⌜j < length ls - 1⌝ -∗ 
        (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
          ∗ ⌜(ls !!! j) ∈ FP s ∧ Marki s (ls !!! j) i = true 
              ∧ Nexti s (ls !!! j) i = Some (ls !!! ((j+1)%nat))⌝))
    ∗ (let last := ls !!! (length ls - 1) in
        ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
        ∗ ⌜last ∈ FP s ∧ Marki s last i = true 
            ∧ Nexti s last i = Some c⌝) end.

  
  Lemma traverse_i_spec Σ Hg1 Hg2 Hg3 ls N γ_t γ_r γ_m γ_mt γ_msy r tid t0 k 
    (i: nat) (p pn c: Node):
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
    ⌜i < L - 1⌝ -∗
      {{{ traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k p pn
          ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜c ∈ FP s ∧ i < Height s c⌝)
          ∗ (⌜pn ≠ c⌝ -∗ past_marked_segment Σ Hg1 Hg2 Hg3 γ_m t0 i pn ls c) }}}
        traverse_i #i #p #pn #c #k @ ⊤
      {{{ (ores: option (Node * Node * bool)), 
            RET (match ores with
                  None => NONEV
                | Some res =>SOMEV (#res.1.1,#res.1.2,#res.2) end);
            match ores with 
              None => True
            | Some res =>
              let p' := res.1.1 in let c' := res.1.2 in let b := res.2 in
              traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k p' c'
              ∗ (⌜i = 0⌝ → (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ 
                              ⌜if b then 
                                  k ∈ abs s ∧ k = Key s c' 
                                  ∧ c' ∈ FP s ∧ Marki s c' 0 = false
                                else 
                                  k ∉ abs s ∧ k < Key s c' 
                                  ∧ c' ∈ FP s⌝)) end }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k] %HiL". 
    iLöb as "IH" forall (p pn c ls). iIntros (Φ) "!# (#Htr & #FP_c & Hls) Hpost". 
    wp_lam. wp_pure credit: "Hc". wp_pures. 
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd tl)"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Nodes" as "(Node_c & Nodes_rest)".
    iAssert (⌜i < Height s0 c⌝)%I as %Height_c0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
      iPoseProof (height_eq_2 Σ Hg1 Hg2 Hg3 c with "[%] [$] [$Past_s] [%]") as "->"; 
        try done. }
    iAssert ((node Σ c (Height s0 c) (Mark s0 c) (Next s0 c) (Key s0 c)) 
      ∗ ⌜i < Height s0 c⌝)%I with "[Node_c]" as "Hpre".
    { iFrame "Node_c %". }
    iAaccIntro with "Hpre".
    { iIntros "(Node_c & _)". iModIntro. iFrame "Hpost Hc Hls".
      iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Nodes_rest". iFrame. }
    iIntros (m cn) "(Node_c & %Mark_c0 & %Next_c0)".
    iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iPoseProof (snapshot_current with "[%] [#] [$]") 
      as ">(#Past_s0&Hist)"; try done.
    assert (c ≠ tl → Next s0 c !! i = Some cn) as Next_c0'. 
    { intros Hctl. rewrite lookup_lookup_total. by rewrite Next_c0. 
      rewrite -elem_of_dom. apply PT_s0 in FP_c0. destruct FP_c0 as (_&H'&H''). 
      rewrite H'; try done. rewrite elem_of_gset_seq. lia. }
    iAssert (⌜Mark s0 c !!! i = false⌝ → ⌜Key s0 c < k⌝ → 
      traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k c cn)%I as "#Hcase".
    { iIntros "%Hm %Hk". assert (Next s0 c !! i = Some cn) as H'. apply Next_c0'.
      intros ->. destruct PT_s0 as ((_&_&H'&_)&_). clear -H' Hk Range_k. lia.
      iSplitL; iExists s0; iFrame "Past_s0"; iPureIntro.
      repeat split; try done. apply PT_s0 in FP_c0. destruct FP_c0 as (H''&_).
      apply H''. by exists i. destruct PT_s0 as (_&_&_&_&_&PT&PT').
      repeat split; try done. by apply (PT c _ i). by apply (PT' c _ i). }
    
    iAssert (⌜pn = c⌝ -∗ 
              ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s
            ∗ ⌜p ∈ FP s⌝
            ∗ ⌜Key s p < k⌝
            ∗ ⌜Marki s p 0 = false⌝
            ∗ ⌜i < Height s p⌝
            ∗ ⌜i = 0 → Nexti s p i = Some c⌝
            ∗ ⌜per_tick_inv hd tl s⌝
            ∗ ⌜c ∈ FP s → Mark s0 c !!! i = false → Mark s c !!! i = false⌝
            ∗ ⌜c ∈ FP s → Key s c = Key s0 c⌝
            ∗ ⌜∀ k, c ∈ FP s → k ∈ keyset (FI s c) → k ∈ abs s ↔ k ∈ Content s c⌝)%I
      with "[Hist]" as "#Htr'".
    { iIntros "%". subst pn. iDestruct "Htr" as "(Htrp & Htrc)".
      iDestruct "Htrp" as (s)"(Past_s & %FP_ps & %Key_ps & %Marki_ps & 
        %Height_ps & %Nexti_ps)".
      iAssert (⌜per_tick_inv hd tl s⌝)%I as %PT_s.
      { iPoseProof (per_tick_past with "[%] Hist Past_s") as "%"; try done. }
      iAssert (⌜c ∈ FP s⌝ → ⌜Mark s0 c !!! i = false⌝ 
        → ⌜Mark s c !!! i = false⌝)%I as %HM.
      { iIntros "%FP_cs %Hm". destruct (decide (Mark s c !!! i = false)); try done.
        iExFalso. rewrite not_false_iff_true in n.
        iAssert (⌜Marki s0 c i = Marki s c i⌝)%I as %H'.
        { apply leibniz_equiv in Habs0. rewrite -Habs0.
          iPoseProof (marking_mono_2 Σ Hg1 Hg2 Hg3 c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
            try done. }
        rewrite /Marki Hm n in H'. done. } 
      iAssert (⌜c ∈ FP s⌝ → ⌜Key s c = Key s0 c⌝)%I as %Key_eq. 
      { iIntros "%FP_cs". 
        apply leibniz_equiv in Habs0. rewrite -Habs0.
        iPoseProof (key_eq_2 Σ Hg1 Hg2 Hg3 c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. }
      assert (∀ k, c ∈ FP s →  k ∈ keyset (FI s c) → 
        (k ∈ abs s ↔ k ∈ Content s c)) as Hks.
      { destruct PT_s as (_&_&H'&_). intros k'; apply H'. }
      iExists s. iFrame "#%". }
    iAssert (⌜pn = c⌝ -∗ ⌜i = 0⌝ → ⌜Mark s0 c !!! i = false⌝ → ⌜k < Key s0 c⌝ → 
      ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
          ∗ ⌜k ∉ abs s ∧ k < Key s c ∧ c ∈ FP s⌝)%I as "Hcase1".
    { iIntros "%Hpnc %Hi %Mark_c0' %Key_c0".
      iDestruct ("Htr'" with "[%]") as (s)"(#Past_s & %FP_ps & %Key_ps & %Marki_ps 
        & %Height_ps & %Nexti_ps & %PT_s & %HM & %Key_eq & %Hks)"; try done.  
      pose proof Nexti_ps Hi as Nexti_ps'.
      subst i. iExists s. iFrame "Past_s". clear Nexti_ps.
      assert (c ∈ FP s) as FP_cs. 
      { destruct PT_s as (_&_&_&_&_&H'&_). apply (H' p c 0); try done. }
      apply HM in Mark_c0'; try done. rename Mark_c0' into Mark_cs. 
      rewrite -Key_eq in Key_c0; try done.
      assert (k ∈ keyset (FI s c)) as k_in_ksc.
      { apply (in_keyset hd tl s p c k); try done. lia. }
      assert (k ∉ Content s c) as k_notin_cntc.
      { rewrite /Content /Marki Mark_cs elem_of_singleton. lia. }
      apply Hks in k_in_ksc; try done. iPureIntro. repeat split; try done.
      intros H'%k_in_ksc. by apply k_notin_cntc. }
    iAssert (⌜pn = c⌝ -∗ ⌜i = 0⌝ → ⌜Mark s0 c !!! i = false⌝ → ⌜k = Key s0 c⌝ → 
      ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
          ∗ ⌜k ∈ abs s ∧ k = Key s c ∧ c ∈ FP s ∧ Marki s c 0 = false⌝)%I as "Hcase2".
    { iIntros "%Hpnc %Hi %Mark_c0' %Key_c0".
      iDestruct ("Htr'" with "[%]") as (s)"(#Past_s & %FP_ps & %Key_ps & %Marki_ps 
        & %Height_ps & %Nexti_ps & %PT_s & %HM & %Key_eq & %Hks)"; try done.
      pose proof Nexti_ps Hi as Nexti_ps'.
      subst i. iExists s. iFrame "Past_s". clear Nexti_ps. 
      assert (c ∈ FP s) as FP_cs. 
      { destruct PT_s as (_&_&_&_&_&H'&_). apply (H' p c 0); try done. }
      apply HM in Mark_c0'; try done. rename Mark_c0' into Mark_cs. 
      rewrite -Key_eq in Key_c0; try done.
      assert (k ∈ keyset (FI s c)) as k_in_ksc.
      { apply (in_keyset hd tl s p c k); try done. lia. }
      assert (k ∈ Content s c) as k_in_cntc.
      { rewrite /Content /Marki Mark_cs elem_of_singleton. lia. }
      apply Hks in k_in_ksc; try done. iPureIntro. repeat split; try done.
      by apply k_in_ksc. }
    assert (m = true → c ≠ tl) as H1'.
    { intros ->. destruct PT_s0 as ((_&_&_&_&H'&_)&_).
      assert (i < L) as H'' by lia. pose proof H' i H'' as H1'.
      intros ->. rewrite H1' in Mark_c0; try done. }
    iAssert (⌜m = true⌝ → ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
      ∗ ⌜cn ∈ FP s ∧ i < Height s cn⌝)%I as "#FP_cn'".
    { iIntros "%". subst m. iExists s0. iFrame "Past_s0". iPureIntro. 
      destruct PT_s0 as (_&_&_&_&_&H'&H''). split.
      apply (H' c cn i). apply Next_c0'. by apply H1'. 
      apply (H'' c cn i). apply Next_c0'. by apply H1'. }
    iAssert (⌜m = true⌝ -∗ ∃ s : snapshot, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
      ⌜c ∈ FP s ∧ Marki s c i = true ∧ Nexti s c i = Some cn⌝)%I as "Hcase3'".
    { iIntros "%". subst m. iExists s0. iFrame "Past_s0". iPureIntro.
      repeat split; try done. apply Next_c0'. by apply H1'. }

    iModIntro. iSplitR "Hpost Hc Hls".
    { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Nodes_rest". iFrame. }
    clear Habs0 PT0 Trans_M0 PT_s0 Next_c0' H1'.

    destruct m; wp_pures.
    { iDestruct ("FP_cn'" with "[%]") as "FP_cn"; try done.
      iDestruct ("Hcase3'" with "[%]") as "Hcase3"; try done.
      destruct (decide (pn = c)) as [-> | Hpnc].
      iApply ("IH" $! p c cn []); try done. iFrame "Htr FP_cn".
      iIntros "%". rewrite /past_marked_segment. iApply "Hcase3"; try done.
      iDestruct ("Hls" with "[%]") as "Hls"; try done.
      iAssert (past_marked_segment Σ Hg1 Hg2 Hg3 γ_m t0 i pn (ls ++ [c]) cn)
        with "[Hls]" as "Hls".
      { rewrite /past_marked_segment. 
        destruct ls as [| n lss] eqn: Def_ls. 
        - iSimpl. iFrame "Hls". iSplit. iIntros (j)"%H'". exfalso. clear -H'; lia.
          iApply "Hcase3"; try done.
        - iSimpl. iDestruct "Hls" as "(Hls1 & Hls2 & Hls3)".
          iFrame "Hls1". iSplit.
          + iIntros (j)"%Hj". rewrite app_length /= in Hj. 
            destruct (decide (j = length lss)) as [-> | Hj'].
            assert ((n :: lss ++ [c]) !!! length lss = 
              (n :: lss) !!! (length (n :: lss) - 1)) as ->.
            { rewrite /=. rewrite (lookup_total_app_l (n :: lss) [c]). 
              rewrite Nat.sub_0_r. done. rewrite /=. lia. }
            assert ((n :: lss ++ [c]) !!! (length lss + 1)%nat = c) as ->.
            { assert (length lss + 1 = length (n :: lss)) as ->.
              { rewrite /=. lia. } 
              rewrite (list_lookup_total_middle (n :: lss)); try done. }
            iFrame "Hls3".
            assert ((n :: lss ++ [c]) !!! j = (n :: lss) !!! j) as ->.
            { rewrite (lookup_total_app_l (n :: lss) [c]). done.
              rewrite /=; lia. }
            assert ((n :: lss ++ [c]) !!! (j + 1)%nat = 
              (n :: lss) !!! (j + 1)%nat) as ->.
            { rewrite (lookup_total_app_l (n :: lss) [c]). done.
              rewrite /=; lia. }
            iApply "Hls2". iPureIntro. 
            assert (length (lss ++ [c]) = length lss + 1) as H'.
            { by rewrite app_length /=. }
            rewrite /=. lia.
          + assert ((n :: lss ++ [c]) !!! (length (lss ++ [c]) - 0) = c) as ->.
            { rewrite app_length /=. 
            rewrite (list_lookup_total_middle (n :: lss)); try done.
            rewrite /=; lia. }
            iApply "Hcase3"; try done. }
      iSpecialize ("IH" $! p pn cn (ls ++ [c])).
      iApply ("IH" with "[Hls]"); try done. iFrame "Htr FP_cn".
      iIntros "%". done. }
    awp_apply compareKey_spec. 
    iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl')"(HR & SShot1 & Res & %PT1 & %Trans_M1)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I as %[-> ->]. admit.
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
    { apply leibniz_equiv in Habs1. rewrite -Habs1.
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s0] [%]"); try done. }
    rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
    iDestruct "Nodes" as "(Node_c & Nodes_rest)".
    iAaccIntro with "Node_c".
    { iIntros "Node_c". iModIntro. iFrame "Hpost Hc Hls".
      iNext; iExists M1, T1, s1. iFrame "∗%#". iExists hd, tl. iFrame "∗%#".
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto. iFrame. }
    iIntros (res)"(Node_c & %Hif)".
    iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
          as ">(#Past_s1&Hist)"; try done.
    iAssert (⌜Key s1 c = Key s0 c⌝)%I as %Key_c10.
    { apply leibniz_equiv in Habs1. rewrite -Habs1.
      iPoseProof (key_eq_2 with "[%] [$Hist] [$Past_s0] [%]") as "->"; try done. }
    iModIntro. iSplitR "Hpost Hls".
    { iNext. iExists M1, T1, s1. iFrame "∗%". iExists hd, tl. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
      iFrame "Nodes_rest". iFrame. }
    clear Habs1 PT1 Trans_M1.
    wp_pures.
    destruct (bool_decide (#res = #0)) eqn: Hbool.
    { wp_pures. iApply ("IH" $! c cn cn []); try done.
      assert (Key s0 c < k) as H'.
      { rewrite -Key_c10. rewrite bool_decide_eq_true in Hbool.
        inversion Hbool. rewrite decide_True in Hif; last first.
        clear -H0; lia. done. }
      iDestruct ("Hcase" with "[%] [%]") as "H'"; try done.
      iFrame "H'". iDestruct "H'" as "(_&H')". iFrame "H'".
      iIntros "%"; try done. }
    rewrite bool_decide_eq_false in Hbool.
    assert (res ≠ 0) as res_neq_0. 
    { intros ->. apply Hbool. apply f_equal. apply f_equal. lia. }
    wp_pures. destruct (bool_decide (#pn = #c)) eqn: Hpnc.
    - rewrite bool_decide_eq_true in Hpnc. inversion Hpnc. subst pn.
      wp_pures. destruct (bool_decide (#res = #1)) eqn:Hbool1.
      + wp_pures. iApply ("Hpost" $! (Some (p, c, true))). iSimpl.
        iModIntro. iFrame "Htr". iIntros "%Hi0". iApply "Hcase2"; try done.
        iPureIntro. rewrite bool_decide_eq_true in Hbool1.
        inversion Hbool1. rewrite decide_False in Hif; try done.
        rewrite decide_True in Hif; try lia.
      + wp_pures. iApply ("Hpost" $! (Some (p, c, false))). iSimpl.
        iModIntro. iFrame "Htr". iIntros "%Hi0". iApply "Hcase1"; try done.
        iPureIntro. rewrite bool_decide_eq_false in Hbool1.
        rewrite decide_False in Hif; try done.
        rewrite decide_False in Hif; try lia. intros ->. apply Hbool1. 
        apply f_equal. apply f_equal. lia.
    - iClear "Hcase Htr' Hcase1 Hcase2 FP_cn' Hcase3' Past_s0".
      wp_pure credit: "Hc". wp_pures. awp_apply changeNext_spec; try done.
      iInv "HInv" as (M2 T2 s2) "(>Ds & >%Habs2 & >Hist & Help & >Templ)".
      iDestruct "Templ" as (hd' tl')"(HR & SShot2 & Res & %PT2 & %Trans_M2)".
      iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I as %[-> ->]. admit.
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iPoseProof (snapshot_current with "[%] [#] [$]") 
        as ">(#Past_s2&Hist)"; try done.
      iAssert (⌜p ∈ FP s2⌝)%I as %FP_p2.
      { apply leibniz_equiv in Habs2. rewrite -Habs2.
        iDestruct "Htr" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
        destruct Htr_sp as (H'&_). 
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
      rewrite (big_sepS_delete _ (FP s2) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAssert (⌜i < Height s2 p⌝)%I as %Height_p2.
      { apply leibniz_equiv in Habs2. rewrite -Habs2.
        iDestruct "Htr" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
        destruct Htr_sp as (H'&_&_&H''&_). 
        iPoseProof (height_eq_2 _ _ _ _ p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. }
      iAssert ((node _ p (Height s2 p) (Mark s2 p) (Next s2 p) (Key s2 p)) 
        ∗ ⌜i < Height s2 p⌝)%I with "[Node_p]" as "Hpre".
      { iFrame "Node_p %". }
      iAaccIntro with "Hpre".
      { iIntros "(Node_p&_)". iModIntro. iFrame "Hpost Hc Hls".
        iNext; iExists M2, T2, s2. iFrame "∗%#". iExists hd, tl. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s2) p); last by eauto. iFrame. }
      iIntros (success next') "(Node_p & Hsuccess)".
      iApply (lc_fupd_add_later with "Hc"). iNext. 
      destruct success; last first.
      { iDestruct "Hsuccess" as %(_&->).
        iModIntro. iSplitR "Hpost Hls".
        { iNext. iExists M2, T2, s2. iFrame "∗%". iExists hd, tl. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s2) p); last by eauto.
          iFrame "Nodes_rest". iFrame. }
        wp_pures. iApply ("Hpost" $! None). done. }
      
      iDestruct "Hsuccess" as %[Next_p2' [Mark_p2 Def_next']].
      assert (pn ≠ c) as pn_neq_c.
      { intros <-. rewrite bool_decide_eq_false in Hpnc. by apply Hpnc. }
      iDestruct ("Hls" with "[%]") as "Hls"; try done.
      (*
      destruct ls as [| pnn lss] eqn: Def_ls. 
      { iDestruct "Hls" as %H'. clear -H' pn_neq_c; done. }
      rewrite <-Def_ls. iDestruct "Hls" as "#Hls". 
      *)
      iAssert (⌜per_tick_inv hd tl s2⌝)%I as %PT_s2.
      { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }

      iAssert (⌜Key s2 p < k⌝)%I as %Key_pk. 
      { apply leibniz_equiv in Habs2. rewrite -Habs2.
        iDestruct "Htr" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
        destruct Htr_sp as (H'&H''&_).
        iPoseProof (key_eq_2 _ _ _ _ p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. }
      assert (Key s2 p < W) as Key_pW. { clear -Key_pk Range_k; lia. }
      assert (p ≠ tl) as p_neq_tl.
      { intros ->. destruct PT_s2 as ((_&_&H'&_)&_). clear -H' Key_pk Range_k; lia. }
      iAssert (⌜Key s2 c = Key s1 c⌝)%I as %Key_c21.
      { apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (key_eq_2 _ _ _ _ c with "[%] [$Hist] [$Past_s1] [%]") as "->"; 
          try done. }

      assert (Next s2 p !! i = Some pn) as Next_p2.
      { rewrite lookup_lookup_total. by rewrite Next_p2'. rewrite -elem_of_dom.
        apply PT_s2 in FP_p2. destruct FP_p2 as (_&H'&_). rewrite H'.
        rewrite elem_of_gset_seq. lia. done. }
      
      iAssert (⌜Marki s2 pn i = true⌝)%I as %Marki_pn2.
      { rewrite /past_marked_segment. destruct ls as [ | n lss] eqn: Def_ls. 
        iDestruct "Hls" as (s)"(Past_s & %FP_pn & %Mark_pn & _)".
        apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (marking_mono_2 _ _ _ _ pn with "[%] [$Hist] [$Past_s] [%]") 
          as "->"; try done.
        rewrite <-Def_ls.
        iDestruct "Hls" as "(H'&_)". 
        iDestruct "H'" as (s)"(Past_s & %FP_pn & %Mark_pn & _)".
        apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (marking_mono_2 _ _ _ _ pn with "[%] [$Hist] [$Past_s] [%]") 
          as "->"; try done. }
      iAssert (∀ n, ⌜n ∈ ls⌝ → ⌜Marki s2 n i = true⌝)%I as %Marki_ls.
      { rewrite /past_marked_segment. destruct ls as [ | n0 lss] eqn: Def_ls.
        iIntros (n)"%H'"; clear -H'; set_solver.
        rewrite <-Def_ls.
        iIntros (n)"%Hn". assert (Hn' := Hn). 
        apply elem_of_list_lookup_total in Hn'. destruct Hn' as [j [Hj Def_j]].
        destruct (decide (j = length ls - 1)) as [-> | Hlj].
        - iDestruct "Hls" as "(_&_&H')". 
          iDestruct "H'" as (s)"(Past_s & %FP_n & %Mark_n & _)".
          apply leibniz_equiv in Habs2. rewrite -Habs2.
          iPoseProof (marking_mono_2 _ _ _ _ n with "[%] [$Hist] [$Past_s] [%]") 
            as "->"; try done. all: by rewrite -Def_j.
        - assert (j < length ls - 1) as Hj'. { clear - Hlj Hj. lia. }
          iDestruct "Hls" as "(_&H'&_)".
          iDestruct ("H'" with "[%]") as "H''". apply Hj'.
        iDestruct "H''" as (s)"(Past_s & %FP_n & %Mark_n & _)".
        apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (marking_mono_2 _ _ _ _ n with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. all: by rewrite -Def_j. }
      iAssert (⌜ls = []⌝ -∗ ⌜Nexti s2 pn i = Some c⌝)%I as %Nexti_pn2.
      { iIntros "%". subst ls.
        iDestruct "Hls" as (s)"(Past_s & %FP_pn & %Mark_pn & %Next_pn)".
        apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (next_unchanged _ _ _ _ pn with "[%] [$Hist] [$Past_s] [%]") 
          as "->"; try done. }
      iAssert (∀ pnn lss, ⌜ls = pnn :: lss⌝ -∗ 
        ⌜Nexti s2 pn i = Some pnn⌝)%I as %Nexti_pn2'.
      { iIntros (pnn lss)"%". subst ls.
        iDestruct "Hls" as "(Hls&_)". 
        iDestruct "Hls" as (s)"(Past_s & %FP_pn & %Mark_pn & %Next_pn)".
        apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (next_unchanged _ _ _ _ pn with "[%] [$Hist] [$Past_s] [%]") 
          as "->"; try done. }
      iAssert (∀ j, ⌜j < length ls - 1⌝ → 
        ⌜Nexti s2 (ls !!! j) i = Some (ls !!! (j+1)%nat)⌝)%I as %Nexti_ls.
      { rewrite /past_marked_segment. destruct ls as [ | n0 lss] eqn: Def_ls.
        iIntros (j)"%H'"; clear -H'. exfalso. rewrite /= in H'. lia.
        rewrite <-Def_ls.
        iIntros (j)"%Hj". iDestruct "Hls" as "(_&H'&_)". 
        iDestruct ("H'" with "[%]") as "H''". apply Hj.
        iDestruct "H''" as (s)"(Past_s & %FP_n & %Mark_n & %Next_n)".
        apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (next_unchanged _ _ _ _ (ls !!! j) with "[%] [$Hist] [$Past_s] [%]") 
          as "->"; try done. }
      iAssert (∀ pnn lss, ⌜ls = pnn :: lss⌝ -∗
        ⌜Nexti s2 (ls !!! (length ls - 1)) i = Some c⌝)%I as %Nexti_lsc.
      { iIntros (pnn lss)"%". subst ls. iDestruct "Hls" as "(_&_&H')". 
        iDestruct "H'" as (s)"(Past_s & %FP_n & %Mark_n & %Next_n)".
        apply leibniz_equiv in Habs2. rewrite -Habs2.
        iPoseProof (next_unchanged _ _ _ _ _ with "[%] [$Hist] [$Past_s] [%]") 
          as "->"; try done. }
      iAssert (⌜c ∈ FP s2⌝)%I as %FP_c2. 
      { apply leibniz_equiv in Habs2. rewrite -Habs2.
        iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
      iAssert (⌜i < Height s2 c⌝)%I as %Ht_c2. 
      { apply leibniz_equiv in Habs2. rewrite -Habs2.
        iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
        iPoseProof (height_eq_2 Σ Hg1 Hg2 Hg3 c with "[%] [$] [$Past_s] [%]") as "->"; 
          try done. }

      destruct (decide (i = 0)) as [-> | Hi0].
      + iDestruct "SShot2" as %[FP2 [C2 [Ht2 [Mk2 [Nx2 [Ky2 [I2 
          [Hs2 [Dom_Ht2 [Dom_Mk2 [Dom_Nx2 [Dom_Ky2 Dom_I2]]]]]]]]]]]].
        assert (∀ x, x ∈ FP s2 → flow_constraints_I x (FI s2 x) 
              (Mark s2 x !!! 0) (Next s2 x !! 0) (Key s2 x)) as Hflow.
        { destruct PT_s2 as (_&_&_&H'&_).
          intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&?). }
        assert (∀ x, I2 !!! x = FI s2 x) as I2_eq_s2.
        { intros x. rewrite Hs2; unfold FI. try done. }
        assert (p ∈ dom I2) as p_in_I2. { by rewrite Hs2 /= -Dom_I2 in FP_p2. }
        

        iAssert (⌜∃ (I: gmap Node (multiset_flowint_ur nat)),
                    dom I = {[p; pn]} ∪ list_to_set ls
                  ∧ dom I ⊆ dom I2
                  ∧ Key s2 p < Key s2 c
                  ∧ ([^op set] x ∈ dom I, FI s2 x) = ([^op set] x ∈ dom I, I !!! x)
                  ∧ (I !!! p = int {| infR := inf_map (FI s2 p); 
                                  outR := <<[ c := out (FI s2 p) pn ]>> ∅ |})
                  ∧ (∀ x, x ∈ dom I → x ≠ p → 
                      I !!! x = int {| infR := {[x := ∅]}; outR := ∅ |})
                  ∧ (flow_constraints_I p (I !!! p) (Mark s2 p !!! 0)
                      (Some c) (Key s2 p))
                  ∧ (∀ x, x ∈ dom I → x ≠ p → flow_constraints_I x (I !!! x) 
                      (Mark s2 x !!! 0) (Next s2 x !! 0) (Key s2 x))
                  ∧ (∀ x, x ∈ dom I → keyset (I !!! x) = keyset (I2 !!! x))⌝)%I 
          as %[I Hflupd].
        { assert (∃ (Nx: gmap Node Node), ∀ x, Nx !! x = Next s2 x !! 0)
            as [Nx Def_Nx].
          { admit. }
          assert (∃ (Mk: gmap Node bool), ∀ (x: Node), Mk !! x = Mark s2 x !! 0)
            as [Mk Def_Mk'].
          { admit. }
          assert (∀ x, Mk !!! x = Mark s2 x !!! 0) as Def_Mk.
          { intros n. rewrite lookup_total_alt. by rewrite Def_Mk'. }
          assert (dom Nx ⊆ dom Nx2) as Dom_Nx.
          { intros n. rewrite !elem_of_dom. rewrite Def_Nx.
            rewrite Hs2. unfold Nexti, Next.
            destruct (Nx2 !! n) eqn: H'; try done.
            rewrite H'. rewrite lookup_empty. 
            intros [? H'']; try done. }
          assert (dom Mk = dom Mk2) as Dom_Mk.
          { apply set_eq_subseteq; split.
            - intros n. rewrite !elem_of_dom. rewrite Def_Mk'.
              rewrite Hs2. unfold Mark.
              destruct (Mk2 !! n) eqn: H'; try done.
              rewrite H'. rewrite lookup_empty. 
              intros [? H'']; try done.
            - intros n. rewrite !elem_of_dom. rewrite Def_Mk'.
              rewrite Hs2. unfold Mark.
              destruct (Mk2 !! n) eqn: H'; try done.
              rewrite H'. intros _.
              assert (H1' := H'). 
              apply elem_of_dom_2 in H'.
              rewrite Dom_Mk2 in H'.
              destruct PT_s2 as (_&_&_&PT&_).
              rewrite {1}Hs2 in PT. unfold FP in PT.
              apply PT in H'. destruct H' as (_&_&H'&_).
              rewrite Hs2 /Mark H1' in H'.
              rewrite -elem_of_dom H' elem_of_gset_seq. clear; lia.
              intros [? H'']; try done. }
          assert (∀ x, Ky2 !!! x = Key s2 x) as Def_Ky2.
          { rewrite Hs2. unfold Key. try done. }

          assert (nx_key_rel Nx Ky2) as Nx_key_rel.
          { destruct PT_s2 as (_&_&_&_&H'&_). intros n1 n2.
            rewrite !Def_Nx !Def_Ky2. apply H'. }
          assert (nx_mk_closed Nx Mk (dom I2)) as Hcl.
          { split; last split; last split. 
            - rewrite Dom_I2 -Dom_Nx2. done.
            - rewrite Dom_Mk. clear -Dom_Mk2 Dom_I2; set_solver.
            - destruct PT_s2 as (_&_&_&_&_&H'&_). intros n1 n2.
              rewrite {2}Hs2 in H'. unfold FP in H'.
              rewrite !Def_Nx Dom_I2. apply H'.
            - intros x Hmx Hnx.
              assert (x ∈ FP s2) as H'. rewrite /FP Hs2 -Dom_Mk2.
              apply elem_of_dom_2 in Hmx. by rewrite -Dom_Mk.
              apply PT_s2 in H'. destruct H' as (_&H'&_).
              destruct (decide (x = tl)) as [-> | Hxtl].
              + destruct PT_s2 as ((_&_&_&_&H''&_)&_).
                pose proof H'' 0 as H''. rewrite -Def_Mk in H''; try done.
                apply lookup_total_correct in Hmx. rewrite Hmx in H''.
                clear -H'' HL; try (done || lia).
              + apply H' in Hxtl. 
                rewrite Def_Nx in Hnx; try done. 
                rewrite -not_elem_of_dom Hxtl in Hnx. apply Hnx.
                rewrite elem_of_gset_seq. clear; lia. }
          assert (marked_segment Nx Mk pn ls c) as Hms.
          { rewrite /marked_segment. repeat split.
            rewrite Def_Mk. by rewrite /Marki in Marki_pn2.
            intros x. rewrite Def_Mk. rewrite /Marki in Marki_ls. apply Marki_ls.
            destruct ls as [ | pnn lss] eqn: Def_ls. 
            rewrite /= Def_Nx. by apply Nexti_pn2.
            repeat split. rewrite Def_Nx. by apply (Nexti_pn2' pnn lss).  
            intros x. rewrite Def_Nx. rewrite /Nexti in Nexti_ls. apply Nexti_ls.
            rewrite Def_Nx. by apply (Nexti_lsc pnn lss). }
          clear Nexti_lsc Nexti_ls Nexti_pn2 Nexti_pn2'.
          assert (✓ ([^op set] x ∈ dom I2, (I2 !!! x: multiset_flowint_ur nat))) 
            as VI.
          { destruct PT_s2 as (_&H'&_).
            unfold GFI in H'. rewrite Dom_I2.
            rewrite {2}Hs2 in H'. unfold FP in H'.
            assert (([^op set] x ∈ FP2, I2 !!! x) = 
              ([^op set] x ∈ FP2, FI s2 x)) as H1'.
            { by apply big_opS_ext. }
            by rewrite H1'. }
          assert (FP s2 = dom I2) as FP_s2_I2.
          { by rewrite /FP Hs2 Dom_I2. }
          rewrite FP_s2_I2 in Hflow.
          assert (∀ x, x ∈ dom I2 → dom (I2 !!! x: multiset_flowint_ur nat) 
            = {[x]}) as Domm_I2.
          { intros x Hx%Hflow. destruct Hx as (Hx&_). by rewrite I2_eq_s2. }
          assert (∀ x, x ∈ dom I2 → Mk !!! x = true → 
            keyset (I2 !!! x) = ∅) as KS_mk.
          { intros x Hx%Hflow. rewrite Def_Mk I2_eq_s2. 
            rewrite /Marki; intros H'; rewrite H' in Hx. 
            by destruct Hx as (_&_&_&Hx&_). }
          assert (∀ n1 n2, insets (I2 !!! n1) ≠ ∅ → Nx !! n1 = Some n2 → 
            dom (out_map (I2 !!! n1: multiset_flowint_ur nat)) = {[n2]}) 
            as Nx_dom.
          { intros n1 n2 Hin Nx_n1. assert (n1 ∈ dom I2) as H'.
            { apply elem_of_dom_2 in Nx_n1. apply Dom_Nx in Nx_n1. 
              by rewrite Dom_I2 -Dom_Nx2. }
            apply Hflow in H'. destruct H' as (_&H'&_).
            rewrite -Def_Nx Nx_n1 -I2_eq_s2 in H'. by apply H' in Hin. }
          assert (∀ x k, x ∈ dom I2 → 
            inf ((I2 !!! x):multiset_flowint_ur _) x !!! k ≤ 1) as Inf_x.
          { intros x k' Hx%Hflow. destruct Hx as (_&_&_&_&_&H'&_).
            rewrite I2_eq_s2. apply H'. }
          assert (∀ x x' k, x ∈ dom I2 → 
            out ((I2 !!! x):multiset_flowint_ur _) x' !!! k ≤ 1) as Out_x.
          { intros x x' k' Hx%Hflow. destruct Hx as (_&_&_&_&_&_&H').
            rewrite I2_eq_s2. apply H'. }
          assert (∀ x, x ∈ dom I2 → outsets (I2 !!! x) ⊆ insets (I2 !!! x))
            as Out_In.
          { intros x Hx%Hflow. destruct Hx as (_&_&H'&_).
            rewrite I2_eq_s2. apply H'. }
          
          
          assert (insets (I2 !!! p) ≠ ∅) as Insets_p_ne.
          { apply Hflow in p_in_I2. rewrite -I2_eq_s2 Mark_p2 in p_in_I2.
            destruct p_in_I2 as (_&_&_&(H'&_)&_).
            apply (non_empty_inhabited_L k). apply H'.
            rewrite elem_of_gset_seq. clear -Range_k Key_pk; lia. }
          assert (Nx !! p = Some pn) as Nx_p.
          { by rewrite Def_Nx. }
          set S : nzmap nat nat := out (I2 !!! p) pn.
          assert (W ∈ outset _ (I2 !!! p) pn) as Outset_W.
          { apply Hflow in p_in_I2. rewrite -I2_eq_s2 Mark_p2 in p_in_I2.
            assert (W ∈ outsets (I2 !!! p)) as H'.
            { destruct p_in_I2 as (_&_&_&(_&H')&_). rewrite -H' elem_of_gset_seq.
              split; try done. clear -Key_pW; lia. }
            rewrite /outsets in H'. destruct p_in_I2 as (_&H''&_).
            apply H'' in Insets_p_ne. rewrite Next_p2 in Insets_p_ne.
            by rewrite Insets_p_ne big_opS_singleton in H'. }
          assert (dom S ≠ ∅) as Dom_S.
          { rewrite /S. rewrite /outset in Outset_W. clear -Outset_W; set_solver. }
          assert (∀ x y, Nx !! x = Some y → 
            insets ((I2 !!! x: multiset_flowint_ur nat)) ≠ ∅ → 
              inf ((I2 !!! y : multiset_flowint_ur nat)) y = 
              out ((I2 !!! x: multiset_flowint_ur nat)) y) as Inf_eq_Out.
          { intros x y Nx_x Insets_x. rewrite !I2_eq_s2.
            assert (x ∈ dom I2) as x_in_I2.
            { apply elem_of_dom_2 in Nx_x. apply Hcl in Nx_x. done. }
            assert (y ∈ dom I2) as y_in_I2.
            { destruct Hcl as (_&_&H'&_). apply (H' x). done. }
            rewrite I2_eq_s2 in Insets_x.
            apply (outflow_eq_inflow hd tl); try done.
            all: try (by rewrite FP_s2_I2). rewrite Def_Nx in Nx_x. apply Nx_x. }
          set I' := list_flow_upd_unlink p pn ls c S Nx Mk I2.
          assert (list_flow_upd_unlink p pn ls c S Nx Mk I2 = I') as Def_I'.
          { by rewrite /I'. }

          pose proof unlink_flow_upd_summary Ky2 p pn ls c Nx Mk I2 I'
            Nx_key_rel Hcl Hms Dom_S Nx_p VI Domm_I2 Nx_dom KS_mk Inf_eq_Out 
            Out_In Inf_x Out_x Insets_p_ne Def_I' as Hflupd.
          destruct Hflupd as (Dom_I'&Dom_I'_in_I2&Ky_pc&Heq&I'_p&I'_x).
          iPureIntro. exists I'. 
          
          assert (insets (I' !!! p) = insets (I2 !!! p)) as Insets_p.
          { rewrite I'_p. clear. 
            rewrite /insets /dom /flowint_dom /inset /inf /=. done. }
          assert (outsets (I' !!! p) = outsets (I2 !!! p)) as Outsets_p.
          { apply Nx_dom in Nx_p; try done. rewrite /outsets Nx_p.
            assert (dom (out_map (I' !!! p : multiset_flowint_ur _)) = {[c]}) as H'.
            { rewrite I'_p. rewrite /= -leibniz_equiv_iff nzmap_dom_insert_nonzero.
              rewrite /dom; clear; set_solver. rewrite -/S. intros ->.
              clear -Dom_S. rewrite /ccmunit /= in Dom_S. set_solver. }
            rewrite H' -leibniz_equiv_iff !big_opS_singleton.
            by rewrite /outset I'_p /out /= nzmap_lookup_total_insert. }
          assert (∀ x, x ∈ dom I' → x ≠ p → insets (I' !!! x) = ∅) as Insets_x.
          { intros x Hx Hxp. rewrite I'_x; try done. clear.
            rewrite /insets /dom /flowint_dom /= dom_singleton_L.
            rewrite -leibniz_equiv_iff big_opS_singleton.
            rewrite /inset /inf /= lookup_insert /=. set_solver. }
          assert (∀ x, x ∈ dom I' → x ≠ p → outsets (I' !!! x) = ∅) as Outsets_x.
          { intros x Hx Hxp. rewrite I'_x; try done. clear. rewrite /outsets /=.
            assert (dom ∅ = (∅: gset Node)) as ->. set_solver. 
            rewrite big_opS_empty. set_solver. }
          split; last split; last split; last split; last split; 
            last split; last split; last split; try done.
          - by rewrite !Def_Ky2 in Ky_pc.
          - by rewrite Hs2 Heq. 
          - by rewrite I'_p I2_eq_s2.
          - assert (flow_constraints_I p (I2 !!! p) (false) (Some pn) (Key s2 p))
              as Hp. 
            { apply Hflow in p_in_I2. 
              by rewrite -I2_eq_s2 Mark_p2 Next_p2 in p_in_I2. }
            rewrite Mark_p2 I'_p. repeat split.
            + rewrite /= /flowint_dom /=. by apply Domm_I2.
            + intros ?. rewrite /= -leibniz_equiv_iff nzmap_dom_insert_nonzero.
              rewrite /dom; clear; set_solver. rewrite -/S. intros ->.
              clear -Dom_S. rewrite /ccmunit /= in Dom_S. set_solver.
            + rewrite -I'_p Insets_p Outsets_p. apply Hp.
            + rewrite -I'_p Insets_p. apply Hp. 
            + rewrite -I'_p Outsets_p. apply Hp.
            + rewrite -I'_p Insets_p. apply Hp.
            + intros ?; rewrite /=; apply Hp.
            + intros n k'; rewrite /out /=.
              destruct (decide (n = c)) as [-> | Hnc].
              rewrite nzmap_lookup_total_insert. apply Hp.
              rewrite nzmap_lookup_total_insert_ne; try done. 
              rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit; clear; lia.
          - intros x Hx Hxp. 
            assert (Mark s2 x !!! 0 = true) as ->.
            { rewrite Dom_I' !elem_of_union !elem_of_singleton in Hx. 
              destruct Hx as [[-> | ->] | Hx]; try done. apply Marki_ls.
              clear - Hx; set_solver. }
            repeat split.
            + rewrite I'_x; try done. 
              rewrite /dom /flowint_dom /=. clear; set_solver.
            + rewrite Insets_x; try done.
            + rewrite Insets_x; try done. rewrite Outsets_x; try done.
            + rewrite /keyset. rewrite Insets_x; try done. 
              rewrite Outsets_x; try done.
            + rewrite Insets_x; try done. 
            + intros ?; rewrite I'_x; try done. rewrite /inf /= lookup_insert /=.
              rewrite nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia.
            + intros n k'; rewrite /out /out_map /=. rewrite I'_x /=; try done.
              rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit; clear; lia.
          - intros x Hx. destruct (decide (x = p)) as [-> | Hxp].
            + by rewrite /keyset Insets_p Outsets_p.
            + assert (H' := Hx). rewrite Dom_I' in Hx.
              assert (Mk !!! x = true) as Hmkx.
              { clear -Hxp Hx Hms. destruct Hms as (Hm1&Hm2&_).
                destruct (decide (x = pn)) as [-> | Hxpn]; try done.
                apply Hm2. set_solver. }
              apply KS_mk in Hmkx. rewrite Hmkx.
              rewrite /keyset Insets_x; try done. rewrite Outsets_x; try done.
              by apply Dom_I'_in_I2 in H'. }
        
        clear Nexti_lsc Nexti_ls Nexti_pn2 Nexti_pn2'.

        set Nx2' := <[p := next']> Nx2.
        set I2' := intf_merge I I2.
        set s2' := (FP2, C2, Ht2, Mk2, Nx2', Ky2, I2'): snapshot.
        set M2' := <[T2 + 1 := s2']> M2.

        assert (abs s2 = C2) as Habs2'.
        { rewrite Hs2. by unfold abs. }
        assert (dom I ⊆ dom I2) as Dom_I_in_I2.
        { by apply Hflupd. }
        iAssert (⌜snapshot_constraints s2'⌝)%I as "SShot2'".
        { iPureIntro. exists FP2, C2, Ht2, Mk2, Nx2', Ky2, I2'.
          repeat split; try done.
          rewrite /Nx2'. rewrite dom_insert_L.
          assert (p ∈ dom Nx2) as H'. 
          { rewrite Hs2 in FP_p2. rewrite Dom_Nx2. by unfold FP in FP_p2. }
          clear -H' Dom_Nx2. set_solver.
          rewrite /I2'. rewrite intf_merge_dom; try done. }
        
        assert (FP s2' = FP s2) as FP_s2'.
        { by rewrite Hs2 /s2'; unfold FP. }
        assert (∀ n, n ≠ p → Next s2' n = Next s2 n) as HN.
        { intros n Hnp. 
          rewrite /Next /s2' Hs2 /= /Nx2' lookup_insert_ne; try done. }
        assert (Next s2' p = <[0:=c]> (Next s2 p)) as HNp.
        { by rewrite /s2' Hs2 /Next /Nx2' lookup_insert Def_next' /Next Hs2. }
        assert (∀ n, Key s2' n = Key s2 n) as HK.
        { by rewrite /Key /s2' Hs2 /=. }
        assert (∀ n, Height s2' n = Height s2 n) as HT.
        { by rewrite /s2' Hs2 /=. }
        assert (∀ n, n ∈ dom I → FI s2' n = I !!! n) as HI.
        { rewrite /FI /s2' /= /I2'. intros n Hn. 
          rewrite intf_merge_lookup; try done. }
        assert (∀ n, n ∈ dom I2 → n ∉ dom I → FI s2' n = FI s2 n) as HI'.
        { rewrite /FI /s2' Hs2 /= /I2'. intros n Hn Hn'. 
          rewrite intf_merge_lookup_ne; try done. clear -Hn Hn'; set_solver. }
        assert (∀ n, Mark s2' n = Mark s2 n) as HM.
        { by rewrite /FI /s2' Hs2. }
        assert (FP s2 = dom I2) as FP_I2.
        { by rewrite Hs2 /FP. }

        assert (abs s2' = abs s2) as Habs'.
        { by rewrite /abs /s2' Hs2. }
        iAssert (dsRepI _ _ _ _ γ_r (abs s2'))%I with "[Ds]" as "Ds".
        { by rewrite Habs'. }
        iAssert (own γ_ks (● prodKS (KS, abs s2')))%I with "[GKS]" as "GKS".
        { by rewrite Habs'. }
        iAssert (resources _ _ γ_ks s2')%I 
          with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
        { iFrame "GKS". rewrite FP_s2'. iSplitR "Nodes_KS".
          rewrite (big_opS_delete _ (FP s2) p); try done.
          iSplitL "Node_p". rewrite Def_next' HNp HM HK HT. done.
          iApply (big_sepS_mono with "Nodes_rest"); try done.
          intros x Hx. iIntros "Hn". rewrite HK HM HT HN. done.
          clear -Hx; set_solver.
          iApply (big_sepS_mono with "Nodes_KS"); try done.
          intros x Hx. iIntros "Hn".
          assert (Content s2' x = Content s2 x) as ->.
          { rewrite /Content /Marki HM HK. done. }
          assert (keyset (FI s2' x) = keyset (FI s2 x)) as ->.
          { destruct (decide (x ∈ dom I)) as [Hx1 | Hx1].
            rewrite HI; try done. destruct Hflupd as (_&_&_&_&_&_&_&_&H').
            rewrite -I2_eq_s2 H'; try done.
            rewrite HI'; try done. by rewrite -FP_I2. }
          done. }
        
        iAssert (⌜∀ n k, n ∈ FP s2' → k ∈ keyset (FI s2' n) →
          (k ∈ abs s2' ↔ k ∈ Content s2' n)⌝)%I as "%Hks".
        { iDestruct "Res" as "(GKS & _ & HKS)".
          iPoseProof (keyset_summary with "GKS HKS") as "%H'"; try done. }
        
        assert (p ∈ dom I) as p_in_I.
        { destruct Hflupd as (->&_). clear; set_solver. }

        assert (per_tick_inv hd tl s2') as PT_s2'.
        { destruct PT_s2 as (PT1'&PT2'&PT3'&PT4'&PT5'&PT6'&PT7').
          split; last split; last split; last split; last split; last split.
          - rewrite FP_s2' !HK !HM !HT. repeat split; try apply PT1'. 
            destruct (decide (p = hd)) as [-> | Hphd]. 
            rewrite HNp. rewrite lookup_insert_ne. apply PT1'. 
            clear -HL; lia.
            all: rewrite HN; try done; apply PT1'.
            - rewrite /GFI FP_s2'.
              assert (([^op set] x ∈ FP s2, FI s2' x) 
                = ([^op set] x ∈ FP s2, I2' !!! x)) as ->.
              { apply big_opS_ext. intros x Hx'.
                by rewrite /s2' /FI /=. }
              unfold GFI in PT2'.
              assert (([^op set] x ∈ FP s2, I2' !!! x) 
                = ([^op set] x ∈ FP s2, FI s2 x)) as ->; last done.
              rewrite {1 3}Hs2 /FP -Dom_I2.
              assert (([^op set] x ∈ dom I2, FI s2 x) 
                = ([^op set] x ∈ dom I2, I2 !!! x)) as ->.
              { apply big_opS_ext. intros x Hx'.
                by rewrite Hs2 /FI /=. }
              symmetry. apply (intf_merge_intfEq I); try done.
              assert (([^op set] x ∈ dom I, I2 !!! x)
                = ([^op set] x ∈ dom I, FI s2 x)) as ->.
              { apply big_opS_ext. intros x Hx.
                rewrite Hs2; unfold FI; try done. }
              by apply Hflupd.
          - apply Hks. 
          - intros n Hn. assert (Hnn := Hn). rewrite FP_s2' in Hn. apply PT4' in Hn.
            destruct (decide (n ∈ dom I)) as [Hn' | Hn'].
            + destruct (decide (n = p)) as [-> | Hnp].
              * rewrite HNp HK HM HT HI; try done.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split; try done.
                intros H'. assert (H1' := H'). apply Hn2 in H1'. 
                rewrite dom_insert_L H1'.
                assert (0 ∈ gset_seq 0 (Height s2 p - 1)) as H''.
                { rewrite elem_of_gset_seq; split; clear; lia. }
                clear -H''; set_solver. 
                rewrite lookup_insert. apply Hflupd.
              * rewrite HM HT HK HI; try done. rewrite HN; try done.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split; try done.
                apply Hflupd. all: done.
            + rewrite HK HM HT HN; try done. rewrite HI'; try done.
              by rewrite FP_s2' FP_I2 in Hnn. clear -p_in_I Hn'; set_solver.
          - intros n1 n2. destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite /Nexti HNp !HK.
              rewrite lookup_insert. intros [=<-]. apply Hflupd.
            + rewrite !HK /Nexti HN; try done. apply PT5'. 
          - intros n1 n2 i'. rewrite FP_s2'. 
            destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite /Nexti HNp. destruct (decide (i' = 0)) as [-> | Hi'i].
              rewrite lookup_insert. intros [=<-]. done.
              rewrite lookup_insert_ne; try done. apply PT6'.
            + rewrite /Nexti HN; try done. apply PT6'.
          - intros n1 n2 i. rewrite /Nexti. 
            destruct (decide (n1 = p)) as [-> | Hn1p]; last first.
            { rewrite HT HN; try done. apply PT7'. }
            rewrite HNp. destruct (decide (i = 0)) as [-> | Hi0].
            + rewrite lookup_insert HT. intros [=<-]. apply PT4' in FP_c2.
              destruct FP_c2 as (_&_&_&H'&_). apply Ht_c2.
            + rewrite HT lookup_insert_ne; try done. apply PT7'. }
        assert (transition_inv s2 s2') as Trans_s2.
        { repeat split; try rewrite FP_s2'; try done; last first.
          - intros n i' Hfp. rewrite /Marki HM. done.
          - intros n. rewrite /Marki HM. intros H' H''. 
            rewrite H' in H''; try done. 
          - intros n' i' Hn'. destruct (decide (n' = p)) as [-> | Hnp].
            + rewrite /Marki HM /Nexti HNp. 
              destruct (decide (i' = 0)) as [-> | Hi].
              rewrite Mark_p2. clear; try done.
              rewrite lookup_insert_ne; try done.
            + rewrite /Marki /Nexti HM HN; try done. }
        
        iAssert (⌜dom M2 = gset_seq 0 T2⌝)%I as %Dom_M2. 
        { by iDestruct "Hist" as (M2'') "(_&_&%&_)". }

        iAssert (|==> hist _ _ _ _ γ_t γ_m M2' (T2+1))%I with "[Hist]" as ">Hist".
        { iPoseProof (hist_upd _ _ _ _ _ _ _ _ _ s2' with "[%] [%] [$Hist]") as ">H'".
          apply  Habs2. intros <-. rewrite map_eq_iff in HNp.
          pose proof HNp 0 as HNp. rewrite Next_p2 lookup_insert in HNp.
          inversion HNp; try done. by rewrite /M2'. }
        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> 
          helping_inv _ _ _ _ N γ_t γ_r γ_mt γ_msy M2' ∗ dsRep _ _ _ _ γ_r (abs s2'))%I with
          "[Help Ds]" as ">(Help & Ds)".
        { iMod (fupd_mask_subseteq (⊤ ∖ ↑cntrN N)) as "H'". { clear; set_solver. }
          iPoseProof ("Upd" with "[%] [Ds] [Help]") as ">Help"; try done.
          apply leibniz_equiv in Habs2. iMod "H'" as "_". by iModIntro. }
        iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
          as ">(#Past_s2'&Hist)"; try done.
        iEval (rewrite /M2' lookup_total_insert) in "Past_s2'".

        iAssert (traversal_inv _ _ _ _ γ_m t0 0 k p c)%I as "#Htr'".
        { iSplitL; iExists s2'; iFrame "Past_s2'". iPureIntro. 
          repeat split; try (by rewrite FP_s2' || done).
          by rewrite HK. rewrite /Marki HM Mark_p2. done. rewrite HT. done.
          by rewrite /Nexti HNp lookup_insert. iPureIntro. split. 
          by rewrite FP_s2'. by rewrite HT. }
        iAssert (⌜Marki s2 c 0 = false⌝ -∗ ⌜Key s1 c = k⌝ -∗
          ∃ s : snapshot, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
            ⌜k ∈ abs s ∧ k = Key s c ∧ c ∈ FP s ∧ Marki s c 0 = false⌝)%I as "#Hcase1".
        { iIntros "%Marki_c2 %Key_c2". rewrite -Key_c21 in Key_c2.
          iExists s2'. iFrame "Past_s2'". iPureIntro. rewrite -FP_s2' in FP_c2.
          assert (Marki s2' c 0 = false) as Marki_c2'.
          { rewrite /Marki HM. apply Marki_c2. }
          repeat split; try done.
          pose proof Hks c k FP_c2 as Hks. apply Hks. 
          apply (in_keyset hd tl s2' p c k); try done.
          rewrite FP_s2'. done. rewrite /Marki HM. done.
          rewrite /Nexti HNp lookup_insert. done. rewrite !HK. 
          clear -Key_c2 Key_pk; lia.
          rewrite /Content Marki_c2' HK Key_c2. clear; set_solver. 
          by rewrite HK. }
        iAssert (⌜Marki s2 c 0 = false⌝ -∗ ⌜k < Key s1 c⌝ -∗
          ∃ s : snapshot, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
            ⌜(k ∉ abs s) ∧ k < Key s c ∧ c ∈ FP s⌝)%I as "#Hcase2".
        { iIntros "%Marki_c2 %Key_c2". rewrite -Key_c21 in Key_c2.
          iExists s2'. iFrame "Past_s2'". iPureIntro. rewrite -FP_s2' in FP_c2.
          assert (Marki s2' c 0 = false) as Marki_c2'.
          { rewrite /Marki HM. apply Marki_c2. }
          repeat split; try done.
          assert (k ∈ keyset (FI s2' c)) as KS_k.
          { apply (in_keyset hd tl s2' p c k); try done.
            rewrite FP_s2'. done. rewrite /Marki HM. done.
            rewrite /Nexti HNp lookup_insert. done. rewrite !HK. 
            clear -Key_c2 Key_pk; lia. }
          pose proof Hks c k FP_c2 KS_k as Hks. intros H'%Hks. 
          rewrite /Content Marki_c2' HK elem_of_singleton in H'. 
          clear -Key_c2 H'; lia. by rewrite HK. }
  

        iModIntro. iSplitR "Hpost".
        { iNext. iExists M2', (T2+1), s2'. iFrame "∗#%". 
          iSplitR. iPureIntro. rewrite /M2'. by rewrite lookup_total_insert.
          iExists hd, tl. iFrame "∗#%".
          iPureIntro; rewrite /M2'; split.
          - intros t Ht. destruct (decide (t = T2+1)) as [-> | Ht'].
            + by rewrite lookup_total_insert.
            + rewrite lookup_total_insert_ne; try done. apply PT2.
              clear -Ht' Ht; lia.
          - intros t Ht. destruct (decide (t = T2)) as [-> | Ht'].
            + rewrite lookup_total_insert. rewrite lookup_total_insert_ne.
              apply leibniz_equiv in Habs2. by rewrite Habs2. clear; lia.
            + rewrite !lookup_total_insert_ne. apply Trans_M2.
              all: clear -Ht Ht'; lia. }
        wp_pures.

        awp_apply findNext_spec.
        iInv "HInv" as (M3 T3 s3) "(>Ds & >%Habs3 & >Hist & Help & >Templ)".
        iDestruct "Templ" as (hd' tl')"(HR & SShot3 & Res & %PT3 & %Trans_M3)".
        iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I as %[-> ->]. admit.
        iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
        iAssert (⌜c ∈ FP s3⌝)%I as %FP_c3.
        { apply leibniz_equiv in Habs3. rewrite -Habs3.
          iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
          iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
        rewrite (big_sepS_delete _ (FP s3) c); last by eauto.
        iDestruct "Nodes" as "(Node_c & Nodes_rest)".
        iAssert (⌜0 < Height s3 c⌝)%I as %Height_c3.
        { apply leibniz_equiv in Habs3. rewrite -Habs3.
          iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
          iPoseProof (height_eq_2 Σ Hg1 Hg2 Hg3 c with "[%] [$] [$Past_s] [%]") as "->"; 
            try done. }
        iAssert ((node Σ c (Height s3 c) (Mark s3 c) (Next s3 c) (Key s3 c)) 
          ∗ ⌜0 < Height s3 c⌝)%I with "[Node_c]" as "Hpre".
        { iFrame "Node_c %". }
        iAaccIntro with "Hpre".
        { iIntros "(Node_c & _)". iModIntro. iFrame "Hpost".
          iNext; iExists M3, T3, s3. iFrame "∗%#". iExists hd, tl. iFrame "∗%#". 
          rewrite (big_sepS_delete _ (FP s3) c); last by eauto. 
          iFrame "Nodes_rest". iFrame. }
        iIntros (m' cn') "(Node_c & %Mark_c3 & %Next_c3)".
        iAssert (⌜per_tick_inv hd tl s3⌝)%I as %PT_s3.
        { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
        iAssert (⌜m' = false⌝ -∗ ⌜Marki s2 c 0 = false⌝)%I as %Marki_c2.
        { iIntros "%". subst m'. destruct (decide (Marki s2 c 0 = false)); try done.
          iExFalso. rewrite not_false_iff_true in n.
          iAssert (⌜Marki s3 c 0 = Marki s2 c 0⌝)%I as %H'.
          { apply leibniz_equiv in Habs3. rewrite -Habs3.
            iPoseProof (marking_mono_2 _ _ _ _ c with "[%] [$Hist] [$Past_s2] [%]") 
              as "->"; try done. }
          rewrite n /Marki H in H'. exfalso; clear -H'; done. }
    
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M3, T3, s3. iFrame "∗%". iExists hd, tl. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s3) c); last by eauto.
          iFrame "Nodes_rest". iFrame. }
        destruct m'; wp_pures.
        { iApply ("Hpost" $! None). done. }
        assert (Marki s2 c 0 = false) as H'.
        { by apply Marki_c2. }
        destruct (bool_decide (#res = #1)) eqn: Hbool1.
        { wp_pures. iApply ("Hpost" $! (Some (p, c, true))). iSimpl.
          iFrame "Htr'". iModIntro. iIntros "_". iApply "Hcase1"; try done.
          iPureIntro. rewrite bool_decide_eq_true in Hbool1. inversion Hbool1.
          rewrite decide_False in Hif. rewrite decide_True in Hif. done.
          clear -H0; lia. intros ->. clear -H0; lia. }
        { wp_pures. iApply ("Hpost" $! (Some (p, c, false))). iSimpl.
          iFrame "Htr'". iModIntro. iIntros "_". iApply "Hcase2"; try done.
          iPureIntro. rewrite bool_decide_eq_false in Hbool1.
          rewrite decide_False in Hif; try done. rewrite decide_False in Hif. done.
          intros ->. apply Hbool1; clear; apply f_equal; apply f_equal; lia. }
      + iDestruct "SShot2" as %[FP2 [C2 [Ht2 [Mk2 [Nx2 [Ky2 [I2 
          [Hs2 [Dom_Ht2 [Dom_Mk2 [Dom_Nx2 [Dom_Ky2 Dom_I2]]]]]]]]]]]].
        set Nx2' := <[p := next']> Nx2.
        set s2' := (FP2, C2, Ht2, Mk2, Nx2', Ky2, I2): snapshot.
        set M2' := <[T2 + 1 := s2']> M2.
        
        assert (FP s2' = FP s2) as FP_s2'.
        { by rewrite /FP /s2' Hs2. }
        assert (abs s2' = abs s2) as Habs'.
        { by rewrite /abs /s2' Hs2. }
        iAssert (dsRepI _ _ _ _ γ_r (abs s2'))%I with "[Ds]" as "Ds".
        { by rewrite Habs'. }
        iAssert (own γ_ks (● prodKS (KS, abs s2')))%I with "[GKS]" as "GKS".
        { by rewrite Habs'. }
        assert (∀ n, n ≠ p → Next s2' n = Next s2 n) as HN.
        { intros n Hnc. 
          rewrite /Next /s2' Hs2 /= /Nx2' lookup_insert_ne; try done. }
        assert (Next s2' p = <[i:=c]> (Next s2 p)) as HNp.
        { by rewrite /s2' Hs2 /Next /Nx2' lookup_insert Def_next' /Next Hs2. }
        assert (∀ n, Key s2' n = Key s2 n) as HK.
        { by rewrite /Key /s2' Hs2 /=. }
        assert (∀ n, FI s2' n = FI s2 n) as HI.
        { by rewrite /FI /s2' Hs2 /=. }
        assert (∀ n, Mark s2' n = Mark s2 n) as HM.
        { by rewrite /FI /s2' Hs2. }
        assert (∀ n, Height s2' n = Height s2 n) as HT.
        { by rewrite /FI /s2' Hs2. }
        
        iAssert (⌜snapshot_constraints s2'⌝)%I as "SShot2'".
        { iPureIntro. exists FP2, C2, Ht2, Mk2, Nx2', Ky2, I2.
          repeat split; try done.
          rewrite /Nx2'. rewrite dom_insert_L.
          assert (p ∈ dom Nx2). 
          { rewrite Hs2 in FP_p2. rewrite Dom_Nx2. by unfold FP in FP_p2. }
          clear -H Dom_Nx2. set_solver. }
        
        iAssert (resources _ _ γ_ks s2')%I 
          with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
        { iFrame "GKS". rewrite FP_s2'. iSplitR "Nodes_KS".
          rewrite (big_opS_delete _ (FP s2) p); try done.
          iSplitL "Node_p". rewrite Def_next' HNp HT HM HK. done.
          iApply (big_sepS_mono with "Nodes_rest"); try done.
          intros x Hx. iIntros "Hn". rewrite HK HT HM HN. done.
          clear -Hx; set_solver.
          iApply (big_sepS_mono with "Nodes_KS"); try done.
          intros x Hx. iIntros "Hn". rewrite HI.
          assert (Content s2' x = Content s2 x) as ->.
          rewrite /Content HK /Marki HM. done. done. }

        assert (per_tick_inv hd tl s2') as PT_s2'.
        { destruct PT_s2 as (PT1'&PT2'&PT3'&PT4'&PT5'&PT6'&PT7').
          split; last split; last split; last split; last split; last split.
          - rewrite FP_s2' !HK !HM !HT. repeat split; try apply PT1'. 
            destruct (decide (p = hd)) as [-> | Hphd]. 
            rewrite HNp. rewrite lookup_insert_ne; try done. apply PT1'.
            clear -HiL; lia. all: rewrite HN; try done; apply PT1'.
          - rewrite /s2' /GFI /FP /FI. by rewrite Hs2 /GFI /FP /FI in PT2'.
          - intros n k'. rewrite FP_s2' HI Habs' /Content /Marki HM HK.
            apply PT3'.
          - intros n Hn. rewrite FP_s2' in Hn. apply PT4' in Hn.
            destruct (decide (n = p)) as [-> | Hnp].
            + rewrite HNp HK HI HT HM.
              destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
              split; last split; last split; last split; last split; try done.
              * intros H'. assert (H1' := H'). apply Hn2 in H1'. 
                rewrite dom_insert_L H1'.
                assert (i ∈ gset_seq 0 (Height s2 p - 1)) as H''.
                rewrite elem_of_gset_seq. split; try lia.
                clear -H''; set_solver.
              * rewrite lookup_insert_ne; try done.
            + rewrite HK HT HI HM. rewrite HN; try done.
          - intros n1 n2. destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite /Nexti HNp !HK. 
              rewrite lookup_insert_ne; try done. apply PT5'.
            + rewrite !HK /Nexti HN; try done. apply PT5'. 
          - intros n1 n2 i'. rewrite FP_s2'. 
            destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite /Nexti HNp. destruct (decide (i = i')) as [-> | Hi'i].
              rewrite lookup_insert. intros [=<-]. done. 
              rewrite lookup_insert_ne; try done. apply PT6'.
            + rewrite /Nexti HN; try done. apply PT6'.
          - intros n1 n2 i'. rewrite /Nexti. 
            destruct (decide (n1 = p)) as [-> | Hn1p]; last first.
            { rewrite HT HN; try done. apply PT7'. }
            rewrite HNp. destruct (decide (i' = i)) as [-> | Hii'].
            + rewrite lookup_insert HT. intros [=<-]. done.
            + rewrite HT lookup_insert_ne; try done. apply PT7'. }
        assert (transition_inv s2 s2') as Trans_s2.
        { repeat split; try rewrite FP_s2'; try done; last first.
          - intros n i' Hfp. rewrite /Marki HM. done.
          - intros n. rewrite /Marki HM. intros H' H''. 
            rewrite H' in H''; try done.
          - intros n' i' Hn'. destruct (decide (n' = p)) as [-> | Hnp].
            + rewrite /Marki HM /Nexti HNp. 
              destruct (decide (i' = i)) as [-> | Hi].
              rewrite Mark_p2. clear; try done.
              rewrite lookup_insert_ne; try done.
            + rewrite /Marki /Nexti HM HN; try done. }

        iAssert (⌜dom M2 = gset_seq 0 T2⌝)%I as %Dom_M2. 
        { by iDestruct "Hist" as (M2'') "(_&_&%&_)". }

        iAssert (|==> hist _ _ _ _ γ_t γ_m M2' (T2+1))%I with "[Hist]" as ">Hist".
        { iPoseProof (hist_upd _ _ _ _ _ _ _ _ _ s2' with "[%] [%] [$Hist]") as ">H'".
          apply  Habs2. intros <-. rewrite map_eq_iff in HNp.
          pose proof HNp i as HNp. rewrite Next_p2 lookup_insert in HNp.
          inversion HNp; try done. by rewrite /M2'. }
        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> 
          helping_inv _ _ _ _ N γ_t γ_r γ_mt γ_msy M2' ∗ dsRep _ _ _ _ γ_r (abs s2'))%I with
          "[Help Ds]" as ">(Help & Ds)".
        { iMod (fupd_mask_subseteq (⊤ ∖ ↑cntrN N)) as "H'". { clear; set_solver. }
          iPoseProof ("Upd" with "[%] [Ds] [Help]") as ">Help"; try done.
          apply leibniz_equiv in Habs2. iMod "H'" as "_". by iModIntro. }
        iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
          as ">(#Past_s2'&Hist)"; try done.
        iEval (rewrite /M2' lookup_total_insert) in "Past_s2'".

        iAssert (traversal_inv _ _ _ _ γ_m t0 i k p c)%I as "#Htr'".
        { iSplitL; iExists s2'; iFrame "Past_s2'". iPureIntro. 
          repeat split; try (by rewrite FP_s2' || done).
          by rewrite HK. rewrite /Marki HM. apply PT_s2 in FP_p2.
          destruct FP_p2 as (H'&_). apply H'. by exists i. rewrite HT. done.
          iPureIntro. split. by rewrite FP_s2'. by rewrite HT. }

        iModIntro. iSplitR "Hpost".
        { iNext. iExists M2', (T2+1), s2'. iFrame "∗#%". 
          iSplitR. iPureIntro. rewrite /M2'. by rewrite lookup_total_insert.
          iExists hd, tl. iFrame "∗#%".
          iPureIntro; rewrite /M2'; split.
          - intros t Ht. destruct (decide (t = T2+1)) as [-> | Ht'].
            + by rewrite lookup_total_insert.
            + rewrite lookup_total_insert_ne; try done. apply PT2.
              clear -Ht' Ht; lia.
          - intros t Ht. destruct (decide (t = T2)) as [-> | Ht'].
            + rewrite lookup_total_insert. rewrite lookup_total_insert_ne.
              apply leibniz_equiv in Habs2. by rewrite Habs2. clear; lia.
            + rewrite !lookup_total_insert_ne. apply Trans_M2.
              all: clear -Ht Ht'; lia. }
        wp_pures.
          
        awp_apply findNext_spec.
        iInv "HInv" as (M3 T3 s3) "(>Ds & >%Habs3 & >Hist & Help & >Templ)".
        iDestruct "Templ" as (hd' tl')"(HR & SShot3 & Res & %PT3 & %Trans_M3)".
        iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I as %[-> ->]. admit.
        iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
        iAssert (⌜c ∈ FP s3⌝)%I as %FP_c3.
        { apply leibniz_equiv in Habs3. rewrite -Habs3.
          iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
          iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
        rewrite (big_sepS_delete _ (FP s3) c); last by eauto.
        iDestruct "Nodes" as "(Node_c & Nodes_rest)".
        iAssert (⌜i < Height s3 c⌝)%I as %Height_c3.
        { apply leibniz_equiv in Habs3. rewrite -Habs3.
          iDestruct "FP_c" as (s)"(Past_s & %FP_c & %Ht_c)".
          iPoseProof (height_eq_2 Σ Hg1 Hg2 Hg3 c with "[%] [$] [$Past_s] [%]") as "->"; 
            try done. }
        iAssert ((node Σ c (Height s3 c) (Mark s3 c) (Next s3 c) (Key s3 c)) 
          ∗ ⌜i < Height s3 c⌝)%I with "[Node_c]" as "Hpre".
        { iFrame "Node_c %". }
        iAaccIntro with "Hpre".
        { iIntros "(Node_c & _)". iModIntro. iFrame "Hpost".
          iNext; iExists M3, T3, s3. iFrame "∗%#". iExists hd, tl. iFrame "∗%#". 
          rewrite (big_sepS_delete _ (FP s3) c); last by eauto. 
          iFrame "Nodes_rest". iFrame. }
        iIntros (m' cn') "(Node_c & %Mark_c3 & %Next_c3)".
        iAssert (⌜per_tick_inv hd tl s3⌝)%I as %PT_s3.
        { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M3, T3, s3. iFrame "∗%". iExists hd, tl. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s3) c); last by eauto.
          iFrame "Nodes_rest". iFrame. }
        destruct m'; wp_pures.
        { iApply ("Hpost" $! None). done. }
        destruct (bool_decide (#res = #1)) eqn: Hbool1.
        { wp_pures. iApply ("Hpost" $! (Some (p, c, true))). iSimpl.
          iModIntro. iFrame "Htr'". iIntros "%H'". clear -Hi0 H'; lia. }
        { wp_pures. iApply ("Hpost" $! (Some (p, c, false))). iSimpl.
          iModIntro. iFrame "Htr'". iIntros "%H'". clear -Hi0 H'; lia. }
  Admitted.

  Lemma traverse_pop_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r tid t0 k 
    preds succs ps0 ss0 (i: nat) hd tl:
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
        {{{ is_array Σ Hg1 preds ps0 ∗ is_array Σ Hg1 succs ss0 
            ∗ ⌜length ps0 = L⌝ ∗ ⌜length ss0 = L⌝ ∗ ⌜i+1 < L⌝
            ∗ ⌜ps0 !!! (L-1) = hd⌝ ∗ ⌜ss0 !!! (L-1) = tl⌝
            ∗ (∀ j, ⌜i < j < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 j k (ps0 !!! j) (ss0 !!! j)) }}}
          traverse_pop #k #preds #succs #i @ ⊤
        {{{ (ores: option (loc * loc * bool)) (ps ss: list Node) (b: bool), 
              RET (match ores with 
                    None => NONEV 
                  | Some res => SOMEV (#res.1.1,#res.1.2,#res.2) end);
              match ores with 
                None => is_array Σ Hg1 preds ps0 ∗ is_array Σ Hg1 succs ss0
              | Some res => 
                ⌜res.1.1 = preds⌝ ∗ ⌜res.1.2 = succs⌝ ∗ ⌜res.2 = b⌝
              ∗ is_array Σ Hg1 preds ps ∗ is_array Σ Hg1 succs ss
              ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
              ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
              ∗ (∀ j, ⌜i-1 < j < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 j k (ps !!! j) (ss !!! j))
              ∗ (⌜i = 0⌝ →  let p := ps !!! 0 in
                            let c := ss !!! 0 in
                            traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 0 k p c ∗ 
                            (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
                              ⌜if b then 
                                  k ∈ abs s ∧ k = Key s c 
                                  ∧ c ∈ FP s ∧ Marki s c 0 = false
                                else 
                                  k ∉ abs s ∧ k < Key s c 
                                  ∧ c ∈ FP s⌝)) end }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & %Len_ps0 & %Len_ss0 & %Len_i 
      & %Hps0_L & %Hss0_L & #Hj)". 
    wp_lam. wp_pures. iEval (rewrite /is_array) in "Hpreds".
    assert (is_Some (ps0 !! (i+1))) as [p Hp].
    { by rewrite lookup_lt_is_Some Len_ps0. } 
    assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
    iEval (rewrite <-H'). clear H'.
    wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i+1) ((λ n : loc, #n) <$> ps0) #p
      with "[Hpreds]"); try done. 
    { by rewrite list_lookup_fmap Hp /=. }
    iIntros "Hpreds".
    iAssert (is_array Σ Hg1 preds ps0) with "[Hpreds]" as "Hpreds".
    { unfold is_array. iFrame. }
    wp_pures. wp_bind (findNext _ _)%E. 
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl') "(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I as %[-> ->]. admit.
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 (i+1) k p (ss0 !!! (i+1)%nat))%I as "#Htr_i1". 
    { iAssert (⌜i < i+1 < L⌝)%I as "H'". by iPureIntro; lia.
      iPoseProof ("Hj" with "H'") as "H''". 
      apply list_lookup_total_correct in Hp. rewrite Hp. done. }
    iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0. 
      iDestruct "Htr_i1" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
      destruct Htr_sp as (H'&_).
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
    rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
    iDestruct "Nodes" as "(Node_p & Nodes_rest)".
    iAssert (⌜i < Height s0 p⌝)%I as %Height_p0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "Htr_i1" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
      destruct Htr_sp as (H''&_&_&H').
      iPoseProof (height_eq_2 _ _ _ _ p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
        try done. iPureIntro. clear -H'; lia. }
    iAssert ((node Σ p (Height s0 p) (Mark s0 p) (Next s0 p) (Key s0 p)) 
      ∗ ⌜i < Height s0 p⌝)%I with "[Hj Node_p]" as "Hpre".
    { iFrame "Node_p %". }
    iAaccIntro with "Hpre".    
    { iIntros "(Node_p&_)". iModIntro. iFrame "Hpost Hpreds Hsuccs".
      iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    iIntros (m c) "(Node_p & %Mark_p0 & %Next_p0)".
    iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iDestruct "Htr_i1" as "(Htr_p & Htr_si1)".
    iDestruct "Htr_p" as (s)"(#Past_s & %Htr_p)".
    iAssert (⌜Key s0 p = Key s p⌝)%I as %Key_p.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iPoseProof (key_eq_2 with "[%] [$Hist] [$Past_s] [%]") as "->"; try done.
      apply Htr_p. }
    iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
      as ">(#Past_s0&Hist)"; try done.
    iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k p c ∗ 
      hist Σ Hg1 Hg2 Hg3 γ_t γ_m M0 T0)%I with "[Hist]" as ">(#Hcase & Hist)".
    { assert (Next s0 p !! i = Some c) as Next_p0'.
      { rewrite lookup_lookup_total. by rewrite Next_p0. rewrite -elem_of_dom.
        apply PT_s0 in FP_p0. destruct FP_p0 as (_&H'&_). rewrite H'.
        rewrite elem_of_gset_seq. lia. intros ->. destruct PT_s0 as ((_&_&H''&_)&_).
        destruct Htr_p as (_&H1'&_). clear -H1' Key_p H'' Range_k. lia. }
      iAssert (∃ s1 : snapshot, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s1 ∗ 
        ⌜c ∈ FP s1 ∧ i < Height s1 c⌝)%I as "#Htr_c".
      { iExists s0. iFrame "Past_s0". iPureIntro. 
        destruct PT_s0 as (_&_&_&_&_&H'&H''). split. 
        apply (H' p c i); try done. apply (H'' p c i); try done. }
      iFrame "Htr_c". 
      destruct (decide (i = 0)) as [-> | Hi0].
      - destruct m.
        + iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
          { by iDestruct "Hist" as (M0'') "(_&_&%&_)". }
          destruct Htr_p as (FP_ps&Key_ps&Mark_ps&Height_ps&_).
          iDestruct "Past_s" as (ts)"(%t0_le_ts&Hts)".
          iPoseProof (marking_witness with "[%] [Hist] [Hts] [%] [%] [%]") 
            as "%HM"; try done. 
          apply leibniz_equiv in Habs0. by rewrite /Marki Habs0.
          destruct HM as [t [Ht [Hmt Hmt']]].
          assert (0 ≤ t < T0) as Ht'. lia.
          apply Trans_M0 in Ht'. rewrite Nat.add_1_r in Ht'.
          destruct Ht' as (Hm'&_&_&_&_&Hfp'). 
          assert (t ∈ dom M0) as t_in_M0. 
          { rewrite Dom_M0 elem_of_gset_seq; lia. }
          assert (H'' := t_in_M0).
          apply elem_of_dom in t_in_M0. destruct t_in_M0 as [s' Hs'].
          iPoseProof (snapshot_create Σ Hg1 Hg2 Hg3 t t0 with "[%] [$Hist]")
            as ">(#Past_t & Hist)"; try done. lia.

          iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> own γ_m (◯ {[t := to_agree s']}) 
            ∗ hist Σ Hg1 Hg2 Hg3 γ_t γ_m M0 T0)%I with "[Hist]" as ">(#Ht & Hist)".
          { iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
            iPoseProof (own_update _ (● M') (● M' ⋅ ◯ {[t := to_agree s']}) 
              with "HM'") as ">(HM' & #Ht')". 
            { apply auth_update_alloc, local_update_unital_discrete. 
              intros z Hm Hz. split; try done. rewrite left_id in Hz. 
              rewrite -Hz. apply map_equiv_iff. intros x. apply M_eq in Hs'.
              destruct (decide (x = t)) as [-> | Hxz].
              - rewrite lookup_op Hs' lookup_insert. rewrite /op /cmra_op /=.
                by rewrite agree_idemp.
              - rewrite lookup_op lookup_insert_ne; try done. rewrite lookup_empty.
                rewrite /op /cmra_op /=. destruct (M' !! x) eqn:H1'; 
                rewrite H1'; try done. }
            iModIntro. iFrame "Ht'". iExists M'. iFrame "∗%". } 
          assert (ts ≤ t ≤ T0) as Ht' by lia.
          iPoseProof (in_FP Σ Hg1 Hg2 Hg3 p with "[%] [$Hist] [$Hts] [%] [%]") 
            as "%FP_pt"; try done.
          pose proof Hm' p 0 FP_pt Hmt' as Hn'.

          assert (S t ∈ dom M0) as Hst.
          { rewrite Dom_M0 elem_of_gset_seq. lia. }
          assert (t0 ≤ S t) as Hst' by lia.
          iPoseProof (snapshot_create Σ Hg1 Hg2 Hg3 (S t) t0 with "[%] [$Hist]")
            as ">(#Past_st & Hist)"; try done. lia. 
          assert (FP_pst := FP_pt). apply Hfp' in FP_pst.
          iPoseProof (next_unchanged with "[%] [$Hist] [$Past_st] [%] [%]")
            as "%H'"; try done. rewrite -H' in Hn'.
          apply leibniz_equiv in Habs0. rewrite Habs0 /Nexti Next_p0' in Hn'.
          iPoseProof (height_eq with "[%] [$Hist] [$Hts] [%] [%]")
            as "%HH"; try done.
          iPoseProof (key_eq with "[%] [$Hist] [$Hts] [%] [%]")
            as "%HK"; try done.
          iModIntro. iFrame. iExists (M0 !!! t). iFrame "#". iPureIntro.
          repeat split; try done. clear -HK Key_ps; lia.  clear -HH Height_ps; lia.
        + iModIntro. iFrame.
          iExists s0. iFrame "Past_s0". iPureIntro. 
          repeat split; try done. destruct Htr_p as (_&H'&_). 
          clear -H' Key_p; lia.
      - iModIntro. iFrame.
        iExists s. iFrame "Past_s". iPureIntro. repeat split; try apply Htr_p.
        destruct Htr_p as (_&_&_&H'&_). clear -H'; lia. intros ?; try done. }
    
    iModIntro. iSplitR "Hpreds Hsuccs Hpost Hj".
    { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    wp_pures. wp_apply (traverse_i_spec _ _ _ _ []); try done. 
    { iPureIntro. lia. }
    { iFrame "Hcase". iDestruct "Hcase" as "(_&H')". iFrame "H'". by iIntros "%". }

    iIntros (ores) "Hores".
    destruct ores as [[[p' c'] b]|]; last first.
    { wp_pures. iSpecialize ("Hpost" $! None ps0 ss0 true). iApply "Hpost".
      iFrame. done. }
    iSimpl in "Hores". wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hpreds]").
    { iFrame "Hpreds". iPureIntro. rewrite Len_ps0. lia. }
    iIntros "!> Hpreds". wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hsuccs]").
    { iFrame "Hsuccs". iPureIntro. rewrite Len_ss0. lia. }
    iIntros "!> Hsuccs". wp_pures.
    iSpecialize ("Hpost" $! (Some (preds,succs,b)) _ _ b).
    iSimpl in "Hpost". iApply "Hpost".
    iModIntro. iFrame "Hpreds Hsuccs". repeat (iSplitR; first by iPureIntro).
    iDestruct "Hores" as "(#Htr & #Hzero)".
    iSplitR. iPureIntro. by rewrite insert_length.
    iSplitR. iPureIntro. by rewrite insert_length.
    iSplitR. iPureIntro. rewrite list_lookup_total_insert_ne; try done. 
    clear -Len_i; lia.  
    iSplitR. iPureIntro. rewrite list_lookup_total_insert_ne; try done. 
    clear -Len_i; lia.  
    iSplitR. iIntros (j)"%Hj". destruct (decide (j = i)) as [-> | Hij].
    { rewrite !list_lookup_total_insert. iFrame "#". 
      all: try rewrite Len_ps0 Len_ss0; lia. }
    iAssert (⌜i < j < L⌝)%I as "Hj'". { iPureIntro. lia. }
    iPoseProof ("Hj" with "Hj'") as "H'".
    rewrite !list_lookup_total_insert_ne; try done.
    iIntros "%". subst i. rewrite !list_lookup_total_insert.
    iFrame "∗#". iApply "Hzero". by iPureIntro.
    all: try rewrite Len_ps0 Len_ss0; lia.
  Admitted.

  Lemma traverse_rec_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r tid 
    t0 k preds succs ps0 ss0 (i: nat) hd tl:
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
      {{{ is_array Σ Hg1 preds ps0 ∗ is_array Σ Hg1 succs ss0
          ∗ ⌜length ps0 = L⌝ ∗ ⌜length ss0 = L⌝ ∗ ⌜i+1 < L⌝
          ∗ ⌜ps0 !!! (L-1) = hd⌝ ∗ ⌜ss0 !!! (L-1) = tl⌝
          ∗ (∀ j, ⌜i < j < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 j k (ps0 !!! j) (ss0 !!! j)) }}}
        traverse_rec #k #preds #succs #i @ ⊤
      {{{ (ps ss: list Node) (res: bool), 
            RET (#preds, #succs, #res);
            is_array Σ Hg1 preds ps ∗ is_array Σ Hg1 succs ss
          ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
          ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
          ∗ (∀ i, ⌜i < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k (ps !!! i) (ss !!! i))
          ∗ (let c := ss !!! 0 in 
                ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
                    ⌜if res then 
                      k ∈ abs s ∧ k = Key s c ∧ c ∈ FP s ∧ Marki s c 0 = false
                    else 
                      k ∉ abs s ∧ k < Key s c ∧ c ∈ FP s⌝) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iLöb as "IH" forall (i ps0 ss0). 
    iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & %Len_ps0 & %Len_ss0 & %Len_i 
      & %Hps0_L & %Hss0_L & #Hj)".
    wp_lam. wp_pures. iApply fupd_wp.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I as %[-> ->]. admit.
    iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iPoseProof (traversal_inv_hd_tl with "[%] [%] [%] [%] [#] [Hist]") 
      as ">(#HtrL & Hist)"; try done.
    iModIntro. iSplitR "Hpreds Hsuccs Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%". }
    iModIntro.      
    wp_apply (traverse_pop_spec with "[] [] [] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs Hj %". iIntros (ores ps ss b)"Hores".
    destruct ores as [[[preds' succs'] res] |]; last first.
    { wp_pures. iDestruct "Hores" as "(Hpreds & Hsuccs)".
      iApply ("IH" with "[Hpreds Hsuccs]"); try iFrame "∗%#". 
      iSplitR. iPureIntro. lia. iIntros (j)"%Hj".
      assert (j = L-1) as -> by lia. rewrite Hps0_L Hss0_L. iFrame "HtrL". }
    wp_pures. iDestruct "Hores" as "(%H' & %H'' & %H1' & H1'')". 
    rewrite /= in H' H'' H1'. subst preds' succs' b.  
    iDestruct "H1''" as "(Hpreds & Hsuccs & %Len_ps & %Len_ss & %Hps_L 
      & %Hss_L & #Hj' & #Hi0)".
    destruct (bool_decide (#i = #0)) eqn: Hbool; wp_pures.
    - rewrite bool_decide_eq_true in Hbool. inversion Hbool. iModIntro.
      iApply "Hpost". iFrame "Hpreds Hsuccs %".
      iAssert (⌜i = 0⌝)%I as "Htr0". { iPureIntro; lia. }
      iDestruct ("Hi0" with "Htr0") as "#H'". iSplit.
      + iIntros (j) "%Hj". destruct (decide (j = 0)) as [-> | Hj0].
        * iDestruct "H'" as "(H' & _)". iFrame "H'".
        * iApply "Hj'". iPureIntro; lia.
      + iDestruct "H'" as "(_ & H')". iFrame "H'".
    - iSpecialize ("IH" $! (i-1) ps ss).
      rewrite bool_decide_eq_false in Hbool.
      assert (i ≠ 0). { intros ->. apply Hbool. try done. }
      assert (Z.sub i 1 = (i-1)%nat) as -> by lia.
      iApply ("IH" with "[$Hpreds $Hsuccs]"); try done. iFrame "%#".
      iPureIntro. clear -Len_i; lia.
  Admitted.

  Lemma traverse_spec (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    N γ_t γ_r γ_m γ_mt γ_msy r tid t0 k (hd tl: Node):
    main_inv Σ H' H'' H''' N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ H' H'' H''' γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ H' H'' H''' N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
      {{{ True }}}
          traverse #hd #tl #k @ ⊤
      {{{ (preds succs: loc) (ps ss: list Node) (res: bool), 
            RET (#preds, #succs, #res);
            (preds ↦∗ ((fun n => # (LitLoc n)) <$> ps))
          ∗ (succs ↦∗ ((fun n => # (LitLoc n)) <$> ss))
          ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
          ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
          ∗ (∀ i, ⌜i < L⌝ → traversal_inv Σ H' H'' H''' γ_m t0 i k (ps !!! i) (ss !!! i))
          ∗ (let c := ss !!! 0 in 
                ∃ s, past_state Σ H' H'' H''' γ_m t0 s ∗
                    ⌜if res then 
                      k ∈ abs s ∧ k = Key s c ∧ c ∈ FP s ∧ Marki s c 0 = false
                    else 
                      k ∉ abs s ∧ k < Key s c ∧ c ∈ FP s⌝) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures. wp_bind (AllocN _ _)%E. 
    iApply array_repeat. iPureIntro; lia.
    iNext. iIntros (preds) "Hpreds".
    wp_pures. wp_bind (AllocN _ _)%E.
    iApply array_repeat. iPureIntro; lia.
    iNext. iIntros (succs) "Hsuccs". wp_pures. iApply fupd_wp.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I as %[-> ->]. admit.
    iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iPoseProof (traversal_inv_hd_tl with "[%] [%] [%] [%] [#] [Hist]") 
      as ">(#HtrL & Hist)"; try done.
    iModIntro. iSplitR "Hpreds Hsuccs Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%". }
    iModIntro.      
    wp_apply (traverse_rec_spec with "[] [] [] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs".
    iSplitR. iPureIntro. by rewrite replicate_length.
    iSplitR. iPureIntro. by rewrite replicate_length.
    iSplitR. iPureIntro. clear -HL; lia.
    iSplitR. iPureIntro. rewrite lookup_total_replicate_2. done. lia.
    iSplitR. iPureIntro. rewrite lookup_total_replicate_2. done. lia.
    iIntros (j) "%Hj". 
    assert (j = L-1) as -> by lia. rewrite !lookup_total_replicate_2.
    all : try lia. iFrame "HtrL".
  Admitted.
  
End HARRIS_SPEC.