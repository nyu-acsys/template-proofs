(* Herlihy Skiplist with a single level : Search *)

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
Require Export skiplist_v1 skiplist_v1_util.

Module SKIPLIST1_SPEC_TRAVERSE.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS.

  Lemma array_store E (i : nat) (v : Node) arr (xs : list Node) :
    {{{ ⌜i < length xs⌝ ∗ ▷ is_array arr xs }}}
      #(arr +ₗ i) <- #v
    @ E {{{ RET #(); is_array arr (<[i:=v]>xs) }}}.
  Proof.
  Admitted.

  Lemma array_repeat (b : loc) (n : nat) :
    {{{ ⌜0 < n⌝ }}} AllocN #n #b 
    {{{ arr, RET #arr; is_array arr (replicate n b) }}}.
  Proof.
    iIntros (ϕ ?%inj_lt) "Post".
    iApply wp_allocN; try done.
    iNext. iIntros (l) "[lPts _]".
    iApply "Post".
    unfold is_array.
    rewrite Nat2Z.id.
    rewrite -> fmap_replicate.
    (* iAssumption. *)
  Admitted.


  Definition traversal_inv s i k p c : Prop :=
    p ∈ FP s 
  ∧ c ∈ FP s 
  ∧ Key s p < k 
  ∧ Marki s p i = false 
  ∧ Nexti s p i = Some c.

(*
  Lemma traverse_i_spec_high N γ_t γ_s γ_m γ_td γ_ght γ_sy t_id t0 k 
                           (i: nat) (p c: Node):
      main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ ∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p c⌝  }}}
           traverse_i #i #k #p #c
        {{{ (p' c': Node) (res: bool), 
              RET (#p', #c', #res);
              ∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p' c'⌝ }}}.
  Proof.
    iIntros "#HInv #Thd". iLöb as "IH" forall (p c).
    iIntros (Φ) "!# #HtrInv Hpost". wp_lam. wp_pures.
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(Hglob & Res & %PT0 & %Trans_M0)". 
    set γ_I := skiplist_v1.SKIPLIST1.γ_I.
    set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
    set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Res" as "((Node_c & Node_crest) & Res_rest)".
    iAaccIntro with "Node_c".
    { iIntros "Node". iModIntro. iFrame.
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Res_rest". iFrame. }
    iIntros (m c') "(Node_c & %Mark_c0 & %Next_c0)".
    iModIntro. iSplitR "Hpost".
    { iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Res_rest". iFrame. }
    clear γ_I γ_fp γ_ks.
    destruct c' as [c' |]; destruct m; wp_pures. 
    - awp_apply try_constraint_traverse_spec; try done.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(Hglob & Res & %PT1 & %Trans_M1)". 
      set γ_I := skiplist_v1.SKIPLIST1.γ_I.
      set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
      set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p1.
      { (* interpolation *) admit. }
      iAssert (past_state γ_m t0 s1) as "#Hs1".
      { admit. }
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Res" as "((Node_p & Node_prest) & Res_rest)".
      iAaccIntro with "Node_p".
      { iIntros "Node". iModIntro. iFrame.
        iNext; iExists M1, T1, s1.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto. 
        iFrame "Res_rest". iFrame. }
      iIntros (success next')"(Node_p & Hif)".
      destruct success.
      + iDestruct "Hif" as "%H'".
        destruct H' as [Mark_p1 [Next_p1 Def_next']].
        iAssert (∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p c'⌝)%I 
          as "#HtrInv'".
        { iExists s1. iFrame "Hs1". iPureIntro.
          split; try done. admit. admit. }  
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1.
          iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
          iFrame "Res_rest". admit. }
        wp_pures.
        iApply "IH"; try done.
      + iDestruct "Hif" as "%H'". 
        destruct H' as [Mark_p1 ->].
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1.
          iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
          iFrame "Res_rest". iFrame. }
        wp_pures.
        (* Restart case *) admit.  
    - awp_apply compareKey_spec. 
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(Hglob & Res & %PT1 & %Trans_M1)". 
      set γ_I := skiplist_v1.SKIPLIST1.γ_I.
      set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
      set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
      iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
      iDestruct "Res" as "((Node_c & Node_crest) & Res_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node". iModIntro. iFrame.
        iNext; iExists M1, T1, s1.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto. 
        iFrame "Res_rest". iFrame. }
      iIntros (res)"(Node_c & Hif)".
      iAssert (past_state γ_m t0 s1) as "#Hs1".
      { admit. }
      iModIntro. iSplitR "Hpost Hif".
      { iNext. iExists M1, T1, s1.
        iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
        iFrame "Res_rest". iFrame. }
      wp_pures.
      destruct (decide_rel eq #res #0); first last.
      + wp_pures. destruct (decide_rel eq #res #1); first last.
        * wp_pures. iModIntro; by iApply "Hpost". 
        * destruct (decide (res = 0)).
          { subst res. exfalso; apply n. apply f_equal.
            eauto. }
          destruct (decide (res = 1)); wp_pures; iModIntro; by iApply "Hpost". 
      + wp_pures. 
        destruct (decide (res = 0)); last first.
        { clear -e n. exfalso. injection e. intros H'.
          apply n. lia. }
        iDestruct "Hif" as %Key_c1.  
        iApply "IH"; try done.
        iExists s0. admit.
    - (* Contradiction case *) admit.
    - iModIntro; by iApply "Hpost".
  Admitted.

  Lemma traverse_pop_spec N γ_t γ_s γ_m γ_td γ_ght γ_sy t_id t0 k 
                           (i: nat) preds succs ps ss:
      main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{  is_array preds ps ∗ is_array succs ss 
              ∗ (∀ j, ⌜i < j < L⌝ → 
                  ∃ s, past_state γ_m t0 s 
                      ∗ ⌜traversal_inv s j k (ps !!! j) (ss !!! j)⌝)  }}}
           traverse_pop #k #preds #succs #i%nat
        {{{ (ps' ss': list Node) (res: bool), 
              RET (#preds, #succs, #res);
              is_array preds ps' ∗ is_array succs ss' 
              ∗ (∀ j, ⌜i - 1 < j < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s j k (ps' !!! j) (ss' !!! j)⌝) }}}.
  Proof.
    iIntros "#HInv #Thd". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & #HtrInv)".
    wp_lam. wp_pures.
    wp_bind (! _)%E.
    iEval (rewrite /is_array) in "Hpreds".
    assert (is_Some (ps !! (i+1))) as Hpred.
    { admit. }
    destruct Hpred as [p Hpred].
    assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
    iEval (rewrite <-H').
    wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i+1) ((λ n : nat, #n) <$> ps) #p
      with "[Hpreds]"); try done.
    { admit. }
    { iNext. admit. }
    iIntros "Hpreds".
    iAssert (is_array preds ps) with "[Hpreds]" as "Hpreds".
    { unfold is_array. admit. }
    wp_pures. wp_bind (findNext _ _)%E. 
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(Hglob & Res & %PT0 & %Trans_M0)". 
    set γ_I := skiplist_v1.SKIPLIST1.γ_I.
    set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
    set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
    iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
    iDestruct "Res" as "((Node_p & Node_prest) & Res_rest)".
    iAaccIntro with "Node_p".
    { iIntros "Node". iModIntro. iFrame.
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. 
      iFrame "Res_rest". iFrame. }
    iIntros (m c) "(Node_p & %Mark_p0 & %Next_p0)".
    iModIntro. iSplitR "Hpreds Hsuccs Hpost".
    { iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iFrame "Res_rest". iFrame. }
    clear γ_I γ_fp γ_ks.
    destruct c as [c |]; last first; wp_pures.
    + (* Contradiction case *) admit.
    + wp_apply traverse_i_spec_high; try done.
      { admit. }
      iIntros (p' c' res)"#HtrInv_p'".
      wp_pures. wp_bind (_ <- _)%E. 
      iApply (array_store with "[Hpreds]").
      { iFrame "Hpreds". iPureIntro. admit. }
      iNext. iIntros "Hpreds". 
      wp_pures. wp_bind (_ <- _)%E. 
      iApply (array_store with "[Hsuccs]").
      { iFrame "Hsuccs". iPureIntro. admit. }
      iNext. iIntros "Hsuccs". wp_pures.
      iApply ("Hpost"). iModIntro; iFrame.
      iIntros (j)"%Hj". destruct (decide (j = i)) as [-> | Hij].
      - assert (<[i:=p']> ps !!! i = p') as H1'. 
        (* rewrite lookup_total_insert. *)
        admit.
        assert (<[i:=c']> ss !!! i = c') as H1''. 
        admit. 
        by rewrite H1' H1''.
      - assert (<[i := p']> ps !!! j = ps !!! j) as H1'. 
        admit. 
        assert (<[i := c']> ss !!! j = ss !!! j) as H1''. 
        admit. 
        rewrite H1' H1''. iApply "HtrInv". 
        iPureIntro; lia.
  Admitted.


  Lemma traverse_loop_rec_spec N γ_t γ_s γ_m γ_td γ_ght γ_sy t_id t0 k 
                           (i: nat) preds succs ps ss:
      main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{  is_array preds ps ∗ is_array succs ss 
              ∗ (∀ j, ⌜i < j < L⌝ → 
                  ∃ s, past_state γ_m t0 s 
                      ∗ ⌜traversal_inv s j k (ps !!! j) (ss !!! j)⌝)  }}}
           traverse_loop_rec #k #preds #succs #i%nat
        {{{ (ps' ss': list Node), 
              RET #();
              is_array preds ps' ∗ is_array succs ss' 
              ∗ (∀ i, ⌜1 ≤ i < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s i k (ps' !!! i) (ss' !!! i)⌝) }}}.
  Proof.
    iIntros "#HInv #Thd". iIntros (Φ) "!# Hpre Hpost".
    iLöb as "IH" forall (i ps ss). 
    iDestruct "Hpre" as "(Hpreds & Hsuccs & #HtrInv)".
    wp_lam. wp_pures.
    destruct (decide_rel Z.le 1%nat i); first last.
    - iEval (unfold bool_decide); wp_pures.
      assert (i < 1) by lia.
      iApply "Hpost". iModIntro.
      iFrame "Hpreds Hsuccs".
      iIntros (i') "%Hi". iApply "HtrInv".
      iPureIntro; lia.
    - iEval (unfold bool_decide); wp_pures.
      wp_apply (traverse_pop_spec with "[] [] [Hpreds Hsuccs]"); try done.
      { iFrame "Hpreds Hsuccs". try done. }
      iIntros (ps' ss' res) "(Hpreds & Hsuccs & #HtrInv')". wp_pures.
      iSpecialize ("IH" $! (i-1) ps' ss').
      assert (Z.of_nat (i-1) = (Z.of_nat i - 1)%Z) as H' by lia.
      iEval (rewrite H') in "IH".
      iApply ("IH" with "[$Hpreds $Hsuccs]"); try done.
  Admitted.


  Lemma traverse_loop_spec N γ_t γ_s γ_m γ_td γ_ght γ_sy t_id t0 k 
                           preds succs ps ss:
      main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ is_array preds ps ∗ is_array succs ss 
            ∗ (∃ s, past_state γ_m t0 s 
                    ∗ ⌜traversal_inv s (L-1) k (ps !!! (L-1)) (ss !!! (L-1))⌝) }}}
           traverse_loop #k #preds #succs
        {{{ (ps' ss': list Node), 
              RET #();
              is_array preds ps' ∗ is_array succs ss' 
              ∗ (∀ i, ⌜1 ≤ i < L⌝ → 
                  ∃ s, past_state γ_m t0 s 
                        ∗ ⌜traversal_inv s i k (ps' !!! i) (ss' !!! i)⌝) }}}.
  Proof.
    iIntros "#HInv #Thd". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & #HtrInv)".
    wp_lam. wp_pures.
    assert (L > 1). admit.
    wp_apply (traverse_loop_rec_spec with "[] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs".
    iIntros (j) "%Hj".
    assert (j = L-1) as -> by lia.
    try done.
  Admitted.


  Lemma traverse_i_spec_base N γ_t γ_s γ_m γ_td γ_ght γ_sy t_id t0 k 
                           (i: nat) (p c: Node):
      main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ ∃ s, past_state γ_m t0 s ∗ ⌜k ∈ insets (FI s p)⌝
                  ∗ ⌜Marki s p 0 = false⌝ ∗ ⌜k ∈ outset _ (FI s p) c⌝ }}}
           traverse_i #0%nat #k #p #c
        {{{ (p' c': Node) (res: bool), 
              RET (#p', #c', #res);
              if res then 
                ∃ s, past_state γ_m t0 s 
                ∗ ⌜k ∈ keyset (FI s c')⌝
                ∗ ⌜k = Key s c'⌝
              else
                ∃ s, past_state γ_m t0 s 
                ∗ ⌜k ∉ abs s⌝ }}}.
  Proof.
    iIntros "#HInv #Thd". iLöb as "IH" forall (p c).
    iIntros (Φ) "!# #HtrInv Hpost". wp_lam. wp_pures.
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(Hglob & Res & %PT0 & %Trans_M0)". 
    set γ_I := skiplist_v1.SKIPLIST1.γ_I.
    set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
    set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Res" as "((Node_c & Node_crest) & Res_rest)".
    iAaccIntro with "Node_c".
    { iIntros "Node". iModIntro. iFrame.
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Res_rest". iFrame. }
    iIntros (m c') "(Node_c & %Mark_c0 & %Next_c0)".
    iModIntro. iSplitR "Hpost".
    { iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Res_rest". iFrame. }
    clear γ_I γ_fp γ_ks.
    destruct c' as [c' |]; destruct m; wp_pures. 
    - awp_apply try_constraint_traverse_spec; try done.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(Hglob & Res & %PT1 & %Trans_M1)". 
      set γ_I := skiplist_v1.SKIPLIST1.γ_I.
      set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
      set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p1.
      { (* interpolation *) admit. }
      iAssert (past_state γ_m t0 s1) as "#Hs1".
      { admit. }
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Res" as "((Node_p & Node_prest) & Res_rest)".
      iAaccIntro with "Node_p".
      { iIntros "Node". iModIntro. iFrame.
        iNext; iExists M1, T1, s1.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto. 
        iFrame "Res_rest". iFrame. }
      iIntros (success next')"(Node_p & Hif)".
      destruct success.
      + iDestruct "Hif" as "%H'".
        destruct H' as [Mark_p1 [Next_p1 Def_next']].
        iAssert (∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p c'⌝)%I 
          as "#HtrInv'".
        { iExists s1. iFrame "Hs1". iPureIntro.
          split; try done. admit. admit. }  
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1.
          iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
          iFrame "Res_rest". admit. }
        wp_pures.
        iApply "IH"; try done.
        admit.
      + iDestruct "Hif" as "%H'". 
        destruct H' as [Mark_p1 ->].
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1.
          iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
          iFrame "Res_rest". iFrame. }
        wp_pures.
        (* Restart case *) admit.  
    - awp_apply compareKey_spec. 
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(Hglob & Res & %PT1 & %Trans_M1)". 
      set γ_I := skiplist_v1.SKIPLIST1.γ_I.
      set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
      set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
      iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
      iDestruct "Res" as "((Node_c & Node_crest) & Res_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node". iModIntro. iFrame.
        iNext; iExists M1, T1, s1.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto. 
        iFrame "Res_rest". iFrame. }
      iIntros (res)"(Node_c & Hif)".
      iAssert (past_state γ_m t0 s1) as "#Hs1".
      { admit. }
      iModIntro. iSplitR "Hpost Hif".
      { iNext. iExists M1, T1, s1.
        iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
        iFrame "Res_rest". iFrame. }
      wp_pures.
      (*
      destruct (decide_rel eq #res #0); first last.
      + wp_pures. destruct (decide_rel eq #res #1); first last.
        * wp_pures. iModIntro; by iApply "Hpost". 
        * destruct (decide (res = 0)).
          { subst res. exfalso; apply n. apply f_equal.
            eauto. }
          destruct (decide (res = 1)); wp_pures; iModIntro; by iApply "Hpost". 
      + wp_pures. 
        destruct (decide (res = 0)); last first.
        { clear -e n. exfalso. injection e. intros H'.
          apply n. lia. }
        iDestruct "Hif" as %Key_c1.  
        iApply "IH"; try done.
        iExists s0. admit.
    - (* Contradiction case *) admit.
    - iModIntro; by iApply "Hpost".
    *)
  Admitted.

  Lemma traverse_pop_spec_base N γ_t γ_s γ_m γ_td γ_ght γ_sy t_id t0 k 
                           preds succs ps ss:
      main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{  is_array preds ps ∗ is_array succs ss 
             ∗ (∀ i, ⌜1 ≤ i < L⌝ → 
                  ∃ s, past_state γ_m t0 s 
                        ∗ ⌜traversal_inv s i k (ps !!! i) (ss !!! i)⌝)  }}}
           traverse_pop #k #preds #succs #0%nat
        {{{ (preds succs: loc) (ps' ss': list Node) (p c: Node) (res: bool), 
              RET (#preds, #succs, #res);
              is_array preds ps' ∗ is_array succs ss'
            ∗ (∀ i, ⌜1 ≤ i < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                           ∗ ⌜traversal_inv s i k (ps' !!! i) (ss' !!! i)⌝)
            ∗ (⌜ps' !!! 0 = p⌝) ∗ (⌜ss' !!! 0 = c⌝)
            ∗ if res then 
                ∃ s, past_state γ_m t0 s 
                ∗ ⌜k ∈ keyset (FI s c)⌝
                ∗ ⌜k = Key s c⌝
              else
                ∃ s, past_state γ_m t0 s 
                ∗ ⌜k ∉ abs s⌝ }}}.
  Proof.
    iIntros "#HInv #Thd". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & #HtrInv)".
    wp_lam. wp_pures. 
    assert (is_Some (ps !! 1)) as Hpred.
    { admit. }    
    destruct Hpred as [p Hpred].
    assert (Z.of_nat (1) = (Z.of_nat 0 + 1)%Z) as H' by lia.
    iEval (rewrite <-H').
    wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (1) ((λ n : nat, #n) <$> ps) #p
      with "[Hpreds]"); try done.
    { admit. }
    { iNext. admit. }
    iIntros "Hpreds".
    iAssert (is_array preds ps) with "[Hpreds]" as "Hpreds".
    { unfold is_array. admit. }
    wp_pures. wp_bind (findNext _ _)%E. 
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(Hglob & Res & %PT0 & %Trans_M0)". 
    set γ_I := skiplist_v1.SKIPLIST1.γ_I.
    set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
    set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
    iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
    iDestruct "Res" as "((Node_p & Node_prest) & Res_rest)".
    iAaccIntro with "Node_p".
    { iIntros "Node". iModIntro. iFrame.
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. 
      iFrame "Res_rest". iFrame. }
    iIntros (m c) "(Node_p & %Mark_p0 & %Next_p0)".
    iModIntro. iSplitR "Hpreds Hsuccs Hpost".
    { iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iFrame "Res_rest". iFrame. }
    clear γ_I γ_fp γ_ks.
    destruct c as [c |]; last first; wp_pures.
    + (* Contradiction case *) admit.
    + 
      (*
      iApply fupd_wp.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      iDestruct "Templ" as "(Hglob & Res & %PT1 & %Trans_M1)". 
      set γ_I := skiplist_v1.SKIPLIST1.γ_I.
      set γ_fp := skiplist_v1.SKIPLIST1.γ_fp.
      set γ_ks := skiplist_v1.SKIPLIST1.γ_ks.
      assert (ps !!! 1 = p) as Hp.
      { admit. }
      assert (ps !!! 1 = p) as Hp.
      { admit. }


      iAssert (⌜traversal_inv s i k (ps !!! i) (ss !!! i)⌝)%I as %Htr_pc.
      iEval (rewrite Hp) in "Hkey".
      iDestruct "Hkey" as (s)"(Hpast_s & %Key_s_p)".
      iAssert (⌜k ∈ insets (FI s p)⌝)%I as "%Insets_s_p".
      { iDestruct "Hpast_s" as (t)"Hpast_s".
        assert (t ∈ dom M1) as t_in_M1.
        { admit. }
        apply PT1 in t_in_M1.
        assert (M1 !! t = Some s) as M1_t_s.
        { admit. }
        unfold lookup_total, map_lookup_total in t_in_M1.
        rewrite M1_t_s in t_in_M1.
        simpl in t_in_M1. clear H'.
        destruct t_in_M1 as [_ [_ [_ H']]].
        assert (p ∈ FP s) as p_in_s. { admit. }
        apply H' in p_in_s.
        destruct p_in_s as [_ [_ [H'' _]]].
        iPureIntro. apply H''. admit.
        split; try done. lia. admit. }
      iModIntro. iSplitR "Hpreds Hsuccs Hpost".
      { iNext. iExists M1, T1, s1.
        iFrame "∗%". }
      clear γ_I γ_fp γ_ks. 
      iModIntro.
      *)

      wp_apply traverse_i_spec_base; try done.
      
      
      { admit. }
      iIntros (p' c' res) "Hres".
      wp_pures. wp_bind (_ <- _)%E. 
      iApply (array_store with "[Hpreds]").
      { iFrame "Hpreds". iPureIntro. admit. }
      iNext. iIntros "Hpreds". 
      wp_pures. wp_bind (_ <- _)%E. 
      iApply (array_store with "[Hsuccs]").
      { iFrame "Hsuccs". iPureIntro. admit. }
      iNext. iIntros "Hsuccs". wp_pures.
      iApply ("Hpost" $! _ _ _ _ p' c'). 
      iModIntro.
      iFrame "Hpreds Hsuccs Hres".
      iSplit. iIntros (i) "%Hi".
      assert (<[0:=p']> ps !!! i = ps !!! i) as H1'. 
      admit. rewrite H1'. 
      assert (<[0:=c']> ss !!! i = ss !!! i) as H1''. 
      admit. rewrite H1''. 
      iApply "HtrInv"; try done.
      iPureIntro; admit.
  Admitted.
*)
    
  Lemma traverse_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght (h t: Node) γ_sy t_id t0 k:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ True }}}
           traverse #h #t #k
        {{{ (preds succs: loc) (ps ss: list Node) (p c: Node) (res: bool), 
              RET (#preds, #succs, #res);
              is_array preds ps ∗ is_array succs ss
            ∗ (∀ i, ⌜1 ≤ i < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                           ∗ ⌜traversal_inv s i k (ps !!! i) (ss !!! i)⌝)
            ∗ (⌜ps !!! 0 = p⌝) ∗ (⌜ss !!! 0 = c⌝)
            ∗ (∃ s, past_state γ_m t0 s ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝
                    ∗ if res then ⌜k ∈ keyset (FI s c)⌝ ∗ ⌜k = Key s c⌝
                      else ⌜k ∉ abs s⌝) }}}.
  Proof.  
    iIntros "#HInv #Thd". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures. wp_bind (AllocN _ _)%E. Check array_repeat.
    iApply array_repeat. admit.
    iNext. iIntros (preds) "Hpreds".
    wp_pures. wp_bind (AllocN _ _)%E.
    iApply array_repeat. admit.
    iNext. iIntros (succs) "Hsuccs".
    wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hpreds]").
    iFrame "Hpreds". { iPureIntro. rewrite replicate_length. admit. }
    iNext. iIntros "Hpreds".
    wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hsuccs]").
    iFrame "Hsuccs". { iPureIntro. admit. }
    iNext. iIntros "Hsuccs". wp_pures.
    wp_apply (traverse_loop_spec with "[] [] [Hpreds Hsuccs]"); try done.
    { iFrame "Hpreds Hsuccs". admit. }
    iIntros (ps' ss') "(Hpreds & Hsuccs & #HtrInv)". wp_pures.
    wp_apply (traverse_pop_spec_base with "[] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs". iApply "HtrInv".
  Admitted.

End SKIPLIST1_SPEC_TRAVERSE.
  
  
