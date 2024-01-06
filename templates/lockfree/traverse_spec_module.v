From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
From flows Require Import array_util skiplist_util.
Set Default Proof Using "All".

Module Type TRAVERSE_SPEC.
  Declare Module SK_UTIL : SKIPLIST_UTIL.
  Export SK_UTIL SK_UTIL.DEFS SK_UTIL.DEFS.DS.
  Export TR TR.NODE.

  Definition traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k p c : iProp Σ :=
    (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
        ∗ ⌜p ∈ FP s ∧ i < Height s p ∧ Key s p < k⌝)
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
      set_solver.
    - iPureIntro; repeat split; try (done || lia). set_solver.
  Qed. 

  Parameter traverse_rec_spec : ∀ Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r tid 
    t0 k preds succs ps0 ss0 (i: nat) (hd tl: Node),
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
    r ↦□ (#hd, #tl) -∗
      {{{ is_array Σ Hg1 preds ps0 ∗ is_array Σ Hg1 succs ss0
          ∗ ⌜length ps0 = L⌝ ∗ ⌜length ss0 = L⌝ ∗ ⌜i+1 < L⌝
          ∗ ⌜ps0 !!! (L-1) = hd⌝ ∗ ⌜ss0 !!! (L-1) = tl⌝
          ∗ (∀ j, ⌜i < j < L⌝ → 
              traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 j k (ps0 !!! j) (ss0 !!! j)
            ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
                        ∗ ⌜(ps0 !!! j) ∈ FP s ∧ Marki s (ps0 !!! j) 0 = false⌝)) }}}
        traverse_rec #k #preds #succs #i @ ⊤
      {{{ (ps ss: list Node) (res: bool), 
            RET (#preds, #succs, #res);
            is_array Σ Hg1 preds ps ∗ is_array Σ Hg1 succs ss
          ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
          ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
          ∗ (∀ i, ⌜i < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k (ps !!! i) (ss !!! i))
          ∗ (let c := ss !!! 0 in 
              ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
                ⌜c ∈ FP s ∧ k ∈ keyset (FI s c) ∧ (res ↔ k ∈ Content s c)⌝) }}}.

  
  Lemma traverse_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r tid t0 k (hd tl: Node):
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
    r ↦□ (#hd, #tl) -∗
      {{{ True }}}
          traverse #hd #tl #k @ ⊤
      {{{ (preds succs: loc) (ps ss: list Node) (res: bool), 
            RET (#preds, #succs, #res);
            (preds ↦∗ ((fun n => # (LitLoc n)) <$> ps))
          ∗ (succs ↦∗ ((fun n => # (LitLoc n)) <$> ss))
          ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
          ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
          ∗ (∀ i, ⌜i < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k (ps !!! i) (ss !!! i))
          ∗ (let c := ss !!! 0 in 
                ∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
                    ⌜c ∈ FP s ∧ k ∈ keyset (FI s c) ∧ (res ↔ k ∈ Content s c)⌝) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k] #HR'". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures. wp_bind (AllocN _ _)%E. 
    iApply array_repeat. iPureIntro; lia.
    iNext. iIntros (preds) "Hpreds".
    wp_pures. wp_bind (AllocN _ _)%E.
    iApply array_repeat. iPureIntro; lia.
    iNext. iIntros (succs) "Hsuccs". wp_pures. iApply fupd_wp.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
    { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }
    iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iPoseProof (traversal_inv_hd_tl with "[%] [%] [%] [%] [#] [Hist]") 
      as ">(#HtrL & Hist)"; try done.
    iPoseProof (snapshot_current with "[%] [#] [$Hist]") 
      as ">(#Past_s0&Hist)"; try done.
    iAssert (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
      ⌜hd ∈ FP s ∧ Marki s hd 0 = false⌝)%I as "Marked_hd".
    { iExists s0. iFrame "Past_s0". iPureIntro. destruct PT_s0 as (PT&_).
      destruct PT as (H'&_&_&H''&_). split. set_solver. apply H''. lia. }
    iModIntro. iSplitR "Hpreds Hsuccs Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%". }
    iModIntro.    
    wp_apply (traverse_rec_spec with "[] [] [] [] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs".
    iSplitR. iPureIntro. by rewrite replicate_length.
    iSplitR. iPureIntro. by rewrite replicate_length.
    iSplitR. iPureIntro. clear -HL; lia.
    iSplitR. iPureIntro. rewrite lookup_total_replicate_2. done. lia.
    iSplitR. iPureIntro. rewrite lookup_total_replicate_2. done. lia.
    iIntros (j) "%Hj". 
    assert (j = L-1) as -> by lia. rewrite !lookup_total_replicate_2.
    all : try lia. iFrame "HtrL Marked_hd".
  Qed.

End TRAVERSE_SPEC.