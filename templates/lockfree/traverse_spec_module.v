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

(* Traversal Spec *)

Module Type TRAVERSE_SPEC.
  Declare Module SK_UTIL : SKIPLIST_UTIL.
  Export SK_UTIL SK_UTIL.DEFS SK_UTIL.DEFS.DS.
  Export TR TR.NODE.

  Definition traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k p c : iProp Σ :=
    (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
        ∗ ⌜p ∈ FP s ∧ i < Height s p ∧ Key s p < k⌝)
  ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜c ∈ FP s ∧ i < Height s c⌝).
  
  Parameter traverse_spec : ∀ Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r tid t0 k (hd tl: Node)
    preds succs ps0 ss0,
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
    r ↦□ (#hd, #tl) -∗
      {{{ is_array Σ Hg1 preds ps0 ∗ is_array Σ Hg1 succs ss0
          ∗ ⌜length ps0 = L⌝ ∗ ⌜length ss0 = L⌝
          ∗ ⌜ps0 !!! (L-1) = hd⌝ ∗ ⌜ss0 !!! (L-1) = tl⌝ }}}
          traverse #hd #tl #preds #succs #k @ ⊤
      {{{ (p c : Node) (ps ss: list Node) (res: bool), 
            RET (#p, #c, #res);
            is_array Σ Hg1 preds ps ∗ is_array Σ Hg1 succs ss
          ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
          ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
          ∗ ⌜ps !!! 0 = p⌝ ∗ ⌜ss !!! 0 = c⌝
          ∗ (∀ i, ⌜i < L⌝ → traversal_inv Σ Hg1 Hg2 Hg3 γ_m t0 i k (ps !!! i) (ss !!! i))
          ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗
                    ⌜c ∈ FP s ∧ k ∈ keyset (FI s c) ∧ (res ↔ k ∈ Content s c)⌝) }}}.

End TRAVERSE_SPEC.