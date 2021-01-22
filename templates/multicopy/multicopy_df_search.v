From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy_df multicopy_lsm_util.

Section multicopy_df_search.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_dfG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).
  
  Lemma search_recency N γ_te γ_he γ_s Prot 
                       γ_t γ_cr γ_cd γ_d lc r d (k: K) t0 :
    ⊢ ⌜k ∈ KS⌝ -∗ 
        mcs_inv N γ_te γ_he γ_s Prot
           (Inv_DF γ_s γ_t γ_cr γ_cd γ_d lc r d) -∗
          SR γ_s (k, t0) -∗
              <<< True >>> 
                  search r #k @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ (t': nat), SR γ_s (k, t') ∗ ⌜t0 ≤ t'⌝ , RET #t' >>>.
  Proof.
  Admitted.
  
