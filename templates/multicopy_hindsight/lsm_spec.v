(* Hindsight spec for skiplist *)

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
Require Export lsm_search lsm_upsert hindsight_proof.

Module LSM_SPEC : HINDSIGHT_SPEC.
  Declare Module UTIL : LSM_UTIL.
  Declare Module SEARCH : LSM_SEARCH with Module UTIL := UTIL.
  Declare Module UPSERT : LSM_UPSERT with Module UTIL := UTIL.
  Module DEFS := UTIL.DEFS.
  Export UTIL.DEFS UTIL.DEFS.DS UTIL.DEFS.DS.NODE. 

  Lemma dsOp_spec (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    N γ_t γ_r γ_m γ_mt γ_msy r op (p: proph_id) pvs tid t0 Q :
          main_inv Σ H' H'' H''' N γ_t γ_r γ_m γ_mt γ_msy r -∗
          thread_start Σ H' H'' H''' γ_t γ_mt tid t0 -∗
          □ update_helping_protocol Σ H' H'' H''' N γ_t γ_r γ_mt γ_msy -∗
          ⌜local_pre op⌝ -∗
            {{{ proph p pvs ∗ 
                (match process_proph tid pvs with
                  contra => au Σ H' H'' H''' N γ_r op Q
                | no_upd => True
                | upd => au Σ H' H'' H''' N γ_r op Q end) }}}
                  dsOp (Op_to_val op) #p #r @ ⊤
            {{{ (res: resT) prf pvs', RET #res;
                proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
                (match process_proph tid pvs with
                  contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
                | no_upd => past_lin_witness Σ H' H'' H''' γ_m op res t0
                | upd => Q #res ∨ 
                    ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof.
    iIntros "#HInv #Thd #HUpd %Local". unfold dsOp. 
    iIntros (Φ) "!# Hpre Hpost". 
    wp_lam. wp_pures. unfold Op_to_val. destruct op as [k|k v]; wp_pures.
    - wp_apply (SEARCH.searchOp_spec with "[] [] [] [] [Hpre]"); try done.
    - wp_apply (UPSERT.upsertOp_spec with "[] [] [] [] [Hpre]"); try done.
  Qed.

End LSM_SPEC.
