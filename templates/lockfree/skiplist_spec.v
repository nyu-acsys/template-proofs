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
Require Export skiplist_search skiplist_delete skiplist_insert hindsight_proof.

Module SKIPLIST_SPEC : HINDSIGHT_SPEC.
  Module DS := skiplist_util.SK.
  Module DEFS := skiplist_util.DEFS.
  Export DS DEFS.
  
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
    wp_lam. wp_pures. wp_bind (! _)%E.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd tl)"(#HR & SShot0 & Res & %PT0 & %Trans_M0)".
    wp_load. iModIntro. iSplitR "Hpre Hpost".
    { iExists M0, T0, s0. iNext. iFrame "%#∗". iExists hd, tl. iFrame "%#". }
    wp_pures. unfold Op_to_val; destruct op as [k|k|k]; wp_pures.
    - wp_apply (searchOp_spec with "[] [] [] [] [Hpre]"); try done.
    - wp_apply (insertOp_spec with "[] [] [] [] [Hpre]"); try done.
    - wp_apply (deleteOp_spec with "[] [] [] [] [Hpre]"); try done.
  Qed.

End SKIPLIST_SPEC.


