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
Require Export traverse_spec_module flows.
  
  Export skiplist_util.TR.NODE skiplist_util.SK skiplist_util.DEFS.

  Lemma searchOp_spec (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    N γ_t γ_r γ_m γ_mt γ_msy r (p: proph_id) pvs tid t0 Q k (hd tl: Node) :
      main_inv Σ H' H'' H''' N γ_t γ_r γ_m γ_mt γ_msy r -∗
      thread_start Σ H' H'' H''' γ_t γ_mt tid t0 -∗
      □ update_helping_protocol Σ H' H'' H''' N γ_t γ_r γ_mt γ_msy -∗
      ⌜local_pre (searchOp k)⌝ -∗
        {{{ proph p pvs ∗ 
            (match process_proph tid pvs with
              contra => au Σ H' H'' H''' N γ_r (searchOp k) Q
            | no_upd => True
            | upd => au Σ H' H'' H''' N γ_r (searchOp k) Q end) }}}
              search #hd #tl #k @ ⊤
        {{{ (res: resT) prf pvs', RET #res;
            proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
            (match process_proph tid pvs with
              contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
            | no_upd => past_lin_witness Σ H' H'' H''' γ_m (searchOp k) res t0
            | upd => Q #res ∨ 
                ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof. 
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". 
    iIntros (Φ) "!# (Hproph & Hmatch) Hpost".
    wp_lam. wp_pures.
    wp_apply (traverse_spec Σ H' H'' H'''); try done.
    iIntros (preds succs ps ss res) "(Hpreds & Hsuccs & %Len_ps 
      & %Len_ss & %HpsL & %HssL & #Htr)".  
    wp_pures. 
    iAssert (past_lin_witness _ _ _ _ γ_m (searchOp k) res t0)%I as "#PastW".
    { iDestruct "Htr" as "(_ & Htr)". destruct res.
      all: iDestruct "Htr" as (s)"(#Past_s & %Hk_s & _)".
      all: iExists s; iFrame "#"; iPureIntro. all: set_solver. }
    destruct (process_proph tid pvs) eqn: Hpvs.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph". by iPureIntro.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph". iSplitR. by iPureIntro.
      iRight. by iPureIntro.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph #". done.
  Qed.