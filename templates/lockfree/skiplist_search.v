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
(* Require Import skiplist_util. *)
Require Export traverse_spec_module flows.


Module Type SKIPLIST_SEARCH.
  Declare Module TR_SPEC : TRAVERSE_SPEC.
  Export TR_SPEC TR_SPEC.SK_UTIL TR_SPEC.SK_UTIL.SK TR_SPEC.SK_UTIL.DEFS.
  Export TR_SPEC.SK_UTIL.SK.TR TR_SPEC.SK_UTIL.SK.TR.NODE.

  Lemma searchOp_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r (p: proph_id) 
    pvs tid t0 Q k (hd tl: Node) :
      main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
      thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
      □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
      ⌜local_pre (searchOp k)⌝ -∗
      r ↦□ (#hd, #tl) -∗
        {{{ proph p pvs ∗ 
            (match process_proph tid pvs with
              contra => au Σ Hg1 Hg2 Hg3 N γ_r (searchOp k) Q
            | no_upd => True
            | upd => au Σ Hg1 Hg2 Hg3 N γ_r (searchOp k) Q end) }}}
              search #hd #tl #k @ ⊤
        {{{ (res: resT) prf pvs', RET #res;
            proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
            (match process_proph tid pvs with
              contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
            | no_upd => past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (searchOp k) res t0
            | upd => Q #res ∨ 
                ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof. 
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k] #HR'". 
    iIntros (Φ) "!# (Hproph & Hmatch) Hpost".
    wp_lam. wp_pures.
    wp_apply traverse_spec; try done.
    iIntros (preds succs ps ss res) "(Hpreds & Hsuccs & %Len_ps 
      & %Len_ss & %HpsL & %HssL & #Htr)".  
    wp_pures. 
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
    { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }  
    iAssert (past_lin_witness _ _ _ _ γ_m (searchOp k) res t0)%I as "#PastW".
    { iDestruct "Htr" as "(_ & Htr)". 
      iDestruct "Htr" as (s)"(#Past_s & %H')". 
      set c := ss !!! 0. rewrite -/c in H'.
      iPoseProof (per_tick_past with "[%] Hist Past_s") as "%PT_s"; try done.
      iExists s. iFrame "#". iPureIntro. rewrite /seq_spec. split. done.
      destruct H' as (H' & H'' & H'''). destruct PT_s as (_&_&PT&_).
      pose proof PT c k H' H'' as H1'. destruct res; set_solver. }
    iModIntro. iSplitR "Hproph Hmatch Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%". }
    destruct (process_proph tid pvs) eqn: Hpvs.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph". by iPureIntro.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph". iSplitR. by iPureIntro.
      iRight. by iPureIntro.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph #". done.
  Qed.

End SKIPLIST_SEARCH.

(*
Module SKIPLIST_INSERT (TR_SPEC : TRAVERSE_SPEC).
  Include TR_SPEC.

  Lemma insertOp_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r (p: proph_id) 
    pvs tid t0 Q k (hd tl: Node) :
      main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
      thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
      □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
      ⌜local_pre (insertOp k)⌝ -∗
      r ↦□ (#hd, #tl) -∗
        {{{ proph p pvs ∗ 
            (match process_proph tid pvs with
              contra => au Σ Hg1 Hg2 Hg3 N γ_r (insertOp k) Q
            | no_upd => True
            | upd => au Σ Hg1 Hg2 Hg3 N γ_r (insertOp k) Q end) }}}
              insert #p #hd #tl #k @ ⊤
        {{{ (res: resT) prf pvs', RET #res;
            proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
            (match process_proph tid pvs with
              contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
            | no_upd => past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (insertOp k) res t0
            | upd => Q #res ∨ 
                ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof. 
  Admitted.

End SKIPLIST_INSERT.
*)