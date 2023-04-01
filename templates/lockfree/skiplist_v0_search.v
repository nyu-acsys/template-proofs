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
Require Export skiplist_v0_traverse.

Section skiplist_v0_search.

  Context {Σ} `{!heapGS Σ, !dsG Σ, !skG Σ}.
  Notation iProp := (iProp Σ).

  
  Lemma searchOp_spec N γ_s γ_t γ_m γ_td γ_ght γ_I γ_fp γ_ks r (k: K) γ_sy t_id t0:
        ⌜k ∈ KS⌝ -∗
          css_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv γ_I γ_fp γ_ks r) -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     search r #k
                {{{ res, RET #res; past_lin_witness γ_m searchOp k res t0  }}}.
  Proof.
    iIntros "%k_in_KS #HInv #HUpd #Thd". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures.
    wp_apply traverse_spec; try done.
    iIntros (p c s) "(#Hpast & %)".
    destruct H as [FP_p [FP_c [Unmarked_p [k_in_ins_p 
      [k_in_outs_p [Unmarked_c k_in_ks_c]]]]]].
    wp_pures.
    awp_apply (inContents_spec); try done.
    iInv "HInv" as (M0 T0 s0) "(>CSS & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(Hglob & Res & %PT0 & %Trans_M0)". 
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Res" as "((Node_c & Node_crest) & Res_rest)".
    iAaccIntro with "Node_c".
    { iIntros "Node". iModIntro. iFrame "Hpost". 
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Res_rest". iFrame. }
    iIntros (res) "(Node_c & Hres)". iDestruct "Hres" as %Hres.
    iSpecialize ("Hpost" $! res).

    iAssert (past_state γ_m t0 s)%I as "#Hpast2". { done. }
    iDestruct "Hpast2" as (t)"(%t0_le_t & #Hist_s)".
    iAssert (⌜t ∈ dom M0⌝)%I as %t_in_M0.
    { admit. }
    apply PT0 in t_in_M0.
    iAssert (⌜M0 !!! t = s⌝)%I as %M0_t_s.
    { admit. } rewrite M0_t_s in t_in_M0. 
    destruct t_in_M0 as [Ins_r [Out_r [Mark_r Hbig_star]]].
    pose proof Hbig_star c FP_c as H'.
    assert (PC s c = PC s0 c) as PC_c.
    { admit. }

    iAssert (⌜seq_spec searchOp (Cont s c) (Cont s c) res k⌝)%I as %Seq_spec_c.
    { iPureIntro. 
      unfold seq_spec. split; try done. destruct res; 
      unfold Cont; destruct (decide (Mark s c)); try done; rewrite PC_c.
      - by apply Hres.
      - intros ?. by apply Hres. }
    iAssert (⌜Cont s c ⊆ keyset (FI s c)⌝)%I as %cc_sub_ksc.
    { iPureIntro. by destruct H' as [? [? _]]. }
    iAssert (⌜seq_spec searchOp (abs s) (abs s) res k⌝)%I as %Seq_spec.
    { iPureIntro. unfold seq_spec. split; try done. destruct res.
      - assert (k ∈ Cont s c) as H''.
        { unfold Cont. rewrite decide_False; try done.
          rewrite PC_c.
          by apply Hres. }
        assert (Cont s c ⊆ abs s) as H'''.
        { admit. }
        clear -H'' H'''; set_solver.
      - (* Need this property from all snapshots *)
        assert (∀ s n k, k ∈ keyset (FI s n) → (k ∈ (Cont s n) ↔ k ∈ abs s)).
        { admit. }
        admit. }
    iAssert (past_lin_witness γ_m searchOp k res t0) as "Witn".
    { unfold past_lin_witness, updater_thread. iExists s.
      iFrame "#". by iPureIntro. }

    iModIntro. iSplitR "Hpost"; last first.
    { iApply "Hpost"; try done. } 
    { iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Res_rest". iFrame. }
  Admitted.      
    
End skiplist_v0_search.