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

  
  Lemma searchOp_spec N γ_s γ_t γ_m γ_td γ_ght r (k: K) γ_sy t_id t0:
        ⌜k ∈ KS⌝ -∗
          css_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv r) -∗
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
    iDestruct "Templ" as "(PT & %Trans_M1 & %Trans_s1 & Res)". 
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Res" as "(NodeFull_c & Res_rest)".
    iDestruct "NodeFull_c" as (mc Ic pcc) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "Hpost". 
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Res_rest".
      iExists mc, Ic, pcc. iFrame. }
    iIntros (res) "(Node & Hres)". iDestruct "Hres" as %Hres.
    iSpecialize ("Hpost" $! res).

    iAssert (past_state γ_m t0 s)%I as "#Hpast2". { done. }
    iDestruct "Hpast2" as (t)"(%t0_le_t & #Hist_s)".
    iAssert (⌜t ∈ dom M0⌝)%I as %t_in_M0.
    { admit. }

    rewrite (big_sepS_delete _ (dom M0) t); last by eauto.
    iDestruct "PT" as "(Tick_t & PT_rest)".
    iAssert (⌜M0 !!! t = s⌝)%I as %M0_t_s.
    { admit. } iEval (rewrite M0_t_s) in "Tick_t". 
    iDestruct "Tick_t" as "(HI & HKS & Ins_r & Out_r & Mark_r & Hbig_star)".
    rewrite (big_sepS_delete _ (FP s) c); last by eauto.
    iDestruct "Hbig_star" as "(Node_local & Hbig_star_rest)".
    iDestruct "Node_local" as "(HIc & Hksc & Hpurec)".
    iAssert (⌜pcc = PC s c⌝)%I as %->.
    { (* interpolation *) admit. }
    iAssert (⌜seq_spec searchOp (Cont s c) (Cont s c) res k⌝)%I as %Seq_spec_c.
    { iPureIntro. unfold seq_spec. split; try done. destruct res; 
      unfold Cont; destruct (decide (mark s c)); try done.
      - by apply Hres.
      - intros ?. by apply Hres. }
    iAssert (⌜Cont s c ⊆ keyset (intf s c)⌝)%I as %cc_sub_ksc.
    { by iDestruct "Hpurec" as "(_ & % & _)". }
    iAssert (⌜seq_spec searchOp (abs s) (abs s) res k⌝)%I as %Seq_spec.
    { iPureIntro. unfold seq_spec. split; try done. destruct res.
      - assert (k ∈ Cont s c) as H'.
        { unfold Cont. rewrite decide_False; try done.
          by apply Hres. }
        assert (Cont s c ⊆ abs s) as H''.
        { admit. }
        clear -H' H''; set_solver.
      - (* Need this property from all snapshots *)
        assert (∀ s n k, k ∈ keyset (intf s n) → (k ∈ (Cont s n) ↔ k ∈ abs s)).
        { admit. }
        admit. }
(*        
    iMod (ghost_update_keyset (γ_ks s) searchOp k (Cont s c) (Cont s c) res 
      (keyset (intf s c)) (abs s)
      with "[$HKS $Hksc]") as (C') "(%Seq_spec & HKS & Hksc)".
    { iPureIntro; repeat (split; try done). }
    iAssert (⌜C' = abs s⌝)%I as %->.
    { by destruct Seq_spec as [? _]. }
*)    
    iAssert (past_lin_witness γ_m searchOp k res t0) as "Witn".
    { unfold past_lin_witness, updater_thread. iExists s.
      iFrame "#". by iPureIntro. }

    iModIntro. iSplitR "Hpost"; last first.
    { iApply "Hpost"; try done. } 
    { iNext. iExists M0, T0, s0.
      iFrame "CSS Hist Help %".
      iSplitR "Node Node_rest Res_rest".
      rewrite (big_sepS_delete _ (dom M0) t); last by eauto.
      iFrame "PT_rest". iEval (rewrite M0_t_s). iFrame "HI HKS".
      rewrite (big_sepS_delete _ (FP s) c); last by eauto.
      iFrame"Hbig_star_rest". iFrame.
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Res_rest". iExists mc, Ic, (PC s c). iFrame. }
  Admitted.      
    
End skiplist_v0_search.