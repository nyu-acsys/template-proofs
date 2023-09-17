(* Herlihy Skiplist with a single level : Delete *)

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
Require Export skiplist_v0.

Module SKIPLIST0_SPEC_DELETE.
  Module DEFS := HINDSIGHT_DEFS SKIPLIST0.
  Import SKIPLIST0 DEFS.

  Parameter inContents_spec : ∀ (k: nat) (n: Node),
     ⊢ (<<< ∀∀ m es pc, node n m es pc >>>
           inContents #n #k @ ⊤
       <<< ∃∃ (v: bool),
              node n m es pc ∗ ⌜v ↔ k ∈ pc⌝,
              RET #v >>>)%I.

  Parameter try_constraint_delete_spec : ∀ (k: nat) (curr: Node),
     ⊢ (<<< ∀∀ m es pc, node curr m es pc >>>
           try_constraint #curr @ ⊤
       <<< ∃∃ (success: bool) m',
              node curr m' es pc
            ∗ (match success with true => ⌜m = false⌝ ∗ ⌜m' = true⌝ 
                                | false => ⌜m' = m⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.


  Lemma traverse_spec N γ_t γ_s γ_m γ_td γ_ght r γ_sy t_id t0 
    (k: nat) :
    ⌜k ∈ KS⌝ -∗
      main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
       thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ True }}}
           traverse r #k
        {{{ (p c: Node) s, RET (#p, #c); 
              past_state γ_m t0 s
            ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
            ∗ ⌜¬ Mark s p⌝
            ∗ ⌜k ∈ inset nat (FI s p) p⌝
            ∗ ⌜k ∈ outset nat (FI s p) c⌝
            ∗ ⌜¬ Mark s c⌝
            ∗ ⌜k ∈ keyset (FI s c)⌝ }}}.
  Proof.
  Admitted.
  
  Lemma deleteOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght (r: Node) 
                      γ_sy t_id t0 (k: nat),
          main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     delete #r #k
                {{{ res, RET #res; 
                    past_lin_witness γ_m (deleteOp k) res t0 }}}.
  Proof.
    iIntros (N γ_s γ_t γ_m γ_td γ_ght r γ_sy t_id t0 k)"#HInv #HUpd #Thd". 
    iIntros (Φ) "!# _ Hpost".
    assert (k ∈ KS) as k_in_KS.
    { admit. }
    wp_lam. wp_pures. wp_apply traverse_spec; try done. 
    iIntros (p c s) "(#Hpast & %)".
    destruct H as [FP_p [FP_c [Unmarked_p [k_in_ins_p 
      [k_in_outs_p [Unmarked_c k_in_ks_c]]]]]].
    wp_pures.
    awp_apply (inContents_spec); try done.
    iInv "HInv" as (M0 T0 s0) "(>CSS & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(Hglob & Res & %PT0 & %Trans_M0)".
    set γ_I := skiplist_v0.SKIPLIST0.γ_I.
    set γ_fp := skiplist_v0.SKIPLIST0.γ_fp.
    set γ_ks := skiplist_v0.SKIPLIST0.γ_ks.
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
    iIntros (res) "(Node_c & Hres)". 
    iDestruct "Hres" as %Hres.
    destruct res; last first.
    - destruct (decide (k ∈ PC s0 c)) as [Hres' | Hres'].
      { exfalso. by apply Hres. }
      assert (∀ s n k, k ∈ keyset (FI s n) → (k ∈ (Cont s n) ↔ k ∈ abs s)) 
        as Hkeyset.
      { admit. }
      iAssert (⌜k ∉ abs s⌝)%I as "%k_notin_s".
      { assert (k ∉ Cont s c) as k_notin_c.
        { unfold Cont. destruct (decide (Mark s c)); try done.
          admit. }
        iPureIntro.
        pose proof Hkeyset s c k k_in_ks_c as Hkeyset.
        intros H'. apply Hkeyset in H'.
        try done. }
      iAssert (past_lin_witness γ_m (deleteOp k) false t0)%I as "HpastW".
      { unfold past_lin_witness, updater_thread.
        iExists s; iFrame "#".
        iPureIntro. simpl. split; try done.
        clear -k_notin_s; set_solver. } 
      iModIntro. iSplitR "Hpost".
      iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame. wp_pures.
      iModIntro. by iApply "Hpost".
    - iModIntro. iSplitR "Hpost".
      iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame. clear γ_I γ_fp γ_ks.
      wp_pures.
      awp_apply try_constraint_delete_spec; try done.
      iInv "HInv" as (M1 T1 s1) "(>CSS & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
      { admit. }
      iDestruct "Templ" as "(Hglob & Res & %PT1 & %Trans_M1)".
      set γ_I := skiplist_v0.SKIPLIST0.γ_I.
      set γ_fp := skiplist_v0.SKIPLIST0.γ_fp.
      set γ_ks := skiplist_v0.SKIPLIST0.γ_ks.
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
      iDestruct "Res" as "((Node_c & Node_crest) & Res_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node_c". iModIntro. iFrame. 
        iNext; iExists M1, T1, s1.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto. 
        iFrame "Res_rest". iFrame. }
      iIntros (succ m') "(Node_c & Hsucc)".
      destruct succ; last first.
      + iAssert (past_lin_witness γ_m (deleteOp k) false t0)%I as "HpastW".
        { (* interpolation *) admit. }
        iDestruct "Hsucc" as "%H'".
        iModIntro. iSplitR "Hpost".
        iNext. iExists M1, T1, s1.
        iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
        iFrame. rewrite H'. try done. wp_pures.
        iModIntro. by iApply "Hpost".
      + iDestruct "Hsucc" as "(%Mark_s_c & ->)".
        
          
         
      
  Admitted.    
  
  
  
  
  
End skiplist_v0_delete.