From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Export skiplist_v0 skiplist_v0_search.

Section skiplist_v0_search.

  Context {Σ} `{!heapGS Σ, !dsG Σ, !skG Σ}.
  Notation iProp := (iProp Σ).
  
  (* Proofs *)

  Lemma insertOp_spec N γ_s γ_t γ_m γ_td γ_ght r (k: K) γ_sy t_id t0:
        ⌜k ∈ KS⌝ -∗
          css_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv r) -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     insert r #k
                {{{ res, RET #res; past_lin_witness γ_m insertOp k res t0  }}}.
  Proof.
    iIntros "%k_in_KS #HInv #Thd". iLöb as "IH".
    iIntros "#Tr_inv" (Φ) "!# _ Hpost".
    wp_lam. wp_apply traverse_spec; try done.
    iIntros (p c s) "(#Hpast & %)".
    destruct H as [FP_p [FP_c [Unmarked_p [k_in_ins_p 
      [k_in_outs_p [Unmarked_c k_in_ks_c]]]]]].
    wp_pures.
    awp_apply (inContents_spec); try done.
    iInv "HInv" as (M0 T0 s0) "(>CSS & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(PT & %Trans_M0 & %Trans_s0 & Res)". 
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
    destruct res.
    - destruct (decide (k ∈ pcc)) as [Hres' | Hres']; last first.
      { exfalso. apply Hres'. by apply Hres. }
      assert (∀ s n k, k ∈ keyset (intf s n) → (k ∈ (Cont s n) ↔ k ∈ abs s)) as Hkeyset.
      { admit. }
      iAssert (⌜k ∈ abs s⌝)%I as "%".
      { assert (k ∈ Cont s c) as k_in_c.
        { unfold Cont. destruct (decide (mark s c)); try done.
          admit. }
        iPureIntro.
        pose proof Hkeyset s c k k_in_ks_c as Hkeyset.
        by apply Hkeyset. }
      iAssert (past_lin_witness γ_m insertOp k false t0)%I as "HpastW".
      { unfold past_lin_witness, updater_thread.
        iExists s; iFrame "#".
        iPureIntro. simpl. split; try done. } 
      iModIntro. iSplitR "Hpost".
      iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame. iExists mc, Ic, pcc.
      iFrame "∗%". wp_pures.
      iModIntro. by iApply "Hpost".
    - iModIntro. iSplitR "Hpost".
      iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame. iExists mc, Ic, pcc.
      iFrame "∗%". wp_pures.
      wp_apply createNode_spec; try done.
      iIntros (e em Ie epc) "(Node_e & k_in_e & k_in_Ie_c)".
      wp_pures.
      awp_apply (try_constraint_insert_spec k).
      iInv "HInv" as (M1 T1 s1) "(>CSS & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p1.
      { admit. }
      iDestruct "Templ" as "(PT & %Trans_M1 & %Trans_s1 & Res)".
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Res" as "(NodeFull_p & Res_rest)".
      iDestruct "NodeFull_p" as (mp Ip pcp) "(Node & Node_rest)".
      iAaccIntro with "Node".
      { iIntros "Node". admit. }
      iIntros (succ Ip')"(Node_p & Hif)".
      destruct succ; last first.
      + iModIntro. iSplitR "Hpost".
        iNext. iExists M1, T1, s1.
        iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
        iFrame. iExists mp, Ip, pcp.
        iDestruct "Hif" as "(_ & %)". subst Ip'. 
        iFrame "∗%".
        wp_pures. iApply "IH"; try done.
      + 
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1.
          iFrame "∗%". admit. }
        wp_pures. by iApply "Hpost". 
      

      
    
    
    
    
  Admitted.    
    
  
