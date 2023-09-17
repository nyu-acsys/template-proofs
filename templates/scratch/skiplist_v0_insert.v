From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Export skiplist_v0 skiplist_v0_traverse.

Section skiplist_v0_search.

  Context {Σ} `{!heapGS Σ, !dsG Σ, !skG Σ}.
  Notation iProp := (iProp Σ).
  
  (* Proofs *)

  Lemma insertOp_spec N γ_s γ_t γ_m γ_td γ_ght γ_I γ_fp γ_ks r (k: K) γ_sy t_id t0:
        ⌜k ∈ KS⌝ -∗
          css_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv γ_I γ_fp γ_ks r) -∗
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
    destruct res.
    - destruct (decide (k ∈ PC s0 c)) as [Hres' | Hres']; last first.
      { exfalso. apply Hres'. by apply Hres. }
      assert (∀ s n k, k ∈ keyset (FI s n) → (k ∈ (Cont s n) ↔ k ∈ abs s)) as Hkeyset.
      { admit. }
      iAssert (⌜k ∈ abs s⌝)%I as "%".
      { assert (k ∈ Cont s c) as k_in_c.
        { unfold Cont. destruct (decide (Mark s c)); try done.
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
      iFrame. wp_pures.
      iModIntro. by iApply "Hpost".
    - iModIntro. iSplitR "Hpost".
      iNext. iExists M0, T0, s0.
      iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame. wp_pures.
      wp_apply createNode_spec; try done.
      iIntros (e es) "(Node_e & k_in_Ie_c)".
      wp_pures.
      awp_apply (try_constraint_insert_spec k).
      iInv "HInv" as (M1 T1 s1) "(>CSS & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p1.
      { admit. }
      iDestruct "Templ" as "(Hglob & Res & %PT1 & %Trans_M1)". 
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Res" as "((Node_p & Node_prest) & Res_rest)".
      iAaccIntro with "Node_p".
      { iIntros "Node_p". iModIntro. iFrame. 
        iNext; iExists M1, T1, s1.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto. 
        iFrame "Res_rest". iFrame. }
      iIntros (succ Ip')"(Node_p & Hif)".
      destruct succ; last first.
      + iModIntro. iSplitR "Hpost".
        iNext. iExists M1, T1, s1.
        iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
        iFrame.
        iDestruct "Hif" as "(_ & %)". subst Ip'. 
        iFrame "∗%".
        wp_pures. iApply "IH"; try done.
      + 
        set (s1' := 0).
        iAssert (⌜c ∈ FP s1 ∖ {[p]}⌝)%I as %FP_c_p.
        { admit. }
        rewrite (big_sepS_delete _ (FP s1 ∖ {[p]}) c); last by eauto.
        iDestruct "Res_rest" as "((Node_c & Node_crest) & Res_rest)".
        iDestruct "Node_prest" as "(HI_p & Hks_p & %Hpure_p)".
        iDestruct "Node_crest" as "(HI_c & Hks_c & %Hpure_c)".
        
        iAssert (own γ_I (◯ (FI s1 p ⋅ FI s1 c)))%I with "[HI_p HI_c]" as "HI_pc".
        { admit. }
        assert (FI s1 p ⋅ FI s1 c = FI s1' p ⋅ FI s1' e ⋅ FI s1' c) as flow_upd.
        { admit. }
        iEval (rewrite flow_upd) in "HI_pc".
        iAssert (own γ_I (◯ FI s1' p) ∗ own γ_I (◯ FI s1' e) ∗ own γ_I (◯ FI s1' c))%I 
          with "[HI_pc]" as "(HI_p & HI_e & HI_c)".
        { admit. }
        
        iAssert (own γ_ks (◯ prod (keyset (FI s1 p) ∪ keyset (FI s1 c), Cont s1 p ∪ Cont s1 c)))
          with "[Hks_p Hks_c]" as "Hks_pc".
        { admit. }
        
        assert (keyset (FI s1 p) ∪ keyset (FI s1 c) = 
                  keyset (FI s1' p) ∪ keyset (FI s1' e) ∪ keyset (FI s1' c)) as Keyset_upd.
        { admit. }
        assert (k ∈ keyset (FI s1' e)) as k_in_kse.
        { admit. }
        
        assert (Cont s1 p ∪ Cont s1 c ∪ {[k]} = Cont s1' p ∪ Cont s1' c) as Cont_upd.
        { admit. }
        
        iAssert (own γ_ks (◯ prod (keyset (FI s1 p) ∪ keyset (FI s1 c), Cont s1 p ∪ Cont s1 c ∪ {[k]})))
          with "[Hks_pc]" as "Hks_pc".
        { admit. }
        
        iAssert (own γ_ks (◯ prod (keyset (FI s1' p), Cont s1' p)) ∗
                    own γ_ks (◯ prod (keyset (FI s1' e), Cont s1' e)) ∗
                      own γ_ks (◯ prod (keyset (FI s1' c), Cont s1' c)))%I
          with "[Hks_pc]" as "(Hks_p & Hks_e & Hks_c)".
        { admit. }
        
        assert (node_inv_pure s1' e) as Hpure_e.
        { admit. }
        
        iDestruct "Hglob" as "(HI & HFP & HKS)".
        
        iAssert (own γ_I (● GFI s1'))%I with "[HI]" as "HI".
        { admit. }

        assert (FP s1' = FP s1 ∪ {[e]}) as FP_s1'.
        { admit. }
        assert (abs s1' = abs s1 ∪ {[k]}) as abs_s1'.
        { admit. }

        iAssert (own γ_fp (● FP s1'))%I with "[HFP]" as "HFP".
        { admit. }
        
        iAssert (own γ_ks (● prod (KS, abs s1')))%I with "[HKS]" as "HKS".
        { admit. }
        
        
        
        
        
        
        
                      
        
        

        iDestruct "HI_pc" as "(HI_p & HI_e)". & HI_c)". 
        
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1.
          iFrame "∗%". admit. }
        wp_pures. by iApply "Hpost". 
      

      
    
    
    
    
  Admitted.    
    
  
