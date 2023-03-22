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
    destruct res.
    
    
    
    
  Admitted.    
    
  
