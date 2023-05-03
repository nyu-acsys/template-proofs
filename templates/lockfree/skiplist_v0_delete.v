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
  Import DEFS SKIPLIST0.

  Parameter inContents_spec : ∀ (k: nat) (n: Node),
     ⊢ (<<< ∀∀ m es pc, node n m es pc >>>
           inContents #n #k @ ⊤
       <<< ∃∃ (v: bool),
              node n m es pc ∗ ⌜v ↔ k ∈ pc⌝,
              RET #v >>>)%I.


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
                    DEFS.past_lin_witness γ_m (deleteOp k) res t0 }}}.
  Proof.
    iIntros (N γ_s γ_t γ_m γ_td γ_ght r γ_sy t_id t0 k)"#HInv #HUpd #Thd". 
    iIntros (Φ) "!# _ Hpost".
    assert (k ∈ KS) as k_in_KS.
    { admit. }
    wp_lam. wp_pures. wp_apply traverse_spec; try done. 
    iIntros (p c s) "(#Hpast & %)".
    destruct H as [FP_p [FP_c [Unmarked_p [k_in_ins_p 
      [k_in_outs_p [Unmarked_c k_in_ks_c]]]]]].
    wp_pures. Locate inContents_spec.
    awp_apply (inContents_spec); try done.
    iInv "HInv" as (M0 T0 s0) "(>CSS & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(Hglob & Res & %PT0 & %Trans_M0)".
      
  Admitted.    
  
  
  
  
  
End skiplist_v0_delete.