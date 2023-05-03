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
Require Export skiplist_v0 hindsight_proof.


Module SKIPLIST_SPEC : HINDSIGHT_SPEC SKIPLIST0.
  Module DEFS := HINDSIGHT_DEFS SKIPLIST0.
  Import SKIPLIST0.
  
  Lemma searchOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght (r: Node) 
                      γ_sy t_id t0 (k: nat),
          DEFS.main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
            □ DEFS.update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              DEFS.thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     search #r #k
                {{{ res, RET #res; 
                    DEFS.past_lin_witness γ_m (searchOp k) res t0 }}}.
  Proof.
  Admitted.

  Lemma insertOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght (r: Node) 
                      γ_sy t_id t0 (k: nat),
          DEFS.main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
            □ DEFS.update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              DEFS.thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     insert #r #k
                {{{ res, RET #res; 
                    DEFS.past_lin_witness γ_m (insertOp k) res t0 }}}.
  Proof.
  Admitted.

  Lemma deleteOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght (r: Node) 
                      γ_sy t_id t0 (k: nat),
          DEFS.main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
            □ DEFS.update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              DEFS.thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     delete #r #k
                {{{ res, RET #res; 
                    DEFS.past_lin_witness γ_m (deleteOp k) res t0 }}}.
  Proof.
  Admitted.

  
  Lemma dsOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght op (r: Node) 
                      γ_sy t_id t0,
          DEFS.main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
            □ DEFS.update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              DEFS.thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     dsOp (Op_to_val op) #r
                {{{ res, RET #res; DEFS.past_lin_witness γ_m op res t0 }}}.
  Proof.
    iIntros (N γ_s γ_t γ_m γ_td γ_ght op r γ_sy t_id t0) "#HInv #HUpd #Thd_vars".
    unfold dsOp. iIntros (Φ) "!# _ Hpost". wp_lam. wp_pure.
    unfold Op_to_val; destruct op as [k|k|k].
    - wp_pures. wp_apply searchOp_spec; try done.
    - wp_pures. wp_apply insertOp_spec; try done.
    - wp_pures. wp_apply deleteOp_spec; try done.
  Qed.

End SKIPLIST_SPEC. 
