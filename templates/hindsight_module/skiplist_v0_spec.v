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
(* From diaframe.heap_lang Require Import proof_automation atomic_specs wp_auto_lob. *)
Require Export skiplist_v0.


Module SKIPLIST_SPEC : HINDSIGHT_SPEC SEARCH_STRUCTURE SKIPLIST0.
  Module DEFS := HINDSIGHT_DEFS SEARCH_STRUCTURE SKIPLIST0.
  Import SEARCH_STRUCTURE SKIPLIST0 DEFS.
  
  Lemma dsOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght op (r: Node) γ_sy t_id t0,
          main_inv N γ_t γ_s γ_m γ_td γ_ght -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     dsOp (Op_to_val op) #r
                {{{ res, RET #res; past_lin_witness γ_m op res t0  }}}.
  Proof.
    iIntros (N γ_s γ_t γ_m γ_td γ_ght op r γ_sy t_id t0) "HInv HUpd Thd_vars".
    unfold dsOp. wp_pures.
  Admitted.

End SKIPLIST_SPEC. 
