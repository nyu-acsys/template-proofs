From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants fancy_updates.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
From diaframe.heap_lang Require Import proof_automation atomic_specs wp_auto_lob.
Require Export one_shot_proph typed_proph hindsight_defs.

Module Type HINDSIGHT_PROOF.
  Declare Module DS : DATA_STRUCTURE.
  Declare Module DEFS : HINDSIGHT_DEFS.
  Import DEFS DS.

  Definition dsOp' : val :=
    λ: "OP" "r",     
      let: "t_id" := NewProph in
      let: "p" := NewProph in
      let: "v" := dsOp "OP" "r" in
      resolve_proph: "p" to: "v";;
  
      "v".
        
  (** Proofs *)

  Lemma dsOp'_spec N γ_s γ_t γ_m γ_td γ_ght template_inv op r :
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
              <<< ∀∀ a, dsRep γ_s a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N)
              <<< ∃∃ a' res, dsRep γ_s a' ∗ ⌜seq_spec op a a' res⌝, RET #res >>>.
  Proof.


  Parameter dsOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght template_inv op r γ_sy t_id t0,
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     dsOp (Op_to_val op) #r
                {{{ res, RET #res; past_lin_witness γ_m op res t0  }}}.

