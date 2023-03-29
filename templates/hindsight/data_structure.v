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
Require Export one_shot_proph typed_proph.

Module Type DATA_STRUCTURE.
  
  Parameter dsOp : val.
  Parameter Op : Type.
  Parameter Op_to_val : Op -> val.

  Parameter snapshotUR : ucmra.
  Definition snapshot := ucmra_car snapshotUR.

  Parameter absTUR : ucmra.
  Definition absT := ucmra_car absTUR.

  Parameter resT : Type.
  Parameter resT_to_base_lit : resT -> base_lit.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Parameter resT_from_val : val -> option resT.
  Parameter resT_to_val : resT -> val.
  Parameter resT_inj_prop : ∀ (r : resT), resT_from_val (resT_to_val r) = Some r.
  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.
  Parameter resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  
  Parameter seq_spec : Op -> absT -> absT -> resT -> Prop.
  Parameter abs : snapshot -> absT.
  Parameter updater_thread: Op -> resT -> bool.

  Parameter neg_seq_spec_dec : ∀ op c c' res, Decision (¬ seq_spec op c c' res).
  Parameter seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Parameter updater_thread_dec: ∀ op res b, Decision (updater_thread op res = b).  
  
  Parameter snapshotUR_discrete : CmraDiscrete snapshotUR.
  Parameter absTUR_discrete : CmraDiscrete absTUR.
  Parameter snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Parameter snapshot_inhabited : Inhabited snapshot.
  Parameter resT_inhabited : Inhabited resT.
  Parameter Op_inhabited : Inhabited Op.
  
End DATA_STRUCTURE.  
