From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
From flows Require Import node_module.

Module Type TRAVERSE.
  Declare Module NODE : NODE_IMPL.
  Export NODE.

  Parameter traverse_rec : heap_lang.val.

  Definition traverse : heap_lang.val :=
    λ: "h" "t" "k",
      let: "preds" := AllocN #L "h" in
      let: "succs" := AllocN #L "t" in
      traverse_rec "k" "preds" "succs" #(L-2)%nat.

End TRAVERSE.

