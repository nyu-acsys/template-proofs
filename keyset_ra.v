Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset big_op.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "All".
Require Export flows.

Section productRA.

  Inductive prodT := 
    prod : gset key*gset key → prodT
  | prodTop : prodT
  | prodBot : prodT.

  Canonical Structure prodRAC := leibnizO prodT.

  Instance prodOp : Op prodT :=
    λ p1 p2,
    match p1 with 
    | prod (K1, C1) => match p2 with 
                    | prod (K2, C2) => if decide (K1 ## K2) then 
                                (if decide (C1 ## C2) then (prod (K1 ∪ K2, C1 ∪ C2)) else prodTop)
                                            else prodTop
                    | prodTop => prodTop
                    | prodBot => p1 end
    | prodTop => prodTop
    | prodBot => p2 end.                     

  Instance prodValid : Valid prodT :=
    λ p, match p with
         | prod (K, C) => C ⊆ K
         | prodBot => True
         | prodTop => False end.

  Instance prodCore : PCore prodT :=
    λ p, match p with
         | prod (K, C) => Some (prod (∅, ∅))
         | _ => Some (prodBot) end. 

  Instance prodUnit : cmra.Unit prodT := prodBot.
   
  Definition prodRA_mixin : RAMixin prodT.
  Proof.
    split; try apply _; try done.
    unfold valid, op, prodOp, prodValid. intros ? ? cx -> ?; exists cx; done.
    - unfold op, prodOp. intros [] [] []; try (simpl; done). case_eq p. intros g g0 Hp. 
      case_eq p0. intros g1 g2 Hp0. case_eq p1. intros g3 g4 Hp1. destruct (decide (g1 ## g3)).
      destruct (decide (g2 ## g4)). destruct (decide (g ## g1 ∪ g3)). destruct (decide (g0 ## g2 ∪ g4)).
      destruct (decide (g ## g1)). destruct (decide (g0 ## g2)). destruct (decide (g ∪ g1 ## g3)).
      destruct (decide (g0 ∪ g2 ## g4)). assert (g ∪ (g1 ∪ g3) = g ∪ g1 ∪ g3). { set_solver. }
  Admitted.

  Canonical Structure prodRA := discreteR prodT prodRA_mixin.

  Instance prodRA_cmra_discrete : CmraDiscrete prodRA.
  Proof. apply discrete_cmra_discrete. Qed.

  Instance prodRA_cmra_total : CmraTotal prodRA.
  Proof. unfold CmraTotal. intros x. case_eq x; try eauto.
         intros. unfold pcore. rewrite /(cmra_pcore prodRA) /=.
         case_eq p; try eauto. Qed.

  Lemma prod_ucmra_mixin : UcmraMixin prodT.
  Proof. split; apply _ || done. Qed.

  Canonical Structure prodUR : ucmraT := UcmraT prodT prod_ucmra_mixin.

End productRA.