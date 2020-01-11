(* Add LoadPath "/home/nrp364/academics/templates-iris". *)
From iris.algebra Require Import gset.
From iris.proofmode Require Import tactics.
Set Default Proof Using "All".
Require Export flows.

Inductive prodT := 
  prod : gset key*gset key → prodT
| prodTop : prodT
| prodBot : prodT.

Canonical Structure prodRAC := leibnizO prodT.

Instance prodOp : Op prodT :=
  λ p1 p2,
  match p1, p2 with 
  | prod (K1, C1), prod (K2, C2) => if (decide(C1 ⊆ K1)) then  
                                       (if (decide(C2 ⊆ K2)) then
                                           (if (decide (K1 ## K2)) then
                                               (if (decide (C1 ## C2)) then (prod (K1 ∪ K2, C1 ∪ C2))
                                                else prodTop)
                                            else prodTop)
                                        else prodTop)
                                    else prodTop
  | prodTop, _ => prodTop
  | _, prodTop => prodTop
  | p1, prodBot => p1
  | prodBot, p2 => p2 end.
Instance prodValid : Valid prodT :=
λ p, match p with
       | prod (K, C) => C ⊆ K
       | prodTop => False
       | prodBot => True end.

Instance prodCore : PCore prodT :=
  λ p, Some prodBot.

Instance prodUnit : Unit prodT := prodBot.

Definition prodRA_mixin : RAMixin prodT.
Proof.
  split; try apply _; try done.
  - (* Core is unique? *)
    intros ? ? cx -> ?. exists cx. done.
  - unfold op, prodOp. intros [] [] []; try (simpl; done).
    case_eq p. intros g g0 Hp. case_eq p0. intros g1 g2 Hp0. case_eq p1. intros g3 g4 Hp1.
    destruct (decide (g2 ⊆ g1)). destruct (decide (g4 ⊆ g3)). destruct (decide (g1 ## g3)).
    destruct (decide (g2 ## g4)). destruct (decide (g0 ⊆ g)). destruct (decide (g2 ∪ g4 ⊆ g1 ∪ g3)).
    destruct (decide (g ## g1 ∪ g3)). destruct (decide (g0 ## g2 ∪ g4)).
    destruct (decide (g ## g1)). destruct (decide (g0 ## g2)). destruct (decide (g0 ∪ g2 ⊆ g ∪ g1)).
    destruct (decide (g ∪ g1 ## g3)). destruct (decide (g0 ∪ g2 ## g4)). apply leibniz_equiv_iff.
    assert (g ∪ (g1 ∪ g3) = g ∪ g1 ∪ g3). { set_solver. }
    assert (g0 ∪ (g2 ∪ g4) = g0 ∪ g2 ∪ g4). { set_solver. }
    rewrite H. rewrite H0. reflexivity.
    unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver.
    destruct (decide (g ## g1)). destruct (decide (g0 ## g2)). destruct (decide (g ∪ g1 ## g3)).
    destruct (decide (g0 ∪ g2 ## g4)). 
    unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver.
    destruct (decide (g0 ∪ g2 ⊆ g ∪ g1)); try done. done. done.
    destruct (decide (g ## g1)). destruct (decide (g0 ## g2)). destruct (decide (g0 ∪ g2 ⊆ g ∪ g1)).
    destruct (decide (g ∪ g1 ## g3)). destruct (decide (g0 ∪ g2 ## g4)).
    unfold not in n. exfalso. apply n. set_solver. done. done. done. done. done. 
    unfold not in n. exfalso. apply n. set_solver. done.
    unfold not in n. exfalso. apply n. set_solver.
    destruct (decide (g0 ⊆ g)). destruct (decide (g ## g1)); try done.
    destruct (decide (g0 ## g2)). destruct (decide (g0 ∪ g2 ⊆ g ∪ g1)). 
    destruct (decide (g ∪ g1 ## g3)). unfold not in n. exfalso. apply n. set_solver.
    done. done. done. done. destruct (decide (g0 ⊆ g)).
    destruct (decide (g ## g1)). destruct (decide (g0 ## g2)).
    destruct (decide (g0 ∪ g2 ⊆ g ∪ g1)). done. done. done. done. done.
    destruct (decide (g0 ⊆ g)). done. done.
    case_eq p. intros g g0 Hp. case_eq p0. intros g1 g2 Hp0. destruct (decide (g0 ⊆ g)).
    destruct (decide (g2 ⊆ g1)). destruct (decide (g ## g1)).
    destruct (decide (g0 ## g2)). done. done. done. done. done.
    case_eq p. intros g g0 Hp. case_eq p0. intros g1 g2 Hp0. destruct (decide (g0 ⊆ g)).
    destruct (decide (g2 ⊆ g1)). destruct (decide (g ## g1)).
    destruct (decide (g0 ## g2)). done. done. done. done. done.
    case_eq p; try done. case_eq p; try done. case_eq p; try done. case_eq p; try done.
    case_eq p; try done. case_eq p; try done. case_eq p. intros g g0 Hp. case_eq p0. intros g1 g2 Hp0.
    destruct (decide (g0 ⊆ g)). destruct (decide (g2 ⊆ g1)). destruct (decide (g ## g1)).
    destruct (decide (g0 ## g2)). done. done. done. done. done.
    case_eq p; try done. case_eq p; try done.
  - unfold op, prodOp. intros [] []. case_eq p. intros g g0 Hp. case_eq p0. intros g1 g2 Hp0.
    destruct (decide (g0 ⊆ g)); try done. destruct (decide (g2 ⊆ g1)); try done.
    destruct (decide (g ## g1)). destruct (decide (g0 ## g2)). destruct (decide (g1 ## g)).
    destruct (decide (g2 ## g0)). assert (g1 ∪ g = g ∪ g1 ∧ g2 ∪ g0 = g0 ∪ g2) as [H1 H2]. { set_solver. }
    rewrite H1; rewrite H2. done. unfold not in n. exfalso. apply n. done.      
    unfold not in n. exfalso. apply n. done. destruct (decide (g1 ## g)). destruct (decide (g2 ## g0)).
    unfold not in n. exfalso. apply n. done. done. done. destruct (decide (g1 ## g)).
    unfold not in n. exfalso. apply n. done. done. destruct (decide (g2 ⊆ g1)); try done.
    case_eq p; try done. case_eq p; try done. case_eq p; try done. done. done.
    case_eq p; try done. done. done.
  - unfold pcore, prodCore. intros x cx. intros Hx. inversion Hx.
    unfold op, prodOp. destruct x; try done.
  - unfold pcore, prodCore. intros x cx Hx. inversion Hx. done.
  - intros x y cx Hxy HS. inversion HS. exists prodBot. split; try done. exists prodBot; done.
  - unfold valid, prodValid. intros x y. destruct x. destruct p.
    destruct y. destruct p. unfold op, prodOp. destruct (decide (g0 ⊆ g)).
    destruct (decide (g2 ⊆ g1)). destruct (decide (g ## g1)). destruct (decide (g0 ## g2)).
    intros. done. intros; done. intros; done. intros; done. intros; done.
    unfold op, prodOp. intros; done. unfold op, prodOp. done. unfold op, prodOp. done.
    destruct y. destruct p. unfold op, prodOp. done. unfold op, prodOp. done. unfold op, prodOp. done.
Qed.

Canonical Structure keysetRA := discreteR prodT prodRA_mixin.

Instance prodRA_cmra_discrete : CmraDiscrete keysetRA.
Proof. apply discrete_cmra_discrete. Qed.

Lemma prod_ucmra_mixin : UcmraMixin prodT.
Proof.
  split; try apply _; try done. unfold LeftId. intros x. unfold ε, prodUnit.
  unfold op, prodOp. destruct x; try done.
Qed.    
    
Canonical Structure keysetUR : ucmraT := UcmraT prodT prod_ucmra_mixin.

Parameter KS : gset key.                                

Lemma auth_ks_included (a1 a2 b1 b2: gset key) : 
           ✓ prod (a1, b1) → ✓ prod (a2, b2) → prod (a1, b1) ≼ prod (a2, b2) 
              → (a1 = a2 ∧ b1 = b2) ∨ 
                  (∃ a0 b0, a2 = a1 ∪ a0 ∧ b2 = b1 ∪ b0 ∧ a1 ## a0 ∧ b1 ## b0 ∧ b1 ⊆ a1 ∧ b2 ⊆ a2 ∧ b0 ⊆ a0).
Proof.
  intros H1 H2 H. destruct H as [z H]. assert (✓ z). { apply (cmra_valid_op_r (prod (a1, b1))).
  rewrite <-H. done. } rewrite /(✓ prod (a1, b1)) /= in H1. rewrite /(✓ prod (a2, b2)) /= in H2.
  destruct z.
  - destruct p. rewrite /(✓ prod (g, g0)) /= in H0. rewrite /(⋅) /= in H.
    destruct (decide (b1 ⊆ a1)). destruct (decide (g0 ⊆ g)). destruct (decide (a1 ## g)).
    destruct (decide (b1 ## g0)). right. exists g, g0. set_solver. inversion H. inversion H.
    inversion H. inversion H.
  - rewrite /(✓ prodTop) /= in H0. exfalso. done.
  - rewrite /(⋅) /= in H. inversion H. left. done.
Qed.  

Lemma auth_ks_local_update_insert K1 C Cn k:
            ✓ prod (KS, C) ∧ ✓ prod (K1, Cn) ∧ k ∈ K1 ∧ k ∉ Cn ∧ k ∈ KS →
           (prod (KS, C), prod (K1, Cn)) ~l~> (prod (KS, C ∪ {[k]}), prod (K1, Cn ∪ {[k]})).
Proof.
  intros [H1 [H2 [H3 [H4 HKS]]]]. apply local_update_discrete. intros z.
  intros _. intros. split. rewrite /(✓ prod (KS, C ∪ {[k]})) /=. 
  rewrite /(cmra_valid keysetRA) /=. rewrite /(✓ prod (KS, C)) /= in H1.
  set_solver. rewrite /(opM) /= in H.
  destruct z. rewrite /(opM) /=. destruct c. destruct p. rewrite /(op) /= in H.
  rewrite /(cmra_op keysetRA) /= in H. destruct (decide (Cn ⊆ K1)).
  destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ## g0)).
  inversion H. rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. destruct (decide (Cn ∪ {[k]} ⊆ K1)).
  destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ∪ {[k]} ## g0)).
  assert (Cn ∪ g0 ∪ {[k]} = Cn ∪ {[k]} ∪ g0). { set_solver. } rewrite H0. rewrite H5. done.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
  rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
  rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. done.
  rewrite /(opM) /=. inversion H. done.
Qed.

Lemma auth_ks_local_update_delete K1 C Cn k:
            ✓ prod (KS, C) ∧ ✓ prod (K1, Cn) ∧ k ∈ K1 ∧ k ∈ Cn →
           (prod (KS, C), prod (K1, Cn)) ~l~> (prod (KS, C ∖ {[k]}), prod (K1, Cn ∖ {[k]})).
Proof.
  intros [H1 [H2 [H3 H4]]]. apply local_update_discrete. intros z.
  intros _. intros. split. rewrite /(✓ prod (KS, C ∖ {[k]})) /=. 
  rewrite /(cmra_valid keysetRA) /=. rewrite /(✓ prod (KS, C)) /= in H1.
  set_solver. rewrite /(opM) /= in H.
  destruct z. rewrite /(opM) /=. destruct c. destruct p. rewrite /(op) /= in H.
  rewrite /(cmra_op keysetRA) /= in H. destruct (decide (Cn ⊆ K1)).
  destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ## g0)).
  inversion H. rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. destruct (decide (Cn ∖ {[k]} ⊆ K1)).
  destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ∖ {[k]} ## g0)).
  assert (k ∉ g0). { set_solver. }
  assert ((Cn ∪ g0) ∖ {[k]} = Cn ∖ {[k]} ∪ g0). { set_solver. } rewrite H7. rewrite H5. done.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
  rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
  rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
  rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. done.
  rewrite /(opM) /=. inversion H. done.
Qed.


