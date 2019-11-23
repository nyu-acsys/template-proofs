From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Export auth agree.


(* ---------- Flow Interface encoding and camera definitions ---------- *)

(* This section is proved in the appendix *)

Definition key := nat.                                             (* put this in the templates file *)

Definition Node := nat.

Definition flowdom := nat.

Record flowintT :=
  {
    inf : gmap Node flowdom;
    out : gmap Node flowdom;
    dom : gset Node;
  }.
  
Canonical Structure flowintRAC := leibnizO flowintT.

Instance flowintRAop : Op flowintT.
Proof. Admitted.

Instance flowintRAvalid : Valid flowintT.
Proof. Admitted.

Instance flowintRAcore : PCore flowintT.
Proof. Admitted.

Instance flowintRAunit : cmra.Unit flowintT.
Proof. Admitted.

Lemma intComp_assoc (I1 I2 I3: flowintT) : I1 ⋅ I2 ⋅ I3 ≡ I1 ⋅ (I2 ⋅ I3).
Proof. Admitted.

Definition flowintRA_mixin : RAMixin flowintT.
Proof.
  split; try apply _; try done.
  - (* Core is unique? *)
    intros ? ? cx -> ?. exists cx. done.
  - (* Associativity *)
    intros I1 I2 I3. try (apply leibniz_equiv). try auto.
    (* HELP. Can't I just use intComp_assoc here? *)
Admitted.


Canonical Structure flowintRA := discreteR flowintT flowintRA_mixin.

Instance flowintRA_cmra_discrete : CmraDiscrete flowintRA.
Proof. apply discrete_cmra_discrete. Qed.

Instance flowintRA_cmra_total : CmraTotal flowintRA.
Proof. Admitted.

Lemma flowint_ucmra_mixin : UcmraMixin flowintT.
Proof. Admitted.

Canonical Structure flowintUR : ucmraT := UcmraT flowintT flowint_ucmra_mixin.

(* Sid: let's rename this to intLeq to be consistent with Grasshopper *)
Parameter contextualLeq : flowintUR → flowintUR → Prop.

(* This is the rule AUTH-FI-UPD in the paper *)
Definition flowint_update_P (I I_n I_n': flowintUR) (x : authR flowintUR) : Prop :=
  match (auth_auth_proj x) with
  | Some (q, z) => ∃ I', (z = to_agree(I')) ∧ q = 1%Qp ∧ (I_n' = auth_frag_proj x) 
                        ∧ contextualLeq I I' ∧ ∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o
  | _ => False
  end.

(* Directly follows from definition of contextual extension *)
Hypothesis contextualLeq_impl_fp : ∀ I I', contextualLeq I I' → dom I = dom I'.

Hypothesis flowint_update : ∀ I I_n I_n',
  contextualLeq I_n I_n' → (● I ⋅ ◯ I_n) ~~>: (flowint_update_P I I_n I_n').

Hypothesis flowint_comp_fp : ∀ I1 I2 I, I = I1 ⋅ I2 → dom I = dom I1 ∪ dom I2.
