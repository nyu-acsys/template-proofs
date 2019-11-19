From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Export auth agree.


(* ---------- Flow Interface encoding and camera definitions ---------- *)

(* This section is proved in Grasshopper *)

Definition key := nat.

Definition node := nat.

Parameter flowdom: Set.

Record flowintT :=
  {
    inf : gmap node flowdom;
    out : gmap node flowdom;
    dom : gset node;
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

Definition flowintRA_mixin : RAMixin flowintT.
Proof.
  split; try apply _; try done.
Admitted.

Canonical Structure flowintRA := discreteR flowintT flowintRA_mixin.

Instance flowintRA_cmra_discrete : CmraDiscrete flowintRA.
Proof. apply discrete_cmra_discrete. Qed.

Instance flowintRA_cmra_total : CmraTotal flowintRA.
Proof. Admitted.

Lemma flowint_ucmra_mixin : UcmraMixin flowintT.
Proof. Admitted.
Canonical Structure flowintUR : ucmraT := UcmraT flowintT flowint_ucmra_mixin.

Parameter in_inset : key → flowintUR → node → Prop.
Parameter in_edgeset : key → flowintUR → node → node → Prop.
Parameter in_outset : key → flowintUR → node → Prop.
Parameter not_in_outset : key → flowintUR → node → Prop.
Parameter cont : node → gset key.
Parameter inreach : flowintUR → node → gset key.
Parameter intLeq : flowintUR → flowintUR → Prop.
Parameter is_empty_flowint : flowintUR → Prop.
Parameter globalint : flowintUR → Prop.           (* Need to discuss *)

(* ---------- Lemmas about flow interfaces proved in the appendix : ---------- *)

(* Directly follows from definition of composition *)
Lemma flowint_comp_fp (I1 I2 I : flowintUR) : I = I1 ⋅ I2 → dom I = dom I1 ∪ dom I2.
Proof. Admitted.

(* Directly follows from definition of contextual extension *)
Lemma intLeq_impl_fp I I' : intLeq I I' → dom I ⊆ dom I'.
Proof. Admitted.

(* This is the rule AUTH-FI-UPD in the paper *)
Definition flowint_update_P (I I_n I_n': flowintUR) (x : authR flowintUR) : Prop :=
  match (auth_auth_proj x) with
  | Some (q, z) => ∃ I', (z = to_agree(I')) ∧ q = 1%Qp ∧ (I_n' = auth_frag_proj x) 
                        ∧ intLeq I I' ∧ ∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o
  | _ => False
  end.


Lemma flowint_update I I_n I_n' :
  intLeq I_n I_n' → (● I ⋅ ◯ I_n) ~~>: (flowint_update_P I I_n I_n').
Proof. Admitted.

(* ---------- Proved in GRASShopper for each implementation: ---------- *)

Lemma inreach_impl_inset I_n n k:
  dom I_n = {[n]} → k ∈ inreach I_n n ∧ not_in_outset k I_n n ∧ ✓ I_n → in_inset k I_n n.
Proof. Admitted.

Lemma flowint_inset_step I1 n I2 n' k :
  dom I1 = {[n]} → dom I2 = {[n']} → ✓(I1 ⋅ I2)
  → in_inset k I1 n → in_edgeset k I1 n n' → in_inset k I2 n'.        (* in_edgeset interpretation? *)
Proof. Admitted.

Lemma flowint_inreach_step (I I1 I2: flowintUR) k n n':
  dom I1 = {[n]} → n' ∈ dom I2 → I = I1 ⋅ I2 → ✓(I)
  → k ∈ inreach I n → in_edgeset k I1 n n' → k ∈ inreach I n'.
Proof. Admitted.

Lemma flowint_proj I I_n n k :
  I_n ≼ I → ✓I → in_inset k I n → in_inset k I_n n.
Proof. Admitted.

Lemma flowint_step (I I1 I2: flowintUR) k n n':
  I = I1 ⋅ I2 → ✓I → n ∈ dom I1 → in_edgeset k I1 n n' → globalint I → n' ∈ dom I2.
Proof. Admitted.

(** Proved in multiset-flows.spl *)
Lemma flowint_step_gh (I I1 I2: flowintUR) k n:
  I = I1 ⋅ I2 → ✓I → in_outset k I1 n → globalint I → n ∈ dom I2.
Proof. Admitted.

