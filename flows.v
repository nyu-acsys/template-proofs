From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.algebra Require Export auth agree.


(* ---------- Flow Interface encoding and camera definitions ---------- *)

(* This section is proved in the appendix *)

Definition key := nat.

Definition node := nat.

Definition flowdom := nat.

Record flowintT :=
  {
    Nds : gset node;
    Edf : gmap (node * node * flowdom) flowdom;
    inf : gmap node flowdom;
    outf : gmap node flowdom;
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

(* inset I n := { k | I.inf[n].ks[k] > 0 } *)
(* TODO in_inset k I n -> k ∈ inset I n *)
Parameter in_inset : key → flowintUR → node → Prop.

(* outset I n' := { k | I.out[n'].ks[k] > 0 } OR *)
(* outset I n' := { k | I.out[n'].ks[k] > 0 || I.out[n'].ir[k] > 0 } *)
(* TODO in_outset k I n n' -> k ∈ outset I n' *)
(* TODO not_in_outset k I n' -> k ∉ outset I n' *)
Parameter in_outset : key → flowintUR → node → node → Prop.
Parameter not_in_outset : key → flowintUR → node → Prop.

(* TODO remove this *)
Parameter cont : flowintUR → gset key.

(* inreach I n  := { k | I.inf[n].ks[k] > 0 || I.inf[n].ir[k] > 0 } *)
Parameter inreach : flowintUR → node → gset key.

(* TODO contextualLeq is just equality, unless decisiveOp returns more than one node. *)
Parameter contextualLeq : flowintUR → flowintUR → Prop.

(* TODO discuss when doing lock coupling. *)
Parameter is_empty_flowint : flowintUR → Prop.

Parameter globalint : flowintUR → Prop.


(* ---------- Lemmas about flow interfaces proved in GRASShopper : ---------- *)

(* Directly follows from definition of composition *)
Lemma flowint_comp_fp (I1 I2 I : flowintUR) : I = I1 ⋅ I2 → Nds I = Nds I1 ∪ Nds I2.
Proof. Admitted.

(* Directly follows from definition of contextual extension *)
Lemma contextualLeq_impl_fp I I' : contextualLeq I I' → Nds I = Nds I'.
Proof. Admitted.

(* This is the rule AUTH-FI-UPD in the paper *)
Definition flowint_update_P (I I_n I_n': flowintUR) (x : authR flowintUR) : Prop :=
  match (auth_auth_proj x) with
  | Some (q, z) => ∃ I', (z = to_agree(I')) ∧ q = 1%Qp ∧ (I_n' = auth_frag_proj x) 
                        ∧ contextualLeq I I' ∧ ∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o
  | _ => False
  end.


Lemma flowint_update I I_n I_n' :
  contextualLeq I_n I_n' → (● I ⋅ ◯ I_n) ~~>: (flowint_update_P I I_n I_n').
Proof. Admitted.

(* ---------- Proved in GRASShopper for each implementation: ---------- *)

Lemma inreach_impl_inset I_n n k:
  Nds I_n = {[n]} → k ∈ inreach I_n n ∧ not_in_outset k I_n n ∧ ✓ I_n → in_inset k I_n n.
Proof. Admitted.

Lemma flowint_inset_step I1 n I2 n' k :
  Nds I1 = {[n]} → Nds I2 = {[n']} → ✓(I1 ⋅ I2)
  → in_inset k I1 n → in_outset k I1 n n' → in_inset k I2 n'.        (* in_outset interpretation? *)
Proof. Admitted.

Lemma flowint_inreach_step (I I1 I2: flowintUR) k n n':
  Nds I1 = {[n]} → Nds I2 = {[n']} → ✓(I1 ⋅ I2)
  → k ∈ inreach I1 n → in_outset k I1 n n' → k ∈ inreach I2 n'.
Proof. Admitted.

Lemma flowint_proj I I_n n k :
  I_n ≼ I → ✓I → in_inset k I n → in_inset k I_n n.
Proof. Admitted.

Lemma flowint_step (I I1 I2: flowintUR) k n n':
  I = I1 ⋅ I2 → ✓I → n ∈ Nds I1 → in_outset k I1 n n' → globalint I → n' ∈ Nds I2.
Proof. Admitted.

