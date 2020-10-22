Require Import Coq.Numbers.NatInt.NZAddOrder.
From iris.algebra Require Import numbers.
(*From iris.algebra Require Export numbers. *)
Set Default Proof Using "All".
Require Export flows ccm.

Section KT_flows.

(*Definition K := Z. *)
Context `{Countable K}.

Definition KT : Type := (K * nat).

Definition KT_multiset := nzmap KT nat.

Global Instance KT_multiset_ccm : CCM KT_multiset := lift_ccm KT nat.

Definition dom_ms (m : KT_multiset) := dom (gset KT) m.

Definition inset_KT I n := dom (gset KT) (inf I n).

Definition outset_KT I n := dom_ms (out I n).

Definition out_KT I k := ∃ t n, (k, t) ∈ outset_KT I n.

Global Canonical Structure KT_flowint_ur : ucmraT := flowintUR KT_multiset.

End KT_flows.

Arguments KT_multiset _ {_ _} : assert.
Arguments KT_flowint_ur _ {_ _} : assert.
 
