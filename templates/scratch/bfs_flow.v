Require Import Coq.Numbers.NatInt.NZAddOrder.
From Coq Require Import QArith Qcanon.
Set Default Proof Using "All".
Require Export flows ccm.
Require Import Coq.Setoids.Setoid.

(** Flow interface cameras and auxiliary lemmas for multiset flows *)

Section bfs_flow.

Context `{Countable K}.

(** CCM of finite multisets over a countable set K *)

Definition K_bfs := nzmap K Qc.

Global Instance K_bfs_ccm : CCM K_bfs := lift_ccm K Qc.

Global Canonical Structure bfs_flowint_ur : ucmra := flowintUR K_bfs.

Implicit Type I : bfs_flowint_ur.

(** Insets and outsets of flow interfaces *)

Definition bfs_inset I n := dom (inf I n).

Definition outset I n := dom (out I n).

Definition in_inset k I n := k ∈ dom (inf I n).

Definition in_outset k I n := k ∈ dom (out I n).

Definition in_outsets k In := ∃ n, in_outset k In n.
