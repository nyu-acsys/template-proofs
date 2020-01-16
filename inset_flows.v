Set Default Proof Using "All".
Require Export flows ccm.

(** CCM of multisets over natural numbers *)
Definition int_multiset := nzmap Z nat.

Instance int_multiset_ccm : CCM int_multiset := lift_ccm Z nat.

Definition dom_ms (m : int_multiset) := dom (gset Z) m.

Canonical Structure inset_flowint_ur : ucmraT := flowintUR int_multiset.

Implicit Type I : inset_flowint_ur.

Definition inset I n := dom_ms (inf I n).

Definition outset I n := dom_ms (out I n).

Definition in_inset k I n := k ∈ dom_ms (inf I n).
  
Definition in_outset k I n := k ∈ dom_ms (out I n).

Definition keyset I n := dom_ms (inf I n) ∖ dom_ms (out I n).

Definition in_outsets k In := ∃ n, in_outset k In n.

Lemma keyset_def : ∀ k I_n n, k ∈ inset I_n n → ¬ in_outsets k I_n → k ∈ keyset I_n n.
Proof.
  intros.
  unfold keyset.
  unfold inset in H.
  unfold in_outsets in H0.
  rewrite elem_of_difference.
  naive_solver.
Qed.

Definition globalinv root I : Prop := ✓I ∧ (root ∈ domm I) ∧ (∀ k n, k ∉ outset I n) 
                                      ∧ ∀ n, ((n = root) → (∀ k, k ∈ inset I n))
                                             ∧ ((n ≠ root) → (∀ k, k ∉ inset I n)).  

Lemma flowint_step :
  ∀ I I1 I2 k n root, I = I1 ⋅ I2 → ✓I → k ∈ outset I1 n → globalinv root I → n ∈ domm I2.
Proof.
  intros.
  unfold globalinv in H2.
  destruct H2.
  destruct H3.
  destruct H4.
  (*assert (n inf I n = out I1 n + out I2 n)*)
  (* TODO: lemma_int_comp_unfold *)
Admitted.
