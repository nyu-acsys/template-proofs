From stdpp Require Import list.
From iris.algebra Require Import gset numbers.

Definition gset_seq i j : gset nat :=
  list_to_set (seq i (j + 1 - i)).

Lemma elem_of_gset_seq i j k :
  k ∈ gset_seq i j ↔ i ≤ k ≤ j.
Proof.
  intros; rewrite elem_of_list_to_set elem_of_seq; lia.
Qed.

Lemma gset_seq_eq T T' :
  gset_seq 0 T = gset_seq 0 T' → T = T'.
Proof.
  intros Heq. 
  assert (T ∈ gset_seq 0 T') as HT. 
  { rewrite -Heq elem_of_gset_seq. lia. }
  assert (T' ∈ gset_seq 0 T) as HT'. 
  { rewrite Heq elem_of_gset_seq. lia. }
  rewrite !elem_of_gset_seq in HT HT'. lia.
Qed.

Lemma gset_seq_union T :
gset_seq 0 (T+1) = gset_seq 0 T ∪ {[T+1]}.
Proof.
  apply set_eq_subseteq. split.
  all: intros x; rewrite elem_of_union !elem_of_gset_seq elem_of_singleton; lia.
Qed.

