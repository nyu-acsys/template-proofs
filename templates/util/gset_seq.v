From stdpp Require Import list.
From iris.algebra Require Import gset numbers.
From flows Require Import flows.

  (* Define gset representing [n1 ... n2]; and its properties *)

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

  Lemma mark_map (h: nat) :
    h > 0 →
      ∃ (m: gmap nat bool), (∀ i, i < h → m !! i = Some false) 
        ∧ dom m = gset_seq 0 (h-1).
  Proof.
    intros Hz.
    Fixpoint f n (res: gmap nat bool) := 
      match n with S n' => f n' (<[n' := false]> res) | 0 => res end.
    set m := f h ∅.
    assert (∀ n res i, (i < n → f n res !! i = Some false) ∧ 
                  (¬ i < n → f n res !! i = res !! i)) as H'.
    { clear. induction n.
      - intros res i; split; first by lia. intros H'; by simpl.
      - intros res i. pose proof IHn (<[n:=false]> res) i as H''.
        split; intros Hi; simpl.
        + destruct (decide (i = n)) as [-> | Hin].
          { assert (¬ n < n) as H' by lia. 
            destruct H'' as [_ H'']. pose proof H'' H' as H''.
            rewrite H'' lookup_insert. done. }
          assert (i < n) as H'%H'' by lia. by rewrite H'.
        + assert (¬ i < n) as H'%H'' by lia. rewrite H'.
          rewrite lookup_insert_ne; try (done || lia). }
    exists m. split. apply H'. pose proof H' h ∅ as H'. 
    rewrite -/m in H'. apply set_eq_subseteq. split.
    intros j Hj. destruct (decide (j < h)) as [Hj' | Hj']. 
    rewrite elem_of_gset_seq. lia. apply H' in Hj'. 
    rewrite lookup_empty -not_elem_of_dom in Hj'. done.
    intros j Hj. rewrite elem_of_gset_seq in Hj. 
    assert (j < h) as H'' by lia. apply H' in H''.
    rewrite elem_of_dom H''. done.    
  Qed.

  Lemma next_map (h: nat) (ss : list Node) :
    h > 0 →  
      (∃ (nx: gmap nat Node), (∀ i, i < h → nx !! i = Some (ss !!! i))
        ∧ dom nx = gset_seq 0 (h-1)).
  Proof.
    intros Hz.
    Fixpoint f' (l: list Node) n (res: gmap nat Node) := 
        match n with S n' => f' l n' (<[n':= l !!! n']> res) | 0 => res end.
      set nx := f' ss h ∅.
      assert (∀ n res i, (i < n → f' ss n res !! i = Some (ss !!! i)) ∧ 
                    (¬ i < n → f' ss n res !! i = res !! i)) as H'.
      { clear. induction n.
        - intros res i; split; first by lia. intros H'; by simpl.
        - intros res i. pose proof IHn (<[n:=(ss !!! n)]> res) i as H''.
          split; intros Hi; simpl.
          + destruct (decide (i = n)) as [-> | Hin].
            { assert (¬ n < n) as H' by lia. 
              destruct H'' as [_ H'']. pose proof H'' H' as H''.
              rewrite H'' lookup_insert. done. }
            assert (i < n) as H'%H'' by lia. by rewrite H'.
          + assert (¬ i < n) as H'%H'' by lia. rewrite H'.
            rewrite lookup_insert_ne; try (done || lia). }
      exists nx. split. apply H'. pose proof H' h ∅ as H'. 
      rewrite -/nx in H'. apply set_eq_subseteq. split.
      intros j Hj. destruct (decide (j < h)) as [Hj' | Hj']. 
      rewrite elem_of_gset_seq. lia. apply H' in Hj'. 
      rewrite lookup_empty -not_elem_of_dom in Hj'. done.
      intros j Hj. rewrite elem_of_gset_seq in Hj. 
      assert (j < h) as H'' by lia. apply H' in H''.
      rewrite elem_of_dom H''. done.
  Qed.
