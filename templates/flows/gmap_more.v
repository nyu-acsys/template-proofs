From stdpp Require Export gmap pmap.
From Coq Require Import PArith.
Require Import Coq.Setoids.Setoid.

(** Extend stdpp's gmap with a merge function where the merge operation 
  also depends on the key and not just the merged values. *)

Definition gmap_imerge `{Countable K} {A B C} 
  (f : K → option A → option B → option C) 
  (m1: gmap K A) (m2: gmap K B) : gmap K C :=
  let fx := λ (k: K) res, match f k (m1 !! k) (m2 !! k) with
                          | Some x => <[k := x]> res
                          | None => res end in
    set_fold fx (∅: gmap K C) (dom m1 ∪ dom m2).

Lemma gmap_imerge_lookup_aux `{Countable K} {A B C} 
    (f : K → option A → option B → option C)
    (m1 : gmap K A) (m2 : gmap K B) i `{∀ i, f i None None = None} :
    (i ∈ (dom m1 ∪ dom m2) → gmap_imerge f m1 m2 !! i = f i (m1 !! i) (m2 !! i))
    ∧ (i ∉ (dom m1 ∪ dom m2) → gmap_imerge f m1 m2 !! i = None).
Proof.
  set (P := λ (m': gmap K C) (X: gset K),
              ∀ x, (x ∈ X → m' !! x = f x (m1 !! x) (m2 !! x))
                  ∧ (x ∉ X → m' !! x = None) ).
  apply (set_fold_ind_L P); try done.
  intros k X res Hk. unfold P. intros HP. intros x.
  rewrite elem_of_union. rewrite elem_of_singleton. split.
  - intros [-> | Hx].
    + destruct (f k (m1 !! k) (m2 !! k)) as [r |] eqn: Hr.
      by rewrite lookup_insert. by apply HP.
    + assert (x ≠ k) by set_solver.
      destruct (f k (m1 !! k) (m2 !! k)) as [r |] eqn: Hr.
      rewrite lookup_insert_ne; try done. by apply HP.
      by apply HP in Hx.
  - intros H'. assert (x ∉ X ∧ x ≠ k) as [Hx Hxk] by set_solver.
    destruct (f k (m1 !! k) (m2 !! k)) as [r |] eqn: Hr.
    rewrite lookup_insert_ne; try done. by apply HP.
    by apply HP in Hx.
Qed.

Lemma gmap_imerge_lookup `{Countable K} {A B C} 
    (f : K → option A → option B → option C)
    (m1 : gmap K A) (m2 : gmap K B) i `{∀ i, f i None None = None} :
    gmap_imerge f m1 m2 !! i = f i (m1 !! i) (m2 !! i).
Proof.
  destruct (decide (i ∈ dom m1 ∪ dom m2)) as [Hi | Hi].
  - apply gmap_imerge_lookup_aux; try done.
  - assert (i ∉ dom m1 ∧ i ∉ dom m2) as [Hi1 Hi2] by set_solver.
    apply not_elem_of_dom in Hi1. apply not_elem_of_dom in Hi2.
    rewrite Hi1. rewrite Hi2. rewrite H0. 
    apply gmap_imerge_lookup_aux; try done.
Qed.

Lemma gmap_imerge_empty {A} `{Countable K}
      (f : K → option A → option A → option A)
      : (∀ i y, f i y None = y) -> ∀ m, gmap_imerge f m ∅ = m.
Proof.
  intros Hf m.
  rewrite map_eq_iff.
  intros i.
  rewrite gmap_imerge_lookup.
  replace (empty !! i) with (None : option A).
  all: auto.
Qed.


Definition gmap_insert_map {A} `{Countable K} (m s: gmap K A) : (gmap K A) :=
      let f := λ k a m', <[k := a]> m' in
      map_fold f m s.

Lemma gmap_lookup_insert_map_aux {A} `{Countable K} (m s: gmap K A) :
      ∀ k, (k ∈ dom s → gmap_insert_map m s !! k = s !! k)
          ∧ (k ∉ dom s → gmap_insert_map m s !! k = m !! k).
Proof.
  set (P := λ (m': gmap K A) (X: gmap K A),
              ∀ j, (j ∈ dom X → m' !! j = X !! j)
                  ∧ (j ∉ dom X → m' !! j = m !! j)).
  apply (map_fold_ind P); try done.
  intros k a m' r Hmi HP. unfold P. unfold P in HP.
  intros j. split.
  - intros Hj. rewrite <-not_elem_of_dom in Hmi.
    rewrite dom_insert in Hj. rewrite elem_of_union in Hj.
    destruct Hj as [Hj | Hj].
    + assert (j = k) by set_solver; subst j.
      by rewrite !lookup_insert.
    + assert (j ≠ k) by set_solver.
      rewrite !lookup_insert_ne; try done.
      by apply HP.
  - intros Hj. rewrite <-not_elem_of_dom in Hmi.
    rewrite dom_insert in Hj.
    assert (j ≠ k) by set_solver. 
    rewrite !lookup_insert_ne; try done. 
    apply HP. set_solver.
Qed.                              

Lemma gmap_lookup_insert_map {A} `{Countable K} (m s: gmap K A) (k: K) :
      k ∈ dom s → gmap_insert_map m s !! k = s !! k.
Proof.
  apply gmap_lookup_insert_map_aux.
Qed.

Lemma gmap_lookup_insert_map_ne {A} `{Countable K} (m s: gmap K A) (k: K) :
      k ∉ dom s → gmap_insert_map m s !! k = m !! k.
Proof.
  apply gmap_lookup_insert_map_aux.
Qed.
