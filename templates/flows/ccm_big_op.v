From stdpp Require Export functions gmap gmultiset.
Require Export ccm.

(** * Big ops over lists *)
Fixpoint ccm_big_opL `{CCM M} {A} (f : nat → A → M) (xs : list A) : M :=
  match xs with
  | [] => ccm_unit
  | x :: xs => ccm_op (f 0 x) (ccm_big_opL (λ n, f (S n)) xs)
  end.
Global Instance: Params (@ccm_big_opL) 3 := {}.
Global Arguments ccm_big_opL {M} {_ A} _ !_ /.
Typeclasses Opaque ccm_big_opL.
Notation "'[^' + 'list]' k ↦ x ∈ l , P" := (ccm_big_opL (λ k x, P) l)
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[^ +  list]  k ↦ x  ∈  l ,  P") : stdpp_scope.
Notation "'[^' + 'list]' x ∈ l , P" := (ccm_big_opL (λ _ x, P) l)
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[^ +  list]  x  ∈  l ,  P") : stdpp_scope.
   
Definition ccm_big_opS_def `{CCM M} `{Countable A} (f : A → M)
  (X : gset A) : M := ccm_big_opL (λ _, f) (elements X).
Definition ccm_big_opS_aux : seal (@ccm_big_opS_def). Proof. by eexists. Qed.
Definition ccm_big_opS := ccm_big_opS_aux.(unseal).
Global Arguments ccm_big_opS {M} {_ A _ _} _ _.
Definition ccm_big_opS_eq : @ccm_big_opS = @ccm_big_opS_def := ccm_big_opS_aux.(seal_eq).
Global Instance: Params (@ccm_big_opS) 6 := {}.
Notation "'[^' + 'set]' x ∈ X , P" := (ccm_big_opS (λ x, P) X)
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[^ +  set]  x  ∈  X ,  P") : stdpp_scope.

(** * Properties about big ops *)
Section ccm_big_op.
Context `{CCM M}.
Implicit Types xs : list M.
Open Scope ccm_scope.

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : nat → A → M.

  Lemma ccm_big_opL_nil f : ([^+ list] k↦y ∈ [], f k y) = ccm_unit.
  Proof. done. Qed.
  Lemma ccm_big_opL_cons f x l :
    ([^+ list] k↦y ∈ x :: l, f k y) = f 0 x + [^+ list] k↦y ∈ l, f (S k) y.
  Proof. done. Qed.
  Lemma ccm_big_opL_singleton f x : ([^+ list] k↦y ∈ [x], f k y) = f 0%nat x.
  Proof. unfold ccm_big_opL. apply ccm_right_id. Qed.
  Lemma ccm_big_opL_app f l1 l2 :
    ([^+ list] k↦y ∈ l1 ++ l2, f k y)
    = ([^+ list] k↦y ∈ l1, f k y) + ([^+ list] k↦y ∈ l2, f (length l1 + k)%nat y).
  Proof.
    revert f. induction l1 as [|x l1 IH]=> f /=; first by rewrite ccm_left_id.
    rewrite IH. apply ccm_assoc.
  Qed.
  Lemma ccm_big_opL_snoc f l x :
    ([^+ list] k↦y ∈ l ++ [x], f k y) = ([^+ list] k↦y ∈ l, f k y) + f (length l) x.
  Proof. by rewrite ccm_big_opL_app ccm_big_opL_singleton Nat.add_0_r. Qed.

  Lemma ccm_big_opL_unit l : ([^+ list] k↦y ∈ l, 0) = 0.
  Proof. induction l; rewrite /= ?ccm_left_id //. 
    rewrite IHl. apply ccm_left_id. 
  Qed.
  
  Lemma ccm_big_opL_take_drop Φ l n :
    ([^+ list] k ↦ x ∈ l, Φ k x) =
    ([^+ list] k ↦ x ∈ take n l, Φ k x) + ([^+ list] k ↦ x ∈ drop n l, Φ (n + k) x).
  Proof.
    rewrite -{1}(take_drop n l) ccm_big_opL_app take_length.
    destruct (decide (length l ≤ n)).
    - rewrite drop_ge //=.
    - rewrite Nat.min_l //=; lia.
  Qed.
  
  Lemma ccm_big_opL_gen_proper_2 {B} (R : relation M) f (g : nat → B → M)
        l1 (l2 : list B) :
    R ccm_unit ccm_unit →
    Proper (R ==> R ==> R) ccm_op →
    (∀ k,
      match l1 !! k, l2 !! k with
      | Some y1, Some y2 => R (f k y1) (g k y2)
      | None, None => True
      | _, _ => False
      end) →
    R ([^+ list] k ↦ y ∈ l1, f k y) ([^+ list] k ↦ y ∈ l2, g k y).
  Proof.
    intros ??. revert l2 f g. induction l1 as [|x1 l1 IH]=> -[|x2 l2] //= f g Hfg.
    - by specialize (Hfg 0).
    - by specialize (Hfg 0).
    - f_equiv.
      + pose proof (Hfg 0) as Hfg. by simpl in Hfg.
      + apply IH. intros k. apply (Hfg (S k)).
  Qed.
  Lemma ccm_big_opL_gen_proper R f g l :
    Reflexive R →
    Proper (R ==> R ==> R) ccm_op →
    (∀ k y, l !! k = Some y → R (f k y) (g k y)) →
    R ([^+ list] k ↦ y ∈ l, f k y) ([^+ list] k ↦ y ∈ l, g k y).
  Proof.
    intros. apply ccm_big_opL_gen_proper_2; [done..|].
    intros k. destruct (l !! k) eqn:?; auto.
  Qed.
  
  Lemma ccm_big_opL_ext f g l :
    (∀ k y, l !! k = Some y → f k y = g k y) →
    ([^+ list] k ↦ y ∈ l, f k y) = [^+ list] k ↦ y ∈ l, g k y.
  Proof. apply ccm_big_opL_gen_proper; apply _. Qed.
  
  Lemma ccm_big_opL_permutation (f : A → M) l1 l2 :
    l1 ≡ₚ l2 → ([^+ list] x ∈ l1, f x) = ([^+ list] x ∈ l2, f x).
  Proof.
    induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
    - by rewrite IH.
    - by rewrite !assoc (comm _ (f x)).
    - by etrans.
  Qed.

  Global Instance ccm_big_opL_permutation' (f : A → M) :
    Proper ((≡ₚ) ==> (=)) (ccm_big_opL (λ _, f)).
  Proof. intros xs1 xs2. apply ccm_big_opL_permutation. Qed.

  (** The lemmas [big_opL_ne] and [big_opL_proper] are more generic than the
  instances as they also give [l !! k = Some y] in the premise. *)
  Lemma ccm_big_opL_proper f g l :
    (∀ k y, l !! k = Some y → f k y = g k y) →
    ([^+ list] k ↦ y ∈ l, f k y) = ([^+ list] k ↦ y ∈ l, g k y).
  Proof. apply ccm_big_opL_gen_proper; apply _. Qed.

  Lemma ccm_big_opL_proper_2 f g l1 l2 :
    l1 = l2 →
    (∀ k y1 y2,
      l1 !! k = Some y1 → l2 !! k = Some y2 → y1 = y2 → f k y1 = g k y2) →
    ([^+ list] k ↦ y ∈ l1, f k y) = ([^+ list] k ↦ y ∈ l2, g k y).
  Proof.
    intros Hl Hf. apply ccm_big_opL_gen_proper_2; try (apply _ || done).
    (* FIXME (Coq #14441) unnecessary type annotation *)
    intros k. assert (l1 !! k = l2 !! k) as Hlk by (by f_equiv).
    destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
  Qed.

  Global Instance ccm_big_opL_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (=)) ==> (=) ==> (=))
           (ccm_big_opL (A:=A)).
  Proof. intros f f' Hf l ? <-. apply ccm_big_opL_proper; intros; apply Hf. Qed.


  Lemma ccm_big_opL_consZ_l (f : Z → A → M) x l :
    ([^+ list] k↦y ∈ x :: l, f k y) = f 0 x + [^+ list] k↦y ∈ l, f (1 + k)%Z y.
  Proof. rewrite ccm_big_opL_cons. auto using ccm_big_opL_ext with f_equal lia. Qed.
  Lemma ccm_big_opL_consZ_r (f : Z → A → M) x l :
    ([^+ list] k↦y ∈ x :: l, f k y) = f 0 x + [^+ list] k↦y ∈ l, f (k + 1)%Z y.
  Proof. rewrite ccm_big_opL_cons. auto using ccm_big_opL_ext with f_equal lia. Qed.

  Lemma ccm_big_opL_fmap {B} (h : A → B) (f : nat → B → M) l :
    ([^+ list] k↦y ∈ h <$> l, f k y) = ([^+ list] k↦y ∈ l, f k (h y)).
  Proof. revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite IH. Qed.

  Lemma ccm_big_opL_omap {B} (h : A → option B) (f : B → M) l :
    ([^+ list] y ∈ omap h l, f y) = ([^+ list] y ∈ l, from_option f ccm_unit (h y)).
  Proof.
    revert f. induction l as [|x l IH]=> f //; csimpl.
    case_match; csimpl; by rewrite IH // left_id.
  Qed.

  Lemma ccm_big_opL_op f g l :
    ([^+ list] k↦x ∈ l, f k x + g k x)
    = ([^+ list] k↦x ∈ l, f k x) + ([^+ list] k↦x ∈ l, g k x).
  Proof.
    revert f g; induction l as [|x l IH]=> f g /=; first by rewrite left_id.
    by rewrite IH -!assoc (assoc _ (g _ _)) [(ccm_op (g 0 x) _)]comm -!assoc.
  Qed.
End list.

Lemma ccm_big_opL_bind {A B} (h : A → list B) (f : B → M) l :
  ([^+ list] y ∈ l ≫= h, f y) = ([^+ list] x ∈ l, [^+ list] y ∈ h x, f y).
Proof.
  revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite ccm_big_opL_app IH.
Qed.

Lemma ccm_big_opL_sep_zip_with {A B C} (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : nat → A → M) (h2 : nat → B → M) l1 l2 :
  (∀ x y, g1 (f x y) = x) →
  (∀ x y, g2 (f x y) = y) →
  length l1 = length l2 →
  ([^+ list] k↦xy ∈ zip_with f l1 l2, h1 k (g1 xy) + h2 k (g2 xy)) =
  ([^+ list] k↦x ∈ l1, h1 k x) + ([^+ list] k↦y ∈ l2, h2 k y).
Proof.
  intros Hlen Hg1 Hg2. rewrite ccm_big_opL_op.
  rewrite -(ccm_big_opL_fmap g1) -(ccm_big_opL_fmap g2).
  rewrite fmap_zip_with_r; [|auto with lia..].
  by rewrite fmap_zip_with_l; [|auto with lia..].
Qed.

Lemma ccm_big_opL_sep_zip {A B} (h1 : nat → A → M) (h2 : nat → B → M) l1 l2 :
  length l1 = length l2 →
  ([^+ list] k↦xy ∈ zip l1 l2, h1 k xy.1 + h2 k xy.2) =
  ([^+ list] k↦x ∈ l1, h1 k x) + ([^+ list] k↦y ∈ l2, h2 k y).
Proof. by apply ccm_big_opL_sep_zip_with. Qed.

(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

Lemma ccm_big_opS_gen_proper R f g X :
    Reflexive R → Proper (R ==> R ==> R) (+) →
    (∀ x, x ∈ X → R (f x) (g x)) →
    R ([^+ set] x ∈ X, f x) ([^+ set] x ∈ X, g x).
  Proof.
    rewrite ccm_big_opS_eq. intros ?? Hf. apply (ccm_big_opL_gen_proper R); auto.
    intros k x ?%elem_of_list_lookup_2. by apply Hf, elem_of_elements.
  Qed.

  Lemma ccm_big_opS_ext f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^+ set] x ∈ X, f x) = ([^+ set] x ∈ X, g x).
  Proof. apply ccm_big_opS_gen_proper; apply _. Qed.

  (** The lemmas [big_opS_ne] and [big_opS_proper] are more generic than the
  instances as they also give [x ∈ X] in the premise. *)
  Lemma ccm_big_opS_proper f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^+ set] x ∈ X, f x) = ([^+ set] x ∈ X, g x).
  Proof. apply ccm_big_opS_gen_proper; apply _. Qed.

  Global Instance ccm_big_opS_proper' :
    Proper (pointwise_relation _ (=) ==> (=) ==> (=)) (ccm_big_opS (A:=A)).
  Proof. intros f g Hf m ? <-. apply ccm_big_opS_proper; intros; apply Hf. Qed.

  (* FIXME: This lemma could be generalized from [≡] to [=], but that breaks
  [setoid_rewrite] in the proof of [big_sepS_sepS]. See Coq issue #14349. *)
  Lemma ccm_big_opS_elements f X :
    ([^+ set] x ∈ X, f x) = [^+ list] x ∈ elements X, f x.
  Proof. by rewrite ccm_big_opS_eq. Qed.

  Lemma ccm_big_opS_empty f : ([^+ set] x ∈ ∅, f x) = ccm_unit.
  Proof. by rewrite ccm_big_opS_eq /ccm_big_opS_def elements_empty. Qed.

  Lemma ccm_big_opS_insert f X x :
    x ∉ X → ([^+ set] y ∈ {[ x ]} ∪ X, f y) = (f x + [^+ set] y ∈ X, f y).
  Proof. intros. by rewrite !ccm_big_opS_elements elements_union_singleton. Qed.
  Lemma ccm_big_opS_fn_insert {B} (f : A → B → M) h X x b :
    x ∉ X →
    ([^+ set] y ∈ {[ x ]} ∪ X, f y (<[x:=b]> h y))
    = f x b + [^+ set] y ∈ X, f y (h y).
  Proof.
    intros. rewrite ccm_big_opS_insert // fn_lookup_insert.
    f_equiv; apply ccm_big_opS_proper; auto=> y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma ccm_big_opS_fn_insert' f X x P :
    x ∉ X → ([^+ set] y ∈ {[ x ]} ∪ X, <[x:=P]> f y) = (P + [^+ set] y ∈ X, f y).
  Proof. apply (ccm_big_opS_fn_insert (λ y, id)). Qed.

  Lemma ccm_big_opS_union f X Y :
    X ## Y →
    ([^+ set] y ∈ X ∪ Y, f y) = ([^+ set] y ∈ X, f y) + ([^+ set] y ∈ Y, f y).
  Proof.
    intros. induction X as [|x X ? IH] using set_ind_L.
    { by rewrite left_id_L ccm_big_opS_empty left_id. }
    rewrite -assoc_L !ccm_big_opS_insert; [|set_solver..].
    by rewrite -assoc IH; last set_solver.
  Qed.

  Lemma ccm_big_opS_delete f X x :
    x ∈ X → ([^+ set] y ∈ X, f y) = f x + [^+ set] y ∈ X ∖ {[ x ]}, f y.
  Proof.
    intros. rewrite -ccm_big_opS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.

  Lemma ccm_big_opS_singleton f x : ([^+ set] y ∈ {[ x ]}, f y) = f x.
  Proof. intros. rewrite ccm_big_opS_elements elements_singleton /=. 
    apply ccm_right_id. Qed.

  Lemma ccm_big_opS_unit X : ([^+ set] y ∈ X, ccm_unit: M) = (ccm_unit : M).
  Proof.
    by induction X using set_ind_L; rewrite /= ?ccm_big_opS_insert ?left_id // ccm_big_opS_eq.
  Qed.

  Lemma ccm_big_opS_filter' (φ : A → Prop) `{∀ x, Decision (φ x)} f X :
    ([^+ set] y ∈ filter φ X, f y)
    = ([^+ set] y ∈ X, if decide (φ y) then f y else ccm_unit).
  Proof.
    induction X as [|x X ? IH] using set_ind_L.
    { by rewrite filter_empty_L !ccm_big_opS_empty. }
    destruct (decide (φ x)).
    - rewrite filter_union_L filter_singleton_L //.
      rewrite !ccm_big_opS_insert //; last set_solver.
      by rewrite decide_True // IH.
    - rewrite filter_union_L filter_singleton_not_L // left_id_L.
      by rewrite !ccm_big_opS_insert // decide_False // IH left_id.
  Qed.

  Lemma ccm_big_opS_op f g X :
    ([^+ set] y ∈ X, f y + g y) = ([^+ set] y ∈ X, f y) + ([^+ set] y ∈ X, g y).
  Proof. by rewrite !ccm_big_opS_elements -ccm_big_opL_op. Qed.

  Lemma ccm_big_opS_list_to_set f (l : list A) :
    NoDup l →
    ([^+ set] x ∈ list_to_set l, f x) = [^+ list] x ∈ l, f x.
  Proof.
    induction 1 as [|x l ?? IHl].
    - rewrite ccm_big_opS_empty //.
    - rewrite /= ccm_big_opS_union; last set_solver.
      by rewrite ccm_big_opS_singleton IHl.
  Qed.
End gset.

Lemma ccm_big_opS_set_map `{Countable A, Countable B} (h : A → B) (X : gset A) (f : B → M) :
  Inj (=) (=) h →
  ([^+ set] x ∈ set_map h X, f x) = ([^+ set] x ∈ X, f (h x)).
Proof.
  intros Hinj.
  induction X as [|x X ? IH] using set_ind_L.
  { by rewrite set_map_empty !ccm_big_opS_empty. }
  rewrite set_map_union_L set_map_singleton_L.
  rewrite !ccm_big_opS_union; [|set_solver..].
  rewrite !ccm_big_opS_singleton IH //.
Qed.

End ccm_big_op.


  





  
  

  


