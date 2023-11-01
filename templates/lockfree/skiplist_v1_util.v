From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
From flows Require Export skiplist_v1.

Module SKIPLIST1_UTIL.
  Module DEFS := HINDSIGHT_DEFS SKIPLIST1.
  Import SKIPLIST1 DEFS.
  
  Definition intf_merge (II I: gmap Node (multiset_flowint_ur nat)) :=
    let f := λ m1 m2,
              match m1, m2 with 
              | Some m1, Some m2 => Some m1
              | None, Some m2 => Some m2
              | Some m1, None => Some m1
              | None, None => None end in
    merge f II I.

  Lemma intf_merge_dom II I :
    (dom II ⊆ dom I) →
      dom (intf_merge II I) = dom I.
  Proof.
    intros Hdom. apply set_eq_subseteq. split.
    - intros x. rewrite elem_of_dom.
      intros [m Hx].
      unfold intf_merge in Hx.
      rewrite lookup_merge in Hx.
      unfold diag_None in Hx.
      destruct (I !! x) as [mI |] eqn: HIx.
      + rewrite elem_of_dom; try done.
      + destruct (II !! x) as [mII |] eqn: HIIx; try done.
        apply Hdom. rewrite elem_of_dom; try done.
    - intros x. rewrite !elem_of_dom.
      intros [mx Hx].
      unfold intf_merge.
      rewrite lookup_merge.
      unfold diag_None.
      rewrite Hx.
      destruct (II !! x) as [mII |]; try done.
  Qed.

  Lemma intf_merge_lookup II I :
    (dom II ⊆ dom I) →
      (∀ x, x ∈ dom II → (intf_merge II I) !! x = II !! x).
  Proof.
    intros Dom_II_in_I. intros x Hx.
    unfold intf_merge. rewrite lookup_merge. unfold diag_None.
    destruct (II !! x) as [mII |] eqn: HmII.
    - destruct (I !! x) as [mI |] eqn: HmI; try done.
    - assert (I !! x = None) as H'.
      { apply not_elem_of_dom. 
        apply not_elem_of_dom_2 in HmII.
        set_solver. }
      by rewrite H'.
  Qed.    

  Lemma intf_merge_lookup_total II I :
    (dom II ⊆ dom I) →
      (∀ x, x ∈ dom II → (intf_merge II I) !!! x = II !!! x).
  Proof.
    intros ? H' ?; rewrite !lookup_total_alt.
    rewrite (intf_merge_lookup _ _ _ H'); try done.
  Qed.  

  Lemma intf_merge_lookup_ne II I :
    (dom II ⊆ dom I) →
      (∀ x, x ∈ dom I ∖ dom II → (intf_merge II I) !! x = I !! x).
  Proof.
    intros Dom_II_in_I. intros x Hx.
    rewrite elem_of_difference in Hx.
    destruct Hx as [Hx1 Hx2]. unfold intf_merge.
    rewrite lookup_merge. unfold diag_None.
    rewrite elem_of_dom in Hx1.
    destruct Hx1 as [mI Hx1].
    rewrite Hx1.
    rewrite not_elem_of_dom in Hx2.
    by rewrite Hx2.
  Qed.  

  Lemma intf_merge_lookup_total_ne II I :
    (dom II ⊆ dom I) →
      (∀ x, x ∈ dom I ∖ dom II → (intf_merge II I) !!! x = I !!! x).
  Proof.
    intros ? H' ?; rewrite !lookup_total_alt.
    rewrite (intf_merge_lookup_ne _ _ _ H'); try done.
  Qed.

  Lemma intf_merge_intfEq II I I' :
    let FI := λ I x, I !!! x in
    (dom II ⊆ dom I) →
    (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x)) → 
    I' = intf_merge II I →
      (([^op set] x ∈ dom I, FI I x) = ([^op set] x ∈ dom I, FI I' x)).
  Proof.
    intros FI Dom_II_in_I Heq Def_I'.
    assert (dom I = dom II ∪ (dom I ∖ dom II)) as ->.
    { apply set_eq_subseteq. split; try set_solver.
      intros x Hx. rewrite elem_of_union. rewrite elem_of_difference.
      destruct (decide (x ∈ dom II)); try set_solver. }
    rewrite !big_opS_union; [ | by set_solver..].
    assert (([^op set] y ∈ dom II, FI I' y) = ([^op set] y ∈ dom II, FI II y)) 
      as ->.
    { apply big_opS_ext. intros x Hx. subst I'. unfold FI.
      rewrite intf_merge_lookup_total; try done. }
    assert (([^op set] y ∈ (dom I ∖ dom II), FI I' y) 
      = ([^op set] y ∈ (dom I ∖ dom II), FI I y)) as ->.
    { apply big_opS_ext. intros x Hx. subst I'. unfold FI.
      rewrite intf_merge_lookup_total_ne; try done. }
    by rewrite -Heq.
  Qed.

  Lemma history_sync γ_m (M: gmap nat (agreeR (ucmra_ofeO snapshotUR))) 
    (s: snapshot) t: 
    own γ_m (● M) -∗ own γ_m (◯ {[t := to_agree s]}) -∗
      ⌜M !! t ≡ Some (to_agree s)⌝.
  Proof.
  Admitted.
  

  Lemma temporal_interpolation_refl_trans `{R: relation A}
    (M : gmap nat snapshot) (t0 T: nat) (F: snapshot → A) :
      Reflexive R → Transitive R → 
      (∀ t, t0 ≤ t < T → R (F (M !!! t)) (F (M !!! (t+1)%nat))) →
        (∀ t1 t2, t0 ≤ t1 ≤ t2 ≤ T → R (F (M !!! t1)) (F (M !!! t2))).
  Proof.
    intros R_refl R_trans Hcons. induction t1.
    - induction t2.
      + intros; try done.
      + intros Ht2.
        assert (R (F (M !!! 0)) (F (M !!! t2))) as H'.
        { apply IHt2. lia. }
        assert (R (F (M !!! t2)) (F (M !!! S t2))) as H''.
        { assert (t2 + 1 = S t2) as <- by lia.
          apply Hcons. lia. }
        apply (R_trans _ _ _ H' H''); try done.
    - induction t2.
      + intros H'. exfalso; lia.
      + intros Ht1.
        destruct (decide (S t1 <= t2)).
        * assert (R (F (M !!! S t1)) (F (M !!! t2))) as H'.
          { apply IHt2; try lia. }
          assert (R (F (M !!! t2)) (F (M !!! S t2))) as H''.
          { assert (t2 + 1 = S t2) as <- by lia. 
            apply Hcons. split; try lia. }
          apply (R_trans _ _ _ H' H''); try done.
        * assert (t1 = t2) as -> by lia.
          apply R_refl.
  Qed.

  Lemma temporal_interpolation_fp (M : gmap nat snapshot) (T: nat) :
      (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) →
        (∀ t1 t2, 0 ≤ t1 ≤ t2 ≤ T → FP (M !!! t1) ⊆ FP (M !!! t2)).
  Proof.
    apply temporal_interpolation_refl_trans; try apply _.
  Qed.

  Lemma temporal_interpolation_keys (M : gmap nat snapshot) t0 T n :
      (∀ t, t0 ≤ t < T → Key (M !!! t) n = Key (M !!! (t+1)%nat) n) →
        (∀ t1 t2, t0 ≤ t1 ≤ t2 ≤ T → Key (M !!! t1) n = Key (M !!! t2) n).
  Proof.
    apply (temporal_interpolation_refl_trans _ _ _ (λ x, Key x n)); try apply _.
  Qed.

  Lemma temporal_interpolation_ht (M : gmap nat snapshot) t0 T n :
      (∀ t, t0 ≤ t < T → Height (M !!! t) n = Height (M !!! (t+1)%nat) n) →
        (∀ t1 t2, t0 ≤ t1 ≤ t2 ≤ T → Height (M !!! t1) n = Height (M !!! t2) n).
  Proof.
    apply (temporal_interpolation_refl_trans _ _ _ (λ x, Height x n)); try apply _.
  Qed.

  Lemma temporal_interpolation_marking_mono (M : gmap nat snapshot) t0 T n i :
    let F := λ (x: bool), match x with false => 0 | true => 1 end in
      (∀ t, t0 ≤ t < T → 
          F (Marki (M !!! t) n i) ≤ F (Marki (M !!! (t+1)%nat) n i)) →
        (∀ t1 t2, t0 ≤ t1 ≤ t2 ≤ T → 
            F (Marki (M !!! t1) n i) ≤ F (Marki (M !!! t2) n i)).
  Proof.
    intros F.
    apply (temporal_interpolation_refl_trans _ _ _ (λ x, F (Marki x n i))); 
      try apply _.
  Qed.

  Lemma in_FP n M T γ_t γ_m s ts t:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜n ∈ FP (M !!! t)⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Ht".
    assert (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) as H'.
    { intros t' Ht'. apply Trans in Ht'. 
    by destruct Ht' as (_&_&_&_&_&H'). }
    pose proof temporal_interpolation_fp _ _ H' as H''.
    iDestruct "Hist" as (M') "(H'&H''&H''')".
    iDestruct (history_sync with "[$H''] [$Past_s]") as "%M_ts".
    iDestruct "H'''" as "(%H1'&%H1''&_)".
    apply H1'' in M_ts. assert (M_ts' := M_ts). 
    apply lookup_total_correct in M_ts.
    iPureIntro. apply (H'' ts t). repeat (split; try lia).
    rewrite lookup_total_alt. by rewrite M_ts'.
  Qed.

  Lemma in_FP_2 n M T γ_t γ_m s t0:
  ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
  hist γ_t γ_m M T -∗
  past_state γ_m t0 s -∗ 
  ⌜n ∈ FP s⌝ -∗ 
    ⌜n ∈ FP (M !!! T)⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts".
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (in_FP with "[%] [$Hist] [$Hs] [%]"); try done.
  Qed.

  Lemma key_eq n M T γ_t γ_m s ts t:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜Key (M !!! t) n = Key s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Ht".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts".
    iDestruct "H1'''" as "(%H2'&%H2''&_)".
    apply H2'' in M_ts. 
    assert (ts ∈ dom M) as ts_in_M.
    { rewrite elem_of_dom. by rewrite M_ts. }
    apply lookup_total_correct in M_ts.
    assert (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) as FP_t.
    { intros t' Ht'. apply Trans in Ht'. 
      by destruct Ht' as (_&_&_&_&_&H'). }
    pose proof temporal_interpolation_fp _ _ FP_t as FP_t'.
    assert (∀ t, ts ≤ t < T → Key (M !!! t) n = Key (M !!! (t+1)%nat) n) as Hk.
    { intros t' Ht'. 
      assert (0 <= t' < T) as H'%Trans by lia. 
      destruct H' as (_&_&_&_&H'&_).
      rewrite -M_ts in n_in_s. symmetry.
      apply H'. apply (FP_t' ts); try (done || lia). }
    pose proof temporal_interpolation_keys _ _ _ _ Hk as Hk'.
    iPureIntro. rewrite -M_ts. symmetry. apply Hk'.
    repeat (split; try done).
  Qed.

  Lemma key_eq_2 n M T γ_t γ_m s t0:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    past_state γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
      ⌜Key (M !!! T) n = Key s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts".
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (key_eq with "[%] [$Hist] [$Hs] [%]"); try done.  
  Qed.

  Lemma height_eq n M T γ_t γ_m s ts t:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜Height (M !!! t) n = Height s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Ht".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts".
    iDestruct "H1'''" as "(%H2'&%H2''&_)".
    apply H2'' in M_ts. 
    assert (ts ∈ dom M) as ts_in_M.
    { rewrite elem_of_dom. by rewrite M_ts. }
    apply lookup_total_correct in M_ts.
    assert (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) as FP_t.
    { intros t' Ht'. apply Trans in Ht'. 
      by destruct Ht' as (_&_&_&_&_&H'). }
    pose proof temporal_interpolation_fp _ _ FP_t as FP_t'.
    assert (∀ t, ts ≤ t < T → Height (M !!! t) n = Height (M !!! (t+1)%nat) n) as Hk.
    { intros t' Ht'. 
      assert (0 <= t' < T) as H'%Trans by lia. 
      destruct H' as (_&_&_&H'&_).
      rewrite -M_ts in n_in_s. symmetry.
      apply H'. apply (FP_t' ts); try (done || lia). }
    pose proof temporal_interpolation_ht _ _ _ _ Hk as Hk'.
    iPureIntro. rewrite -M_ts. symmetry. apply Hk'.
    repeat (split; try done).
  Qed.

  Lemma height_eq_2 n M T γ_t γ_m s t0:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    past_state γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
      ⌜Height (M !!! T) n = Height s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts".
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (height_eq with "[%] [$Hist] [$Hs] [%]"); try done.  
  Qed.

  Lemma marking_mono n i M T γ_t γ_m s ts t :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = true⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜Marki (M !!! t) n i = true⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s Mark_n %Ht".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts".
    iDestruct "H1'''" as "(%H2'&%H2''&_)".
    apply H2'' in M_ts. 
    assert (ts ∈ dom M) as ts_in_M.
    { rewrite elem_of_dom. by rewrite M_ts. }
    apply lookup_total_correct in M_ts.
    assert (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) as FP_t.
    { intros t' Ht'. apply Trans in Ht'. 
    by destruct Ht' as (_&_&_&_&_&H'). }
    pose proof temporal_interpolation_fp _ _ FP_t as FP_t'.
    set F := λ (x: bool), match x with false => 0 | true => 1 end.
    assert (∀ t, ts ≤ t < T → 
      F (Marki (M !!! t) n i) ≤ F (Marki (M !!! (t+1)%nat) n i)) as Hm.
    { intros t' Ht'. 
      assert (0 <= t' < T) as H'%Trans by lia. 
      destruct H' as (_&_&H'&_).
      assert (n ∈ FP (M !!! t')) as n_in_t'.
      { assert (0 ≤ ts ≤ t' ≤ T) as H''%FP_t' by lia. apply H''.
        by rewrite -M_ts in n_in_s. }
      pose proof (H' n i n_in_t') as H''.
      set a: bool := Marki (M !!! t') n i.
      set b: bool := Marki (M !!! (t' + 1)) n i.
      rewrite -/a -/b in H''.
      destruct a; destruct b; unfold F; try (done || lia). }
    pose proof temporal_interpolation_marking_mono _ _ _ _ _ Hm as Hm'.
    assert (ts ≤ T) as Hts. 
    { rewrite H2' elem_of_gset_seq in ts_in_M. lia. }
    assert (ts ≤ ts ≤ t ≤ T) as H' by lia.
    pose proof Hm' _ _ H' as Hm'.
    iDestruct "Mark_n" as %Mark_n.
    rewrite -M_ts in Mark_n.
    rewrite Mark_n in Hm'. iPureIntro.
    set a : bool := Marki (M !!! t) n i.
    rewrite -/a in Hm'. destruct a; try (done || lia).
  Qed.

  Lemma marking_mono_2 n i M T γ_t γ_m s t0 :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    past_state γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = true⌝ -∗
      ⌜Marki (M !!! T) n i = true⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Hm".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts".
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (marking_mono with "[%] [$Hist] [$Hs] [%] [%]"); try done.
  Qed.  

  Lemma temporal_interpolation_marking (M : gmap nat snapshot) 
    (t0 T: nat) (Mark: snapshot → bool) :
      (∀ t, t0 ≤ t < T → Mark (M !!! t) = true → Mark (M !!! S t) = true) →
        Mark (M !!! t0) = false → Mark (M !!! T) = true → t0 ≤ T →
        (∃ t, t0 ≤ t < T ∧ Mark (M !!! t) = false ∧ Mark (M !!! S t) = true).
  Proof.
    intros Htrans; induction t0; induction T; intros Mark1 Mark2 t1_le_t2.
    - exfalso. rewrite Mark2 in Mark1. inversion Mark1.
    - destruct (decide (Mark (M !!! T) = true)).
      + assert (∀ t, 0 <= t < T → Mark (M !!! t) = true → 
          Mark (M !!! S t) = true) as H'.
        { intros t Ht; apply Htrans; try lia. }
        assert (0 ≤ T) as H'' by lia.
        pose proof IHT H' Mark1 e H'' as [t [? [? ?]]].
        exists t; repeat split; try (done || lia).
      + rewrite not_true_iff_false in n.
        exists T. repeat split; try (done || lia).
    - exfalso; lia.
    - assert (t0 < T ∨ t0 = T) as [t0_le_T | ->] by lia; last first.
      { exfalso. rewrite Mark2 in Mark1. inversion Mark1. }
      destruct (decide (Mark (M !!! T) = true)); last first.
      { rewrite not_true_iff_false in n.
        exists T. repeat split; try (done || lia). }
      assert (∀ t, S t0 <= t < T → Mark (M !!! t) = true → 
        Mark (M !!! S t) = true) as H'.
      { intros t Ht; apply Htrans; lia. }
      assert ((∀ t, t0 <= t < T → Mark (M !!! t) = true → 
                  Mark (M !!! S t) = true) → 
               Mark (M !!! t0) = false → 
               Mark (M !!! T) = true → 
               t0 ≤ T → 
               ∃ t, t0 <= t < T ∧ Mark (M !!! t) = false 
                ∧ Mark (M !!! S t) = true) as H''.
      { intros Htrans' Mark1' _ _. 
        assert (∀ t, t0 <= t < S T → Mark (M !!! t) = true → 
          Mark (M !!! S t) = true) as H''.
        { intros t Ht; destruct (decide (t = t0)) as [-> | ?].
          - intros H''; rewrite H'' in Mark1'. done. 
          - apply Htrans. lia. }
        assert (t0 ≤ S T) as H1' by lia.
        pose proof IHt0 H'' Mark1' Mark2 H1' as H1''.
        destruct H1'' as [t [? [? ?]]].
        destruct (decide (t = T)) as [-> | Ht].
        { rewrite e in H0. done. }
        exists t. repeat split; try (done || lia). }
      assert (S t0 ≤ T) as H1' by lia.
      pose proof IHT H' H'' Mark1 e H1' as H1''.
      destruct H1'' as [t [? [? ?]]].
      exists t. repeat split; try (done || lia).
  Qed.


  Lemma marking_witness n i M T γ_t γ_m ts s :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = false⌝ -∗
    ⌜Marki (M !!! T) n i = true⌝ -∗
      ⌜∃ t, ts ≤ t < T ∧ Marki (M !!! t) n i = false ∧ Marki (M !!! S t) n i = true⌝.
  Proof.
    iIntros "%Trans Hist #Hts %n_in_s %Mark_n %Mark_n'".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    iDestruct (history_sync with "[$HM'] [$Hts]") as "%M_ts".
    apply M_eq in M_ts. assert (ts ∈ dom M) as ts_in_M.
    { rewrite elem_of_dom. by rewrite M_ts. }
    apply lookup_total_correct in M_ts.
    assert (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) as FP_t.
    { intros t' Ht'. apply Trans in Ht'. 
      by destruct Ht' as (_&_&_&_&_&H'). }
    pose proof temporal_interpolation_fp _ _ FP_t as FP_t'.
    assert (∀ t, ts ≤ t < T → Marki (M !!! t) n i = true → 
                                Marki (M !!! S t) n i = true) as H'.
    { intros t' Ht'. 
      assert (0 <= t' < T) as H'%Trans by lia. 
      destruct H' as (_&_&H'&_).
      assert (n ∈ FP (M !!! t')) as n_in_t'.
      { assert (0 ≤ ts ≤ t' ≤ T) as H''%FP_t' by lia. apply H''.
        by rewrite -M_ts in n_in_s. }
      pose proof (H' n i n_in_t') as H''.
      assert (S t' = t' + 1) as -> by lia. done. }
    assert (Marki (M !!! ts) n i = false) as Mark1.
    { rewrite M_ts. done. }
    assert (ts ≤ T) as Ht_s. { rewrite Dom_M elem_of_gset_seq in ts_in_M. lia. }
    pose proof temporal_interpolation_marking M ts T (λ s, Marki s n i) 
      H' Mark1 Mark_n' Ht_s as H''. 
    destruct H'' as [t [? [? ?]]].
    iPureIntro. exists t; repeat split; try (done || lia).
  Qed.

  Lemma temporal_interpolation_next (M : gmap nat snapshot) 
    (t0 t T: nat) (Mark: snapshot → bool) (Next: snapshot → option Node) :
      (∀ t, t0 ≤ t < T → Next (M !!! S t) = Next (M !!! t)) →
      t0 ≤ t ≤ T →
        (Next (M !!! t) = Next (M !!! t0)).
  Proof.
    intros Htrans; induction t; intros Range_t.
    - assert (t0 = 0) as -> by lia. done.
    - destruct (decide (S t = t0)) as [-> | H']; try done.
      rewrite Htrans. apply IHt. all: lia.
  Qed.

  Lemma next_unchanged n i M T γ_t γ_m t0 s :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist γ_t γ_m M T -∗
    past_state γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = true⌝ -∗
      ⌜Nexti (M !!! T) n i = Nexti s n i⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Mark_n".
    iAssert (past_state γ_m t0 s) with "Past_s" as "H'".
    iDestruct "H'" as (ts)"(%Hts & Hs)".
    iAssert (∀ t, ⌜ts ≤ t < T⌝ → 
      ⌜Nexti (M !!! S t) n i = Nexti (M !!! t) n i⌝)%I as %Htrans.
    { iIntros (t)"%Range_t". assert (0 ≤ t < T) as H'. lia.
      apply Trans in H'. destruct H' as (H'&_).
      iAssert (⌜n ∈ FP (M !!! t)⌝)%I as %Hfp.
      { iApply (in_FP with "[%] [$Hist] [$Hs] [%] [%]"); try done. lia. }
      iAssert (⌜Marki (M !!! (t+1)%nat) n i = true⌝)%I as %Hm.
      { iApply (marking_mono with "[%] [$Hist] [$Hs] [%] [%] [%]"); try done. lia. }
      iPureIntro. assert (∀ t, (t+1)%nat = S t) as H'' by lia. rewrite -H''.
      apply H'; try done. }
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts".
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    assert (ts ≤ T ≤ T) as H' by lia.
    pose proof temporal_interpolation_next _ ts T T (λ s, Marki s n i)
      (λ s, Nexti s n i) Htrans H' as H''. rewrite /= in H''.
    
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts".
    iDestruct "H1'''" as "(%H2'&%H2''&_)".
    apply H2'' in M_ts. apply lookup_total_correct in M_ts.
    rewrite M_ts in H''. by iPureIntro.
  Qed.

  Lemma per_tick_current γ_t γ_m M T s :
    ⌜M !!! T ≡ s⌝ -∗ 
    ⌜∀ t, t ∈ dom M → per_tick_inv (M !!! t)⌝ -∗
    hist γ_t γ_m M T -∗ 
      ⌜per_tick_inv s⌝.
  Proof.
    iIntros "%Habs %PT Hist". iDestruct "Hist" as (M')"(_&_&%H'&_)". iPureIntro.
    apply leibniz_equiv in Habs. rewrite <-Habs. apply PT.
    rewrite H' elem_of_gset_seq; lia. 
  Qed.

  Lemma snapshot_create t γ_t γ_m M T t0:
    ⌜t ∈ dom M⌝ -∗
    ⌜t0 ≤ t⌝ -∗ 
    own γ_t (◯ MaxNat t0) -∗ 
    hist γ_t γ_m M T -∗ 
      |==> past_state γ_m t0 (M !!! t) ∗ hist γ_t γ_m M T.
  Proof.
    iIntros "%Dom_t %t0_le_t Ht0 Hist".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    apply elem_of_dom in Dom_t. destruct Dom_t as [s Dom_t].
    apply M_eq in Dom_t. 
    iPoseProof (own_update _ (● M') (● M' ⋅ ◯ {[t := to_agree s]}) with "HM'") 
      as ">(HM' & #Ht)". 
    { apply auth_update_alloc, local_update_unital_discrete. 
      intros z Hm Hz. split; try done. rewrite left_id in Hz. rewrite -Hz.
      apply map_equiv_iff. intros x. destruct (decide (x = t)) as [-> | Hxz].
      - rewrite lookup_op Dom_t lookup_insert. rewrite /op /cmra_op /=.
        by rewrite agree_idemp.
      - rewrite lookup_op lookup_insert_ne; try done. rewrite lookup_empty.
        rewrite /op /cmra_op /=. destruct (M' !! x) eqn:H'; rewrite H'; try done. }
    iModIntro. iFrame. iSplitR. iExists t. apply M_eq, lookup_total_correct in Dom_t.
    rewrite Dom_t. iFrame "%#". iExists M'. iFrame "∗%".
  Qed.

  Lemma snapshot_current γ_t γ_m M T s t0:
    ⌜M !!! T ≡ s⌝ -∗ 
    own γ_t (◯ MaxNat t0) -∗ 
    hist γ_t γ_m M T -∗ 
      |==> past_state γ_m t0 s ∗ hist γ_t γ_m M T.
  Proof.
    iIntros "%Habs #Ht0 Hist". 
    iAssert (⌜t0 ≤ T ∧ T ∈ dom M⌝)%I as "(%H' & %H'')".
    { iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
      iPoseProof (own_valid_2 with "HT Ht0") as "%Hv".
      rewrite auth_both_valid_discrete max_nat_included /= in Hv.
      iPureIntro. split. apply Hv. rewrite Dom_M elem_of_gset_seq; lia. }
    apply leibniz_equiv in Habs. rewrite -Habs.
    iPoseProof (snapshot_create with "[%] [%] [$Ht0] [$Hist]") as "H'"; try done.
  Qed.

  Lemma hist_upd γ_t γ_m M T s s':
  ⌜M !!! T ≡ s⌝ -∗
  ⌜s ≠ s'⌝ -∗ 
  hist γ_t γ_m M T -∗
    |==> hist γ_t γ_m (<[T+1:=s']> M) (T+1).
  Proof.
    iIntros "%Habs %Hs Hist".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    iPoseProof (own_update _ (● MaxNat T) (● MaxNat (T+1)) with "HT") 
      as ">HT".
    { apply (auth_update_auth _ _ (MaxNat (T+1))), max_nat_local_update.
      simpl. lia. } 
    iPoseProof (own_update _ (● M') (● (<[T+1:= to_agree s']> M')) with "HM'") 
      as ">HM'". 
    { apply (auth_update_auth _ _ {[T+1 := to_agree s']}). 
      apply local_update_unital_discrete. intros z Hm Hz. rewrite left_id in Hz. 
      rewrite -Hz. split. 
      - apply insert_valid; try done.
      - assert (M' !! (T+1) = None) as Hmt. 
        { assert (T+1 ∉ dom M) as H'. rewrite Dom_M elem_of_gset_seq. lia.
          assert (T+1 ∉ dom M') as H''. intros H''. rewrite elem_of_dom in H''.
          destruct H'' as [x H'']. assert (M' !! (T+1) ≡ Some x) as H1'.
          rewrite H''. done. pose proof lookup_valid_Some _ _ _ Hm H1' as H1''.
          apply to_agree_uninj in H1''. destruct H1'' as [s'' H1''].
          rewrite -H1'' in H1'. apply M_eq in H1'. apply elem_of_dom_2 in H1'.
          set_solver. by rewrite not_elem_of_dom in H''. }
        apply map_equiv_iff. intros x. destruct (decide (x = T+1)) as [-> | Hxz].
        + rewrite lookup_op Hmt !lookup_insert /=. try done.
        + rewrite lookup_op !lookup_insert_ne; try done. rewrite lookup_empty.
          rewrite /op /cmra_op /=. destruct (M' !! x) eqn:H'; rewrite H'; try done. }
    iModIntro. iExists (<[T+1:= to_agree s']> M'). iFrame. iPureIntro. split; last split.
    - rewrite dom_insert_L Dom_M. rewrite gset_seq_union. clear; set_solver.
    - intros t s0. destruct (decide (t = T+1)) as [-> | Ht].
      + rewrite !lookup_insert. split. intros H'. inversion H'.
        apply to_agree_inj in H1. apply leibniz_equiv in H1. by rewrite H1.
        intros [=]. by subst s0.
      + rewrite !lookup_insert_ne; try done.
    - intros t. destruct (decide (t = T)) as [-> | Ht].
      + rewrite lookup_total_insert_ne. rewrite lookup_total_insert.
        apply leibniz_equiv in Habs. rewrite Habs. done. lia.
      + intros ?; rewrite !lookup_total_insert_ne; try lia. apply M_neq. lia.
  Qed.

End SKIPLIST1_UTIL.