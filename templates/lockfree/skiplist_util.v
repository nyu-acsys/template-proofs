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
From flows Require Export skiplist flows_big_op.

Declare Module TR : TRAVERSE.
Module SK := SKIPLIST TR.
Module DEFS := HINDSIGHT_DEFS SK.
Export TR.NODE SK DEFS.

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
    apply not_elem_of_dom_2 in HmII.
    { apply not_elem_of_dom. 
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

  Lemma history_sync (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ) 
    γ_m (M: gmap nat (agreeR (ucmra_ofeO snapshotUR))) (s: snapshot) t: 
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

  Lemma in_FP (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    n M T γ_t γ_m s ts t:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
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
    iDestruct (history_sync with "[$H''] [$Past_s]") as "%M_ts"; try done.
    iDestruct "H'''" as "(%H1'&%H1''&_)".
    apply H1'' in M_ts. assert (M_ts' := M_ts). 
    apply lookup_total_correct in M_ts.
    iPureIntro. apply (H'' ts t). repeat (split; try lia).
    rewrite lookup_total_alt. by rewrite M_ts'.
  Qed.

  Lemma in_FP_2 (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    n M T γ_t γ_m s t0:
  ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
  hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
  past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗ 
  ⌜n ∈ FP s⌝ -∗ 
    ⌜n ∈ FP (M !!! T)⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (in_FP with "[%] [$Hist] [$Hs] [%]"); try done.
  Qed.

  Lemma key_eq Σ Hg1 Hg2 Hg3 n M T γ_t γ_m s ts t:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜Key (M !!! t) n = Key s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Ht".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts"; try done.
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

  Lemma key_eq_2 Σ Hg1 Hg2 Hg3 n M T γ_t γ_m s t0:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
      ⌜Key (M !!! T) n = Key s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (key_eq with "[%] [$Hist] [$Hs] [%]"); try done.  
  Qed.

  Lemma height_eq Σ Hg1 Hg2 Hg3 n M T γ_t γ_m s ts t:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜Height (M !!! t) n = Height s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Ht".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts"; try done.
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

  Lemma height_eq_2 Σ Hg1 Hg2 Hg3 n M T γ_t γ_m s t0:
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
      ⌜Height (M !!! T) n = Height s n⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (height_eq with "[%] [$Hist] [$Hs] [%]"); try done.  
  Qed.

  Lemma marking_mono Σ Hg1 Hg2 Hg3 n i M T γ_t γ_m s ts t :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = true⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜Marki (M !!! t) n i = true⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s Mark_n %Ht".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts"; try done.
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

  Lemma marking_mono_2 Σ Hg1 Hg2 Hg3 n i M T γ_t γ_m s t0 :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = true⌝ -∗
      ⌜Marki (M !!! T) n i = true⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Hm".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T⌝)%I as %ts_le_T.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
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


  Lemma marking_witness Σ Hg1 Hg2 Hg3 n i M T γ_t γ_m ts s :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = false⌝ -∗
    ⌜Marki (M !!! T) n i = true⌝ -∗
      ⌜∃ t, ts ≤ t < T ∧ Marki (M !!! t) n i = false ∧ Marki (M !!! S t) n i = true⌝.
  Proof.
    iIntros "%Trans Hist #Hts %n_in_s %Mark_n %Mark_n'".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    iDestruct (history_sync with "[$HM'] [$Hts]") as "%M_ts"; try done.
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

  Lemma next_unchanged Σ Hg1 Hg2 Hg3 n i M T γ_t γ_m t0 s :
    ⌜∀ t, 0 <= t < T → transition_inv (M !!! t) (M !!! (t + 1)%nat)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
    ⌜Marki s n i = true⌝ -∗
      ⌜Nexti (M !!! T) n i = Nexti s n i⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Mark_n".
    iAssert (past_state Σ Hg1 Hg2 Hg3 γ_m t0 s) with "Past_s" as "H'".
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
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    assert (ts ≤ T ≤ T) as H' by lia.
    pose proof temporal_interpolation_next _ ts T T (λ s, Marki s n i)
      (λ s, Nexti s n i) Htrans H' as H''. rewrite /= in H''.
    
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
    iDestruct "H1'''" as "(%H2'&%H2''&_)".
    apply H2'' in M_ts. apply lookup_total_correct in M_ts.
    rewrite M_ts in H''. by iPureIntro.
  Qed.

  Lemma history_dom Σ Hg1 Hg2 Hg3 t γ_t γ_m M T :
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
      ⌜t ∈ dom M ↔ 0 ≤ t ≤ T⌝.
  Proof.
    iIntros "Hist".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    by rewrite Dom_M elem_of_gset_seq.
  Qed. 

  Lemma per_tick_current Σ Hg1 Hg2 Hg3 γ_t γ_m M T s hd tl :
    ⌜M !!! T ≡ s⌝ -∗ 
    ⌜∀ t, 0 ≤ t ≤ T → per_tick_inv hd tl (M !!! t)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
      ⌜per_tick_inv hd tl s⌝.
  Proof.
    iIntros "%Habs %PT Hist". iDestruct "Hist" as (M')"(_&_&%H'&_)". iPureIntro.
    apply leibniz_equiv in Habs. rewrite <-Habs. apply PT. lia.
  Qed.

  Lemma per_tick_past Σ Hg1 Hg2 Hg3 γ_t γ_m M T s t0 hd tl:
    ⌜∀ t, 0 ≤ t ≤ T → per_tick_inv hd tl (M !!! t)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
    past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗
      ⌜per_tick_inv hd tl s⌝.
  Proof.
    iIntros "%PT Hist #Past_s".
    iDestruct "Past_s" as (ts)"(_&Hts)".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    iPoseProof (history_sync with "HM' Hts") as "%H'"; try done.
    assert (H'' := H'). apply M_eq, elem_of_dom_2 in H''.
    rewrite Dom_M elem_of_gset_seq in H''.
    apply PT in H''. apply M_eq, lookup_total_correct in H'. by rewrite -H'.
  Qed.

  Lemma snapshot_create Σ Hg1 Hg2 Hg3 t t0 γ_t γ_m M T:
    ⌜t0 ≤ t ≤ T⌝ -∗ 
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
      |==> past_state Σ Hg1 Hg2 Hg3 γ_m t0 (M !!! t) ∗ hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T.
  Proof.
    iIntros "%Ht Hist".
    iPoseProof (history_dom Σ Hg1 Hg2 Hg3 t with "Hist") as "%Hdom".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    assert (0 ≤ t ≤ T) as Dom_t by lia. apply Hdom in Dom_t.
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
    rewrite Dom_t. iFrame "%#". iPureIntro; lia. iExists M'. iFrame "∗%".
  Qed.

  Lemma snapshot_current Σ Hg1 Hg2 Hg3 γ_t γ_m γ_mt M T s tid t0:
    ⌜M !!! T ≡ s⌝ -∗ 
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
      |==> past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T.
  Proof.
    iIntros "%Habs #(_&Ht0) Hist".
    iAssert (⌜t0 ≤ T⌝)%I as "%H'".
    { iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
      iPoseProof (own_valid_2 with "HT Ht0") as "%Hv".
      rewrite auth_both_valid_discrete max_nat_included /= in Hv.
      iPureIntro. apply Hv. }
    apply leibniz_equiv in Habs. rewrite -Habs.
    iPoseProof (snapshot_create with "[%] [$Hist]") as "H'"; try done.
  Qed.

  Lemma hist_upd Σ Hg1 Hg2 Hg3 γ_t γ_m M T s s':
  ⌜M !!! T ≡ s⌝ -∗
  ⌜s ≠ s'⌝ -∗ 
  hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    |==> hist Σ Hg1 Hg2 Hg3 γ_t γ_m (<[T+1:=s']> M) (T+1).
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

  Lemma in_insets hd tl s p c k :
    per_tick_inv hd tl s → 
    p ∈ FP s → 
    Marki s p 0 = false → 
    Nexti s p 0 = Some c → 
    Key s p < k < W →  
      k ∈ insets (FI s c).
  Proof.
    intros PT FP_p Marki_p Nexti_p Key_pk.
    destruct PT as (PT1&PT2&PT3&PT4&PT5&PT6&PT7).
    assert (c ∈ FP s) as FP_c.
    { by apply (PT6 p c 0). }
    assert (p ≠ c) as p_neq_c.
    { intros ->. pose proof PT5 c c Nexti_p as H'. lia. }
    apply (inset_in_insets _ c). apply (flowint_inset_step (FI s p)).
    destruct PT2 as (H'&_). rewrite /GFI in H'.
    assert ({[p; c]} ⊆ FP s) as Hsub.
    { clear -FP_c FP_p. set_solver. }
    pose proof (flow_big_op_valid _ _ {[p; c]} Hsub H') as H''.
    rewrite big_opS_union in H''. rewrite !big_opS_singleton in H''. done.
    clear -p_neq_c. set_solver. apply PT4 in FP_c. destruct FP_c as (_&_&_&_&_&Hf).
    destruct Hf as (->&_). clear; set_solver.
    apply PT4 in FP_p. destruct FP_p as (_&_&_&_&_&Hf).
    rewrite /Marki in Marki_p. rewrite Marki_p in Hf.
    rewrite /Nexti in Nexti_p. rewrite Nexti_p in Hf.
    destruct Hf as (_&H'&_&H''&_). 
    assert (insets (FI s p) ≠ ∅) as Insets_p. 
    { assert (k ∈ insets (FI s p)) as H1'.
      destruct H'' as (H''&_). apply H''. rewrite elem_of_gset_seq. lia.
      set_solver. }
    apply H' in Insets_p. destruct H'' as (_&H''). rewrite /outsets Insets_p in H''.
    rewrite -leibniz_equiv_iff big_opS_singleton in H''. 
    rewrite -H'' elem_of_gset_seq. lia.
  Qed.
  

  Lemma in_keyset hd tl s p c k :
    per_tick_inv hd tl s → 
    p ∈ FP s → 
    c ∈ FP s → 
    Marki s p 0 = false → 
    Marki s c 0 = false →
    Nexti s p 0 = Some c → 
    Key s p < k ≤ Key s c → 
    0 < k < W → 
        k ∈ keyset (FI s c).
  Proof.
    intros PT FP_p FP_c Mark_p Mark_c Next_p Hk Range_k.
    assert (flow_constraints_I p (FI s p) false (Some c) (Key s p)) as Hp.
    { apply PT in FP_p. destruct FP_p as (_&_&_&_&_&H'). 
      by rewrite -Mark_p -Next_p. }
    assert (flow_constraints_I c (FI s c) false (Next s c !! 0) (Key s c)) as Hc.
    { apply PT in FP_c. destruct FP_c as (_&_&_&_&_&H'). by rewrite -Mark_c. }
    destruct Hp as (Hp1&Hp2&Hp3&(Hp4&Hp4')&Hp5&Hp6&Hp7).
    destruct Hc as (Hc1&Hc2&Hc3&(Hc4&Hc4')&Hc5&Hc6&Hc7).
    assert (k ∈ outsets (FI s p)) as k_in_outsp.
    { rewrite -Hp4' elem_of_gset_seq. lia. }
    assert (insets (FI s p) ≠ ∅) as Domout_p%Hp2.
    { clear -Hp3 k_in_outsp. set_solver. }
    assert (k ∈ outset _ (FI s p) c) as k_in_outp.
    { by rewrite /outsets Domout_p big_opS_singleton in k_in_outsp. }
    assert (k ∉ outsets (FI s c)) as k_notin_outc.
    { rewrite -Hc4' elem_of_gset_seq. lia. }
    assert (p ≠ c) as p_neq_c. { intros ->; clear -Hk; lia. }
    assert (✓ (FI s p ⋅ FI s c)) as VI.
    { destruct PT as (_&(VI&_)&_). rewrite /GFI in VI.
      assert ({[p; c]} ⊆ FP s) as Hsub.
      { clear -FP_p FP_c. set_solver. }
      pose proof (flow_big_op_valid _ _ {[p; c]} Hsub VI) as VI'.
      rewrite big_opS_union in VI'.
      by rewrite !big_opS_singleton in VI'. clear -p_neq_c; set_solver. }
    assert (k ∈ insets (FI s c)) as k_in_infc.
    { apply (inset_in_insets _ c).  
      apply (flowint_inset_step (FI s p) (FI s c) k); try done.
      by rewrite Hc1 elem_of_singleton. }
    clear -k_in_infc k_notin_outc. set_solver.
  Qed.

  Lemma keyset_big_op_auth (S: gset Node) (fks fc : Node → gset nat) :
    ([^op set] x ∈ S, ◯ prodKS (fks x, fc x)) ≡
      ◯ ([^op set] x ∈ S, prodKS (fks x, fc x)).
  Proof.
    induction S as [| s S] using set_ind_L; try done.
    - by rewrite !big_opS_empty.
    - rewrite !big_opS_union; try set_solver.
      rewrite !big_opS_singleton. rewrite IHS.
      by rewrite auth_frag_op.
  Qed.

  Lemma keyset_big_op (S: gset Node) (fks fc : Node → gset nat) :
    ✓ ([^op set] x ∈ S, prodKS (fks x, fc x)) → 
    ([^op set] x ∈ S, prodKS (fks x, fc x)) ≡
        prodKS (([^union set] x ∈ S, fks x), ([^union set] x ∈ S, fc x)).
  Proof.
    induction S as [| s S] using set_ind_L; try done.
    - by rewrite !big_opS_empty.
    - rewrite big_opS_union; last by set_solver. rewrite big_opS_singleton.
      intros HV. assert (HVl := HV). assert (HVr := HV).
      apply (cmra_valid_op_l (prodKS (fks s, fc s))) in HVl.
      apply (cmra_valid_op_r (prodKS (fks s, fc s))) in HVr.
      pose proof IHS HVr as H'. rewrite H'. 
      assert (([^union set] x ∈ ({[s]} ∪ S), fks x) = 
        fks s ∪ ([^union set] x ∈ S, fks x)) as ->.
      { apply leibniz_equiv. rewrite big_opS_union. 
        by rewrite big_opS_singleton. set_solver. }
      assert (([^union set] x ∈ ({[s]} ∪ S), fc x) = 
        fc s ∪ ([^union set] x ∈ S, fc x)) as ->.
      { apply leibniz_equiv. rewrite big_opS_union. 
        by rewrite big_opS_singleton. set_solver. }
      rewrite H' in HV. rewrite ksRAT_prodKS_op; try done.
  Qed.

  Lemma keyset_big_op_valid (S: gset Node) (fks fc : Node → gset nat) :
    ✓ ([^op set] x ∈ S, prodKS (fks x, fc x)) → 
      ((∀ n1 n2 : Node, n1 ∈ S → n2 ∈ S → n1 ≠ n2 → fks n1 ## fks n2)
      ∧ (∀ n, n ∈ S → fc n ⊆ fks n)).
  Proof.
    induction S as [| s S] using set_ind_L; try done.
    rewrite big_opS_union; last by set_solver. rewrite big_opS_singleton.
    intros HV. assert (HVl := HV). assert (HVr := HV).
    apply (cmra_valid_op_l (prodKS (fks s, fc s))) in HVl.
    apply (cmra_valid_op_r (prodKS (fks s, fc s))) in HVr.
    pose proof IHS HVr as H'. pose proof keyset_big_op _ _ _ HVr as H''. 
    rewrite H'' in HV. assert (HV' := HV).
    apply ksRAT_composable_valid in HV'.
    destruct HV' as (_&_&Disj). simpl in Disj.
    assert (∀ x, x ∈ S → fks x ⊆ ([^union set] x ∈ S, fks x)) as Hx.
    { intros x Hx. rewrite (big_opS_delete _ _ x); try done. set_solver. } 
    split.
    - intros n1 n2. rewrite !elem_of_union !elem_of_singleton.
      intros [-> | Hn1s]; intros [-> | Hn2s]; try done.
      + apply Hx in Hn2s. intros _. set_solver.
      + apply Hx in Hn1s. intros _. set_solver.
      + by apply H'.
    - intros n. rewrite elem_of_union elem_of_singleton.
      intros [-> | Hns]. by rewrite /valid /cmra_valid /= in HVl.
      apply IHS; try done.
  Qed. 

  Lemma keyset_disjoint_subset Σ (_: dsGG Σ) γ_ks (S: gset Node) (fks fc : Node → gset nat) :
    ([∗ set] n ∈ S, own γ_ks (◯ prodKS (fks n, fc n))) -∗
        ⌜∀ n1 n2, n1 ∈ S → n2 ∈ S → n1 ≠ n2 → fks n1 ## fks n2⌝
      ∗ ⌜∀ n, n ∈ S → fc n ⊆ fks n⌝.
  Proof.
    destruct (decide (S = ∅)) as [-> | Hs].
    { iIntros "_". iPureIntro. set_solver. }
    rewrite -big_opS_own; try done. iIntros "HKS".
    iPoseProof (own_valid with "HKS") as "%HV".
    iPureIntro. rewrite keyset_big_op_auth in HV.
    rewrite auth_frag_valid in HV. 
    pose proof keyset_big_op_valid _ _ _ HV as H'. apply H'.
  Qed.

  Lemma elem_of_big_op `{Countable A, Countable B} (f : A → gset B) (S: gset A) k :
    k ∈ ([^union set] x ∈ S, f x) → ∃ y, y ∈ S ∧ k ∈ f y.
  Proof.
    induction S as [| s S] using set_ind_L; try done.
    - by rewrite big_opS_empty.
    - rewrite big_opS_union; last by set_solver.
      rewrite big_opS_singleton elem_of_union.
      intros [Hk | Hk]. exists s; set_solver.
      apply IHS in Hk. destruct Hk as [y [Hk1 Hk2]].
      exists y; set_solver. 
  Qed.

  Lemma keyset_summary Σ (_: dsGG Σ) γ_ks (S: gset Node) fks fc (C: gset nat):
    own γ_ks (● prodKS (KS, C)) -∗
    ([∗ set] n ∈ S, own γ_ks (◯ prodKS (fks n, fc n))) -∗
      ⌜∀ n k, n ∈ S → k ∈ fks n → (k ∈ C ↔ k ∈ fc n)⌝.
  Proof.
    destruct (decide (S = ∅)) as [-> | Hs].
    { iIntros "_ _". iPureIntro. set_solver. }
    iIntros "GKS HKS". rewrite -big_opS_own; try done. 
    rewrite keyset_big_op_auth.
    iPoseProof (own_valid with "HKS") as "%HV".
    rewrite auth_frag_valid in HV. 
    pose proof keyset_big_op_valid _ _ _ HV as [Disj Hsub].
    pose proof keyset_big_op _ _ _ HV as H'.
    iPoseProof (own_valid_2 with "GKS HKS") as "%HV2".
    assert (Hincl := HV2). apply auth_both_valid_discrete in Hincl.
    rewrite H' in Hincl. destruct Hincl as [Hincl VKS].
    rewrite H' in HV. 
    pose proof auth_ks_included _ _ _ _ HV VKS Hincl as [Ke [Ce H'']].
    destruct H'' as (Def_KS&Def_C&Disj_ks&Disj_c&Sub1&Sub2&Sub3).
    iPureIntro. intros n k Hn Hk. split.
    - intros Hc. rewrite Def_C elem_of_union in Hc.
      destruct Hc as [Hc | Hc].
      + apply elem_of_big_op in Hc. destruct Hc as [x [Hx1 Hx2]].
        destruct (decide (x = n)) as [-> | Hxn]; try done.
        apply Hsub in Hx2; try done. pose proof Disj x n Hx1 Hn Hxn as H''.
        clear -H'' Hk Hx2; set_solver.
      + apply Sub3 in Hc. rewrite (big_opS_delete _ _ n) in Disj_ks; try done.
        clear -Disj_ks Hk Hc; set_solver.
    - intros Hc. 
      assert (([^union set] x ∈ S, fc x) = 
        fc n ∪ ([^union set] x ∈ S ∖ {[n]}, fc x)) as H''.
      { apply leibniz_equiv. by rewrite (big_opS_delete _ S n). }
      rewrite H'' in Def_C. clear -Def_C Hc; set_solver.
  Qed.

  Lemma nzmap_lookup_big_op `{Countable A, Countable K} (f : A → nzmap K nat) 
    (S : gset A) (k: K) :
    ([^+ set] x ∈ S, f x) !!! k = ([^+ set] x ∈ S, (f x) !!! k).
  Proof. 
    induction S as [| s S] using set_ind_L; try done.
    - rewrite !ccm_big_opS_empty. rewrite nzmap_lookup_empty. done.
    - rewrite !ccm_big_opS_union. all : try set_solver.
      rewrite !ccm_big_opS_singleton. rewrite lookup_total_lifting IHS. done.
  Qed.

  Lemma nat_nonzero_big_op `{Countable A} (f : A → nat) (S : gset A) :
    1 ≤ ([^+ set] x ∈ S, f x) → ∃ x, x ∈ S ∧ 1 ≤ f x.
  Proof. 
    induction S as [| s S] using set_ind_L; try done.
    - rewrite ccm_big_opS_empty /ccm_unit /= /nat_unit. lia.
    - rewrite ccm_big_opS_union; last by set_solver.
      rewrite ccm_big_opS_singleton /ccmop /ccm_op /= /nat_op.
      destruct (decide (1 ≤ f s)). 
      + intros _. exists s. split. set_solver. done.
      + assert (f s = 0) as ->. lia. rewrite left_id.
        intros H'%IHS. destruct H' as [x [Hxs H'']].
        exists x. split. set_solver. done. 
  Qed.

  Lemma outflow_eq_inflow hd tl s p n :
    per_tick_inv hd tl s →
    p ∈ FP s → n ∈ FP s →
    insets (FI s p) ≠ ∅ →
    Nexti s p 0 = Some n → 
      inf (FI s n) n = out (FI s p) n.
  Proof.
    intros PT FP_p FP_n Insets_p Next_p. 
    assert (Hp := FP_p). apply PT in Hp.
    assert (Hn := FP_n). apply PT in Hn.
    assert (Hfp := Hp). destruct Hfp as (_&_&_&_&_&Hfp).
    assert (Hfn := Hn). destruct Hfn as (_&_&_&_&_&Hfn).
    destruct Hfp as (Hfp1&Hfp2&Hfp3&Hfp4&Hfp5&Hfp6&Hfp7&Hfp8).
    destruct Hfn as (Hfn1&Hfn2&Hfn3&Hfn4&Hfn5&Hfn6&Hfn7&Hfn8).
    apply nzmap_eq. intros k. 
    assert (inf (FI s n) n !!! k = 0 ∨ inf (FI s n) n !!! k = 1) as H'. 
    { pose proof Hfn7 k as Hfn7. lia. }
    assert (out (FI s p) n !!! k = 0 ∨ out (FI s p) n !!! k = 1) as H''. 
    { pose proof Hfp8 n k as Hfp8. lia. }
    assert (n ≠ p) as n_neq_p. 
    { destruct PT as (_&_&_&_&PT&_). apply PT in Next_p. intros ->. lia. }
    destruct H' as [Hinf | Hinf]; destruct H'' as [Hout | Hout]; 
      try (rewrite Hinf Hout; lia). 
    - exfalso. assert (✓ ((FI s p) ⋅ (FI s n))) as VI. 
      { destruct PT as (_&(PT&_)&_). clear -PT FP_p FP_n n_neq_p. 
        assert ({[p; n]} ⊆ FP s) as Hsub.
        { clear -FP_p FP_n. set_solver. }
        pose proof (flow_big_op_valid _ _ {[p; n]} Hsub PT) as VI'.
        rewrite big_opS_union in VI'.
        rewrite !big_opS_singleton in VI'. done. set_solver. }
      assert (n ∈ dom (FI s n)) as Dom_n. rewrite Hfn1. clear; set_solver.
      pose proof intComp_unfold_inf_2 _ _ VI n Dom_n as H'.
      rewrite /ccmop /ccm_op /= /lift_op /ccmop /ccm_op /= in H'. 
      rewrite nzmap_eq in H'. pose proof H' k as H'.
      rewrite nzmap_lookup_merge /nat_op Hinf Hout in H'. lia.
    - exfalso. 
      assert (∃ p', p' ∈ FP s ∧ out (FI s p') n !!! k = 1) as [p' [FP_p' Out_p']].
      { destruct PT as (Hdtl&(PT&PT')&_&Hpure&Hkey&_). assert (n ∈ dom (FI s n)) as H1'.
        { rewrite Hfn1. clear; set_solver. }
        pose proof flow_big_op_inf _ _ n n PT FP_n H1' as H'.
        assert (n ≠ hd) as n_neq_hd. 
        { apply Hkey in Next_p. intros ->. destruct Hdtl as (_&H''&_).
          rewrite H'' in Next_p. lia. }
        assert (inf (GFI s) n = 0%CCM) as GFI_n. 
        { by apply PT'. }
        rewrite GFI_n in H'. rewrite nzmap_eq in H'. pose proof H' k as H'.
        rewrite nzmap_lookup_empty /ccmunit /= /ccmop_inv /ccm_opinv /= in H'.
        rewrite lookup_total_lifting_inv /ccmop_inv /ccm_opinv /= in H'.
        rewrite /nat_unit /nat_opinv in H'. rewrite Hinf in H'. 
        assert (1 ≤ ([^+ set] x ∈ (FP s ∖ {[n]}), out (FI s x) n) !!! k) as H''.
        { clear -H'. set a := ([^+ set] x ∈ (FP s ∖ {[n]}), out (FI s x) n) !!! k.
          rewrite -/a in H'. lia. }
        rewrite nzmap_lookup_big_op in H''.
        apply nat_nonzero_big_op in H''. destruct H'' as [p' [FP_p'' Out_p']].
        exists p'. assert (p' ∈ FP s) as FP_p'. { clear -FP_p''; set_solver. }
        split; try done. apply Hpure in FP_p'. destruct FP_p' as (_&_&_&_&_&H'').
        destruct H'' as (_&_&_&_&_&_&_&H''). pose proof H'' n k as H''.
        set a := out (FI s p') n !!! k. rewrite -/a in H'' Out_p'. lia. }
      assert (Hfp' := FP_p'). apply PT in Hfp'. destruct Hfp' as (_&_&_&_&_&Hfp').
      destruct Hfp' as (Hfp1'&Hfp2'&Hfp3'&Hfp4'&Hfp5'&Hfp6'&Hfp7'&Hfp8').
      assert (k ∈ outsets (FI s p')) as Outsets_k.
      { apply (outset_in_outsets _ n). rewrite /outset nzmap_elem_of_dom_total.
        rewrite Out_p' /ccmunit /= /nat_unit. lia. }
      assert (insets (FI s p') ≠ ∅) as Hinsets. 
      { apply Hfp3' in Outsets_k. clear -Outsets_k; set_solver. }
      assert (Domout_p' := Hinsets). apply Hfp2' in Domout_p'.
      destruct (Next s p' !! 0) eqn: Next_p'; last first.
      { rewrite Next_p' in Domout_p'. rewrite /outsets Domout_p' in Outsets_k.
        rewrite big_opS_empty in Outsets_k. clear -Outsets_k; set_solver. }
      rewrite Next_p' in Domout_p'.
      assert (n0 = n) as ->. 
      { assert (n ∈ dom (out_map (FI s p'))) as H'.
        rewrite nzmap_elem_of_dom_total nzmap_eq. intros H'.
        pose proof H' k as H'. rewrite /ccmunit /ccm_unit /= /lift_unit 
          nzmap_lookup_empty /ccmunit /= /nat_unit in H'.
        rewrite Out_p' in H'. lia. rewrite Domout_p' in H'. set_solver. }
      assert (W ∈ outsets (FI s p')) as HWp'.
      { apply Hfp5' in Hinsets. destruct (Mark s p' !!! 0).
        clear -Hinsets Hfp4' Hfp3'. set_solver.
        destruct Hfp4' as [_ <-]. rewrite elem_of_gset_seq. split; try lia.
        destruct Hn as (_&_&_&_&Hn&_). destruct PT as (_&_&_&_&PT&_).
        apply PT in Next_p'. clear -Next_p' Hn. lia. }
      rewrite /outsets Domout_p' big_opS_singleton in HWp'.
      assert (W ∈ outsets (FI s p)) as HWp.
      { apply Hfp5 in Insets_p. destruct (Mark s p !!! 0).
        clear -Insets_p Hfp4 Hfp3. set_solver.
        destruct Hfp4 as [_ <-]. rewrite elem_of_gset_seq. split; try lia.
        destruct Hn as (_&_&_&_&Hn&_). destruct PT as (_&_&_&_&PT&_).
        apply PT in Next_p. clear -Next_p Hn. lia. }
      apply Hfp2 in Insets_p. rewrite /Nexti in Next_p. rewrite Next_p in Insets_p.
      rewrite /outsets Insets_p big_opS_singleton in HWp.
      assert (n ≠ p') as n_neq_p'.
      { destruct PT as (_&_&_&_&PT&_). rewrite /Nexti in PT. 
        apply PT in Next_p'. intros ->. lia. }
      assert (p ≠ p') as p_neq_p'.
      { intros <-. rewrite Out_p' in Hout. done. }
      assert (✓ (((FI s p) ⋅ (FI s p')) ⋅ (FI s n))) as VI.
      { destruct PT as (_&(PT&_)&_). 
        clear -PT FP_p FP_n FP_p' n_neq_p n_neq_p' p_neq_p'. 
        assert ({[p; p'; n]} ⊆ FP s) as Hsub.
        { clear -FP_p FP_p' FP_n. set_solver. }
        pose proof (flow_big_op_valid _ _ {[p; p'; n]} Hsub PT) as VI'.
        rewrite !big_opS_union in VI'.
        rewrite !big_opS_singleton in VI'. done. all : set_solver. }
      assert (n ∈ dom (FI s n)) as Dom_n. rewrite Hfn1. clear; set_solver.
      pose proof intComp_unfold_inf_2 ((FI s p) ⋅ (FI s p')) (FI s n) VI n Dom_n as H'.
      rewrite nzmap_eq in H'. pose proof H' W as H'.
      rewrite /ccmop /ccm_op /= lookup_total_lifting /ccmop /ccm_op /= /nat_op in H'.
      assert (✓ ((FI s p) ⋅ (FI s p'))) as VI'. by apply cmra_valid_op_l in VI.
      assert (n ∉ dom ((FI s p) ⋅ (FI s p'))) as Dom_n'.
      { rewrite intComp_dom; try done. rewrite Hfp1 Hfp1'. 
        clear -n_neq_p n_neq_p'. set_solver. }
      pose proof intComp_unfold_out _ _ VI' n Dom_n' as H''.
      rewrite nzmap_eq in H''. pose proof H'' W as H''.
      rewrite /ccmop /ccm_op /= lookup_total_lifting /ccmop /ccm_op /= /nat_op in H''.
      rewrite H'' in H'. clear -Hfn7 HWp HWp' H'. 
      rewrite /outset nzmap_elem_of_dom_total /ccmunit /ccm_unit /= /nat_unit in HWp.
      rewrite /outset nzmap_elem_of_dom_total /ccmunit /ccm_unit /= /nat_unit in HWp'.
      pose proof Hfn7 W as H''. 
      set a := inf (FI s n) n !!! W.
      set b := out (FI s p) n !!! W.
      set c := out (FI s p') n !!! W.
      rewrite -/a -/b -/c in H'' H' HWp HWp'. lia.
  Qed.

  Lemma make_next_map (Nx : gmap Node (gmap nat Node)) :
      ∃ (N: gmap Node Node), 
          (∀ x, N !! x = (Nx !!! x) !! 0)
        ∧ (dom N ⊆ dom Nx).
  Proof.
    set f := λ (n: Node) (nx: gmap nat Node) (res: gmap Node Node), 
      match nx !! 0 with None => res | Some n' => <[n := n']> res end.
    set N : gmap Node Node := map_fold f ∅ Nx.
    exists N. 
    assert (∀ x : Node, N !! x = (Nx !!! x) !! 0) as Lookup_N.
    { set P := λ (res: gmap Node Node) (m: gmap Node (gmap nat Node)),
        (∀ x: Node, res !! x = 
              (match m !! x with Some mn => mn | None => ∅ end) !! 0).
      apply (map_fold_ind P); try done.
      intros n Nx_n m res Hmn HP. unfold P. unfold P in HP.
      intros n'. unfold f. 
      destruct (decide (n' = n)) as [-> | Hn'].
      - destruct (Nx_n !! 0) as [Nx_n0 | ] eqn:Hn0.
        + rewrite !lookup_insert. by rewrite Hn0.
        + rewrite lookup_insert. rewrite Hn0.
          by rewrite (HP n) Hmn.
      - destruct (Nx_n !! 0) as [Nx_n0 | ] eqn:Hn0.
        + rewrite !lookup_insert_ne; try done.
        + rewrite (HP n'). by rewrite lookup_insert_ne. }
    assert (dom N ⊆ dom Nx) as Dom_N.
    { intros n. rewrite !elem_of_dom. rewrite Lookup_N. 
      destruct (Nx !! n) eqn: H'; try done.
      rewrite lookup_total_alt H' /= lookup_empty. intros [? H'']; try done. }
    done.
  Qed.
  
  Lemma make_mark_map (Mk : gmap Node (gmap nat bool)) :
    (∀ x, x ∈ dom Mk → 0 ∈ dom (Mk !!! x)) →
      ∃ (M: gmap Node bool), 
          (∀ x, M !! x = (Mk !!! x) !! 0)
        ∧ (∀ x, M !!! x = (Mk !!! x) !!! 0)
        ∧ (dom M = dom Mk).
  Proof.
    intros Dom_Mk.
    set f := λ (n: Node) (mk: gmap nat bool) (res: gmap Node bool), 
      match mk !! 0 with None => res | Some n' => <[n := n']> res end.
    set M : gmap Node bool := map_fold f ∅ Mk.
    exists M. 
    assert (∀ x, M !! x = (Mk !!! x) !! 0) as Lookup_M.
    { set P := λ (res: gmap Node bool) (m: gmap Node (gmap nat bool)),
        ∀ x: Node, res !! x = 
          (match m !! x with Some mn => mn | None => ∅ end) !! 0.
      apply (map_fold_ind P); try done.
      intros n Mk_n m res Hmn HP. unfold P. unfold P in HP.
      intros n'. unfold f. 
      destruct (decide (n' = n)) as [-> | Hn'].
      - destruct (Mk_n !! 0) as [Mk_n0 | ] eqn:Hn0.
        + rewrite !lookup_insert. by rewrite Hn0.
        + rewrite lookup_insert. rewrite Hn0. 
          by rewrite (HP n) Hmn.
      - destruct (Mk_n !! 0) as [Mk_n0 | ] eqn:Hn0.
        + rewrite !lookup_insert_ne; try done. 
        + rewrite (HP n'). by rewrite lookup_insert_ne. }
    assert (∀ x, M !!! x = (Mk !!! x) !!! 0) as LookupT_M.
    { intros n. rewrite lookup_total_alt. by rewrite Lookup_M. }
    assert (dom M = dom Mk) as Dom_M.
    { apply set_eq_subseteq; split.
      - intros n. rewrite !elem_of_dom Lookup_M.
        destruct (Mk !! n) eqn: H'; try done.
        rewrite lookup_total_alt H' lookup_empty. intros [? H'']; try done.
      - intros n. rewrite !elem_of_dom Lookup_M.
        destruct (Mk !! n) eqn: H'; try done. intros _.
        assert (H1' := H'). apply (elem_of_dom_2 Mk) in H'.
        apply Dom_Mk in H'. by rewrite elem_of_dom in H'.
        intros [? H'']; try done. }
    done.
  Qed.
