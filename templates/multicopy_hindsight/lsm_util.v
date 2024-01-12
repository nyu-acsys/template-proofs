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
From flows Require Export lsm.

Module Type LSM_UTIL.
  Declare Module LSM : LSM_TREE.
  Declare Module DEFS : HINDSIGHT_DEFS with Module DS := LSM.
  Export DEFS DEFS.DS DEFS.DS.NODE.

  Lemma temporal_interpolation_fp (M : gmap nat snapshot) (T: nat) :
      (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) →
        (∀ t1 t2, 0 ≤ t1 ≤ t2 ≤ T → FP (M !!! t1) ⊆ FP (M !!! t2)).
  Proof.
    apply temporal_interpolation_refl_trans; try apply _.
  Qed.

  Lemma temporal_interpolation_inset (M : gmap nat snapshot) (T: nat) n :
    let F := λ s, inset _ (FJ s n) n in
      (∀ t, 0 ≤ t < T → F (M !!! t) ⊆ F (M !!! (t+1)%nat)) →
        (∀ t1 t2, 0 ≤ t1 ≤ t2 ≤ T → F (M !!! t1) ⊆ F (M !!! t2)).
  Proof.
    apply temporal_interpolation_refl_trans; try apply _.
  Qed.

  Lemma in_FP (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    n r M T γ_t γ_m s ts t:
    ⌜transition_inv r M T⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜ts ≤ t ≤ T⌝ -∗
      ⌜n ∈ FP (M !!! t)⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s %Ht".
    assert (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) as H'.
    { intros t' Ht'. apply Trans in Ht'. apply Ht'. }
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
    n r M T γ_t γ_m s t0:
  ⌜transition_inv r M T⌝ -∗
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

  Lemma in_inset (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    n r M T0 γ_t γ_m s t0 k :
  ⌜transition_inv r M T0⌝ -∗
  hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T0 -∗
  past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗ 
  ⌜k ∈ inset _ (FJ s n) n⌝ -∗ 
    ⌜k ∈ inset _ (FJ (M !!! T0) n) n⌝.
  Proof.
    set F := λ s, inset _ (FJ s n) n.
    iIntros "%Trans Hist #Past_s %n_in_s".
    assert (∀ t, 0 ≤ t < T0 → F (M !!! t) ⊆ F (M !!! (t+1)%nat)) as H'.
    { intros t' Ht'. apply Trans in Ht'. apply Ht'. }
    pose proof temporal_interpolation_inset _ _ _ H' as H''.
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
    iDestruct "H1'''" as "(%H2'&%H2''&_)".
    apply H2'' in M_ts. assert (M_ts' := M_ts). apply elem_of_dom_2 in M_ts. 
    rewrite H2' elem_of_gset_seq in M_ts. iPureIntro.
    apply (H'' ts T0). lia. rewrite lookup_total_alt M_ts' /=. done. 
  Qed.


  Lemma per_tick_current Σ Hg1 Hg2 Hg3 γ_t γ_m r M T s :
    ⌜M !!! T ≡ s⌝ -∗ 
    ⌜∀ t, 0 ≤ t ≤ T → per_tick_inv r (M !!! t)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
      ⌜per_tick_inv r s⌝.
  Proof.
    iIntros "%Habs %PT Hist". iDestruct "Hist" as (M')"(_&_&%H'&_)". iPureIntro.
    apply leibniz_equiv in Habs. rewrite <-Habs. apply PT. lia.
  Qed.

  Lemma per_tick_past Σ Hg1 Hg2 Hg3 γ_t γ_m r M T s t0 :
    ⌜∀ t, 0 ≤ t ≤ T → per_tick_inv r (M !!! t)⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
    past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗
      ⌜per_tick_inv r s⌝.
  Proof.
    iIntros "%PT Hist #Past_s".
    iDestruct "Past_s" as (ts)"(_&Hts)".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    iPoseProof (history_sync with "HM' Hts") as "%H'"; try done.
    assert (H'' := H'). apply M_eq, elem_of_dom_2 in H''.
    rewrite Dom_M elem_of_gset_seq in H''.
    apply PT in H''. apply M_eq, lookup_total_correct in H'. by rewrite -H'.
  Qed.

  Lemma temporal_interpolation_bn (M: gmap nat snapshot) (t0 T0: nat) 
    (F: snapshot → (V * T : Type)) :
    (∀ t, t0 ≤ t < T0 → 
      F (M !!! t) = F (M !!! (t+1)) ∨ (F (M !!! t)).2 < (F (M !!! (t+1))).2) →
        (∀ t1 t2, t0 ≤ t1 ≤ t2 ≤ T0 → 
          F (M !!! t1) = F (M !!! t2) ∨ (F (M !!! t1)).2 < (F (M !!! t2)).2).
  Proof.
    set R : relation (V * T) := λ x y, x = y ∨ x.2 < y.2.
    assert (Reflexive R) as Ref.
    { rewrite /Reflexive /R. intros x. by left. }
    assert (Transitive R) as Trans.
    { rewrite /Transitive /R. intros x y z. intros [H1' | H1'] [H2' | H2'].
      - left. by rewrite H1'.
      - subst y. by right.
      - subst z. by right.
      - right; lia. }
    apply (@temporal_interpolation_refl_trans _ R); try apply _.
  Qed.

  Lemma BN_le (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    n k M T0 γ_t γ_m r s ts t:
    ⌜transition_inv r M T0⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T0 -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜n ∈ FP s⌝ -∗
    ⌜ts ≤ t ≤ T0⌝ -∗
      ⌜BN s n !!! k = BN (M !!! t) n !!! k ∨ 
        (BN s n !!! k).2 < (BN (M !!! t) n !!! k).2⌝.
  Proof.
    set R : relation (V * T) := λ x y, x = y ∨ x.2 < y.2.
    set F : snapshot → (V * T : Type) := λ s, BN s n !!! k.
    iIntros "%Trans Hist #Past_s %n_in_s %Ht".
    iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
    iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts"; try done.
    iDestruct "H1'''" as "(%H2'&%H2''&_)".
    apply H2'' in M_ts. 
    assert (ts ∈ dom M) as ts_in_M.
    { rewrite elem_of_dom. by rewrite M_ts. }
    apply lookup_total_correct in M_ts.
    assert (∀ t, 0 ≤ t < T0 → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) as FP_t.
    { intros t' Ht'. apply Trans in Ht'. apply Ht'. }
    pose proof temporal_interpolation_fp _ _ FP_t as FP_t'.
    assert (∀ t, ts ≤ t < T0 → R (F (M !!! t)) (F (M !!! (t+1)%nat))) as Hk.
    { intros t' Ht'. 
      assert (0 <= t' < T0) as H'%Trans by lia. apply H'. }
    pose proof temporal_interpolation_bn _ _ _ _ Hk as Hk'.
    iPureIntro. rewrite -M_ts. apply Hk'. lia.
  Qed.

  Lemma BN_le_2 (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    n M T0 γ_t γ_m r t0 s k:
    ⌜transition_inv r M T0⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T0 -∗
    past_state Σ Hg1 Hg2 Hg3 γ_m t0 s -∗ 
    ⌜n ∈ FP s⌝ -∗
      ⌜BN s n !!! k = BN (M !!! T0) n !!! k ∨ 
        (BN s n !!! k).2 < (BN (M !!! T0) n !!! k).2⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %n_in_s".
    iDestruct "Past_s" as (ts)"(%Hts & Hs)".
    iAssert (⌜ts ≤ T0⌝)%I as %ts_le_T0.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Hs]") as "%M_ts"; try done.
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply elem_of_dom_2 in M_ts. 
      rewrite H2' elem_of_gset_seq in M_ts. iPureIntro. lia. }
    iApply (BN_le with "[%] [$Hist] [$Hs] [%]"); try done.
  Qed. 

  Lemma BN_le_r (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    k M T0 γ_t γ_m r s ts t :
    ⌜transition_inv r M T0⌝ -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T0 -∗
    own γ_m (◯ {[ts := to_agree s]}) -∗
    ⌜∀ t, 0 <= t <= T0 → per_tick_inv r (M !!! t)⌝ -∗
    ⌜ts ≤ t ≤ T0⌝ -∗
      ⌜(BN s r !!! k).2 ≤ (BN (M !!! t) r !!! k).2⌝.
  Proof.
    iIntros "%Trans Hist #Past_s %PT %Ht".
    iAssert (⌜r ∈ FP s⌝)%I as %FP_r.
    { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
      iDestruct (history_sync with "[$H1''] [$Past_s]") as "%M_ts"; try done.
      iDestruct "H1'''" as "(%H2'&%H2''&_)".
      apply H2'' in M_ts. apply lookup_total_correct in M_ts.
      assert (0 ≤ ts ≤ T0) as H' by lia.
      apply PT in H'. rewrite M_ts in H'. iPureIntro. apply H'. }
    iPoseProof (BN_le _ _ _ _ r k 
      with "[%] [$Hist] [$Past_s] [%]") as "%H'"; try done.
    apply H' in Ht. iPureIntro. destruct Ht as [Ht | Ht]; try done.
    rewrite Ht. done. lia.
  Qed.

  Lemma ghost_heap_sync Σ (Hg1 : heapGS Σ) (Hg2 : dsGG Σ) γ_gh γn γn' n : 
    own γ_gh (◯ {[n := to_agree γn]}) -∗
    own γ_gh (◯ {[n := to_agree γn']}) -∗
      ⌜γn = γn'⌝.
  Proof.
    iIntros "H' H''". iCombine "H' H''" as "H'". 
    iPoseProof (own_valid with "H'") as "%H'". iPureIntro. 
    rewrite auth_frag_valid singleton_valid in H'. by apply to_agree_op_inv_L in H'.
  Qed.

  Lemma frac_sync Σ Hg1 Hg2 γn es Vn es' Vn' : 
    lock_frac Σ Hg1 Hg2 γn es Vn -∗
    lock_frac Σ Hg1 Hg2 γn es' Vn' -∗
      ⌜es = es' ∧ Vn = Vn'⌝.
  Proof.
    iIntros "H' H''". unfold lock_frac. iCombine "H' H''" as "H'". 
    iPoseProof (own_valid with "H'") as "%H'". iPureIntro.
    apply dfrac_agree_op_valid_L in H'. destruct H' as [_ H']. by inversion H'.
  Qed.

End LSM_UTIL.
