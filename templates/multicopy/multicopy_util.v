From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.proofmode Require Import tactics.
Set Default Proof Using "All".
Require Export multicopy.

Section multicopy_util.
  Context {Σ} `{!multicopyG Σ}.
  Notation iProp := (iProp Σ).

  Lemma MCS_agree γ_te γ_he t H t' H':
    MCS_auth γ_te γ_he t H -∗ MCS γ_te γ_he t' H' -∗ ⌜t = t'⌝ ∗ ⌜H = H'⌝.
  Proof.
    iIntros "(Ht● & HH●) (Ht'◯ & HH'◯ & _)".
    iDestruct (own_valid_2 with "Ht● Ht'◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "HH● HH'◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    by iPureIntro.
  Qed.

  Lemma map_of_set_lookup_cases H k:
        (∃ v t, (k, v, t) ∈ H ∧ (∀ v' t', (k, v', t') ∈ H → t' ≤ t) ∧ map_of_set H !! k = Some (v, t))
      ∨ ((∀ v t, (k, v, t) ∉ H) ∧ map_of_set H !! k = None).
  Proof.
    set (P := λ (m: gmap K (V*TS)) (X: gset KVT),
                (∃ v t, (k, v, t) ∈ X ∧ (∀ v' t', (k, v', t') ∈ X → t' ≤ t)
                          ∧ m !! k = Some (v, t))
              ∨ ((∀ v t, (k, v, t) ∉ X) ∧ m !! k = None)).
    apply (set_fold_ind_L P); try done.
    - unfold P. right. split; try done.
    - intros [[k' v'] t'] X m Hnotin Hp.
      destruct (decide (k' = k)).
      + replace k'. unfold P. left. unfold P in Hp.
        destruct Hp as [Hp | Hp].
        * destruct Hp as [v [t Hp]].
          destruct (decide (t < t')).
          ** exists v', t'. repeat split; first set_solver.
             intros v'' t''. rewrite elem_of_union.
             intros [Hv | Hv]. assert (t'' = t') by set_solver.
             lia. destruct Hp as [_ [Hp _]].
             pose proof Hp v'' t'' Hv. lia. simpl.
             assert ((m !!! k).2 <= t') as Hm.
             { unfold lookup_total, map_lookup_total.
               destruct Hp as [_ [_ Hp]]. rewrite Hp.
               simpl. lia. }
             destruct (decide ((m !!! k).2 ≤ t')); try done.
             by rewrite lookup_insert.
          ** assert (t' = t ∨ t' < t) as Ht by lia. clear n.
             destruct Hp as [Hp1 [Hp2 Hp3]].
             destruct Ht as [Ht | Ht]. 
             *** replace t'. exists v', t.
                 repeat split; first set_solver.
                 intros v'' t''. rewrite elem_of_union.
                 intros [Hv | Hv]. assert (t'' = t) by set_solver.
                 assert (v'' = v') by set_solver.
                 lia. pose proof Hp2 v'' t'' Hv. lia. simpl.
                 assert ((m !!! k).2 <= t) as Hm.
                 { unfold lookup_total, map_lookup_total.
                   rewrite Hp3. simpl. lia. }
                 destruct (decide ((m !!! k).2 ≤ t)); try done.
                 rewrite lookup_insert. done.
             *** exists v, t. repeat split; first set_solver.
                 intros v'' t''. rewrite elem_of_union.
                 intros [Hv | Hv]. assert (t'' = t') by set_solver.
                 assert (v'' = v') by set_solver.
                 lia. pose proof Hp2 v'' t'' Hv. lia. simpl.
                 assert (not ((m !!! k).2 ≤ t')) as Hm.
                 { unfold lookup_total, map_lookup_total.
                   rewrite Hp3. simpl. lia. }
                 destruct (decide ((m !!! k).2 ≤ t')); try done.
        * exists v', t'. simpl. repeat split; first set_solver.
          intros v'' t''. rewrite elem_of_union. intros [Hv | Hv].
          assert (t'' = t') by set_solver. assert (v'' = v') by set_solver.
          lia. destruct Hp as [Hp _].
          pose proof Hp v'' t'' as Hp. set_solver.
          assert ((m !!! k).2 ≤ t') as Hm.
          { unfold lookup_total, map_lookup_total.
            destruct Hp as [_ Hp]. rewrite Hp. simpl; lia. }
          destruct (decide ((m !!! k).2 ≤ t')); try done.
          by rewrite lookup_insert.
      + unfold P. unfold P in Hp.
        destruct Hp as [Hp | Hp].
        * destruct Hp as [v [t [Hp1 [Hp2 Hp3]]]].
          left. exists v, t. repeat split; first set_solver.
          intros v'' t'' Hkt. assert ((k, v'', t'') ∈ X) as Hx by set_solver.
          by pose proof Hp2 v'' t'' Hx. simpl.
          destruct (decide ((m !!! k').2 <= t')).
          rewrite lookup_insert_ne; try done. done.
        * destruct Hp as [Hp1 Hp2]. right.
          repeat split; first set_solver. simpl.
          destruct (decide ((m !!! k').2 <= t')).
          rewrite lookup_insert_ne; try done. done.
  Qed.

  Lemma map_of_set_lookup H k v t :
        unique_val H → 
          (k, v, t) ∈ H → (∀ v' t', (k, v', t') ∈ H → t' ≤ t) →
            map_of_set H !! k = Some (v, t).
  Proof.
    intros Uniq Hkt Hmax.
    pose proof (map_of_set_lookup_cases H k) as Hp.
    destruct Hp as [Hp | Hp].
    - destruct Hp as [v' [t' [Hp1 [Hp2 Hp3]]]].
      pose proof Hmax v' t' Hp1 as Ht1.
      pose proof Hp2 v t Hkt as Ht2.
      assert (t = t') as Ht by lia. subst t'.
      pose proof Uniq k v v' t Hkt Hp1 as Uniq.
      by subst v'.
    - destruct Hp as [Hp _].
      pose proof Hp v t. set_solver.
  Qed.  
  
  Lemma map_of_set_lookup_some_aux (H: gset KVT) k :
        unique_val H → 
          (∀ v t, (k, v, t) ∉ H) ∨ 
            (∃ v t, (k, v, t) ∈ H ∧ (∀ v' t', (k, v', t') ∈ H → t' ≤ t)).
  Proof.
    intros Uniq.
    set (P := λ (X: gset KVT), (∀ v t, (k, v, t) ∉ X) ∨
                  (∃ v T, (k, v, T) ∈ X ∧ (∀ v' t', (k, v', t') ∈ X → t' ≤ T))).
    apply (set_ind_L P); try done.
    - unfold P. left. intros v t. set_solver.
    - intros [[k' v'] t'] X Hkt HP. subst P.
      simpl in HP. simpl. destruct (decide (k' = k)).
      + subst k'. destruct HP as [H' | H'].
        * right. exists v', t'. split.
          set_solver. intros v t. destruct (decide (t' = t)).
          subst t'. intros; done.
          intros H''. assert ((k,v,t) ∈ X).
          set_solver. pose proof H' v t as H'.
          done.
        * right. destruct H' as [v [T H']].
          destruct (decide (t' < T)).
          ** exists v, T. split.
             destruct H' as [H' _].
             set_solver. intros v'' t'' Hkt'.
             rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia.
             destruct H' as [_ H'']. apply (H'' v''); try done.
          ** exists v', t'. split. set_solver.
             intros v'' t'' Hkt'. 
             rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia.
             destruct H' as [_ H''].
             apply (Nat.le_trans _ T _); try lia.
             apply (H'' v''). try done.
      + destruct HP as [H' | H'].
        * left. intros v t. set_solver.
        * right. destruct H' as [v [T H']].
          exists v, T. destruct H' as [H' H''].
          split. set_solver. intros v'' t''.
          intros Hkt'. rewrite elem_of_union in Hkt'*; intros Hkt'.
          destruct Hkt' as [Hkt' | Hkt'].
          rewrite elem_of_singleton in Hkt'*; intros Hkt'.
          inversion Hkt'. done. apply (H'' v''); try done.
  Qed.
  
  Lemma map_of_set_lookup_some (H: gset KVT) k v t :
          unique_val H →    
            (k, v, t) ∈ H → is_Some(map_of_set H !! k).
  Proof.
    intros Uniq Hkt.
    pose proof map_of_set_lookup_some_aux H k Uniq as Hkt'.
    destruct Hkt' as [Hkt' | Hkt'].
    { pose proof Hkt' v t as H'. set_solver. }
    pose proof (map_of_set_lookup_cases H k) as H'.
    destruct H' as [H' | H'].
    - destruct H' as [v' [T' H']].
      destruct H' as [_ [_ H']].
      rewrite H'. by exists (v',T').
    - destruct Hkt' as [v' [T Hkt']].
      destruct Hkt' as [Hkt' _].
      destruct H' as [H' _].
      pose proof H' v' T as H'.
      set_solver.
  Qed.
  
  Lemma map_of_set_lookup_lb H k v t :
    (k, v, t) ∈ H → t ≤ (map_of_set H !!! k).2.
  Proof. 
    intros kt_in_H.
    pose proof map_of_set_lookup_cases H k as [H' | H'].
    - destruct H' as [V [T [kT_in_H [H' H_k]]]].
      rewrite lookup_total_alt. rewrite H_k.
      simpl. apply (H' v); try done.
    - destruct H' as [H' _].
      pose proof H' v t as H'.
      contradiction.
  Qed.
  
  Lemma set_of_map_member_ne (C: gmap K (V*TS)) k :
            C !! k = None →
              ∀ v t, (k, v, t) ∉ set_of_map C.
  Proof.  
    set (P := λ (s: gset KVT) (m: gmap K (V*TS)),
                   m !! k = None → ∀ v t, (k, v, t) ∉ s).
    apply (map_fold_ind P); try done.
    intros kx tx m r Hm HP. unfold P.
    unfold P in HP. destruct (decide (kx = k)).
    - subst kx. rewrite lookup_insert. try done.
    - rewrite lookup_insert_ne; try done.
      intros Hm'. pose proof HP Hm' as HP.
      intros v t. intros Hnot.
      rewrite elem_of_union in Hnot*; intros Hnot.
      destruct Hnot as [Hnot | Hnot].
      + by apply HP in Hnot.
      + rewrite elem_of_singleton in Hnot*; intros Hnot.
        inversion Hnot. try done.
  Qed.
  
  Lemma map_of_set_union_ne H k v t k' :
          unique_val H → k' ≠ k → 
            map_of_set (H ∪ {[(k, v, t)]}) !! k' = map_of_set H !! k'.
  Proof.
    intros Uniq Hk.
    pose proof (map_of_set_lookup_cases H k') as Hp.
    pose proof (map_of_set_lookup_cases (H ∪ {[(k, v, t)]}) k') as Hu.
    destruct Hp as [Hp | Hp].
    - destruct Hu as [Hu | Hu].
      + destruct Hp as [v0 [T [Hp1 [Hp2 Hp3]]]].
        destruct Hu as [v0' [T' [Hu1 [Hu2 Hu3]]]].
        assert (T ≤ T') as Ht1.
        { assert ((k', v0, T) ∈ H ∪ {[k, v, t]}) as Ht by set_solver.
          by pose proof Hu2 v0 T Ht. }
        assert (T' ≤ T) as Ht2.
        { assert ((k', v0', T') ∈ H) as Ht by set_solver.
          by pose proof Hp2 v0' T' Ht. }
        rewrite Hp3 Hu3. assert (T = T') as Ht by lia.
        subst T'. assert ((k', v0', T) ∈ H) as H'.
        { clear -Hu1 Hk; set_solver. }
        pose proof Uniq k' v0 v0' T Hp1 H' as Uniq.
        by rewrite Uniq.
      + destruct Hp as [v0 [T [Hp1 [Hp2 Hp3]]]].
        destruct Hu as [Hu1 Hu2].
        pose proof Hu1 v0 T as Hu1. set_solver.
    - destruct Hu as [Hu | Hu].
      + destruct Hp as [Hp1 Hp2].
        destruct Hu as [v0 [T' [Hu1 [Hu2 Hu3]]]].
        pose proof Hp1 v0 T' as Hp1. set_solver.
      + destruct Hp as [Hp1 Hp2].
        destruct Hu as [Hu1 Hu2].
        by rewrite Hp2 Hu2.
  Qed.
  
  Lemma map_of_set_insert_eq (C: gmap K (V*TS)) k v t H :
        unique_val H →
          (∀ v' t', (k, v', t') ∈ H → t' < t) →
            C = map_of_set H →
              <[k := (v, t)]> C = map_of_set (H ∪ {[(k, v, t)]}).
  Proof.
    intros Uniq Hmax Hc. apply map_eq. intros k'.
    destruct (decide (k' = k)).
    - replace k'. rewrite lookup_insert.
      rewrite (map_of_set_lookup _ _ v t); try done.
      { intros k0 v0 v0' t0. rewrite !elem_of_union.
        intros [Hkvt0 | Hkvt0]; intros [Hkvt0' | Hkvt0'].
        - by pose proof Uniq k0 v0 v0' t0 Hkvt0 Hkvt0'.
        - assert ((k0, v0', t0) = (k, v, t)) as H' by set_solver.
          inversion H'. subst k0 v0' t0.
          pose proof Hmax v0 t Hkvt0 as Hmax. lia.
        - assert ((k0, v0, t0) = (k, v, t)) as H' by set_solver.
          inversion H'. subst k0 v0 t0.
          pose proof Hmax v0' t Hkvt0' as Hmax. lia.
        - assert ((k0, v0, t0) = (k0, v0', t0)) as H' by set_solver.
          by inversion H'. }  
      set_solver. intros v' t'. rewrite elem_of_union.
      intros [Hk | Hk]. pose proof Hmax v' t' Hk. lia.
      assert (t' = t) by set_solver. by replace t'.
    - rewrite map_of_set_union_ne; try done.
      rewrite lookup_insert_ne; try done.
      by rewrite Hc.
  Qed.
  
  Lemma set_of_map_member (C: gmap K (V*TS)) k v t :
            C !! k = Some((v, t)) →
              (k, v, t) ∈ set_of_map C.
  Proof.
    intros Hc. unfold set_of_map.
    set (P := λ (s: gset KVT) (m: gmap K (V*TS)),
                  ∀ j v x, m !! j = Some (v, x) → (j, v, x) ∈ s).
    apply (map_fold_ind P); try done.
    intros i x m s Hmi Hp. unfold P.
    intros j v' x'. destruct (decide (i = j)).
    - replace j. rewrite lookup_insert.
      intros H'; inversion H'. set_solver.
    - rewrite lookup_insert_ne; try done.
      pose proof Hp j v' x' as Hp'. set_solver.
  Qed.
  
  Lemma set_of_map_member_rev (C: gmap K (V*TS)) k v t :
            (k, v, t) ∈ set_of_map C →
                C !! k = Some((v, t)).
  Proof.
    set (P := λ (s: gset KVT) (m: gmap K (V*TS)),
                  ∀ k v t, (k, v, t) ∈ s → m !! k = Some (v, t)).
    apply (map_fold_ind P); try done.
    intros k' vt m r Hmi Hp. unfold P.
    intros k0 v0 t0 Hkvt0. destruct (decide (k0 = k')).
    - subst k0. rewrite lookup_insert.
      rewrite elem_of_union in Hkvt0*; intros Hkvt0.
      destruct Hkvt0 as [Hkvt0 | Hkvt0].
      unfold P in Hp. pose proof Hp k' v0 t0 Hkvt0 as Hp.
      rewrite Hp in Hmi. inversion Hmi.
      assert ((v0, t0) = (vt.1, vt.2)) as H' by set_solver.
      inversion H'. destruct vt as [v' t']; by simpl.
    - assert ((k0, v0, t0) ∈ r) as Hj by set_solver.
      pose proof Hp k0 v0 t0 Hj as Hp.
      rewrite lookup_insert_ne; try done.
  Qed.
  
  Lemma set_of_map_insert_subseteq (C: gmap K (V*TS)) k v t :
    set_of_map (<[k := (v, t)]> C) ⊆ set_of_map C ∪ {[(k, v, t)]}.
  Proof.
    intros [[k' v'] t'] Hkt. destruct (decide (k' = k)).
    - subst k'.
      apply set_of_map_member_rev in Hkt.
      rewrite lookup_insert in Hkt.
      inversion Hkt. set_solver.
    - apply set_of_map_member_rev in Hkt.
      rewrite lookup_insert_ne in Hkt; try done.
      apply set_of_map_member in Hkt.
      set_solver.
  Qed.

End multicopy_util.
