(* LSM Tree : Upsert *)

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
Require Export lsm_util.

Module Type LSM_UPSERT.
  Declare Module UTIL : LSM_UTIL.
  Export UTIL UTIL.DEFS UTIL.DEFS.DS UTIL.DEFS.DS.NODE.

  Lemma upsertOp_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r (p: proph_id) 
    pvs tid t0 Q k v :
      main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
      thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
      □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
      ⌜local_pre (upsertOp k v)⌝ -∗
        {{{ proph p pvs ∗ 
            (match process_proph tid pvs with
              contra => au Σ Hg1 Hg2 Hg3 N γ_r (upsertOp k v) Q
            | no_upd => True
            | upd => au Σ Hg1 Hg2 Hg3 N γ_r (upsertOp k v) Q end) }}}
              upsert #p #r #k #v @ ⊤
        {{{ (res: resT) prf pvs', RET #res;
            proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
            (match process_proph tid pvs with
              contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
            | no_upd => past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (upsertOp k v) res t0
            | upd => Q #res ∨ 
                ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd %k_in_KS". iLöb as "IH". 
    iIntros (Φ) "!# (Hproph & Hmatch) Hpost".
    wp_lam. wp_pures. awp_apply lockNode_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜per_tick_inv r s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iAssert (⌜r ∈ FP s0⌝)%I as %FP_r0.
    { iPureIntro. apply PT_s0.  }
    rewrite /resources. rewrite (big_sepS_delete _ (FP s0) r); last by eauto.
    iDestruct "Res" as "(Res_r & Res_rest)".
    iDestruct "Res_r" as (b γr) "(#Hghr & Hlf & Lock_r)".
    iAaccIntro with "Lock_r".
    { iIntros "Lock_r". iModIntro. iFrame "∗". iNext. iExists M0, T0, s0.
      iFrame "∗%". rewrite /resources. 
      rewrite (big_sepS_delete _ (FP s0) r); last by eauto. iFrame.
      iExists b, γr. iFrame "Hghr ∗".  }
    iIntros "(Lock_r & (Node_r & Hlff))".
    iModIntro. iSplitR "Hproph Hmatch Hpost Node_r Hlff". 
    { iNext. iExists M0, T0, s0. iFrame "∗%". rewrite /resources. 
      rewrite (big_sepS_delete _ (FP s0) r); last by eauto. iFrame. 
      iExists true, γr. iFrame "Hghr ∗". }
    clear b. wp_pures. wp_apply (addContents_spec with "[Node_r]"). 
    { iFrame "Node_r". by iPureIntro. }
    iIntros (succ Vn')"(Node_r & Hsucc)". wp_pures. destruct succ; last first.
    - wp_pures. iDestruct "Hsucc" as %->. awp_apply unlockNode_spec.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iAssert (⌜per_tick_inv r s1⌝)%I as %PT_s1.
      { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
      iAssert (⌜r ∈ FP s1⌝)%I as %FP_r1.
      { iPureIntro. apply PT_s1. }
      rewrite /resources. rewrite (big_sepS_delete _ (FP s1) r); last by eauto.
      iDestruct "Res" as "(Res_r & Res_rest)".
      iDestruct "Res_r" as (b γr') "(#Hghr' & Hlf & Lock_r)".
      iAssert (⌜γr' = γr⌝)%I as %->. 
      { iPoseProof (ghost_heap_sync with "Hghr Hghr'") as "%"; try done. } 
      iClear "Hghr'". iAssert (⌜b = true⌝)%I as %->.
      { destruct b; try done. iExFalso. iDestruct "Lock_r" as "(H' & H'' & _)".
        iApply (node_sep_star with "[Node_r H'']"). iFrame. }
      iAssert (⌜ES s1 r = ES s0 r ∧ VN s1 r = VN s0 r⌝)%I as %[ES_01 VN_01]. 
      { iPoseProof (frac_sync with "Hlf Hlff") as "%"; try done. }
      iCombine "Lock_r Node_r Hlff" as "H'". iEval (rewrite ES_01 VN_01) in "H'".
      iAaccIntro with "H'".
      { iIntros "(Lock_r & Node_r & Hlff)". iModIntro. iFrame "∗". iNext. 
        iExists M1, T1, s1. iFrame "∗%". rewrite /resources. 
        rewrite (big_sepS_delete _ (FP s1) r); last by eauto. 
        iFrame. iExists true, γr. iFrame "Hghr ∗". }
      iIntros "Lock_r". iModIntro. iSplitR "Hpost Hmatch Hproph". 
      { iNext. iExists M1, T1, s1. iFrame "∗%". rewrite /resources. 
        rewrite (big_sepS_delete _ (FP s1) r); last by eauto. iFrame. 
        iExists false, γr. iFrame "Hghr ∗". rewrite ES_01 VN_01. done. }
      wp_pures. iApply ("IH" with "[$Hmatch $Hproph]"); try done.
    - wp_pure credit: "Hc". iDestruct "Hsucc" as %Def_Vn'. 
      wp_apply (wp_resolve with "Hproph"). rewrite /=. done.
      wp_pures. iModIntro. iIntros (pvs')"%Def_pvs Hproph". wp_pures.
      
      awp_apply unlockNode_spec.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)". 
      iAssert (⌜per_tick_inv r s1⌝)%I as %PT_s1.
      { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
      iAssert (⌜r ∈ FP s1⌝)%I as %FP_r1.
      { iPureIntro. apply PT_s1. }
      rewrite /resources. rewrite (big_sepS_delete _ (FP s1) r); last by eauto.
      iDestruct "Res" as "(Res_r & Res_rest)".
      iDestruct "Res_r" as (b γr') "(#Hghr' & Hlf & Lock_r)".
      iAssert (⌜γr' = γr⌝)%I as %->. 
      { iPoseProof (ghost_heap_sync with "Hghr Hghr'") as "%"; try done. } 
      iClear "Hghr'". iAssert (⌜b = true⌝)%I as %->.
      { destruct b; try done. iExFalso. iDestruct "Lock_r" as "(H' & H'' & _)".
        iApply (node_sep_star with "[Node_r H'']"). iFrame. }
      iAssert (⌜ES s1 r = ES s0 r ∧ VN s1 r = VN s0 r⌝)%I as %[ES_01 VN_01]. 
      { iPoseProof (frac_sync with "Hlf Hlff") as "%"; try done. }

      iAssert (lockR Σ Hg1 true r (node Σ Hg1 r r (ES s1 r) (Vn') 
                      ∗ lock_frac Σ Hg1 Hg2 γr (ES s1 r) (VN s1 r)) 
                ∗ node Σ Hg1 r r (ES s1 r) (Vn')
                ∗ lock_frac Σ Hg1 Hg2 γr (ES s1 r) (VN s1 r))%I with "[Node_r Lock_r Hlff]" as "H'".
      { rewrite ES_01. rewrite VN_01. iFrame. }
      iAaccIntro with "H'".
      { iIntros "(Lock_r & Node_r & Hlff)". iModIntro. rewrite ES_01 VN_01. 
        iFrame "∗". iNext. iExists M1, T1, s1. iFrame "∗%". rewrite /resources. 
        rewrite (big_sepS_delete _ (FP s1) r); last by eauto. 
        iFrame. iExists true, γr. rewrite ES_01 VN_01. iFrame "Hghr ∗". }

      iIntros "Lock_r". iApply (lc_fupd_add_later with "Hc"). iNext.

      iDestruct "SShot1" as %[FP1 [C1 [ES1 [VN1 [TN1 [QN1 [BN1 [I1 [J1 [Hs1 
        [Dom_ES1 [Dom_VN1 [Dom_TN1 [Dom_QN1 [Dom_BN1 [Dom_I1 Dom_J1]]]]]]]]]]]]]]]].

      set C1' := <[k := v]> C1.
      set VN1' := <[r := Vn']> VN1.
      set Tn' := <[k := T1+1]> (TN s1 r).
      set TN1' := <[r := Tn']> TN1.
      set Bn' := <[k := (v, T1+1)]> (BN s1 r).
      set BN1' := <[r := Bn']> BN1.
      set s1' := (FP1, C1', ES1, VN1', TN1', QN1, BN1', I1, J1) : snapshot.
      set M1' := <[T1 + 1 := s1']> M1.

      assert (FP s1' = FP s1) as FP_s1'.
      { by rewrite /FP /s1' Hs1. }
      assert (abs s1' = <[k := v]> (abs s1)) as Habs'.
      { by rewrite /abs /s1' Hs1. }
      assert (∀ n, ES s1' n = ES s1 n) as HES.
      { by rewrite /ES /s1' Hs1 /=. }
      assert (∀ n, n ≠ r → VN s1' n = VN s1 n) as HVN.
      { intros n Hnr. rewrite /s1' Hs1 /VN /= /VN1' lookup_insert_ne; try done. }
      assert (VN s1' r = <[k:=v]> (VN s1 r)) as HVNr.
      { rewrite /s1' Hs1 /VN /= /VN1' lookup_insert Def_Vn' -VN_01. 
        rewrite Hs1 /VN /=. done. }
      assert (∀ n, n ≠ r → TN s1' n = TN s1 n) as HTN.
      { intros n Hnr. rewrite /s1' Hs1 /TN /= /TN1' lookup_insert_ne; try done. }
      assert (TN s1' r = <[k:=T1+1]> (TN s1 r)) as HTNr.
      { rewrite /s1' Hs1 /TN /= /TN1' lookup_insert /Tn'. rewrite Hs1 /TN /=. done. }
      assert (∀ n, QN s1' n = QN s1 n) as HQN.
      { by rewrite /QN /s1' Hs1 /=. }
      assert (∀ n, n ≠ r → BN s1' n = BN s1 n) as HBN.
      { intros n Hnr. rewrite /s1' Hs1 /BN /= /BN1' lookup_insert_ne; try done. }
      assert (BN s1' r = <[k:=(v, T1+1)]> (BN s1 r)) as HBNr.
      { rewrite /s1' Hs1 /BN /= /BN1' lookup_insert /Bn'. rewrite Hs1 /BN /=. done. }
      assert (∀ n, FI s1' n = FI s1 n) as HI.
      { by rewrite /FI /s1' Hs1 /=. }
      assert (∀ n, FJ s1' n = FJ s1 n) as HJ.
      { by rewrite /FJ /s1' Hs1 /=. }

      iAssert (⌜dom M1 = gset_seq 0 T1⌝)%I as %Dom_M1. 
      { by iDestruct "Hist" as (M1'') "(_&_&%&_)". }
      assert (dom M1' = dom M1 ∪ {[T1+1]}) as Dom_M1'.
      { rewrite /M1' dom_insert_L. clear; set_solver. }  
      assert ((T1+1) ∉ dom M1) as T1_M1.
      { intros H'. rewrite Dom_M1 elem_of_gset_seq in H'. clear -H'; lia. }
      
      assert ((BN s1 r !!! k).2 ≤ T1) as BN_k_le_T1.
      { destruct Trans_M1 as (_&H'&_). 
        pose proof H' r k ((BN s1 r !!! k).1) ((BN s1 r !!! k).2) T1 as H'.
        assert (T1 ∈ dom M1) as H1'. { rewrite Dom_M1 elem_of_gset_seq. clear; lia. }
        assert (BN (M1 !!! T1) r !!! k = ((BN s1 r !!! k).1, (BN s1 r !!! k).2)) 
          as H1''. { rewrite leibniz_equiv_iff in Habs1. rewrite Habs1. 
          destruct (BN s1 r !!! k); try done. }
        pose proof H' H1' H1'' as H'. clear -H'; lia. }
      assert (node_inv_pure r (ES s1' r) (VN s1' r) (TN s1' r) 
        (QN s1' r) (BN s1' r) (FI s1' r) (FJ s1' r)) as Hr.
      { rewrite HES HQN HI HJ HVNr HTNr HBNr. apply PT_s1 in FP_r1.
        destruct FP_r1 as (Hn1&Hn2&Hn3&Hn4&Hn5). 
        split; last split; last split; last split.
        - intros k' Hk'. destruct (decide (k' = k)) as [-> | Hkk].
          + split. intros _. rewrite lookup_insert !lookup_total_insert. done.
            rewrite dom_insert_L. intros H'; clear -H'; set_solver.
          + rewrite dom_insert_L elem_of_union elem_of_singleton. split.
            intros [H' | H']; try done. rewrite lookup_insert_ne; try done.
            rewrite !lookup_total_insert_ne; try done. apply Hn1; try done.
            intros H'. apply Decidable.not_or in H'.
            destruct H' as [_ H']. rewrite lookup_insert_ne; try done.
            apply Hn1; try done.
        - apply Hn2.
        - intros k' Hk'. destruct (decide (k' = k)) as [-> | Hkk].
          + rewrite lookup_total_insert /=. pose proof Hn3 k Hk' as Hn3.
            clear -Hn3 BN_k_le_T1. lia.
          + rewrite lookup_total_insert_ne; try done. apply Hn3; try done.
        - rewrite !dom_insert_L Hn4. done.
        - destruct Hn5 as (Hf1&Hf2&Hf3&Hf4&Hf5&Hf6&Hf7&Hf8&Hf9). 
          split; last split; last split; last split; last split; last split; 
            last split; last split; try done.
          intros k' v' t' Hk' Hinset. destruct PT_s1 as ((_&H'&_)&_).
          rewrite H' in Hinset. clear -Hinset. set_solver.
          intros k' Hk'. destruct PT_s1 as ((_&_&H')&_). right. rewrite H'. done. }
      assert (per_tick_inv r s1') as PT_s1'. 
      { destruct PT_s1 as (PT1'&PT2'&PT3'&PT4'&PT5').
        split; last split; last split; last split.
        - rewrite FP_s1' HI HJ. done.
        - assert (GFI s1' = GFI s1) as ->.
          { rewrite /GFI FP_s1'. apply big_opS_ext. intros x Hx. by rewrite HI. }
          assert (GFJ s1' = GFJ s1) as ->.
          { rewrite /GFJ FP_s1'. apply big_opS_ext. intros x Hx. by rewrite HJ. }
          done.
        - intros k'. rewrite Habs' HBNr. destruct (decide (k' = k)) as [-> | Hkk'].
          + rewrite !lookup_total_insert /=. done.
          + rewrite !lookup_total_insert_ne; try done.
        - intros n Hn. rewrite FP_s1' in Hn. 
          destruct (decide (n = r)) as [-> | Hnr]; try done.
          rewrite HES HQN HI HJ HVN; try done. rewrite HTN; try done. 
          rewrite HBN; try done. by apply PT4'.
        - intros n n'. rewrite FP_s1' HES. apply PT5'. }

      assert (transition_inv r M1' (T1 + 1)) as Trans_M1'. 
      { destruct Trans_M1 as (HT1&HT2&HT3). split; last split.
        - intros n k' v' t' t''. rewrite Dom_M1' elem_of_union elem_of_singleton.
          intros [Ht'' | ->]. 
          + assert (M1' !!! t'' = M1 !!! t'') as ->.
            { rewrite /M1' lookup_total_insert_ne. done. clear -T1_M1 Ht''; set_solver. }
            intros H'. assert (H'' := H'). apply HT1 in H''; try done.
            assert (M1' !!! t' = M1 !!! t') as ->. 
            { rewrite /M1'. rewrite lookup_total_insert_ne. done.
              apply lookup_total_correct in H'. apply HT2 in H'. 
              rewrite Dom_M1 elem_of_gset_seq in Ht''. clear -Ht'' H'. lia. done. }
            apply H''.
          + destruct (decide (k' = k ∧ n = r)) as [[-> ->] | Hkk'].
            * intros H'. assert (v' = v ∧ t' = T1+1) as [-> ->].
              { rewrite /M1' lookup_total_insert HBNr lookup_insert in H'.
                inversion H'. done. } done.
            * assert (BN (M1' !!! (T1 + 1)) n !! k' = BN (M1 !!! T1) n !! k') as H'.
              { rewrite /M1' lookup_total_insert. rewrite leibniz_equiv_iff in Habs1.
                rewrite Habs1. destruct (decide (n = r)) as [-> | Hnr].
                destruct (decide (k' = k)) as [-> | Hk']. exfalso. by apply Hkk'. 
                rewrite HBNr lookup_insert_ne; try done. rewrite HBN; try done. }
              intros H''. assert (H1' := H''). rewrite H' in H'' H1'.
              apply HT1 in H''. apply lookup_total_correct in H1'. apply HT2 in H1'.
              assert (M1' !!! t' = M1 !!! t') as ->. 
              { rewrite /M1' lookup_total_insert_ne. done. clear -H1'; lia. }
              done. all : (rewrite Dom_M1 elem_of_gset_seq; clear; lia).
        - intros n k' v' t' t''. rewrite Dom_M1' elem_of_union elem_of_singleton.
          intros [Ht'' | ->].
          + assert (M1' !!! t'' = M1 !!! t'') as ->.
            { rewrite /M1' lookup_total_insert_ne. done. clear -T1_M1 Ht''; set_solver. }
            intros H'%HT2. all: done.
          + destruct (decide (k' = k ∧ n = r)) as [[-> ->] | Hkk'].
            * intros H'. assert (v' = v ∧ t' = T1+1) as [-> ->].
              { rewrite /M1' lookup_total_insert HBNr lookup_total_insert in H'.
                inversion H'. done. } done.
            * assert (BN (M1' !!! (T1 + 1)) n !!! k' = BN (M1 !!! T1) n !!! k') as H'.
              { rewrite /M1' lookup_total_insert. rewrite leibniz_equiv_iff in Habs1.
                rewrite Habs1. destruct (decide (n = r)) as [-> | Hnr].
                destruct (decide (k' = k)) as [-> | Hk']. exfalso. by apply Hkk'. 
                rewrite HBNr lookup_total_insert_ne; try done. rewrite HBN; try done. }
              rewrite H'. intros H''%HT2. clear -H''; lia. 
              rewrite Dom_M1 elem_of_gset_seq. clear; lia.
        - intros t Ht. destruct (decide (t = T1)) as [-> | Ht'].
          + rewrite /=. assert (M1' !!! T1 = s1) as ->. 
            { rewrite /M1' lookup_total_insert_ne. by apply leibniz_equiv.
              clear; lia. }
            assert (M1' !!! (T1+1) = s1') as ->. 
            { rewrite /M1' lookup_total_insert. done. }
            split; last split; last first. intros ?; rewrite HJ. done. 
            all: try by rewrite FP_s1'. intros n k'.
            destruct (decide (n = r)) as [-> | Hnr].
            * destruct (decide (k' = k)) as [-> | Hk].
              right. rewrite HBNr lookup_total_insert /=. clear -BN_k_le_T1; lia.
              left. rewrite HBNr lookup_total_insert_ne; try done.
            * left. rewrite HBN; try done.
          + rewrite /=. assert (M1' !!! t = M1 !!! t) as ->. 
            { rewrite /M1' lookup_total_insert_ne. done. lia. }
            assert (M1' !!! (t+1) = M1 !!! (t+1)) as ->.
            { rewrite /M1' lookup_total_insert_ne. done. lia. }
            apply HT3. lia. }


      iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> Φ #0 ∗ dsRepI _ _ _ _ γ_r (abs s1'))%I 
        with "[Hpost Hmatch Hproph Ds]" as ">(HΦ & Ds)".
      { destruct (process_proph tid pvs) eqn: H'. 
        - iMod "Hmatch" as (a)"[DsR [_ H']]".
          iCombine "DsR Ds" as "H''".
          iAssert (⌜a = abs s1⌝)%I as %->. 
          { iPoseProof (own_valid with "[$H'']") as "%H''".
            rewrite frac_agree_op_valid_L in H''. iPureIntro; apply H''. }
          iEval (rewrite <-frac_agree_op) in "H''".
          iEval (rewrite Qp.half_half) in "H''".
          iMod ((own_update γ_r (to_frac_agree 1 (abs s1)) 
            (to_frac_agree 1 (abs s1'))) with "[$H'']") as "H''".
          { apply cmra_update_exclusive. 
            rewrite /valid /cmra_valid /= /prod_valid_instance.
            split; simpl; try done. }
          iEval (rewrite -Qp.half_half) in "H''".
          iEval (rewrite frac_agree_op) in "H''".
          iDestruct "H''" as "(Ds & DsR)".
          iSpecialize ("H'" $! (abs s1') 0%Z).
          iMod ("H'" with "[$DsR]") as "HQ". { by iPureIntro. } iFrame "Ds". 
          iApply ("Hpost" $! 0%Z [((#(), #true)%V, #())] pvs'). 
          iFrame "Hproph". iModIntro. iPureIntro. rewrite Def_pvs.
          clear. split; try done. rewrite Forall_singleton. intros H'.
          rewrite /= in H'. inversion H'.
        - iMod "Hmatch" as (a)"[DsR [_ H']]".
          iCombine "DsR Ds" as "H''".
          iAssert (⌜a = abs s1⌝)%I as %->. 
          { iPoseProof (own_valid with "[$H'']") as "%H''".
            rewrite frac_agree_op_valid_L in H''. iPureIntro; apply H''. }
          iEval (rewrite <-frac_agree_op) in "H''".
          iEval (rewrite Qp.half_half) in "H''".
          iMod ((own_update γ_r (to_frac_agree 1 (abs s1)) 
            (to_frac_agree 1 (abs s1'))) with "[$H'']") as "H''".
          { apply cmra_update_exclusive. 
            rewrite /valid /cmra_valid /= /prod_valid_instance.
            split; simpl; try done. }
          iEval (rewrite -Qp.half_half) in "H''".
          iEval (rewrite frac_agree_op) in "H''".
          iDestruct "H''" as "(Ds & DsR)".
          iSpecialize ("H'" $! (abs s1') 0%Z).
            iMod ("H'" with "[$DsR]") as "HQ". { by iPureIntro. } iFrame "Ds". 
          iApply ("Hpost" $! 0%Z [((#(), #true)%V, #())] pvs'). 
          iFrame "Hproph". iModIntro. iSplitR. iPureIntro. rewrite Def_pvs.
          clear. try done. by iLeft.
        - exfalso. rewrite Def_pvs in H'. clear -H'. apply process_proph_no_upd in H'.
          destruct H' as [i [x [Hi Htake]]].
          destruct (decide (i = 0)) as [-> | Hi0].
          { rewrite /= in Hi. inversion Hi. }
          assert (take i (((#(), #true)%V, #()) :: pvs') !! 0 = 
            Some (((#(), #true)%V, #()))) as H'. 
          { rewrite lookup_take; try done. lia. }
          apply (Forall_lookup_1 _ _ _ _ Htake) in H'.
          destruct H' as [H' _]. apply H'; rewrite /is_snd /=. by exists #(). }

      iAssert (|==> hist _ _ _ _ γ_t γ_m M1' (T1+1))%I with "[Hist]" as ">Hist".
      { iPoseProof (hist_upd _ _ _ _ _ _ _ _ _ s1' with "[%] [%] [$Hist]") as ">H'".
        apply  Habs1. intros <-. rewrite map_eq_iff in HBNr. 
        pose proof HBNr k as HBNr. rewrite lookup_insert in HBNr.
        apply lookup_total_correct in HBNr. rewrite HBNr /= in BN_k_le_T1.
        clear -BN_k_le_T1; lia. by iModIntro. }
      iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> helping_inv _ _ _ _ N γ_t γ_r γ_mt γ_msy M1' 
        ∗ dsRep _ _ _ _ γ_r (abs s1'))%I with
        "[Help Ds]" as ">(Help & Ds)".
      { iMod (fupd_mask_subseteq (⊤ ∖ ↑cntrN N)) as "H'". { clear; set_solver. }
        iPoseProof ("Upd" with "[%] [Ds] [Help]") as ">Help"; try done.
        apply leibniz_equiv in Habs1. iMod "H'" as "_". by iModIntro. }
      
      iDestruct "Lock_r" as "(Hl & Node_r & Hlff)". unfold lock_frac.
      iCombine "Hlf Hlff" as "H'". iEval (rewrite ES_01 VN_01) in "H'".
      iEval (rewrite -frac_agree_op Qp.half_half) in "H'".
      iMod (own_update γr 
        (to_frac_agree 1 ((ES s0 r: esTUR), (VN s0 r:V_contentsUR))) 
        (to_frac_agree 1 ((ES s1' r: esTUR), (VN s1' r:V_contentsUR))) 
        with "[H']") as "H'".
      { apply cmra_update_exclusive. 
        rewrite /valid /cmra_valid /=. unfold prod_valid_instance. rewrite /=.
        split; try done. }
      { iFrame "H'". }
      iEval (rewrite -Qp.half_half frac_agree_op) in "H'".
      iDestruct "H'" as "(Hlf & Hlff)".
      
      iAssert (resources _ _ _ r s1') with "[Hl Node_r Hlf Hlff Res_rest]" as "Res".
      { rewrite /resources FP_s1'. 
        rewrite (big_sepS_delete _ (FP s1) r); last by eauto. 
        iSplitR "Res_rest". iExists false, γr. rewrite HES HVNr Def_Vn' VN_01. 
        iFrame "#". iFrame "∗".
        iApply (big_sepS_mono with "Res_rest"); try done.
        iIntros (x)"%Hx H'". assert (x ≠ r) as Hxr by (clear -Hx; set_solver).
        iDestruct "H'" as (b γ)"H'". iExists b, γ. rewrite HES HVN; try done. }
      iAssert (⌜snapshot_constraints s1'⌝)%I as "SShot1'".
      { iPureIntro. exists FP1, C1', ES1, VN1', TN1', QN1, BN1', I1, J1.
        rewrite Hs1 /= in FP_r1. repeat split; try done.
        rewrite /VN1'. rewrite dom_insert_L. clear -FP_r1 Dom_VN1. set_solver.
        rewrite /TN1'. rewrite dom_insert_L. clear -FP_r1 Dom_TN1. set_solver.
        rewrite /BN1'. rewrite dom_insert_L. clear -FP_r1 Dom_BN1. set_solver. }
      iModIntro. iSplitR "HΦ".
      { iNext. iExists M1', (T1+1), s1'. iFrame "∗%#". iPureIntro. split.
        rewrite /M1' lookup_total_insert. done. intros t Ht.
        destruct (decide (t = T1 + 1)) as [-> | Ht']. rewrite /M1' lookup_total_insert.
        done. rewrite /M1' lookup_total_insert_ne. apply PT1. lia. lia. }
      wp_pures. done. Unshelve. try done.  
  Qed.

End LSM_UPSERT.
