(* LSM Tree : Search *)

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
Require Export flows_big_op lsm_util.

Module Type LSM_SEARCH.
  Declare Module UTIL : LSM_UTIL.
  Export UTIL UTIL.DEFS UTIL.DEFS.DS UTIL.DEFS.DS.NODE.

  Definition traversal_inv Σ Hg1 Hg2 Hg3 γ_m r t0 n k v t : iProp Σ := 
    (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ ⌜BN s r !!! k = (v, t)⌝)
  ∗ (∃ s, past_state Σ Hg1 Hg2 Hg3 γ_m t0 s 
          ∗ ⌜n ∈ FP s ∧ k ∈ inset _ (FJ s n) n ∧ BN s n !!! k = (v, t)⌝). 
  

  Lemma traverse_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r (p: proph_id) 
    tid t0 k (n: Node) v t :
      main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
      thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
      □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
      ⌜k ∈ KS⌝ -∗
        {{{ traversal_inv Σ Hg1 Hg2 Hg3 γ_m r t0 n k v t }}}
              traverse #n #k @ ⊤
        {{{ (res: resT), RET #res; 
            past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (searchOp k) res t0 }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd %k_in_KS". iLöb as "IH" forall (n v t). 
    iIntros (Φ) "!# #(Habs & HBN) Hpost".
    wp_lam. wp_pures. awp_apply lockNode_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (⌜n ∈ FP s0⌝)%I as %FP_n0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "HBN" as (s)"(Past_s & %H' & %H'')".
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
    rewrite /resources. rewrite (big_sepS_delete _ (FP s0) n); last by eauto.
    iDestruct "Res" as "(Res_n & Res_rest)".
    iDestruct "Res_n" as (b γn) "(#Hghn & Hlf & Lock_n)".
    iAaccIntro with "Lock_n".
    { iIntros "Lock_n". iModIntro. iFrame "Hpost". iNext. iExists M0, T0, s0.
      iFrame "∗%". rewrite /resources. 
      rewrite (big_sepS_delete _ (FP s0) n); last by eauto. iFrame.
      iExists b, γn. iFrame "Hghn ∗".  }
    iIntros "(Lock_n & (Node_n & Hlff))".
    iAssert (⌜per_tick_inv r s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iPoseProof (snapshot_current with "[%] [#] [$]") 
      as ">(#Past_s0&Hist)"; try done.
    
    set tb := (BN s0 n !!! k).2.
    set sb := M0 !!! tb.
    iAssert (⌜T0 ∈ dom M0⌝)%I as %T0_in_M0.
    { iDestruct "Hist" as (M')"(_&_&%H''&_)". iPureIntro.
      rewrite H'' elem_of_gset_seq. clear; lia. }
    assert (tb ≤ T0) as tb_le_T0.
    { destruct Trans_M0 as (_&H'&_). 
      pose proof H' n k (BN s0 n !!! k).1 (BN s0 n !!! k).2 T0 T0_in_M0 as H'.
      rewrite leibniz_equiv_iff in Habs0. rewrite Habs0 -/tb in H'.
      apply H'. destruct (BN s0 n !!! k); try done. }
    iAssert (|==> own γ_m (◯ {[tb := to_agree sb]}) 
      ∗ hist Σ Hg1 Hg2 Hg3 γ_t γ_m M0 T0)%I with "[Hist]" as ">(#Past_sb & Hist)".
    { iPoseProof (history_dom Σ Hg1 Hg2 Hg3 tb with "Hist") as "%Hdom".
      iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
      assert (0 ≤ tb ≤ T0) as Dom_tb by lia. apply Hdom in Dom_tb.
      apply elem_of_dom in Dom_tb. destruct Dom_tb as [s' Dom_tb].
      assert (s' = sb) as ->. { apply lookup_total_correct in Dom_tb.
        rewrite /sb. done. }
      apply M_eq in Dom_tb. 
      iPoseProof (own_update _ (● M') (● M' ⋅ ◯ {[tb := to_agree sb]}) with "HM'") 
        as ">(HM' & #Htb)". 
      { apply auth_update_alloc, local_update_unital_discrete. 
        intros z Hm Hz. split; try done. rewrite left_id in Hz. rewrite -Hz.
        apply map_equiv_iff. intros x. destruct (decide (x = tb)) as [-> | Hxz].
        - rewrite lookup_op Dom_tb lookup_insert. rewrite /op /cmra_op /=.
          by rewrite agree_idemp.
        - rewrite lookup_op lookup_insert_ne; try done. rewrite lookup_empty.
          rewrite /op /cmra_op /=. destruct (M' !! x) eqn:H'; rewrite H'; try done. }
      iModIntro. iFrame "Htb". iExists M'. iFrame "∗%". } 

    iAssert (∀ v0, ⌜VN s0 n !! k = Some v0⌝ → 
       past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (searchOp k) v0 t0)%I as "#Hcase1".
    { iIntros (v0) "%VN_n0". rewrite /past_lin_witness. 
      iDestruct "HBN" as (s)"(Past_s & %FP_ns & %Hinset & %BN_ns)".
      iAssert (⌜(BN s n !!! k = BN s0 n !!! k) ∨ 
        ((BN s n !!! k).2 < (BN s0 n !!! k).2)⌝)%I as %HBN'.
      { rewrite leibniz_equiv_iff in Habs0. rewrite -Habs0.
        iPoseProof (BN_le_2 with "[%] [Hist] [$Past_s]") as "%H'"; try done.
        iPureIntro. apply H'; try done. }
      assert (BN s0 n !!! k = (VN s0 n !!! k, TN s0 n !!!k)) as H'.
      { apply PT_s0 in FP_n0. destruct FP_n0 as (H'&_).
        apply elem_of_dom_2 in VN_n0. apply (H' _ k_in_KS) in VN_n0.
        by apply lookup_total_correct in VN_n0. }
      destruct HBN' as [HBN' | HBN'].
      - iDestruct "Habs" as (s')"(Past_s' & %Habs)".
        iAssert (⌜per_tick_inv r s'⌝)%I as %PT_s'.
        { iPoseProof (per_tick_past with "[%] Hist Past_s'") as "%"; try done. }
        rewrite -HBN' BN_ns in H'. apply lookup_total_correct in VN_n0.
        rewrite VN_n0 in H'. inversion H'.
        iExists s'. iFrame "Past_s'". iPureIntro. split. done.
        assert ((abs s' : gmap K V) !!! k = (BN s' r !!! k).1) as H1'.
        { destruct PT_s' as (_&_&H1'&_). apply H1'. }
        rewrite H1' Habs /=. done.
      - iAssert (⌜BN sb r !!! k = BN s0 n !!! k⌝)%I as %BN_sb_r.
        { destruct Trans_M0 as (H1' & _). iPureIntro.
          assert (BN s0 n !! k = Some (VN s0 n !!! k, TN s0 n !!! k)) as H1''.
          { apply PT_s0 in FP_n0. destruct FP_n0 as (H2'&_).
            apply elem_of_dom_2 in VN_n0. apply (H2' _ k_in_KS) in VN_n0. done. }
          pose proof H1' n k (VN s0 n !!! k) (TN s0 n !!! k) T0 T0_in_M0 as H2'.
          rewrite leibniz_equiv_iff in Habs0. rewrite Habs0 in H2'.
          pose proof H2' H1'' as H2'. rewrite /sb /tb H' /=.
          rewrite lookup_total_alt H2' /=. done. }
        destruct (decide (t0 ≤ tb)) as [Htb | Htb].
        + iAssert (past_state Σ Hg1 Hg2 Hg3 γ_m t0 sb) as "#Past_sb'".
          { iExists tb. iFrame "#". iPureIntro. done. }
          iAssert (⌜per_tick_inv r sb⌝)%I as %PT_sb.
          { iPoseProof (per_tick_past with "[%] Hist Past_sb'") as "%"; try done. }
          assert ((abs sb : gmap K V) !!! k = (BN sb r !!! k).1) as H''.
          { destruct PT_sb as (_&_&H1'&_). apply H1'. }
          iExists sb. iFrame "Past_sb'". iPureIntro. split. done. 
          rewrite H'' BN_sb_r H' /=. apply lookup_total_correct in VN_n0. done.
        + apply not_le in Htb.
          assert (t < tb) as H1'.
          { rewrite BN_ns -/tb /= in HBN'. done. }
          iDestruct "Habs" as (s')"(Past_s' & %Habs)".
          iDestruct "Past_s'" as (ts')"Past_s'".
          iAssert (⌜tb < ts'⌝)%I as %tb_lt_ts'. 
          { iDestruct "Past_s'" as "(%&_)". iPureIntro. lia. }
          iAssert (⌜(BN sb r !!! k).2 ≤ (BN s' r !!! k).2⌝)%I as %H''.
          { iAssert (⌜M0 !!! ts' = s' ∧ ts' ≤ T0⌝)%I as %[H2' H2'']. 
            { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
              iDestruct "Past_s'" as "(% & Past_s')".
              iDestruct (history_sync with "[$H1''] [$Past_s']") as "%M_ts"; try done.
              iDestruct "H1'''" as "(%H2'&%H2''&_)". 
              apply H2'' in M_ts. assert (H3' := M_ts). apply elem_of_dom_2 in H3'.
              rewrite H2' elem_of_gset_seq in H3'. iPureIntro. split.
              apply lookup_total_correct in M_ts. done. lia. } rewrite -H2'.
            iPoseProof (BN_le_r _ _ _ _ k with "[%] [Hist] [$Past_sb] [%]") 
            as "%H3'"; try done. iPureIntro. apply H3'. lia. }
          assert (tb ≤ t) as H1''.
          { rewrite BN_sb_r -/tb Habs /= in H''. done. }
          lia. }
    iPoseProof (node_es_empty with "Node_n") as "%ES_n_empty".
    iAssert (∀ n', ⌜VN s0 n !! k = None⌝ -∗ ⌜k ∈ ES s0 n !!! n'⌝ -∗ 
      traversal_inv Σ Hg1 Hg2 Hg3 γ_m r t0 n' k (BN s0 n !!! k).1 (BN s0 n !!! k).2)%I
      as "#Hcase2".
    { iIntros (n') "%VN_n0 %k_in_ES_n0".
      assert (n' ∈ FP s0) as FP_n'.
      { destruct PT_s0 as (_&_&_&_&H'). apply (H' n); try done.
        clear -k_in_ES_n0; set_solver. }
      assert (Hn := FP_n0). apply PT_s0 in Hn.
      assert (BN s0 n !! k = QN s0 n !! k) as BN_eq_QN.
      { destruct Hn as (Hn & _). apply Hn; try done. by apply not_elem_of_dom. }
      iDestruct "HBN" as (s)"(Past_s & %FP_ns & %Hinset & %HBN)".
      iAssert (⌜(BN s n !!! k = BN s0 n !!! k) ∨ 
        ((BN s n !!! k).2 < (BN s0 n !!! k).2)⌝)%I as %HBN'.
      { rewrite leibniz_equiv_iff in Habs0. rewrite -Habs0.
        iPoseProof (BN_le_2 with "[%] [Hist] [$Past_s]") as "%H'"; try done.
        iPureIntro. apply H'; try done. }
      iAssert (⌜k ∈ inset _ (FJ s0 n) n⌝)%I as %Hinset0.
      { rewrite leibniz_equiv_iff in Habs0. rewrite -Habs0.
        iPoseProof (in_inset with "[%] [Hist] [$Past_s] [%]") as "%"; try done. }
      assert (k ∈ dom (QN s0 n)) as k_in_QN.
      { destruct Hn as (_&_&_&_&Hnf). destruct Hnf as (_&_&_&_&_&_&H'&_).
        apply H'; try done. by exists n'. }
      apply elem_of_dom in k_in_QN. destruct k_in_QN as [[v' t'] QN_k].
      assert (n ≠ n') as n_neq_n'.
      { intros <-. destruct ES_n_empty as [_ H']. rewrite H' in k_in_ES_n0.
        clear -k_in_ES_n0; set_solver. }
      assert ({[n; n']} ⊆ FP s0) as Hsub.
      { clear -FP_n0 FP_n'. set_solver. }
      assert (BN s0 n' !!! k = BN s0 n !!! k) as BN_n'.
      { assert ((k, v', t') ∈ outset _ (FI s0 n) n') as Outset_n.
        { destruct Hn as (_&_&_&_&_&H'). apply H'; try done. }
        assert ((k, v', t') ∈ inset _ (FI s0 n') n') as Inset_n'.
        { apply (flowint_inset_step (FI s0 n)).
          destruct PT_s0 as (_&(H'&_)&_). rewrite /GFI in H'. 
          pose proof (flow_big_op_valid _ _ {[n; n']} Hsub H') as H''.
          rewrite big_opS_union in H''. rewrite !big_opS_singleton in H''. done.
          clear -n_neq_n'. set_solver. apply PT_s0 in FP_n'. 
          destruct FP_n' as (_&_&_&_&(->&_)). clear; set_solver. done. }
        assert (Hn' := FP_n'). apply PT_s0 in Hn'.
        destruct Hn' as (_&_&_&_&(_&_&H'&_)). apply H' in Inset_n'; try done.
        rewrite Inset_n' lookup_total_alt BN_eq_QN QN_k /=. done. }
      assert (k ∈ inset K (FJ s0 n') n') as Hinset0'.
      { assert (k ∈ outset _ (FJ s0 n) n') as Outset_n.
        { destruct Hn as (_&_&_&_&_&H'). apply H'; try done. }
        apply (flowint_inset_step (FJ s0 n)). destruct PT_s0 as (_&(_ &H'&_)&_). 
        rewrite /GFJ in H'. pose proof (flow_big_op_valid _ _ {[n; n']} Hsub H') as H''.
        rewrite big_opS_union in H''. rewrite !big_opS_singleton in H''. done.
        clear -n_neq_n'. set_solver. apply PT_s0 in FP_n'. 
        destruct FP_n' as (_&_&_&_&(_&->&_)). clear; set_solver. done. }
      destruct HBN' as [HBN' | HBN'].
      - iSplit. rewrite -HBN' HBN /=. iFrame "Habs".
        rewrite -HBN' HBN /=. iExists s0. iFrame "Past_s0".
        iPureIntro. split. done. rewrite BN_n' -HBN' HBN. done.
      - iAssert (⌜BN sb r !!! k = BN s0 n !!! k⌝)%I as %BN_sb_r.
        { destruct Trans_M0 as (H1' & _). iPureIntro.
          assert (BN s0 n !! k = Some (v', t')) as H1''.
          { rewrite BN_eq_QN QN_k. done.  }
          pose proof H1' n k v' t' T0 T0_in_M0 as H2'.
          rewrite leibniz_equiv_iff in Habs0. rewrite Habs0 in H2'.
          pose proof H2' H1'' as H2'. apply lookup_total_correct in H1''. 
          rewrite /sb /tb H1'' /= lookup_total_alt H2' /=. done. }
        destruct (decide (t0 ≤ tb)) as [Htb | Htb].
        + iAssert (past_state Σ Hg1 Hg2 Hg3 γ_m t0 sb) as "#Past_sb'".
          { iExists tb. iFrame "#". iPureIntro. done. }
          iSplit. iExists sb. iFrame "Past_sb'".
          iPureIntro. rewrite BN_sb_r /tb. destruct (BN s0 n !!! k); done.
          iExists s0. iFrame "Past_s0". iPureIntro. split. done.
          rewrite BN_n' /tb. destruct (BN s0 n !!! k); done.
        + apply not_le in Htb.
          assert (t < tb) as H1'.
          { rewrite HBN -/tb /= in HBN'. done. }
          iDestruct "Habs" as (s')"(Past_s' & %Habs)".
          iDestruct "Past_s'" as (ts')"Past_s'".
          iAssert (⌜tb < ts'⌝)%I as %tb_lt_ts'. 
          { iDestruct "Past_s'" as "(%&_)". iPureIntro. lia. }
          iAssert (⌜(BN sb r !!! k).2 ≤ (BN s' r !!! k).2⌝)%I as %H''.
          { iAssert (⌜M0 !!! ts' = s' ∧ ts' ≤ T0⌝)%I as %[H2' H2'']. 
            { iDestruct "Hist" as (M') "(H1'&H1''&H1''')".
              iDestruct "Past_s'" as "(% & Past_s')".
              iDestruct (history_sync with "[$H1''] [$Past_s']") as "%M_ts"; try done.
              iDestruct "H1'''" as "(%H2'&%H2''&_)". 
              apply H2'' in M_ts. assert (H3' := M_ts). apply elem_of_dom_2 in H3'.
              rewrite H2' elem_of_gset_seq in H3'. iPureIntro. split.
              apply lookup_total_correct in M_ts. done. lia. } rewrite -H2'.
            iPoseProof (BN_le_r _ _ _ _ k with "[%] [Hist] [$Past_sb] [%]") 
            as "%H3'"; try done. iPureIntro. apply H3'. lia. }
          assert (tb ≤ t) as H1''.
          { rewrite BN_sb_r -/tb Habs /= in H''. done. }
          lia. }
    iAssert (⌜VN s0 n !! k = None⌝ -∗ ⌜∀ n'' : Node, k ∉ ES s0 n !!! n''⌝ -∗ 
      past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (searchOp k) bot t0)%I as "#Hcase3".
    { iIntros "%VN_n0 %k_notin_ES_n0".
      assert (Hn := FP_n0). apply PT_s0 in Hn.
      assert (QN s0 n !! k = None) as HQN.
      { destruct Hn as (_&H'&_). apply H'; try done. }
      assert (BN s0 n !! k = None) as BN_n0.
      { destruct Hn as (Hn & _). rewrite -HQN. apply Hn; try done. 
        by apply not_elem_of_dom. }
      iDestruct "HBN" as (s)"(Past_s & %FP_ns & %Hinset & %HBN)".
      iAssert (⌜(BN s n !!! k = BN s0 n !!! k) ∨ 
        ((BN s n !!! k).2 < (BN s0 n !!! k).2)⌝)%I as %HBN'.
      { rewrite leibniz_equiv_iff in Habs0. rewrite -Habs0.
        iPoseProof (BN_le_2 with "[%] [Hist] [$Past_s]") as "%H'"; try done.
        iPureIntro. apply H'; try done. }
      destruct HBN' as [HBN' | HBN'].
      - iDestruct "Habs" as (s')"(Past_s' & %Habs)".
        iAssert (⌜per_tick_inv r s'⌝)%I as %PT_s'.
        { iPoseProof (per_tick_past with "[%] Hist Past_s'") as "%"; try done. }
        assert ((abs s' : gmap K V) !!! k = (BN s' r !!! k).1) as H''.
        { destruct PT_s' as (_&_&H1'&_). apply H1'. } 
        iExists s'. iFrame "Past_s'". iPureIntro. split. done.
        rewrite H'' Habs. assert (BN s0 n !!! k = (inhabitant : V * T)) as H1'.
        { rewrite lookup_total_alt BN_n0 /=. done. }
        rewrite HBN' H1' in HBN. rewrite -HBN. rewrite /bot /inhabitant /=. done.
      - rewrite HBN lookup_total_alt BN_n0 /= in HBN'. 
        rewrite /ccmunit /nat_unit in HBN'. exfalso; lia. }
    iModIntro. iSplitR "Hpost Node_n Hlff".
    { iNext. iExists M0, T0, s0. iFrame "∗%". rewrite /resources. 
      rewrite (big_sepS_delete _ (FP s0) n); last by eauto. iFrame.
      iExists true, γn. iFrame "Hghn ∗". } clear b.
    wp_pures. wp_apply (inContents_spec with "Node_n").
    iIntros (v0)"(Node_n & %VN_k0)". wp_pures.
    (** Case analysis on whether k in contents of n **)
    destruct v0 as [v0 |]; last first.
    - (** Case : k not in contents of n **)
      wp_pures. wp_apply (findNext_spec with "Node_n").
      iIntros (n') "(Node_n & H')". destruct n' as [n' | ].
      + iDestruct "H'" as %k_in_ES_n0. wp_pures. awp_apply unlockNode_spec.
        iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
        iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
        iAssert (⌜n ∈ FP s1⌝)%I as %FP_n1.
        { apply leibniz_equiv in Habs1. rewrite -Habs1.
          iDestruct "HBN" as (s)"(Past_s & %H' & %H'')".
          iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
        rewrite /resources. rewrite (big_sepS_delete _ (FP s1) n); last by eauto.
        iDestruct "Res" as "(Res_n & Res_rest)".
        iDestruct "Res_n" as (b γn') "(#Hghn' & Hlf & Lock_n)".
        iAssert (⌜γn' = γn⌝)%I as %->. 
        { iPoseProof (ghost_heap_sync with "Hghn Hghn'") as "%"; try done. } 
        iClear "Hghn'". iAssert (⌜b = true⌝)%I as %->.
        { destruct b; try done. iExFalso. iDestruct "Lock_n" as "(H' & H'' & _)".
          iApply (node_sep_star with "[Node_n H'']"). iFrame. }
        iAssert (⌜ES s1 n = ES s0 n ∧ VN s1 n = VN s0 n⌝)%I as %[ES_01 VN_01]. 
        { iPoseProof (frac_sync with "Hlf Hlff") as "%"; try done. }
        iCombine "Lock_n Node_n Hlff" as "H'". iEval (rewrite ES_01 VN_01) in "H'".
        iAaccIntro with "H'".
        { iIntros "(Lock_n & Node_n & Hlff)". iModIntro.
          iFrame "Hpost Node_n Hlff". iNext. iExists M1, T1, s1. iFrame "∗%". 
          rewrite /resources. rewrite (big_sepS_delete _ (FP s1) n); last by eauto. 
          iFrame. iExists true, γn. iFrame "Hghn ∗". }
        iIntros "Lock_n". iModIntro. iSplitR "Hpost". 
        { iNext. iExists M1, T1, s1. iFrame "∗%". rewrite /resources. 
          rewrite (big_sepS_delete _ (FP s1) n); last by eauto. iFrame. 
          iExists false, γn. iFrame "Hghn ∗". rewrite ES_01 VN_01. done. }
        wp_pures. iApply "IH"; try done. iApply "Hcase2"; try done.
      + iDestruct "H'" as %k_notin_ES_n0. wp_pures. awp_apply unlockNode_spec.
        iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
        iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
        iAssert (⌜n ∈ FP s1⌝)%I as %FP_n1.
        { apply leibniz_equiv in Habs1. rewrite -Habs1.
          iDestruct "HBN" as (s)"(Past_s & %H' & %H'')".
          iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
        rewrite /resources. rewrite (big_sepS_delete _ (FP s1) n); last by eauto.
        iDestruct "Res" as "(Res_n & Res_rest)".
        iDestruct "Res_n" as (b γn') "(#Hghn' & Hlf & Lock_n)".
        iAssert (⌜γn' = γn⌝)%I as %->. 
        { iPoseProof (ghost_heap_sync with "Hghn Hghn'") as "%"; try done. } 
        iClear "Hghn'". iAssert (⌜b = true⌝)%I as %->.
        { destruct b; try done. iExFalso. iDestruct "Lock_n" as "(H' & H'' & _)".
          iApply (node_sep_star with "[Node_n H'']"). iFrame. }
        iAssert (⌜ES s1 n = ES s0 n ∧ VN s1 n = VN s0 n⌝)%I as %[ES_01 VN_01]. 
        { iPoseProof (frac_sync with "Hlf Hlff") as "%"; try done. }
        iCombine "Lock_n Node_n Hlff" as "H'". iEval (rewrite ES_01 VN_01) in "H'".
        iAaccIntro with "H'".
        { iIntros "(Lock_n & Node_n & Hlff)". iModIntro.
          iFrame "Hpost Node_n Hlff". iNext. iExists M1, T1, s1. iFrame "∗%". 
          rewrite /resources. rewrite (big_sepS_delete _ (FP s1) n); last by eauto. 
          iFrame. iExists true, γn. iFrame "Hghn ∗". }
        iIntros "Lock_n". iModIntro. iSplitR "Hpost". 
        { iNext. iExists M1, T1, s1. iFrame "∗%". rewrite /resources. 
          rewrite (big_sepS_delete _ (FP s1) n); last by eauto. iFrame. 
          iExists false, γn. iFrame "Hghn ∗". rewrite ES_01 VN_01. done. }
        wp_pures. iApply "Hpost". iApply "Hcase3"; try done. 
    - wp_pures. awp_apply unlockNode_spec.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iAssert (⌜n ∈ FP s1⌝)%I as %FP_n1.
      { apply leibniz_equiv in Habs1. rewrite -Habs1.
        iDestruct "HBN" as (s)"(Past_s & %H' & %H'')".
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
      rewrite /resources. rewrite (big_sepS_delete _ (FP s1) n); last by eauto.
      iDestruct "Res" as "(Res_n & Res_rest)".
      iDestruct "Res_n" as (b γn') "(#Hghn' & Hlf & Lock_n)".
      iAssert (⌜γn' = γn⌝)%I as %->. 
      { iPoseProof (ghost_heap_sync with "Hghn Hghn'") as "%"; try done. } 
      iClear "Hghn'". iAssert (⌜b = true⌝)%I as %->.
      { destruct b; try done. iExFalso. iDestruct "Lock_n" as "(H' & H'' & _)".
        iApply (node_sep_star with "[Node_n H'']"). iFrame. }
      iAssert (⌜ES s1 n = ES s0 n ∧ VN s1 n = VN s0 n⌝)%I as %[ES_01 VN_01]. 
      { iPoseProof (frac_sync with "Hlf Hlff") as "%"; try done. }
      iCombine "Lock_n Node_n Hlff" as "H'". iEval (rewrite ES_01 VN_01) in "H'".
      iAaccIntro with "H'".
      { iIntros "(Lock_n & Node_n & Hlff)". iModIntro.
        iFrame "Hpost Node_n Hlff". iNext. iExists M1, T1, s1. iFrame "∗%". 
        rewrite /resources. rewrite (big_sepS_delete _ (FP s1) n); last by eauto. 
        iFrame. iExists true, γn. iFrame "Hghn ∗". }
      iIntros "Lock_n". iModIntro. iSplitR "Hpost". 
      { iNext. iExists M1, T1, s1. iFrame "∗%". rewrite /resources. 
        rewrite (big_sepS_delete _ (FP s1) n); last by eauto. iFrame. 
        iExists false, γn. iFrame "Hghn ∗". rewrite ES_01 VN_01. done. }
      wp_pures. iApply "Hpost". iApply "Hcase1". done.
  Qed.

  Lemma searchOp_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r (p: proph_id) 
    pvs tid t0 Q k :
      main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
      thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
      □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
      ⌜local_pre (searchOp k)⌝ -∗
        {{{ proph p pvs ∗ 
            (match process_proph tid pvs with
              contra => au Σ Hg1 Hg2 Hg3 N γ_r (searchOp k) Q
            | no_upd => True
            | upd => au Σ Hg1 Hg2 Hg3 N γ_r (searchOp k) Q end) }}}
              search #r #k @ ⊤
        {{{ (res: resT) prf pvs', RET #res;
            proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
            (match process_proph tid pvs with
              contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
            | no_upd => past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (searchOp k) res t0
            | upd => Q #res ∨ 
                ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd %k_in_KS". rewrite /= in k_in_KS.
    iIntros (Φ) "!# (Hproph & Hmatch) Hpost".
    wp_lam. wp_pures. iApply fupd_wp. 
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iPoseProof (snapshot_current with "[%] [#] [$]") 
      as ">(#Past_s0&Hist)"; try done.
    iAssert (⌜per_tick_inv r s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iAssert (traversal_inv Σ Hg1 Hg2 Hg3 γ_m r t0 r k (BN s0 r !!! k).1 (BN s0 r !!! k).2)
      as "#Htr".
    { iSplit. iExists s0. iFrame "Past_s0". iPureIntro. destruct (BN s0 r !!! k); try done.
      iExists s0. iFrame "Past_s0". iPureIntro. split. apply PT_s0.
      destruct (BN s0 r !!! k). split; try done. by destruct PT_s0 as ((_&_&->)&_). }
    iModIntro. iSplitR "Hproph Hmatch Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%". }
    iModIntro. wp_apply (traverse_spec); try done.
    iIntros (res)"PastW". destruct (process_proph tid pvs) eqn: Hpvs.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph". by iPureIntro.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph". iSplitR. by iPureIntro.
      iRight. by iPureIntro.
    - iApply ("Hpost" $! res [] pvs). iFrame "Hproph #". iFrame "PastW". done.  
  Qed.

End LSM_SEARCH.
