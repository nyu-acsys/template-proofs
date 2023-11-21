(* Herlihy Skiplist with a single level : Insert *)

From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
From flows Require Export skiplist_v1_util list_flow_upd_insert.

Module SKIPLIST1_SPEC_INSERT.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS SKIPLIST1_UTIL.

  Parameter createNode_spec : ∀ (succs: loc) ss (k: nat),
  ⊢  {{{ is_array succs ss ∗ ⌜length ss = L⌝ }}}
           createNode #k #succs
        {{{ (n: Node) (h: nat) mark next,
            RET #n;
              is_array succs ss
            ∗ node n h mark next k
            ∗ ⌜0 < h < L⌝
            ∗ ⌜dom mark = gset_seq 0 (h-1)⌝ ∗ ⌜dom next = gset_seq 0 (h-1)⌝
            ∗ (⌜∀ i, i < h → mark !! i = Some false⌝)
            ∗ (⌜∀ i, i < h → next !! i = Some (ss !!! i)⌝) }}}.

  Parameter changeNext_spec : ∀ (n m m': Node) (i: nat),
    ⊢  <<{ ∀∀ h mark next k, node n h mark next k ∗ ⌜i < h⌝ }>>
            changeNext #n #m #m' #i @ ∅
      <<{ ∃∃ (success: bool) next',
              node n h mark next' k
            ∗ (match success with true => ⌜next !! i = Some m 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := m']> next⌝
                                | false => ⌜(next !! i ≠ Some m ∨ 
                                              mark !!! i = true)
                                            ∧ next' = next⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  }>>.

  Parameter changeNext_proph_spec : ∀ (n m m': Node) (p: proph_id) pvs,
    ⊢ proph p pvs -∗
      <<{ ∀∀ h mark next k, node n h mark next k ∗ ⌜0 < h⌝ }>>
            changeNext #n #m #m' #p @ ∅
      <<{ ∃∃ (success: bool) next' prf pvs',
              node n h mark next' k
            ∗ proph p pvs'
            ∗ ⌜Forall (λ x, ∃ v1, x = ((v1, #false)%V, #())) prf⌝
            ∗ (match success with 
                true => ⌜next !! 0 = Some m 
                        ∧ mark !!! 0 = false
                        ∧ next' = <[0 := m']> next
                        ∧ (∃ v1, pvs = prf ++ [((v1, #true)%V, #())] ++ pvs')⌝
              | false => ⌜(next !! 0 ≠ Some m ∨ mark !!! 0 = true)
                          ∧ next' = next
                          ∧ pvs = prf ++ pvs'⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end) }>>.

  Definition traversal_inv γ_m t0 i k p c : iProp :=
    (∃ s, past_state γ_m t0 s ∗ ⌜p ∈ FP s ∧ Key s p < k ∧ 
      Marki s p 0 = false ∧ i < Height s p ∧ (i = 0 → Nexti s p i = Some c)⌝)
  ∗ (∃ s, past_state γ_m t0 s ∗ ⌜c ∈ FP s ∧ i < Height s c⌝).

  Lemma traverse_spec N γ_t γ_r γ_m γ_mt γ_msy tid t0 k:
  main_inv N γ_t γ_r γ_m γ_mt γ_msy  -∗
  thread_start γ_t γ_mt tid t0 -∗
  □ update_helping_protocol N γ_t γ_r γ_mt γ_msy -∗ 
  ⌜1 < L ∧ 0 < k < W⌝ -∗
    {{{ True }}}
        traverse #hd #tl #k @ ⊤
    {{{ (preds succs: loc) (ps ss: list Node) (res: bool), 
          RET (#preds, #succs, #res);
          is_array preds ps ∗ is_array succs ss
        ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
        ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
        ∗ (∀ i, ⌜i < L⌝ → traversal_inv γ_m t0 i k (ps !!! i) (ss !!! i))
        ∗ (let c := ss !!! 0 in 
              ∃ s, past_state γ_m t0 s ∗
                  ⌜if res then 
                    k ∈ abs s ∧ k = Key s c ∧ c ∈ FP s ∧ Marki s c 0 = false
                  else 
                    k ∉ abs s ∧ k < Key s c ∧ c ∈ FP s⌝) }}}.
  Proof.
  Admitted.

  Lemma maintenanceOp_insert_spec ps ss N γ_t γ_r γ_m γ_mt γ_msy tid t0 k (n:Node) 
    preds succs:
    main_inv N γ_t γ_r γ_m γ_mt γ_msy -∗
    thread_start γ_t γ_mt tid t0 -∗
    □ update_helping_protocol N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
        {{{   preds ↦∗ ((λ n0 : loc, #n0) <$> ps)
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss)
            ∗ (∃ s, past_state γ_m t0 s ∗ ⌜n ∈ FP s⌝)
            ∗ ⌜n ≠ hd⌝ ∗ ⌜n ≠ tl⌝
            ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
            ∗ ⌜ps !!! (L - 1) = hd⌝ ∗ ⌜ss !!! (L - 1) = tl⌝
            ∗ (∀ i, ⌜i < L⌝ → traversal_inv γ_m t0 i k (ps !!! i) (ss !!! i)) }}}
           maintenanceOp_insert #k #preds #succs #n
        {{{ (ps' ss': list Node),
            RET #();
              preds ↦∗ ((λ n0 : loc, #n0) <$> ps')
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss') }}}.
  Proof.
  Admitted.

  Lemma insertOp_spec N γ_t γ_r γ_m γ_mt γ_msy (pr: proph_id) pvs 
  tid t0 Q (k: nat):
       main_inv N γ_t γ_r γ_m γ_mt γ_msy  -∗
       thread_start γ_t γ_mt tid t0 -∗
       □ update_helping_protocol N γ_t γ_r γ_mt γ_msy -∗
       ⌜1 < L ∧ 0 < k < W⌝ -∗
         {{{ proph pr pvs ∗ 
             (match process_proph tid pvs with
              | contra => au N γ_r (insertOp k) Q
              | no_upd => True
              | upd => au N γ_r (insertOp k) Q end) }}}
            insert #hd #tl #k #pr @ ⊤
         {{{ (res: resT) prf pvs', RET #res;
             proph pr pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
             (match process_proph tid pvs with
              | contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
              | no_upd => past_lin_witness γ_m (insertOp k) res t0
              | upd => Q #res ∨ 
                      ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iLöb as "IH" forall (pvs).
    iIntros (Φ) "!# (Hproph & Hmatch) Hpost".
    wp_lam. wp_pures. wp_apply traverse_spec; try done.
    iIntros (preds succs ps ss res) "(Hpreds & Hsuccs & %Len_ps 
    & %Len_ss & %HpsL & %HssL & #Htr)".
    wp_pures. destruct res; wp_pures.
    - iAssert (past_lin_witness γ_m (insertOp k) false t0)%I as "#PastW".
      { iDestruct "Htr" as "(_ & Htr)". 
        iDestruct "Htr" as (s)"(#Past_s & %k_in_s & _)".
        iExists s. iFrame "#". iPureIntro. set_solver. }
      destruct (process_proph tid pvs) eqn: Hpvs.
      + iApply ("Hpost" $! false [] pvs). iFrame "Hproph". by iPureIntro.
      + iApply ("Hpost" $! false [] pvs). iFrame "Hproph". iSplitR. by iPureIntro.
        iRight. by iPureIntro.
      + iApply ("Hpost" $! false [] pvs). iFrame "Hproph #". done.
    - wp_apply (createNode_spec _ ss with "[Hsuccs]"); try done.
      { iFrame. by iPureIntro. }
      iIntros (n h mark next) "(Hsuccs & Node_n & %Range_h & %Dom_mark 
        & %Dom_next & %Def_mark & %Def_next)".
      wp_pures. wp_bind (! _)%E.
      iEval (rewrite /is_array) in "Hpreds".
      assert (is_Some (ps !! 0)) as [p Hps0].
      { rewrite lookup_lt_is_Some Len_ps; lia. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) _ ((λ n : loc, #n) <$> ps) #p
        with "[Hpreds]"); try done.
      { by rewrite list_lookup_fmap Hps0 /=. }
      { iNext. admit. }
      iIntros "Hpreds". wp_pures.
      wp_bind (! _)%E.
      iEval (rewrite /is_array) in "Hsuccs".
      assert (is_Some(ss !! 0)) as [c Hss0].
      { rewrite lookup_lt_is_Some Len_ss; lia. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) _ ((λ n : loc, #n) <$> ss) #c
        with "[Hsuccs]"); try done.
      { by rewrite list_lookup_fmap Hss0 /=. }
      { iNext. admit. }
      iIntros "Hsuccs". wp_pure credit: "Hc". wp_pures.
      awp_apply (changeNext_proph_spec with "Hproph"); try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
      { apply leibniz_equiv in Habs0. rewrite -Habs0. iDestruct "Htr" as "(H'&_)".
        iAssert (⌜0 < L⌝)%I as "H''". { iPureIntro; lia. }
        iPoseProof ("H'" with "H''") as "Htr". 
        apply list_lookup_total_correct in Hps0. rewrite Hps0.
        iDestruct "Htr" as "(Hp&_)". iDestruct "Hp" as (s)"(Past_s & % & _)".
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
      iAssert (¬ ⌜n ∈ FP s0⌝)%I as %n_notin_s0. 
      { iIntros "%H'". rewrite (big_opS_delete _ (FP s0) n); try done.
        iDestruct "Nodes" as "(Node_n' & _)".
        iApply (node_sep_star with "[$Node_n] [$Node_n']"). }
      assert (n ≠ p) as n_neq_p.
      { clear -FP_p0 n_notin_s0. set_solver. }
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
      { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
      iAssert ((node p (Height s0 p) (Mark s0 p) (Next s0 p) (Key s0 p)) 
        ∗ ⌜0 < Height s0 p⌝)%I with "[Node_p]" as "Hpre".
      { iFrame "Node_p". iPureIntro. 
        destruct (decide (p = hd)) as [-> | Hphd].
        destruct PT_s0 as ((_&_&_&_&_&_&_&->&_)&_). lia.
        destruct (decide (p = tl)) as [-> | Hptl].
        destruct PT_s0 as ((_&_&_&_&_&_&_&_&->)&_). lia.
        apply PT_s0 in FP_p0. by apply FP_p0. }
      iAaccIntro with "Hpre".
      { iIntros "(Node_p&_)". iModIntro. 
        iFrame "Hpost Hmatch Node_n Hpreds Hsuccs Hc".
        iNext; iExists M0, T0, s0. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
      iIntros (success next' prf pvs')"(Node_p & Hproph & %Hprf & Hif)".
      iApply (lc_fupd_add_later with "Hc"). iNext.
      destruct success; last first.
      + iDestruct "Hif" as %[H' [-> Hpvs]]. 
        iModIntro. iSplitR "Hpost Hproph Hmatch".
        { iNext. iExists M0, T0, s0. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
        wp_pures. 
        destruct (process_proph tid pvs) eqn: Def_pvs.
        * assert (process_proph tid pvs' = contra) as Hpvs'.
          { clear -Hpvs Hprf Def_pvs. apply (process_proph_contra_rec _ prf).
            by rewrite -Hpvs. rewrite Forall_lookup. 
            rewrite Forall_lookup in Hprf. intros i' x' H'%Hprf. 
            destruct H' as [v1' ->]. done. }
          iSpecialize ("IH" $! pvs'). rewrite Hpvs'.
          iApply ("IH" with "[$Hproph $Hmatch]"). iNext. 
          iIntros (res prf' pvs'') "(Hproph & %Def_pvs' & %Hprf')".
          iApply ("Hpost" $! _ (prf ++ prf') pvs''). iFrame "Hproph". 
          iPureIntro. rewrite Def_pvs' in Hpvs. split. rewrite Hpvs. 
          by rewrite assoc. rewrite Forall_app. split; try done.
          apply (Forall_impl _ _ _ Hprf). intros [x1 x2]. intros [v' [=]]. 
          by subst x2.
        * assert (process_proph tid pvs' = upd) as Hpvs'. 
          { clear -Hpvs Hprf Def_pvs. apply (process_proph_upd_rec _ prf).
            by rewrite -Hpvs. rewrite Forall_lookup. 
            rewrite Forall_lookup in Hprf. intros i' x' H'%Hprf. 
            destruct H' as [v1' ->]. rewrite /is_snd /=.
            split; try done. intros [v Hv]. inversion Hv. }
          iSpecialize ("IH" $! pvs'). rewrite Hpvs'.
          iApply ("IH" with "[$Hproph $Hmatch]"). iNext. 
          iIntros (res prf' pvs'') "(Hproph & %Def_pvs' & Hor)".
          iApply ("Hpost" $! _ (prf ++ prf') pvs''). iFrame "Hproph". iSplitR. 
          iPureIntro. rewrite Def_pvs' in Hpvs. rewrite Hpvs. 
          by rewrite assoc. iDestruct "Hor" as "[HQ | %Hprf']". by iLeft.
          iRight. rewrite Forall_app. iPureIntro. split; try done.
          apply (Forall_impl _ _ _ Hprf). intros [x1 x2]. intros [v' [=]]. 
          subst x1 x2. split; try done. rewrite /is_snd /=. intros [? [=]].
        * assert (process_proph tid pvs' = no_upd) as Hpvs'. 
          { clear -Hpvs Hprf Def_pvs. apply (process_proph_no_upd_rec _ prf).
            by rewrite -Hpvs. rewrite Forall_lookup. 
            rewrite Forall_lookup in Hprf. intros i' x' H'%Hprf. 
            destruct H' as [v1' ->]. rewrite /is_snd /=.
            split; try done. intros [v Hv]. inversion Hv. }
          iSpecialize ("IH" $! pvs'). rewrite Hpvs'.
          iApply ("IH" with "[$Hproph $Hmatch]"); try done. iNext. 
          iIntros (res prf' pvs'') "(Hproph & %Def_pvs' & #PastW)".
          iApply ("Hpost" $! _ (prf ++ prf') pvs''). iFrame "Hproph #".
          iPureIntro. rewrite Def_pvs' in Hpvs. rewrite Hpvs. 
          by rewrite assoc. 
      + iDestruct "Hif" as %(Next_p0 & Mark_p0 & Def_next' & Hpvs').
        iAssert (∀ i, ⌜i < L⌝ → ⌜(ss !!! i) ∈ FP s0⌝ ∗ ⌜i < Height s0 (ss !!! i)⌝)%I 
          as %Hss.
        { iIntros (i)"#Hi". iDestruct "Htr" as "(Htr&_)". 
          iPoseProof ("Htr" with "Hi") as "#Htr'". iDestruct "Htr'" as "(_&Htr')". 
          iDestruct "Htr'" as (s)"(Past_s & %Hfp & %Ht)". 
          apply leibniz_equiv in Habs0. rewrite <-Habs0.
          iSplit. 
          iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done.
          iAssert (⌜Height (M0 !!! T0) (ss !!! i) = Height s (ss !!! i)⌝)%I as %H'.
          iPoseProof (height_eq_2 (ss !!! i) with "[%] [$Hist] [$Past_s] [%]") 
            as "->"; try done. iPureIntro. by rewrite H'. }
        assert (∀ i, i < L → (ss !!! i) ∈ FP s0) as Hss_fp.
        { intros i Hi; apply Hss; try done. }
        assert (∀ i, i < L → i < Height s0 (ss !!! i)) as Hss_ht.
        { intros i Hi; apply Hss; try done. } 
        clear Hss. 
      
        iDestruct "SShot0" as %[FP0 [C0 [Ht0 [Mk0 [Nx0 [Ky0 [I0 
          [Hs0 [Dom_Ht0 [Dom_Mk0 [Dom_Nx0 [Dom_Ky0 Dom_I0]]]]]]]]]]]].
        assert (∀ x, x ∈ FP s0 → flow_constraints_I x (FI s0 x) 
                  (Mark s0 x !!! 0) (Next s0 x !! 0) (Key s0 x)) as Hflow.
        { destruct PT_s0 as (_&_&_&H'&_).
          intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&?). }
        set Mk0' := <[n := mark]> Mk0.
        set Nx0' := <[n := next]> (<[p := next']> Nx0).
        set Ky0' := <[n := k]> Ky0.
        set Ht0' := <[n := h]> Ht0.
        iAssert (⌜∃ (I: gmap Node (multiset_flowint_ur nat)) (nk: Node),
            dom I = FP s0 ∪ {[n]}
          ∧ nk ∈ FP s0
          ∧ n ≠ nk
          ∧ k < Key s0 nk
          ∧ Mark s0 nk !!! 0 = false
          ∧ k ∈ keyset (I !!! n)
          ∧ (Key s0 nk ∈ keyset (I0 !!! nk) → Key s0 nk ∈ keyset (I !!! nk))
          ∧ keyset (I !!! nk) ∪ keyset (I !!! n) = keyset (I0 !!! nk)
          ∧ keyset (I !!! n) ## keyset (I !!! nk)
          ∧ (∀ x, x ∈ dom I ∖ {[ n; nk ]} → 
                    keyset (I !!! x) = keyset (I0 !!! x))
          ∧ ✓ ([^op set] x ∈ dom I, (I !!! x: multiset_flowint_ur nat))
          ∧ (∀ n1 n2, (Nx0' !!! n1) !! 0 = Some n2 → Ky0' !!! n1 < Ky0' !!! n2)
          ∧ (∀ n1 n2 i, (Nx0' !!! n1) !! i = Some n2 → n2 ∈ dom I)
          ∧ (∀ x, x ∈ dom I → x ≠ p → x ≠ n →
            flow_constraints_I x (I !!! x) (Mark s0 x !!! 0) (Next s0 x !! 0) (Key s0 x))
          ∧ (flow_constraints_I p (I !!! p) (false) (Some n) (Key s0 p) )
          ∧ (flow_constraints_I n (I !!! n) (false) (Some c) (k))
          ∧ p ≠ tl⌝)%I
          as %[I [nk Hflupd]].
        { iAssert (⌜Key s0 p < k⌝)%I as %Key_pn.
          { apply leibniz_equiv in Habs0. rewrite -Habs0.
            iAssert (⌜0 < L⌝)%I as "H'". { iPureIntro. lia. }
            iDestruct "Htr" as "(Htr&_)".
            iPoseProof ("Htr" with "H'") as "(Htr'&_)".
            iDestruct "Htr'" as (s)"(Past_s & %H' & %H'' & _)".
            apply list_lookup_total_correct in Hps0. rewrite Hps0 in H' H''.
            iPoseProof (key_eq_2 p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
              try done. }
          iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
          { apply leibniz_equiv in Habs0. rewrite -Habs0. iDestruct "Htr" as "(H'&_)".
            iAssert (⌜0 < L⌝)%I as "H''". { iPureIntro; lia. }
            iPoseProof ("H'" with "H''") as "(_&Htr)". 
            apply list_lookup_total_correct in Hss0. rewrite Hss0.
            iDestruct "Htr" as (s)"(Past_s & % & _)".
            iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
          iAssert (⌜k < Key s0 c⌝)%I as %Key_nc.
          { apply leibniz_equiv in Habs0. rewrite -Habs0.
            iDestruct "Htr" as "(_&Htr)".
            iDestruct "Htr" as (s)"(Past_s & %H' & %H'')".
            apply list_lookup_total_correct in Hss0. rewrite Hss0 in H''.
            iPoseProof (key_eq_2 c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
              try done. apply H''. iPureIntro. apply H''. }
          iPureIntro.
          set Ip0 := I0 !!! p. set Ic0 := I0 !!! c. set out_pc := out Ip0 c.
          set Ip0' := int {| infR := inf_map Ip0; outR :=  <<[n := out_pc]>> ∅ |}.
          set In0' := int {| infR := {[n := out_pc]}; 
                              outR := <<[c := out_pc]>> ∅ |}.
          assert (∀ x, I0 !!! x = FI s0 x) as I0_eq_s0.
          { intros x. rewrite Hs0; unfold FI. try done. }
          assert (Key s0 p < Key s0 c) as Key_pc.
          { destruct PT_s0 as (_&_&_&_&PT&_). rewrite /Nexti in PT.
            by pose proof PT p c Next_p0. }
          assert (Key s0 p < W) as Key_p0.
          { destruct PT_s0 as (_&_&_&PT&_). apply PT in FP_c0.
            destruct FP_c0 as (_&_&_&_&H'&_). clear -H' Key_pc; lia. }
          
          assert (insets (FI s0 p) ≠ ∅) as Insets_p_ne.
          { apply Hflow in FP_p0. rewrite Mark_p0 -I0_eq_s0 in FP_p0.
            destruct FP_p0 as (_&_&_&(H'&_)&_). rewrite -I0_eq_s0. 
            intros H''; rewrite H'' in H'. 
            assert (W ∈ gset_seq (Key s0 p) W) as H1'.
            { rewrite elem_of_gset_seq. split; clear -Key_p0; lia. }
            clear -H' H1'; set_solver. }
          assert (out_pc ≠ 0%CCM) as Out_pc_nz.
          { apply Hflow in FP_p0. rewrite /Marki Mark_p0 /Nexti Next_p0 in FP_p0.
            destruct FP_p0 as (_&H'&_&(_&H'')&_). rewrite /outsets H' in H''. 
            rewrite -leibniz_equiv_iff big_opS_singleton in H''.
            rewrite /out_pc /Ip0 I0_eq_s0. rewrite /ccmunit /lift_unit.
            clear H'; intros H'. rewrite nzmap_eq in H'. pose proof H' W as H'.
            rewrite nzmap_lookup_empty /ccmunit /= /nat_unit in H'.
            rewrite /outset in H''. rewrite -nzmap_elem_of_dom_total2 -H'' in H'.
            apply H'. rewrite elem_of_gset_seq. clear -Key_p0; split; lia.
            done. }
          assert (p ≠ c) as p_neq_c.
          { intros ->. clear -Key_pc; lia. }
          assert (n ≠ c) as n_neq_c.
          { clear -FP_c0 n_notin_s0. set_solver. }
          assert (✓ ([^op set] x ∈ dom I0, (I0 !!! x: multiset_flowint_ur nat))) 
            as VI0.
          { destruct PT_s0 as (_&H'&_).
            unfold GFI in H'. rewrite Dom_I0.
            rewrite {2}Hs0 in H'. unfold FP in H'.
            assert (([^op set] x ∈ FP0, I0 !!! x) = 
              ([^op set] x ∈ FP0, FI s0 x)) as H1'.
            { by apply big_opS_ext. }
            by rewrite H1'. }

          assert (FP s0 = dom I0) as FP_s0_I0.
          { by rewrite /FP Hs0 Dom_I0. }
          rewrite FP_s0_I0 in Hflow.
          assert (∀ x, x ∈ dom I0 → dom (I0 !!! x: multiset_flowint_ur nat) 
            = {[x]}) as Domm_I0.
          { intros x Hx%Hflow. destruct Hx as (Hx&_). by rewrite I0_eq_s0. }
          assert (p ∈ dom I0) as p_in_I0.
          { by rewrite Hs0 /FP -Dom_I0 in FP_p0. }
          assert (c ∈ dom I0) as c_in_I0.
          { by rewrite Hs0 /FP -Dom_I0 in FP_c0. }
          assert (n ∉ dom I0) as n_notin_I0.
          { by rewrite Hs0 /FP -Dom_I0 in n_notin_s0. }
          assert (✓ Ip0) as Vp0.
          { assert ({[p]} ⊆ dom I0) as H'. 
            { clear -p_in_I0; set_solver. }
            pose proof (flow_big_op_valid _ (dom I0) {[p]} H' VI0) as H''.
            by rewrite big_opS_singleton in H''. }
          assert (✓ Ip0') as Vp0'.
          { rewrite /valid /=. apply Domm_I0 in p_in_I0.
            unfold dom, flowint_dom in p_in_I0.
            rewrite p_in_I0. rewrite nzmap_dom_insert_nonzero; try done.
            split. clear -n_neq_p; set_solver.
            intros H'; rewrite H' in p_in_I0. clear -p_in_I0; set_solver. }
          assert (dom Ic0 ## dom Ip0) as Disj_pc.
          { rewrite !Domm_I0; try done. clear -p_neq_c; set_solver. }
          assert (c ∈ dom Ic0) as c_in_Ic0.
          { rewrite Domm_I0; try done. clear; set_solver. }
          assert (n ∉ dom Ip0 ∪ dom Ic0) as n_notin_pc.
          { rewrite !Domm_I0; try done. clear -n_neq_p n_neq_c. set_solver. }
          assert (dom Ip0 = dom Ip0') as Dom_Ip0'.
          { apply Domm_I0 in p_in_I0.
            unfold dom, flowint_dom in p_in_I0.
            unfold dom, flowint_dom. by rewrite p_in_I0. }
          assert (out Ip0 n = 0%CCM) as Out_Ip0_n.
          { apply Hflow in p_in_I0. 
            rewrite /Nexti Next_p0 in p_in_I0.
            destruct p_in_I0 as (_&Hx&_). unfold out.
            rewrite -nzmap_elem_of_dom_total2. rewrite /Ip0 I0_eq_s0 Hx.
            clear -n_neq_c; set_solver. done. }
          assert (out Ip0' n = out Ip0 c) as Out_Ip0'_n.
          { rewrite {1}/out /out_map /Ip0' /=.
            rewrite nzmap_lookup_total_insert. done. }
          assert (out Ip0' c = 0%CCM) as Out_Ip0'_c.
          { rewrite {1}/out /out_map /Ip0' /=.
            rewrite nzmap_lookup_total_insert_ne; try done. }
          assert (∀ n0, n0 ≠ n → n0 ≠ c → out Ip0' n0 = out Ip0 n0) as Out_Ip0'. 
          { intros n' Hn' Hn''. apply Hflow in p_in_I0. 
            rewrite /Nexti Next_p0 in p_in_I0. destruct p_in_I0 as (_&Hx&_). 
            rewrite {1}/out /out_map /Ip0' /=. rewrite /out /Ip0 I0_eq_s0.
            rewrite nzmap_lookup_total_insert_ne; try done.
            rewrite nzmap_lookup_empty. symmetry. 
            rewrite -nzmap_elem_of_dom_total2. rewrite Hx. 
            clear -Hn''; set_solver. done. }
          assert (∀ n, inf Ip0' n = inf Ip0 n) as Inf_Ip0'.
          { intros ?; try done. }
          pose proof contextualLeq_insert_node _ Ip0 Ic0 Ip0' n c Vp0 Vp0'
            Disj_pc c_in_Ic0 n_notin_pc Dom_Ip0' Out_Ip0_n Out_Ip0'_n 
            Out_Ip0'_c Out_Ip0' Inf_Ip0' as ContLeq0.
          rewrite -/out_pc -/In0' in ContLeq0.
          set I0' := <[n := In0']> (<[p := Ip0']> I0).
          set Io := ([^op set] x ∈ dom I0 ∖ {[p]}, 
                          ((I0 !!! x): multiset_flowint_ur _)).
          assert (✓ (Ip0 ⋅ Io)) as Vpo.
          { assert (Ip0 ⋅ Io = 
              ([^op set] x ∈ dom I0, I0 !!! x : multiset_flowint_ur nat)) as ->.
            rewrite /Ip0 /Io. by rewrite (big_opS_delete _ (dom I0) p).
            done. }
          assert (dom In0' = {[n]}) as Dom_In0'.
          { rewrite /dom /flowint_dom /=. by rewrite dom_singleton_L. }
          assert (p ∉ dom Io) as p_notin_Io.
          { rewrite (big_opS_delete _ _ p) in VI0; try done. 
            rewrite -/Io in VI0. apply intComp_dom_disjoint in VI0.
            rewrite (Domm_I0 p p_in_I0) in VI0. clear - VI0; set_solver. }
          assert (dom ([^op set] x ∈ dom I0, I0 !!! x : multiset_flowint_ur nat)
            = FP s0) as Dom_I0_FP.
          { rewrite set_eq_subseteq. split.
            - intros x Hx. rewrite flow_big_op_dom in Hx; try done.
              destruct Hx as [x0 [Hx01 Hx02]].
              rewrite (Domm_I0 x0 Hx01) in Hx02.
              rewrite /FP Hs0 -Dom_I0.
              clear -Hx01 Hx02; set_solver.
            - intros x Hx. rewrite flow_big_op_dom; try done.
              exists x. rewrite /FP Hs0 -Dom_I0 in Hx. split; try done.
              rewrite (Domm_I0 x Hx). clear; set_solver. }
          assert (n ∉ dom Io) as n_notin_Io.
          { assert (dom Io ⊆ 
              dom ([^op set] x ∈ dom I0, I0 !!! x : multiset_flowint_ur _)) as H'. 
            { rewrite (big_opS_delete _ _ p) -/Io; try done.
              rewrite intComp_dom. clear; set_solver.
              rewrite (big_opS_delete _ _ p) -/Io in VI0; try done. }
            rewrite Dom_I0_FP in H'.
            clear -H' n_notin_s0. set_solver. }
          assert (dom (Ip0' ⋅ In0') ∩ dom Io = ∅) as Disj_Io.
          { rewrite intComp_dom. rewrite Dom_In0' -Dom_Ip0' (Domm_I0 p p_in_I0).
            clear -p_notin_Io n_notin_Io. set_solver.
            by destruct ContLeq0 as (_&?&_). }
          assert (out ([^op set] x ∈ dom I0, I0 !!! x: multiset_flowint_ur _) n 
                    = 0%CCM) as Out_s0_n.
          { set a := out ([^op set] x ∈ dom I0, I0 !!! x) n.
            destruct (decide (a = 0%CCM)) as [? | Ha]; try done. exfalso.
            rewrite /a in Ha. rewrite flow_big_op_out in Ha; try done.
            rewrite /ccmunit /lift_unit /= in Ha.
            assert (([^+ set] x ∈ dom I0, out (I0 !!! x) n) = 
              ([^+ set] x ∈ dom I0, (∅ : nzmap nat nat))) as H'.
            { apply ccm_big_opS_ext. intros x Hx. rewrite /out.
              rewrite -nzmap_elem_of_dom_total2. intros Hn.
              apply Hflow in Hx. destruct Hx as (_&Hx&Hx1&_).
              destruct (decide (insets (FI s0 x) = ∅)).
              { assert (outsets (FI s0 x) = ∅) by (clear -Hx1 e; set_solver).
                rewrite /outsets in H. apply leibniz_equiv_iff in H.
                rewrite (big_opS_delete _ (dom (out_map (FI s0 x))) n) in H.
                assert (outset nat (FI s0 x) n = ∅). 
                { clear -H; set_solver. } 
                rewrite /outset /out in H0.
                { rewrite -I0_eq_s0 in H0. 
                  assert (out_map (I0 !!! x) !!! n = (∅: nzmap _ _)) as H'.
                  { apply nzmap_eq. intros k'. rewrite nzmap_lookup_empty.
                    rewrite -nzmap_elem_of_dom_total2 H0. clear; set_solver. }
                  rewrite nzmap_elem_of_dom_total in Hn. rewrite H' in Hn.
                  clear -Hn; try done. }
              by rewrite I0_eq_s0 in Hn. }
              rewrite I0_eq_s0 Hx in Hn.
              destruct (Next s0 x !! 0) as [n'|] eqn: Hn'.
              rewrite elem_of_singleton in Hn; subst n'.
              destruct PT_s0 as (_&_&_&_&_&PT&_).
              pose proof PT x n 0 Hn' as PT. clear -PT n_notin_s0; try done.
              clear -Hn; set_solver. done. }
            rewrite H' ccm_big_opS_unit /ccm_unit /= /lift_unit in Ha.
            clear -Ha; done. by rewrite Dom_I0_FP. }
          assert (∀ n, n ∈ dom (Ip0' ⋅ In0') ∖ dom Ip0 → out_map Io !!! n = 0%CCM)
           as Out_Io.
          { intros n'. rewrite intComp_dom; last first. 
            { by destruct ContLeq0 as (_&?&_). }  
            rewrite Dom_In0' -Dom_Ip0' (Domm_I0 p p_in_I0).
            intros Hn'. assert (n' = n) as ->.
            { clear -Hn'; set_solver. }
            rewrite (big_opS_delete _ _ p) in Out_s0_n. 
            rewrite intComp_unfold_out in Out_s0_n.
            rewrite /ccmunit /lift_unit /=. rewrite nzmap_eq.
            intros k'. rewrite nzmap_lookup_empty. 
            rewrite /ccmunit /= /nat_unit.
            rewrite /ccmunit /= /lift_unit in Out_s0_n.
            rewrite /ccmop /ccm_op /= in Out_s0_n.
            rewrite nzmap_eq in Out_s0_n. pose proof Out_s0_n k' as H'.
            rewrite lookup_total_lifting in H'. 
            rewrite /ccmop /ccm_op /= /nat_op in H'.
            rewrite nzmap_lookup_empty in H'.
            rewrite /ccmunit /= /nat_unit in H'.
            rewrite -/Io in H'. clear -H'.
            set a := (out (I0 !!! p: multiset_flowint_ur _) n) !!! k'.
            set b := (out Io n) !!! k'.
            rewrite -/a -/b in H'. lia.
            by rewrite (big_opS_delete _ _ p) in VI0.
            rewrite (big_opS_delete _ _ p) in Dom_I0_FP.
            by rewrite Dom_I0_FP. done. done. }
          pose proof replacement_theorem _ Io Ip0 (Ip0' ⋅ In0') Vpo Disj_Io 
            Out_Io ContLeq0 as ContLeq0'.
          assert (∃ (Nx: gmap Node Node), (∀ x, Nx !! x = (Nx0' !!! x) !! 0))
            as [Nx Def_Nx'].
          { set f_Nx := λ (n: Node) (nx: gmap nat Node) (res: gmap Node Node), 
                        match nx !! 0 with None => res 
                                        | Some n' => <[n := n']> res end.
            set Nx : gmap Node Node := map_fold f_Nx ∅ Nx0'.
            exists Nx.
            set P := λ (res: gmap Node Node) (m: gmap Node (gmap nat Node)),
                (∀ x: Node, res !! x = 
                  (match m !! x with Some mn => mn | None => ∅ end) !! 0).
            apply (map_fold_ind P); try done.
            intros n' Nx_n' m res Hmn HP. unfold P. unfold P in HP.
            intros n''. unfold f_Nx. 
            destruct (decide (n'' = n')) as [-> | Hn''].
            - destruct (Nx_n' !! 0) as [Nx_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert. by rewrite Hn0.
              + rewrite lookup_insert. rewrite Hn0.
                by rewrite (HP n') Hmn.
            - destruct (Nx_n' !! 0) as [Nx_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert_ne; try done.
              + rewrite (HP n''). by rewrite lookup_insert_ne. }
          assert (Nx !! p = Some n) as Nx_p.
          { rewrite Def_Nx' /Nx0'. rewrite lookup_total_insert_ne; try done.
            rewrite lookup_total_insert. rewrite Def_next'.
            by rewrite lookup_insert. }
          assert (Nx !! n = Some c) as Nx_n.
          { rewrite Def_Nx' /Nx0'. rewrite lookup_total_insert (Def_next 0).
            apply f_equal. rewrite list_lookup_total_alt Hss0 /=. done. 
            apply Range_h. }
          assert (∀ x, x ≠ p → x ≠ n → Nx !! x = Next s0 x !! 0) as Def_Nx.
          { intros x Hxp Hxn. rewrite Def_Nx' /Nx0'. 
            rewrite lookup_total_insert_ne; try done.
            rewrite lookup_total_insert_ne; try done.
            rewrite /Nexti /Next Hs0. destruct (Nx0 !! x); try done. }
          assert (∃ (Mk: gmap Node bool), ∀ x, Mk !! x = (Mk0' !!! x) !! 0)
            as [Mk Def_Mk'].
          { set f_Mk := λ (n: Node) (nx: gmap nat bool) (res: gmap Node bool), 
                        match nx !! 0 with None => res 
                                        | Some n' => <[n := n']> res end.
            set Mk : gmap Node bool := map_fold f_Mk ∅ Mk0'.
            exists Mk.
            set P := λ (res: gmap Node bool) (m: gmap Node (gmap nat bool)),
              ∀ x: Node, res !! x = 
                (match m !! x with Some mn => mn | None => ∅ end) !! 0.
            apply (map_fold_ind P); try done.
            intros n' Mk_n m res Hmn HP. unfold P. unfold P in HP.
            intros n''. unfold f_Mk. 
            destruct (decide (n'' = n')) as [-> | Hn''].
            - destruct (Mk_n !! 0) as [Mk_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert. by rewrite Hn0.
              + rewrite lookup_insert. rewrite Hn0. 
                by rewrite (HP n') Hmn.
            - destruct (Mk_n !! 0) as [Mk_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert_ne; try done. 
              + rewrite (HP n''). by rewrite lookup_insert_ne. }
          assert (Mk !! n = Some false) as Mk_n.
          { rewrite Def_Mk' /Mk0'. 
            rewrite lookup_total_insert Def_mark; try done. apply Range_h. }
          assert (∀ x, x ≠ n → Mk !!! x = Mark s0 x !!! 0) as Def_Mk.
          { intros n' Hn'. rewrite lookup_total_alt. rewrite Def_Mk' /Mk0'.
            rewrite lookup_total_insert_ne; try done.
            rewrite Hs0 /Marki /Mark; try done. }
          assert (dom Nx ⊆ dom Nx0 ∪ {[n]}) as Dom_Nx.
          { intros n'. rewrite !elem_of_dom.
            destruct (decide (n' = n)) as [-> | Hn'].
            { intros _; clear; set_solver. }
            destruct (decide (n' = p)) as [-> | Hn''].
            { intros _; rewrite elem_of_union; left.
              rewrite Dom_Nx0 -Dom_I0. done. }
            rewrite elem_of_union. 
            rewrite Def_Nx; try done.
            rewrite Hs0 /Nexti /Next.
            destruct (Nx0 !! n') eqn: H'; try done.
            + apply elem_of_dom_2 in H'. intros _; left; done.
            + rewrite H'. rewrite lookup_empty. 
              intros [? H'']; try done. }
          assert (dom Mk = dom Mk0 ∪ {[n]}) as Dom_Mk.
          { apply set_eq_subseteq; split.
            - intros n'. 
              destruct (decide (n' = n)) as [-> | Hn'].
              { intros _; clear; set_solver. }
              intros Hn''. rewrite elem_of_dom in Hn''.
              rewrite elem_of_union. left.
              rewrite Def_Mk' /Mk0' in Hn''. 
              rewrite lookup_total_insert_ne in Hn''; try done.
              rewrite elem_of_dom.
              destruct (Mk0 !! n') eqn: H'; try done.
              rewrite lookup_total_alt in Hn''.
              rewrite H' /= in Hn''. rewrite lookup_empty in Hn''.
              destruct Hn'' as [? ?]; try done. 
            - intros n'. rewrite elem_of_union. intros [Hn' | Hn']; last first.
              { assert (n' = n) as -> by (clear -Hn'; set_solver).
                by rewrite elem_of_dom Mk_n. }
              rewrite !elem_of_dom.
              destruct (decide (n' = n)) as [-> | Hn''].
              { rewrite Dom_Mk0 in Hn'. rewrite /FP Hs0 in n_notin_s0.
                clear -n_notin_s0 Hn'. set_solver. }
              destruct (Mk !! n') eqn: H'; try done.
              rewrite Def_Mk' in H'. 
              apply not_elem_of_dom in H'. rewrite /Mk0' in H'.
              rewrite lookup_total_insert_ne in H'; try done.
              rewrite Dom_Mk0 in Hn'.
              destruct PT_s0 as (_&_&_&PT&_).
              rewrite {1}Hs0 /FP in PT.
              apply PT in Hn'. destruct Hn' as (_&_&Hn'&_).
              rewrite Hs0 /Mark in Hn'. exfalso; apply H'.
              rewrite Hn' elem_of_gset_seq; clear; lia. }
          assert (∀ x, Ky0 !!! x = Key s0 x) as Def_Ky0.
          { rewrite Hs0. unfold Key. try done. }
          set S := gset_seq (Key s0 p + 1) k.
          set res := list_flow_upd_insert n Nx Mk S I0'.
          assert (dom out_pc = gset_seq (Key s0 p + 1) W) as Dom_outpc.
          { rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
            rewrite /Marki Mark_p0 /Nexti Next_p0 in p_in_I0.
            destruct p_in_I0 as (_&H'&_&(_&->)&_).
            pose proof H' Insets_p_ne as H'.
            rewrite I0_eq_s0 /outsets H' -leibniz_equiv_iff big_opS_singleton.
            by rewrite /outset. }
          assert (S ⊂ dom out_pc) as S_sub_outpc.
          { rewrite Dom_outpc /S. rewrite elem_of_subset. split.
            - intros x; rewrite !elem_of_gset_seq. clear -Range_k; lia.
            - intros H'. pose proof H' W as H'.
              rewrite !elem_of_gset_seq in H'. clear -H' Key_p0 Range_k. lia. }
          assert (nx_key_rel Nx Ky0') as Nx_key_rel.
          { destruct PT_s0 as (_&_&_&_&H'&H''&_). intros n1 n2.
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite Nx_p. intros [=<-]. rewrite /Ky0'.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. by rewrite Def_Ky0. } 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite Nx_n. intros [=<-]. rewrite /Ky0'.
              rewrite lookup_total_insert.
              rewrite lookup_total_insert_ne; try done.
              by rewrite Def_Ky0. }
            rewrite !Def_Nx /Ky0'; try done. 
            destruct (decide (n2 = n)) as [-> | Hn2n].
            { intros H1'. pose proof H'' n1 n 0 H1' as H''.
              by apply n_notin_s0 in H''. }
            rewrite !lookup_total_insert_ne; try done.
            rewrite !Def_Ky0. apply H'. }
          assert (dom I0' = dom I0 ∪ {[n]}) as Dom_I0'.
          { rewrite /I0'. rewrite !dom_insert_L. 
            clear -p_in_I0. set_solver. }
          assert (nx_mk_closed Nx Mk (dom I0')) as Hcl.
          { split; last split; last split. 
            - by rewrite Dom_I0' Dom_I0 -Dom_Nx0.
            - by rewrite Dom_Mk Dom_I0' Dom_Mk0 Dom_I0.
            - destruct PT_s0 as (_&_&_&_&_&H'&_). intros n1 n2.
              destruct (decide (n1 = n)) as [-> | Hn1n].
              + rewrite Nx_n. intros [=<-]. rewrite Dom_I0'.
                clear -c_in_I0; set_solver.
              + destruct (decide (n1 = p)) as [-> | Hn1p].
                * rewrite Nx_p. intros [=<-]. rewrite Dom_I0'.
                  clear; set_solver.
                * rewrite Def_Nx; try done. intros H''%H'.
                  rewrite Hs0 /FP -Dom_I0 in H''. rewrite Dom_I0'.
                  clear -H''; set_solver.
            - intros x Hmx Hnx. assert (x ≠ n) as Hxn. intros ->. 
              rewrite Mk_n in Hmx. clear -Hmx; try done.
              assert (x ∈ FP s0) as H'. rewrite /FP Hs0 -Dom_Mk0.
              apply elem_of_dom_2 in Hmx. clear -Hmx Hxn Dom_Mk; set_solver.
              apply PT_s0 in H'. destruct H' as (_&H'&_).
              destruct (decide (x = tl)) as [-> | Hxtl].
              + destruct PT_s0 as ((_&_&_&_&H''&_)&_).
                pose proof H'' 0 as H''. rewrite -Def_Mk in H''; try done.
                apply lookup_total_correct in Hmx. rewrite Hmx in H''.
                clear -H'' HL; try (done || lia).
              + apply H' in Hxtl. assert (x ≠ p) as Hxp. 
                intros ->. rewrite Nx_p in Hnx. clear -Hnx; done. 
                rewrite Def_Nx in Hnx; try done. 
                rewrite -not_elem_of_dom Hxtl in Hnx. apply Hnx.
                rewrite elem_of_gset_seq. clear; lia. } 
          assert (([^op set] x ∈ dom I0', (I0' !!! x: multiset_flowint_ur nat))
            = Ip0' ⋅ In0' ⋅ Io) as Def_I0'.
          { rewrite (big_opS_delete _ _ n); last first.
            { rewrite Dom_I0'. clear; set_solver. }
            rewrite (big_opS_delete _ _ p); last first.
            { rewrite Dom_I0' elem_of_difference. split.
              clear -p_in_I0; set_solver. clear -n_neq_p; set_solver. }
              assert (([^op set] y ∈ (dom I0' ∖ {[n]} ∖ {[p]}), I0' !!! y) = Io)
                as <-.
              { rewrite /Io. 
                assert (dom I0' ∖ {[n]} ∖ {[p]} = dom I0 ∖ {[p]}) as ->.
                { rewrite Dom_I0'. clear -n_notin_I0 n_neq_p p_in_I0. 
                  set_solver. }
                apply big_opS_ext. intros x Hx. rewrite /I0'.
                rewrite !lookup_total_insert_ne; try done.
                clear -Hx; set_solver. clear -Hx n_notin_I0. set_solver. }
              rewrite {1 2}/I0'. rewrite lookup_total_insert. 
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. by rewrite assoc (comm _ Ip0' In0'). }
          assert (✓ ([^op set] x ∈ dom I0', (I0' !!! x: multiset_flowint_ur nat))) 
            as VI0'.
          { rewrite Def_I0'. by destruct ContLeq0' as (_&?&_). }
          assert (∀ n1 n2, insets (I0' !!! n1) ≠ ∅ → Nx !! n1 = Some n2 → 
            dom (out_map (I0' !!! n1: multiset_flowint_ur nat)) = {[n2]}) 
            as Nx_dom.
          { intros n1 n2. destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite Nx_n; intros Hin [=<-]. rewrite /I0'. 
              rewrite lookup_total_insert. rewrite /In0'.
              simpl. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done. 
              clear. unfold dom, nzmap_dom. set_solver. }
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite Nx_p; intros Hin [=<-]. rewrite /I0'.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. rewrite /Ip0'.
              simpl. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done. 
              clear. unfold dom, nzmap_dom. set_solver. }
            intros Hin Hn1. assert (Hn1' := Hn1). apply elem_of_dom_2 in Hn1.
            apply Dom_Nx in Hn1. rewrite elem_of_union in Hn1.
            destruct Hn1 as [Hn1 | Hn1]; last first.
            { clear -Hn1 Hn1n; set_solver. } rewrite Dom_Nx0 -Dom_I0 in Hn1.
            apply Hflow in Hn1. rewrite Def_Nx in Hn1'. rewrite Hn1' in Hn1.
            destruct Hn1 as (_&H'&_). 
            rewrite /I0' !lookup_total_insert_ne; try done.
            rewrite /I0' in Hin. rewrite !lookup_total_insert_ne in Hin; try done.
            rewrite -I0_eq_s0 in H'. apply H'. all: done. }
          assert (n ∈ dom I0') as n_in_I0'.
          { rewrite Dom_I0'; clear; set_solver. }
          assert (∀ x, x ∈ dom I0' → Mk !!! x = true → 
            keyset (I0' !!! x) = ∅) as KS_mk.
          { intros x Hx Hmkx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx]; last first.
            { assert (x = n) as -> by (clear -Hx; set_solver).
              by rewrite lookup_total_alt Mk_n /= in Hmkx. }
            assert (x ≠ n) by (clear -Hx n_notin_I0; set_solver).
            apply Hflow in Hx. rewrite Def_Mk in Hmkx. rewrite Hmkx in Hx.
            destruct Hx as (_&_&_&Hx&_). rewrite /I0'.
            rewrite lookup_total_insert_ne; try done.
            destruct (decide (x = p)) as [-> | Hxp].
            { rewrite /Marki Mark_p0 in Hmkx. clear -Hmkx; done. }
            rewrite lookup_total_insert_ne; try done.
            by rewrite I0_eq_s0. done. }
          assert (∀ x : Node, x ∈ dom I0' → dom (I0' !!! x) = {[x]}) 
            as Domm_I0'.
          { intros x Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx]; last first. 
            { assert (x = n) as -> by (clear -Hx; set_solver).
              rewrite /I0' lookup_total_insert /In0'.
              rewrite /dom /flowint_dom /=. by rewrite dom_singleton_L. }
            assert (x ≠ n) by (clear -Hx n_notin_I0; set_solver).
            rewrite /I0' lookup_total_insert_ne; try done.
            destruct (decide (x = p)) as [-> | Hxp].
            { rewrite lookup_total_insert /Ip0'. rewrite /dom /flowint_dom /=.
              apply Domm_I0 in p_in_I0. apply p_in_I0. }
            rewrite lookup_total_insert_ne; try done.
            apply Domm_I0; try done. }
          assert (S ⊂ insets (I0' !!! n)) as Insets_S.
          { rewrite /insets Domm_I0'; try done.
            rewrite /I0' lookup_total_insert.
            assert (([^union set] x ∈ {[n]}, inset nat In0' x) =
              inset nat In0' n) as ->.
            { by rewrite -leibniz_equiv_iff big_opS_singleton. }
            by rewrite /In0' /inset /inf /= lookup_insert /=. }
          assert (S ⊂ outset _ (I0' !!! n) c) as Outset_S.
          { by rewrite /I0' lookup_total_insert /In0' /outset /out /= 
              nzmap_lookup_total_insert. }
          assert (∀ x k', x ∈ dom I0' → 
            inf (I0' !!! x : multiset_flowint_ur _) x !!! k' ≤ 1) as Inf_x.
          { intros x k' Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx].
            - assert (Hx' := Hx). apply Hflow in Hx. 
              destruct Hx as (_&_&_&_&_&H'&_). rewrite /I0'.
              rewrite lookup_total_insert_ne; last first.
              { clear -Hx' n_notin_I0. set_solver. } 
              destruct (decide (x = p)) as [-> | Hxp].
              + rewrite lookup_total_insert /Ip0' /inf /= /Ip0.
                rewrite /inf -I0_eq_s0 in H'. apply H'.
              + rewrite lookup_total_insert_ne; try done.
                rewrite I0_eq_s0. apply H'.
            - rewrite elem_of_singleton in Hx; subst x.
              rewrite /I0' lookup_total_insert /In0' /inf /= lookup_insert /=.
              rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
              destruct p_in_I0 as (_&_&_&_&_&_&H').
              rewrite I0_eq_s0; apply H'. }
          assert (∀ x x' k, x ∈ dom I0' → 
            out (I0' !!! x : multiset_flowint_ur _) x' !!! k ≤ 1)
            as Out_x.
          { intros x x' k' Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx].
            - assert (Hx' := Hx). apply Hflow in Hx. 
              destruct Hx as (_&_&_&_&_&_&H'). rewrite /I0'.
              rewrite lookup_total_insert_ne; last first.
              { clear -Hx' n_notin_I0. set_solver. } 
              destruct (decide (x = p)) as [-> | Hxp].
              + rewrite lookup_total_insert /Ip0' /out /= /Ip0.
                destruct (decide (x' = n)) as [-> | Hx'n]; last first.
                { rewrite nzmap_lookup_total_insert_ne; try done.
                  rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia. }
                rewrite nzmap_lookup_total_insert.
                rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
                destruct p_in_I0 as (_&_&_&_&_&_&H'').
                rewrite I0_eq_s0; apply H'.
              + rewrite lookup_total_insert_ne; try done.
                apply Hflow in Hx'. rewrite I0_eq_s0; apply Hx'.
            - rewrite elem_of_singleton in Hx; subst x.
              rewrite /I0' lookup_total_insert /In0' /out /=.
              destruct (decide (x' = c)) as [-> | Hx'c]; last first.
              { rewrite nzmap_lookup_total_insert_ne; try done.
                rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia. }
              rewrite nzmap_lookup_total_insert.
              rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
              destruct p_in_I0 as (_&_&_&_&_&_&H').
              rewrite I0_eq_s0; apply H'. }
          assert (∀ x, x ∈ dom I0' → Mk !!! x = false → 
            Ky0' !!! n < Ky0' !!! x → S ## outsets (I0' !!! x)) as Disj_outsets.
          { intros x Hx Mk_x Hkey. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx]; last first.
            { rewrite elem_of_singleton in Hx; subst x. 
              clear -Hkey; lia. }
            rewrite /Ky0' lookup_total_insert lookup_total_insert_ne 
                in Hkey; try done. rewrite Def_Ky0 in Hkey.
            destruct (decide (x = p)) as [-> | Hxp].
            { clear -Hkey Key_pn; lia. }
            rewrite elem_of_disjoint. intros k' Hk1' Hk2'.
            destruct PT_s0 as (_&_&_&H'&_). rewrite {1}Hs0 /FP -Dom_I0 in H'.
            assert (Hx1 := Hx). apply H' in Hx. 
            destruct Hx as (_&_&_&_&_&Hx &Hx'). 
            assert (Mark s0 x !!! 0 = false) as Hm.
            { rewrite -Def_Mk; try done. clear -Hx1 n_notin_I0; set_solver. } 
            rewrite Hm in Hx'. destruct Hx' as (_&_&(_&H'')&_).
            rewrite /I0' !lookup_total_insert_ne in Hk2'; try done.
            rewrite I0_eq_s0 -H'' in Hk2'. rewrite elem_of_gset_seq in Hk2'.
            rewrite /S elem_of_gset_seq in Hk1'. 
            clear -Hkey Key_pn Hk1' Hk2'; lia.
            clear -Hx1 n_notin_I0; set_solver.
            clear -Hx n_notin_I0; set_solver. }
          
          assert (insets (I0' !!! p) ≠ ∅) as Insets_p_ne'.
          { assert (insets (I0' !!! p) = insets (FI s0 p)) as H'.
            { rewrite /I0' lookup_total_insert_ne; try done.
              rewrite lookup_total_insert /insets -Dom_Ip0' /Ip0 -I0_eq_s0.
              rewrite Domm_I0; try done. }
            by rewrite -H' in Insets_p_ne. }
          assert (insets (I0' !!! n) ≠ ∅) as Insets_n_ne'.
          { intros H'. rewrite H' in Insets_S. clear -Insets_S Key_pn.
            assert (Key s0 p + 1 ∈ S). rewrite /S elem_of_gset_seq. lia.
            set_solver. }

          assert (∀ x, x ∈ dom I0' → outsets (I0' !!! x) ⊆ insets (I0' !!! x))
            as Out_In.
          { intros x Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx].
            - assert (Hx' := Hx). apply Hflow in Hx.
              destruct Hx as (Hx0&Hx1&Hx2&_).
              destruct (decide (x = p)) as [-> | Hxp].
              + rewrite /insets /outsets Domm_I0'; try done; last first.
                { rewrite Dom_I0' elem_of_union; by left. }
                rewrite (Nx_dom p n Insets_p_ne' Nx_p) !big_opS_singleton.
                rewrite /I0' lookup_total_insert_ne; last done.
                rewrite lookup_total_insert /Ip0'.
                rewrite /outset /out /inset /inf /= /Ip0.
                rewrite nzmap_lookup_total_insert.
                rewrite /Nexti Next_p0 in Hx1.
                rewrite /outsets /insets Hx0 Hx1 in Hx2. 
                rewrite !big_opS_singleton in Hx2.
                rewrite -I0_eq_s0 /outset /inset in Hx2. apply Hx2. done.
              + rewrite /I0' !lookup_total_insert_ne; try done.
                by rewrite I0_eq_s0. clear -Hx' n_notin_I0; set_solver.
            - rewrite elem_of_singleton in Hx; subst x.
              rewrite /outsets /insets Domm_I0'; try done.
              rewrite (Nx_dom n c Insets_n_ne' Nx_n) !big_opS_singleton.
              rewrite /I0' lookup_total_insert /In0' /outset /inset /out /inf 
                nzmap_lookup_total_insert lookup_insert /=. done. }
          assert (list_flow_upd_insert n Nx Mk S I0' = res) as Hflow'.
          { by rewrite /res. } 
          
          pose proof insert_flow_updk_summary Ky0' n Nx Mk S I0' res c
            Nx_key_rel Hcl KS_mk Disj_outsets Nx_dom Out_In Nx_n VI0' 
            Domm_I0' n_in_I0' Insets_S Outset_S Inf_x Out_x Hflow' 
            as [II [nk [-> Hres]]].
          destruct Hres as [Dom_II_sub_I0 [n_in_II [nk_in_II [n_neq_nk [Mk_nk 
            [Mk_x [Nx_x [Key_n [Domm_II [Heq [II_n [II_nk [II_x [Inf_x' [Out_x' 
            [Insets_ne [Dom_out [Out_In' [KS_n [KS_nk 
            [KS_x S_in_nk]]]]]]]]]]]]]]]]]]]]].
          clear Hflow'.
          set I := intf_merge II I0'.
          assert (dom I = dom I0') as Dom_I.
          { rewrite /I intf_merge_dom; try done. }
          assert (([^op set] x ∈ dom I, I !!! x) =
          ([^op set] x ∈ dom I0', I0' !!! x : multiset_flowint_ur nat)) as Def_I.
          { pose proof intf_merge_intfEq II I0' I Dom_II_sub_I0 Heq as H'.
            rewrite Dom_I. symmetry. apply H'. by rewrite /I. }
          assert (nk ∈ FP s0) as nk_in_s0.
          { rewrite Hs0 /FP -Dom_I0. rewrite Dom_I0' in Dom_II_sub_I0.
            clear -Dom_II_sub_I0 nk_in_II n_neq_nk. set_solver. }
          assert (nk ∈ dom I0) as nk_in_I0.
          { by rewrite Hs0 /FP -Dom_I0 in nk_in_s0. }
          assert (p ∉ dom II) as p_notin_II.
          { intros H'. assert (p ∈ dom II ∖ {[n]}) as H''. clear -H' n_neq_p.
            set_solver. apply Key_n in H''. 
            rewrite /Ky0' lookup_total_insert in H''.
            rewrite lookup_total_insert_ne in H''; try done.
            rewrite Hs0 /Key in Key_pn. clear -H'' Key_pn.
            assert (Ky0 !!! p = match Ky0 !! p with Some k => k | None => 0 end)
              as H1'. done. rewrite -H1' in Key_pn. lia. }
          assert (I0' !!! nk = I0 !!! nk) as I0'_nk.
          { rewrite /I0' !lookup_total_insert_ne; try done. 
            clear -p_notin_II nk_in_II; set_solver. }
          assert (keyset (I0' !!! n) = ∅) as KS_n'.
          { rewrite /keyset /insets /outsets Domm_I0'; try done.
            rewrite (Nx_dom n c Insets_n_ne' Nx_n) -leibniz_equiv_iff !big_opS_singleton.
            rewrite /inset /outset /I0' lookup_total_insert /In0' /inf /out /=.
            rewrite lookup_insert nzmap_lookup_total_insert /=.
            clear; set_solver. }
          assert (S ⊆ keyset (I0 !!! nk)) as S_in_ksnk.
          { by rewrite -I0'_nk. }
          assert (keyset Ip0' = keyset (I0 !!! p)) as KS_Ip0'.
          { rewrite /keyset. assert (insets Ip0' = insets (I0 !!! p)) as ->. 
            rewrite /insets /Ip0' /dom /flowint_dom /= /Ip0.
            apply big_opS_ext. intros x Hx. by rewrite /inset /inf /=.
            assert (outsets Ip0' = outsets (I0 !!! p)) as ->.
            rewrite /outsets. apply Hflow in p_in_I0.
            rewrite /Nexti Next_p0 -I0_eq_s0 in p_in_I0. 
            destruct p_in_I0 as (_&->&_). pose proof Nx_dom p n Insets_p_ne' Nx_p as H'.
            rewrite /I0' lookup_total_insert_ne in H'; try done.
            rewrite lookup_total_insert in H'. rewrite H'.
            rewrite -leibniz_equiv_iff !big_opS_singleton.
            rewrite /outset /Ip0' {1}/out /= nzmap_lookup_total_insert.
            clear; done. rewrite I0_eq_s0; done. done. }
          assert (k < Key s0 nk) as k_lt_nk.
          { assert (nk ∈ dom II ∖ {[n]}) as H'.
            clear -nk_in_II n_neq_nk. set_solver.
            apply Key_n in H'. rewrite /Ky0' lookup_total_insert in H'.
            rewrite lookup_total_insert_ne in H'; try done.
            by rewrite Def_Ky0 in H'. } 
          exists I, nk. split; last split; last split; last split; 
            last split; last split; last split; last split; last split; 
            last split; last split; last split; last split; last split;
            last split; last split.
          - by rewrite Dom_I Dom_I0' Hs0 /FP -Dom_I0.
          - done.
          - done.
          - done.
          - rewrite -Def_Mk; try done. by rewrite lookup_total_alt Mk_nk /=.
          - rewrite /I intf_merge_lookup_total; try done. rewrite KS_n.
            rewrite elem_of_union /S; right. rewrite elem_of_gset_seq.
            clear -Key_pn. split; lia.
          - intros H'. rewrite /I intf_merge_lookup_total; try done. 
            rewrite KS_nk elem_of_difference. split. by rewrite I0'_nk.
            rewrite /S elem_of_gset_seq. clear -k_lt_nk; lia. 
          - rewrite /I !intf_merge_lookup_total; try done. rewrite KS_n KS_nk.
            rewrite I0'_nk KS_n'. clear -S_in_ksnk; apply set_eq_subseteq. 
            split; first by set_solver. intros x Hx.
            rewrite !elem_of_union elem_of_difference.
            destruct (decide (x ∈ S)); try set_solver.
          - rewrite /I !intf_merge_lookup_total; try done. 
            rewrite KS_n KS_nk KS_n'. clear; set_solver.
          - intros x Hx. destruct (decide (x ∈ dom II)) as [Hx' | Hx'].
            + rewrite /I intf_merge_lookup_total; try done.
              rewrite KS_x; try done. rewrite /I0' !lookup_total_insert_ne.
              done. clear -p_notin_II Hx'; set_solver. clear -Hx; set_solver.
              clear -Hx Hx'; set_solver.
            + rewrite /I intf_merge_lookup_total_ne; try done.
              destruct (decide (x = p)) as [-> | Hxp].
              * rewrite /I0' lookup_total_insert_ne; try done.
                by rewrite lookup_total_insert.
              * rewrite /I0' !lookup_total_insert_ne; try done.
                clear -Hx; set_solver.
              * rewrite Dom_I in Hx. clear -Hx Hx'; set_solver.
          - by rewrite Def_I. 
          - intros n1 n2. destruct PT_s0 as (_&_&_&_&PT&PT'&_). 
            rewrite /Nexti /Next Hs0 /Key in PT. rewrite /Nx0'. 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite lookup_total_insert /Ky0'. intros H'. assert (H'' := H').
              rewrite Def_next in H'; last first. apply elem_of_dom_2 in H''.
              rewrite Dom_next elem_of_gset_seq in H''. clear -H'' Range_h. lia.
              inversion H'. apply list_lookup_total_correct in Hss0. rewrite Hss0.
              rewrite lookup_total_insert. rewrite lookup_total_insert_ne; try done.
              rewrite Def_Ky0. done. }
            rewrite lookup_total_insert_ne; try done.
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite lookup_total_insert Def_next'.
              rewrite lookup_insert. intros [=<-].
              rewrite /Ky0' lookup_total_insert_ne; try done.
              by rewrite lookup_total_insert Def_Ky0. }
            rewrite lookup_total_insert_ne; try done.
            destruct (decide (n2 = n)) as [-> | Hn2n].
            { rewrite /Nexti /Next {1}Hs0 in PT'. intros H'%PT'. 
              clear -H' n_notin_s0; done. }
            rewrite !lookup_total_insert_ne; try done. apply PT.
          - intros n1 n2 i. destruct PT_s0 as (_&_&_&_&_&PT&_).
            rewrite /Nexti /Next {1}Hs0 FP_s0_I0 in PT. rewrite /Nx0' Dom_I Dom_I0'. 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite lookup_total_insert. intros H'. assert (H'' := H').
              rewrite Def_next in H'; last first. apply elem_of_dom_2 in H''.
              rewrite Dom_next elem_of_gset_seq in H''. clear -H'' Range_h. lia.
              inversion H'. apply elem_of_dom_2 in H''. 
              rewrite Dom_next elem_of_gset_seq in H''. assert (i < L) as Hi.
              clear -H'' Range_h; lia. rewrite elem_of_union. left.
              rewrite -FP_s0_I0. by apply Hss_fp. }
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert Def_next'.
              destruct (decide (i = 0)) as [-> | Hi0].
              rewrite lookup_insert. intros [=<-]. clear; set_solver.
              rewrite lookup_insert_ne; try done.
              destruct (decide (n2 = n)) as [-> | Hn2n].
              { intros _; clear; set_solver. }
              rewrite /Next Hs0. intros H'%PT. clear -H' Hn2n; set_solver. }
            rewrite !lookup_total_insert_ne; try done.
            intros H'%PT. clear -H'; set_solver.
          - intros x Hx Hxp Hxn. destruct (decide (x ∈ dom II)) as [Hx' | Hx'].
            + rewrite /I intf_merge_lookup_total; try done.
              assert (I0' !!! x = I0 !!! x) as HI. 
              { rewrite /I0' !lookup_total_insert_ne; try done. }
              assert (insets (II !!! x) = insets (FI s0 x) ∖ S) as HInset.
              { rewrite /insets Domm_II; try done.
                assert (dom (FI s0 x) = {[x]}) as ->.
                { rewrite -I0_eq_s0 Domm_I0; try done. 
                  rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn; set_solver. }
                rewrite -leibniz_equiv_iff !big_opS_singleton.
                destruct (decide (x = nk)) as [-> | Hxnk].
                rewrite II_nk HI.
                rewrite inflow_delete_set_inset I0_eq_s0. done.
                apply Hflow in nk_in_I0. destruct nk_in_I0 as (_&_&_&_&_&H'&_).
                intros k' Hk'. apply H'.
                rewrite II_x /outflow_delete_set. rewrite outflow_map_set_inset.
                rewrite inflow_delete_set_inset HI I0_eq_s0. done.
                assert (x ∈ dom I0) as x_in_I0%Hflow.
                { rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn. set_solver. }
                destruct x_in_I0 as (_&_&_&_&_&H'&_). intros k' Hk'. apply H'.
                clear -Hx' Hxnk Hxn; set_solver. }
              destruct (decide (x = nk)) as [-> | Hxnk].
              * apply Hflow in nk_in_I0 as Hnk.
                destruct Hnk as (H1'&H2'&H3'&H4'&H5'&H6'&H7').
                apply lookup_total_correct in Mk_nk.
                rewrite -Def_Mk; last done. rewrite Mk_nk.
                rewrite -Def_Nx; [|done|done]. 
                split; last split; last split; last split; last split; last split.
                { apply Domm_II; try done. }
                { rewrite Dom_out; try done. rewrite HI I0_eq_s0 H2'.
                  rewrite Def_Nx; try done. pose proof Insets_ne nk nk_in_II as H'.
                  by rewrite I0'_nk I0_eq_s0 in H'. }
                { apply Out_In'; try done. }
                { rewrite -Def_Mk in H4'; try done. rewrite Mk_nk in H4'.
                  destruct H4' as [H4' H4'']. split.
                  rewrite HInset. intros k' Hk'. rewrite elem_of_difference. 
                  split. by apply H4' in Hk'.
                  intros Hk''. apply elem_of_gset_seq in Hk'.
                  apply elem_of_gset_seq in Hk''.
                  clear -k_lt_nk Hk' Hk''. lia.
                  by rewrite II_nk inflow_delete_set_outsets HI I0_eq_s0. }
                { rewrite HInset. intros k'; clear -H5'; set_solver. }
                { intros k'; apply Inf_x'; try done. }
                { intros x' k'; apply Out_x'; try done. }
              * assert (x ∈ dom I0) as Hx''%Hflow. 
                { rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn. set_solver. }
                assert (Mark s0 x !!! 0 = true) as HM. 
                { rewrite -Def_Mk; try done. rewrite lookup_total_alt Mk_x /=.
                  done. clear -Hx' Hxn Hxnk; set_solver. }
                rewrite HM. rewrite HM in Hx''.
                destruct Hx'' as (H1'&H2'&H3'&H4'&H5'&H6'&H7').
                split; last split; last split; last split; last split; last split.
                { apply Domm_II; try done. }
                { rewrite Dom_out; try done. intros Hin. rewrite HI I0_eq_s0.
                  apply H2'. pose proof Insets_ne x Hx' as H'.
                  rewrite /I0' !lookup_total_insert_ne in H'; try done.
                  by rewrite I0_eq_s0 in H'. }
                { apply Out_In'; try done. }
                { rewrite KS_x. by rewrite HI I0_eq_s0.
                  clear -Hx' Hxn Hxnk; set_solver. }
                { rewrite HInset. intros k'; clear -H5'; set_solver. }
                { intros k'; apply Inf_x'; try done. }
                { intros x' k'; apply Out_x'; try done. }
            + rewrite /I intf_merge_lookup_total_ne; last first; try done.
              { rewrite Dom_I in Hx. clear -Hx Hx'; set_solver. }
              rewrite /I0'. rewrite !lookup_total_insert_ne; try done.
              rewrite I0_eq_s0. apply Hflow.
              rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn; set_solver.
          - assert (p ∈ dom I0') as p_in_I0'.
            { rewrite Dom_I0'. clear -p_in_I0; set_solver. }
            rewrite /I intf_merge_lookup_total_ne; try done; last first.
            { rewrite Dom_I0'. clear -p_in_I0 n_neq_p p_notin_II; set_solver. }
            rewrite /I0'. rewrite lookup_total_insert_ne; try done.
            rewrite lookup_total_insert. apply Hflow in p_in_I0. 
            rewrite -I0_eq_s0 in p_in_I0.
            rewrite /Marki Mark_p0 /Nexti Next_p0 in p_in_I0.
            destruct p_in_I0 as (H1'&H2'&H3'&H4'&H5'&H6'&H7').
            repeat split; try done.
            { intros _. rewrite /Ip0' /out_map /=. apply leibniz_equiv.
              rewrite nzmap_dom_insert_nonzero; try done.
              rewrite /dom /nzmap_dom. clear; set_solver. }
            { apply Out_In in p_in_I0'. rewrite /I0' in p_in_I0'.
              rewrite lookup_total_insert_ne in p_in_I0'; try done.
              rewrite lookup_total_insert in p_in_I0'; try done. }
            { rewrite /insets -Dom_Ip0' /Ip0 H1'. rewrite big_opS_singleton.
              rewrite /Ip0' /inset /inf /= /Ip0.
              destruct H4' as [H4' _].
              rewrite /insets H1' in H4'. rewrite big_opS_singleton in H4'.
              rewrite /inset in H4'. apply H4'. }
            { assert (outsets Ip0' = outsets (I0 !!! p)) as ->.
              rewrite -I0_eq_s0 in Insets_p_ne.
              rewrite /outsets (H2' Insets_p_ne) {2}/Ip0' /out_map /=.
              assert (dom <<[ n := out_pc ]>> ∅ = {[n]}) as ->.
              rewrite -leibniz_equiv_iff. rewrite nzmap_dom_insert_nonzero; try done.
              clear; rewrite /dom. set_solver.
              rewrite -leibniz_equiv_iff !big_opS_singleton.
              rewrite /Ip0' /outset /out {1}/out_map /= nzmap_lookup_total_insert.
              rewrite /out_pc. done.
              apply H4'. }
            { intros x' k'. apply (Out_x _ x' k') in p_in_I0'. 
              rewrite /I0' in p_in_I0'.
              rewrite lookup_total_insert_ne in p_in_I0'; try done.
              rewrite lookup_total_insert in p_in_I0'; try done. }
          - rewrite /I intf_merge_lookup_total; try done.
            rewrite II_n /I0' lookup_total_insert.
            assert (dom (out_map (outflow_delete_set In0' c S)) = {[c]}) as Hdom.
            { apply Dom_out in n_in_II. rewrite II_n {1}/I0' in n_in_II.
              rewrite lookup_total_insert in n_in_II.
              rewrite n_in_II. pose proof Nx_dom n c Insets_n_ne' Nx_n as H'.
              by rewrite /I0' lookup_total_insert in H'. }
            assert (insets In0' = dom out_pc) as Hinset.
            { rewrite /insets Dom_In0' -leibniz_equiv_iff big_opS_singleton.
              by rewrite /inset /In0' /inf /= lookup_insert /=. }
            assert (∀ x' k', out In0' x' !!! k' ≤ 1) as Out_In0'.
            { apply Dom_II_sub_I0 in n_in_II.
              intros x' k'. apply (Out_x _ x' k') in n_in_II.
              rewrite /I0' lookup_total_insert in n_in_II. apply n_in_II. }
            repeat split; try done.
            { rewrite outflow_delete_set_insets /outsets Hdom.
              rewrite big_opS_singleton outflow_delete_set_outset; try done.
              rewrite Hinset /In0' /outset /out /= nzmap_lookup_total_insert.
              clear; set_solver. }
            { rewrite outflow_delete_set_insets Hinset Dom_outpc.
              intros k'; rewrite !elem_of_gset_seq. clear -Key_pn; lia. }
            { rewrite /outsets Hdom. rewrite -leibniz_equiv_iff big_opS_singleton.
              rewrite outflow_delete_set_outset; try done.
              rewrite /In0' /outset /out /= nzmap_lookup_total_insert Dom_outpc.
              rewrite /S. rewrite leibniz_equiv_iff set_eq_subseteq.
              split; intros k'; rewrite elem_of_difference !elem_of_gset_seq.
              all: clear -Key_pn; lia. }
            { rewrite outflow_delete_set_insets Hinset Dom_outpc.
              intros k'; rewrite elem_of_gset_seq. clear; lia. } 
            { intros k'. apply (Inf_x' _ k') in n_in_II.
              by rewrite II_n /I0' lookup_total_insert in n_in_II. }
            { intros x' k'. apply (Out_x' _ x' k') in n_in_II.
              by rewrite II_n /I0' lookup_total_insert in n_in_II. }
          - intros ->. destruct PT_s0 as ((_&_&H'&_)&_). rewrite H' in Key_p0.
            clear -Key_p0; lia. }
        set s0' := (FP0 ∪ {[n]}, C0 ∪ {[k]}, Ht0', Mk0', Nx0', Ky0', I): snapshot.
        set M0' := <[T0+1 := s0']> M0.
        assert (abs s0 = C0) as Habs0'.
        { rewrite Hs0. by unfold abs. }
        iAssert (⌜snapshot_constraints s0'⌝)%I as "SShot0'".
        { iPureIntro. exists (FP0 ∪ {[n]}), (C0 ∪ {[k]}), Ht0', Mk0', 
            Nx0', Ky0', I. repeat split; try done.
          rewrite /Ht0'. rewrite dom_insert_L. 
          rewrite Dom_Ht0. clear; set_solver.
          rewrite /Mk0'. rewrite dom_insert_L. 
          rewrite Dom_Mk0. clear; set_solver.
          rewrite /Nx0'. rewrite !dom_insert_L.
          rewrite Dom_Nx0. rewrite Hs0 in FP_p0. unfold FP in FP_p0. 
          clear -FP_p0; set_solver.
          rewrite /Ky0'. rewrite dom_insert_L.
          rewrite Dom_Ky0. clear; set_solver.
          destruct Hflupd as (H' & _). rewrite Hs0 in H'; by unfold FP in H'. }

        assert (FP s0' = FP s0 ∪ {[n]}) as FP_s0'.
        { by rewrite Hs0 /s0'; unfold FP. }
        assert (∀ n', n' ≠ p → n' ≠ n → Next s0' n' = Next s0 n') as HN.
        { intros n' Hp Hn. rewrite /Next /s0' Hs0 /= /Nx0'.
          rewrite !lookup_insert_ne; try done. }
        assert (Next s0' n = next) as HNn.
        { rewrite /Next /s0' /= /Nx0'. rewrite lookup_insert; try done. }
        assert (Next s0' p = <[0:=n]> (Next s0 p)) as HNp.
        { rewrite /Next /s0' Hs0 /= /Nx0'. rewrite lookup_insert_ne; try done.
          rewrite lookup_insert Def_next' /Next Hs0. done. }
        assert (∀ n', n' ≠ n → Key s0' n' = Key s0 n') as HK.
        { intros n' Hn. rewrite /Key /s0' Hs0 /= /Ky0'. 
          rewrite lookup_insert_ne; try done. }
        assert (Key s0' n = k) as HKn.
        { rewrite /Key /s0' /= /Ky0' lookup_insert; try done. }
        assert (∀ n', n' ≠ n → Height s0' n' = Height s0 n') as HT.
        { intros n' Hn. rewrite /Height /s0' Hs0 /= /Ky0'. 
          rewrite lookup_insert_ne; try done. }
        assert (Height s0' n = h) as HTn.
        { rewrite /Key /s0' /= /Ht0' lookup_insert; try done. }
        assert (∀ n', FI s0' n' = I !!! n') as HI.
        { by rewrite /FI /s0' /=. }
        assert (∀ n', n' ≠ n → Mark s0' n' = Mark s0 n') as HM.
        { intros n' Hn. by rewrite /FI /s0' Hs0 /Mk0' /= lookup_insert_ne. }
        assert (Mark s0' n = mark) as HMn.
        { by rewrite /FI /s0' /Mk0' /= lookup_insert. }
        assert (n ≠ hd) as n_neq_hd. 
        { intros ->. destruct PT_s0 as (PT&_). 
          destruct PT as (H'&_). clear -H' n_notin_s0. set_solver. }
        assert (n ≠ tl) as n_neq_tl. 
        { intros ->. destruct PT_s0 as (PT&_). 
          destruct PT as (H'&_). clear -H' n_notin_s0. set_solver. }

          iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> resources γ_ks s0' ∗ ⌜k ∉ abs s0⌝)%I 
          with "[GKS Nodes_KS Node_n Node_p Nodes_rest]" as ">(Res & %k_notin_s0)".
        { rewrite (big_sepS_delete _ _ nk); last first. 
          { apply Hflupd. }
          iDestruct "Nodes_KS" as "(KS_nk & Nodes_KS)".
          iAssert (⌜k ∉ abs s0⌝)%I as %k_notin_s0.
          { iPoseProof (own_valid_2 with "GKS KS_nk") as "%H'".
            iDestruct (own_valid with "KS_nk") as "%Vnk".
            iDestruct (own_valid with "GKS") as "%VKS".
            iPureIntro. apply auth_both_valid_discrete in H'.
            rewrite auth_frag_valid auth_auth_valid in Vnk VKS.
            destruct H' as [H' _]. apply auth_ks_included in H'; try done.
            assert (Mark s0 nk !!! 0 = false) as Mark_nk0. apply Hflupd.
            assert (nk ∈ FP s0) as Hnk. apply Hflupd.
            assert (k < Key s0 nk) as Hk. apply Hflupd.
            apply PT_s0 in Hnk. destruct Hnk as (_&_&_&_&_&_&H'').
            rewrite Mark_nk0 in H''. 
            assert (k ∉ Content s0 nk) as Hcont.
            { rewrite /Content /Marki Mark_nk0 elem_of_singleton. clear -Hk; lia. }
            assert (k ∈ keyset (FI s0 nk)) as Hks.
            { rewrite Hs0 /FI. destruct Hflupd as (_&_&_&_&_&H1'&_&H1''&_).
              rewrite -H1''. clear -H1'; set_solver. }
            destruct H' as [KSr [Cr H']].
            clear -H' Hcont Hks; set_solver. } iFrame "%".
          iDestruct (own_valid with "KS_nk") as "%H'".
          iDestruct (own_valid with "GKS") as "%H''".
          rewrite auth_frag_valid in H'. rewrite auth_auth_valid in H''.
          assert (k ∈ keyset (I !!! n)) as KS_n.
          { apply Hflupd. }
          assert (Marki s0 nk 0 = false) as Mark_nk.
          { apply Hflupd. }
          assert (Key s0 nk ∈ keyset (I !!! nk)) as KS_nk.
          { apply Hflupd. rewrite /valid /cmra_valid /= /ucmra_valid /= in H'.
            rewrite /Content Mark_nk {2}Hs0 /FI in H'. clear -H'; set_solver. }
          assert (k ≠ Key s0 nk) as k_neq_Keynk.
          { intros H1'. destruct Hflupd as (_&_&_&H1''&_).
            rewrite H1' in H1''. clear -H1''; lia. }
          assert (Marki s0' nk 0 = false) as Mark_nk'.
          { rewrite /Marki /Mark /s0' /Mk0' lookup_insert_ne.
            by rewrite /Marki /Mark Hs0 in Mark_nk.
            apply Hflupd. }
          assert (Marki s0' n 0 = false) as Mark_n'.
          { rewrite /Marki /Mark /s0' /Mk0' lookup_insert lookup_total_alt.
            rewrite Def_mark; try done. apply Range_h. }
          assert (keyset (I !!! n) ## keyset (I !!! nk)) as Disj_ks.
          { apply Hflupd. }
          iMod (own_update_2 γ_ks
                  (● prodKS (KS, abs s0))
                  (◯ prodKS (keyset (FI s0 nk), Content s0 nk))
                  ((● prodKS (KS, abs s0 ∪ {[k]})) ⋅
                      (◯ prodKS (keyset (FI s0 nk), Content s0 nk ∪ {[k]})))
                  with "[$GKS] [$KS_nk]") as "H'".
          { apply auth_update. apply auth_ks_local_update_insert; try done. 
            - rewrite /FI Hs0. destruct Hflupd as (_&_&_&_&_&_&_&H1'&_).
              rewrite -H1' elem_of_union; by right.
            - rewrite /Content Mark_nk. clear -k_neq_Keynk; set_solver.
            - admit. }
          iDestruct "H'" as "(GKS & H')".
          assert (keyset (FI s0 nk) = keyset (FI s0' n) ∪ keyset (FI s0' nk)) as ->.
          { rewrite /FI Hs0 /s0'. destruct Hflupd as (_&_&_&_&_&_&_&H1'&_).
            rewrite -H1' -leibniz_equiv_iff. 
            by rewrite (comm _ (keyset (I !!! nk)) _). }
          assert (Content s0 nk ∪ {[k]} = Content s0' n ∪ Content s0' nk) as ->.
          { rewrite /Content Mark_nk Mark_nk' Mark_n'.
            rewrite /Key Hs0 /s0' /Ky0' lookup_insert lookup_insert_ne.
            clear; set_solver. apply Hflupd. }
          assert (prodKS (keyset (FI s0' n) ∪ keyset (FI s0' nk), 
                    Content s0' n ∪ Content s0' nk) = 
                  prodKS (keyset (FI s0' n), Content s0' n) ⋅ 
                    prodKS (keyset (FI s0' nk), Content s0' nk)) as ->.
          { rewrite comm. apply ksRAT_prodKS_op. apply ksRAT_valid_composable. 
            rewrite /ksRAT_composable /valid /ksRATValid /ksRAT_fst. 
            repeat split.
            - rewrite /Content Mark_n'. rewrite /s0' /Key /FI /Ky0' lookup_insert.
              clear -KS_n. set_solver.
            - rewrite /Content Mark_nk'. rewrite /s0' /Key /FI /Ky0'.
              rewrite !lookup_insert_ne. rewrite Hs0 /Key in KS_nk.
              clear -KS_nk; set_solver. apply Hflupd.
            - apply Disj_ks. }
          iDestruct "H'" as "(KS_n & KS_nk)".
          iModIntro. iSplitL "GKS".
          { by rewrite /s0' Hs0; unfold abs. }
          iSplitL "Node_p Node_n Nodes_rest". rewrite FP_s0'.
          rewrite big_sepS_union; try done. iSplitL "Node_p Nodes_rest".
          rewrite (big_opS_delete _ (FP s0) p); try done. iSplitL "Node_p".
          { rewrite /Marki /Nexti HT. rewrite HM. rewrite HK. rewrite HNp.
            all: try done. rewrite Def_next'. done. }
          iApply (big_sepS_mono with "Nodes_rest"); try done.
          { intros x Hx. iIntros "Node_x". 
            rewrite /Marki /Nexti HT. rewrite HM. rewrite HK. rewrite HN. done.
            all : clear -Hx n_notin_s0; set_solver. }
          { rewrite big_opS_singleton. rewrite HTn HMn HNn HKn. done. }
          { clear -n_notin_s0; set_solver. }
          rewrite FP_s0'. rewrite big_opS_union; last first.
          { clear -n_notin_s0; set_solver. }
          iSplitL "Nodes_KS KS_nk".
          rewrite (big_sepS_delete _ (FP s0) nk); last by apply Hflupd. 
          iFrame "KS_nk". 
          iApply (big_sepS_mono with "Nodes_KS"); try done.
          { intros x Hx. iIntros "Hks".
            assert (keyset (FI s0' x) = keyset (FI s0 x)) as ->.
            rewrite /FI /s0' Hs0. apply Hflupd.
            destruct Hflupd as [-> _]. clear -Hx n_notin_s0; set_solver.
            assert (Content s0' x = Content s0 x) as ->.
            rewrite /Content /s0' Hs0 /Marki /Mark /Key /Mk0' /Ky0'.
            rewrite !lookup_insert_ne. done. 
            all : try (clear -Hx n_notin_s0; set_solver); done. }
          by rewrite big_opS_singleton. }

        iAssert (⌜∀ n k, n ∈ FP s0' → k ∈ keyset (FI s0' n) →
          (k ∈ abs s0' ↔ k ∈ Content s0' n)⌝)%I as "%Hks".
        { iDestruct "Res" as "(GKS & _ & HKS)".
          iPoseProof (keyset_summary with "GKS HKS") as "%H'"; try done. }
        

        assert (per_tick_inv s0') as PT_s0'.
        { destruct PT_s0 as (PT1&PT2&PT3&PT4&PT5&PT6&PT7).
          split; last split; last split; last split; last split; last split.
          - rewrite FP_s0' !HK; try done. rewrite !HM; try done.
            rewrite !HT; try done. assert (Next s0' tl = Next s0 tl) as ->.
            { rewrite HN; try done. apply not_eq_sym. apply Hflupd. }
            destruct PT1 as (PT11&PT12&PT13&PT14&PT15&PT16&PT17&PT18&PT19).
            destruct (decide (p = hd)) as [-> | Hphd].
            + repeat split; try done. 
              * clear -PT11; set_solver.
              * rewrite HNp lookup_insert_ne; try done. clear -HL; lia.
            + rewrite HN; try done. repeat split; try done. clear -PT11; set_solver.
          - unfold GFI.
            assert (FP s0' = dom I) as ->. 
            { symmetry. rewrite FP_s0'. apply Hflupd. }
            apply Hflupd.
          - done.
          - rewrite FP_s0'. intros n' Hn'.
            destruct (decide (n' = n)) as [-> | Hn'n].
            + rewrite HMn HNn HKn HI HTn. 
              split; last split; last split; last split; last split; try done.
              * intros ?; rewrite lookup_total_alt Def_mark /=. done. apply Range_h.
              * clear -Range_k; lia.
              * rewrite (lookup_total_alt mark) Def_mark /=.
                rewrite (Def_next 0). rewrite list_lookup_total_alt Hss0 /=.
                apply Hflupd. all: apply Range_h. 
            + assert (n' ∈ FP s0) as H'. clear -Hn' Hn'n; set_solver.
              apply PT4 in H'.
              destruct H' as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6&Hn7).
              destruct (decide (n' = p)) as [-> | Hn'p]; last first.
              * rewrite HM. rewrite HK. rewrite HN. rewrite HI. rewrite HT.
                all: try done. 
                split; last split; last split; last split; last split; try done.
                apply Hflupd. assert (dom I = FP s0 ∪ {[n]}) as ->.
                apply Hflupd. clear -Hn' Hn'n; set_solver. all: done.
              * rewrite HM. rewrite HNp. rewrite HK. rewrite HI. rewrite HT.
                all: try done.
                split; last split; last split; last split; last split; try done.
                { intros H'%Hn2; rewrite dom_insert_L H'. 
                  assert (0 ∈ gset_seq 0 (Height s0 p - 1)) as H''. 
                  { rewrite elem_of_gset_seq; lia. } clear -H''; set_solver. }
                { rewrite lookup_insert Mark_p0. apply Hflupd. }
          - intros n1 n2. rewrite /Nexti /Next /s0' /Key. apply Hflupd.
          - intros n1 n2 i. rewrite /Nexti /Next /s0' /FP.
            destruct Hflupd as [H' H'']. rewrite Hs0 /FP in H'.
            rewrite -H'. apply H''.
          - intros n1 n2 i. rewrite /Nexti. 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            + rewrite HNn. intros H'. assert (i < h) as Hi. 
              { apply elem_of_dom_2 in H'. rewrite Dom_next elem_of_gset_seq in H'. 
                clear -H' Range_h. lia. } assert (i < L) as Hi'.
              { clear -Hi Range_h; lia. }
              rewrite Def_next in H'; try done.
              inversion H'. rewrite HT. apply Hss_ht; try done.
              assert (ss !!! i ∈ FP s0) as H''. { by apply Hss_fp. }
              clear -n_notin_s0 H''; set_solver.
            + intros H'. assert (H'' := H'). rewrite /Nexti in PT6. 
              destruct (decide (n1 = p)) as [-> | Hn1p]; last first.
              { rewrite HN in H' H''; try done. apply PT6 in H''. rewrite HT. 
                apply (PT7 n1). apply H'. clear -H'' n_notin_s0; set_solver. }
              rewrite HNp in H' H''. destruct (decide (i = 0)) as [-> | Hi0].
              rewrite lookup_insert in H'. inversion H'. subst n2. rewrite HTn. 
              apply Range_h. rewrite lookup_insert_ne in H' H''; try done. 
              rewrite HT. apply (PT7 p). apply H'. apply PT6 in H''.
              clear -H'' n_notin_s0; set_solver. }
        assert (transition_inv s0 s0') as Trans_s0.
        { repeat split.
          - intros n' i FP_n'.
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            rewrite /Marki HM; try done. 
            destruct (decide (n' = p)) as [-> | Hn'p]. 
            + rewrite /Nexti HNp. destruct (decide (i = 0)) as [-> | Hi0].
              * rewrite Mark_p0. clear; try done.
              * rewrite lookup_insert_ne; try done.
            + rewrite /Nexti HN; try done.
          - intros n'. destruct (decide (n' = n)) as [-> | Hn'].
            + intros _ H'. rewrite /Marki /Mark /s0' /Mk0' in H'.
              rewrite lookup_insert in H'. 
              rewrite lookup_total_alt Def_mark /= in H'.
              clear -H'; done. apply Range_h. 
            + rewrite /Marki /Mark Hs0 /s0' /Mk0'. 
              rewrite lookup_insert_ne; try done.
              intros H' H''. rewrite H' in H''. clear -H''; done.
          - intros n' i FP_n'.
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            rewrite /Marki HM; try done.
          - intros n' FP_n'. 
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            rewrite HT; try done.
          - intros n' FP_n'. 
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            rewrite HK; try done.
          - rewrite FP_s0'. clear; set_solver. }
        
        
        iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
        { by iDestruct "Hist" as (M0'') "(_&_&%&_)". }
        
        assert (seq_spec (insertOp k) (abs s0) (abs s0') true) as Hss.
        { rewrite Hs0 /s0' /abs. rewrite Hs0 /abs /= in k_notin_s0. 
          clear -k_notin_s0. set_solver. }
        iAssert (|==> hist γ_t γ_m M0' (T0+1))%I with "[Hist]" as ">Hist".
        { iPoseProof (hist_upd _ _ _ _ _ s0' with "[%] [%] [$Hist]") as ">H'".
          apply  Habs0. intros <-. clear -FP_s0' n_notin_s0. set_solver.
          by rewrite /M0'. }
        assert (∀ t, 0 ≤ t ≤ T0+1 → per_tick_inv (M0' !!! t)) as PT0'.
        { intros t Ht. destruct (decide (t = T0 + 1)) as [-> | Ht'].
          + by rewrite lookup_total_insert.
          + rewrite lookup_total_insert_ne; try done. apply PT0.
            clear -Ht Ht'; lia. }
        assert ((∀ t, 0 <= t < T0 + 1 → 
          transition_inv (M0' !!! t) (M0' !!! (t + 1)))) as Trans_M0'.
        { intros t Ht. destruct (decide (t = T0)) as [-> | Ht'].
          + rewrite lookup_total_insert. 
            rewrite lookup_total_insert_ne; last by lia.
            apply leibniz_equiv in Habs0. by rewrite Habs0.
          + rewrite !lookup_total_insert_ne; try lia.
            apply Trans_M0. clear -Ht Ht'; lia. }
        
        iPoseProof (snapshot_current with "[%] [#] [$]") 
          as ">(#Past_s0'&Hist)"; try done.
        iEval (rewrite /M0' lookup_total_insert) in "Past_s0'".

        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> Φ #true ∗ dsRepI γ_r (abs s0'))%I 
          with "[Hpost Hmatch Hproph Ds]" as ">(HΦ & Ds)".
        { destruct Hpvs' as [v1 Hpvs']. destruct (process_proph tid pvs) eqn: H'.
          - iMod "Hmatch" as (a)"[DsR [_ H']]".
            iCombine "DsR Ds" as "H''".
            iAssert (⌜a = abs s0⌝)%I as %->. 
            { iPoseProof (own_valid with "[$H'']") as "%H''".
              rewrite frac_agree_op_valid_L in H''. iPureIntro; apply H''. }
            iEval (rewrite <-frac_agree_op) in "H''".
            iEval (rewrite Qp.half_half) in "H''".
            iMod ((own_update γ_r (to_frac_agree 1 (abs s0)) 
              (to_frac_agree 1 (abs s0'))) with "[$H'']") as "H''".
            { apply cmra_update_exclusive. 
              rewrite /valid /cmra_valid /= /prod_valid_instance.
              split; simpl; try done. }
            iEval (rewrite -Qp.half_half) in "H''".
            iEval (rewrite frac_agree_op) in "H''".
            iDestruct "H''" as "(Ds & DsR)".
            iSpecialize ("H'" $! (abs s0') true).
            iMod ("H'" with "[$DsR]") as "HQ". { by iPureIntro. } iFrame "Ds". 
            iApply ("Hpost" $! true (prf ++ [((v1, #true)%V, #())]) pvs'). 
            iFrame "Hproph". iModIntro. iPureIntro.
            clear -Hpvs' Hprf. split; try done.
            rewrite Hpvs'. by rewrite assoc. rewrite Forall_app. split.
            apply (Forall_impl _ _ _ Hprf). intros [x1 x2]. intros [v1' [=]].
            by subst x2. by rewrite Forall_singleton.
          - iMod "Hmatch" as (a)"[DsR [_ H']]".
            iCombine "DsR Ds" as "H''".
            iAssert (⌜a = abs s0⌝)%I as %->. 
            { iPoseProof (own_valid with "[$H'']") as "%H''".
              rewrite frac_agree_op_valid_L in H''. iPureIntro; apply H''. }
            iEval (rewrite <-frac_agree_op) in "H''".
            iEval (rewrite Qp.half_half) in "H''".
            iMod ((own_update γ_r (to_frac_agree 1 (abs s0)) 
              (to_frac_agree 1 (abs s0'))) with "[$H'']") as "H''".
            { apply cmra_update_exclusive. 
              rewrite /valid /cmra_valid /= /prod_valid_instance.
              split; simpl; try done. }
            iEval (rewrite -Qp.half_half) in "H''".
            iEval (rewrite frac_agree_op) in "H''".
            iDestruct "H''" as "(Ds & DsR)".
            iSpecialize ("H'" $! (abs s0') true).
            iMod ("H'" with "[$DsR]") as "HQ". { by iPureIntro. } iFrame "Ds". 
            iApply ("Hpost" $! true (prf ++ [((v1, #true)%V, #())]) pvs'). 
            iFrame "Hproph". iModIntro. iSplitR; last by iLeft.
            iPureIntro. rewrite Hpvs'. by rewrite assoc.
          - exfalso. clear -Hpvs' Hprf H'. apply process_proph_no_upd in H'.
            destruct H' as [i [x [Hi Htake]]].
            destruct (decide (length prf < i)) as [Hiprf | Hiprf]; last first.
            { rewrite Hpvs' /= in Hi. rewrite Nat.nlt_ge Nat.le_lteq in Hiprf. 
              destruct Hiprf as [Hiprf | ->]. 
              rewrite lookup_app_l in Hi; try done.
              rewrite Forall_lookup in Hprf.
              pose proof Hprf i (x, #tid) Hi as [? H']. try done.
              rewrite list_lookup_middle in Hi. by inversion Hi. done. }
            assert (take i pvs !! (length prf) = Some ((v1, #true)%V, #())) as H'.
            { rewrite lookup_take; try done. 
              rewrite Hpvs' list_lookup_middle; try done. }
            apply (Forall_lookup_1 _ _ _ _ Htake) in H'.
            destruct H' as [H' _]. apply H'; rewrite /is_snd /=. by exists v1. }
        
        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> 
          helping_inv N γ_t γ_r γ_mt γ_msy M0' ∗ dsRep γ_r (abs s0'))%I with
          "[Help Ds]" as ">(Help & Ds)".
        { iMod (fupd_mask_subseteq (⊤ ∖ ↑cntrN N)) as "H'". { clear; set_solver. }
          iPoseProof ("Upd" with "[%] [Ds] [Help]") as ">Help"; try done.
          apply leibniz_equiv in Habs0. iMod "H'" as "_". by iModIntro. }
        iModIntro. iSplitR "Hpreds Hsuccs HΦ".
        { iNext. iExists M0', (T0+1)%nat, s0'. iFrame "∗#%". iPureIntro.
          by rewrite lookup_total_insert. }
        wp_pures. 
        wp_apply (maintenanceOp_insert_spec ps ss with 
          "[] [] [] [] [Hpreds Hsuccs]"); try done. 
        { iSplitL "Hpreds". admit. iSplitL "Hsuccs". admit. 
          iSplitR. iExists s0'. iFrame "Past_s0'". iPureIntro.
          rewrite FP_s0'. clear; set_solver. 
          repeat (iSplit; first by iPureIntro).
          iDestruct "Htr" as "(Htr&_)". iFrame "Htr". }
        iIntros (??)"_". by wp_pures.
  Admitted. 


    

  
