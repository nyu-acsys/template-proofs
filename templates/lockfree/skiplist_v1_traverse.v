(* Herlihy Skiplist with a single level : Search *)

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
Require Export skiplist_v1 skiplist_v1_util flows_big_op.

Module SKIPLIST1_SPEC_TRAVERSE.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS SKIPLIST1_UTIL.

  Lemma array_store E (i : nat) (v : Node) arr (xs : list Node) :
    {{{ ⌜i < length xs⌝ ∗ ▷ is_array arr xs }}}
      #(arr +ₗ i) <- #v
    @ E {{{ RET #(); is_array arr (<[i:=v]>xs) }}}.
  Proof.
  Admitted.

  Lemma array_repeat (b : loc) (n : nat) :
    {{{ ⌜0 < n⌝ }}} AllocN #n #b 
    {{{ arr, RET #arr; is_array arr (replicate n b) }}}.
  Proof.
    iIntros (ϕ ?%inj_lt) "Post".
    iApply wp_allocN; try done.
    iNext. iIntros (l) "[lPts _]".
    iApply "Post".
    unfold is_array.
    rewrite Nat2Z.id.
    rewrite -> fmap_replicate.
    (* iAssumption. *)
  Admitted.

  Parameter findNext_spec : ∀ (n: Node) (i: nat),
    ⊢ <<{ ∀∀ h mark next k, node n h mark next k ∗ ⌜i < h⌝ }>>
          findNext #n #i @ ∅
      <<{ ∃∃ (m: bool) (opt_n': option Node),
              node n h mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !! i = opt_n'⌝ |
              RET (match opt_n' with None => (#m, NONEV) 
                                    | Some n' => (#m, SOMEV #n') end) }>>.

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
                                    | false => NONEV end) }>>.

  Parameter compareKey_spec : ∀ (n: Node) (k': nat),
    ⊢ <<{ ∀∀ h mark next k, node n h mark next k }>>
           compareKey #n #k' @ ∅
     <<{ ∃∃ (res: nat),
            node n h mark next k 
          ∗ ⌜if decide (res = 0) then k < k'
             else if decide (res = 1) then k = k'
             else k > k'⌝ |
         RET #res }>>.

  Definition traversal_inv γ_m t0 i k p c : iProp :=
    (∃ s, past_state γ_m t0 s ∗ ⌜p ∈ FP s ∧ Key s p < k ∧ 
      Marki s p 0 = false ∧ i < Height s p ∧ (i = 0 → Nexti s p i = Some c)⌝)
  ∗ (∃ s, past_state γ_m t0 s ∗ ⌜c ∈ FP s ∧ i < Height s c⌝).

  Lemma traversal_inv_hd_tl γ_m γ_t M T s t0 k:
    ⌜M !!! T ≡ s⌝ -∗ 
    ⌜per_tick_inv s⌝ -∗
    ⌜1 < L⌝ -∗
    ⌜0 < k < W⌝ -∗
    own γ_t (◯ MaxNat t0) -∗ 
    hist γ_t γ_m M T -∗
      |==> traversal_inv γ_m t0 (L-1) k hd tl ∗ hist γ_t γ_m M T.
  Proof.
    iIntros "%Habs %PT %HL %Range_k #Ht0 Hist".
    iPoseProof (snapshot_current with "[%] [$Ht0] [$Hist]") 
      as ">(#Past_s&Hist)"; try done.
    destruct PT as ((H1'&H2'&H3'&H4'&H5'&H6'&H7'&H8'&H9')&_).
    iModIntro. iFrame. iSplit; iExists s; iFrame "Past_s".
    - iPureIntro; repeat split; try (done || lia).
      set_solver. apply H4'. lia.
    - iPureIntro; repeat split; try (done || lia). set_solver.
  Qed. 

  Lemma traverse_i_spec N γ_t γ_r γ_m γ_mt γ_msy tid t0 k (i: nat) (p c: Node):
    main_inv N γ_t γ_r γ_m γ_mt γ_msy  -∗
    thread_start γ_t γ_mt tid t0 -∗
    □ update_helping_protocol2 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
      {{{ traversal_inv γ_m t0 i k p c }}}
        traverse_i #i #p #c #k @ ⊤
      {{{ (ores: option (Node * Node * bool)), 
            RET (match ores with
                  None => NONEV
                | Some res =>SOMEV (#res.1.1,#res.1.2,#res.2) end);
            match ores with 
              None => True
            | Some res =>
              let p' := res.1.1 in
              let c' := res.1.2 in
              let b := res.2 in
              traversal_inv γ_m t0 i k p' c'
              ∗ (⌜i = 0⌝ → (∃ s, past_state γ_m t0 s ∗ 
                              ⌜if b then 
                                  k ∈ abs s ∧ k = Key s c' 
                                  ∧ c' ∈ FP s ∧ Marki s c' 0 = false
                                else 
                                  k ∉ abs s ∧ k < Key s c' 
                                  ∧ c' ∈ FP s⌝)) end }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iLöb as "IH" forall (p c).
    iIntros (Φ) "!# #Htr Hpost". wp_lam. wp_pure credit: "Hc". wp_pures.
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "Htr" as "(_&H')". iDestruct "H'" as (s)"(Past_s & %Htr_sc)".
      destruct Htr_sc as (H'&_).
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Nodes" as "(Node_c & Nodes_rest)".
    iAssert (⌜i < Height s0 c⌝)%I as %Height_c0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "Htr" as "(_&H')". iDestruct "H'" as (s)"(Past_s & %Htr_sc)".
      destruct Htr_sc as (H'&H'').
      iPoseProof (height_eq_2 c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
        try done. }
    iAssert ((node c (Height s0 c) (Mark s0 c) (Next s0 c) (Key s0 c)) 
      ∗ ⌜i < Height s0 c⌝)%I with "[Node_c]" as "Hpre".
    { iFrame "Node_c %". }
    iAaccIntro with "Hpre".
    { iIntros "(Node_c & _)". iModIntro. iFrame "Hpost Hc".
      iNext; iExists M0, T0, s0. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Nodes_rest". iFrame. }
    iIntros (m c') "(Node_c & %Mark_c0 & %Next_c0)".
    iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    assert (Mark s0 c !!! i = true → Next s0 c !! i = None → false) as Hcontra.
    { intros Hm Hn. apply PT_s0 in FP_c0. 
      assert (c ≠ tl) as Hctl. 
      { intros ->. destruct PT_s0 as ((_&_&_&_&H'&_)&_). rewrite H' in Hm.
        done. destruct FP_c0 as (_&_&_&H''&_). clear -Height_c0 H''; lia. }
      destruct FP_c0 as (_&H'&H''&_). apply H' in Hctl. 
      apply not_elem_of_dom in Hn. rewrite Hctl in Hn. apply Hn.
      rewrite elem_of_gset_seq. lia. }

    iAssert (own γ_t (◯ MaxNat t0)) as "#Ht0".
    { iDestruct "Thd_st" as "(_&H')". iFrame "H'". }
    iPoseProof (snapshot_current with "[%] [$Ht0] [$Hist]") 
      as ">(#Past_s0&Hist)"; try done.
    
    iAssert (∀ cn, ⌜Mark s0 c !!! i = false⌝ → ⌜Next s0 c !! i = Some cn⌝ →
      ⌜Key s0 c < k⌝ → traversal_inv γ_m t0 i k c cn)%I as "#Hcase".
    { iIntros (cn)"%Hm %Hn %Hk". iSplitL; iExists s0; iFrame "Past_s0"; iPureIntro. 
      repeat split; try done. apply PT_s0 in FP_c0. destruct FP_c0 as (H'&_).
      apply H'. by exists i. destruct PT_s0 as (_&_&_&_&_&PT&PT'). 
      repeat split; try done. by apply (PT c _ i). by apply (PT' c _ i). }
    iAssert (traversal_inv γ_m t0 i k p c) with "Htr" as "Htr'".
    iDestruct "Htr'" as "(Htrp & Htrc)".
    iDestruct "Htrp" as (s)"(Past_s & %FP_ps & %Key_ps & %Marki_ps & 
      %Height_ps & %Nexti_ps)".
    iAssert (⌜per_tick_inv s⌝)%I as %PT_s.
    { iPoseProof (per_tick_past with "[%] Hist Past_s") as "%"; try done. }
    iAssert (⌜c ∈ FP s⌝ → ⌜Mark s0 c !!! i = false⌝ 
      → ⌜Mark s c !!! i = false⌝)%I as %HM.
    { iIntros "%FP_cs %Hm". destruct (decide (Mark s c !!! i = false)); try done.
      iExFalso. rewrite not_false_iff_true in n.
      iAssert (⌜Marki s0 c i = Marki s c i⌝)%I as %H'.
      { apply leibniz_equiv in Habs0. rewrite -Habs0.
        iPoseProof (marking_mono_2 c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. }
      rewrite /Marki Hm n in H'. done. } 
    iAssert (⌜c ∈ FP s⌝ → ⌜Key s c = Key s0 c⌝)%I as %Key_eq. 
    { iIntros "%FP_cs". 
      apply leibniz_equiv in Habs0. rewrite -Habs0.
      iPoseProof (key_eq_2 c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
        try done. }
    assert (∀ k, c ∈ FP s →  k ∈ keyset (FI s c) → 
      (k ∈ abs s ↔ k ∈ Content s c)) as Hks.
    { destruct PT_s as (_&_&H'&_). intros k'; apply H'. }
    iAssert (⌜i = 0⌝ → ⌜Mark s0 c !!! i = false⌝ → ⌜k < Key s0 c⌝ → 
      ∃ s, past_state γ_m t0 s ∗ ⌜k ∉ abs s ∧ k < Key s c ∧ c ∈ FP s⌝)%I as "Hcase1".
    { iIntros "%Hi %Mark_c0' %Key_c0". pose proof Nexti_ps Hi as Nexti_ps'.
      subst i. iExists s. iFrame "Past_s". clear Nexti_ps.
      assert (c ∈ FP s) as FP_cs. 
      { destruct PT_s as (_&_&_&_&_&H'&_). apply (H' p c 0); try done. }
      apply HM in Mark_c0'; try done. rename Mark_c0' into Mark_cs. 
      rewrite -Key_eq in Key_c0; try done.
      assert (k ∈ keyset (FI s c)) as k_in_ksc.
      { apply (in_keyset s p c k); try done. lia. }
      assert (k ∉ Content s c) as k_notin_cntc.
      { rewrite /Content /Marki Mark_cs elem_of_singleton. lia. }
      apply Hks in k_in_ksc; try done. iPureIntro. repeat split; try done.
      intros H'%k_in_ksc. by apply k_notin_cntc. }
    iAssert (⌜i = 0⌝ → ⌜Mark s0 c !!! i = false⌝ → ⌜k = Key s0 c⌝ → 
      ∃ s, past_state γ_m t0 s 
          ∗ ⌜k ∈ abs s ∧ k = Key s c ∧ c ∈ FP s ∧ Marki s c 0 = false⌝)%I as "Hcase2".
    { iIntros "%Hi %Mark_c0' %Key_c0". pose proof Nexti_ps Hi as Nexti_ps'.
      subst i. iExists s. iFrame "Past_s". clear Nexti_ps. 
      assert (c ∈ FP s) as FP_cs. 
      { destruct PT_s as (_&_&_&_&_&H'&_). apply (H' p c 0); try done. }
      apply HM in Mark_c0'; try done. rename Mark_c0' into Mark_cs. 
      rewrite -Key_eq in Key_c0; try done.
      assert (k ∈ keyset (FI s c)) as k_in_ksc.
      { apply (in_keyset s p c k); try done. lia. }
      assert (k ∈ Content s c) as k_in_cntc.
      { rewrite /Content /Marki Mark_cs elem_of_singleton. lia. }
      apply Hks in k_in_ksc; try done. iPureIntro. repeat split; try done.
      by apply k_in_ksc. }
    iAssert (⌜i = 0⌝ → ⌜Mark s0 c !!! i = false⌝ → ⌜Nexti s0 c i = None⌝ → 
      ∃ s, past_state γ_m t0 s ∗ ⌜k ∉ abs s ∧ k < Key s c ∧ c ∈ FP s⌝)%I as "Hcase3".
    { iIntros "%Hi %Mark_c0' %Next_c0'". subst i. assert (c = tl) as ->.
      { destruct (decide (c = tl)); try done. exfalso. 
        apply PT_s0 in FP_c0. destruct FP_c0 as (_&H'&_). apply H' in n. 
        rewrite /Nexti in Next_c0'. apply not_elem_of_dom in Next_c0'.
        rewrite n in Next_c0'. apply Next_c0'. 
        rewrite elem_of_gset_seq; clear; lia. }
      assert (Marki s tl 0 = false ∧ Key s tl = W) as [H' H''].
      { destruct PT_s as ((_&_&H'&_&H''&_)&_). split.
        apply H''. clear -HL; lia. done. }
      assert (tl ∈ FP s) as FP_tls.
      { destruct PT_s as ((H1'&_)&_). clear -H1'; set_solver. }
      assert (k ∈ keyset (FI s tl)) as k_in_kstl.
      { apply (in_keyset s p tl k); try done. by apply Nexti_ps. lia. }
      assert (k ∉ Content s tl) as k_notin_tl.
      { rewrite /Content H' elem_of_singleton. lia. }
      apply Hks in k_in_kstl; try done. iExists s. iFrame "Past_s". 
      iPureIntro. repeat split; try done.
      intros H1'%k_in_kstl. by apply k_notin_tl. lia. }
    iClear "Past_s Htrc".
    clear PT_s0 s FP_ps Key_ps Marki_ps Height_ps Nexti_ps HM PT_s Key_eq Hks.
    iModIntro. iSplitR "Hpost Hc".
    { iNext. iExists M0, T0, s0. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Nodes_rest". iFrame. }
    destruct c' as [cn |]; destruct m; wp_pures. 
    - awp_apply changeNext_spec; try done.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p1.
      { apply leibniz_equiv in Habs1. rewrite -Habs1.
        iDestruct "Htr" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
        destruct Htr_sp as (H'&_). 
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAssert (⌜i < Height s1 p⌝)%I as %Height_p1.
      { apply leibniz_equiv in Habs1. rewrite -Habs1.
        iDestruct "Htr" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
        destruct Htr_sp as (H'&_&_&H''&_). 
        iPoseProof (height_eq_2 p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
          try done. }
      iAssert ((node p (Height s1 p) (Mark s1 p) (Next s1 p) (Key s1 p)) 
        ∗ ⌜i < Height s1 p⌝)%I with "[Node_p]" as "Hpre".
      { iFrame "Node_p %". }
      iAaccIntro with "Hpre".
      { iIntros "(Node_p&_)". iModIntro. iFrame "Hpost Hc".
        iNext; iExists M1, T1, s1. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto. iFrame. }
      iIntros (success next') "(Node_p & Hsuccess)".
      iApply (lc_fupd_add_later with "Hc"). iNext. 
      destruct success.
      + iDestruct "Hsuccess" as %[Next_p1 [Mark_p1 Def_next']].
        iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
        { apply leibniz_equiv in Habs1. rewrite -Habs1.
          iDestruct "Htr" as "(_&H')". iDestruct "H'" as (s)"(Past_s & %Htr_sc)".
          destruct Htr_sc as (H'&_). 
          iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
        iAssert (⌜Mark s1 c !!! i = true⌝)%I as %Mark_c1.
        { fold (Marki s0 c i) in Mark_c0. fold (Marki s1 c i).
          apply leibniz_equiv in Habs1. rewrite -Habs1.
          iPoseProof (marking_mono_2 c with "[%] [$Hist] [$Past_s0] [%]") as "->"; 
            try done. }
        iAssert (⌜Next s1 c !! i = Some cn⌝)%I as %Next_c1.
        { fold (Nexti s0 c i) in Next_c0. fold (Nexti s1 c i).
          apply leibniz_equiv in Habs1. rewrite -Habs1.
          iPoseProof (next_unchanged c with "[%] [$Hist] [$Past_s0] [%]") as "->"; 
            try done. }  
        iAssert (⌜Key s1 p < k⌝)%I as %Key_pk.
        { apply leibniz_equiv in Habs1. rewrite -Habs1.
          iDestruct "Htr" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
          destruct Htr_sp as (H'&H''&_).
          iPoseProof (key_eq_2 p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
            try done. }
        iAssert (⌜per_tick_inv s1⌝)%I as %PT_s1.
        { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
        destruct (decide (i = 0)) as [-> | Hi0]; 
          last destruct (decide (c = cn)) as [<- | c_neq_cn].
        * iDestruct "SShot1" as %[FP1 [C1 [Ht1 [Mk1 [Nx1 [Ky1 [I1 
            [Hs1 [Dom_Ht1 [Dom_Mk1 [Dom_Nx1 [Dom_Ky1 Dom_I1]]]]]]]]]]]].
          set Nx1' := <[p := next']> Nx1.
          set Ip1 := I1 !!! p. set Ic1 := I1 !!! c. set out_pc := out Ip1 c.
          set Ip1' := int {| infR := inf_map Ip1; outR :=  <<[cn := out_pc]>> ∅ |}.
          set Ic1': multiset_flowint_ur nat := 
            int {| infR := {[c := (inf Ic1 c - out_pc)%CCM]}; 
                  outR := <<[cn := (out Ic1 cn - out_pc)%CCM]>> ∅ |}.
          set I1' := <[c := Ic1']> (<[p := Ip1']> I1).
          set s1' := (FP1, C1, Ht1, Mk1, Nx1', Ky1, I1'): snapshot.
          set M1' := <[T1 + 1 := s1']> M1.

          assert (∀ x, x ∈ FP s1 → flow_constraints_I x (FI s1 x) 
                  (Mark s1 x !!! 0) (Next s1 x !! 0) (Key s1 x)) as Hflow.
          { destruct PT_s1 as (_&_&_&H'&_).
            intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&?). }
          assert (∀ x, I1 !!! x = FI s1 x) as I1_eq_s1.
          { intros x. rewrite Hs1; unfold FI. try done. }
          assert (flow_constraints_I p Ip1 false (Some c) (Key s1 p)) as Hp.
          { apply Hflow in FP_p1. by rewrite -I1_eq_s1 Next_p1 Mark_p1 in FP_p1. }
          assert (flow_constraints_I c Ic1 true (Some cn) (Key s1 c)) as Hc.
          { apply Hflow in FP_c1. by rewrite -I1_eq_s1 Next_c1 Mark_c1 in FP_c1. }
          assert (Key s1 p < Key s1 c) as Key_pc.
          { destruct PT_s1 as (_&_&_&_&PT&_). rewrite /Nexti in PT.
            by pose proof PT p c Next_p1. }
          assert (Key s1 p < W) as Key_p1.
          { destruct PT_s1 as (_&_&_&PT&_). apply PT in FP_c1.
            destruct FP_c1 as (_&_&_&_&H'&_). clear -H' Key_pc. lia. }
          assert (Key s1 c < Key s1 cn) as Key_ccn.
          { destruct PT_s1 as (_&_&_&_&PT&_). rewrite /Nexti in PT.
            by pose proof PT c cn Next_c1. }
          assert (p ≠ c) as p_neq_c.
          { intros ->. clear -Key_pc; lia. }
          assert (c ≠ cn) as c_neq_cn.
          { intros ->. clear -Key_ccn; lia. }
          assert (p ≠ cn) as p_neq_cn.
          { intros ->. clear -Key_pc Key_ccn. lia. }
          assert (insets Ip1 ≠ ∅) as Inset_p1_ne.
          { destruct Hp as (_&_&_&(H'&_)&_). intros H''. rewrite H'' in H'.
            assert (W ∈ (∅: gset nat)) as H1'. apply H'.
            rewrite elem_of_gset_seq; split; try lia. clear -H1'; set_solver. }
          assert (dom Ip1 = {[p]}) as Dom_Ip1 by apply Hp.
          assert (dom Ic1 = {[c]}) as Dom_Ic1 by apply Hc.
          assert (dom Ip1' = {[p]}) as Dom_Ip1'.
          { rewrite /dom /flowint_dom /Ip1' /=. apply Dom_Ip1. }
          assert (dom Ic1' = {[c]}) as Dom_Ic1'.
          { by rewrite /dom /flowint_dom /Ip1' /= dom_singleton_L. }
          assert (✓ (Ip1 ⋅ Ic1)) as Vpc1.
          { destruct PT_s1 as (_&H'&_). rewrite /GFI in H'.
            assert ({[p; c]} ⊆ FP s1) as Hsub.
            { clear -FP_p1 FP_c1. set_solver. }
            pose proof (flow_big_op_valid _ _ {[p; c]} Hsub H') as VI'.
            rewrite big_opS_union in VI'.
            rewrite !big_opS_singleton -!I1_eq_s1 in VI'. apply VI'.
            clear -p_neq_c; set_solver. }
          assert (dom (out_map Ip1) = {[c]}) as Domout_Ip1.
          { by apply Hp. }
          assert (outsets Ip1 ⊆ insets Ic1) as Out_In_c1.
          { rewrite /outsets /insets Domout_Ip1 Dom_Ic1 !big_opS_singleton.
            intros k' Hk'. apply (flowint_inset_step Ip1 Ic1); try done.
            rewrite Dom_Ic1. clear; set_solver. }
          assert (insets Ic1 ≠ ∅) as Inset_c1_ne.
          { assert (W ∈ outsets Ip1) as H'. 
            { rewrite /outsets Domout_Ip1 big_opS_singleton.
              destruct Hp as (_&H'&_&(_&H'')&_). apply H' in Inset_p1_ne.
              rewrite /outsets Inset_p1_ne -leibniz_equiv_iff big_opS_singleton 
                in H''. rewrite -H''. rewrite elem_of_gset_seq; split; try lia. }
            apply Out_In_c1 in H'. clear -H'; set_solver. }
          assert (out_pc ≠ 0%CCM) as Out_pc.
          { destruct Hp as (_&H'&_&(_&H'')&_). rewrite /outsets H' in H''. 
            rewrite -leibniz_equiv_iff big_opS_singleton in H''.
            rewrite /out_pc /Ip1 I1_eq_s1. rewrite /ccmunit /lift_unit.
            clear H'; intros H'. rewrite nzmap_eq in H'. pose proof H' W as H'.
            rewrite nzmap_lookup_empty /ccmunit /= /nat_unit in H'.
            rewrite /outset in H''. rewrite -nzmap_elem_of_dom_total2 in H'.
            rewrite -I1_eq_s1 -H'' in H'. apply H'. 
            rewrite elem_of_gset_seq. clear -Key_p1; split; lia. done. }
          
          assert (dom (out_map Ic1) = {[cn]}) as Domout_Ic1.
          { by apply Hc. }
          assert (dom (out_map Ip1') = {[cn]}) as Domout_Ip1'.
          { rewrite /Ip1' /= -leibniz_equiv_iff nzmap_dom_insert_nonzero.
            rewrite /empty /dom. clear; set_solver. done. }        
          assert (out Ic1 cn = inf Ic1 c) as Out_Ic1.
          { destruct Hc as (_&_&H'&H''&_&Hc1&Hc2). rewrite /keyset in H''.
            assert (insets Ic1 ⊆ outsets Ic1) as H1'. clear -H''; set_solver.
            assert (insets Ic1 = outsets Ic1) as H1''. clear -H1' H'; set_solver.
            rewrite /insets /outsets Dom_Ic1 Domout_Ic1 in H1''.
            rewrite -leibniz_equiv_iff !big_opS_singleton in H1''. 
            clear H' H'' H1'. apply nzmap_eq. intros k'.
            destruct (decide (k' ∈ inset _ Ic1 c)) as [Hk' | Hk'].
            - assert (Hk'' := Hk'). rewrite H1'' in Hk''.
              rewrite /inset nzmap_elem_of_dom_total in Hk'.
              rewrite /ccmunit /= /nat_unit in Hk'.
              pose proof Hc1 k' as Hc1.
              rewrite /outset nzmap_elem_of_dom_total in Hk''.
              rewrite /ccmunit /= /nat_unit in Hk''.
              pose proof Hc2 cn k' as Hc2.
              set a := inf Ic1 c !!! k'. set b := out Ic1 cn !!! k'.
              rewrite -/a -/b in Hk' Hk'' Hc1 Hc2. clear -Hk' Hk'' Hc1 Hc2; lia.
            - assert (Hk'' := Hk'). rewrite H1'' in Hk''.
              rewrite /inset nzmap_elem_of_dom_total2 in Hk'.
              rewrite /outset nzmap_elem_of_dom_total2 in Hk''.
              by rewrite Hk' Hk''. }
          assert (✓ (Ip1' ⋅ Ic1')) as Vpc1'.
          { apply intValid_composable. assert (Hcomp := Vpc1). 
            apply intComposable_valid in Hcomp. 
            destruct Hcomp as (H1'&H2'&H3'&H4'&H5'). repeat split; simpl.
            - rewrite /dom /flowint_dom in Dom_Ip1. rewrite Dom_Ip1.
              rewrite nzmap_dom_insert_nonzero. clear -p_neq_cn; set_solver.
              done.
            - intros H'. rewrite /dom /flowint_dom H' in Dom_Ip1.
              clear -Dom_Ip1; set_solver.
            - clear -c_neq_cn. rewrite dom_insert dom_empty.
              destruct (decide ((out Ic1 cn - out_pc)%CCM = 0%CCM)).
              rewrite nzmap_dom_insert_zero; try done. 
              rewrite /dom /nzmap_dom. set_solver.
              rewrite nzmap_dom_insert_nonzero; try done. 
              rewrite /dom /nzmap_dom. set_solver.
            - intros H'. pose proof f_equal dom H' as H''.
              rewrite dom_singleton_L in H''. clear -H''; set_solver.
            - rewrite /flowint_dom /= dom_singleton_L. 
              rewrite /dom /flowint_dom in Dom_Ip1. rewrite Dom_Ip1.
              clear -p_neq_c; set_solver.
            - apply map_Forall_lookup. intros i x Hix. assert (Hix' := Hix).
              apply elem_of_dom_2 in Hix. rewrite /dom /flowint_dom in Dom_Ip1. 
              rewrite Dom_Ip1 elem_of_singleton in Hix. subst i.
              assert (inf Ip1' p = x) as ->. { by rewrite /inf /Ip1' Hix' /=. } 
              assert (out Ic1' p = 0%CCM) as ->. 
              { rewrite /out /Ic1' /out_map /= nzmap_lookup_total_insert_ne.
                rewrite nzmap_lookup_empty. all: done. }
              by rewrite ccm_left_id ccm_pinv_unit.
            - apply map_Forall_lookup. intros i m. 
              destruct (decide (i = c)) as [-> | Hic].
              + rewrite lookup_insert. intros [=<-].
                assert (out Ip1' c = 0%CCM) as ->.
                { rewrite /out /Ip1' /out_map /= nzmap_lookup_total_insert_ne.
                  by rewrite nzmap_lookup_empty. done. }
                assert ((inf Ic1 c - out_pc)%CCM = inf Ic1' c) as ->.
                { by rewrite /Ic1' {2}/inf /inf_map /= lookup_insert /=. }
                rewrite /inf /Ic1' /inf_map /= lookup_insert /=.
                by rewrite ccm_left_id ccm_pinv_unit.
              + rewrite lookup_insert_ne; try done. }
          assert (dom (Ip1 ⋅ Ic1) = {[p;c]}) as Dom_pc.
          { rewrite intComp_dom; try done. rewrite Dom_Ip1 Dom_Ic1; done. } 
          assert (dom (Ip1' ⋅ Ic1') = {[p;c]}) as Dom_pc'.
          { rewrite intComp_dom; try done. rewrite Dom_Ip1' Dom_Ic1'; done. } 
          assert (Ip1' ⋅ Ic1' = Ip1 ⋅ Ic1) as Heq.
          { apply intEq.
            - by rewrite Dom_pc Dom_pc'.
            - rewrite Dom_pc'; clear; set_solver. 
            - intros n. destruct (decide (n = p)) as [-> | Hnp].
              + rewrite !intComp_inf_1; try done.
                assert (inf Ip1' p = inf Ip1 p) as ->. 
                { by rewrite /inf /Ip1' /=. }
                assert (out Ic1' p = 0%CCM) as ->. 
                { rewrite /out /Ic1' /out_map /= nzmap_lookup_total_insert_ne.
                  rewrite nzmap_lookup_empty. all: done. }
                assert (out Ic1 p = 0%CCM) as ->.
                { rewrite /out -nzmap_elem_of_dom_total2.
                  destruct Hc as (_&Hc&_). rewrite Hc; try done.
                  clear -p_neq_cn; set_solver. }
                done. rewrite Dom_Ip1; clear; set_solver.
                rewrite Dom_Ip1'; clear; set_solver.
              + destruct (decide (n = c)) as [-> | Hnc]; last first.
                { assert (n ∉ dom (Ip1' ⋅ Ic1')) as H'.
                  rewrite Dom_pc'. clear -Hnp Hnc; set_solver.
                  rewrite /dom /flowint_dom not_elem_of_dom in H'.
                  assert (n ∉ dom (Ip1 ⋅ Ic1)) as H''.
                  rewrite Dom_pc. clear -Hnp Hnc; set_solver.
                  rewrite /dom /flowint_dom not_elem_of_dom in H''.
                  by rewrite /inf H' H''. }
                rewrite !intComp_inf_2; try done.
                assert (out Ip1' c = 0%CCM) as ->. 
                { rewrite /out /Ip1' /out_map /=.
                  rewrite nzmap_lookup_total_insert_ne; try done. }
                rewrite {1}/inf /Ic1' /inf_map /= lookup_insert /= /out_pc.
                by rewrite ccm_pinv_unit. rewrite Dom_Ic1. clear; set_solver. 
                rewrite Dom_Ic1'. clear; set_solver.
            - intros n. destruct (decide (n ∈ ({[p;c]}: gset Node))) as [Hn | Hn].
              { rewrite !intValid_in_dom_not_out; try done.
                by rewrite Dom_pc. by rewrite Dom_pc'. }
              rewrite !intComp_unfold_out; try done.
              destruct (decide (n = cn)) as [-> | Hncn].
              + assert (out Ip1' cn = out_pc) as ->.
                { by rewrite /out /Ip1' /= nzmap_lookup_total_insert. }
                assert (out Ic1' cn = (out Ic1 cn - out_pc)%CCM) as ->.
                { by rewrite /Ic1' /out /= nzmap_lookup_total_insert. }
                assert (out Ip1 cn = 0%CCM) as ->.
                { rewrite /out -nzmap_elem_of_dom_total2.
                  destruct Hp as (_&Hp&_). rewrite Hp; try done.
                  clear -c_neq_cn; set_solver. }
                rewrite Out_Ic1 /out_pc. rewrite ccm_left_id.
                apply intComposable_valid in Vpc1. destruct Vpc1 as (_&_&_&_&H'). 
                rewrite map_Forall_lookup in H'. pose proof H' c (inf Ic1 c) as H'.
                rewrite {2}H'. done. rewrite /inf. assert (c ∈ dom Ic1) as H''.
                rewrite Dom_Ic1; clear; set_solver. 
                rewrite /dom /flowint_dom elem_of_dom in H''. 
                destruct H'' as [m ->]. by simpl.
              + assert (out Ip1' n = 0%CCM) as ->. 
                { rewrite /out /Ip1' /= nzmap_lookup_total_insert_ne; try done. }
                assert (out Ic1' n = 0%CCM) as ->.
                { rewrite /out /Ic1' /= nzmap_lookup_total_insert_ne; try done. }
                assert (out Ip1 n = 0%CCM) as ->.
                { rewrite /out -nzmap_elem_of_dom_total2 Domout_Ip1.
                  clear -Hn; set_solver. }
                assert (out Ic1 n = 0%CCM) as ->.
                { rewrite /out -nzmap_elem_of_dom_total2 Domout_Ic1.
                  clear -Hncn; set_solver. }
                done.
              + by rewrite Dom_pc.
              + by rewrite Dom_pc'. }
          assert (insets Ip1' = insets Ip1) as Insets_Ip1'.
          { rewrite /insets Dom_Ip1 Dom_Ip1' /inset /inf /=. done. }
          assert (outsets Ip1' = outsets Ip1) as Outsets_Ip1'.
          { destruct Hp as (_&Hp&_). rewrite /outsets Hp /Ip1 /=; try done.
            assert (dom <<[cn := out_pc]>> ∅ = {[cn]}) as ->.
            apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero; try done.
            rewrite /dom. clear; set_solver. apply leibniz_equiv.
            rewrite !big_opS_singleton. rewrite /outset /Ip1' {1}/out /=.
            rewrite nzmap_lookup_total_insert /out_pc /Ip1. done. }
          assert (flow_constraints_I p Ip1' false (Some cn) (Key s1 p)) as Hp'.
          { destruct Hp as (Hp1&Hp2&Hp3&Hp4&Hp5&Hp6&Hp7). 
            split; last split; last split; last split; last split; 
              last split; try done.
            - rewrite Insets_Ip1' Outsets_Ip1'. done.
            - rewrite Insets_Ip1' Outsets_Ip1'. done.
            - intros n' k'. destruct (decide (n' = cn)) as [-> | Hn'cn].
              + assert (out Ip1' cn = out_pc) as ->.
                { by rewrite /out /Ip1' /= nzmap_lookup_total_insert. }
                pose proof Hp7 c k' as H'. apply H'.
              + assert (out Ip1' n' = 0%CCM) as ->.
                { rewrite /out /Ip1' /= nzmap_lookup_total_insert_ne; try done. }
                rewrite nzmap_lookup_empty. rewrite /ccmunit /= /nat_unit. lia. }
          set S := dom out_pc.
          assert (S ⊆ insets Ic1) as S_sub_c1.
          { rewrite /S /out_pc. rewrite /outsets Domout_Ip1 big_opS_singleton 
              /outset in Out_In_c1. done. }
          assert (∀ k', inf Ic1 c !!! k' ≤ 1) as HInf_Ic1.
          { apply Hc. }
          assert (∀ n' k', out Ic1 n' !!! k' ≤ 1) as HOut_Ic1.
          { apply Hc. }
          assert (∀ k', out_pc !!! k' ≤ 1) as Hout_pc.
          { intros k'. rewrite /out_pc. apply Hp. }
          assert (insets Ic1' = insets Ic1 ∖ S) as Insets_Ic1'.
          { rewrite /insets Dom_Ic1' Dom_Ic1. apply leibniz_equiv. 
            rewrite !big_opS_singleton. 
            assert (inset _ Ic1' c = dom (inf Ic1 c - out_pc)%CCM) as ->.
            { rewrite /inset {1}/inf /=  lookup_insert /=. done. }
            rewrite /inset /S. rewrite set_equiv_subseteq.
            split. intros k' Hk'. apply nzmap_elem_of_dom_total in Hk'.
            rewrite lookup_total_lifting_inv in Hk'. rewrite elem_of_difference.
            rewrite /ccmunit /= /nat_unit /ccmop_inv /ccm_opinv /= 
              /nat_opinv in Hk'. 
            assert (inf Ic1 c !!! k' = 1 ∧ out_pc !!! k' = 0) as [H' H''].
            { pose proof HInf_Ic1 k' as H'. pose proof Hout_pc k' as H''.
              set a := inf Ic1 c !!! k'. set b := out_pc !!! k'.
              rewrite -/a in H'. rewrite -/b in H''. rewrite -/a -/b in Hk'.
              clear -H' H'' Hk'; split; try lia. }
            split. rewrite nzmap_elem_of_dom_total H' /ccmunit /= /nat_unit. 
            clear; lia. rewrite nzmap_elem_of_dom_total2 H''. 
            by rewrite /ccmunit /= /nat_unit.
            intros k' Hk'. rewrite elem_of_difference in Hk'.
            destruct Hk' as [Hk1' Hk2']. rewrite nzmap_elem_of_dom_total in Hk1'.
            rewrite /ccmunit /= /nat_unit in Hk1'.
            rewrite nzmap_elem_of_dom_total2 /ccmunit /= /nat_unit in Hk2'.
            rewrite nzmap_elem_of_dom_total /ccmunit /= /nat_unit /ccmop_inv.
            rewrite lookup_total_lifting_inv /ccmop_inv /ccm_opinv /= /nat_opinv.
            rewrite Hk2'. clear -Hk1'; lia. }
          assert (outsets Ic1' = outsets Ic1 ∖ S) as Outsets_Ic1'.
          { rewrite /outsets Domout_Ic1.
            destruct (decide ((out Ic1 cn - out_pc = 0)%CCM)) as [H' | H'].
            - assert (dom (out_map Ic1') = ∅) as H''.
              { rewrite /Ic1' /=. rewrite -leibniz_equiv_iff nzmap_dom_insert_zero.
                clear; set_solver. done. }
              rewrite H''. rewrite big_opS_empty -leibniz_equiv_iff. 
              rewrite big_opS_singleton. rewrite /monoid_unit /=.
              rewrite /ccmunit /lift_unit /ccmop_inv in H'. 
              apply set_equiv_subseteq. split; try done. intros k' Hk'.
              rewrite elem_of_difference in Hk'. destruct Hk' as [Hk1' Hk2'].
              rewrite /outset nzmap_elem_of_dom_total /ccmunit /= /nat_unit in Hk1'.
              rewrite /S nzmap_elem_of_dom_total2 /ccmunit /= /nat_unit in Hk2'. 
              rewrite nzmap_eq in H'. pose proof H' k' as H'. 
              rewrite nzmap_lookup_empty lookup_total_lifting_inv /ccmunit /= in H'.
              rewrite /ccmop_inv /ccm_opinv /= /nat_unit /nat_opinv in H'.
              rewrite Hk2' in H'. clear -Hk1' H'. exfalso. lia.
            - assert (dom (out_map Ic1') = {[cn]}) as H''.
              { rewrite /Ic1' /=. rewrite -leibniz_equiv_iff. 
                rewrite nzmap_dom_insert_nonzero /dom. clear; set_solver. done. }
              rewrite H''. rewrite -leibniz_equiv_iff !big_opS_singleton.
              rewrite /Ic1' /outset /S {1}/out /= nzmap_lookup_total_insert.
              rewrite /ccmop_inv. apply set_equiv_subseteq. split.
              + intros k' Hk'. rewrite nzmap_elem_of_dom_total /ccmunit /= in Hk'.
                rewrite lookup_total_lifting_inv /ccmop_inv /ccm_opinv /= in Hk'.
                rewrite /nat_opinv /nat_unit in Hk'. 
                pose proof HOut_Ic1 cn k' as H1'. pose proof Hout_pc k' as H1''.
                assert (out Ic1 cn !!! k' = 1 ∧ out_pc !!! k' = 0) as [Hk1 Hk2].
                { set a := out Ic1 cn !!! k'. set b := out_pc !!! k'.
                  rewrite -/a -/b in H1'' H1' Hk'. clear -H1'' H1' Hk'; lia. }
                rewrite elem_of_difference. split. rewrite nzmap_elem_of_dom_total.
                rewrite Hk1; try done. rewrite nzmap_elem_of_dom_total2 Hk2. done.
              + intros k' Hk'. rewrite elem_of_difference in Hk'.
                destruct Hk' as [Hk1' Hk2']. rewrite nzmap_elem_of_dom_total in Hk1'.
                rewrite nzmap_elem_of_dom_total2 in Hk2'. 
                rewrite nzmap_elem_of_dom_total lookup_total_lifting_inv Hk2'.
                rewrite ccm_pinv_unit. done. }
          assert (flow_constraints_I c Ic1' true (Some cn) (Key s1 c)) as Hc'.
          { destruct Hc as (Hc1&Hc2&Hc3&Hc4&Hc5&Hc6&Hc7). 
            split; last split; last split; last split; last split; 
              last split; try done.
            - intros H'. rewrite /Ic1' /=. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done.
              rewrite /dom. clear; set_solver. rewrite Out_Ic1.
              rewrite /insets Dom_Ic1' -leibniz_equiv_iff in H'. 
              rewrite big_opS_singleton /inset /Ic1' {1}/inf /= 
                lookup_insert /= in H'.
              intros H''. rewrite H'' in H'. apply H'.
              rewrite /ccmunit /=. clear; set_solver.
            - rewrite Insets_Ic1' Outsets_Ic1'. clear -Hc3 S_sub_c1; set_solver.
            - rewrite /keyset Insets_Ic1' Outsets_Ic1'.
              clear -Hc4 S_sub_c1; set_solver.
            - rewrite Insets_Ic1'. intros k'. rewrite elem_of_difference.
              intros [Hk1' Hk2']. by apply Hc5.
            - intros k'. rewrite /Ic1' /inf /= lookup_insert /=.
              rewrite /ccmop_inv lookup_total_lifting_inv /ccmop_inv /ccm_opinv /=.
              rewrite /nat_opinv.  
              set a := default 0%CCM (inf_map Ic1 !! c) !!! k'.
              assert (a ≤ 1) as H'. pose proof HInf_Ic1 k' as H'.
              rewrite /inf in H'. done. clear -H'; lia.
            - intros n' k'. rewrite /Ic1' /out /=.
              destruct (decide (n' = cn)) as [-> | Hn'cn].
              + rewrite nzmap_lookup_total_insert. rewrite /ccmop_inv.
                rewrite lookup_total_lifting_inv /ccmop_inv /ccm_opinv /= /nat_opinv.
                set a := (out_map Ic1 !!! cn) !!! k'.
                assert (a ≤ 1) as H'. pose proof HOut_Ic1 cn k' as H'.
                rewrite /out in H'. done. clear -H'; lia.
              + rewrite nzmap_lookup_total_insert_ne; try done.
                rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia. }
          assert (FP s1' = FP s1) as FP_s1'.
          { by rewrite /FP /s1' Hs1. }
          assert (abs s1' = abs s1) as Habs'.
          { by rewrite /abs /s1' Hs1. }
          iAssert (dsRepI γ_r (abs s1'))%I with "[Ds]" as "Ds".
          { by rewrite Habs'. }
          iAssert (own γ_ks (● prodKS (KS, abs s1')))%I with "[GKS]" as "GKS".
          { by rewrite Habs'. }
          assert (∀ n, n ≠ p → Next s1' n = Next s1 n) as HN.
          { intros n Hnc. 
            rewrite /Next /s1' Hs1 /= /Nx1' lookup_insert_ne; try done. }
          assert (Next s1' p = <[0:=cn]> (Next s1 p)) as HNp.
          { by rewrite /s1' Hs1 /Next /Nx1' lookup_insert Def_next' /Next Hs1. }
          assert (∀ n, Key s1' n = Key s1 n) as HK.
          { by rewrite /Key /s1' Hs1 /=. }
          assert (∀ n, n ≠ p → n ≠ c → FI s1' n = FI s1 n) as HI.
          { intros n Hnp Hnc. rewrite /FI /s1' /I1' Hs1 /= !lookup_insert_ne.
            all: done. }
          assert (FI s1' p = Ip1') as HIp.
          { rewrite /FI /s1' /I1' lookup_insert_ne; try done. 
            by rewrite lookup_insert. }
          assert (FI s1' c = Ic1') as HIc.
          { rewrite /FI /s1' /I1' lookup_insert; try done. }
          assert (∀ n, Mark s1' n = Mark s1 n) as HM.
          { by rewrite /FI /s1' Hs1. }
          assert (∀ n, Height s1' n = Height s1 n) as HT.
          { by rewrite /FI /s1' Hs1. }
          iAssert (⌜snapshot_constraints s1'⌝)%I as "SShot1'".
          { iPureIntro. exists FP1, C1, Ht1, Mk1, Nx1', Ky1, I1'.
            repeat split; try done.
            rewrite /Nx1'. rewrite dom_insert_L.
            assert (p ∈ dom Nx1) as H'. 
            { rewrite Hs1 in FP_p1. rewrite Dom_Nx1. by unfold FP in FP_p1. }
            clear -H' Dom_Nx1. set_solver.
            rewrite /I1' !dom_insert_L.
            assert ({[p;c]} ⊆ dom I1) as H'.
            { rewrite Hs1 /FP -Dom_I1 in FP_p1 FP_c1. 
              clear -FP_c1 FP_p1; set_solver. }
            clear -H' Dom_I1; set_solver. }
          assert (p ≠ tl) as p_neq_tl. 
          { intros ->. destruct PT_s1 as ((_&_&H'&_)&_). clear -H' Key_p1; lia. }
          assert (cn ∈ FP s1) as FP_cn1.
          { destruct PT_s1 as (_&_&_&_&_&H'&_). by pose proof H' c cn 0 Next_c1. }
          iAssert (resources γ_ks s1')%I 
            with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
          { iFrame "GKS". rewrite FP_s1'. iSplitR "Nodes_KS".
            rewrite (big_opS_delete _ (FP s1) p); try done.
            iSplitL "Node_p". rewrite Def_next' HNp HM HK HT. done.
            iApply (big_sepS_mono with "Nodes_rest"); try done.
            intros x Hx. iIntros "Hn". rewrite HK HM HT HN. done.
            clear -Hx; set_solver.
            iApply (big_sepS_mono with "Nodes_KS"); try done.
            intros x Hx. iIntros "Hn".
            assert (Content s1' x = Content s1 x) as ->.
            { rewrite /Content /Marki HM HK. done. }
            destruct (decide (x = p)) as [-> | Hxp].
            { assert (keyset (FI s1' p) = keyset (FI s1 p)) as ->.
              { rewrite HIp -I1_eq_s1 /keyset Insets_Ip1' Outsets_Ip1'. done. }
              done. }
            destruct (decide (x = c)) as [-> | Hxc].
            { assert (keyset (FI s1' c) = keyset (FI s1 c)) as ->.
              { rewrite HIc -I1_eq_s1 /keyset Insets_Ic1' Outsets_Ic1'. 
                destruct Hc as (_&_&_&H'&_). rewrite /keyset in H'. 
                clear -S_sub_c1 H'; set_solver. }
              done. }
            rewrite HI; try done. }
          
          iAssert (⌜∀ n k, n ∈ FP s1' → k ∈ keyset (FI s1' n) →
            (k ∈ abs s1' ↔ k ∈ Content s1' n)⌝)%I as "%Hks".
          { iDestruct "Res" as "(GKS & _ & HKS)".
            iPoseProof (keyset_summary with "GKS HKS") as "%H'"; try done. }

          assert (per_tick_inv s1') as PT_s1'.
          { destruct PT_s1 as (PT1'&PT2'&PT3'&PT4'&PT5'&PT6'&PT7').
            split; last split; last split; last split; last split; last split.
            - rewrite FP_s1' !HK !HM !HT. repeat split; try apply PT1'. 
              destruct (decide (p = hd)) as [-> | Hphd]. 
              rewrite HNp. rewrite lookup_insert_ne. apply PT1'. clear -HL; lia.
              all: rewrite HN; try done; apply PT1'.
            - rewrite /GFI. rewrite FP_s1'. rewrite /GFI in PT2'.
              assert (FP s1 = FP s1 ∖ {[p;c]} ∪ {[p;c]}) as H'.
              { apply set_eq_subseteq. split; clear -FP_p1 FP_c1; try set_solver.
                intros x Hx. rewrite elem_of_union. 
                destruct (decide (x ∈ ({[p;c]}: gset Node))) as [H' | H'].
                right. done. left; by rewrite elem_of_difference. } rewrite H'.
              rewrite big_opS_union; last first. clear; set_solver.
              assert (([^op set] y ∈ {[p;c]}, FI s1' y) = Ip1' ⋅ Ic1') as ->.
              { rewrite big_opS_union; last first. clear -p_neq_c; set_solver.
                rewrite !big_opS_singleton. rewrite /FI /s1' /I1'.
                rewrite lookup_insert_ne; try done. by rewrite !lookup_insert. }
              assert (([^op set] y ∈ (FP s1 ∖ {[p; c]}), FI s1' y) = 
              ([^op set] y ∈ (FP s1 ∖ {[p; c]}), FI s1 y)) as ->.
              { apply big_opS_ext. intros x Hx. rewrite /FI /s1' Hs1 /I1'.
                rewrite !lookup_insert_ne; try done. all: clear -Hx; set_solver. }
              rewrite Heq. rewrite H' big_opS_union in PT2'; last first.
              clear; set_solver. 
              assert (([^op set] y ∈ {[p; c]}, FI s1 y) = Ip1 ⋅ Ic1) as H''.
              { rewrite big_opS_union; last first. clear -p_neq_c; set_solver.
                rewrite !big_opS_singleton. rewrite -!I1_eq_s1. done. } 
              rewrite H'' in PT2'. done.
            - apply Hks. 
            - intros n Hn. rewrite FP_s1' in Hn. apply PT4' in Hn.
              destruct (decide (n = p)) as [-> | Hnp].
              + rewrite HNp HK HIp HM HT.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split; try done.
                * intros H'. assert (H1' := H'). apply Hn2 in H1'. 
                  rewrite dom_insert_L H1'.
                  assert (0 ∈ gset_seq 0 (Height s1 p - 1)) as H''.
                  { rewrite elem_of_gset_seq; split; clear; lia. }
                  clear -H''; set_solver. 
                * rewrite lookup_insert Mark_p1. done.
              + destruct (decide (n = c)) as [-> | Hnc]; last first.
                { rewrite HK HM HT. rewrite HN; try done. rewrite HI; try done. }
                rewrite HK HM HT HIc HN; try done.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split;
                  try done. rewrite Mark_c1 Next_c1. done.
            - intros n1 n2. destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp !HK.
                rewrite lookup_insert. intros [=<-]. clear -Key_pc Key_ccn. lia.
              + rewrite !HK /Nexti HN; try done. apply PT5'. 
            - intros n1 n2 i'. rewrite FP_s1'. 
              destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp. destruct (decide (i' = 0)) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. done.
                rewrite lookup_insert_ne; try done. apply PT6'.
              + rewrite /Nexti HN; try done. apply PT6'.
            - intros n1 n2 i. rewrite /Nexti. 
              destruct (decide (n1 = p)) as [-> | Hn1p]; last first.
              { rewrite HT HN; try done. apply PT7'. }
              rewrite HNp. destruct (decide (i = 0)) as [-> | Hi0].
              + rewrite lookup_insert HT. intros [=<-]. apply PT4' in FP_cn1.
                destruct FP_cn1 as (_&_&_&H'&_). clear -H'; lia.
              + rewrite HT lookup_insert_ne; try done. apply PT7'. }
          assert (transition_inv s1 s1') as Trans_s1.
          { repeat split; try rewrite FP_s1'; try done; last first.
            - intros n i' Hfp. rewrite /Marki HM. done.
            - intros n. rewrite /Marki HM. intros H' H''. 
              rewrite H' in H''; try done. 
            - intros n' i' Hn'. destruct (decide (n' = p)) as [-> | Hnp].
              + rewrite /Marki HM /Nexti HNp. 
                destruct (decide (i' = 0)) as [-> | Hi].
                rewrite Mark_p1. clear; try done.
                rewrite lookup_insert_ne; try done.
              + rewrite /Marki /Nexti HM HN; try done. }
          
          iAssert (⌜Key s1' p < k⌝)%I as %Key_p1k.
          { rewrite HK. by iPureIntro. }

          iAssert (⌜dom M1 = gset_seq 0 T1⌝)%I as %Dom_M1. 
          { by iDestruct "Hist" as (M1'') "(_&_&%&_)". }

          iAssert (|==> hist γ_t γ_m M1' (T1+1))%I with "[Hist]" as ">Hist".
          { iPoseProof (hist_upd _ _ _ _ _ s1' with "[%] [%] [$Hist]") as ">H'".
            apply  Habs1. intros <-. rewrite map_eq_iff in HNp.
            pose proof HNp 0 as HNp. rewrite Next_p1 lookup_insert in HNp.
            inversion HNp; try done. by rewrite /M1'. }
          iAssert (helping_inv N γ_t γ_r γ_mt γ_msy M1')%I with
            "[Help]" as "Help".
          { unfold update_helping_protocol2.
            iSpecialize ("Upd" $! M1 T1 s1').
            iPoseProof ("Upd" with "[%] [%] [Help]") as "Help"; try done.
            apply leibniz_equiv in Habs1. rewrite Habs1. by rewrite /s1' Hs1 /=.
            admit. }
          iPoseProof (snapshot_current with "[%] [$Ht0] [$Hist]") 
            as ">(#Past_s1'&Hist)"; try done.
          iEval (rewrite /M1' lookup_total_insert) in "Past_s1'".
        
          iAssert (traversal_inv γ_m t0 0 k p cn)%I as "#Htr'".
          { iSplitL; iExists s1'; iFrame "Past_s1'". iPureIntro. 
            repeat split; try (by rewrite FP_s1' || done).
            rewrite /Marki HM Mark_p1. done. rewrite HT. 
            apply PT_s1 in FP_p1. apply FP_p1.
            by rewrite /Nexti HNp lookup_insert. iPureIntro. split. 
            by rewrite FP_s1'. rewrite HT.
            apply PT_s1 in FP_cn1. apply FP_cn1. }  
          iModIntro. iSplitR "Hpost".
          { iNext. iExists M1', (T1+1), s1'. iFrame "∗#%".
            iPureIntro; rewrite /M1'; split; last split.
            - by rewrite lookup_total_insert.
            - intros t Ht. destruct (decide (t = T1+1)) as [-> | Ht'].
              + by rewrite lookup_total_insert.
              + rewrite lookup_total_insert_ne; try done. apply PT1.
                rewrite dom_insert in Ht. clear -Ht' Ht; set_solver.
            - intros t Ht. destruct (decide (t = T1)) as [-> | Ht'].
              + rewrite lookup_total_insert. rewrite lookup_total_insert_ne.
                apply leibniz_equiv in Habs1. by rewrite Habs1. clear; lia.
              + rewrite !lookup_total_insert_ne. apply Trans_M1.
                all: clear -Ht Ht'; lia. }
          wp_pures.
          iApply "IH"; try done.
        * assert (next' = Next s1 p) as Hnext'. 
          { rewrite Def_next'. apply map_eq. intros i'. 
            destruct (decide (i' = i)) as [-> | Hi]. 
            by rewrite lookup_insert Next_p1. by rewrite lookup_insert_ne. }
          rewrite Hnext'.
          iModIntro. iSplitR "Hpost".
          { iNext. iExists M1, T1, s1. iFrame "∗#%".
            rewrite (big_sepS_delete _ (FP s1) p); try done. iFrame. }
          wp_pures.
          iApply "IH"; try done.
        * iDestruct "SShot1" as %[FP1 [C1 [Ht1 [Mk1 [Nx1 [Ky1 [I1 
            [Hs1 [Dom_Ht1 [Dom_Mk1 [Dom_Nx1 [Dom_Ky1 Dom_I1]]]]]]]]]]]].
          set Nx1' := <[p := next']> Nx1.
          set s1' := (FP1, C1, Ht1, Mk1, Nx1', Ky1, I1): snapshot.
          set M1' := <[T1 + 1 := s1']> M1.
          
          assert (FP s1' = FP s1) as FP_s1'.
          { by rewrite /FP /s1' Hs1. }
          assert (abs s1' = abs s1) as Habs'.
          { by rewrite /abs /s1' Hs1. }
          iAssert (dsRepI γ_r (abs s1'))%I with "[Ds]" as "Ds".
          { by rewrite Habs'. }
          iAssert (own γ_ks (● prodKS (KS, abs s1')))%I with "[GKS]" as "GKS".
          { by rewrite Habs'. }
          assert (∀ n, n ≠ p → Next s1' n = Next s1 n) as HN.
          { intros n Hnc. 
            rewrite /Next /s1' Hs1 /= /Nx1' lookup_insert_ne; try done. }
          assert (Next s1' p = <[i:=cn]> (Next s1 p)) as HNp.
          { by rewrite /s1' Hs1 /Next /Nx1' lookup_insert Def_next' /Next Hs1. }
          assert (∀ n, Key s1' n = Key s1 n) as HK.
          { by rewrite /Key /s1' Hs1 /=. }
          assert (∀ n, FI s1' n = FI s1 n) as HI.
          { by rewrite /FI /s1' Hs1 /=. }
          assert (∀ n, Mark s1' n = Mark s1 n) as HM.
          { by rewrite /FI /s1' Hs1. }
          assert (∀ n, Height s1' n = Height s1 n) as HT.
          { by rewrite /FI /s1' Hs1. }
          
          assert (i < Height s1 c) as HT_ci. 
          { destruct PT_s1 as (_&_&_&_&_&_&H'). rewrite /Nexti in H'.
            by pose proof H' p c i Next_p1. }
          assert (i < Height s1 cn) as HT_cni. 
          { destruct PT_s1 as (_&_&_&_&_&_&H'). rewrite /Nexti in H'.
            by pose proof H' c cn i Next_c1. }
          assert (Key s1 p < W) as Key_pW.
          { clear -Key_pk Range_k; lia. }

          assert (p ≠ c) as p_neq_c.
          { intros ->. rewrite Mark_c1 in Mark_p1. done. }
          assert (p ≠ tl) as p_neq_tl.
          { intros ->. destruct PT_s1 as ((_&_&H'&_)&_). clear -H' Key_pW; lia. }
          assert (cn ∈ FP s1) as FP_cn1.
          { destruct PT_s1 as (_&_&_&_&_&H'&_). by pose proof H' c cn i Next_c1. }
          iAssert (⌜snapshot_constraints s1'⌝)%I as "SShot1'".
          { iPureIntro. exists FP1, C1, Ht1, Mk1, Nx1', Ky1, I1.
            repeat split; try done.
            rewrite /Nx1'. rewrite dom_insert_L.
            assert (p ∈ dom Nx1). 
            { rewrite Hs1 in FP_p1. rewrite Dom_Nx1. by unfold FP in FP_p1. }
            clear -H Dom_Nx1. set_solver. }

          iAssert (resources γ_ks s1')%I 
            with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
          { iFrame "GKS". rewrite FP_s1'. iSplitR "Nodes_KS".
            rewrite (big_opS_delete _ (FP s1) p); try done.
            iSplitL "Node_p". rewrite Def_next' HNp HT HM HK. done.
            iApply (big_sepS_mono with "Nodes_rest"); try done.
            intros x Hx. iIntros "Hn". rewrite HK HT HM HN. done.
            clear -Hx; set_solver.
            iApply (big_sepS_mono with "Nodes_KS"); try done.
            intros x Hx. iIntros "Hn". rewrite HI.
            assert (Content s1' x = Content s1 x) as ->.
            rewrite /Content HK /Marki HM. done. done. }

          assert (per_tick_inv s1') as PT_s1'.
          { destruct PT_s1 as (PT1'&PT2'&PT3'&PT4'&PT5'&PT6'&PT7').
            split; last split; last split; last split; last split; last split.
            - rewrite FP_s1' !HK !HM !HT. repeat split; try apply PT1'. 
              destruct (decide (p = hd)) as [-> | Hphd]. 
              rewrite HNp. destruct (decide (i = (L-1))) as [-> | Hi].
              destruct PT1' as (_&_&_&_&H'&H''&_). rewrite Next_p1 in H''.
              inversion H''. subst c. pose proof H' (L-1) as H'.
              rewrite H' in Mark_c1. clear -Mark_c1; done. clear -HL; lia.
              rewrite lookup_insert_ne; try done. apply PT1'.
              all: rewrite HN; try done; apply PT1'.
            - rewrite /s1' /GFI /FP /FI. by rewrite Hs1 /GFI /FP /FI in PT2'.
            - intros n k'. rewrite FP_s1' HI Habs' /Content /Marki HM HK.
              apply PT3'.
            - intros n Hn. rewrite FP_s1' in Hn. apply PT4' in Hn.
              destruct (decide (n = p)) as [-> | Hnp].
              + rewrite HNp HK HI HT HM.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split; try done.
                * intros H'. assert (H1' := H'). apply Hn2 in H1'. 
                  rewrite dom_insert_L H1'.
                  assert (i ∈ gset_seq 0 (Height s1 p - 1)) as H''.
                  rewrite elem_of_gset_seq. split; try lia.
                  clear -H''; set_solver.
                * rewrite lookup_insert_ne; try done.
              + rewrite HK HT HI HM. rewrite HN; try done.
            - intros n1 n2. destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp !HK. 
                rewrite lookup_insert_ne; try done. apply PT5'.
              + rewrite !HK /Nexti HN; try done. apply PT5'. 
            - intros n1 n2 i'. rewrite FP_s1'. 
              destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp. destruct (decide (i = i')) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. done. 
                rewrite lookup_insert_ne; try done. apply PT6'.
              + rewrite /Nexti HN; try done. apply PT6'.
            - intros n1 n2 i'. rewrite /Nexti. 
              destruct (decide (n1 = p)) as [-> | Hn1p]; last first.
              { rewrite HT HN; try done. apply PT7'. }
              rewrite HNp. destruct (decide (i' = i)) as [-> | Hii'].
              + rewrite lookup_insert HT. intros [=<-]. done.
              + rewrite HT lookup_insert_ne; try done. apply PT7'. }
          assert (transition_inv s1 s1') as Trans_s1.
          { repeat split; try rewrite FP_s1'; try done; last first.
            - intros n i' Hfp. rewrite /Marki HM. done.
            - intros n. rewrite /Marki HM. intros H' H''. 
              rewrite H' in H''; try done.
            - intros n' i' Hn'. destruct (decide (n' = p)) as [-> | Hnp].
              + rewrite /Marki HM /Nexti HNp. 
                destruct (decide (i' = i)) as [-> | Hi].
                rewrite Mark_p1. clear; try done.
                rewrite lookup_insert_ne; try done.
              + rewrite /Marki /Nexti HM HN; try done. }
          
          iAssert (⌜Key s1' p < k⌝)%I as %Key_p1k.
          { rewrite HK. by iPureIntro. }

          iAssert (⌜dom M1 = gset_seq 0 T1⌝)%I as %Dom_M1. 
          { by iDestruct "Hist" as (M1'') "(_&_&%&_)". }

          iAssert (|==> hist γ_t γ_m M1' (T1+1))%I with "[Hist]" as ">Hist".
          { iPoseProof (hist_upd _ _ _ _ _ s1' with "[%] [%] [$Hist]") as ">H'".
            apply  Habs1. intros <-. rewrite map_eq_iff in HNp.
            pose proof HNp i as HNp. rewrite Next_p1 lookup_insert in HNp.
            inversion HNp; try done. by rewrite /M1'. }
          iAssert (helping_inv N γ_t γ_r γ_mt γ_msy M1')%I with
            "[Help]" as "Help".
          { unfold update_helping_protocol2.
            iSpecialize ("Upd" $! M1 T1 s1').
            iPoseProof ("Upd" with "[%] [%] [Help]") as "Help"; try done.
            apply leibniz_equiv in Habs1. rewrite Habs1. by rewrite /s1' Hs1 /=.
            admit. }
          iPoseProof (snapshot_current with "[%] [$Ht0] [$Hist]") 
            as ">(#Past_s1'&Hist)"; try done.
          iEval (rewrite /M1' lookup_total_insert) in "Past_s1'".

          iAssert (traversal_inv γ_m t0 i k p cn)%I as "#Htr'".
          { iSplitL; iExists s1'; iFrame "Past_s1'"; iPureIntro. 
            repeat split; try (done || by rewrite FP_s1').
            rewrite /Marki HM. apply PT_s1 in FP_p1.
            destruct FP_p1 as (H'&_). apply H'. by exists i. by rewrite HT.
            split; first by rewrite FP_s1'. by rewrite HT. }  
          iModIntro. iSplitR "Hpost".
          { iNext. iExists M1', (T1+1), s1'. iFrame "∗#%".
            iPureIntro; rewrite /M1'; split; last split.
            - by rewrite lookup_total_insert.
            - intros t Ht. destruct (decide (t = T1+1)) as [-> | Ht'].
              + by rewrite lookup_total_insert.
              + rewrite lookup_total_insert_ne; try done. apply PT1.
                rewrite dom_insert in Ht. clear -Ht' Ht; set_solver.
            - intros t Ht. destruct (decide (t = T1)) as [-> | Ht'].
              + rewrite lookup_total_insert. rewrite lookup_total_insert_ne.
                apply leibniz_equiv in Habs1. by rewrite Habs1. clear; lia.
              + rewrite !lookup_total_insert_ne. apply Trans_M1.
                all: clear -Ht Ht'; lia. }
          wp_pures.
          iApply "IH"; try done.
      + iDestruct "Hsuccess" as %[Hcond ->].
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
          iFrame "Nodes_rest". iFrame. }
        wp_pures. iSpecialize ("Hpost" $! None). by iApply "Hpost".
    - awp_apply compareKey_spec. 
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
      { apply leibniz_equiv in Habs1. rewrite -Habs1.
        iApply (in_FP_2 with "[%] [$Hist] [$Past_s0] [%]"); try done. }
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
      iDestruct "Nodes" as "(Node_c & Nodes_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node_c". iModIntro. iFrame "Hpost Hc".
        iNext; iExists M1, T1, s1. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto. iFrame. }
      iIntros (res)"(Node_c & %Hif)".
      iPoseProof (snapshot_current with "[%] [$Ht0] [$Hist]") 
            as ">(#Past_s1&Hist)"; try done.
      iAssert (⌜Key s1 c = Key s0 c⌝)%I as %Key_c10.
      { apply leibniz_equiv in Habs1. rewrite -Habs1.
        iPoseProof (key_eq_2 with "[%] [$Hist] [$Past_s0] [%]") as "->"; try done. }
      iModIntro. iSplitR "Hpost".
      { iNext. iExists M1, T1, s1. iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
        iFrame "Nodes_rest". iFrame. }
      wp_pures.
      destruct (bool_decide (#res = #0)) eqn: Hbool; first last.
      + rewrite bool_decide_eq_false in Hbool.
        assert (res ≠ 0) as Hres0. { intros ->. by apply Hbool. } 
        wp_pures. destruct (bool_decide (#res = #1)) eqn:Hbool1; first last.
        * rewrite bool_decide_eq_false in Hbool1.
          assert (res ≠ 1) as Hres1. { intros ->. by apply Hbool1. } 
          wp_pures. iModIntro. iSpecialize ("Hpost" $! (Some (p,c,false))).
          iEval (rewrite /=) in "Hpost". iApply "Hpost". iFrame "Htr".
          iIntros "%Hi0". iApply "Hcase1"; try done. iPureIntro.
          repeat rewrite decide_False in Hif; try done.
          all : clear -Hif Key_c10; lia.
        * rewrite bool_decide_eq_true in Hbool1. inversion Hbool1.
          assert (res = 1) as -> by lia.
          wp_pures. iModIntro. iSpecialize ("Hpost" $! (Some (p,c,true))).
          iEval (rewrite /=) in "Hpost". iApply "Hpost". iFrame "Htr".
          iIntros "%Hi0". iApply "Hcase2"; try done. iPureIntro. 
          rewrite /= in Hif. repeat split; try (done || lia).
      + wp_pures. iApply "IH"; try done. iApply "Hcase"; try done. iPureIntro.
        rewrite -Key_c10. rewrite bool_decide_eq_true in Hbool. inversion Hbool.
        rewrite decide_True in Hif. done. clear -H0; lia.
    - exfalso; apply Hcontra; try done. 
    - iModIntro. iSpecialize ("Hpost" $! (Some (p,c,false))). 
      iEval (rewrite /=) in "Hpost". iApply "Hpost". iFrame "Htr".
      iIntros "%Hi0". iApply "Hcase3"; try done.
  Admitted.

  Lemma traverse_pop_spec N γ_t γ_r γ_m γ_mt γ_msy tid t0 k 
    preds succs ps0 ss0 (i: nat):
    main_inv N γ_t γ_r γ_m γ_mt γ_msy  -∗
    thread_start γ_t γ_mt tid t0 -∗
    □ update_helping_protocol2 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
        {{{ is_array preds ps0 ∗ is_array succs ss0 
            ∗ ⌜length ps0 = L⌝ ∗ ⌜length ss0 = L⌝ ∗ ⌜i+1 < L⌝
            ∗ ⌜ps0 !!! (L-1) = hd⌝ ∗ ⌜ss0 !!! (L-1) = tl⌝
            ∗ (∀ j, ⌜i < j < L⌝ → traversal_inv γ_m t0 j k (ps0 !!! j) (ss0 !!! j)) }}}
          traverse_pop traverse_rec #k #preds #succs #i @ ⊤
        {{{ (ores: option (loc * loc * bool)) (ps ss: list Node) (b: bool), 
              RET (match ores with 
                    None => NONEV 
                  | Some res => SOMEV (#res.1.1,#res.1.2,#res.2) end);
              match ores with 
                None => is_array preds ps0 ∗ is_array succs ss0
              | Some res =>
                ⌜res.1.1 = preds⌝ ∗ ⌜res.1.2 = succs⌝ ∗ ⌜res.2 = b⌝
              ∗ is_array preds ps ∗ is_array succs ss
              ∗ ⌜length ps = L⌝ ∗ ⌜length ss = L⌝
              ∗ ⌜ps !!! (L-1) = hd⌝ ∗ ⌜ss !!! (L-1) = tl⌝
              ∗ (∀ j, ⌜i-1 < j < L⌝ → traversal_inv γ_m t0 j k (ps !!! j) (ss !!! j))
              ∗ (⌜i = 0⌝ →  let p := ps !!! 0 in
                            let c := ss !!! 0 in
                            traversal_inv γ_m t0 0 k p c ∗ 
                            (∃ s, past_state γ_m t0 s ∗
                              ⌜if b then 
                                  k ∈ abs s ∧ k = Key s c 
                                  ∧ c ∈ FP s ∧ Marki s c 0 = false
                                else 
                                  k ∉ abs s ∧ k < Key s c 
                                  ∧ c ∈ FP s⌝)) end }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & %Len_ps0 & %Len_ss0 & %Len_i 
      & %Hps0_L & %Hss0_L & #Hj)". 
    wp_lam. wp_pures. iEval (rewrite /is_array) in "Hpreds".
    assert (is_Some (ps0 !! (i+1))) as [p Hp].
    { by rewrite lookup_lt_is_Some Len_ps0. } 
    assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
    iEval (rewrite <-H'). clear H'.
    wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i+1) ((λ n : loc, #n) <$> ps0) #p
      with "[Hpreds]"); try done. 
    { by rewrite list_lookup_fmap Hp /=. }
    { iNext. admit. }
    iIntros "Hpreds".
    iAssert (is_array preds ps0) with "[Hpreds]" as "Hpreds".
    { unfold is_array. admit. }
    wp_pures. wp_bind (findNext _ _)%E. 
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (traversal_inv γ_m t0 (i+1) k p (ss0 !!! (i+1)%nat))%I as "#Htr_i1". 
    { iAssert (⌜i < i+1 < L⌝)%I as "H'". by iPureIntro; lia.
      iPoseProof ("Hj" with "H'") as "H''". 
      apply list_lookup_total_correct in Hp. rewrite Hp. done. }
    iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0. 
      iDestruct "Htr_i1" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
      destruct Htr_sp as (H'&_).
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
    rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
    iDestruct "Nodes" as "(Node_p & Nodes_rest)".
    iAssert (⌜i < Height s0 p⌝)%I as %Height_p0.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iDestruct "Htr_i1" as "(H'&_)". iDestruct "H'" as (s)"(Past_s & %Htr_sp)".
      destruct Htr_sp as (H''&_&_&H').
      iPoseProof (height_eq_2 p with "[%] [$Hist] [$Past_s] [%]") as "->"; 
        try done. iPureIntro. clear -H'; lia. }
    iAssert ((node p (Height s0 p) (Mark s0 p) (Next s0 p) (Key s0 p)) 
      ∗ ⌜i < Height s0 p⌝)%I with "[Hj Node_p]" as "Hpre".
    { iFrame "Node_p %". }
    iAaccIntro with "Hpre".    
    { iIntros "(Node_p&_)". iModIntro. iFrame "Hpost Hpreds Hsuccs".
      iNext; iExists M0, T0, s0. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    iIntros (m oc) "(Node_p & %Mark_p0 & %Next_p0)".
    iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iDestruct "Htr_i1" as "(Htr_p & Htr_si1)".
    iDestruct "Htr_p" as (s)"(#Past_s & %Htr_p)".
    iAssert (⌜Key s0 p = Key s p⌝)%I as %Key_p.
    { apply leibniz_equiv in Habs0. rewrite -Habs0.
      iPoseProof (key_eq_2 with "[%] [$Hist] [$Past_s] [%]") as "->"; try done.
      apply Htr_p. }
    destruct oc as [c |]; last first.
    { apply PT_s0 in FP_p0. assert (p ≠ tl) as H'.
      { intros ->. destruct PT_s0 as ((_&_&H'&_)&_). 
        destruct Htr_p as (_&H''&_). rewrite -Key_p H' in H''. lia. }
      apply FP_p0 in H'. apply not_elem_of_dom in Next_p0. 
      rewrite H' in Next_p0. exfalso; apply Next_p0.
      rewrite elem_of_gset_seq. split; try lia. }
    iAssert (own γ_t (◯ MaxNat t0)) as "#Ht0".
    { by iDestruct "Thd_st" as "(_&H')". }
    iPoseProof (snapshot_current with "[%] [$Ht0] [$Hist]") 
      as ">(#Past_s0&Hist)"; try done.
    iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> traversal_inv γ_m t0 i k p c ∗ 
      hist γ_t γ_m M0 T0)%I with "[Hist]" as ">(#Hcase & Hist)".
    { iAssert (∃ s1 : snapshot, past_state γ_m t0 s1 ∗ 
        ⌜c ∈ FP s1 ∧ i < Height s1 c⌝)%I as "#Htr_c".
      { iExists s0. iFrame "Past_s0". iPureIntro. 
        destruct PT_s0 as (_&_&_&_&_&H'&H''). split. 
        apply (H' p c i); try done. apply (H'' p c i); try done. }
      iFrame "Htr_c". 
      destruct (decide (i = 0)) as [-> | Hi0].
      - destruct m.
        + iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
          { by iDestruct "Hist" as (M0'') "(_&_&%&_)". }
          destruct Htr_p as (FP_ps&Key_ps&Mark_ps&Height_ps&_).
          iDestruct "Past_s" as (ts)"(%t0_le_ts&Hts)".
          iPoseProof (marking_witness with "[%] [Hist] [Hts] [%] [%] [%]") 
            as "%HM"; try done. 
          apply leibniz_equiv in Habs0. by rewrite /Marki Habs0.
          destruct HM as [t [Ht [Hmt Hmt']]].
          assert (0 ≤ t < T0) as Ht'. lia.
          apply Trans_M0 in Ht'. rewrite Nat.add_1_r in Ht'.
          destruct Ht' as (Hm'&_&_&_&_&Hfp'). 
          assert (t ∈ dom M0) as t_in_M0. 
          { rewrite Dom_M0 elem_of_gset_seq; lia. }
          assert (H'' := t_in_M0).
          apply elem_of_dom in t_in_M0. destruct t_in_M0 as [s' Hs'].
          iPoseProof (snapshot_create t with "[%] [%] [$Ht0] [Hist]")
            as ">(#Past_t & Hist)"; try done. lia.

          iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> own γ_m (◯ {[t := to_agree s']}) 
            ∗ hist γ_t γ_m M0 T0)%I with "[Hist]" as ">(#Ht & Hist)".
          { iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
            iPoseProof (own_update _ (● M') (● M' ⋅ ◯ {[t := to_agree s']}) 
              with "HM'") as ">(HM' & #Ht')". 
            { apply auth_update_alloc, local_update_unital_discrete. 
              intros z Hm Hz. split; try done. rewrite left_id in Hz. 
              rewrite -Hz. apply map_equiv_iff. intros x. apply M_eq in Hs'.
              destruct (decide (x = t)) as [-> | Hxz].
              - rewrite lookup_op Hs' lookup_insert. rewrite /op /cmra_op /=.
                by rewrite agree_idemp.
              - rewrite lookup_op lookup_insert_ne; try done. rewrite lookup_empty.
                rewrite /op /cmra_op /=. destruct (M' !! x) eqn:H1'; 
                rewrite H1'; try done. }
            iModIntro. iFrame "Ht'". iExists M'. iFrame "∗%". } 
          assert (ts ≤ t ≤ T0) as Ht' by lia.
          iPoseProof (in_FP p with "[%] [$Hist] [$Hts] [%] [%]") 
            as "%FP_pt"; try done.
          pose proof Hm' p 0 FP_pt Hmt' as Hn'.

          assert (S t ∈ dom M0) as Hst.
          { rewrite Dom_M0 elem_of_gset_seq. lia. }
          assert (t0 ≤ S t) as Hst' by lia.
          iPoseProof (snapshot_create (S t) with "[%] [%] [Ht0] [Hist]")
            as ">(#Past_st & Hist)"; try done.
          assert (FP_pst := FP_pt). apply Hfp' in FP_pst.
          iPoseProof (next_unchanged with "[%] [$Hist] [$Past_st] [%] [%]")
            as "%H'"; try done. rewrite -H' in Hn'.
          apply leibniz_equiv in Habs0. rewrite Habs0 /Nexti Next_p0 in Hn'.
          iPoseProof (height_eq with "[%] [$Hist] [$Hts] [%] [%]")
            as "%HH"; try done.
          iPoseProof (key_eq with "[%] [$Hist] [$Hts] [%] [%]")
            as "%HK"; try done.
          iModIntro. iFrame. iExists (M0 !!! t). iFrame "#". iPureIntro.
          repeat split; try done. clear -HK Key_ps; lia.  clear -HH Height_ps; lia.
        + iModIntro. iFrame.
          iExists s0. iFrame "Past_s0". iPureIntro. 
          repeat split; try done. destruct Htr_p as (_&H'&_). 
          clear -H' Key_p; lia.
      - iModIntro. iFrame.
        iExists s. iFrame "Past_s". iPureIntro. repeat split; try apply Htr_p.
        destruct Htr_p as (_&_&_&H'&_). clear -H'; lia. intros ?; try done. }
    
    iModIntro. iSplitR "Hpreds Hsuccs Hpost Hj".
    { iNext. iExists M0, T0, s0. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    wp_pures. wp_apply traverse_i_spec; try done.
    iIntros (ores) "Hores".
    destruct ores as [[[p' c'] b]|]; last first.
    { wp_pures. iSpecialize ("Hpost" $! None ps0 ss0 true). iApply "Hpost".
      iFrame. done. }
    iSimpl in "Hores". wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hpreds]").
    { iFrame "Hpreds". iPureIntro. rewrite Len_ps0. lia. }
    iIntros "!> Hpreds". wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hsuccs]").
    { iFrame "Hsuccs". iPureIntro. rewrite Len_ss0. lia. }
    iIntros "!> Hsuccs". wp_pures.
    iSpecialize ("Hpost" $! (Some (preds,succs,b)) _ _ b).
    iSimpl in "Hpost". iApply "Hpost".
    iModIntro. iFrame "Hpreds Hsuccs". repeat (iSplitR; first by iPureIntro).
    iDestruct "Hores" as "(#Htr & #Hzero)".
    iSplitR. iPureIntro. by rewrite insert_length.
    iSplitR. iPureIntro. by rewrite insert_length.
    iSplitR. iPureIntro. rewrite list_lookup_total_insert_ne; try done. 
    clear -Len_i; lia.  
    iSplitR. iPureIntro. rewrite list_lookup_total_insert_ne; try done. 
    clear -Len_i; lia.  
    iSplitR. iIntros (j)"%Hj". destruct (decide (j = i)) as [-> | Hij].
    { rewrite !list_lookup_total_insert. iFrame "#". 
      all: try rewrite Len_ps0 Len_ss0; lia. }
    iAssert (⌜i < j < L⌝)%I as "Hj'". { iPureIntro. lia. }
    iPoseProof ("Hj" with "Hj'") as "H'".
    rewrite !list_lookup_total_insert_ne; try done.
    iIntros "%". subst i. rewrite !list_lookup_total_insert.
    iFrame "∗#". iApply "Hzero". by iPureIntro.
    all: try rewrite Len_ps0 Len_ss0; lia.
  Admitted.

  Lemma traverse_rec_spec N γ_t γ_r γ_m γ_mt γ_msy tid 
    t0 k preds succs ps0 ss0 (i: nat):
    main_inv N γ_t γ_r γ_m γ_mt γ_msy  -∗
    thread_start γ_t γ_mt tid t0 -∗
    □ update_helping_protocol2 N γ_t γ_r γ_mt γ_msy -∗ 
    ⌜1 < L ∧ 0 < k < W⌝ -∗
      {{{ is_array preds ps0 ∗ is_array succs ss0
          ∗ ⌜length ps0 = L⌝ ∗ ⌜length ss0 = L⌝ ∗ ⌜i+1 < L⌝
          ∗ ⌜ps0 !!! (L-1) = hd⌝ ∗ ⌜ss0 !!! (L-1) = tl⌝
          ∗ (∀ j, ⌜i < j < L⌝ → traversal_inv γ_m t0 j k (ps0 !!! j) (ss0 !!! j)) }}}
        traverse_rec #k #preds #succs #i @ ⊤
      {{{ (ps ss: list Node) (res: bool), 
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
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iLöb as "IH" forall (i ps0 ss0). 
    iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & %Len_ps0 & %Len_ss0 & %Len_i 
      & %Hps0_L & %Hss0_L & #Hj)".
    wp_lam. wp_pures. iApply fupd_wp.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (own γ_t (◯ MaxNat t0))%I as "#Ht0".
    { iDestruct "Thd_st" as "(_&H'')". iFrame "#". }
    iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iPoseProof (traversal_inv_hd_tl with "[%] [%] [%] [%] [$Ht0] [Hist]") 
      as ">(#HtrL & Hist)"; try done.
    iModIntro. iSplitR "Hpreds Hsuccs Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%". }
    iModIntro.      
    wp_apply (traverse_pop_spec with "[] [] [] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs Hj %". iIntros (ores ps ss b)"Hores".
    destruct ores as [[[preds' succs'] res] |]; last first.
    { wp_pures. iDestruct "Hores" as "(Hpreds & Hsuccs)".
      iApply ("IH" with "[Hpreds Hsuccs]"); try iFrame "∗%#". 
      iSplitR. iPureIntro. lia. iIntros (j)"%Hj".
      assert (j = L-1) as -> by lia. rewrite Hps0_L Hss0_L. iFrame "HtrL". }
    wp_pures. iDestruct "Hores" as "(%H' & %H'' & %H1' & H1'')". 
    rewrite /= in H' H'' H1'. subst preds' succs' b.  
    iDestruct "H1''" as "(Hpreds & Hsuccs & %Len_ps & %Len_ss & %Hps_L 
      & %Hss_L & #Hj' & #Hi0)".
    destruct (bool_decide (#i = #0)) eqn: Hbool; wp_pures.
    - rewrite bool_decide_eq_true in Hbool. inversion Hbool. iModIntro.
      iApply "Hpost". iFrame "Hpreds Hsuccs %".
      iAssert (⌜i = 0⌝)%I as "Htr0". { iPureIntro; lia. }
      iDestruct ("Hi0" with "Htr0") as "#H'". iSplit.
      + iIntros (j) "%Hj". destruct (decide (j = 0)) as [-> | Hj0].
        * iDestruct "H'" as "(H' & _)". iFrame "H'".
        * iApply "Hj'". iPureIntro; lia.
      + iDestruct "H'" as "(_ & H')". iFrame "H'".
    - iSpecialize ("IH" $! (i-1) ps ss).
      rewrite bool_decide_eq_false in Hbool.
      assert (i ≠ 0). { intros ->. apply Hbool. try done. }
      assert (Z.sub i 1 = (i-1)%nat) as -> by lia.
      iApply ("IH" with "[$Hpreds $Hsuccs]"); try done. iFrame "%#".
      iPureIntro. clear -Len_i; lia.
  Qed.

Lemma traverse_spec N γ_t γ_r γ_m γ_mt γ_msy tid t0 k:
    main_inv N γ_t γ_r γ_m γ_mt γ_msy  -∗
    thread_start γ_t γ_mt tid t0 -∗
    □ update_helping_protocol2 N γ_t γ_r γ_mt γ_msy -∗ 
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
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k]". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures. wp_bind (AllocN _ _)%E. 
    iApply array_repeat. iPureIntro; lia.
    iNext. iIntros (preds) "Hpreds".
    wp_pures. wp_bind (AllocN _ _)%E.
    iApply array_repeat. iPureIntro; lia.
    iNext. iIntros (succs) "Hsuccs". wp_pures. iApply fupd_wp.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iAssert (own γ_t (◯ MaxNat t0))%I as "#Ht0".
    { iDestruct "Thd_st" as "(_&H'')". iFrame "#". }
    iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
    { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
    iPoseProof (traversal_inv_hd_tl with "[%] [%] [%] [%] [$Ht0] [Hist]") 
      as ">(#HtrL & Hist)"; try done.
    iModIntro. iSplitR "Hpreds Hsuccs Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%". }
    iModIntro.      
    wp_apply (traverse_rec_spec with "[] [] [] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs".
    iSplitR. iPureIntro. by rewrite replicate_length.
    iSplitR. iPureIntro. by rewrite replicate_length.
    iSplitR. iPureIntro. clear -HL; lia.
    iSplitR. iPureIntro. rewrite lookup_total_replicate_2. done. lia.
    iSplitR. iPureIntro. rewrite lookup_total_replicate_2. done. lia.
    (* iFrame "Htr". *) iIntros (j) "%Hj". 
    assert (j = L-1) as -> by lia. rewrite !lookup_total_replicate_2.
    all : try lia. iFrame "HtrL". 
  Qed.

End SKIPLIST1_SPEC_TRAVERSE.
  
  
