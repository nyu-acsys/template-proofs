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
Require Export skiplist_v1 skiplist_v1_util.

Module SKIPLIST1_SPEC_TRAVERSE.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS.

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
     ⊢ (<<< ∀∀ mark next k, node n mark next k >>>
           findNext #n #i @ ⊤
       <<< ∃∃ (m: bool) (opt_n': option Node),
              node n mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !! i = opt_n'⌝,
              RET (match opt_n' with None => (#m, NONEV) 
                                    | Some n' => (#m, SOMEV #n') end) >>>)%I.

  Parameter try_constraint_traverse_spec : ∀ (pred curr new_node: Node) (i: nat),
     ⊢ (<<< ∀∀ mark next k, node pred mark next k >>>
           try_constraint #pred #curr #new_node #i @ ⊤
       <<< ∃∃ (success: bool) next',
              node pred mark next' k
            ∗ (match success with true => ⌜next !! i = Some curr 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := new_node]> next⌝
                                | false => ⌜(next !! i ≠ Some curr ∨ 
                                              mark !!! i = true)
                                            ∧ next' = next⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.

  Parameter compareKey_spec : ∀ (n: Node) (k': nat),
     ⊢ (<<< ∀∀ mark next k, node n mark next k >>>
           compareKey #n #k' @ ⊤
       <<< ∃∃ (res: nat),
              node n mark next k ∗ 
              ⌜if decide (res = 0) then k < k'
               else if decide (res = 1) then k = k'
               else k > k'⌝,
              RET #res >>>)%I.
                                    

  Definition traversal_inv s i k p c : Prop :=
    p ∈ FP s 
  ∧ c ∈ FP s 
  ∧ Key s p < k 
  ∧ Marki s p i = false 
  ∧ Nexti s p i = Some c.

  Lemma traverse_i_spec N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght
  γ_sy t_id t0 k (i: nat) (p c: Node):
  main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
    thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
    {{{ (∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p c⌝) }}}
      traverse_i #i #p #c #k
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
            (∃ s, past_state γ_m t0 s 
              ∗ ⌜traversal_inv s i k p' c'⌝
              ∗ ⌜i = 0 → if b then k ∈ keyset (FI s c') ∧ k = Key s c'
                          else k ∉ abs s⌝) end }}}.
  Proof.
    iIntros "#HInv #Thd". iLöb as "IH" forall (p c).
    iIntros (Φ) "!# #HtrInv Hpost". wp_lam. wp_pures.
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Nodes" as "(Node_c & Nodes_rest)".
    iAaccIntro with "Node_c".
    { iIntros "Node". iModIntro. iFrame "Hpost".
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Nodes_rest". iFrame. }
    iIntros (m c') "(Node_c & %Mark_c0 & %Next_c0)".
    iModIntro. iSplitR "Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Nodes_rest". iFrame. }
    destruct c' as [cn |]; destruct m; wp_pures. 
    - awp_apply try_constraint_traverse_spec; try done.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p1.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAaccIntro with "Node_p".
      { iIntros "Node_p". iModIntro. iFrame "Hpost".
        iNext; iExists M1, T1, s1. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto. iFrame. }
      iIntros (success next') "(Node_p & Hsuccess)".
      destruct success.
      + iDestruct "Hsuccess" as %[Next_p1 [Mark_p1 Def_next']].
        destruct (decide (i = 0)) as [-> | Hi0].
        * iDestruct "SShot1" as %[FP1 [C1 [Mk1 [Nx1 [Ky1 [I1 
            [Hs1 [Dom_Mk1 [Dom_Nx1 [Dom_Ky1 Dom_I1]]]]]]]]]].
          set Nx1' := <[p := next']> Nx1.
          set Ip1 := I1 !!! p. set Ic1 := I1 !!! c. set out_pc := out Ip1 c.
          set Ip1' := int {| infR := inf_map Ip1; outR :=  <<[cn := out_pc]>> ∅ |}.
          set Ic1': multiset_flowint_ur nat := 
            int {| infR := {[c := ∅]}; outR := ∅ |}.
          set I1' := <[c := Ic1']> (<[p := Ip1']> I1).
          set s1' := (FP1, C1, Mk1, Nx1', Ky1, I1'): snapshot.
          set M1' := <[T1 + 1 := s1']> M1.
          


        * iDestruct "SShot1" as %[FP1 [C1 [Mk1 [Nx1 [Ky1 [I1 
            [Hs1 [Dom_Mk1 [Dom_Nx1 [Dom_Ky1 Dom_I1]]]]]]]]]].
          set Nx1' := <[p := next']> Nx1.
          set s1' := (FP1, C1, Mk1, Nx1', Ky1, I1): snapshot.
          set M1' := <[T1 + 1 := s1']> M1.
          iAssert (⌜per_tick_inv s1⌝)%I as %PT_s1.
          { iDestruct "Hist" as (M')"(_&_&_&%&_)". iPureIntro.
            apply leibniz_equiv in Habs1. rewrite <-Habs1.
            by apply PT1. }
          iAssert (hist γ_t γ_m M1' (T1+1))%I with "[Hist]" as "Hist".
          { admit. }
          iAssert (▷ helping_inv N γ_t γ_r γ_td1 γ_td2 γ_ght M1')%I with
            "[Help]" as "Help".
          { admit. }
          iAssert (past_state γ_m t0 s1')%I as "Past_s1'".
          { admit. }
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
          assert (p ≠ tl) as p_neq_tl. admit.
          assert (Key s1 p < Key s1 cn) as Key_pcn. admit.
          assert (cn ∈ FP s1) as FP_cn1. admit.
          iAssert (⌜snapshot_constraints s1'⌝)%I as "SShot1'".
          { iPureIntro. exists FP1, C1, Mk1, Nx1', Ky1, I1.
            repeat split; try done.
            rewrite /Nx1'. rewrite dom_insert_L.
            assert (p ∈ dom Nx1). 
            { rewrite Hs1 in FP_p1. rewrite Dom_Nx1. by unfold FP in FP_p1. }
            clear -H Dom_Nx1. set_solver. }
          assert (per_tick_inv s1') as PT_s1'.
          { destruct PT_s1 as (PT1'&PT2'&PT3'&PT4'&PT5').
            split; last split; last split; last split.
            - destruct PT1' as (PT11'&PT12'&PT13'&PT14'&PT15'). repeat split.
              + intros i'. rewrite /Marki HM. apply PT11'.
              + rewrite HK. apply PT12'.
              + rewrite HK. apply PT13'.
              + by rewrite FP_s1'.
              + by rewrite FP_s1'.
            - rewrite /s1' /GFI /FP /FI. by rewrite Hs1 /GFI /FP /FI in PT2'.
            - intros n Hn. rewrite FP_s1' in Hn. apply PT3' in Hn.
              destruct (decide (n = p)) as [-> | Hnp].
              + rewrite HNp HK HI HM.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split; try done.
                * intros i'. destruct (decide (i' = i)) as [-> | Hi'i].
                  rewrite lookup_insert. split; try done.
                  rewrite lookup_insert_ne; try done.
                * rewrite dom_insert. clear -Hn3; set_solver.
                * rewrite lookup_insert_ne; try done.
              + rewrite HK HI HM. rewrite HN; try done.
            - intros n1 n2 i'. destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp !HK. destruct (decide (i = i')) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. done. 
                rewrite lookup_insert_ne; try done. apply PT4'.
              + rewrite !HK /Nexti HN; try done. apply PT4'. 
            - intros n1 n2 i'. rewrite FP_s1'. 
              destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp. destruct (decide (i = i')) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. done. 
                rewrite lookup_insert_ne; try done. apply PT5'.
              + rewrite /Nexti HN; try done. apply PT5'. }
          assert (transition_inv s1 s1') as Trans_s1.
          { repeat split; try rewrite FP_s1'; try done; last first.
            - intros n i' Hfp. rewrite /Marki HM. done.
            - intros n. rewrite /Marki HM. intros H' H''. 
              rewrite H' in H''; try done. }
          iAssert (resources γ_ks s1')%I 
            with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
          { iFrame "GKS". rewrite FP_s1'. iSplitR "Nodes_KS".
            rewrite (big_opS_delete _ (FP s1) p); try done.
            iSplitL "Node_p". rewrite Def_next' HNp HM HK. done.
            iApply (big_sepS_mono with "Nodes_rest"); try done.
            intros x Hx. iIntros "Hn". rewrite HK HM HN. done.
            clear -Hx; set_solver.
            iApply (big_sepS_mono with "Nodes_KS"); try done.
            intros x Hx. iIntros "Hn". rewrite HI.
            assert (Content s1' x = Content s1 x) as ->.
            rewrite /Content HK /Marki HM. done. done. }

          iAssert (∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p cn⌝)%I 
            as "#HtrInv'".
          { iExists s1'. iFrame "#". iPureIntro. repeat split.
            rewrite FP_s1'; try done. rewrite FP_s1'; try done.
            admit. rewrite /Marki HM Mark_p1. done. rewrite /Nexti HNp.
            by rewrite lookup_insert. }  
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
      { admit. }
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
      iDestruct "Nodes" as "(Node_c & Nodes_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node_c". iModIntro. iFrame "Hpost".
        iNext; iExists M1, T1, s1. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto. iFrame. }
      iIntros (res)"(Node_c & %Hif)".
      iAssert (past_state γ_m t0 s1) as "#Hs1".
      { admit. }
      iModIntro. iSplitR "Hpost".
      { iNext. iExists M1, T1, s1. iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
        iFrame "Nodes_rest". iFrame. }
      wp_pures.
      destruct (bool_decide (#res = #0)) eqn: Hbool; first last.
      + rewrite bool_decide_eq_false in Hbool.
        assert (res ≠ 0) as Hres0. { intros ->. by apply Hbool. } 
        wp_pures. destruct (bool_decide (#res = #1)) eqn:Hbool1; first last.
        * wp_pures. iModIntro. iSpecialize ("Hpost" $! (Some (p,c,false))).
          iEval (rewrite /=) in "Hpost". iApply "Hpost".
          iDestruct "HtrInv" as (s)"(Past_s & Hpc)".
          iExists s. iFrame "#". admit.  
        * rewrite bool_decide_eq_true in Hbool1. inversion Hbool1.
          assert (res = 1) as -> by lia.
          wp_pures. iModIntro. iSpecialize ("Hpost" $! (Some (p,c,true))).
          iEval (rewrite /=) in "Hpost". iApply "Hpost".
          iDestruct "HtrInv" as (s)"(Past_s & Hpc)".
          iExists s. iFrame "#". admit.  
      + wp_pures. iApply "IH". { iExists s0. admit. }
        iFrame.
    - (* Contradiction case *) admit.
    - iModIntro. iSpecialize ("Hpost" $! (Some (p,c,false))). 
      iEval (rewrite /=) in "Hpost". iApply "Hpost".
      iDestruct "HtrInv" as (s)"(Past_s & Hpc)".
      iExists s. iFrame "#". admit.  
  Admitted.

  Lemma traverse_pop_spec N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght
    γ_sy t_id t0 k preds succs ps0 ss0 (i: nat):
    main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
      thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ is_array preds ps0 ∗ is_array succs ss0
            ∗ (∀ j, ⌜i < j < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s j k (ps0 !!! j) (ss0 !!! j)⌝) }}}
          traverse_pop traverse_rec #k #preds #succs #i
        {{{ (ores: option (loc * loc * bool)) (ps ss: list Node) (b: bool), 
              RET (match ores with 
                    None => NONEV 
                  | Some res => SOMEV (#res.1.1,#res.1.2,#res.2) end);
              match ores with 
                None => is_array preds ps0 ∗ is_array succs ss0
              | Some res =>
                ⌜res.1.1 = preds⌝ ∗ ⌜res.1.2 = succs⌝ ∗ ⌜res.2 = b⌝
              ∗ is_array preds ps ∗ is_array succs ss
              ∗ (∀ j, ⌜i-1 < j < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s j k (ps !!! j) (ss !!! j)⌝)
              ∗ (⌜i = 0⌝ →  let p := ps !!! 0 in
                            let c := ss !!! 0 in
                            (∃ s, past_state γ_m t0 s 
                            ∗ ⌜traversal_inv s 0 k p c⌝
                            ∗ ⌜if b then k ∈ keyset (FI s c) ∧ k = Key s c
                                else k ∉ abs s⌝)) end }}}.
  Proof.
    iIntros "#HInv #Thd". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & Hj)". wp_lam. wp_pures.
    iEval (rewrite /is_array) in "Hpreds".
    assert (is_Some (ps0 !! (i+1))) as [p Hp].
    { admit. } 
    assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
    iEval (rewrite <-H').
    wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i+1) ((λ n : loc, #n) <$> ps0) #p
      with "[Hpreds]"); try done.
    { admit. }
    { iNext. admit. }
    iIntros "Hpreds".
    iAssert (is_array preds ps0) with "[Hpreds]" as "Hpreds".
    { unfold is_array. admit. }
    wp_pures. wp_bind (findNext _ _)%E. 
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
    iDestruct "Nodes" as "(Node_p & Nodes_rest)".
    iAaccIntro with "Node_p".
    { iIntros "Node_p". iModIntro. iFrame "Hpost Hpreds Hsuccs Hj".
      iNext; iExists M0, T0, s0. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    iIntros (m c) "(Node_p & %Mark_p0 & %Next_p0)".
    iModIntro. iSplitR "Hpreds Hsuccs Hpost Hj".
    { iNext. iExists M0, T0, s0. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    destruct c as [c |]; last first; wp_pures.
    { (* Contradiction case *) admit. }
    iAssert (∃ s : snapshot, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p c⌝)%I
      as "Hpc". { admit. }
    wp_apply traverse_i_spec; try done.
    iIntros (ores) "Hores".
    destruct ores as [[[p' c'] b]|]; last first.
    { wp_pures. iSpecialize ("Hpost" $! None ps0 ss0 true). iApply "Hpost".
      iFrame. done. }
    wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hpreds]").
    { iFrame "Hpreds". admit. }
    iIntros "!> Hpreds". wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hsuccs]").
    { iFrame "Hsuccs". admit. }
    iIntros "!> Hsuccs". wp_pures.
    iSpecialize ("Hpost" $! (Some (preds,succs,b)) _ _ b).
    iEval (rewrite /=) in "Hpost Hores". iApply "Hpost".
    iModIntro. iFrame "∗%". repeat (iSplitR; first by iPureIntro).
    iDestruct "Hores" as (s)"(Past_s & Hpc' & %Hi0)".
    iSplit. iIntros (j)"%Hj". destruct (decide (j = i)) as [-> | Hij].
    { iExists s. rewrite !list_lookup_total_insert. iFrame. all: admit. }
    iAssert (⌜i < j < L⌝)%I as "Hj'". { iPureIntro. lia. }
    iPoseProof ("Hj" with "Hj'") as (s')"(Past_s' & Htr)".
    iExists s'. rewrite !list_lookup_total_insert_ne; try done. iFrame.
    iIntros "%". subst i. rewrite !list_lookup_total_insert.
    iExists s. iFrame. iPureIntro. by apply Hi0. all: admit.
  Admitted.


  Lemma traverse_rec_spec N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght γ_sy t_id 
    t0 k preds succs ps0 ss0 (i: nat):
    main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
      thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
      {{{ is_array preds ps0 ∗ is_array succs ss0
          ∗ (∀ j, ⌜i < j < L⌝ → 
                  ∃ s, past_state γ_m t0 s 
                  ∗ ⌜traversal_inv s j k (ps0 !!! j) (ss0 !!! j)⌝) }}}
        traverse_rec #k #preds #succs #i
      {{{ (ps ss: list Node) (res: bool), 
            RET (#preds, #succs, #res);
            is_array preds ps ∗ is_array succs ss
          ∗ (∀ i, ⌜i < L⌝ → ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s i k (ps !!! i) (ss !!! i)⌝
                          ∗ ⌜i = 0 → let c := ss !!! 0 in
                                      if res then 
                                        k ∈ keyset (FI s c) ∧ k = Key s c
                                      else 
                                        k ∉ abs s⌝ ) }}}.
  Proof.
    iIntros "#HInv #Thd". iLöb as "IH" forall (i ps0 ss0). 
    iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & #HtrInv)".
    wp_lam. wp_pures. 
    wp_apply (traverse_pop_spec with "[] [] [Hpreds Hsuccs]"); try done.
    iFrame "∗#". iIntros (ores ps ss b)"Hores".
    destruct ores as [[[preds' succs'] res] |]; last first.
    { wp_pures. iDestruct "Hores" as "(Hpreds & Hsuccs)".
      iApply ("IH" with "[Hpreds Hsuccs]"). iFrame. iIntros (j)"%Hj".
      assert (j = L-1) as -> by lia. admit. }
    wp_pures. iDestruct "Hores" as "(%H' & %H'' & %H1' & H1'')". 
    rewrite /= in H' H'' H1'. subst preds' succs' b.  
    iDestruct "H1''" as "(Hpreds & Hsuccs & #Hj & Hi0)".
    destruct (bool_decide (#i = #0)) eqn: Hbool; wp_pures.
    - rewrite bool_decide_eq_true in Hbool. inversion Hbool. iModIntro.
      iApply "Hpost". iFrame "Hpreds Hsuccs". 
      iAssert (⌜i = 0⌝)%I as "Htr0". { iPureIntro; lia. }
      iDestruct ("Hi0" with "Htr0") as "H'".
      iIntros (j) "%Hj". destruct (decide (j = 0)) as [-> | Hj0].
      + iDestruct "H'" as (s)"(Hpast_s & #Htr & Hres)".
        iExists s; try iFrame "∗#". iIntros "_". iFrame.
      + iAssert (⌜i - 1 < j < L⌝)%I as "Hj'". { iPureIntro; lia. }
        iPoseProof ("Hj" with "Hj'") as (s)"(Past_s & Htr)".
        iExists s. iFrame "#". iIntros "%"; exfalso; lia.
    - iSpecialize ("IH" $! (i-1) ps ss).
      rewrite bool_decide_eq_false in Hbool.
      assert (i ≠ 0). { intros ->. apply Hbool. try done. }
      assert (Z.sub i 1 = (i-1)%nat) as -> by lia.
      iApply ("IH" with "[$Hpreds $Hsuccs $Hj]"). done.
  Admitted.


  Lemma traverse_spec N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght γ_sy t_id t0 k:
    main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
      thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
      {{{ True }}}
          traverse #hd #tl #k
      {{{ (preds succs: loc) (ps ss: list Node) (res: bool), 
            RET (#preds, #succs, #res);
            is_array preds ps ∗ is_array succs ss
          ∗ (∀ i, ⌜i < L⌝ → ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s i k (ps !!! i) (ss !!! i)⌝
                          ∗ ⌜i = 0 → let c := ss !!! 0 in
                                      if res then 
                                        k ∈ keyset (FI s c) ∧ k = Key s c
                                      else 
                                        k ∉ abs s⌝ ) }}}.
  Proof.  
    iIntros "#HInv #Thd". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures. wp_bind (AllocN _ _)%E. 
    iApply array_repeat. admit.
    iNext. iIntros (preds) "Hpreds".
    wp_pures. wp_bind (AllocN _ _)%E.
    iApply array_repeat. admit.
    iNext. iIntros (succs) "Hsuccs". wp_pures. 
    wp_apply (traverse_rec_spec with "[] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs". iIntros (j) "%Hj". 
    assert (j = L-1) as -> by lia. rewrite !lookup_total_replicate_2.
    all : try lia. admit.  
  Admitted.

End SKIPLIST1_SPEC_TRAVERSE.
  
  
