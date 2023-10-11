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

Module MAINTENANCEOP_INSERT.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS SKIPLIST1_UTIL.

  Parameter permute_levels_spec : ∀ (L: nat),
        {{{ True }}}
           permute_levels #L
        {{{ (perm: loc) (vs: list val) (xs: list nat), RET #perm;
              perm ↦∗ vs
            ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
            ∗ ⌜xs ≡ₚ seq 1 (L-1)⌝ }}}.

  Parameter getHeight_spec : ∀ (n: Node) (i: nat),
    ⊢ <<< ∀∀ h mark next k, node n h mark next k >>>
          getHeight #n @⊤
      <<< node n h mark next k, RET #h >>>.

  Parameter changeNext_spec : ∀ (n m m': Node) (i: nat),
    ⊢  <<< ∀∀ h mark next k, node n h mark next k ∗ ⌜i < h⌝ >>>
            changeNext #n #m #m' #i @⊤
      <<< ∃∃ (success: bool) next',
              node n h mark next' k
            ∗ (match success with true => ⌜next !! i = Some m 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := m']> next⌝
                                | false => ⌜(next !! i ≠ Some m ∨ 
                                              mark !!! i = true)
                                            ∧ next' = next⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>.

  Lemma maintenanceOp_insert_rec_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght k (n: Node) 
    preds succs (ps ss: list Node) perm vs xs (h i: nat):
    main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
      {{{   preds ↦∗ ((λ n0 : loc, #n0) <$> ps)
          ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss)
          ∗ perm ↦∗ vs
          ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
          ∗ ⌜xs ≡ₚ seq 1 (h-1)⌝ }}}
         maintenanceOp_insert_rec #i #k #h #perm #preds #succs #n
      {{{ (ps' ss': list Node),
          RET #();
            preds ↦∗ ((λ n0 : loc, #n0) <$> ps')
          ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss')
          ∗ perm ↦∗ vs }}}.
  Proof.
    iIntros "#HInv". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & Hperm & %Def_vs & %Perm_xs)".
    wp_lam. wp_pures. 
    destruct (bool_decide (Z.lt i (h - 1)%Z)) eqn: Hbool; wp_pures.
    - rewrite bool_decide_eq_true in Hbool.
      assert (is_Some (xs !! i)) as [idx Hidx].
      { assert (i < length xs) as H'. rewrite Perm_xs seq_length. lia.
        by rewrite lookup_lt_is_Some. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i) (vs) #idx
        with "[Hperm]"); try done.
      { rewrite Def_vs. rewrite list_lookup_fmap. rewrite Hidx.
        by simpl. }
      iIntros "Hperm". wp_pures.
      assert (is_Some (ps !! idx)) as [p Hp].
      { admit. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (idx) _ #p
        with "[Hpreds]"); try done.
      { by rewrite list_lookup_fmap Hp /=. }
      iIntros "Hpreds". wp_pures.
      assert (is_Some (ss !! idx)) as [c Hc].
      { admit. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (idx) _ #c
        with "[Hsuccs]"); try done.
      { by rewrite list_lookup_fmap Hc /=. }
      iIntros "Hsuccs". wp_pures.
      awp_apply changeNext_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAssert ((node p (Height s0 p) (Mark s0 p) (Next s0 p) (Key s0 p)) 
        ∗ ⌜idx < Height s0 p⌝)%I with "[Node_p]" as "Hpre".
      { admit. }
      iAaccIntro with "Hpre".
      { iIntros "(Node_p & _)". iModIntro. iFrame "Hpost Hperm Hpreds Hsuccs".
        iNext; iExists M0, T0, s0. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
      iIntros (success next')"(Node_p & Hif)".
      destruct success; last first.
      + iDestruct "Hif" as %[H' ->]. 
        iModIntro. iSplitR "Hpost Hperm Hpreds Hsuccs".
        { iNext. iExists M0, T0, s0. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
        wp_pures. admit.
      + admit.
  Admitted.

  Lemma maintenanceOp_insert_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght k (n:Node) preds succs 
    ps ss:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        {{{   preds ↦∗ ((λ n0 : loc, #n0) <$> ps)
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss) }}}
           maintenanceOp_insert #k #preds #succs #n
        {{{ (ps' ss': list Node),
            RET #();
              preds ↦∗ ((λ n0 : loc, #n0) <$> ps')
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss') }}}.
  Proof.
    iIntros "#HInv". iIntros (Φ) "!# (Hpreds & Hsuccs) Hpost".
    wp_lam. wp_pures. awp_apply getHeight_spec; try done.
    { admit. }
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜n ∈ FP s0⌝)%I as %FP_n0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) n); last by eauto.
    iDestruct "Nodes" as "(Node_n & Nodes_rest)".
    iAaccIntro with "Node_n".
    { iIntros "Node_n". iModIntro. iFrame.
      iNext; iExists M0, T0, s0. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) n); try done. iFrame. }
    iIntros "Node_n". iSplitR "Hpreds Hsuccs Hpost".
    { iModIntro. iNext; iExists M0, T0, s0. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) n); try done. iFrame. }  
    iModIntro. wp_pures. set h := Height s0 n. 
    wp_apply permute_levels_spec; try done.
    iIntros (perm vs xs)"(Hperm & %Def_vs & %Perm_xs)". wp_pures. 
    wp_apply (maintenanceOp_insert_rec_spec with "[] [$Hperm $Hpreds $Hsuccs]"); 
      try done.
    iIntros (ps' ss')"(Hpreds & Hsuccs & Hperm)". 
    iApply "Hpost". iFrame.
  Admitted.

End MAINTENANCEOP_INSERT.

