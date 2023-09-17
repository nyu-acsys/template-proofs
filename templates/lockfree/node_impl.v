From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Export skiplist_v1.

Section node_impl.

  Parameter L : nat. (* Maxlevels *)

  Definition compareKey : val :=
    λ: "n" "k",
      let: "nk" := ! "n" in
      if: "nk" < "k" then
        #0
      else if: "nk" = "k" then
        #1
      else
        #2.
  
  Definition findNext : val :=
    λ: "n" "i",
      let: "arr" := ! ("n" +ₗ #1) in
      let: "li" := ! ("arr" +ₗ "i") in
      let: "res" := ! "li" in
      "res".
  
  Definition markNode : val :=
    rec: "markN" "n" "i" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "li" := ! ("arr" +ₗ "i") in
      let: "res" := ! "li" in
      if: (Fst "res") then
        NONEV
      else
        let: "new" := ref (#true, Snd "res") in
        if: CAS ("arr" +ₗ "i") "li" "new" then
          (InjRV #())
        else
          "markN" "n" "i".
      
  Definition changeNext : val :=
    rec: "chN" "n" "m" "m'" "i" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "li" := ! ("arr" +ₗ "i") in
      let: "res" := ! "li" in
      if: (Fst "res") then
        NONEV
      else
        if: (Snd "res") = InjR "m" then
          let: "new" := ref (#false, InjR "m'") in
          if: CAS ("arr" +ₗ "i") "li" "new" then
            (InjRV #())
          else
            "chN" "n" "m" "m'" "i"
        else
          NONEV.

  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  (*
  Definition next_array_def (v: val) (mi: bool) (nxi: Node) : Prop :=
      match v with
        InjLV (#(LitLoc n')) => mi = false ∧ nxi = n'
      | InjRV (#(LitLoc n')) => mi = true ∧ nxi = n'
      | _ => False end.
  *)
  
  Definition node (n: Node) (mark: gmap nat bool) (next: gmap nat Node) 
    (k: nat) : iProp :=
    ∃ (arr: loc) (ls: list loc),
       n ↦□ #k
    ∗ (n +ₗ 1) ↦□ #arr
    ∗ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls)
    ∗ ⌜length ls = L⌝
    ∗ ∀ (l: loc) (i: nat), ⌜ls !! i = Some l⌝ -∗
        l ↦□ (#((mark !!! i): bool), match ((next !! i): option Node) with 
                                        None => NONEV 
                                      | Some ni => SOMEV #ni end).

  Lemma compareKey_spec (n: Node) (k': nat) :
    ⊢ <<< ∀∀ mark next k, node n mark next k >>>
           compareKey #n #k' @ ⊤
     <<< ∃∃ (res: nat),
            node n mark next k 
          ∗ ⌜if decide (res = 0) then k < k'
             else if decide (res = 1) then k = k'
             else k > k'⌝,
         RET #res >>>.
  Proof.
    iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (m0 nx0 k0) "[Node [_ Hclose]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    destruct (decide (k0 < k')).
    - iSpecialize ("Hclose" $! 0).
      iMod ("Hclose" with "[Harr]") as "AU".
      { iSplitL. iExists arr0, ls0. iFrame "∗%#".
        iPureIntro. destruct (decide (0 = 0)); try done. }
      iModIntro. wp_pures.
      destruct (bool_decide (Z.lt (Z.of_nat k0) (Z.of_nat k'))) eqn: H'; 
        wp_pures; try done.
      rewrite bool_decide_eq_false in H'. lia.
    - destruct (decide (k0 = k')) as [-> | Hk0].
      + iSpecialize ("Hclose" $! 1).
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL. iExists arr0, ls0. iFrame "∗%#".
          iPureIntro. destruct (decide (1 = 0)); try done. }
        iModIntro. wp_pures.
        destruct (bool_decide (Z.lt (Z.of_nat k') (Z.of_nat k'))) eqn: H'; 
          wp_pures; try done.
        rewrite bool_decide_eq_true in H'. lia.
        rewrite bool_decide_eq_false in H'.
        destruct (bool_decide (#(LitInt (Z.of_nat k')) = 
          #(LitInt (Z.of_nat k')))) eqn: H''; wp_pures; try done.
        rewrite bool_decide_eq_false in H''.
        exfalso; by apply H''.
      + iSpecialize ("Hclose" $! 2).
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL. iExists arr0, ls0. iFrame "∗%#".
          iPureIntro. destruct (decide (2 = 0)); try done.
          destruct (decide (2 = 1)); try done. lia. }
        iModIntro. wp_pures.
        destruct (bool_decide (Z.lt (Z.of_nat k0) (Z.of_nat k'))) eqn: H'; 
          wp_pures; try done.
        rewrite bool_decide_eq_true in H'. lia.
        rewrite bool_decide_eq_false in H'.
        destruct (bool_decide (#(LitInt (Z.of_nat k0)) = 
          #(LitInt (Z.of_nat k')))) eqn: H''; wp_pures; try done.
        rewrite bool_decide_eq_true in H''. inversion H''. lia.
  Qed.

  Lemma findNext_spec (n: Node) (i: nat) :
    ⊢ <<< ∀∀ mark next k, node n mark next k >>>
        findNext #n #i @⊤
     <<< ∃∃ (m: bool) (opt_n': option Node),
              node n mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !! i = opt_n'⌝,
              RET (match opt_n' with None => (#m, NONEV) 
                                    | Some n' => (#m, SOMEV #n') end) >>>.
  Proof.
    iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (m0 nx0 k0) "[Node [Hclose _]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (m1 nx1 k1) "[Node [_ Hclose]]".
    iDestruct "Node" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ li, ls1 !! i = Some li) as [li Def_li].
    { admit. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { admit. }
    iIntros "Harr".
    iDestruct ("Hls1" with "[%]") as "H'". apply Def_li.
    iSpecialize ("Hclose" $! (m1 !!! i) (nx1 !! i)).
    iMod ("Hclose" with "[Harr]") as "HΦ".
    { iSplitL. iExists arr0, ls1. iFrame "∗#%". by iPureIntro. }
    iModIntro. wp_pures. wp_load. wp_pures; destruct (nx1 !! i); try done.
  Admitted.
  
  Lemma markNode_spec (n: Node) (i: nat) :
    ⊢  <<< ∀∀ mark next k, node n mark next k >>>
            markNode #n #i @⊤
      <<< ∃∃ (success: bool) mark',
              node n mark' next k
            ∗ (match success with true => ⌜mark !!! i = false
                                            ∧ mark' = <[i := true]> mark⌝
                                | false => ⌜mark !!! i = true
                                            ∧ mark' = mark⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (m0 nx0 k0) "[Node [Hclose _]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (m1 nx1 k1) "[Node HAU]".
    iDestruct "Node" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ li, ls1 !! i = Some li) as [li Def_li].
    { admit. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { admit. }
    iIntros "Harr".
    iDestruct ("Hls1" with "[%]") as "H'". apply Def_li.
    destruct (decide (m1 !!! i = true)) as [Hmi | Hmi].
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false m1).
      iMod ("Hclose" with "[Harr]") as "HΦ".
      { iSplitL. iExists arr0, ls1. iFrame "∗#%".
        by iPureIntro. }
      iModIntro. wp_pures. wp_load. wp_pures.
      rewrite Hmi. wp_pures. done.
    - apply not_true_is_false in Hmi.
      iDestruct "HAU" as "[Hclose _]".
      iMod ("Hclose" with "[Harr]") as "AU".
      { iExists arr0, ls1. iFrame "∗#%". }
      iModIntro. wp_pures. wp_load. wp_pures.
      rewrite Hmi. wp_pures.
      wp_alloc li_new as "Hnew". wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iMod "AU" as (m2 nx2 k2) "[Node HAU]".
      iDestruct "Node" as (arr2 ls2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hls2)".
      iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
      inversion H'; subst arr2; clear H'.
      assert (∃ li', ls2 !! i = Some li') as [li' Def_li'].
      { admit. }
      destruct (decide (li' = li)) as [-> | Des_li].
      + wp_apply (wp_cmpxchg_suc_offset _ _ _ _ _ _ with "[Harr]"); 
          try done.
        { admit. }
        { left; try done. }
        iIntros "Harr".
        iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! true (<[i:=true]> m2)).
        iDestruct (mapsto_persist with "Hnew") as ">#Hnew'".
        iDestruct ("Hls2" with "[%]") as "H''". apply Def_li'.
        iDestruct (mapsto_agree with "H' H''") as "%H'". inversion H'.
        iMod ("Hclose" with "[Harr]") as "HΦ".
        { iSplitL. iExists arr0, (<[i:= li_new]> ls2). iFrame "#".
          iSplitL "Harr". admit. iSplitR. iPureIntro. admit.
          iIntros (l j)"%Hlj". destruct (decide (j = i)) as [-> | Hj].
          assert (<[i:=true]> m2 !!! i = true) as ->.
          by rewrite lookup_total_insert.
          rewrite list_lookup_insert in Hlj. inversion Hlj.
          rewrite H1; try done. admit.
          assert (<[i:=true]> m2 !!! j = m2 !!! j) as ->.
          by rewrite lookup_total_insert_ne.
          rewrite list_lookup_insert_ne in Hlj; try done.
          iClear "H' H''".
          iDestruct ("Hls2" with "[%]") as "H'". apply Hlj.
          done.
          by iPureIntro. }
        iModIntro. wp_pures. done.
      + wp_apply (wp_cmpxchg_fail_offset _ _ _ _ _ _ #li' with "[Harr]"); 
          try done.
        { admit. }
        { by intros [=->]. }
        { left; try done. }
        iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr]") as "AU".
        { iExists arr0, ls2. iFrame "∗#%". }
        iModIntro. wp_pures. by iApply "IH".
  Admitted.  
  
  Lemma changeNext_spec (n m m': Node) (i: nat) :
    ⊢  <<< ∀∀ mark next k, node n mark next k >>>
            changeNext #n #m #m' #i @⊤
      <<< ∃∃ (success: bool) next',
              node n mark next' k
            ∗ (match success with true => ⌜next !! i = Some m 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := m']> next⌝
                                | false => ⌜(next !! i ≠ Some m ∨ 
                                              mark !!! i = true)
                                            ∧ next' = next⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (m0 nx0 k0) "[Node [Hclose _]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (m1 nx1 k1) "[Node HAU]".
    iDestruct "Node" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ li, ls1 !! i = Some li) as [li Def_li].
    { admit. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { admit. }
    iIntros "Harr".
    iDestruct ("Hls1" with "[%]") as "H'". apply Def_li.
    destruct (decide (m1 !!! i = true)) as [Hmi | Hmi].
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false nx1).
      iMod ("Hclose" with "[Harr]") as "HΦ".
      { iSplitL. iExists arr0, ls1. iFrame "∗#%".
        iPureIntro; split; try done. by right. }
      iModIntro. wp_pures. wp_load. wp_pures.
      rewrite Hmi. wp_pures. done.
    - apply not_true_is_false in Hmi.
      destruct (nx1 !! i) as [nx1_i | ] eqn: Hnx1_i; last first.
      + iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! false nx1).
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL. iExists arr0, ls1. iFrame "∗#%". iPureIntro.
          split; try done. by left. }
        iModIntro. wp_pures. wp_load. wp_pures.
        rewrite Hmi. wp_pures. done.
      + destruct (decide (nx1_i = m)) as [-> | Hnx1_i']; last first.
        * iDestruct "HAU" as "[_ Hclose]".
          iSpecialize ("Hclose" $! false nx1).
          iMod ("Hclose" with "[Harr]") as "AU".
          { iSplitL. iExists arr0, ls1. iFrame "∗#%". iPureIntro.
            split; try done. left. by intros [=]. }
          iModIntro. wp_pures. wp_load. wp_pures.
          rewrite Hmi. wp_pures.
          destruct (bool_decide (InjRV #nx1_i = InjRV #m)) eqn: H'.
          rewrite bool_decide_eq_true in H'. inversion H'; try done.
          rewrite bool_decide_eq_false in H'.
          wp_pures. try done.
        * iDestruct "HAU" as "[Hclose _]".
          iMod ("Hclose" with "[Harr]") as "AU".
          { iExists arr0, ls1. iFrame "∗#%". }
          iModIntro. wp_pures. wp_load. wp_pures.
          rewrite Hmi. wp_pures.
          destruct (bool_decide (InjRV #m = InjRV #m)) eqn: H'; last first.
          { rewrite bool_decide_eq_false in H'. exfalso; apply H'; try done. }
          clear H'. wp_pures.
          wp_alloc li_new as "Hnew". wp_pures.
          wp_bind (CmpXchg _ _ _)%E.
          iMod "AU" as (m2 nx2 k2) "[Node HAU]".
          iDestruct "Node" as (arr2 ls2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hls2)".
          iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
          inversion H'; subst arr2; clear H'.
          assert (∃ li', ls2 !! i = Some li') as [li' Def_li'].
          { admit. }
          destruct (decide (li' = li)) as [-> | Des_li].
          -- wp_apply (wp_cmpxchg_suc_offset _ _ _ _ _ _ with "[Harr]"); 
               try done.
             { admit. }
             { left; try done. }
             iIntros "Harr". iDestruct "HAU" as "[_ Hclose]".
             iSpecialize ("Hclose" $! true (<[i:=m']> nx2)).
             iDestruct (mapsto_persist with "Hnew") as ">#Hnew'".
             iDestruct ("Hls2" with "[%]") as "H''". apply Def_li'.
             iDestruct (mapsto_agree with "H' H''") as "%H'". inversion H'.
             iMod ("Hclose" with "[Harr]") as "HΦ".
             { iSplitL. iExists arr0, (<[i:= li_new]> ls2). iFrame "#".
               iSplitL. admit. iSplit. iPureIntro. admit.
               iIntros (l j)"%Hlj". destruct (decide (j = i)) as [-> | Hj].
               rewrite list_lookup_insert in Hlj. inversion Hlj.
               assert (<[i:=m']> nx2 !! i = Some m') as ->. 
               by rewrite lookup_insert. by rewrite -H0. admit.
               rewrite list_lookup_insert_ne in Hlj; try done.
               assert (<[i:=m']> nx2 !! j = nx2 !! j) as ->.
               by rewrite lookup_insert_ne. 
               iClear "H' H''".
               iDestruct ("Hls2" with "[%]") as "H'". apply Hlj.
               done.
               iPureIntro. repeat split; try done.
               destruct (nx2 !! i); try done. by inversion H1. }
             iModIntro. wp_pures. done.
          -- wp_apply (wp_cmpxchg_fail_offset _ _ _ _ _ _ #li' with "[Harr]"); 
               try done.
             { admit. }
             { by intros [=->]. }
             { left; try done. }
             iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
             iMod ("Hclose" with "[Harr]") as "AU".
             { iExists arr0, ls2. iFrame "∗#%". }
             iModIntro. wp_pures. by iApply "IH".
  Admitted.

End node_impl.