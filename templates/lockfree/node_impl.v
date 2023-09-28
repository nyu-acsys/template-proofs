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
From flows Require Import skiplist_v1 bool_ra.

Section node_impl.

  Parameter L : nat. (* Maxlevels *)
  
  Definition createNode_rec : val :=
    rec: "cN" "i" "h" "arr" "succs" :=
      if: "h" ≤ "i" then
        #()
      else
        let: "si" := !("succs" +ₗ "i") in
        let: "li" := ref (#false, InjR "si") in 
        ("arr" +ₗ "i") <- "li";;
        "cN" ("i" + #1) "h" "arr" "succs".

  Definition createNode : val :=
    λ: "k" "h" "succs",
      let: "n" := AllocN #2%nat "k" in
      let: "arr" := AllocN "h" "n" in
      ("n" +ₗ #1) <- "arr";;
      createNode_rec #0%nat "h" "arr" "succs";;
      "n".

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

  Definition node (n: Node) (h: nat) (mark: gmap nat bool) (next: gmap nat Node) 
    (k: nat) : iProp :=
    ∃ (arr: loc) (ls: list loc),
       n ↦□ #k
    ∗ (n +ₗ 1) ↦□ #arr
    ∗ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls)
    ∗ ⌜length ls = h⌝
    ∗ ∀ (l: loc) (i: nat), ⌜ls !! i = Some l⌝ -∗
        l ↦□ (#((mark !!! i): bool), match ((next !! i): option Node) with 
                                        None => NONEV 
                                      | Some ni => SOMEV #ni end).

  Definition is_array (array : loc) (xs : list Node) : iProp :=
    let vs := (fun n => # (LitLoc n)) <$> xs
    in array ↦∗ vs.

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

  Lemma createNode_rec_spec (arr succs: loc) (ls ss: list Node) (h i: nat) :
  ⊢  {{{ is_array succs ss 
         ∗ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls)
         ∗ ⌜length ls = h⌝
         ∗ ⌜h <= length ss⌝
         ∗ ∀ (l: loc) (j: nat), 
           ⌜ls !! j = Some l⌝ -∗ ⌜j < i⌝ -∗
             l ↦□ (#false, match ((ss !! j): option Node) with 
                              None => NONEV | Some s => SOMEV #s end) }}}
           createNode_rec #i #h #arr #succs
      {{{ (ls': list Node),
          RET #();
              is_array succs ss
            ∗ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls')
            ∗ ⌜length ls' = h⌝
            ∗ ∀ (l: loc) (j: nat), 
              ⌜ls' !! j = Some l⌝ -∗ ⌜j < h⌝ -∗
                l ↦□ (#false, match ((ss !! j): option Node) with 
                                  None => NONEV | Some s => SOMEV #s end) }}}.
  Proof.
    iIntros (Φ) "!> Hpre Hpost". iLöb as "IH" forall (i ls).
    iDestruct "Hpre" as "(Hsuccs & Harr & %Len_ls & %Hss & Hls)".
    wp_lam. wp_pures. destruct (bool_decide (h ≤ i)%Z) eqn: Hi; wp_pures.
    - iApply ("Hpost" $! ls). iFrame. iSplitR; first by iPureIntro.
      iModIntro. iIntros (l j)"%Hlj %j_le_h".
      rewrite bool_decide_eq_true in Hi. iApply "Hls"; try done.
      iPureIntro; lia.
    - rewrite bool_decide_eq_false in Hi. 
      assert (∃ si, ss !! i = Some si) as [si Def_si].
      { apply lookup_lt_is_Some. lia. }  
      wp_apply (wp_load_offset _ _ _ _ _ _ #si with "[Hsuccs]"); try done.
      { by rewrite list_lookup_fmap Def_si /=. }
      iIntros "Hsuccs". wp_pures. wp_apply wp_alloc; try done.
      iIntros (l)"(Hl&_)". wp_pures. wp_bind (_ <- _)%E.
      iApply fupd_wp.
      iDestruct (mapsto_persist with "Hl") as ">Hl".
      iModIntro.
      iApply (wp_store_offset _ _ arr i with "Harr").
      { apply lookup_lt_is_Some_2. rewrite fmap_length Len_ls. lia. }
      iIntros "!> Harr". wp_pures.
      assert (Z.add i 1 = (i+1)%nat) as -> by lia. 
      iSpecialize ("IH" $! (i+1) (<[i:=l]>ls)).
      iApply ("IH" with "[Hsuccs Harr Hl Hls]"); try done.
      assert ((λ l0 : loc, #l0) <$> <[i:=l]> ls = 
                  <[i:=#l]> ((λ l0 : loc, #l0) <$> ls)) as ->.
      { apply list_eq. intros i'. 
        destruct (decide (i' = i)) as [-> | Hi'].
        rewrite list_lookup_fmap !list_lookup_insert /=. done.
        rewrite Len_ls; lia. rewrite fmap_length Len_ls. lia.
        rewrite list_lookup_fmap !list_lookup_insert_ne /=; try done.
        by rewrite list_lookup_fmap. }
      iFrame "Hsuccs Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
      iSplitR. by iPureIntro.
      iIntros (l' j)"%Hlj %Hj". destruct (decide (j = i)) as [-> | Hij].
      { rewrite list_lookup_insert in Hlj. inversion Hlj. subst l'.
        rewrite Def_si. iFrame. rewrite Len_ls; lia. }
      iApply "Hls". iPureIntro. rewrite list_lookup_insert_ne in Hlj; try done.
      iPureIntro; lia.
  Qed.

  Lemma createNode_spec (succs: loc) ss (h k: nat) :
  ⊢  {{{ is_array succs ss ∗ ⌜0 < h ≤ length ss⌝ }}}
           createNode #k #h #succs
        {{{ (n: Node) mark next,
            RET #n;
              is_array succs ss
            ∗ node n h mark next k  
            ∗ (⌜∀ i, i < h → mark !! i = Some false⌝)
            ∗ (⌜∀ i, i < h → next !! i = Some (ss !!! i)⌝) }}}.
  Proof.
    iIntros (Φ) "!> (Hsuccs&%Hh) Hpost". wp_lam. wp_pures.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try done.
    iModIntro. iIntros (n)"(Hn&_)". wp_pures.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try done. lia.
    iModIntro. iIntros (arr)"(Harr&_)". wp_pures.
    assert (Z.to_nat h = h) as -> by lia.
    assert (Z.to_nat 2%nat = 2) as -> by lia.
    wp_bind (_ <- _)%E.
    iApply (wp_store_offset _ _ n 1 with "Hn").
    { apply lookup_lt_is_Some_2. rewrite replicate_length. lia. }
    iIntros "!> Hn". wp_pures.
    wp_apply (createNode_rec_spec _ _ _ _ h _ with "[Hsuccs Harr]").
    { assert (replicate h #n = (λ l : loc, #l) <$> (replicate h n)) as ->.
      { apply list_eq. intros i'. rewrite list_lookup_fmap. 
        destruct (decide (i' < h)) as [Hi | Hi].
        - rewrite !lookup_replicate_2; try done.
        - apply not_lt in Hi. Search replicate lookup. 
          assert (h ≤ i') as H' by lia. Search replicate lookup.
          assert (H'' := H').
          apply (lookup_replicate_None h #n i') in H'.
          apply (lookup_replicate_None h n i') in H''.
          rewrite H' H'' /=. done. }
      iFrame "Hsuccs Harr".
      iSplit. { iPureIntro. by rewrite replicate_length. }
      iSplitR. iPureIntro; lia.
      iIntros (l j)"%Hlj %Hj". exfalso; lia. }
    iIntros (ls) "(Hsuccs & Harr & %Length_ls & Hls)".
    assert (∃ (m: gmap nat bool), ∀ i, i < h → m !! i = Some false) as 
      [mark Def_mark].
    { Fixpoint f n (res: gmap nat bool) := 
        match n with S n' => f n' (<[n' := false]> res) | 0 => res end.
      set m := f h ∅.
      assert (∀ n res i, (i < n → f n res !! i = Some false) ∧ 
                    (¬ i < n → f n res !! i = res !! i)) as H'.
      { clear. induction n.
        - intros res i; split; first by lia. intros H'; by simpl.
        - intros res i. pose proof IHn (<[n:=false]> res) i as H''.
          split; intros Hi; simpl.
          + destruct (decide (i = n)) as [-> | Hin].
            { assert (¬ n < n) as H' by lia. 
              destruct H'' as [_ H'']. pose proof H'' H' as H''.
              rewrite H'' lookup_insert. done. }
            assert (i < n) as H'%H'' by lia. by rewrite H'.
          + assert (¬ i < n) as H'%H'' by lia. rewrite H'.
            rewrite lookup_insert_ne; try (done || lia). }
      exists m. apply  H'. }
    assert (∃ (nx: gmap nat Node), ∀ i, i < h → nx !! i = Some (ss !!! i)) as 
      [next Def_next].
    { Fixpoint f' (l: list Node) n (res: gmap nat Node) := 
        match n with S n' => f' l n' (<[n':= l !!! n']> res) | 0 => res end.
      set nx := f' ss h ∅.
      assert (∀ n res i, (i < n → f' ss n res !! i = Some (ss !!! i)) ∧ 
                    (¬ i < n → f' ss n res !! i = res !! i)) as H'.
      { clear. induction n.
        - intros res i; split; first by lia. intros H'; by simpl.
        - intros res i. pose proof IHn (<[n:=(ss !!! n)]> res) i as H''.
          split; intros Hi; simpl.
          + destruct (decide (i = n)) as [-> | Hin].
            { assert (¬ n < n) as H' by lia. 
              destruct H'' as [_ H'']. pose proof H'' H' as H''.
              rewrite H'' lookup_insert. done. }
            assert (i < n) as H'%H'' by lia. by rewrite H'.
          + assert (¬ i < n) as H'%H'' by lia. rewrite H'.
            rewrite lookup_insert_ne; try (done || lia). }
      exists nx. apply H'. }
    wp_pures. iApply ("Hpost" $! n mark next).
    iFrame "Hsuccs". iSplitL; last first.
    { iPureIntro; try done. }  
    iExists arr, ls.
    assert (<[1:=#arr]> (replicate 2 #k) = #k :: #arr :: []) as ->.
    { rewrite /replicate /=. done. }
    iAssert (n ↦ #k ∗ (n +ₗ 1) ↦ #arr)%I with "[Hn]" as "(Hk & Hn)".
    { rewrite /array /big_opL. iDestruct "Hn" as "(Hn1 & Hn2 & _)".
      assert (n +ₗ 0%nat = n) as ->.
      { rewrite /loc_add /=. assert (Z.add (loc_car n) 0%nat = loc_car n) as ->.
        lia. destruct n; try done. } iFrame. }
    iDestruct (mapsto_persist with "Hk") as ">Hk".
    iDestruct (mapsto_persist with "Hn") as ">Hn".
    iFrame "Hn Hk Harr". iSplitR. by iPureIntro.
    iModIntro. iIntros (l j)"%Hlj".
    assert (j < h) as j_lt_h. { by rewrite -Length_ls -lookup_lt_is_Some Hlj /=. }
    rewrite lookup_total_alt Def_mark /=; try done. 
    rewrite Def_next; try done. iSpecialize ("Hls" $! l j).
    iDestruct ("Hls" with "[%] [%]") as "H'"; try done.
    assert (is_Some(ss !! j)) as [sj Def_sj].
    { rewrite lookup_lt_is_Some. lia. }
    rewrite Def_sj. apply lookup_total_correct in Def_sj.
    rewrite -Def_sj. admit.
  Admitted.

  Lemma compareKey_spec (n: Node) (k': nat) :
    ⊢ <<< ∀∀ h mark next k, node n h mark next k >>>
           compareKey #n #k' @ ⊤
     <<< ∃∃ (res: nat),
            node n h mark next k 
          ∗ ⌜if decide (res = 0) then k < k'
             else if decide (res = 1) then k = k'
             else k > k'⌝,
         RET #res >>>.
  Proof.
    iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[Node [_ Hclose]]".
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
    ⊢ <<< ∀∀ h mark next k, node n h mark next k ∗ ⌜i < h⌝ >>>
          findNext #n #i @⊤
      <<< ∃∃ (m: bool) (opt_n': option Node),
              node n h mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !! i = opt_n'⌝,
              RET (match opt_n' with None => (#m, NONEV) 
                                    | Some n' => (#m, SOMEV #n') end) >>>.
  Proof.
    iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[(Node&%Hi0) [Hclose _]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) [_ Hclose]]".
    iDestruct "Node" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ li, ls1 !! i = Some li) as [li Def_li].
    { apply lookup_lt_is_Some. by rewrite Len_vs1. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { by rewrite list_lookup_fmap Def_li /=. }
    iIntros "Harr".
    iDestruct ("Hls1" with "[%]") as "H'". apply Def_li.
    iSpecialize ("Hclose" $! (m1 !!! i) (nx1 !! i)).
    iMod ("Hclose" with "[Harr]") as "HΦ".
    { iSplitL. iExists arr0, ls1. iFrame "∗#%". by iPureIntro. }
    iModIntro. wp_pures. wp_load. wp_pures; destruct (nx1 !! i); try done.
  Qed.
  
  Lemma markNode_spec (n: Node) (i: nat) :
    ⊢  <<< ∀∀ h mark next k, node n h mark next k ∗ ⌜i < h⌝ >>>
            markNode #n #i @⊤
      <<< ∃∃ (success: bool) mark',
              node n h mark' next k
            ∗ (match success with true => ⌜mark !!! i = false
                                            ∧ mark' = <[i := true]> mark⌝
                                | false => ⌜mark !!! i = true
                                            ∧ mark' = mark⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[(Node&%Hi0) [Hclose _]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) HAU]".
    iDestruct "Node" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ li, ls1 !! i = Some li) as [li Def_li].
    { apply lookup_lt_is_Some. by rewrite Len_vs1. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { by rewrite list_lookup_fmap Def_li /=. }
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
      { iFrame "%". iExists arr0, ls1. iFrame "∗#%". }
      iModIntro. wp_pures. wp_load. wp_pures.
      rewrite Hmi. wp_pures.
      wp_alloc li_new as "Hnew". wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
      iDestruct "Node" as (arr2 ls2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hls2)".
      iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
      inversion H'; subst arr2; clear H'.
      assert (∃ li', ls2 !! i = Some li') as [li' Def_li'].
      { apply lookup_lt_is_Some. by rewrite Len_vs2.  }
      destruct (decide (li' = li)) as [-> | Des_li].
      + wp_apply (wp_cmpxchg_suc_offset _ _ _ _ _ _ with "[Harr]"); 
          try done.
        { by rewrite list_lookup_fmap Def_li' /=. }
        { left; try done. }
        iIntros "Harr".
        iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! true (<[i:=true]> m2)).
        iDestruct (mapsto_persist with "Hnew") as ">#Hnew'".
        iDestruct ("Hls2" with "[%]") as "H''". apply Def_li'.
        iDestruct (mapsto_agree with "H' H''") as "%H'". inversion H'.
        iMod ("Hclose" with "[Harr]") as "HΦ".
        { iSplitL. iExists arr0, (<[i:= li_new]> ls2). iFrame "#".
          iSplitL "Harr". 
          assert (((λ l : loc, #l) <$> <[i:=li_new]> ls2) = 
            <[i:=#li_new]> ((λ l : loc, #l) <$> ls2)) as ->.
          { apply list_eq. intros i'. destruct (decide (i' = i)) as [-> | Hi'].
            rewrite list_lookup_fmap !list_lookup_insert /=. done.
            by rewrite fmap_length Len_vs2. by rewrite Len_vs2. 
            rewrite list_lookup_fmap !list_lookup_insert_ne /=; try done.
            by rewrite list_lookup_fmap. }
          iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
          iIntros (l j)"%Hlj". destruct (decide (j = i)) as [-> | Hj].
          assert (<[i:=true]> m2 !!! i = true) as ->.
          by rewrite lookup_total_insert.
          rewrite list_lookup_insert in Hlj. inversion Hlj.
          rewrite H1; try done. by rewrite Len_vs2.
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
        { by rewrite list_lookup_fmap Def_li' /=. }
        { by intros [=->]. }
        { left; try done. }
        iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, ls2. iFrame "∗#%". }
        iModIntro. wp_pures. by iApply "IH".
  Qed.  
  
  Lemma changeNext_spec (n m m': Node) (i: nat) :
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
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[(Node&%Hi0) [Hclose _]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iSplitL; last by iPureIntro. iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) HAU]".
    iDestruct "Node" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ li, ls1 !! i = Some li) as [li Def_li].
    { apply lookup_lt_is_Some. by rewrite Len_vs1. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { by rewrite list_lookup_fmap Def_li /=. }
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
          { iSplitL; last by iPureIntro. iExists arr0, ls1. iFrame "∗#%". }
          iModIntro. wp_pures. wp_load. wp_pures.
          rewrite Hmi. wp_pures.
          destruct (bool_decide (InjRV #m = InjRV #m)) eqn: H'; last first.
          { rewrite bool_decide_eq_false in H'. exfalso; apply H'; try done. }
          clear H'. wp_pures.
          wp_alloc li_new as "Hnew". wp_pures.
          wp_bind (CmpXchg _ _ _)%E.
          iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
          iDestruct "Node" as (arr2 ls2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hls2)".
          iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
          inversion H'; subst arr2; clear H'.
          assert (∃ li', ls2 !! i = Some li') as [li' Def_li'].
          { apply lookup_lt_is_Some. by rewrite Len_vs2. }
          destruct (decide (li' = li)) as [-> | Des_li].
          -- wp_apply (wp_cmpxchg_suc_offset _ _ _ _ _ _ with "[Harr]"); 
               try done.
             { by rewrite list_lookup_fmap Def_li' /=. }
             { left; try done. }
             iIntros "Harr". iDestruct "HAU" as "[_ Hclose]".
             iSpecialize ("Hclose" $! true (<[i:=m']> nx2)).
             iDestruct (mapsto_persist with "Hnew") as ">#Hnew'".
             iDestruct ("Hls2" with "[%]") as "H''". apply Def_li'.
             iDestruct (mapsto_agree with "H' H''") as "%H'". inversion H'.
             iMod ("Hclose" with "[Harr]") as "HΦ".
             { iSplitL. iExists arr0, (<[i:= li_new]> ls2). iFrame "#".
               iSplitL. 
               assert (((λ l : loc, #l) <$> <[i:=li_new]> ls2) = 
                          <[i:=#li_new]> ((λ l : loc, #l) <$> ls2)) as ->.
               { apply list_eq. intros i'. 
                 destruct (decide (i' = i)) as [-> | Hi'].
                 rewrite list_lookup_fmap !list_lookup_insert /=. done.
                 by rewrite fmap_length Len_vs2. by rewrite Len_vs2. 
                 rewrite list_lookup_fmap !list_lookup_insert_ne /=; try done.
                 by rewrite list_lookup_fmap. }
               iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
               iIntros (l j)"%Hlj". destruct (decide (j = i)) as [-> | Hj].
               rewrite list_lookup_insert in Hlj. inversion Hlj.
               assert (<[i:=m']> nx2 !! i = Some m') as ->. 
               by rewrite lookup_insert. by rewrite -H0. by rewrite Len_vs2. 
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
             {  by rewrite list_lookup_fmap Def_li' /=. }
             { by intros [=->]. }
             { left; try done. }
             iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
             iMod ("Hclose" with "[Harr]") as "AU".
             { iSplitL; last by iPureIntro. iExists arr0, ls2. iFrame "∗#%". }
             iModIntro. wp_pures. by iApply "IH".
  Qed.

End node_impl.