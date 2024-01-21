From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
From flows Require Export flows array_util node_module misc_ra gset_seq.
Set Default Proof Using "All".

(* Node Implementation based on encoding mark bit as a data type *)

Module IMPL1 : NODE_IMPL.

  Parameter L : nat. (* Maximum Height *)
  Parameter W : nat. (* Keyspace *)
  Parameter W_gt_0 : 0 < W.
  Parameter L_gt_1 : 1 < L.
  

  Definition MarkT := gmap nat bool.
  Definition NextT := gmap nat Node.
  Definition l0 := {| loc_car := 0 |}.

  Definition createTail_rec : val :=
    rec: "cT" "i" "arr" :=
      if: #L ≤ "i" then
        #()
      else
        let: "li" := ref (#false, #l0) in
        ("arr" +ₗ "i") <- "li";;
        "cT" ("i" + #1) "arr".

  Definition createTail : val :=
    λ: <>,
      let: "tl" := AllocN #2%nat (#W, #L) in
      let: "arr" := AllocN #L "tl" in
      ("tl" +ₗ #1) <- "arr";;
      createTail_rec #0%nat "arr";;
      "tl".

  Definition createHead_rec : val :=
    rec: "cH" "i" "arr" "tl" :=
      if: #L ≤ "i" then
        #()
      else
        let: "li" := ref (#false, "tl") in
        ("arr" +ₗ "i") <- "li";;
        "cH" ("i" + #1) "arr" "tl".

  Definition createHead : val :=
    λ: "tl",
      let: "hd" := AllocN #2%nat (#0, #L) in
      let: "arr" := AllocN #L "tl" in
      ("hd" +ₗ #1) <- "arr";;
      createHead_rec #0%nat "arr" "tl";;
      "hd".
  
  Definition createNode_rec : val :=
    rec: "cN" "i" "h" "arr" "succs" :=
      if: "h" ≤ "i" then
        #()
      else
        let: "si" := !("succs" +ₗ "i") in
        let: "li" := ref (#false, "si") in 
        ("arr" +ₗ "i") <- "li";;
        "cN" ("i" + #1) "h" "arr" "succs".

  Definition createNode : val :=
    λ: "k" "h" "succs",
      let: "n" := AllocN #2%nat ("k", "h") in
      let: "arr" := AllocN "h" "n" in
      ("n" +ₗ #1) <- "arr";;
      createNode_rec #0%nat "h" "arr" "succs";;
      "n".

  Definition getKey : val :=
    λ: "n",
      Fst (! "n").

  Definition getHeight : val :=
    λ: "n",
      Snd (! "n").
  
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

  Definition markNode' : val := 
    rec: "markN" "n" "p" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "li" := ! ("arr" +ₗ #0%nat) in
      let: "res" := ! "li" in
      if: (Fst "res") then
        NONEV
      else
        let: "new" := ref (#true, Snd "res") in
        let: "res" := Resolve (CmpXchg ("arr" +ₗ #0%nat) "li" "new") "p" #() in
        if: Snd "res" then
          (InjRV #())
        else
          "markN" "n" "p".
          
  Definition changeNext : val :=
    rec: "chN" "n" "m" "m'" "i" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "li" := ! ("arr" +ₗ "i") in
      let: "res" := ! "li" in
      if: (Fst "res") then
        NONEV
      else
        if: (Snd "res") = "m" then
          let: "new" := ref (#false, "m'") in
          if: CAS ("arr" +ₗ "i") "li" "new" then
            (InjRV #())
          else
            "chN" "n" "m" "m'" "i"
        else
          NONEV.

  Definition changeNext' : val :=
    rec: "chN" "n" "m" "m'" "p" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "li" := ! ("arr" +ₗ #0%nat) in
      let: "res" := ! "li" in
      if: (Fst "res") then
        NONEV
      else
        if: (Snd "res") = "m" then
          let: "new" := ref (#false, "m'") in
          let: "res" := Resolve (CmpXchg ("arr" +ₗ #0%nat) "li" "new") "p" #() in
          if: Snd "res" then
            (InjRV #())
          else
            "chN" "n" "m" "m'" "p"
        else
          NONEV.

  (* Context `{!heapGS Σ}. *)
  (* Notation iProp := (iProp Σ). *)

  Definition node Σ (Hg1 : heapGS Σ) (n: Node) (h: nat) (mark: MarkT) (next: NextT) 
    (k: nat) : iProp Σ :=
    ∃ (arr: loc) (ls: list loc),
       n ↦□ (#k, #h)
    ∗ (n +ₗ 1) ↦□ #arr
    ∗ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls)
    ∗ ⌜length ls = h ∧ 0 < h⌝
    ∗ ∀ (l: loc) (i: nat), ⌜ls !! i = Some l⌝ -∗
        l ↦□ (#((mark !!! i): bool), #((next !!! i: loc))).
  
  Global Instance node_timeless_proof : ∀ Σ Hg1 n h mark next k, 
        Timeless (node Σ Hg1 n h mark next k).
  Proof. try apply _. Qed.

  Lemma node_sep_star Σ Hg1 n h mark next k h' mark' next' k' :
    node Σ Hg1 n h mark next k -∗ node Σ Hg1 n h' mark' next' k' -∗ False.
  Proof.
    iIntros "Hn0 Hn1". 
    iDestruct "Hn0" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr0 & %Len_vs0 & #Hls0)".
    iDestruct "Hn1" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr1 & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "Hn0 Hn1") as "%H'". inversion H'. clear H'.
    iDestruct (mapsto_agree with "Hk0 Hk1") as "%H'". inversion H'. clear H'.
    assert (∃ l0 ls0', ls0 = l0 :: ls0') as [l0 [ls0' Def_ls0]].
    { destruct ls0. rewrite /= in Len_vs0. lia. by exists l, ls0. }
    rewrite Def_ls0 array_cons. iDestruct "Harr0" as "(Harr0 & Harr0')". 
    assert (∃ l1 ls1', ls1 = l1 :: ls1') as [l1 [ls1' Def_ls1]].
    { destruct ls1. rewrite /= in Len_vs1. lia. by exists l, ls1. }
    rewrite Def_ls1 array_cons. iDestruct "Harr1" as "(Harr1 & Harr1')".
    iCombine "Harr0 Harr1" as "H'". iPoseProof (mapsto_valid with "H'") as "%".
    exfalso; try done.
  Qed.



  Lemma createTail_rec_spec Σ (Hg1 : heapGS Σ) (arr: loc) (ls : list Node) (i: nat) :
  ⊢  {{{ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls)
         ∗ ⌜length ls = L⌝
         ∗ ∀ (l: loc) (j: nat), 
           ⌜ls !! j = Some l⌝ -∗ ⌜j < i⌝ -∗
             l ↦□ (#false, #l0) }}}
           createTail_rec #i #arr
      {{{ (ls': list Node),
          RET #();
              arr ↦∗ ((fun l => # (LitLoc l)) <$> ls')
            ∗ ⌜length ls' = L⌝
            ∗ ∀ (l: loc) (j: nat), 
              ⌜ls' !! j = Some l⌝ -∗ ⌜j < L⌝ -∗
                l ↦□ (#false, #l0) }}}.
  Proof.
    iIntros (Φ) "!> Hpre Hpost". iLöb as "IH" forall (i ls).
    iDestruct "Hpre" as "(Harr & %Len_ls & Hls)".
    wp_lam. wp_pures. destruct (bool_decide (L ≤ i)%Z) eqn: Hi; wp_pures.
    - iApply ("Hpost" $! ls). iFrame. iSplitR; first by iPureIntro.
      iModIntro. iIntros (l j)"%Hlj %j_le_L".
      rewrite bool_decide_eq_true in Hi. iApply "Hls"; try done.
      iPureIntro; lia.
    - rewrite bool_decide_eq_false in Hi.
      wp_apply wp_alloc; try done.
      iIntros (l)"(Hl&_)". wp_pures. wp_bind (_ <- _)%E.
      iApply fupd_wp. iDestruct (mapsto_persist with "Hl") as ">#Hl". iModIntro.
      iApply (wp_store_offset _ _ arr i with "Harr").
      { apply lookup_lt_is_Some_2. rewrite fmap_length Len_ls. lia. }
      iIntros "!> Harr". wp_pures.
      assert (Z.add i 1 = (i+1)%nat) as -> by lia. 
      iSpecialize ("IH" $! (i+1) (<[i:=l]>ls)).
      iApply ("IH" with "[Harr Hls]"); try done.
      assert ((λ l0 : loc, #l0) <$> <[i:=l]> ls = 
                  <[i:=#l]> ((λ l0 : loc, #l0) <$> ls)) as ->.
      { apply list_eq. intros i'. 
        destruct (decide (i' = i)) as [-> | Hi'].
        rewrite list_lookup_fmap !list_lookup_insert /=. done.
        rewrite Len_ls; lia. rewrite fmap_length Len_ls. lia.
        rewrite list_lookup_fmap !list_lookup_insert_ne /=; try done.
        by rewrite list_lookup_fmap. }
      iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
      iIntros (l' j)"%Hlj %Hj". destruct (decide (j = i)) as [-> | Hij].
      { rewrite list_lookup_insert in Hlj. inversion Hlj. subst l'.
        iFrame "#". rewrite Len_ls; lia. }
      iApply "Hls". iPureIntro. rewrite list_lookup_insert_ne in Hlj; try done.
      iPureIntro; lia.
  Qed.

  Lemma createTail_spec Σ Hg1 :
  ⊢  {{{ True }}}
        createTail #()
      {{{ (tl: Node) mark,
        RET #tl;
          node Σ Hg1 tl L mark ∅ W
        ∗ ⌜dom mark = gset_seq 0 (L-1)⌝
        ∗ (⌜∀ i, i < L → mark !! i = Some false⌝) }}}.
  Proof.
    iIntros (Φ) "!> _ Hpost". wp_lam. wp_pures.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try done.
    iModIntro. iIntros (tl)"(Htl&_)". wp_pures.
    assert (L > 1) as HL. apply L_gt_1.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try (done || lia).
    iNext. iIntros (arr)"(Harr&_)". wp_pures.
    assert (Z.to_nat L = L) as -> by lia.
    assert (Z.to_nat 2%nat = 2) as -> by lia.
    wp_bind (_ <- _)%E.
    iApply (wp_store_offset _ _ tl 1 with "Htl").
    { apply lookup_lt_is_Some_2. rewrite replicate_length. lia. }
    iIntros "!> Htl". wp_pures.
    wp_apply (createTail_rec_spec with "[Harr]").
    { assert (replicate L #tl = (λ l : loc, #l) <$> (replicate L tl)) as ->.
      { apply list_eq. intros i'. rewrite list_lookup_fmap. 
        destruct (decide (i' < L)) as [Hi | Hi].
        - rewrite !lookup_replicate_2; try done.
        - apply not_lt in Hi. 
          assert (L ≤ i') as H' by lia. assert (H'' := H').
          apply (lookup_replicate_None L #tl i') in H'.
          apply (lookup_replicate_None L tl i') in H''.
          rewrite H' H'' /=. done. }
      iFrame "Harr".
      iSplit. { iPureIntro. by rewrite replicate_length. }
      iIntros (l j)"%Hlj %Hj". exfalso; lia. }
    iIntros (ls) "(Harr & %Length_ls & Hls)".
    assert (∃ (m: gmap nat bool), (∀ i, i < L → m !! i = Some false) 
      ∧ dom m = gset_seq 0 (L-1)) as 
      [mark [Def_mark Dom_mark]].
    { apply mark_map. lia. }
    wp_pures. 
    assert (<[1:=#arr]> (replicate 2 (#W, #L)%V) = (#W, #L)%V :: #arr :: []) as ->.
    { rewrite /replicate /=. done. }
    iAssert (tl ↦ (#W, #L)%V ∗ (tl +ₗ 1) ↦ #arr)%I with "[Htl]" as "(Hk & Htl)".
    { rewrite /array /big_opL. iDestruct "Htl" as "(Ht1 & Ht2 & _)".
      assert (tl +ₗ 0%nat = tl) as ->.
      { rewrite /Loc.add /=. assert (Z.add (loc_car tl) 0%nat = loc_car tl) as ->.
        lia. destruct tl; try done. } iFrame. }
    iDestruct (mapsto_persist with "Hk") as ">Hk".
    iDestruct (mapsto_persist with "Htl") as ">Htl".
    iAssert (node Σ Hg1 tl L mark ∅ W) with "[- Hpost]" as "Node".
    { iExists arr, ls. iFrame "Htl Hk Harr". iSplitR. iPureIntro. 
      split; try (done || lia). iIntros (l j)"%Hlj".
      assert (j < L) as j_lt_L. { by rewrite -Length_ls -lookup_lt_is_Some Hlj /=. }
      rewrite lookup_total_alt Def_mark /=; try done.
      rewrite lookup_total_empty. iApply "Hls". iPureIntro. apply Hlj.
      by iPureIntro. }
    iApply ("Hpost" $! tl mark). iModIntro. iFrame. iPureIntro. split; try done.
  Qed.

  Lemma createHead_rec_spec Σ (Hg1 : heapGS Σ) (tl: Node) (arr: loc) (ls: list Node) 
    (i: nat) :
  ⊢  {{{ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls)
         ∗ ⌜length ls = L⌝
         ∗ ∀ (l: loc) (j: nat), 
           ⌜ls !! j = Some l⌝ -∗ ⌜j < i⌝ -∗
             l ↦□ (#false, #tl) }}}
           createHead_rec #i #arr #tl
      {{{ (ls': list Node),
          RET #();
              arr ↦∗ ((fun l => # (LitLoc l)) <$> ls')
            ∗ ⌜length ls' = L⌝
            ∗ ∀ (l: loc) (j: nat), 
              ⌜ls' !! j = Some l⌝ -∗ ⌜j < L⌝ -∗
                l ↦□ (#false, #tl) }}}.
  Proof.
    iIntros (Φ) "!> Hpre Hpost". iLöb as "IH" forall (i ls).
    iDestruct "Hpre" as "(Harr & %Len_ls & Hls)".
    wp_lam. wp_pures. destruct (bool_decide (L ≤ i)%Z) eqn: Hi; wp_pures.
    - iApply ("Hpost" $! ls). iFrame. iSplitR; first by iPureIntro.
      iModIntro. iIntros (l j)"%Hlj %j_le_L".
      rewrite bool_decide_eq_true in Hi. iApply "Hls"; try done.
      iPureIntro; lia.
    - rewrite bool_decide_eq_false in Hi.
      wp_apply wp_alloc; try done.
      iIntros (l)"(Hl&_)". wp_pures. wp_bind (_ <- _)%E.
      iApply fupd_wp. iDestruct (mapsto_persist with "Hl") as ">#Hl". iModIntro.
      iApply (wp_store_offset _ _ arr i with "Harr").
      { apply lookup_lt_is_Some_2. rewrite fmap_length Len_ls. lia. }
      iIntros "!> Harr". wp_pures.
      assert (Z.add i 1 = (i+1)%nat) as -> by lia. 
      iSpecialize ("IH" $! (i+1) (<[i:=l]>ls)).
      iApply ("IH" with "[Harr Hls]"); try done.
      assert ((λ l0 : loc, #l0) <$> <[i:=l]> ls = 
                  <[i:=#l]> ((λ l0 : loc, #l0) <$> ls)) as ->.
      { apply list_eq. intros i'. 
        destruct (decide (i' = i)) as [-> | Hi'].
        rewrite list_lookup_fmap !list_lookup_insert /=. done.
        rewrite Len_ls; lia. rewrite fmap_length Len_ls. lia.
        rewrite list_lookup_fmap !list_lookup_insert_ne /=; try done.
        by rewrite list_lookup_fmap. }
      iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
      iIntros (l' j)"%Hlj %Hj". destruct (decide (j = i)) as [-> | Hij].
      { rewrite list_lookup_insert in Hlj. inversion Hlj. subst l'.
        iFrame "#". rewrite Len_ls; lia. }
      iApply "Hls". iPureIntro. rewrite list_lookup_insert_ne in Hlj; try done.
      iPureIntro; lia.
  Qed.

  Lemma createHead_spec Σ Hg1 (tl : Node) :
  ⊢  {{{ True }}}
        createHead #tl
      {{{ (hd: Node) mark next,
          RET #hd;
            node Σ Hg1 hd L mark next 0
          ∗ ⌜dom mark = gset_seq 0 (L-1)⌝ ∗ ⌜dom next = gset_seq 0 (L-1)⌝
          ∗ (⌜∀ i, i < L → mark !! i = Some false⌝)
          ∗ (⌜∀ i, i < L → next !! i = Some tl⌝) }}}.
  Proof.
    iIntros (Φ) "!> _ Hpost". wp_lam. wp_pures.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try done.
    iModIntro. iIntros (hd)"(Hd&_)". wp_pures.
    assert (L > 1) as HL. apply L_gt_1.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try (done || lia).
    iNext. iIntros (arr)"(Harr&_)". wp_pures.
    assert (Z.to_nat L = L) as -> by lia.
    assert (Z.to_nat 2%nat = 2) as -> by lia.
    wp_bind (_ <- _)%E.
    iApply (wp_store_offset _ _ hd 1 with "Hd").
    { apply lookup_lt_is_Some_2. rewrite replicate_length. lia. }
    iIntros "!> Hd". wp_pures.
    wp_apply (createHead_rec_spec with "[Harr]").
    { assert (replicate L #tl = (λ l : loc, #l) <$> (replicate L tl)) as ->.
      { apply list_eq. intros i'. rewrite list_lookup_fmap. 
        destruct (decide (i' < L)) as [Hi | Hi].
        - rewrite !lookup_replicate_2; try done.
        - apply not_lt in Hi. 
          assert (L ≤ i') as H' by lia. assert (H'' := H').
          apply (lookup_replicate_None L #tl i') in H'.
          apply (lookup_replicate_None L tl i') in H''.
          rewrite H' H'' /=. done. }
      iFrame "Harr". iSplit. { iPureIntro. by rewrite replicate_length. }
      iIntros (l j)"%Hlj %Hj". exfalso; lia. }
    iIntros (ls) "(Harr & %Length_ls & Hls)".
    assert (∃ (m: gmap nat bool), (∀ i, i < L → m !! i = Some false) 
      ∧ dom m = gset_seq 0 (L-1)) as 
      [mark [Def_mark Dom_mark]].
    { apply mark_map. lia. }
    assert (∃ (nx: gmap nat Node), (∀ i, i < L → nx !! i = Some tl)
      ∧ dom nx = gset_seq 0 (L-1)) as 
      [next [Def_next Dom_next]].
    { pose proof next_map L (replicate L tl) as H'.
      assert (L > 0) as H'' by lia. apply H' in H''. 
      destruct H'' as [nx H'']. exists nx. split; try apply H''.
      intros i Hi. destruct H'' as [H'' _]. rewrite H''; try done.
      apply f_equal. rewrite list_lookup_total_alt lookup_replicate_2 /=. done. lia. }
    wp_pures. 
    assert (<[1:=#arr]> (replicate 2 (#0, #L)%V) = (#0, #L)%V :: #arr :: []) as ->.
    { rewrite /replicate /=. done. }
    iAssert (hd ↦ (#0, #L)%V ∗ (hd +ₗ 1) ↦ #arr)%I with "[Hd]" as "(Hk & Hd)".
    { rewrite /array /big_opL. iDestruct "Hd" as "(Hd1 & Hd2 & _)".
      assert (hd +ₗ 0%nat = hd) as ->.
      { rewrite /Loc.add /=. assert (Z.add (loc_car hd) 0%nat = loc_car hd) as ->.
        lia. destruct hd; try done. } iFrame. }
    iDestruct (mapsto_persist with "Hk") as ">Hk".
    iDestruct (mapsto_persist with "Hd") as ">Hd".
    iAssert (node Σ Hg1 hd L mark next 0) with "[- Hpost]" as "Node".
    { iExists arr, ls. iFrame "Hd Hk Harr". iSplitR. iPureIntro.  
      split; try (done || lia). iIntros (l j)"%Hlj".
      assert (j < L) as j_lt_L. { by rewrite -Length_ls -lookup_lt_is_Some Hlj /=. }
      rewrite lookup_total_alt Def_mark /=; try done.
      rewrite lookup_total_alt Def_next /=; try done.
      iApply "Hls". iPureIntro. apply Hlj. by iPureIntro. }
    iApply ("Hpost" $! hd mark next). iModIntro. iFrame. iPureIntro. split; try done.
  Qed.

  Lemma createNode_rec_spec Σ (Hg1 : heapGS Σ) (arr succs: loc) (ls ss: list Node) (h i: nat) :
  ⊢  {{{ is_array Σ Hg1 succs ss 
         ∗ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls)
         ∗ ⌜length ls = h⌝
         ∗ ⌜h <= length ss⌝
         ∗ ∀ (l: loc) (j: nat), 
           ⌜ls !! j = Some l⌝ -∗ ⌜j < i⌝ -∗
             l ↦□ (#false, #((ss !!! j): Node)) }}}
           createNode_rec #i #h #arr #succs
      {{{ (ls': list Node),
          RET #();
              is_array Σ Hg1 succs ss
            ∗ arr ↦∗ ((fun l => # (LitLoc l)) <$> ls')
            ∗ ⌜length ls' = h⌝
            ∗ ∀ (l: loc) (j: nat), 
              ⌜ls' !! j = Some l⌝ -∗ ⌜j < h⌝ -∗
                l ↦□ (#false, #((ss !!! j): Node)) }}}.
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
        rewrite list_lookup_total_alt Def_si /=. iFrame. rewrite Len_ls; lia. }
      iApply "Hls". iPureIntro. rewrite list_lookup_insert_ne in Hlj; try done.
      iPureIntro; lia.
  Qed.

  Lemma createNode_spec Σ (Hg1 : heapGS Σ) (succs: loc) ss (k h: nat) :
  ⊢  {{{ is_array Σ Hg1 succs ss ∗ ⌜length ss = L⌝ ∗ ⌜0 < h < L⌝ }}}
           createNode #k #h #succs
        {{{ (n: Node) mark next,
            RET #n;
              is_array Σ Hg1 succs ss
            ∗ node Σ Hg1 n h mark next k
            ∗ ⌜dom mark = gset_seq 0 (h-1)⌝ ∗ ⌜dom next = gset_seq 0 (h-1)⌝
            ∗ (⌜∀ i, i < h → mark !! i = Some false⌝)
            ∗ (⌜∀ i, i < h → next !! i = Some (ss !!! i)⌝) }}}.
  Proof.
    iIntros (Φ) "!> (Hsuccs&%Len_ss&%Range_h) Hpost". wp_lam. wp_pures.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try done.
    iModIntro. iIntros (n)"(Hn&_)". wp_pures.
    wp_bind (AllocN _ _)%E. iApply wp_allocN; try (done || lia).
    iNext. iIntros (arr)"(Harr&_)". wp_pures.
    assert (Z.to_nat h = h) as -> by lia.
    assert (Z.to_nat 2%nat = 2) as -> by lia.
    wp_bind (_ <- _)%E.
    iApply (wp_store_offset _ _ n 1 with "Hn").
    { apply lookup_lt_is_Some_2. rewrite replicate_length. lia. }
    iIntros "!> Hn". wp_pures.
    wp_apply (createNode_rec_spec _ _ _ _ _ _ h _ with "[Hsuccs Harr]").
    { assert (replicate h #n = (λ l : loc, #l) <$> (replicate h n)) as ->.
      { apply list_eq. intros i'. rewrite list_lookup_fmap. 
        destruct (decide (i' < h)) as [Hi | Hi].
        - rewrite !lookup_replicate_2; try done.
        - apply not_lt in Hi. 
          assert (h ≤ i') as H' by lia. assert (H'' := H').
          apply (lookup_replicate_None h #n i') in H'.
          apply (lookup_replicate_None h n i') in H''.
          rewrite H' H'' /=. done. }
      iFrame "Hsuccs Harr".
      iSplit. { iPureIntro. by rewrite replicate_length. }
      iSplitR. iPureIntro; lia.
      iIntros (l j)"%Hlj %Hj". exfalso; lia. }
    iIntros (ls) "(Hsuccs & Harr & %Length_ls & Hls)".
    assert (∃ (m: gmap nat bool), (∀ i, i < h → m !! i = Some false) 
      ∧ dom m = gset_seq 0 (h-1)) as 
      [mark [Def_mark Dom_mark]].
    { apply mark_map. lia. }
    assert (∃ (nx: gmap nat Node), (∀ i, i < h → nx !! i = Some (ss !!! i))
      ∧ dom nx = gset_seq 0 (h-1)) as 
      [next [Def_next Dom_next]].
    { apply next_map. lia. }
    wp_pures. iApply ("Hpost" $! n mark next).
    iFrame "Hsuccs". iSplitL; last first.
    { iPureIntro. repeat split; try (done || lia). }  
    iExists arr, ls.
    assert (<[1:=#arr]> (replicate 2 (#k, #h)%V) = (#k, #h)%V :: #arr :: []) as ->.
    { rewrite /replicate /=. done. }
    iAssert (n ↦ (#k, #h)%V ∗ (n +ₗ 1) ↦ #arr)%I with "[Hn]" as "(Hk & Hn)".
    { rewrite /array /big_opL. iDestruct "Hn" as "(Hn1 & Hn2 & _)".
      assert (n +ₗ 0%nat = n) as ->.
      { rewrite /Loc.add /=. assert (Z.add (loc_car n) 0%nat = loc_car n) as ->.
        lia. destruct n; try done. } iFrame. }
    iDestruct (mapsto_persist with "Hk") as ">Hk".
    iDestruct (mapsto_persist with "Hn") as ">Hn".
    iFrame "Hn Hk Harr". iSplitR. iPureIntro. split; try (done || lia).
    iModIntro. iIntros (l j)"%Hlj".
    assert (j < h) as j_lt_h. { by rewrite -Length_ls -lookup_lt_is_Some Hlj /=. }
    rewrite lookup_total_alt Def_mark /=; try done.
    rewrite lookup_total_alt Def_next /=; try done. iSpecialize ("Hls" $! l j).
    iDestruct ("Hls" with "[%] [%]") as "H'"; try done.
  Qed.

  Lemma getHeight_spec Σ Hg1 (n: Node) :
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k }>>
          getHeight #n @ ∅
      <<{ node Σ Hg1 n h mark next k | RET #h }>>.
  Proof.
    iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[Node [_ Hclose]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. done.
  Qed.

  Lemma getKey_spec Σ Hg1 (n: Node) :
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k }>>
          getKey #n @ ∅
      <<{ node Σ Hg1 n h mark next k | RET #k }>>.
  Proof.
    iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[Node [_ Hclose]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. done.
  Qed.

  Lemma findNext_spec Σ Hg1 (n: Node) (i: nat) :
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜i < h⌝ }>>
          findNext #n #i @ ∅
      <<{ ∃∃ (m: bool) (n': Node),
              node Σ Hg1 n h mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !!! i = n'⌝ |
              RET (#m, #n') }>>.
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
    { apply lookup_lt_is_Some. destruct Len_vs1 as [-> _]. done.  }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { by rewrite list_lookup_fmap Def_li /=. }
    iIntros "Harr".
    iDestruct ("Hls1" with "[%]") as "H'". apply Def_li.
    iSpecialize ("Hclose" $! (m1 !!! i) (nx1 !!! i)).
    iMod ("Hclose" with "[Harr]") as "HΦ".
    { iSplitL. iExists arr0, ls1. iFrame "∗#%". by iPureIntro. }
    iModIntro. wp_pures. wp_load. by wp_pures.
  Qed.
  
  Lemma markNode_spec Σ Hg1 (n: Node) (i: nat) :
    ⊢  <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜i < h⌝ }>>
            markNode #n #i @ ∅
      <<{ ∃∃ (success: bool) mark',
              node Σ Hg1 n h mark' next k
            ∗ (match success with true => ⌜mark !!! i = false
                                            ∧ mark' = <[i := true]> mark⌝
                                | false => ⌜mark !!! i = true
                                            ∧ mark' = mark⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end) }>>.
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
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
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
      { apply lookup_lt_is_Some. by destruct Len_vs2 as [-> _].  }
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
          { destruct Len_vs2 as [Len_vs2 _]. apply list_eq. intros i'. 
            destruct (decide (i' = i)) as [-> | Hi'].
            rewrite list_lookup_fmap !list_lookup_insert /=. done.
            by rewrite fmap_length Len_vs2. by rewrite Len_vs2. 
            rewrite list_lookup_fmap !list_lookup_insert_ne /=; try done.
            by rewrite list_lookup_fmap. }
          iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
          iIntros (l j)"%Hlj". destruct (decide (j = i)) as [-> | Hj].
          assert (<[i:=true]> m2 !!! i = true) as ->.
          by rewrite lookup_total_insert.
          rewrite list_lookup_insert in Hlj. inversion Hlj.
          rewrite H1; try done. by destruct Len_vs2 as [-> _].
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

  Lemma markNode_proph_spec Σ Hg1 (n: Node) (p: proph_id) pvs :
    ⊢ proph p pvs -∗ 
      <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜0 < h⌝ }>>
            markNode' #n #p @ ∅
      <<{ ∃∃ (success: bool) mark' prf pvs',
              node Σ Hg1 n h mark' next k
            ∗ proph p pvs'
            ∗ ⌜Forall (λ x, ∃ v1, x = ((v1, #false)%V, #())) prf⌝
            ∗ (match success with 
                true => ⌜mark !!! 0 = false
                        ∧ mark' = <[0 := true]> mark
                        ∧ (∃ v1, pvs = prf ++ [((v1, #true)%V, #())] ++ pvs')⌝
              | false => ⌜mark !!! 0 = true
                        ∧ mark' = mark
                        ∧ pvs = prf ++ pvs'⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  }>>.
  Proof.
    iIntros "Hproph" (Φ) "AU". iLöb as "IH" forall (pvs).
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[(Node&%Hi0) [Hclose _]]".
    iDestruct "Node" as (arr0 ls0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hls0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "∗%". iExists arr0, ls0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) HAU]".
    iDestruct "Node" as (arr1 ls1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hls1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ li, ls1 !! 0 = Some li) as [li Def_li].
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { by rewrite list_lookup_fmap Def_li /=. }
    iIntros "Harr".
    iDestruct ("Hls1" with "[%]") as "H'". apply Def_li.
    destruct (decide (m1 !!! 0 = true)) as [Hmi | Hmi].
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false m1).
      iMod ("Hclose" with "[Harr Hproph]") as "HΦ".
      { iFrame. iSplitL. iExists arr0, ls1. iFrame "∗#%". by iPureIntro. }
      iModIntro. wp_pures. wp_load. wp_pures.
      rewrite Hmi. wp_pures. done.
    - apply not_true_is_false in Hmi.
      iDestruct "HAU" as "[Hclose _]".
      iMod ("Hclose" with "[Harr]") as "AU".
      { iFrame "∗%". iExists arr0, ls1. iFrame "∗#%". }
      iModIntro. wp_pures. wp_load. wp_pures.
      rewrite Hmi. wp_pures.
      wp_alloc li_new as "Hnew". wp_pures.
      wp_bind (Resolve _ _ _)%E. 
      iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
      iDestruct "Node" as (arr2 ls2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hls2)".
      iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
      inversion H'; subst arr2; clear H'.
      destruct ls2 as [|li' ls2'] eqn: Def_ls2. 
      { rewrite /= in Len_vs2. exfalso; lia. }
      assert (ls2 !! 0 = Some li') as Def_li'.
      { by rewrite Def_ls2 /=. }
      assert (((λ l : loc, #l) <$> li' :: ls2') = 
        #li' :: ((λ l : loc, #l) <$> ls2')) as ->.
      { by rewrite fmap_cons. } rewrite array_cons. 
      iDestruct "Harr" as "(Harr0 & Harr)".
      assert (arr0 +ₗ 0%nat = arr0) as ->. { by rewrite Loc.add_0. }
      destruct (decide (li' = li)) as [-> | Des_li].
      + wp_apply (wp_resolve_cmpxchg_suc with "[$Harr0 $Hproph]").
        { by left. }
        iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
        iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! true (<[0:=true]> m2)).
        iDestruct (mapsto_persist with "Hnew") as ">#Hnew'".
        iDestruct ("Hls2" with "[%]") as "H''". rewrite -Def_ls2. apply Def_li'.
        iDestruct (mapsto_agree with "H' H''") as "%H'". inversion H'.
        iMod ("Hclose" with "[Harr Harr0 Hproph]") as "HΦ".
        { iFrame "Hproph". iSplitL. iExists arr0, (<[0:= li_new]> ls2). iFrame "#".
          iSplitL. assert (((λ l : loc, #l) <$> <[0:=li_new]> ls2) = 
            #li_new :: ((λ l : loc, #l) <$> ls2')) as ->.
          { rewrite Def_ls2 /=. apply f_equal. done. } 
          rewrite array_cons. iFrame. 
          iSplitR. { iPureIntro. by rewrite insert_length Def_ls2. }
          iIntros (l j)"%Hlj". destruct (decide (j = 0)) as [-> | Hj].
          assert (<[0:=true]> m2 !!! 0 = true) as ->.
          by rewrite lookup_total_insert.
          rewrite list_lookup_insert in Hlj. inversion Hlj.
          rewrite H1; try done. destruct Len_vs2 as [Len_vs2 _]. 
          by rewrite Def_ls2 Len_vs2.
          assert (<[0:=true]> m2 !!! j = m2 !!! j) as ->.
          by rewrite lookup_total_insert_ne.
          rewrite list_lookup_insert_ne in Hlj; try done.
          iClear "H' H''".
          iDestruct ("Hls2" with "[%]") as "H'". rewrite -Def_ls2. apply Hlj.
          iFrame "#". iPureIntro. repeat split; try done.
          exists #li. rewrite Hpvs'. clear; set_solver. }
        iModIntro. wp_pures. done.
      + wp_apply (wp_resolve_cmpxchg_fail with "[$Harr0 $Hproph]").
        { by intros [=->]. }
        { by left. }
        iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
        iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr Harr0]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, (li' :: ls2'). iFrame "∗#%". }
        iModIntro. wp_pures. iApply ("IH" with "[$Hproph] [AU]"); try done.
        iAuIntro. rewrite /atomic_acc /=. iClear "#". 
        iMod "AU" as (h3 m3 nx3 k3)"[H' H'']". iModIntro.
        iExists h3, m3, nx3, k3. iFrame "H'". iSplit.
        * iDestruct "H''" as "[H'' _]". iApply "H''".
        * iDestruct "H''" as "[_ H'']". iIntros (res m3' prf pvs'').
          iIntros "(Node & Hproph & %Hprf & Hres)". 
          iSpecialize ("H''" $! res m3' (((#li', #false)%V, #()) :: prf) pvs'').
          iMod ("H''" with "[Node Hproph Hres]") as "HΦ".
          iFrame "Node Hproph". iSplitR. iPureIntro. 
          rewrite Forall_cons; split; try done. by exists #li'.
          destruct res; iDestruct "Hres" as "%H'"; iPureIntro; 
            repeat split; try apply H'. destruct H' as (_&_&[v1 Def_pvs']).
          rewrite Def_pvs' in Hpvs'. exists v1. rewrite Hpvs'. done.
          destruct H' as (_&_&Def_pvs'). rewrite Def_pvs' in Hpvs'.
          rewrite Hpvs'. clear; set_solver.
          done.
  Qed.

  Lemma changeNext_spec Σ Hg1 (n m m': Node) (i: nat) :
    ⊢  <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜i < h⌝ }>>
            changeNext #n #m #m' #i @ ∅
      <<{ ∃∃ (success: bool) next',
              node Σ Hg1 n h mark next' k
            ∗ (match success with true => ⌜next !!! i = m 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := m']> next⌝
                                | false => ⌜(next !!! i ≠ m ∨ 
                                              mark !!! i = true)
                                            ∧ next' = next⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  }>>.
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
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
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
    - apply not_true_is_false in Hmi. rewrite Hmi.
      destruct (decide (nx1 !!! i = m)) as [Hnx1_i | Hnx1_i]; last first.
      + iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! false nx1).
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL. iExists arr0, ls1. iFrame "∗#%". iPureIntro.
          split; try done. by left. }
        iModIntro. wp_pures. wp_load. wp_pures.
        rewrite bool_decide_eq_false_2; last first. { by intros [=]. }
        wp_pures. done.
      + iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, ls1. iFrame "∗#%". }
        iModIntro. wp_pures. wp_load. wp_pures.
        rewrite bool_decide_eq_true_2; last first. { by rewrite Hnx1_i. }
        wp_pures. wp_alloc li_new as "Hnew". wp_pures.
        wp_bind (CmpXchg _ _ _)%E.
        iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
        iDestruct "Node" as (arr2 ls2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hls2)".
        iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
        inversion H'; subst arr2; clear H'.
        assert (∃ li', ls2 !! i = Some li') as [li' Def_li'].
        { apply lookup_lt_is_Some. by destruct Len_vs2 as [-> _]. }
        destruct (decide (li' = li)) as [-> | Des_li].
        * wp_apply (wp_cmpxchg_suc_offset _ _ _ _ _ _ with "[Harr]"); 
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
            { destruct Len_vs2 as [Len_vs2 _]. apply list_eq. intros i'. 
              destruct (decide (i' = i)) as [-> | Hi'].
              rewrite list_lookup_fmap !list_lookup_insert /=. done.
              by rewrite fmap_length Len_vs2. by rewrite Len_vs2. 
              rewrite list_lookup_fmap !list_lookup_insert_ne /=; try done.
              by rewrite list_lookup_fmap. }
            iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
            iIntros (l j)"%Hlj". 
            destruct (decide (j = i)) as [-> | Hj]. 
            rewrite list_lookup_insert in Hlj. inversion Hlj. subst l.
            rewrite -H0. 
            assert (#((<[i:=m']> nx2 !!! i): Node) = #m') as H1'.
            apply f_equal. by rewrite lookup_total_insert.  
            iEval (rewrite -H1') in "Hnew'". iFrame "Hnew'". lia.
            rewrite list_lookup_insert_ne in Hlj; try done. 
            iClear "H' H''".
            iDestruct ("Hls2" with "[%]") as "H'". apply Hlj. 
            assert ((<[i:=m']> nx2 !!! j : Node) = nx2 !!! j) as H1'.
            by rewrite lookup_total_insert_ne. iEval (rewrite -H1') in "H'". 
            iFrame "H'". iPureIntro. repeat split; try done. by rewrite -H1. }
          iModIntro. wp_pures. done.
        * wp_apply (wp_cmpxchg_fail_offset _ _ _ _ _ _ #li' with "[Harr]"); 
            try done.
          {  by rewrite list_lookup_fmap Def_li' /=. }
          { by intros [=->]. }
          { left; try done. }
          iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
          iMod ("Hclose" with "[Harr]") as "AU".
          { iSplitL; last by iPureIntro. iExists arr0, ls2. iFrame "∗#%". }
          iModIntro. wp_pures. by iApply "IH".
  Qed.

  Lemma changeNext_proph_spec Σ (Hg1 : heapGS Σ) (n m m': Node) (p: proph_id) pvs :
  ⊢ proph p pvs -∗
    <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜0 < h⌝ }>>
          changeNext' #n #m #m' #p @ ∅
    <<{ ∃∃ (success: bool) next' prf pvs',
            node Σ Hg1 n h mark next' k
          ∗ proph p pvs'
          ∗ ⌜Forall (λ x, ∃ v1, x = ((v1, #false)%V, #())) prf⌝
          ∗ (match success with 
              true => ⌜next !!! 0 = m 
                      ∧ mark !!! 0 = false
                      ∧ next' = <[0 := m']> next
                      ∧ (∃ v1, pvs = prf ++ [((v1, #true)%V, #())] ++ pvs')⌝
            | false => ⌜(next !!! 0 ≠ m ∨ mark !!! 0 = true)
                        ∧ next' = next
                        ∧ pvs = prf ++ pvs'⌝ end) |
            RET (match success with true => SOMEV #() 
                                  | false => NONEV end) }>>.
  Proof.
    iIntros "Hproph" (Φ) "AU". iLöb as "IH" forall (pvs).
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
    assert (∃ li, ls1 !! 0 = Some li) as [li Def_li].
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ #li with "[Harr]"); try done.
    { by rewrite list_lookup_fmap Def_li /=. }
    iIntros "Harr".
    iDestruct ("Hls1" with "[%]") as "H'". apply Def_li.
    destruct (decide (m1 !!! 0 = true)) as [Hmi | Hmi].
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false nx1).
      iMod ("Hclose" with "[Harr Hproph]") as "HΦ".
      { iFrame. iSplitL. iExists arr0, ls1. iFrame "∗#%".
        iPureIntro; split; try done. repeat split; try done. by right. }
      iModIntro. wp_pures. wp_load. wp_pures.
      rewrite Hmi. wp_pures. done.
    - apply not_true_is_false in Hmi. rewrite Hmi.
      destruct (decide (nx1 !!! 0 = m)) as [Hnx1_i | Hnx1_i]; last first.
      + iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! false nx1).
        iMod ("Hclose" with "[Harr Hproph]") as "AU".
        { iFrame. iSplitL. iExists arr0, ls1. iFrame "∗#%". iPureIntro.
          repeat split; try done. by left. }
        iModIntro. wp_pures. wp_load. wp_pures.
        rewrite bool_decide_eq_false_2; last first. { by intros [=]. }
        wp_pures. done.
      + iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, ls1. iFrame "∗#%". }
        iModIntro. wp_pures. wp_load. wp_pures.
        rewrite bool_decide_eq_true_2; last first. { by rewrite Hnx1_i. }
        wp_pures. wp_alloc li_new as "Hnew". wp_pures.
        wp_bind (Resolve _ _ _)%E. 
        iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
        iDestruct "Node" as (arr2 ls2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hls2)".
        iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
        inversion H'; subst arr2; clear H'.
        destruct ls2 as [|li' ls2'] eqn: Def_ls2. 
        { rewrite /= in Len_vs2. exfalso; lia. }
        assert (ls2 !! 0 = Some li') as Def_li'.
        { by rewrite Def_ls2 /=. }
        assert (((λ l : loc, #l) <$> li' :: ls2') = 
          #li' :: ((λ l : loc, #l) <$> ls2')) as ->.
        { by rewrite fmap_cons. } rewrite array_cons. 
        iDestruct "Harr" as "(Harr0 & Harr)".
        assert (arr0 +ₗ 0%nat = arr0) as ->. { by rewrite Loc.add_0. }
        destruct (decide (li' = li)) as [-> | Des_li].
        * wp_apply (wp_resolve_cmpxchg_suc with "[$Harr0 $Hproph]").
          { by left. }
          iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
          iDestruct "HAU" as "[_ Hclose]".
          iSpecialize ("Hclose" $! true (<[0:=m']> nx2)).
          iDestruct (mapsto_persist with "Hnew") as ">#Hnew'".
          iDestruct ("Hls2" with "[%]") as "H''". rewrite -Def_ls2. apply Def_li'.
          iDestruct (mapsto_agree with "H' H''") as "%H'". inversion H'.
          iMod ("Hclose" with "[Harr Harr0 Hproph]") as "HΦ".
          { iFrame "Hproph". iSplitL. iExists arr0, (<[0:= li_new]> ls2). iFrame "#".
            iSplitL. assert (((λ l : loc, #l) <$> <[0:=li_new]> ls2) = 
              #li_new :: ((λ l : loc, #l) <$> ls2')) as ->.
            { rewrite Def_ls2 /=. apply f_equal. done. } 
            rewrite array_cons. iFrame. 
            iSplitR. { iPureIntro. by rewrite insert_length Def_ls2. }
            iIntros (l j)"%Hlj". destruct (decide (j = 0)) as [-> | Hj].
            rewrite list_lookup_insert in Hlj. inversion Hlj. subst l.
            assert (m2 !!! 0%nat = false) as -> by done.
            assert ((<[0%nat:=m']> nx2 !!! 0%nat : loc) = m') as ->.
            by rewrite lookup_total_insert.
            rewrite H1; try done. destruct Len_vs2 as [Len_vs2 _]. 
            by rewrite Def_ls2 Len_vs2.
            assert ((<[0%nat:=m']> nx2 !!! j : loc) = nx2 !!! j) as ->.
            by rewrite lookup_total_insert_ne.
            rewrite list_lookup_insert_ne in Hlj; try done.
            iClear "H' H''".
            iDestruct ("Hls2" with "[%]") as "H'". rewrite -Def_ls2. apply Hlj.
            iFrame "#". iPureIntro. repeat split; try done. by rewrite -H1.
            exists #li. rewrite Hpvs'. clear; set_solver. }
          iModIntro. wp_pures. done.
        * wp_apply (wp_resolve_cmpxchg_fail with "[$Harr0 $Hproph]").
          { by intros [=->]. }
          { by left. }
          iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
          iDestruct "HAU" as "[Hclose _]".
          iMod ("Hclose" with "[Harr Harr0]") as "AU".
          { iSplitL; last by iPureIntro. iExists arr0, (li' :: ls2'). iFrame "∗#%". }
          iModIntro. wp_pures. iApply ("IH" with "[$Hproph] [AU]"); try done.
          iAuIntro. rewrite /atomic_acc /=. iClear "#". 
          iMod "AU" as (h3 m3 nx3 k3)"[H' H'']". iModIntro.
          iExists h3, m3, nx3, k3. iFrame "H'". iSplit.
          ** iDestruct "H''" as "[H'' _]". iApply "H''".
          ** iDestruct "H''" as "[_ H'']". iIntros (res nx3' prf pvs'').
            iIntros "(Node & Hproph & %Hprf & Hres)". 
            iSpecialize ("H''" $! res nx3' (((#li', #false)%V, #()) :: prf) pvs'').
            iMod ("H''" with "[Node Hproph Hres]") as "HΦ"; try done.
            iFrame "Node Hproph". iSplitR. iPureIntro. 
            rewrite Forall_cons; split; try done. by exists #li'.
            destruct res; iDestruct "Hres" as "%H'"; iPureIntro; 
              repeat split; try apply H'. destruct H' as (_&_&_&[v1 Def_pvs']).
            rewrite Def_pvs' in Hpvs'. exists v1. rewrite Hpvs'. done.
            destruct H' as (_&_&Def_pvs'). rewrite Def_pvs' in Hpvs'.
            rewrite Hpvs'. clear; set_solver.
  Qed.

End IMPL1.