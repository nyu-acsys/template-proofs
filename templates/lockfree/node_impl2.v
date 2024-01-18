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

Module IMPL2 : NODE_IMPL.

  Parameter L : nat. (* Maximum Height *)
  Parameter W : nat. (* Keyspace *)
  Parameter W_gt_0 : 0 < W.
  Parameter L_gt_1 : 1 < L.
  Parameter randomNum : val.

  Definition MarkT := gmap nat bool.
  Definition NextT := gmap nat Node.
  Definition l0 := {| loc_car := 0 |}.

  Definition createTail_rec : val :=
    rec: "cT" "i" "arr" :=
      if: #L ≤ "i" then
        #()
      else
        ("arr" +ₗ "i") <- InjR #l0;;
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
        ("arr" +ₗ "i") <- InjR "tl";;
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
        ("arr" +ₗ "i") <- InjR "si";;
        "cN" ("i" + #1) "h" "arr" "succs".

  Definition createNode : val :=
    λ: "k" "succs",
      let: "h" := randomNum #L%nat in
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
      let: "res" := ! ("arr" +ₗ "i") in
      match: "res" with
        InjL "l" => (#true, "l")
      | InjR "l" => (#false, "l") end.
  
  Definition markNode : val :=
    rec: "markN" "n" "i" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "res" := ! ("arr" +ₗ "i") in
      match: "res" with
        InjL "l" => NONEV
      | InjR "l" => 
        if: CAS ("arr" +ₗ "i") (InjR "l") (InjL "l") then
          InjRV #()
        else
          "markN" "n" "i"
      end.

  Definition markNode' : val :=
    rec: "markN" "n" "p" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "res" := ! ("arr" +ₗ #0%nat) in
      match: "res" with
        InjL "l" => NONEV
      | InjR "l" => 
        let: "res" := Resolve (CmpXchg ("arr" +ₗ #0%nat) (InjR "l") (InjL "l")) "p" #() in
        if: Snd "res" then
          InjRV #()
        else
          "markN" "n" "p"
      end.

  Definition changeNext : val :=
    rec: "chN" "n" "m" "m'" "i" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "res" := ! ("arr" +ₗ "i") in
      match: "res" with
        InjL "l" => NONEV
      | InjR "l" =>
        if: CAS ("arr" +ₗ "i") (InjR "m") (InjR "m'") then
            InjRV #()
          else
            "chN" "n" "m" "m'" "i"
      end.

  Definition changeNext' : val :=
    rec: "chN" "n" "m" "m'" "p" :=
      let: "arr" := ! ("n" +ₗ #1) in
      let: "res" := ! ("arr" +ₗ #0%nat) in
      match: "res" with
        InjL "l" => NONEV
      | InjR "l" =>
        let: "res" := Resolve (CmpXchg ("arr" +ₗ #0%nat) (InjR "m") (InjR "m'")) "p" #() in
        if: Snd "res" then
            InjRV #()
          else
            "chN" "n" "m" "m'" "p"
      end.

  (* Context `{!heapGS Σ}. *)
  (* Notation iProp := (iProp Σ). *)


  Definition node Σ (Hg1 : heapGS Σ) (n: Node) (h: nat) (mark: MarkT) (next: NextT) 
    (k: nat) : iProp Σ :=
    ∃ (arr: loc) (vs: list val),
       n ↦□ (#k, #h)
    ∗ (n +ₗ 1) ↦□ #arr
    ∗ arr ↦∗ vs
    ∗ ⌜length vs = h ∧ 0 < h⌝
    ∗ ∀ (v: val) (i: nat), ⌜vs !! i = Some v⌝ -∗
        (⌜match v with 
          | InjLV #(LitLoc l) => mark !!! i = true ∧ next !!! i = l
          | InjRV #(LitLoc l) => mark !!! i = false ∧ next !!! i = l
          | _ => False end⌝).

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
    { destruct ls0. rewrite /= in Len_vs0. lia. by exists v, ls0. }
    rewrite Def_ls0 array_cons. iDestruct "Harr0" as "(Harr0 & Harr0')". 
    assert (∃ l1 ls1', ls1 = l1 :: ls1') as [l1 [ls1' Def_ls1]].
    { destruct ls1. rewrite /= in Len_vs1. lia. by exists v, ls1. }
    rewrite Def_ls1 array_cons. iDestruct "Harr1" as "(Harr1 & Harr1')".
    iCombine "Harr0 Harr1" as "H'". iPoseProof (mapsto_valid with "H'") as "%".
    exfalso; try done.
  Qed.

  Parameter randomNum_spec : ∀ Σ (Hg1: heapGS Σ) (n: nat),
  ⊢  {{{ True }}} randomNum #n {{{ (n': nat), RET #n'; ⌜0 < n' < n⌝ }}}.

  Lemma mark_map (h: nat) :
    h > 0 →
      ∃ (m: gmap nat bool), (∀ i, i < h → m !! i = Some false) 
        ∧ dom m = gset_seq 0 (h-1).
  Proof.
    intros Hz.
    Fixpoint f n (res: gmap nat bool) := 
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
    exists m. split. apply H'. pose proof H' h ∅ as H'. 
    rewrite -/m in H'. apply set_eq_subseteq. split.
    intros j Hj. destruct (decide (j < h)) as [Hj' | Hj']. 
    rewrite elem_of_gset_seq. lia. apply H' in Hj'. 
    rewrite lookup_empty -not_elem_of_dom in Hj'. done.
    intros j Hj. rewrite elem_of_gset_seq in Hj. 
    assert (j < h) as H'' by lia. apply H' in H''.
    rewrite elem_of_dom H''. done.    
  Qed.

  Lemma next_map (h: nat) (ss : list Node) :
    h > 0 →  
      (∃ (nx: gmap nat Node), (∀ i, i < h → nx !! i = Some (ss !!! i))
        ∧ dom nx = gset_seq 0 (h-1)).
  Proof.
    intros Hz.
    Fixpoint f' (l: list Node) n (res: gmap nat Node) := 
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
      exists nx. split. apply H'. pose proof H' h ∅ as H'. 
      rewrite -/nx in H'. apply set_eq_subseteq. split.
      intros j Hj. destruct (decide (j < h)) as [Hj' | Hj']. 
      rewrite elem_of_gset_seq. lia. apply H' in Hj'. 
      rewrite lookup_empty -not_elem_of_dom in Hj'. done.
      intros j Hj. rewrite elem_of_gset_seq in Hj. 
      assert (j < h) as H'' by lia. apply H' in H''.
      rewrite elem_of_dom H''. done.
  Qed.

  Lemma createTail_rec_spec Σ (Hg1 : heapGS Σ) (arr: loc) (vs: list val) (i: nat) :
  ⊢ {{{  arr ↦∗ vs
         ∗ ⌜length vs = L⌝
         ∗ ∀ (v: val) (j: nat), 
            ⌜vs !! j = Some v⌝ -∗ ⌜j < i⌝ -∗
              (⌜match v with 
              | InjRV #(LitLoc l) => l = l0
              | _ => False end⌝) }}}
          createTail_rec #i #arr
    {{{ (vs': list val),
        RET #();
            arr ↦∗ vs'
          ∗ ⌜length vs' = L⌝
          ∗ ∀ (v: val) (j: nat), 
            ⌜vs' !! j = Some v⌝ -∗ ⌜j < L⌝ -∗
              (⌜match v with 
              | InjRV #(LitLoc l) => l = l0
              | _ => False end⌝) }}}.
  Proof.
    iIntros (Φ) "!> Hpre Hpost". iLöb as "IH" forall (i vs).
    iDestruct "Hpre" as "(Harr & %Len_ls & Hvs)".
    wp_lam. wp_pures. destruct (bool_decide (L ≤ i)%Z) eqn: Hi; wp_pures.
    - iApply ("Hpost" $! vs). iFrame. iSplitR; first by iPureIntro.
      iModIntro. iIntros (v j)"%Hvj %j_le_h".
      rewrite bool_decide_eq_true in Hi. iApply "Hvs"; try done.
      iPureIntro; lia.
    - rewrite bool_decide_eq_false in Hi. 
      wp_bind (_ <- _)%E. iApply (wp_store_offset _ _ arr i vs with "Harr").
      { apply lookup_lt_is_Some_2. lia. }
      iIntros "!> Harr". wp_pures.
      assert (Z.add i 1 = (i+1)%nat) as -> by lia. 
      iSpecialize ("IH" $! (i+1) (<[i:= InjRV #l0]>vs)).
      iApply ("IH" with "[Harr Hvs]"); try done.
      iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
      iIntros (v j)"%Hvj %Hj". destruct (decide (j = i)) as [-> | Hij].
      { rewrite list_lookup_insert in Hvj. inversion Hvj. subst v. done. lia. }
      iApply "Hvs". iPureIntro. rewrite list_lookup_insert_ne in Hvj; try done.
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
    { iFrame "Harr".
      iSplit. { iPureIntro. by rewrite replicate_length. }
      iIntros (l j)"%Hlj %Hj". exfalso; lia. }
    iIntros (ls) "(Harr & %Length_ls & Hvs)".
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
      split; try (done || lia). iIntros (v j)"%Hvj".
      assert (j < L) as j_lt_L. { by rewrite -Length_ls -lookup_lt_is_Some Hvj /=. }
      rewrite lookup_total_alt Def_mark /=; try done.
      rewrite lookup_total_empty. 
      iDestruct ("Hvs" with "[%] [%]") as "%H'". apply Hvj. done.
      destruct v; try done. destruct v; try done. destruct l; try done. }
    iApply ("Hpost" $! tl mark). iModIntro. iFrame. iPureIntro. split; try done.
  Qed.

  Lemma createHead_rec_spec Σ (Hg1 : heapGS Σ) (tl arr : loc) (vs: list val) (i: nat) :
  ⊢ {{{  arr ↦∗ vs
         ∗ ⌜length vs = L⌝
         ∗ ∀ (v: val) (j: nat), 
            ⌜vs !! j = Some v⌝ -∗ ⌜j < i⌝ -∗
              (⌜match v with 
              | InjRV #(LitLoc l) => l = tl
              | _ => False end⌝) }}}
          createHead_rec #i #arr #tl
    {{{ (vs': list val),
        RET #();
            arr ↦∗ vs'
          ∗ ⌜length vs' = L⌝
          ∗ ∀ (v: val) (j: nat), 
            ⌜vs' !! j = Some v⌝ -∗ ⌜j < L⌝ -∗
              (⌜match v with 
              | InjRV #(LitLoc l) => l = tl
              | _ => False end⌝) }}}.
  Proof.
    iIntros (Φ) "!> Hpre Hpost". iLöb as "IH" forall (i vs).
    iDestruct "Hpre" as "(Harr & %Len_ls & Hvs)".
    wp_lam. wp_pures. destruct (bool_decide (L ≤ i)%Z) eqn: Hi; wp_pures.
    - iApply ("Hpost" $! vs). iFrame. iSplitR; first by iPureIntro.
      iModIntro. iIntros (v j)"%Hvj %j_le_h".
      rewrite bool_decide_eq_true in Hi. iApply "Hvs"; try done.
      iPureIntro; lia.
    - rewrite bool_decide_eq_false in Hi. wp_bind (_ <- _)%E.
      iApply (wp_store_offset _ _ arr i vs with "Harr").
      { apply lookup_lt_is_Some_2. lia. }
      iIntros "!> Harr". wp_pures.
      assert (Z.add i 1 = (i+1)%nat) as -> by lia. 
      iSpecialize ("IH" $! (i+1) (<[i:= InjRV #tl]>vs)).
      iApply ("IH" with "[Harr Hvs]"); try done.
      iFrame "Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
      iIntros (v j)"%Hvj %Hj". destruct (decide (j = i)) as [-> | Hij].
      { rewrite list_lookup_insert in Hvj. inversion Hvj. done. lia. }
      iApply "Hvs". iPureIntro. rewrite list_lookup_insert_ne in Hvj; try done.
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
    { iFrame "Harr". iSplit. { iPureIntro. by rewrite replicate_length. }
      iIntros (v j)"%Hvj %Hj". exfalso; lia. }
    iIntros (vs) "(Harr & %Length_vs & Hvs)".
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
    { iExists arr, vs. iFrame "Hd Hk Harr". iSplitR. iPureIntro.  
      split; try (done || lia). iIntros (v j)"%Hvj".
      assert (j < L) as j_lt_L. { by rewrite -Length_vs -lookup_lt_is_Some Hvj /=. }
      rewrite lookup_total_alt Def_mark /=; try done.
      rewrite lookup_total_alt Def_next /=; try done.
      iDestruct ("Hvs" with "[%] [%]") as "%H'". apply Hvj. done.
      destruct v; try done. destruct v; try done. destruct l; try done. }
    iApply ("Hpost" $! hd mark next). iModIntro. iFrame. iPureIntro. split; try done.
  Qed.

    
  Lemma createNode_rec_spec Σ (Hg1 : heapGS Σ) (arr succs: loc) (vs: list val) 
    (ss: list Node) (h i: nat) :
  ⊢ {{{ is_array Σ Hg1 succs ss 
         ∗ arr ↦∗ vs
         ∗ ⌜length vs = h⌝
         ∗ ⌜h <= length ss⌝
         ∗ ∀ (v: val) (j: nat), 
            ⌜vs !! j = Some v⌝ -∗ ⌜j < i⌝ -∗
              (⌜match v with 
              | InjRV #(LitLoc l) => ss !!! j = l
              | _ => False end⌝) }}}
          createNode_rec #i #h #arr #succs
    {{{ (vs': list val),
        RET #();
            is_array Σ Hg1 succs ss
          ∗ arr ↦∗ vs'
          ∗ ⌜length vs' = h⌝
          ∗ ∀ (v: val) (j: nat), 
            ⌜vs' !! j = Some v⌝ -∗ ⌜j < h⌝ -∗
              (⌜match v with 
              | InjRV #(LitLoc l) => ss !!! j = l
              | _ => False end⌝) }}}.
  Proof.
    iIntros (Φ) "!> Hpre Hpost". iLöb as "IH" forall (i vs).
    iDestruct "Hpre" as "(Hsuccs & Harr & %Len_ls & %Hss & Hvs)".
    wp_lam. wp_pures. destruct (bool_decide (h ≤ i)%Z) eqn: Hi; wp_pures.
    - iApply ("Hpost" $! vs). iFrame. iSplitR; first by iPureIntro.
      iModIntro. iIntros (v j)"%Hvj %j_le_h".
      rewrite bool_decide_eq_true in Hi. iApply "Hvs"; try done.
      iPureIntro; lia.
    - rewrite bool_decide_eq_false in Hi. 
      assert (∃ si, ss !! i = Some si) as [si Def_si].
      { apply lookup_lt_is_Some. lia. }  
      wp_apply (wp_load_offset _ _ _ _ _ _ #si with "[Hsuccs]"); try done.
      { by rewrite list_lookup_fmap Def_si /=. }
      iIntros "Hsuccs". wp_pures. wp_bind (_ <- _)%E.
      iApply (wp_store_offset _ _ arr i vs with "Harr").
      { apply lookup_lt_is_Some_2. lia. }
      iIntros "!> Harr". wp_pures.
      assert (Z.add i 1 = (i+1)%nat) as -> by lia. 
      iSpecialize ("IH" $! (i+1) (<[i:= InjRV #si]>vs)).
      iApply ("IH" with "[Hsuccs Harr Hvs]"); try done.
      iFrame "Hsuccs Harr". iSplitR. { iPureIntro. by rewrite insert_length. }
      iSplitR. by iPureIntro.
      iIntros (v j)"%Hvj %Hj". destruct (decide (j = i)) as [-> | Hij].
      { rewrite list_lookup_insert in Hvj. inversion Hvj. subst v.
        rewrite list_lookup_total_alt Def_si /=. done. lia. }
      iApply "Hvs". iPureIntro. rewrite list_lookup_insert_ne in Hvj; try done.
      iPureIntro; lia.
  Qed.

  Lemma createNode_spec Σ (Hg1 : heapGS Σ) (succs: loc) ss (k: nat) :
  ⊢  {{{ is_array Σ Hg1 succs ss ∗ ⌜length ss = L⌝ }}}
           createNode #k #succs
        {{{ (n: Node) (h: nat) mark next,
            RET #n;
              is_array Σ Hg1 succs ss
            ∗ node Σ Hg1 n h mark next k
            ∗ ⌜0 < h < L⌝
            ∗ ⌜dom mark = gset_seq 0 (h-1)⌝ ∗ ⌜dom next = gset_seq 0 (h-1)⌝
            ∗ (⌜∀ i, i < h → mark !! i = Some false⌝)
            ∗ (⌜∀ i, i < h → next !! i = Some (ss !!! i)⌝) }}}.
  Proof.
    iIntros (Φ) "!> (Hsuccs&%Len_ss) Hpost". wp_lam. wp_pures.
    wp_apply randomNum_spec; try done.
    iIntros (h) "%Hn'". wp_pures.  
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
    { iFrame "Hsuccs Harr".
      iSplit. { iPureIntro. by rewrite replicate_length. }
      iSplitR. iPureIntro; lia.
      iIntros (l j)"%Hlj %Hj". exfalso; lia. }
    iIntros (vs) "(Hsuccs & Harr & %Length_vs & #Hvs)".
    assert (∃ (m: gmap nat bool), (∀ i, i < h → m !! i = Some false) 
      ∧ dom m = gset_seq 0 (h-1)) as 
      [mark [Def_mark Dom_mark]].
    { apply mark_map. lia. }
    assert (∃ (nx: gmap nat Node), (∀ i, i < h → nx !! i = Some (ss !!! i))
      ∧ dom nx = gset_seq 0 (h-1)) as 
      [next [Def_next Dom_next]].
    { apply next_map. lia. }
    wp_pures. iApply ("Hpost" $! n h mark next).
    iFrame "Hsuccs". iSplitL; last first.
    { iPureIntro; try done. }  
    iExists arr, vs.
    assert (<[1:=#arr]> (replicate 2 (#k, #h)%V) = (#k, #h)%V :: #arr :: []) as ->.
    { rewrite /replicate /=. done. }
    iAssert (n ↦ (#k, #h)%V ∗ (n +ₗ 1) ↦ #arr)%I with "[Hn]" as "(Hk & Hn)".
    { rewrite /array /big_opL. iDestruct "Hn" as "(Hn1 & Hn2 & _)".
      assert (n +ₗ 0%nat = n) as ->.
      { rewrite /Loc.add /=. assert (Z.add (loc_car n) 0%nat = loc_car n) as ->.
        lia. destruct n; try done. } iFrame. }
    iDestruct (mapsto_persist with "Hk") as ">Hk".
    iDestruct (mapsto_persist with "Hn") as ">Hn".
    iFrame "Hn Hk Harr". iSplitR. iPureIntro. split. done. lia. 
    iModIntro. iIntros (v j)"%Hvj".
    assert (j < h) as j_lt_h. { by rewrite -Length_vs -lookup_lt_is_Some Hvj /=. }
    iSpecialize ("Hvs" $! v j). iDestruct ("Hvs" with "[%] [%]") as "H'"; try done.
    destruct v; try done. destruct v; try done. destruct l; try done.
    iDestruct "H'" as %Hssj. iPureIntro.
    rewrite !lookup_total_alt Def_mark /=; try done. 
    rewrite Def_next; try done. 
  Qed.

  Lemma getHeight_spec Σ Hg1 (n: Node) :
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k }>>
          getHeight #n @ ∅
      <<{ node Σ Hg1 n h mark next k | RET #h }>>.
  Proof.
    iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h0 m0 nx0 k0) "[Node [_ Hclose]]".
    iDestruct "Node" as (arr0 vs0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hvs0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, vs0. iFrame "∗#%". }
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
    iDestruct "Node" as (arr0 vs0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hvs0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, vs0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) [_ Hclose]]".
    iDestruct "Node" as (arr1 vs1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hvs1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ vi, vs1 !! i = Some vi) as [vi Def_vi].
    { apply lookup_lt_is_Some. destruct Len_vs1 as [-> _]. done. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ vi with "[Harr]"); try done.
    iIntros "Harr".
    iDestruct ("Hvs1" with "[%]") as "H'". apply Def_vi.
    iSpecialize ("Hclose" $! (m1 !!! i) (nx1 !!! i)).
    iMod ("Hclose" with "[Harr]") as "HΦ".
    { iSplitL. iExists arr0, vs1. iFrame "∗#%". by iPureIntro. }
    iModIntro. wp_pures. destruct vi; try done; destruct vi; try done; 
    destruct l; try done; wp_pures.
    all: iDestruct "H'" as %[H' H'']; rewrite H' H''; done.
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
    iDestruct "Node" as (arr0 vs0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hvs0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, vs0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) HAU]".
    iDestruct "Node" as (arr1 vs1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hvs1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ vi, vs1 !! i = Some vi) as [vi Def_vi].
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ vi with "[Harr]"); try done.
    iIntros "Harr".
    iDestruct ("Hvs1" with "[%]") as "H'". apply Def_vi.
    destruct (decide (m1 !!! i = true)) as [Hmi | Hmi].
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false m1).
      iMod ("Hclose" with "[Harr]") as "HΦ".
      { iSplitL. iExists arr0, vs1. iFrame "∗#%".
        by iPureIntro. }
      iModIntro. wp_pures. rewrite Hmi. 
      destruct vi; try done; destruct vi; try done; destruct l; try done; last first.
      { iDestruct "H'" as %[? _]. done. } wp_pures. done.
    - apply not_true_is_false in Hmi. rewrite Hmi.
      destruct vi; try done; destruct vi; try done; destruct l; try done.
      { iDestruct "H'" as %[? _]. done. }
      iDestruct "HAU" as "[Hclose _]".
      iMod ("Hclose" with "[Harr]") as "AU".
      { iFrame "%". iExists arr0, vs1. iFrame "∗#%". }
      iModIntro. wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
      iDestruct "Node" as (arr2 vs2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hvs2)".
      iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
      inversion H'; subst arr2; clear H'.
      assert (∃ vi', vs2 !! i = Some vi') as [vi' Def_vi'].
      { apply lookup_lt_is_Some. by destruct Len_vs2 as [-> _]. }
      destruct (decide (vi' = InjRV #l)) as [-> | Des_vi].
      + wp_apply (wp_cmpxchg_suc_offset _ _ _ _ _ _ with "[Harr]"); 
          try done.
        { left; try done. }
        iIntros "Harr".
        iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! true (<[i:=true]> m2)).
        iDestruct ("Hvs2" with "[%]") as "H''". apply Def_vi'.
        iEval (simpl) in "H''". 
        iMod ("Hclose" with "[Harr]") as "HΦ".
        { iDestruct "H''" as %[? ?]. iSplitL; last by iPureIntro. 
          iExists arr0, (<[i:= InjLV #l]> vs2). iFrame "# Harr".
          iSplitR. { iPureIntro. by rewrite insert_length. }
          iIntros (v j)"%Hvj". destruct (decide (j = i)) as [-> | Hj].
          rewrite list_lookup_insert in Hvj; last by lia. inversion Hvj.
          assert (<[i:=true]> m2 !!! i = true) as ->.
          by rewrite lookup_total_insert. by iPureIntro.
          rewrite list_lookup_insert_ne in Hvj; try done. iClear "H'".
          iDestruct ("Hvs2" with "[%]") as "H'". apply Hvj.
          destruct v; try done; destruct v; try done; destruct l1; try done.
          all: iDestruct "H'" as %[? ?]. 
          all: iPureIntro; rewrite lookup_total_insert_ne; try done. }
        iModIntro. wp_pures. done.
      + wp_apply (wp_cmpxchg_fail_offset _ _ _ _ _ _ vi' with "[Harr]"); 
          try done.
        { right; try done. }
        iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, vs2. iFrame "∗#%". }
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
    iDestruct "Node" as (arr0 vs0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hvs0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iFrame "%". iExists arr0, vs0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) HAU]".
    iDestruct "Node" as (arr1 vs1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hvs1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ vi, vs1 !! 0 = Some vi) as [vi Def_vi].
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ vi with "[Harr]"); try done.
    iIntros "Harr".
    iDestruct ("Hvs1" with "[%]") as "H'". apply Def_vi.
    destruct (decide (m1 !!! 0 = true)) as [Hmi | Hmi].
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false m1).
      iMod ("Hclose" with "[Harr Hproph]") as "HΦ".
      { iFrame. iSplitL. iExists arr0, vs1. iFrame "∗#%". by iPureIntro. }
      iModIntro. wp_pures. rewrite Hmi. 
      destruct vi; try done; destruct vi; try done; destruct l; try done; last first.
      { iDestruct "H'" as %[? _]. done. } wp_pures. done.
    - apply not_true_is_false in Hmi. rewrite Hmi.
      destruct vi; try done; destruct vi; try done; destruct l; try done.
      { iDestruct "H'" as %[? _]. done. }
      iDestruct "HAU" as "[Hclose _]".
      iMod ("Hclose" with "[Harr]") as "AU".
      { iFrame "%". iExists arr0, vs1. iFrame "∗#%". }
      iClear "Hvs0 Hvs1". iModIntro. wp_pures. 
      wp_bind (Resolve _ _ _)%E. 
      iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
      iDestruct "Node" as (arr2 vs2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hvs2)".
      iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
      inversion H'; subst arr2; clear H'.
      destruct vs2 as [|vi' vs2'] eqn: Def_vs2.
      { clear -Len_vs2. exfalso. rewrite /= in Len_vs2. lia. } rewrite -Def_vs2.
      assert (vs2 !! 0 = Some vi') as Def_vi'. { rewrite Def_vs2 /=. done. }
      iEval (rewrite Def_vs2 array_cons) in "Harr". 
      iDestruct "Harr" as "(Harr0 & Harr)".
      assert (arr0 +ₗ 0%nat = arr0) as ->. { by rewrite Loc.add_0. }
      destruct (decide (vi' = InjRV #l)) as [-> | Des_vi].
      + wp_apply (wp_resolve_cmpxchg_suc with "[$Harr0 $Hproph]").
        { by left. }
        iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
        iDestruct "HAU" as "[_ Hclose]".
        iSpecialize ("Hclose" $! true (<[0:=true]> m2)).
        iDestruct ("Hvs2" with "[%]") as "H''". apply Def_vi'.
        iEval (simpl) in "H''". 
        iMod ("Hclose" with "[Harr Harr0 Hproph]") as "HΦ".
        { iDestruct "H''" as %[? ?]. iFrame "Hproph". iSplitL. 
          iExists arr0, (<[0:= InjLV #l]> vs2). iFrame "#".
          assert (<[0:=InjLV #l]> vs2 = InjLV #l :: vs2') as H'.
          { rewrite Def_vs2 /=. done. } rewrite H'. iFrame.
          iSplitR. { iPureIntro. rewrite /=. rewrite /= in Len_vs2. done. }
          iIntros (v j)"%Hvj". destruct (decide (j = 0)) as [-> | Hj].
          rewrite /= in Hvj. inversion Hvj.
          assert (<[0:=true]> m2 !!! 0 = true) as ->.
          by rewrite lookup_total_insert. by iPureIntro.
          rewrite -H' in Hvj. rewrite list_lookup_insert_ne in Hvj; try done. 
          iClear "H'".
          iDestruct ("Hvs2" with "[%]") as "H'". apply Hvj.
          destruct v; try done; destruct v; try done; destruct l1; try done.
          all: iDestruct "H'" as %[? ?]; iPureIntro. 
          all: try (rewrite lookup_total_insert_ne; try done).
          repeat split; try done. exists (InjRV #l). rewrite Hpvs'. clear; set_solver. }
        iModIntro. wp_pures. done.
      + wp_apply (wp_resolve_cmpxchg_fail with "[$Harr0 $Hproph]").
        { by intros [=->]. }
        { by right. }
        iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
        iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr Harr0]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, (vi' :: vs2').
          rewrite -Def_vs2. iFrame "∗#%". rewrite Def_vs2 array_cons. iFrame.
          by iPureIntro. }
        iModIntro. wp_pures. iApply ("IH" with "[$Hproph] [AU]"); try done.
        iAuIntro. rewrite /atomic_acc /=. iClear "#". 
        iMod "AU" as (h3 m3 nx3 k3)"[H' H'']". iModIntro.
        iExists h3, m3, nx3, k3. iFrame "H'". iSplit.
        * iDestruct "H''" as "[H'' _]". iApply "H''".
        * iDestruct "H''" as "[_ H'']". iIntros (res m3' prf pvs'').
          iIntros "(Node & Hproph & %Hprf & Hres)". 
          iSpecialize ("H''" $! res m3' (((vi', #false)%V, #()) :: prf) pvs'').
          iMod ("H''" with "[Node Hproph Hres]") as "HΦ".
          iFrame "Node Hproph". iSplitR. iPureIntro. 
          rewrite Forall_cons; split; try done. by exists vi'.
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
    iDestruct "Node" as (arr0 vs0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hvs0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iSplitL; last by iPureIntro. iExists arr0, vs0. iFrame "∗#%". }
    iModIntro. wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) HAU]".
    iDestruct "Node" as (arr1 vs1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hvs1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ vi, vs1 !! i = Some vi) as [vi Def_vi].
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ vi with "[Harr]"); try done.
    iIntros "Harr".
    iDestruct ("Hvs1" with "[%]") as "H'". apply Def_vi.
    destruct vi; try done.
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false nx1).
      destruct vi; try done. destruct l; try done. iDestruct "H'" as %[? _].
      iMod ("Hclose" with "[Harr]") as "HΦ".
      { iSplitL. iExists arr0, vs1. iFrame "∗#%".
        iPureIntro; split; try done. by right. }
      iModIntro. wp_pures. done.
    - destruct vi; try done. destruct l; try done. 
      iDestruct "HAU" as "[Hclose _]".
      iMod ("Hclose" with "[Harr]") as "AU".
      { iSplitL; last by iPureIntro. iExists arr0, vs1. iFrame "∗#%". }
      iModIntro. wp_pures. wp_bind (CmpXchg _ _ _)%E.
      iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
      iDestruct "Node" as (arr2 vs2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hvs2)".
      iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
      inversion H'; subst arr2; clear H'.
      assert (∃ vi', vs2 !! i = Some vi') as [vi' Def_vi'].
      { apply lookup_lt_is_Some. by destruct Len_vs2 as [-> _]. } iClear "H'".
      iDestruct ("Hvs2" with "[%]") as "H'". apply Def_vi'.
      destruct vi'; try done.
      + destruct vi'; try done. destruct l1; try done.
        wp_apply (wp_cmpxchg_fail_offset _ _ _ _ _ _ (InjLV #l1) with "[Harr]"); 
          try done.
        { left; try done. }
        iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
        iMod ("Hclose" with "[Harr]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, vs2. iFrame "∗#%". }
        iModIntro. wp_pures. by iApply "IH".
      + destruct vi'; try done. destruct l1; try done.
        destruct (decide (l1 = m)) as [-> | Des_l1]; last first.
        * wp_apply (wp_cmpxchg_fail_offset _ _ _ _ _ _ (InjRV #l1) with "[Harr]"); 
            try done.
          { by intros [=->]. }
          { left; try done. }
          iIntros "Harr". iDestruct "HAU" as "[Hclose _]".
          iMod ("Hclose" with "[Harr]") as "AU".
          { iSplitL; last by iPureIntro. iExists arr0, vs2. iFrame "∗#%". }
          iModIntro. wp_pures. by iApply "IH".
        * wp_apply (wp_cmpxchg_suc_offset _ _ _ _ _ _ with "[Harr]"); 
            try done.
          { left; try done. }
          iIntros "Harr". iDestruct "HAU" as "[_ Hclose]".
          iSpecialize ("Hclose" $! true (<[i:=m']> nx2)).
          iClear "Hvs0 Hvs1".
          iMod ("Hclose" with "[Harr]") as "HΦ".
          { iDestruct "H'" as %[? ?].
            iSplitL. iExists arr0, (<[i:= InjRV #m']> vs2). iFrame "# Harr".
            iSplitR. { iPureIntro. by rewrite insert_length. }
            iIntros (v j)"%Hvj". 
            destruct (decide (j = i)) as [-> | Hj]. 
            rewrite list_lookup_insert in Hvj. inversion Hvj. subst v.
            iPureIntro. split; try done.
            assert (((<[i:=m']> nx2 !!! i): Node) = m') as H1'.
            by rewrite lookup_total_insert. done. lia.
            rewrite list_lookup_insert_ne in Hvj; try done.
            iDestruct ("Hvs2" with "[%]") as "H'". apply Hvj.
            destruct v; try done; destruct v; try done; destruct l1; try done.
            all: try iDestruct "H'" as %[? ?]. 
            all: try (iPureIntro; rewrite lookup_total_insert_ne; try done).
            iPureIntro. repeat split; try done. }
          iModIntro. wp_pures. done.
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
    iDestruct "Node" as (arr0 vs0) "(#Hk0 & #Hn0 & Harr & %Len_vs0 & #Hvs0)".
    wp_load. 
    iMod ("Hclose" with "[Harr]") as "AU".
    { iSplitL; last by iPureIntro. iExists arr0, vs0. iFrame "∗#%". }
    iModIntro. iClear "Hvs0". wp_pures. wp_bind (! _)%E.
    iMod "AU" as (h1 m1 nx1 k1) "[(Node&%Hi1) HAU]".
    iDestruct "Node" as (arr1 vs1) "(#Hk1 & #Hn1 & Harr & %Len_vs1 & #Hvs1)".
    iDestruct (mapsto_agree with "[$Hn0] [$Hn1]") as "%H'". 
    inversion H'; subst arr1; clear H'.
    assert (∃ vi, vs1 !! 0 = Some vi) as [vi Def_vi].
    { apply lookup_lt_is_Some. by destruct Len_vs1 as [-> _]. }  
    wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        _ vi with "[Harr]"); try done.
    iIntros "Harr".
    iDestruct ("Hvs1" with "[%]") as "H'". apply Def_vi.
    destruct vi; try done.
    - iDestruct "HAU" as "[_ Hclose]".
      iSpecialize ("Hclose" $! false nx1).
      destruct vi; try done. destruct l; try done. iDestruct "H'" as %[? _].
      iMod ("Hclose" with "[Harr Hproph]") as "HΦ".
      { iFrame. iSplitL. iExists arr0, vs1. iFrame "∗#%".
        iPureIntro; split; try done. repeat split; try done. by right. }
      iModIntro. wp_pures. done.
    - destruct vi; try done. destruct l; try done. 
      iDestruct "HAU" as "[Hclose _]".
      iMod ("Hclose" with "[Harr]") as "AU".
      { iSplitL; last by iPureIntro. iExists arr0, vs1. iFrame "∗#%". }
      iModIntro. iClear "Hvs1". wp_pures. wp_bind (Resolve _ _ _)%E.
      iMod "AU" as (h2 m2 nx2 k2) "[(Node&%Hi2) HAU]".
      iDestruct "Node" as (arr2 vs2) "(#Hk2 & #Hn2 & Harr & %Len_vs2 & #Hvs2)".
      iDestruct (mapsto_agree with "[$Hn0] [$Hn2]") as "%H'". 
      inversion H'; subst arr2; clear H'.
      destruct vs2 as [|vi' vs2'] eqn: Def_vs2.
      { clear -Len_vs2. exfalso. rewrite /= in Len_vs2. lia. } rewrite -Def_vs2.
      assert (vs2 !! 0 = Some vi') as Def_vi'. { rewrite Def_vs2 /=. done. }
      iClear "H'". iDestruct ("Hvs2" with "[%]") as "H'". apply Def_vi'.
      iEval (rewrite Def_vs2 array_cons) in "Harr".
      iDestruct "Harr" as "(Harr0 & Harr)".
      assert (arr0 +ₗ 0%nat = arr0) as ->. { by rewrite Loc.add_0. }
      destruct vi'; try done.
      + destruct vi'; try done. destruct l1; try done.
        wp_apply (wp_resolve_cmpxchg_fail with "[$Harr0 $Hproph]").
        { intros H'. inversion H'. }
        { left; try done. }
        iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
        iDestruct "HAU" as "[Hclose _]". iMod ("Hclose" with "[Harr Harr0]") as "AU".
        { iSplitL; last by iPureIntro. iExists arr0, (InjLV #l1 :: vs2'). 
          iFrame "∗#%". rewrite Def_vs2. done. }
        iModIntro. wp_pures. iApply ("IH" with "[$Hproph] [AU]"); try done.
        iAuIntro. rewrite /atomic_acc /=. iClear "#". 
        iMod "AU" as (h3 m3 nx3 k3)"[H' H'']". iModIntro.
        iExists h3, m3, nx3, k3. iFrame "H'". iSplit.
        ** iDestruct "H''" as "[H'' _]". iApply "H''".
        ** iDestruct "H''" as "[_ H'']". iIntros (res nx3' prf pvs'').
          iIntros "(Node & Hproph & %Hprf & Hres)". 
          iSpecialize ("H''" $! res nx3' (((InjLV #l1, #false)%V, #()) :: prf) pvs'').
          iMod ("H''" with "[Node Hproph Hres]") as "HΦ"; try done.
          iFrame "Node Hproph". iSplitR. iPureIntro. 
          rewrite Forall_cons; split; try done. by exists (InjLV #l1).
          destruct res; iDestruct "Hres" as "%H'"; iPureIntro; 
            repeat split; try apply H'. destruct H' as (_&_&_&[v1 Def_pvs']).
          rewrite Def_pvs' in Hpvs'. exists v1. rewrite Hpvs'. done.
          destruct H' as (_&_&Def_pvs'). rewrite Def_pvs' in Hpvs'.
          rewrite Hpvs'. clear; set_solver.
      + destruct vi'; try done. destruct l1; try done.
        destruct (decide (l1 = m)) as [-> | Des_l1]; last first.
        * wp_apply (wp_resolve_cmpxchg_fail with "[$Harr0 $Hproph]").
          { intros H'. inversion H'. done. }
          { left; try done. }
          iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
          iDestruct "HAU" as "[Hclose _]". iMod ("Hclose" with "[Harr Harr0]") as "AU".
          { iSplitL; last by iPureIntro. iExists arr0, (InjRV #l1 :: vs2'). 
            iFrame "∗#%". rewrite Def_vs2. done. }
          iModIntro. wp_pures. iApply ("IH" with "[$Hproph] [AU]"); try done.
          iAuIntro. rewrite /atomic_acc /=. iClear "#". 
          iMod "AU" as (h3 m3 nx3 k3)"[H' H'']". iModIntro.
          iExists h3, m3, nx3, k3. iFrame "H'". iSplit.
          ** iDestruct "H''" as "[H'' _]". iApply "H''".
          ** iDestruct "H''" as "[_ H'']". iIntros (res nx3' prf pvs'').
            iIntros "(Node & Hproph & %Hprf & Hres)". 
            iSpecialize ("H''" $! res nx3' (((InjRV #l1, #false)%V, #()) :: prf) pvs'').
            iMod ("H''" with "[Node Hproph Hres]") as "HΦ"; try done.
            iFrame "Node Hproph". iSplitR. iPureIntro. 
            rewrite Forall_cons; split; try done. by exists (InjRV #l1).
            destruct res; iDestruct "Hres" as "%H'"; iPureIntro; 
              repeat split; try apply H'. destruct H' as (_&_&_&[v1 Def_pvs']).
            rewrite Def_pvs' in Hpvs'. exists v1. rewrite Hpvs'. done.
            destruct H' as (_&_&Def_pvs'). rewrite Def_pvs' in Hpvs'.
            rewrite Hpvs'. clear; set_solver.
        * wp_apply (wp_resolve_cmpxchg_suc with "[$Harr0 $Hproph]").
          { by left. }
          iIntros "H''". iDestruct "H''" as (pvs')"(%Hpvs' & Hproph & Harr0)".
          iDestruct "HAU" as "[_ Hclose]".
          iSpecialize ("Hclose" $! true (<[0:=m']> nx2)).
          iMod ("Hclose" with "[Harr Harr0 Hproph]") as "HΦ".
          { iDestruct "H'" as %[? ?]. iFrame "Hproph".
            iSplitL. iExists arr0, (<[0:= InjRV #m']> vs2). iFrame "#".
            iSplitL. assert (<[0:=InjRV #m']> vs2 = InjRV #m' :: vs2') as ->.
            { rewrite Def_vs2 /=. apply f_equal. done. }
            rewrite array_cons. iFrame. 
            iSplitR. { iPureIntro. by rewrite insert_length Def_vs2. }
            iIntros (v j)"%Hvj". destruct (decide (j = 0)) as [-> | Hj]. 
            rewrite list_lookup_insert in Hvj. inversion Hvj. subst v.
            assert (m2 !!! 0%nat = false) as -> by done.
            assert ((<[0%nat:=m']> nx2 !!! 0%nat : loc) = m') as ->.
            by rewrite lookup_total_insert. by iPureIntro. 
            destruct Len_vs2 as [Len_vs2 _]. by rewrite Def_vs2 Len_vs2.
            assert ((<[0%nat:=m']> nx2 !!! j : loc) = nx2 !!! j) as ->.
            by rewrite lookup_total_insert_ne. 
            rewrite list_lookup_insert_ne in Hvj; try done.
            iDestruct ("Hvs2" with "[%]") as "H'". apply Hvj.
            iFrame "#". iPureIntro. repeat split; try done.
            exists (InjRV #m). rewrite Hpvs'. clear; set_solver. }
          iModIntro. wp_pures. done.
  Qed.


End IMPL2.