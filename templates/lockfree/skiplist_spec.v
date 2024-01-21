(* Hindsight spec for the skiplist template *)

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
Require Import multiset_flows keyset_ra.
Require Export skiplist_search skiplist_insert skiplist_delete hindsight_proof.

Module SKIPLIST_SPEC : HINDSIGHT_SPEC.
  Declare Module TR_SPEC : TRAVERSE_SPEC.
  Declare Module SK_SEARCH : SKIPLIST_SEARCH with Module TR_SPEC := TR_SPEC.
  Declare Module SK_INSERT : SKIPLIST_INSERT with Module TR_SPEC := TR_SPEC.
  Declare Module SK_DELETE : SKIPLIST_DELETE with Module TR_SPEC := TR_SPEC.
  Module DEFS := TR_SPEC.SK_UTIL.DEFS.
  Export TR_SPEC TR_SPEC.SK_UTIL TR_SPEC.SK_UTIL.SK TR_SPEC.SK_UTIL.DEFS.
  Export TR_SPEC.SK_UTIL.SK.TR.NODE TR_SPEC.SK_UTIL.SK.TR.

  (* Proof of initialization of the skiplist template *)
  Lemma init_spec Σ Hg1 Hg2 :
    {{{ True }}} init #() 
    {{{ (r: Node) (s : snapshot), RET #r; ds_inv Σ Hg1 Hg2 r {[0 := s]} 0 s }}}.
  Proof.
    iIntros (Φ) "_ Hpost". wp_lam. wp_apply createTail_spec; try done.
    iIntros (tl mt) "(Node_tl & %Dom_mt & %Mt_i)". 
    wp_pures. wp_apply createHead_spec; try done.
    iIntros (hd mh nh) "(Node_hd & %Dom_mh & %Dom_nh & %Mh_i & %Nh_i)".
    wp_pures. wp_alloc r as "HR". wp_pures. 
    iDestruct (mapsto_persist with "HR") as ">#HR".
    set N : gset Node := {[ hd; tl ]}.
    set C : gset nat := {[ 0; W ]}.
    set H : gmap Node nat := {[ hd := L; tl := L ]}.
    set Mk : gmap Node MarkT := {[ hd := mh; tl := mt ]}.
    set Nx : gmap Node NextT := {[ hd := nh; tl := ∅ ]}.
    set Ky : gmap Node nat := {[ hd := 0; tl := W ]}.
    
    assert (∃ ks : nzmap nat nat, (dom ks = gset_seq 1 W) ∧ (∀ k, ks !!! k ≤ 1))
      as [ks [Dom_ks Def_ks]]. 
    { set S : gset nat := gset_seq 1 W.
      set ks := let f := λ k res, <<[k := 1]>> res in set_fold f ∅ S.
      assert (∀ k, (k ∈ S → ks !!! k = 1) ∧ (k ∉ S → ks !!! k = 0)) as H'.
      { set P := λ (m' : nzmap nat nat) (X : gset nat), 
          ∀ k, (k ∈ X → m' !!! k = 1) ∧ (k ∉ X → m' !!! k = 0).
        apply (set_fold_ind_L P); try done.
        intros k X res Hkx HP. rewrite /P. rewrite /P in HP.
        intros k'. rewrite elem_of_union elem_of_singleton. split.
        intros [-> | Hk']. rewrite nzmap_lookup_total_insert. done.
        rewrite nzmap_lookup_total_insert_ne. apply HP. done. 
        clear -Hkx Hk'; set_solver. intros H'. 
        rewrite nzmap_lookup_total_insert_ne. apply HP. intros ?. apply H'.
        by right. intros ->. apply H'. by left. }
      exists ks. split. apply set_eq_subseteq. split. intros k Hk.
      rewrite nzmap_elem_of_dom_total in Hk. destruct (decide (k ∈ S)); try done.
      apply H' in n. rewrite n in Hk. rewrite /ccmunit /= /nat_unit in Hk. lia.
      intros k Hk. apply H' in Hk. rewrite nzmap_elem_of_dom_total Hk.
      rewrite /ccmunit /= /nat_unit. lia. intros k. 
      destruct (decide (k ∈ S)) as [H'' | H'']; apply H' in H''; lia. }
    set ks' := <<[ 0 := 1 ]>> ks.
    set Ih : multiset_flowint_ur nat := 
      int {| infR := {[hd := ks']}; outR := <<[ tl := ks ]>> ∅ |}.
    set It : multiset_flowint_ur nat := 
      int {| infR := {[tl := ks]}; outR := ∅ |}.
    set I : gmap Node (multiset_flowint_ur nat) := {[ hd := Ih; tl := It ]}.
    set s : snapshot := (N, C, H, Mk, Nx, Ky, I).

    assert (snapshot_constraints s) as SShot.
    { exists N, C, H, Mk, Nx, Ky, I. rewrite /s. split; try done.
      rewrite /H /Mk /Nx /Ky /I /N /= /= !dom_insert_L !dom_empty_L.
      repeat split. all: set_solver. }

    assert (W > 0) as HW. { apply W_gt_0. } 
    assert (L > 1) as HL. { apply L_gt_1. }
    iAssert (⌜hd ≠ tl⌝)%I as %hd_neq_tl.
    { destruct (decide (hd = tl)) as [-> | ?]; try done. iExFalso.
      iApply (node_sep_star with "Node_tl Node_hd"). }
    
    iMod (own_alloc (● prodKS (KS, C) ⋅ ◯ prodKS (KS, C))) as (γ_ks)"HKS".
    { rewrite auth_both_valid_discrete. split; try done. 
      rewrite /valid /cmra_valid /= /ucmra_valid /= /C /KS.
      intros x. rewrite elem_of_union !elem_of_singleton elem_of_gset_seq. lia. }

    iDestruct "HKS" as "(HKS & Hks)". 
    assert (prodKS (KS, C) = prodKS ({[0]}, {[0]}) ⋅ prodKS (KS ∖ {[0]}, {[W]}))
      as H'.
    { assert (KS = {[0]} ∪ (KS ∖ {[0]})) as H'.
      { apply set_eq_subseteq. split. intros x. destruct (decide (x = 0)) as [-> | Hx0].
        clear; set_solver. intros Hx. rewrite elem_of_union. right. set_solver.
        intros x. rewrite elem_of_union elem_of_singleton.
        intros [-> | Hx]. rewrite /KS elem_of_gset_seq. lia. clear -Hx; set_solver. }
      assert (C = {[0]} ∪ {[W]}) as -> by set_solver. rewrite {1}H'. symmetry.
      apply (ksRAT_prodKS_op {[0]} (KS ∖ {[0]}) {[0]} {[W]}).
      apply ksRAT_valid_composable. repeat split. rewrite /valid /=. done.
      rewrite /valid /=. rewrite /KS. intros x. rewrite elem_of_difference.
       rewrite elem_of_gset_seq !elem_of_singleton. lia. rewrite /=. clear; set_solver. }
    iEval (rewrite H') in "Hks". clear H'. iDestruct "Hks" as "(Hksh & Hkst)".
    assert (∀ i, i < L → Mark s hd !! i = Some false) as Mark_hd.
    { rewrite /Mark /s /Mk lookup_insert. done. }
    assert (∀ i, i < L → Mark s tl !! i = Some false) as Mark_tl.
    { rewrite /Mark /s /Mk lookup_insert_ne; try done. by rewrite lookup_insert. }
    assert (Key s hd = 0) as Key_hd. { by rewrite /s /Key /Ky /= lookup_insert. }
    assert (Key s tl = W) as Key_tl. 
    { rewrite /s /Key /Ky /= lookup_insert_ne; try done. by rewrite lookup_insert. }
    assert (Content s hd = {[0]}) as Content_hd.
    { rewrite /Content Key_hd /Marki lookup_total_alt Mark_hd /=. done. lia. }
    assert (Content s tl = {[W]}) as Content_tl.
    { rewrite /Content Key_tl /Marki lookup_total_alt Mark_tl /=. done. lia. }
    assert (FI s hd = Ih) as FI_hd.
    { rewrite /FI /s /I lookup_insert. done.  }
    assert (FI s tl = It) as FI_tl.
    { rewrite /FI /s /I lookup_insert_ne; try done. rewrite lookup_insert. done. }
    assert (dom Ih = {[hd]}) as Dom_Ih.
    { rewrite /dom /flowint_dom /Ih /= dom_insert_L. set_solver. }
    assert (dom It = {[tl]}) as Dom_It.
    { rewrite /dom /flowint_dom /It /= dom_insert_L. set_solver. }
    assert (ks ≠ 0%CCM) as ks_neq_0.
    { rewrite /ccmunit /ccm_unit /= /lift_unit.
      intros H'. rewrite nzmap_eq in H'. pose proof H' W as H'.
      rewrite nzmap_lookup_empty -nzmap_elem_of_dom_total2 in H'.
      apply H'. rewrite Dom_ks elem_of_gset_seq. lia. }
    assert (dom (out_map Ih) = {[tl]}) as Domout_Ih.
    { rewrite /Ih /=. apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero; try done.
      rewrite /dom. set_solver. }
    assert (dom (out_map It) = ∅) as Domout_It.
    { rewrite /It /=. set_solver. }
    assert (insets Ih = KS) as Insets_hd.
    { rewrite /insets Dom_Ih. rewrite -leibniz_equiv_iff big_opS_singleton.
      rewrite /Ih /inset /inf /= lookup_insert /= /ks'. 
      rewrite nzmap_dom_insert_nonzero. rewrite Dom_ks /KS.
      apply leibniz_equiv_iff. rewrite set_eq_subseteq. split;
      (intros x; rewrite elem_of_union elem_of_singleton !elem_of_gset_seq; lia).
      rewrite /ccmunit /= /nat_unit. lia. }
    assert (dom ks = KS ∖ {[0]}) as Dom_ks2.
    { rewrite Dom_ks /KS. apply leibniz_equiv_iff. rewrite set_eq_subseteq. 
      split; (intros x; rewrite elem_of_difference elem_of_singleton 
        !elem_of_gset_seq; lia). }
    assert (outsets Ih = KS ∖ {[0]}) as Outsets_hd.
    { rewrite /outsets Domout_Ih. rewrite -leibniz_equiv_iff big_opS_singleton.
      rewrite /Ih /outset /out /= nzmap_lookup_total_insert. 
      rewrite leibniz_equiv_iff. done. }
    assert (keyset (FI s hd) = {[0]}) as KS_hd.
    { rewrite FI_hd /keyset Insets_hd Outsets_hd. apply set_eq_subseteq. split.
      intros x. rewrite !elem_of_difference !elem_of_singleton. 
      intros [Hx Hx']. destruct (decide (x = 0)) as [-> | ?]; try done.
      exfalso. apply Hx'. done. intros x. 
      rewrite !elem_of_difference !elem_of_singleton. intros ->.
      split. rewrite /KS elem_of_gset_seq. lia. intros ?. lia. }
    assert (insets It = KS ∖ {[0]}) as Insets_tl.
    { rewrite /insets Dom_It. rewrite -leibniz_equiv_iff big_opS_singleton.
      rewrite /It /inset /inf /= lookup_insert /= /ks'. 
      rewrite leibniz_equiv_iff. done. }
    assert (outsets It = ∅) as Outsets_tl.
    { rewrite /outsets Domout_It big_opS_empty. set_solver. }
    assert (keyset (FI s tl) = KS ∖ {[0]}) as KS_tl.
    { rewrite FI_tl /keyset Insets_tl Outsets_tl. clear; set_solver. }
    assert (abs s = C) as Habs. { rewrite /abs /s. done. }
    assert (FP s = {[hd; tl]}) as FP_s. { rewrite /FP /s. done. }
    assert (Height s hd = L) as Ht_hd. 
    { rewrite /Height /s /H lookup_insert. done. }
    assert (Height s tl = L) as Ht_tl. 
    { rewrite /Height /s /H lookup_insert_ne; try done.
      rewrite lookup_insert. done. }
    assert (Mark s hd = mh) as Mk_hd.
    { rewrite /Mark /s /H lookup_insert. done. }
    assert (Mark s tl = mt) as Mk_tl. 
    { rewrite /Mark /s /H lookup_insert_ne; try done.
      rewrite lookup_insert. done. }
    assert (Next s hd = nh) as Nx_hd.
    { rewrite /Next /s /H lookup_insert. done. }
    assert (Next s tl = ∅) as Nx_tl. 
    { rewrite /Next /s /H lookup_insert_ne; try done.
      rewrite lookup_insert. done. }

    iAssert (resources _ _ _ γ_ks s)%I with "[- Hpost]" as "Res".
    { rewrite /resources. iFrame "HKS". rewrite FP_s.
      rewrite !big_sepS_union. rewrite !big_sepS_singleton.
      rewrite Ht_hd Ht_tl Key_hd Key_tl Mk_hd Mk_tl Nx_hd Nx_tl. 
      rewrite KS_hd KS_tl Content_hd Content_tl. iFrame.
      all: (clear -hd_neq_tl; set_solver). }

    iAssert (⌜∀ n k, n ∈ FP s → k ∈ keyset (FI s n) →
      (k ∈ abs s ↔ k ∈ Content s n)⌝)%I as "%Hks".
    { iDestruct "Res" as "(GKS & _ & HKS)".
      iPoseProof (keyset_summary with "GKS HKS") as "%H'"; try done. }
    
    assert (✓ GFI s) as Valid.
    { rewrite /GFI FP_s big_opS_union; last first. clear -hd_neq_tl; set_solver. 
      assert (✓ Ih) as Vh. 
      { rewrite /valid /=. split. rewrite dom_insert_L. 
        rewrite nzmap_dom_insert_nonzero; try done. rewrite /dom. 
        clear -hd_neq_tl; set_solver.
        intros H'; try done. }
      assert (✓ It) as Vt. 
      { rewrite /valid /=. split. rewrite dom_insert_L. rewrite /dom. 
        clear; set_solver. intros H'; try done. }
      rewrite !big_opS_singleton FI_hd FI_tl. apply intValid_composable.
      split; last split; last split; last split; try done.
      rewrite Dom_Ih Dom_It. clear -hd_neq_tl; set_solver.
      apply map_Forall_lookup. intros n m Hm. 
      assert (out It n = 0%CCM) as ->.
      { rewrite /out /It /= nzmap_lookup_empty. done. }
      rewrite ccm_pinv_unit left_id /inf Hm /=. done.
      apply map_Forall_lookup. intros n m Hm. 
      destruct (decide (n = tl)) as [-> | ?]; last first.
      { rewrite /inf_map /It /= lookup_insert_ne in Hm; try done. }
      assert (out Ih tl = ks) as ->.
      { rewrite /out /Ih /= nzmap_lookup_total_insert. done. }
      rewrite /inf Hm /=. rewrite /It /= lookup_insert in Hm. inversion Hm.
      rewrite ccm_pinv_inv ccm_right_id. done. }
    
    assert (GFI s = Ih ⋅ It) as Def_GFI.
    { rewrite /GFI FP_s big_opS_union; last first. clear -hd_neq_tl; set_solver. 
      rewrite !big_opS_singleton FI_hd FI_tl. done. }
    
    assert (per_tick_inv hd tl s) as PT_s.
    { split; last split; last split; last split; last split; last split.
      - rewrite FP_s Ht_hd Ht_tl Mk_hd Mk_tl Nx_hd Nx_tl Key_hd Key_tl.
        repeat split; try done. intros i Hi. rewrite lookup_total_alt.
        rewrite Mh_i; try done. intros i Hi. rewrite lookup_total_alt.
        rewrite Mt_i; try done. apply Nh_i. lia.
      - split. done. intros n Hn. rewrite Def_GFI. 
        destruct (decide (n = tl)) as [-> | ?]. rewrite Def_GFI in Valid.
        assert (tl ∈ dom It) as H'. { rewrite Dom_It. clear; set_solver. }
        pose proof intComp_inf_2 Ih It Valid tl H' as H''. rewrite H''.
        rewrite /inf /It /Ih /out /= lookup_insert nzmap_lookup_total_insert /=.
        rewrite ccm_pinv_inv. done. rewrite /inf.
        destruct (inf_map (Ih ⋅ It) !! n) eqn: H'; try done. 
        rewrite Def_GFI in Valid.
        apply flowint_contains in H'; try done. rewrite intComp_dom in H'; try done.
        rewrite Dom_Ih Dom_It in H'. clear -Hn n0 H'; set_solver.
      - apply Hks.
      - intros n. rewrite FP_s elem_of_union !elem_of_singleton. intros [-> | ->].
        + rewrite Ht_hd Mk_hd Nx_hd Key_hd FI_hd. 
          split; last split; last split; last split; last split; try done.
          * intros _. rewrite lookup_total_alt Mh_i; try done. lia.
          * lia.
          * rewrite Nh_i; try done. rewrite lookup_total_alt Mh_i /=; try done.
            repeat split; try done. rewrite Outsets_hd Insets_hd. clear; set_solver.
            rewrite Insets_hd /KS. done. rewrite Outsets_hd /= -Dom_ks2 Dom_ks. done.
            intros _. rewrite Insets_hd /KS elem_of_gset_seq. lia.
            intros k. rewrite Insets_hd /KS elem_of_gset_seq. clear; lia.
            intros k. rewrite /inf /Ih /= lookup_insert /= /ks'.
            destruct (decide (k = 0)) as [-> | ?]; try done.
            rewrite nzmap_lookup_total_insert. done. 
            rewrite nzmap_lookup_total_insert_ne; try done.  
            intros n k. rewrite /out /Ih /=. destruct (decide (n = tl)) as [-> | ?].
            rewrite nzmap_lookup_total_insert. done.
            rewrite nzmap_lookup_total_insert_ne; try done. 
            rewrite nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia.
            all : (clear -HL; lia).
        + rewrite Ht_tl Mk_tl Nx_tl Key_tl FI_tl. 
          split; last split; last split; last split; last split; try done.
          * intros _. rewrite lookup_total_alt Mt_i; try done. lia.
          * lia.
          * rewrite lookup_total_alt Mt_i /=; last first. lia.
            rewrite lookup_empty. repeat split; try done.
            rewrite Outsets_tl Insets_tl. clear; set_solver.
            rewrite Insets_tl /KS. intros x. rewrite elem_of_difference !elem_of_gset_seq.
            rewrite elem_of_singleton. clear -HW; lia.
            rewrite Outsets_tl. apply set_eq_subseteq. split.
            intros x. rewrite elem_of_gset_seq. clear; lia. clear; set_solver.
            intros _. rewrite Insets_tl /KS elem_of_difference elem_of_gset_seq.
            rewrite elem_of_singleton. clear -HW; lia.
            intros k. rewrite Insets_tl /KS elem_of_difference elem_of_gset_seq.
            rewrite elem_of_singleton; clear; lia.
            intros k. rewrite /inf /It /= lookup_insert /= /ks'. done.
            intros n k. rewrite /out /It /=.
            rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia.
      - intros n1 n2 Hnx. destruct (decide (n1 = hd)) as [-> | ?].
        + rewrite /Nexti Nx_hd Nh_i in Hnx; try done. inversion Hnx. subst n2.
          rewrite Key_hd Key_tl. done. lia.
        + rewrite /Nexti /s /Next /Nx lookup_insert_ne in Hnx.
          destruct (decide (n1 = tl)) as [-> | ?].
          rewrite lookup_insert lookup_empty in Hnx. done.
          rewrite lookup_insert_ne in Hnx. rewrite lookup_empty in Hnx. done.
          all: try done.
      - intros n1 n2 i Hnx. destruct (decide (n1 = hd)) as [-> | ?].
        + assert (i < L) as H'. { rewrite /Nexti Nx_hd in Hnx. 
          apply elem_of_dom_2 in Hnx. rewrite Dom_nh elem_of_gset_seq in Hnx. lia. }
          rewrite /Nexti Nx_hd Nh_i in Hnx; try done. inversion Hnx. subst n2.
          rewrite FP_s. clear; set_solver.
        + rewrite /Nexti /s /Next /Nx lookup_insert_ne in Hnx.
          destruct (decide (n1 = tl)) as [-> | ?].
          rewrite lookup_insert lookup_empty in Hnx. done.
          rewrite lookup_insert_ne in Hnx. rewrite lookup_empty in Hnx. done.
          all: try done.
      - intros n1 n2 i Hnx. destruct (decide (n1 = hd)) as [-> | ?].
        + assert (i < L) as H'. { rewrite /Nexti Nx_hd in Hnx. 
          apply elem_of_dom_2 in Hnx. rewrite Dom_nh elem_of_gset_seq in Hnx. lia. }
          rewrite /Nexti Nx_hd Nh_i in Hnx; try done. inversion Hnx. subst n2.
          rewrite Ht_tl; lia.
        + rewrite /Nexti /s /Next /Nx lookup_insert_ne in Hnx.
          destruct (decide (n1 = tl)) as [-> | ?].
          rewrite lookup_insert lookup_empty in Hnx. done.
          rewrite lookup_insert_ne in Hnx. rewrite lookup_empty in Hnx. done.
          all: try done. }
    
    iModIntro. iApply ("Hpost" $! r s). iExists hd, tl, γ_ks. iFrame "#∗%".
    iPureIntro. split. intros t Ht. assert (t = 0) as -> by lia.
    rewrite lookup_total_insert. done.
    intros t Ht. clear -Ht; lia.
  Qed.
  
  Lemma dsOp_spec Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r op (p: proph_id) 
    pvs tid t0 Q :
          main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
          thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
          □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
          ⌜local_pre op⌝ -∗
            {{{ proph p pvs ∗ 
                (match process_proph tid pvs with
                  contra => au Σ Hg1 Hg2 Hg3 N γ_r op Q
                | no_upd => True
                | upd => au Σ Hg1 Hg2 Hg3 N γ_r op Q end) }}}
                  dsOp (Op_to_val op) #p #r @ ⊤
            {{{ (res: resT) prf pvs', RET #res;
                proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
                (match process_proph tid pvs with
                  contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
                | no_upd => past_lin_witness Σ Hg1 Hg2 Hg3 γ_m op res t0
                | upd => Q #res ∨ 
                    ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof.
    iIntros "#HInv #Thd #HUpd %Local". unfold dsOp. 
    iIntros (Φ) "!# Hpre Hpost". 
    wp_lam. wp_pures. wp_bind (! _)%E.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    iDestruct "Templ" as (hd tl γ_ks)"(#HR & SShot0 & Res & %PT0 & %Trans_M0)".
    wp_load. iModIntro. iSplitR "Hpre Hpost".
    { iExists M0, T0, s0. iNext. iFrame "%#∗". iExists hd, tl, γ_ks. iFrame "%#∗". }
    wp_pures. unfold Op_to_val; destruct op as [k|k|k]; wp_pures.
    - wp_apply (SK_SEARCH.searchOp_spec with "[] [] [] [] [] [Hpre]"); try done.
    - wp_apply (SK_INSERT.insertOp_spec with "[] [] [] [] [] [Hpre]"); try done.
    - wp_apply (SK_DELETE.deleteOp_spec with "[] [] [] [] [] [Hpre]"); try done.
  Qed.

End SKIPLIST_SPEC.


