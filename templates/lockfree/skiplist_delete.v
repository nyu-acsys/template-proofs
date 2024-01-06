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
Require Import list_flow_upd_marking skiplist_util.
Require Export skiplist_delete_maintenance.

Module Type SKIPLIST_DELETE.
  Declare Module TR_SPEC : TRAVERSE_SPEC.
  Declare Module SK_DEL_MNT : SKIPLIST_DELETE_MAINTENANCE with Module TR_SPEC := TR_SPEC.
  Export SK_DEL_MNT SK_DEL_MNT.TR_SPEC. 
  Export SK_UTIL.DEFS SK_UTIL.DEFS.DS.
  Export TR TR.NODE.

  Lemma deleteOp_spec (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ)
    N γ_t γ_r γ_m γ_mt γ_msy r (p: proph_id) pvs tid t0 Q k (hd tl: Node) :
    main_inv Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_m γ_mt γ_msy r -∗
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    □ update_helping_protocol Σ Hg1 Hg2 Hg3 N γ_t γ_r γ_mt γ_msy -∗
    ⌜local_pre (deleteOp k)⌝ -∗
    r ↦□ (#hd, #tl) -∗
      {{{ proph p pvs ∗ 
          (match process_proph tid pvs with
            contra => au Σ Hg1 Hg2 Hg3 N γ_r (deleteOp k) Q
          | no_upd => True
          | upd => au Σ Hg1 Hg2 Hg3 N γ_r (deleteOp k) Q end) }}}
            delete #p #hd #tl #k @ ⊤
      {{{ (res: resT) prf pvs', RET #res;
          proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ ∗
          (match process_proph tid pvs with
            contra => ⌜Forall (λ x, x.2 ≠ #tid) prf⌝
          | no_upd => past_lin_witness Σ Hg1 Hg2 Hg3 γ_m (deleteOp k) res t0
          | upd => Q #res ∨ 
              ⌜Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf⌝ end) }}}.
  Proof.
    iIntros "#HInv #Thd_st #Upd [%HL %Range_k] #HR'". 
    iIntros (Φ) "!# (Hproph & Hmatch) Hpost".
    wp_lam. wp_pures.
    wp_apply (traverse_spec Σ Hg1 Hg2 Hg3); try done.
    iIntros (preds succs ps ss res) "(Hpreds & Hsuccs & %Len_ps 
      & %Len_ss & %HpsL & %HssL & #Htr)".  
    wp_pures. destruct res; wp_pures.
    - assert (is_Some(ss !! 0)) as [c Hss0].
      { rewrite lookup_lt_is_Some Len_ss; lia. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        ((λ n : loc, #n) <$> ss) #c with "[Hsuccs]"); try done.
      { by rewrite list_lookup_fmap Hss0 /=. }
      iIntros "Hsuccs". wp_pures.
      iApply fupd_wp.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
      iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
      { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iPoseProof (per_tick_current with "[%] [%] [$Hist]") as "%PT_s0"; try done.
      iAssert (⌜Key s0 c = k⌝)%I as %Hk.
      { apply list_lookup_total_correct in Hss0. rewrite Hss0.
        iDestruct "Htr" as "(_&H')". iDestruct "H'" as (s)"(Past_s&%H'&%H''&%H''')".
        iAssert (⌜Marki s c 0 = false⌝)%I as %Marki_cs. 
        { iPoseProof (per_tick_past with "[%] Hist Past_s") as "%PT_s"; try done.
          apply PT_s in H'. destruct H' as (_&_&_&_&_&H').
          destruct H' as (_&_&_&H'&_). rewrite /Marki. 
          destruct (Mark s c !!! 0); try done. rewrite H' in H''. clear -H''; set_solver. }
        rewrite /Content Marki_cs in H'''. 
        assert (k = Key s c) as Hk. clear -H'''; set_solver. 
        apply leibniz_equiv in Habs0. rewrite -Habs0.
        iPoseProof (key_eq_2 with "[%] [$] [$Past_s] [%]") as "->"; try done. }
      assert (c ≠ hd) as c_neq_hd.
      { destruct PT_s0 as ((_&H'&_)&_). intros ->. lia. }
      assert (c ≠ tl) as c_neq_tl. 
      { destruct PT_s0 as ((_&_&H'&_)&_). intros ->. lia. }      
      iPoseProof (traversal_inv_hd_tl with "[%] [%] [%] [%] [#] [Hist]") 
        as ">(#HtrL & Hist)"; try done.
      iModIntro. iSplitR "Hpost Hpreds Hsuccs Hmatch Hproph".
      { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%". }
      clear Hk s0 PT_s0 Trans_M0 PT0 Habs0 M0 T0. iModIntro.
      wp_apply (maintenanceOp_delete_spec with "[]"); try done.
      { iFrame "%". iAssert (⌜0 < L⌝)%I as "H'". by (iPureIntro; lia).
        iDestruct "Htr" as "(Htr & _)". 
        iPoseProof ("Htr" with "H'") as "(_&H'')".  
        iDestruct "H''" as (s)"#(Past_c & %FP_c & _)". 
        iExists s; iFrame "#". apply list_lookup_total_correct in Hss0.
        rewrite Hss0 in FP_c. by iPureIntro. }
      iIntros "#Hmnt". wp_pure credit:"Hcred". wp_pures.
      awp_apply (markNode_proph_spec with "Hproph"); try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
      iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
      { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }  
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
      { apply leibniz_equiv in Habs0. rewrite -Habs0.
        iDestruct "Hmnt" as (s h)"(Past_s&%&_)".
      iApply (in_FP_2 with "[%] [$Hist] [$Past_s] [%]"); try done. }
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iDestruct "Nodes" as "(Node_c & Nodes_rest)".
      iAssert (⌜per_tick_inv hd tl s0⌝)%I as %PT_s0.
      { iApply (per_tick_current with "[%] [%] [$Hist]"); try done. }
      iAssert ((node Σ _ c (Height s0 c) (Mark s0 c) (Next s0 c) (Key s0 c)) 
        ∗ ⌜0 < Height s0 c⌝)%I with "[Node_c]" as "Hpre".
      { iFrame. iPureIntro. apply PT_s0 in FP_c0. by apply FP_c0. }
      iAaccIntro with "Hpre".
      { iIntros "(Node_c & _)". iModIntro. 
        iSplitR "Hmatch Hcred Hpreds Hsuccs Hpost"; try done.
        iNext; iExists M0, T0, s0. iFrame "∗%#". iExists hd, tl. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) c); try done. 
        iFrame. iFrame. }
      iIntros (success mark' prf pvs')"(Node_c & Hproph & %Hprf & Hif)".
      iApply (lc_fupd_add_later with "Hcred"). iNext.
      iAssert (∀ i, ⌜1 ≤ i < Height s0 c⌝ → ⌜Marki s0 c i = true⌝)%I as %Marki_c.
      { iIntros (i)"%Hi". 
        iDestruct "Hmnt" as (s h) "(Past_s & %FP_c' & %Ht_c & %Hj)".
        apply leibniz_equiv in Habs0. iAssert (⌜Height s0 c = Height s c⌝)%I as %Ht'.
        { rewrite -Habs0.
          iPoseProof (height_eq_2 _ _ _ _ c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
            try done. }
        rewrite Ht' -Ht_c in Hi. apply Hj in Hi. rewrite -Habs0.
        iPoseProof (marking_mono_2 _ _ _ _ c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
            try done. } 
      destruct success.
      + iDestruct "Hif" as %(Mark_c0 & Def_mark' & Hpvs').
        iDestruct "SShot0" as %[FP0 [C0 [Ht0 [Mk0 [Nx0 [Ky0 [I0 
          [Hs0 [Dom_Ht0 [Dom_Mk0 [Dom_Nx0 [Dom_Ky0 Dom_I0]]]]]]]]]]]].
        assert (∀ x, x ∈ FP s0 → flow_constraints_I x (FI s0 x) 
                  (Mark s0 x !!! 0) (Next s0 x !! 0) (Key s0 x)) as Hflow.
        { destruct PT_s0 as (_&_&_&H'&_).
          intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&?). }
        iAssert (⌜Key s0 c = k⌝)%I as %Key_c. 
        { iDestruct "Htr" as "(_ & Htr)". iDestruct "Htr" as (s)"(Past_s & %H')".
          apply list_lookup_total_correct in Hss0. rewrite Hss0 in H'.
          destruct H' as (H'&H''&H'''). 
          iAssert (⌜Marki s c 0 = false⌝)%I as %Marki_cs. 
          { iPoseProof (per_tick_past with "[%] Hist Past_s") as "%PT_s"; try done.
            apply PT_s in H'. destruct H' as (_&_&_&_&_&H').
            destruct H' as (_&_&_&H'&_). rewrite /Marki. 
            destruct (Mark s c !!! 0); try done. rewrite H' in H''. 
            clear -H''; set_solver. }
          assert (k = Key s c) as Hk.
          { rewrite /Content Marki_cs in H'''. clear -H'''; set_solver. }
            apply leibniz_equiv in Habs0. rewrite -Habs0.
          iPoseProof (key_eq_2 _ _ _ _ c with "[%] [$Hist] [$Past_s] [%]") as "->"; 
            try done.  }
        iAssert (⌜∃ cn, Nexti s0 c 0 = Some cn⌝)%I as %[cn Def_cn].
        { destruct PT_s0 as ((_&_&Hk&_)&_&_&H'&_). apply H' in FP_c0.
          destruct FP_c0 as (_&H''&_). iPureIntro.
          destruct (decide (c = tl)) as [-> | Hctl].
          rewrite -Key_c Hk in Range_k. clear -Range_k; lia.
          apply H'' in Hctl. rewrite /Nexti. apply elem_of_dom.
          rewrite Hctl. rewrite elem_of_gset_seq; lia. }
        
        set S := keyset (I0 !!! c).

        assert (∀ x, I0 !!! x = FI s0 x) as I0_eq_s0.
        { intros x. rewrite Hs0; unfold FI. try done. }
        assert (∀ k', k' ∈ S → k' ≤ k) as HSk.
        { rewrite Hs0 /FP in FP_c0. rewrite {1}Hs0 /FP in Hflow.
          apply Hflow in FP_c0. rewrite /Marki Mark_c0 in FP_c0.
          destruct FP_c0 as (_&_&_&H1'&_&H2'&_&_).
          rewrite /S I0_eq_s0. intros k' Hk'. 
          rewrite /keyset elem_of_difference in Hk'.
          destruct Hk' as [Hk1' Hk2']. destruct H1' as [H1' H1''].
          rewrite -H1'' in Hk2'. rewrite Key_c in Hk2'.
          apply Nat.nlt_ge. intros H'.
          rewrite elem_of_gset_seq in Hk2'.
          apply Hk2'. split; try lia. by apply H2'. }
        
        iAssert (⌜∃ (I: gmap Node (multiset_flowint_ur nat)) (nk: Node),
                  dom I ⊆ FP s0
                ∧ hd ∉ dom I
                ∧ c ∈ dom I
                ∧ nk ∈ dom I
                ∧ c ≠ nk
                ∧ (∀ x, x ∈ dom I → x ≠ c → k < Key s0 x)
                ∧ (keyset (I !!! c) = ∅)
                ∧ (keyset (I !!! nk) = keyset (I0 !!! nk) ∪ keyset (I0 !!! c))
                ∧ (∀ x, x ∈ dom I ∖ {[ c; nk ]} → 
                    keyset (I !!! x) = keyset (I0 !!! x))
                ∧ ([^op set] x ∈ dom I, FI s0 x) = ([^op set] x ∈ dom I, I !!! x)
                ∧ (∀ x, x ∈ dom I → x ≠ c → flow_constraints_I x (I !!! x) 
                                 (Mark s0 x !!! 0) (Next s0 x !! 0) (Key s0 x))
                ∧ (flow_constraints_I c (I !!! c) (true) 
                                        (Next s0 c !! 0) (Key s0 c))⌝)%I 
          as %[I [nk Hflupd]].
        { 
          assert (∃ (Nx: gmap Node Node), (∀ x, Nx !! x = Next s0 x !! 0) 
            ∧ (dom Nx ⊆ dom Nx0)) as [Nx [Def_Nx Dom_Nx]].
          { pose proof make_next_map Nx0 as [Nx [H' H'']]. exists Nx.
            split. rewrite Hs0 /=. apply H'. done. }
          
          assert (∃ (Mk: gmap Node bool), (∀ x, Mk !!! x = Mark s0 x !!! 0) 
            ∧ (dom Mk = dom Mk0)) as [Mk [Def_Mk Dom_Mk]].
          { assert (∀ x, x ∈ dom Mk0 → 0 ∈ dom (Mk0 !!! x)) as H'.
            { intros x Hx. rewrite Dom_Mk0 in Hx.
              destruct PT_s0 as (_&_&_&PT&_). rewrite {1}Hs0 /FP in PT.
              apply PT in Hx. destruct Hx as (_&_&H'&_).
              rewrite Hs0 /Mark in H'. rewrite H' elem_of_gset_seq. clear; lia. }
            pose proof make_mark_map Mk0 H' as [Mk [H1' [H1'' H1''']]].
            exists Mk. split. rewrite Hs0 /=. apply H1''. done. }
          
          assert (∀ x, Ky0 !!! x = Key s0 x) as Def_Ky0.
          { rewrite Hs0. unfold Key. try done. }
          
          assert (nx_key_rel Nx Ky0) as Nx_key_rel.
          { destruct PT_s0 as (_&_&_&_&H'&_). intros n1 n2.
            rewrite !Def_Nx !Def_Ky0. apply H'. }
          assert (nx_mk_closed Nx Mk (dom I0)) as Hcl.
          { split; last split; last split. 
            - rewrite Dom_I0 -Dom_Nx0. done.
            - rewrite Dom_Mk. clear -Dom_Mk0 Dom_I0; set_solver.
            - destruct PT_s0 as (_&_&_&_&_&H'&_). intros n1 n2.
              rewrite {2}Hs0 in H'. unfold FP in H'.
              rewrite !Def_Nx Dom_I0. apply H'.
            - intros x Hmx Hnx.
              assert (x ∈ FP s0) as H'. rewrite /FP Hs0 -Dom_Mk0.
              apply elem_of_dom_2 in Hmx. by rewrite -Dom_Mk.
              apply PT_s0 in H'. destruct H' as (_&H'&_).
              destruct (decide (x = tl)) as [-> | Hxtl].
              + destruct PT_s0 as ((_&_&_&_&H''&_)&_).
                pose proof H'' 0 as H''. rewrite -Def_Mk in H''; try done.
                apply lookup_total_correct in Hmx. rewrite Hmx in H''.
                clear -H'' HL; try (done || lia).
              + apply H' in Hxtl. 
                rewrite Def_Nx in Hnx; try done. 
                rewrite -not_elem_of_dom Hxtl in Hnx. apply Hnx.
                rewrite elem_of_gset_seq. clear; lia. }
          assert (✓ ([^op set] x ∈ dom I0, (I0 !!! x: multiset_flowint_ur nat))) 
            as VI.
          { destruct PT_s0 as (_&(H'&_)&_).
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
          assert (c ∈ dom I0) as c_in_I0.
          { by rewrite -FP_s0_I0. }
          assert (∀ x, x ∈ dom I0 → Mk !!! x = true → 
            keyset (I0 !!! x) = ∅) as KS_mk.
          { intros x Hx%Hflow. rewrite Def_Mk I0_eq_s0. 
            rewrite /Marki; intros H'; rewrite H' in Hx. 
            by destruct Hx as (_&_&_&Hx&_). }
          assert (∀ n1 n2, insets (I0 !!! n1) ≠ ∅ → Nx !! n1 = Some n2 → 
            dom (out_map (I0 !!! n1: multiset_flowint_ur nat)) = {[n2]}) 
            as Nx_dom.
          { intros n1 n2 Hin Nx_n1. assert (n1 ∈ dom I0) as H'.
            { apply elem_of_dom_2 in Nx_n1. apply Dom_Nx in Nx_n1. 
              by rewrite Dom_I0 -Dom_Nx0. }
            apply Hflow in H'. destruct H' as (_&H'&_).
            rewrite -Def_Nx Nx_n1 -I0_eq_s0 in H'. by apply H' in Hin. }
          assert (S ⊆ keyset (I0 !!! c)) as Keyset_S.
          { subst S; clear; set_solver. }
          set res := list_flow_upd_marking c Nx Mk S I0.
          assert (list_flow_upd_marking c Nx Mk S I0 = res) as Def_res by try done.
          
          iAssert (⌜∀ n1 n2, n1 ∈ dom I0 → n2 ∈ dom I0 → 
            n1 ≠ n2 → keyset (I0 !!! n1) ## keyset (I0 !!! n2)⌝)%I as %Disj_KS.
          { iPoseProof (keyset_disjoint_subset with "Nodes_KS") as "(%H' & _)".
            rewrite FP_s0_I0 in H'. iPureIntro. intros n1 n2; rewrite !I0_eq_s0.
            apply H'. }
          assert (∀ x, x ∈ dom I0 → Mk !!! x = false → 
            Ky0 !!! c < Ky0 !!! x → S ## outsets (I0 !!! x)) as Disj_outsets.
          { intros x Hx Mk_x Hkey. rewrite elem_of_disjoint. intros k' Hk1' Hk2'.
            destruct PT_s0 as (_&_&_&H'&_). rewrite {1}Hs0 /FP -Dom_I0 in H'.
            apply H' in Hx. destruct Hx as (_&_&_&_&Hx&Hx'). 
            rewrite /Marki in Def_Mk. rewrite -Def_Ky0 -Def_Mk Mk_x in Hx'. 
            destruct Hx' as (_&_&_&Hx'&_). destruct Hx' as [Hx1 Hx2]. 
            rewrite I0_eq_s0 -Hx2 in Hk2'.
            rewrite Def_Ky0 Key_c in Hkey. rewrite -Def_Ky0 in Hx.
            rewrite elem_of_gset_seq in Hk2'. apply HSk in Hk1'.
            clear -Hk1' Hkey Hx Hk2'. lia. }
          assert (∀ x, x ∈ dom I0 → Mk !!! x = false → 
            Ky0 !!! c < Ky0 !!! x → S ## insets (I0 !!! x)) as Disj_insets.
          { intros x Hx Mk_x Hkey. pose proof Disj_outsets x Hx Mk_x Hkey as Hout.
            rewrite elem_of_disjoint. intros k' Hk1' Hk2'. 
            assert (k' ∈ keyset (I0 !!! x)) as KS_x.
            { rewrite elem_of_difference; split; try done. 
              clear -Hout Hk1'. set_solver. }
            destruct (decide (x = c)) as [-> | Hxc].
            { clear -Hkey; lia. } rewrite /S in Hk1'.
            pose proof Disj_KS x c Hx c_in_I0 Hxc as H'.
            clear -H' KS_x Hk1'; set_solver. }
          assert (∀ x k, x ∈ dom I0 → 
            inf ((I0 !!! x):multiset_flowint_ur _) x !!! k ≤ 1) as Inf_x.
          { intros x k' Hx%Hflow. destruct Hx as (_&_&_&_&_&_&H'&_).
            rewrite I0_eq_s0. apply H'. }
          assert (∀ x x' k, x ∈ dom I0 → 
            out ((I0 !!! x):multiset_flowint_ur _) x' !!! k ≤ 1) as Out_x.
          { intros x x' k' Hx%Hflow. destruct Hx as (_&_&_&_&_&_&_&H').
            rewrite I0_eq_s0. apply H'. }
          assert (∀ x, x ∈ dom I0 → outsets (I0 !!! x) ⊆ insets (I0 !!! x))
            as Out_In.
          { intros x Hx%Hflow. destruct Hx as (_&_&H'&_).
            rewrite I0_eq_s0. apply H'. }
          assert (insets (I0 !!! c) ≠ ∅) as Insets_c_ne.
          { apply Hflow in c_in_I0. rewrite -I0_eq_s0 Mark_c0 in c_in_I0.
            destruct c_in_I0 as (_&_&_&(H'&_)&_).
            apply (non_empty_inhabited_L k). apply H'.
            rewrite elem_of_gset_seq Key_c. clear -Range_k; lia. }
          assert (outsets (I0 !!! c) ≠ ∅) as Outsets_c_ne.
          { apply Hflow in c_in_I0. rewrite -I0_eq_s0 Mark_c0 in c_in_I0.
            destruct c_in_I0 as (_&_&_&(_&H')&_).
            apply (non_empty_inhabited_L W). 
            rewrite -H' elem_of_gset_seq Key_c. clear -Range_k; lia. }
          
          rewrite /Nexti -Def_Nx in Def_cn.
          pose proof marking_flow_upd_summary Ky0 c Nx Mk S I0 res cn 
            Nx_key_rel Hcl KS_mk Disj_insets Nx_dom Out_In Inf_x Out_x
            Def_cn VI Domm_I0 c_in_I0 Keyset_S Insets_c_ne Outsets_c_ne 
            Def_res as [II [nk [-> Hres]]].
          destruct Hres as [Dom_II_sub_I0 [c_in_II [nk_in_II [c_neq_nk 
            [Mk_nk [Mk_x [Nx_x [Key_x [Domm_II [Heq [II_c [II_nk [II_x 
            [Inf_x' [Out_x' [Insets_ne [Dom_out [Out_In' [KS_c 
            [KS_nk KS_x]]]]]]]]]]]]]]]]]]]].
          
          assert (dom I0 = FP s0) as Dom_I0_s0.
          { rewrite Hs0. by unfold FP. }
          iPureIntro. exists II, nk. 
          split; last split; last split; last split; last split; 
            last split; last split; last split; last split; last split; 
            last split; try done.
          - rewrite <-Dom_I0_s0. done.
          - intros H'. destruct (decide (hd = c)) as [Hdc | Hdc].
            + destruct PT_s0 as ((_&H''&_)&_). 
              rewrite Hdc in H''. rewrite Key_c in H''. 
              clear -Range_k H''; lia. 
            + assert (hd ∈ dom II ∖ {[c]}) as H1'.
              { clear -H' Hdc; set_solver. } clear H'.
              apply Key_x in H1'. rewrite Hs0 /Key in Key_c.
              destruct PT_s0 as ((_&H''&_)&_).
              rewrite Hs0 /Key in H''.
              rewrite !lookup_total_alt /inhabitant /= in H1'.
              clear -Key_c H1' H'' Range_k. 
              destruct (Ky0 !! c) eqn: H2'; destruct (Ky0 !! hd) eqn: H2'';
                rewrite H2' in Key_c; rewrite H2'' in H''; simpl in H1'; try lia.
          - intros x Hx Hxc. rewrite -Key_c Hs0 /Key. apply Key_x. 
            clear -Hx Hxc. set_solver.
          - rewrite KS_c; subst S; clear; set_solver.
          - by rewrite Hs0 Heq.
          - intros x Hx Hxc. assert (Hx' := Hx).
            apply Dom_II_sub_I0 in Hx. apply Hflow in Hx.
            destruct Hx as (Hx1&Hx2&Hx3&Hx4&Hx5&Hx6&Hx7&Hx8).
            destruct (decide (x = nk)) as [-> | Hxnk].
            + repeat split. 
              * by apply Domm_II.
              * intros H'. rewrite -Hx2 -I0_eq_s0. apply Dom_out; try done.
                apply Insets_ne; try done.
              * by apply Out_In'.
              * rewrite -Def_Mk lookup_total_alt Mk_nk /=.
                rewrite -Def_Mk lookup_total_alt Mk_nk /= in Hx4. 
                rewrite II_nk inflow_insert_set_outsets inflow_insert_set_insets.
                destruct Hx4 as [Hx4 Hx4']. rewrite I0_eq_s0. split; try done.
                clear -Hx4; set_solver. 
              * rewrite II_nk inflow_insert_set_insets. intros _.
                rewrite elem_of_union. left. rewrite I0_eq_s0. apply Hx5.
                rewrite -I0_eq_s0. by apply Insets_ne.
              * rewrite II_nk inflow_insert_set_insets I0_eq_s0.
                intros k'; rewrite elem_of_union.
                intros [Hk' | Hk']. apply Hx6; try done.
                apply HSk in Hk'. clear -Hk' Range_k; lia.
              * intros k'; by apply Inf_x'.
              * intros n' k'; by apply Out_x'.
            + assert (x ∈ dom II ∖ {[c;nk]}) as Hx1'.
              { clear -Hxc Hx' Hxnk; set_solver. }
              assert (Hx1'' := Hx1'). apply II_x in Hx1'.
              repeat split.
              * by apply Domm_II.
              * intros H'. rewrite -Hx2 -I0_eq_s0. apply Dom_out; try done.
                apply Insets_ne; try done.
              * by apply Out_In'.
              * apply Mk_x in Hx1''. 
                assert (Mk !!! x = true) as H'.
                { by rewrite lookup_total_alt Hx1'' /=. }
                rewrite Def_Mk in H'. rewrite H'.
                rewrite H' in Hx4. rewrite KS_x; try done. 
                by rewrite I0_eq_s0. clear -Hx' Hxnk Hxc; set_solver.
              * rewrite II_x; try done. rewrite outflow_insert_set_insets. 
                rewrite inflow_insert_set_insets. intros _.
                rewrite elem_of_union. left. rewrite I0_eq_s0. apply Hx5.
                rewrite -I0_eq_s0. by apply Insets_ne.
              * rewrite II_x; try done.
                rewrite outflow_insert_set_insets.
                rewrite inflow_insert_set_insets.
                rewrite I0_eq_s0. intros k'; rewrite elem_of_union.
                intros [Hk' | Hk']. apply Hx6; try done.
                apply HSk in Hk'. clear -Hk' Range_k; lia.
              * intros k'; by apply Inf_x'.
              * intros n' k'; by apply Out_x'.
          - apply Hflow in c_in_I0. 
            destruct c_in_I0 as (Hx1&Hx2&Hx3&Hx4&Hx5&Hx6&Hx7&Hx8). repeat split.
            + by apply Domm_II.  
            + intros H'. rewrite -Hx2 -I0_eq_s0. apply Dom_out; try done.
              apply Insets_ne; try done.
            + by apply Out_In'.
            + rewrite KS_c. subst S. clear; set_solver.
            + rewrite II_c outflow_insert_set_insets I0_eq_s0; try done. 
            + rewrite II_c outflow_insert_set_insets I0_eq_s0; try done. 
            + intros k'; by apply Inf_x'. 
            + intros n' k'; by apply Out_x'. }
        set I0' := intf_merge I I0.
        set Mk0' := <[c := mark']> Mk0.
        set s0' := (FP0, C0 ∖ {[k]}, Ht0, Mk0', Nx0, Ky0, I0'): snapshot.
        set M0' := <[T0+1 := s0']> M0.
        assert (abs s0 = C0) as Habs0'.
        { rewrite Hs0. by unfold abs. }
        assert (dom I ⊆ dom I0) as Dom_I_in_I0.
        { destruct Hflupd as (H'&_).
          rewrite Hs0 in H'; unfold FP in H'. by rewrite -Dom_I0 in H'. }
        iAssert (⌜snapshot_constraints s0'⌝)%I as "SShot0'".
        { iPureIntro. exists FP0, (C0 ∖ {[k]}), Ht0, Mk0', Nx0, Ky0, I0'.
          repeat split; try done.
          rewrite /Mk0'. rewrite dom_insert_L.
          assert (c ∈ dom Mk0). 
          { rewrite Hs0 in FP_c0. rewrite Dom_Mk0. by unfold FP in FP_c0. }
          clear -H Dom_Mk0. set_solver.
          rewrite /I0'. rewrite intf_merge_dom; try done. }
        
        assert (FP s0' = FP s0) as FP_s0'.
        { by rewrite Hs0 /s0'; unfold FP. }
        assert (∀ n, Next s0' n = Next s0 n) as HN.
        { by rewrite /Next /s0' Hs0 /=. }
        assert (∀ n, Key s0' n = Key s0 n) as HK.
        { by rewrite /Key /s0' Hs0 /=. }
        assert (∀ n, Height s0' n = Height s0 n) as HT.
        { by rewrite /s0' Hs0 /=. }
        assert (∀ n, n ∈ dom I → FI s0' n = I !!! n) as HI.
        { rewrite /FI /s0' /= /I0'. intros n Hn. 
          rewrite intf_merge_lookup; try done. }
        assert (∀ n, n ∈ dom I0 → n ∉ dom I → FI s0' n = FI s0 n) as HI'.
        { rewrite /FI /s0' Hs0 /= /I0'. intros n Hn Hn'. 
          rewrite intf_merge_lookup_ne; try done. clear -Hn Hn'; set_solver. }
        assert (∀ n, n ≠ c → Mark s0' n = Mark s0 n) as HM.
        { intros n Hnc. by rewrite /FI /s0' Hs0 /Mk0' /= lookup_insert_ne. }
        assert (Mark s0' c = <[0 := true]> (Mark s0 c)) as HMc.
        { rewrite /FI /s0' Hs0 /Mk0' /= lookup_insert Def_mark'.
          by rewrite Hs0 /Mark. }
        assert (FP s0 = dom I0) as FP_I0.
        { by rewrite Hs0 /FP. }

        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> resources _ _ _ γ_ks s0' ∗ ⌜k ∈ abs s0⌝)%I 
          with "[GKS Nodes_KS Node_c Nodes_rest]" as ">(Res & %k_in_s0)".
        { rewrite (big_sepS_delete _ _ c); try done.
          rewrite (big_sepS_delete _ _ nk); last first. 
          { destruct Hflupd as (H'&_&_&H''&H1'&_). apply H' in H''.
            clear -H'' H1'; set_solver. }
          iDestruct "Nodes_KS" as "(KS_c & KS_nk & Nodes_KS)".
          iAssert (⌜k ∈ abs s0⌝)%I as %k_in_s0.
          { iPoseProof (own_valid_2 with "GKS KS_c") as "%H'".
            iDestruct (own_valid with "KS_c") as "%Vc".
            iDestruct (own_valid with "GKS") as "%VKS".
            iPureIntro. apply auth_both_valid_discrete in H'.
            rewrite auth_frag_valid auth_auth_valid in Vc VKS.
            destruct H' as [H' _]. apply auth_ks_included in H'; try done.
            assert (Content s0 c = {[k]}) as Hcont.
            { by rewrite /Content /Marki Mark_c0 Key_c. }
            destruct H' as [? [? [_ [H' _]]]]. rewrite H' Hcont.
            clear; set_solver. } iFrame "%".
          iCombine "KS_c KS_nk" as "KS_cnk".
          iDestruct (own_valid with "KS_cnk") as "%H'".
          iDestruct (own_valid with "GKS") as "%H''".
          rewrite auth_frag_valid in H'. rewrite auth_auth_valid in H''.
          iEval (rewrite (ksRAT_prodKS_op _ _ _ _ H')) in "KS_cnk".
          iMod (own_update_2 γ_ks
                  (● prodKS (KS, abs s0))
                  (◯ prodKS (keyset (FI s0 c) ∪ keyset (FI s0 nk), 
                              Content s0 c ∪ Content s0 nk))
                  ((● prodKS (KS, abs s0 ∖ {[k]})) ⋅
                      (◯ prodKS (keyset (FI s0 c) ∪ keyset (FI s0 nk), 
                              (Content s0 c ∪ Content s0 nk) ∖ {[k]})))
                  with "[$GKS] [$KS_cnk]") as "H'".
          { apply auth_update. apply auth_ks_local_update_delete; try done. 
            - assert (H1' := H'). rewrite ksRAT_prodKS_op in H'; try done.
            - rewrite elem_of_union. left. apply cmra_valid_op_l in H'.
              rewrite /valid /= in H'. unfold cmra_valid in H'. simpl in H'.
              unfold ucmra_valid in H'. simpl in H'. 
              unfold Content, Marki in H'. rewrite Mark_c0 in H'.
              rewrite Key_c in H'. clear -H'; set_solver.
            - rewrite elem_of_union. left. unfold Content, Marki. 
              rewrite Mark_c0 Key_c. clear; set_solver. }
          iDestruct "H'" as "(GKS & H')".
          assert (keyset (FI s0' c) = ∅) as KS_c'. 
          { rewrite /s0' /FI /I0'. rewrite intf_merge_lookup; try done.
            destruct Hflupd as (_&_&_&_&_&_&H2'&_).
            apply H2'. by destruct Hflupd as (_&_&H2'&_). }
          assert (keyset (FI s0' nk) = keyset (FI s0 c) ∪ keyset (FI s0 nk)) 
            as KS_nk'. 
          { assert (FI s0' nk = I !!! nk) as ->.
            { rewrite /s0' /FI /I0'. rewrite intf_merge_lookup; try done.
              by destruct Hflupd as (_&_&_&?&_). }
            assert (FI s0 c = I0 !!! c) as ->.
            { by rewrite Hs0 /FI. }
            assert (FI s0 nk = I0 !!! nk) as ->.
            { by rewrite Hs0 /FI. }
            destruct Hflupd as (_&_&_&_&_&_&_&->&_).
            clear; set_solver. }
          assert (keyset (FI s0 c) ∪ keyset (FI s0 nk) = 
                    keyset (FI s0' c) ∪ keyset (FI s0' nk)) as H1'.
          { rewrite KS_c' KS_nk'. clear; set_solver. }
          assert (Content s0 c = {[k]}) as Cont_c. 
          { unfold Content, Marki. rewrite Mark_c0 Key_c. clear; set_solver. }
          assert (Content s0' c = ∅) as Cont_c'.
          { unfold Content, Marki, Mark. rewrite {1}/s0' /Mk0'.
            rewrite lookup_insert. rewrite Def_mark'.
            by rewrite lookup_total_insert. }
          assert (Content s0' nk = Content s0 nk) as Cont_nk'. 
          { unfold Content, Marki. rewrite /s0' Hs0 /Mark /Key /Mk0'.
            rewrite lookup_insert_ne; try done. 
            by destruct Hflupd as (_&_&_&_&?&_). }
          assert ((Content s0 c ∪ Content s0 nk) ∖ {[k]} = 
                    (Content s0' c ∪ Content s0' nk)) as H1''.
          { assert (k ∉ Content s0 nk) as H1''. 
            { rewrite /Content /Marki. destruct (Mark s0 nk !!! 0); try done.
              destruct Hflupd as (_&_&_&H2'&H2''&H2'''&_).
              clear -H2' H2'' H2'''. intros Hk%elem_of_singleton.
              assert (nk ≠ c) as H' by try done. 
              pose proof H2''' nk H2' H'.  lia. }
            rewrite Cont_c Cont_c' Cont_nk'.
            clear -H1''; set_solver. }
          rewrite H1' H1''. clear H1' H1''.
          iDestruct (own_valid with "H'") as "%H1'".
          rewrite auth_frag_valid in H1'.
          assert (prodKS (keyset (FI s0' c) ∪ keyset (FI s0' nk), 
                            Content s0' c ∪ Content s0' nk) =
                    prodKS (keyset (FI s0' c), Content s0' c) ⋅
                      prodKS (keyset (FI s0' nk), Content s0' nk)) as ->.
          { rewrite KS_c' KS_nk' Cont_c' Cont_nk'. 
            rewrite ksRAT_comm. rewrite ksRAT_unit_op.
            apply f_equal. apply f_equal2; clear; set_solver. }
          iDestruct "H'" as "(KS_c & KS_nk)".
          iModIntro. iSplitL "GKS".
          { by rewrite /s0' Hs0; unfold abs. }
          iSplitL "Node_c Nodes_rest".
          rewrite FP_s0'.
          rewrite (big_sepS_delete _ (FP s0) c); try done.
          iSplitL "Node_c". rewrite Hs0 /s0' /Mark /Next /Key /Mk0'.
          by rewrite lookup_insert.
          iApply (big_sepS_mono with "Nodes_rest"); try done.
          { intros x Hx. rewrite Hs0 /s0' /Mark /Next /Key /Mk0'. 
            rewrite lookup_insert_ne; try done. clear -Hx; set_solver. }
          rewrite FP_s0'.
          rewrite (big_sepS_delete _ (FP s0) c); try done.
          rewrite (big_sepS_delete _ (FP s0 ∖ {[c]}) nk); try done.
          iFrame "KS_c KS_nk". 
          iApply (big_sepS_mono with "Nodes_KS"); try done.
          assert (∀ x, x ∈ FP s0 ∖ {[c; nk]} → 
                    keyset (FI s0' x) = keyset (FI s0 x)) as HKS.
          { intros x Hx. destruct (decide (x ∈ dom I)) as [Hx' | Hx']. 
            rewrite /s0' Hs0 /FI /I0'. rewrite intf_merge_lookup; try done.
            destruct Hflupd as (_&_&_&_&_&_&_&_&H1''&_). apply H1''; try done.
            rewrite elem_of_difference. split; try done.
            rewrite elem_of_difference in Hx. apply Hx.
            rewrite /s0' Hs0 /FI /I0'. rewrite intf_merge_lookup_ne; try done.
            rewrite Hs0 /FP in Hx. rewrite Dom_I0. clear -Hx Hx'; set_solver. } 
          assert (∀ x, x ∈ FP s0 ∖ {[c]} → 
                        Content s0' x = Content s0 x) as Hcont.
          { intros x Hx. rewrite Hs0 /s0' /Content /Marki /Mark /Key /Mk0'.
            rewrite lookup_insert_ne; try done. clear -Hx; set_solver. }
          intros x Hx. rewrite HKS. rewrite Hcont. try done.
          clear -Hx; set_solver. clear - Hx; set_solver.
          rewrite elem_of_difference; split. rewrite Hs0 /FP.
          rewrite -Dom_I0. apply Dom_I_in_I0. by destruct Hflupd as (_&_&_&?&_).
          destruct Hflupd as (_&_&_&_&H1''&_). clear -H1''; set_solver. }

        iAssert (⌜∀ n k, n ∈ FP s0' → k ∈ keyset (FI s0' n) →
          (k ∈ abs s0' ↔ k ∈ Content s0' n)⌝)%I as "%Hks".
        { iDestruct "Res" as "(GKS & _ & HKS)".
          iPoseProof (keyset_summary with "GKS HKS") as "%H'"; try done. }
          
        assert (per_tick_inv hd tl s0') as PT_s0'.
        { destruct PT_s0 as (PT1&PT2&PT3&PT4&PT5&PT6&PT7).
          split; last split; last split; last split; last split; last split.
          - rewrite FP_s0' !HK !HN !HT !HM; try done. 
          - rewrite /GFI FP_s0'.
            assert (([^op set] x ∈ FP s0, FI s0' x) 
              = ([^op set] x ∈ FP s0, I0' !!! x)) as ->.
            { apply big_opS_ext. intros x Hx'.
              by rewrite /s0' /FI /=. }
            unfold GFI in PT2.
            assert (([^op set] x ∈ FP s0, I0' !!! x) 
              = ([^op set] x ∈ FP s0, FI s0 x)) as ->; last done.
            rewrite {1 3}Hs0 /FP -Dom_I0.
            assert (([^op set] x ∈ dom I0, FI s0 x) 
              = ([^op set] x ∈ dom I0, I0 !!! x)) as ->.
            { apply big_opS_ext. intros x Hx'.
              by rewrite Hs0 /FI /=. }
            symmetry. apply (intf_merge_intfEq I); try done.
            assert (([^op set] x ∈ dom I, I0 !!! x)
              = ([^op set] x ∈ dom I, FI s0 x)) as ->.
            { apply big_opS_ext. intros x Hx.
              rewrite Hs0; unfold FI; try done. }
            by apply Hflupd.
          - done.
          - rewrite FP_s0' FP_I0. intros n Hn. assert (Hnn := Hn).
            rewrite FP_I0 in PT4. apply PT4 in Hn.
            destruct (decide (n ∈ dom I)) as [Hn' | Hn'].
            + destruct (decide (n = c)) as [-> | Hnc].
              * rewrite HN HT HK HI; try done. rewrite HMc.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split; try done.
                { intros [i Hi]. destruct (decide (i = 0)) as [-> | Hi'].
                  by rewrite lookup_total_insert in Hi.
                  rewrite lookup_total_insert_ne in Hi; try done.
                  rewrite /Marki in Marki_c. assert (Hii := Hi).
                  rewrite Marki_c in Hi. done.
                  rewrite lookup_total_alt in Hii. 
                  destruct (Mark s0 c !! i) as [mc | ] eqn: Hmc.
                  apply elem_of_dom_2 in Hmc. rewrite Hn3 elem_of_gset_seq in Hmc.
                  clear -Hn4 Hmc Hi'. lia. rewrite Hmc /= in Hii. done. }
                { rewrite dom_insert_L Hn3. 
                  assert (0 ∈ gset_seq 0 (Height s0 c - 1)) as H'. 
                  { rewrite elem_of_gset_seq; lia. } clear -H'; set_solver. }
                { rewrite lookup_total_insert. apply Hflupd. }
              * rewrite HN HT HK HI; try done. rewrite HM; try done.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
                split; last split; last split; last split; last split; try done.
                apply Hflupd. done. done.
            + rewrite HN HT HK HI'. rewrite HM. all: try done.
              assert (c ∈ dom I) as H' by (apply Hflupd).
              clear -H' Hn'; set_solver.
          - intros n1 n2. rewrite /Nexti HN !HK. apply PT5.
          - intros n1 n2 i. rewrite /Nexti HN FP_s0'. apply PT6.
          - intros n1 n2 i. rewrite /Nexti HN HT. apply PT7. }
        
        assert (transition_inv s0 s0') as Trans_s0.
        { repeat split.
          - intros n i. rewrite /Nexti HN. clear; try done.
          - intros n. destruct (decide (n = c)) as [-> | Hcn].
            + intros _ _. rewrite Key_c /s0' /abs. clear; set_solver.
            + rewrite /Marki HM. intros H' H''. rewrite H' in H''; done. done.
          - intros n i FP_n. 
            destruct (decide (n = c)) as [-> | Hcn].
            + rewrite /Marki HMc. intros Hm.
              destruct (decide (i = 0)) as [-> | Hi0].
              * by rewrite lookup_total_insert.
              * rewrite lookup_total_insert_ne; try done.
            + rewrite /Marki HM; try done.
          - intros. by rewrite HT.
          - intros. by rewrite HK.
          - by rewrite FP_s0'. }
        
        iAssert (⌜dom M0 = gset_seq 0 T0⌝)%I as %Dom_M0. 
        { by iDestruct "Hist" as (M0'') "(_&_&%&_)". }
        
        assert (seq_spec (deleteOp k) (abs s0) (abs s0') true) as Hss.
        { rewrite Hs0 /s0' /abs. rewrite Hs0 /abs /= in k_in_s0. 
          clear -k_in_s0. set_solver. }
        iAssert (|==> hist _ _ _ _ γ_t γ_m M0' (T0+1))%I with "[Hist]" as ">Hist".
        { iPoseProof (hist_upd _ _ _ _ _ _ _ _ _ s0' with "[%] [%] [$Hist]") as ">H'".
          apply  Habs0. intros <-. rewrite map_eq_iff in HMc.
          pose proof HMc 0 as HMc. rewrite lookup_insert in HMc.
          apply lookup_total_correct in HMc. rewrite Mark_c0 in HMc.
          clear -HMc; done. by rewrite /M0'. }
        assert (∀ t, 0 ≤ t ≤ T0+1 → per_tick_inv hd tl (M0' !!! t)) as PT0'.
        { intros t Ht. destruct (decide (t = T0 + 1)) as [-> | Ht'].
          + by rewrite lookup_total_insert.
          + rewrite lookup_total_insert_ne; try done.
            apply PT0. clear -Ht Ht'; lia. }
        assert ((∀ t, 0 <= t < T0 + 1 → 
          transition_inv (M0' !!! t) (M0' !!! (t + 1)))) as Trans_M0'.
        { intros t Ht. destruct (decide (t = T0)) as [-> | Ht'].
          + rewrite lookup_total_insert. 
            rewrite lookup_total_insert_ne; last by lia.
            apply leibniz_equiv in Habs0. by rewrite Habs0.
          + rewrite !lookup_total_insert_ne; try lia.
            apply Trans_M0. clear -Ht Ht'; lia. }
        
        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> Φ #true ∗ dsRepI _ _ _ _ γ_r (abs s0'))%I 
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
          helping_inv _ _ _ _ N γ_t γ_r γ_mt γ_msy M0' ∗ dsRep _ _ _ _ γ_r (abs s0'))%I with
          "[Help Ds]" as ">(Help & Ds)".
        { iMod (fupd_mask_subseteq (⊤ ∖ ↑cntrN N)) as "H'". { clear; set_solver. }
          iPoseProof ("Upd" with "[%] [Ds] [Help]") as ">Help"; try done.
          apply leibniz_equiv in Habs0. iMod "H'" as "_". by iModIntro. }
        iModIntro. iSplitR "Hpreds Hsuccs HΦ".
        { iNext. iExists M0', (T0+1)%nat, s0'. iFrame "∗#%". 
          iSplitR. iPureIntro. by rewrite lookup_total_insert. 
          iExists hd, tl. iFrame "∗#%". }
        wp_pures. 
        wp_apply (traverse_rec_spec with "[] [] [] [] [] [Hpreds Hsuccs]"); 
          try done.
        { iFrame "Hpreds Hsuccs".
          repeat (try iSplit; first by iPureIntro).
          iSplit. iPureIntro; clear -HL; lia.
          repeat (try iSplit; first by iPureIntro).
          iIntros (j) "%Hj". 
          assert (j = L-1) as -> by lia. rewrite HpsL HssL. iFrame "HtrL". admit. }
        iIntros (???)"_". wp_pures. done.
      + iDestruct "Hif" as "%H'". destruct H' as [Mark_c0 [-> Def_pvs]].
        iDestruct "Htr" as "(_&Htr)". 
        iDestruct "Htr" as (s)"(Past_s & %H')".
        apply list_lookup_total_correct in Hss0. rewrite Hss0 in H'.
        iAssert (⌜Mark s c !!! 0 = false⌝)%I as %Mark_cs. 
        { destruct H' as (H'&H''&H''').
          iPoseProof (per_tick_past with "[%] Hist Past_s") as "%PT_s"; try done.
          apply PT_s in H'. destruct H' as (_&_&_&_&_&H').
          destruct H' as (_&_&_&H'&_). rewrite /Marki. 
          destruct (Mark s c !!! 0); try done. rewrite H' in H''. 
          clear -H''; set_solver. }
        iDestruct "Past_s" as (ts)"(%Ht0_ts & #Hts)". 
        assert (c ∈ FP s) as FP_cs. { apply H'. }
        iPoseProof (marking_witness _ _ _ _ c 0 with "[%] [$Hist] [$Hts] [%] [%] [%]") 
          as "%H''"; try done. apply leibniz_equiv in Habs0. by rewrite Habs0.
        destruct H'' as [t [Ht [Mark_ct Mark_cst]]].
        iPoseProof (snapshot_create _ _ _ _ (S t) t0 with "[%] [$Hist]") 
          as ">(#Past_St&Hist)"; try (done || lia).
        iPoseProof (snapshot_create _ _ _ _ (t) t0 with "[%] [$Hist]") 
          as ">(#Past_t&Hist)"; try (done || lia).
        iAssert (⌜Key (M0 !!! t) c = k⌝)%I as %Hk.
        { assert (k = Key s c) as ->. 
          { destruct H' as (H'&H''&H'''). rewrite /Content /Marki Mark_cs in H'''.
            clear -H'''; set_solver. }
          iPoseProof (key_eq _ _ _ _ c with "[%] [$Hist] [$Hts] [%]") as "->"; 
            try done. lia. }
        assert (k ∉ abs (M0 !!! S t)) as Hk'.
        { assert (0 <= t < T0) as H'' by lia. apply Trans_M0 in H''.
          destruct H'' as (_&H''&_). rewrite -Hk -Nat.add_1_r. apply H''; try done.
          rewrite Nat.add_1_r. done. }
        iAssert (past_lin_witness _ _ _ _ γ_m (deleteOp k) false t0) as "#PastW".
        { iExists (M0 !!! S t). iFrame "#". iPureIntro. clear -Hk'; set_solver. } 
        iAssert (|={⊤ ∖ ∅ ∖ ↑cntrN N}=> Φ #false)%I 
          with "[Hpost Hmatch Hproph]" as ">HΦ".
        { destruct (process_proph tid pvs) eqn: Hpres.
          - iApply ("Hpost" $! false prf pvs'). iFrame "Hproph". iPureIntro.
            split; try done. apply (Forall_impl _ _ _ Hprf).
            intros [x1 x2]. intros [v1' [=]]. by subst x2.
          - iApply ("Hpost" $! false prf pvs'). iFrame "Hproph". iSplitR. 
            iPureIntro. done. iRight. iPureIntro. apply (Forall_impl _ _ _ Hprf).
            intros [x1 x2]. intros [v1 [=]]. subst x1 x2. split; try done.
            rewrite /is_snd /=. intros [? [=]].
          - iApply ("Hpost" $! false prf pvs'). iFrame "Hproph #".
            by iPureIntro. }
        iModIntro. iSplitR "Hpreds Hsuccs HΦ".
        { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%". 
          rewrite (big_sepS_delete _ (FP s0) c); try done. iFrame. }
        by wp_pures.
    - iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      iDestruct "Templ" as (hd' tl')"(HR & SShot0 & Res & %PT0 & %Trans_M0)".
      iAssert (⌜hd' = hd ∧ tl' = tl⌝)%I with "[HR]" as %[-> ->]. 
      { iDestruct (mapsto_agree with "[$HR] [$HR']") as %[=]. by iPureIntro. }  
      iAssert (past_lin_witness _ _ _ _ γ_m (deleteOp k) false t0)%I as "#PastW".
      { iDestruct "Htr" as "(_ & Htr)". 
        iDestruct "Htr" as (s)"(#Past_s & %H')". 
        set c := ss !!! 0. rewrite -/c in H'.
        iPoseProof (per_tick_past with "[%] Hist Past_s") as "%PT_s"; try done.
        assert (k ∉ abs s) as k_notin_s.
        { destruct H' as (H' & H'' & H'''). destruct PT_s as (_&_&PT&_).
          pose proof PT c k H' H'' as H1'. set_solver. }
        iExists s. iFrame "#". iPureIntro. set_solver. }
      iModIntro. iSplitR "Hproph Hmatch Hpost".
      { iNext. iExists M0, T0, s0. iFrame "∗%". iExists hd, tl. iFrame "∗%". }
      destruct (process_proph tid pvs) eqn: Hpvs.
      + iApply ("Hpost" $! false [] pvs). iFrame "Hproph". by iPureIntro.
      + iApply ("Hpost" $! false [] pvs). iFrame "Hproph". iSplitR. by iPureIntro.
        iRight. by iPureIntro.
      + iApply ("Hpost" $! false [] pvs). iFrame "Hproph #". done.
      Unshelve. try done.
  Admitted.

End SKIPLIST_DELETE.