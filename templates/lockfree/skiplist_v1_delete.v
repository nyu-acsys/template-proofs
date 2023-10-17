(* Herlihy Skiplist with a single level : Delete *)

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
Require Export skiplist_v1_util list_flow_upd_marking.

Module SKIPLIST1_SPEC_DELETE.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS SKIPLIST1_UTIL.


  Parameter markNode_spec : ∀ (n: Node) (i: nat),
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

  Definition traversal_inv s i k p c : Prop :=
    p ∈ FP s 
  ∧ c ∈ FP s 
  ∧ Key s p < k 
  ∧ Marki s p i = false 
  ∧ Nexti s p i = Some c
  ∧ i < Height s p
  ∧ i < Height s c.

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
  Admitted.

  Lemma maintenanceOp_delete_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght t0 c:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        {{{ ∃ s, past_state γ_m t0 s ∗ ⌜c ∈ FP s⌝ }}}
           maintenanceOp_delete #c
        {{{ RET #();
              (∃ s h, past_state γ_m t0 s ∗ ⌜c ∈ FP s⌝ ∗ ⌜h = Height s c⌝
                    ∗ ⌜∀ i, 1 ≤ i < h → Marki s c i = true⌝) }}}.
  Proof.
  Admitted.

  Lemma deleteOp_spec N γ_r γ_t γ_m γ_td1 γ_td2 γ_ght γ_sy t_id t0 k:
          main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
          □ update_helping_protocol N γ_t γ_r γ_td1 γ_td2 γ_ght -∗
          thread_vars γ_t γ_ght γ_sy t_id t0 -∗
            {{{ True }}} 
                delete #hd #tl #k
            {{{ res, RET #res; past_lin_witness γ_m (deleteOp k) res t0 }}}.
  Proof.
    iIntros "#HInv #HUpd #Thd". iIntros (Φ) "!# AU Hpost".
    assert (0 < k < W) as Range_k. { admit. }
    assert (1 < L) as HL. { admit. }
    wp_lam. wp_pures. 
    wp_apply traverse_spec; try done.
    iIntros (preds succs ps ss res) "(Hpreds & Hsuccs & #HtrInv)".  
    wp_pures. destruct res; wp_pures.
    - assert (is_Some(ss !! 0)) as [c Hss0].
      { rewrite lookup_lt_is_Some. admit. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        ((λ n : loc, #n) <$> ss) #c with "[Hsuccs]"); try done.
      { by rewrite list_lookup_fmap Hss0 /=. }
      { iNext. unfold is_array. admit. }
      iIntros "Hsuccs". wp_pures.
      wp_apply (maintenanceOp_delete_spec with "[] []"); try done.
      { iAssert (⌜0 < L⌝)%I as "H'". by (iPureIntro; lia).
        iPoseProof ("HtrInv" with "H'") as "H''". 
        iDestruct "H''" as (s)"#(Hpast & %Htr & %H')". rewrite -/c in Htr.
        iExists s; iFrame "#". apply list_lookup_total_correct in Hss0.
        rewrite Hss0 in Htr. iPureIntro; apply Htr. }
      iIntros "#Hmnt". wp_pure credit:"Hcred". wp_pures.
      awp_apply markNode_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iDestruct "Nodes" as "(Node_c & Nodes_rest)".
      iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
      { iDestruct "Hist" as (M')"(_&_&_&%&_)". iPureIntro.
        apply leibniz_equiv in Habs0. rewrite <-Habs0.
        by apply PT0. }
      iAssert ((node c (Height s0 c) (Mark s0 c) (Next s0 c) (Key s0 c)) 
        ∗ ⌜0 < Height s0 c⌝)%I with "[Node_c]" as "Hpre".
      { iFrame "Node_c". iPureIntro. apply PT_s0 in FP_c0. apply FP_c0. }
      iAaccIntro with "Hpre".
      { iIntros "(Node_c & _)". iModIntro. 
        iSplitR "AU Hcred Hpreds Hsuccs Hpost"; try done.
        iNext; iExists M0, T0, s0. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) c); try done. 
        iFrame. iFrame. }
      iIntros (success mark')"(Node_c & Hif)".
      iApply (lc_fupd_add_later with "Hcred"). iNext.
      iAssert (∀ i, ⌜1 ≤ i < L → Marki s0 c i = true⌝)%I as "%Marki_c".
      { apply leibniz_equiv in Habs0. rewrite <-Habs0.
        (*
        iDestruct "Hmnt" as (s)"(Past_s & %c_in_s & %H')".
        iIntros (i). iDestruct "Past_s" as (ts)"(% & Past_c)". 
        iPoseProof (marking_mono c i with "[%] [$Hist] [] [%]") as "%H''"; 
          try done.
        iPureIntro. intros Hi. apply H''. apply H'. try done.*) admit. }
      destruct success.
      + iDestruct "Hif" as %[Mark_c0 Def_mark'].
        iDestruct "SShot0" as %[FP0 [C0 [Ht0 [Mk0 [Nx0 [Ky0 [I0 
          [Hs0 [Dom_Ht0 [Dom_Mk0 [Dom_Nx0 [Dom_Ky0 Dom_I0]]]]]]]]]]]].
        assert (∀ x, x ∈ FP s0 → flow_constraints_I x (FI s0 x) 
                  (Mark s0 x !!! 0) (Next s0 x !! 0) (Key s0 x)) as Hflow.
        { destruct PT_s0 as (_&_&H'&_).
          intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&_&?). }
        iAssert (⌜Key s0 c = k⌝)%I as %Key_c. 
        { apply leibniz_equiv in Habs0. rewrite <-Habs0.
          (* iDestruct "Htr" as (s)"(Past_s & _ & %c_in_s & _ & ->)".
          iDestruct "Past_s" as (ts)"(% & Past_c)".
          iApply (key_eq with "[%] [$Hist] [] [%]"); try done.*) admit. }
        iAssert (⌜∃ cn, Nexti s0 c 0 = Some cn⌝)%I as %[cn Def_cn].
        { destruct PT_s0 as ((_&_&Hk&_)&_&H'&_). apply H' in FP_c0.
          destruct FP_c0 as (_&H''&_). iPureIntro.
          destruct (Nexti s0 c 0) as [n' | ] eqn: Hn'. by exists n'.
          rewrite /Nexti in Hn'. apply H'' in Hn'. rewrite Hn' Hk in Key_c.
          clear -Key_c Range_k; lia. }
        
        set S := keyset (I0 !!! c).

        assert (∀ x, I0 !!! x = FI s0 x) as I0_eq_s0.
        { intros x. rewrite Hs0; unfold FI. try done. }
        assert (∀ k', k' ∈ S → k' ≤ k) as HSk.
        { rewrite Hs0 /FP in FP_c0. rewrite {1}Hs0 /FP in Hflow.
          apply Hflow in FP_c0. rewrite /Marki Mark_c0 in FP_c0.
          destruct FP_c0 as (_&_&_&H1'&H2'&_&_).
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
        { assert (∃ (Nx: gmap Node Node), ∀ x, Nx !! x = Next s0 x !! 0)
            as [Nx Def_Nx].
          { set f_Nx := λ (n: Node) (nx: gmap nat Node) (res: gmap Node Node), 
                        match nx !! 0 with None => res 
                                        | Some n' => <[n := n']> res end.
            set Nx : gmap Node Node := map_fold f_Nx ∅ Nx0.
            exists Nx. rewrite Hs0. unfold Nexti, Next.
            set P := λ (res: gmap Node Node) (m: gmap Node (gmap nat Node)),
                (∀ x: Node, res !! x = 
                  (match m !! x with Some mn => mn | None => ∅ end) !! 0).
            apply (map_fold_ind P); try done.
            intros n Nx_n m res Hmn HP. unfold P. unfold P in HP.
            intros n'. unfold f_Nx. 
            destruct (decide (n' = n)) as [-> | Hn'].
            - destruct (Nx_n !! 0) as [Nx_n0 | ] eqn:Hn0.
              + rewrite !lookup_insert. by rewrite Hn0.
              + rewrite lookup_insert. rewrite Hn0.
                by rewrite (HP n) Hmn.
            - destruct (Nx_n !! 0) as [Nx_n0 | ] eqn:Hn0.
              + rewrite !lookup_insert_ne; try done.
              + rewrite (HP n'). by rewrite lookup_insert_ne. }  
          assert (∃ (Mk: gmap Node bool), ∀ (x: Node), Mk !! x = Mark s0 x !! 0)
            as [Mk Def_Mk'].
          { set f_Mk := λ (n: Node) (nx: gmap nat bool) (res: gmap Node bool), 
                        match nx !! 0 with None => res 
                                        | Some n' => <[n := n']> res end.
            set Mk : gmap Node bool := map_fold f_Mk ∅ Mk0.
            exists Mk. rewrite Hs0. unfold Mark.
            set P := λ (res: gmap Node bool) (m: gmap Node (gmap nat bool)),
              ∀ x: Node, res !! x = 
                (match m !! x with Some mn => mn | None => ∅ end) !! 0.
            apply (map_fold_ind P); try done.
            intros n Mk_n m res Hmn HP. unfold P. unfold P in HP.
            intros n'. unfold f_Mk. 
            destruct (decide (n' = n)) as [-> | Hn'].
            - destruct (Mk_n !! 0) as [Mk_n0 | ] eqn:Hn0.
              + rewrite !lookup_insert. by rewrite Hn0.
              + rewrite lookup_insert. rewrite Hn0. 
                by rewrite (HP n) Hmn.
            - destruct (Mk_n !! 0) as [Mk_n0 | ] eqn:Hn0.
              + rewrite !lookup_insert_ne; try done. 
              + rewrite (HP n'). by rewrite lookup_insert_ne. }
          assert (∀ x, Mk !!! x = Mark s0 x !!! 0) as Def_Mk.
          { intros n. rewrite lookup_total_alt. by rewrite Def_Mk'. }
          assert (dom Nx = dom Nx0) as Dom_Nx.
          { apply set_eq_subseteq; split.
            - intros n. rewrite !elem_of_dom. rewrite Def_Nx.
              rewrite Hs0. unfold Nexti, Next.
              destruct (Nx0 !! n) eqn: H'; try done.
              rewrite H'. rewrite lookup_empty. 
              intros [? H'']; try done.
            - intros n. rewrite !elem_of_dom. rewrite Def_Nx.
              rewrite Hs0. unfold Nexti, Next.
              destruct (Nx0 !! n) eqn: H'; try done.
              rewrite H'. intros _.
              assert (H1' := H'). 
              apply elem_of_dom_2 in H'.
              rewrite Dom_Nx0 in H'.
              destruct PT_s0 as (_&_&PT&_).
              rewrite {1}Hs0 in PT. unfold FP in PT.
              apply PT in H'. destruct H' as (_&_&H'&_).
              rewrite Hs0 /Next H1' in H'. rewrite -elem_of_dom H'.
              rewrite elem_of_gset_seq. clear; lia.
              intros [? H'']; try done. }
          assert (dom Mk = dom Mk0) as Dom_Mk.
          { apply set_eq_subseteq; split.
            - intros n. rewrite !elem_of_dom. rewrite Def_Mk'.
              rewrite Hs0. unfold Mark.
              destruct (Mk0 !! n) eqn: H'; try done.
              rewrite H'. rewrite lookup_empty. 
              intros [? H'']; try done.
            - intros n. rewrite !elem_of_dom. rewrite Def_Mk'.
              rewrite Hs0. unfold Mark.
              destruct (Mk0 !! n) eqn: H'; try done.
              rewrite H'. intros _.
              assert (H1' := H'). 
              apply elem_of_dom_2 in H'.
              rewrite Dom_Mk0 in H'.
              destruct PT_s0 as (_&_&PT&_).
              rewrite {1}Hs0 in PT. unfold FP in PT.
              apply PT in H'. destruct H' as (_&_&_&H'&_).
              rewrite Hs0 /Mark H1' in H'.
              rewrite -elem_of_dom H' elem_of_gset_seq. clear; lia.
              intros [? H'']; try done. }
          assert (∀ x, Ky0 !!! x = Key s0 x) as Def_Ky0.
          { rewrite Hs0. unfold Key. try done. }
          
          assert (nx_key_rel Nx Ky0) as Nx_key_rel.
          { destruct PT_s0 as (_&_&_&H'&_). intros n1 n2.
            rewrite !Def_Nx !Def_Ky0. apply H'. }
          assert (nx_mk_closed Nx Mk (dom I0)) as Hcl.
          { split; last split. 
            - rewrite Dom_Nx. clear -Dom_Nx0 Dom_I0; set_solver.
            - rewrite Dom_Mk. clear -Dom_Mk0 Dom_I0; set_solver.
            - destruct PT_s0 as (_&_&_&_&H'). intros n1 n2.
              rewrite {2}Hs0 in H'. unfold FP in H'.
              rewrite !Def_Nx Dom_I0. apply H'. }
          assert (✓ ([^op set] x ∈ dom I0, (I0 !!! x: multiset_flowint_ur nat))) 
            as VI.
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
          { intros n1 n2 Hin Nx_n1.
            assert (n1 ∈ dom I0) as H'.
            { apply elem_of_dom_2 in Nx_n1. by rewrite Dom_I0 -Dom_Nx0 -Dom_Nx. }
            apply Hflow in H'. destruct H' as (_&H'&_).
            rewrite -Def_Nx Nx_n1 -I0_eq_s0 in H'. by apply H' in Hin. }
          assert (S ⊆ keyset (I0 !!! c)) as Keyset_S.
          { subst S; clear; set_solver. }
          set res := list_flow_upd_marking c Nx Mk S I0.
          assert (list_flow_upd_marking c Nx Mk S I0 = res) as Def_res by try done.
          
          assert (∀ n1 n2, n1 ∈ dom I0 → n2 ∈ dom I0 → 
                    n1 ≠ n2 → keyset (I0 !!! n1) ## keyset (I0 !!! n2)) as Disj_KS.
          { admit. }
          assert (∀ x, x ∈ dom I0 → Mk !!! x = false → 
            Ky0 !!! c < Ky0 !!! x → S ## outsets (I0 !!! x)) as Disj_outsets.
          { intros x Hx Mk_x Hkey. rewrite elem_of_disjoint. intros k' Hk1' Hk2'.
            destruct PT_s0 as (_&_&H'&_). rewrite {1}Hs0 /FP -Dom_I0 in H'.
            apply H' in Hx. destruct Hx as (_&_&_&_&_&Hx&Hx'). 
            rewrite /Marki in Def_Mk. rewrite -Def_Ky0 -Def_Mk Mk_x in Hx'. 
            destruct Hx' as (_&_&_&Hx'&_).
            destruct Hx' as [Hx1 Hx2]. rewrite I0_eq_s0 -Hx2 in Hk2'.
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
          { intros x k' Hx%Hflow. destruct Hx as (_&_&_&_&_&H'&_).
            rewrite I0_eq_s0. apply H'. }
          assert (∀ x x' k, x ∈ dom I0 → 
            out ((I0 !!! x):multiset_flowint_ur _) x' !!! k ≤ 1) as Out_x.
          { intros x x' k' Hx%Hflow. destruct Hx as (_&_&_&_&_&_&H').
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
            [Inf_x' [Out_x' [Dom_out [Out_In' [KS_c 
            [KS_nk KS_x]]]]]]]]]]]]]]]]]]].
          
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
            destruct Hx as (Hx1&Hx2&Hx3&Hx4&Hx5&Hx6&Hx7).
            destruct (decide (x = nk)) as [-> | Hxnk].
            + repeat split. 
              * by apply Domm_II.
              * intros H'. assert (insets (FI s0 nk) ≠ ∅) as H''.
                admit. apply Hx2 in H''. rewrite Dom_out. 
                rewrite I0_eq_s0; try done. done.
              * by apply Out_In'.
              * rewrite -Def_Mk lookup_total_alt Mk_nk /=.
                rewrite -Def_Mk lookup_total_alt Mk_nk /= in Hx4. 
                rewrite II_nk inflow_insert_set_outsets inflow_insert_set_insets.
                destruct Hx4 as [Hx4 Hx4']. rewrite I0_eq_s0. split; try done.
                clear -Hx4; set_solver. 
              * rewrite II_nk inflow_insert_set_insets I0_eq_s0.
                intros k'; rewrite elem_of_union.
                intros [Hk' | Hk']. apply Hx5; try done.
                apply HSk in Hk'. clear -Hk' Range_k; lia.
              * intros k'; by apply Inf_x'.
              * intros n' k'; by apply Out_x'.
            + assert (x ∈ dom II ∖ {[c;nk]}) as Hx1'.
              { clear -Hxc Hx' Hxnk; set_solver. }
              assert (Hx1'' := Hx1'). apply II_x in Hx1'.
              repeat split.
              * by apply Domm_II.
              * intros H'. assert (insets (FI s0 x) ≠ ∅) as H''.
                admit. apply Hx2 in H''. rewrite Dom_out. 
                rewrite I0_eq_s0; try done. done.
              * by apply Out_In'.
              * apply Mk_x in Hx1''. rewrite Def_Mk' in Hx1''.
                apply lookup_total_correct in Hx1''. rewrite Hx1''.
                rewrite Hx1'' in Hx4. rewrite KS_x; try done. 
                by rewrite I0_eq_s0. clear -Hx' Hxnk Hxc; set_solver.
              * rewrite II_x; try done.
                rewrite outflow_insert_set_insets.
                rewrite inflow_insert_set_insets.
                rewrite I0_eq_s0. intros k'; rewrite elem_of_union.
                intros [Hk' | Hk']. apply Hx5; try done.
                apply HSk in Hk'. clear -Hk' Range_k; lia.
              * intros k'; by apply Inf_x'.
              * intros n' k'; by apply Out_x'.
          - apply Hflow in c_in_I0. 
            destruct c_in_I0 as (Hx1&Hx2&Hx3&Hx4&Hx5&Hx6&Hx7). repeat split.
            + by apply Domm_II.  
            + rewrite Dom_out. rewrite I0_eq_s0; try done.
              assert (insets (II !!! c) = insets (FI s0 c)) as ->.
              admit. done. done.
            + by apply Out_In'.
            + rewrite KS_c. subst S. clear; set_solver.
            + rewrite II_c outflow_insert_set_insets I0_eq_s0; try done. 
            + intros k'; by apply Inf_x'. 
            + intros n' k'; by apply Out_x'. }
        set I0' := intf_merge I I0.
        set Mk0' := <[c := mark']> Mk0.
        set s0' := (FP0, C0 ∖ {[k]}, Ht0, Mk0', Nx0, Ky0, I0'): snapshot.
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
        assert (c ≠ hd) as c_neq_hd.
        { destruct Hflupd as (_&H'&H''&_).
          clear -H' H''; intros ->; set_solver. }
        assert (FP s0 = dom I0) as FP_I0.
        { by rewrite Hs0 /FP. }
        assert (c ≠ tl) as c_neq_tl. admit.
        
        assert (per_tick_inv s0') as PT_s0'.
        { destruct PT_s0 as (PT1&PT2&PT3&PT4&PT5&PT6).
          split; last split; last split; last split; last split.
          - destruct PT1 as (PT11&PT12&PT13&PT14&PT15). repeat split. 
            + intros ?; rewrite /Marki HM; try done. apply PT11.
            + by rewrite HK.
            + by rewrite HK.
            + by rewrite FP_s0'.
            + by rewrite FP_s0'.
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
          - rewrite FP_s0' FP_I0. intros n Hn. assert (Hnn := Hn).
            rewrite FP_I0 in PT3. apply PT3 in Hn.
            destruct (decide (n ∈ dom I)) as [Hn' | Hn'].
            + destruct (decide (n = c)) as [-> | Hnc].
              * rewrite HN HT HK HI; try done. rewrite HMc.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6&Hn7).
                split; last split; last split; last split; last split; 
                  last split; try done.
                { intros [i Hi]. destruct (decide (i = 0)) as [-> | Hi'].
                  by rewrite lookup_total_insert in Hi.
                  rewrite lookup_total_insert_ne in Hi; try done.
                  rewrite /Marki in Marki_c. assert (Hii := Hi).
                  rewrite Marki_c in Hi. done. admit. }
                { rewrite dom_insert_L Hn4. admit. }
                { rewrite lookup_total_insert. apply Hflupd. }
              * rewrite HN HT HK HI; try done. rewrite HM; try done.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6&Hn7).
                split; last split; last split; last split; last split; 
                  last split; try done.
                apply Hflupd. done. done.
            + rewrite HN HT HK HI'. rewrite HM. all: try done.
              assert (c ∈ dom I) as H' by (apply Hflupd).
              clear -H' Hn'; set_solver.
          - intros n1 n2 i. rewrite /Nexti HN !HK. apply PT4.
          - intros n1 n2 i. rewrite /Nexti HN FP_s0'. apply PT5.
          - intros n1 n2 i. rewrite /Nexti HN HT. apply PT6. }
        
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
        iAssert (|={⊤ ∖ ⊤ ∖ ↑cntrN N}=> resources γ_ks s0')%I 
          with "[GKS Nodes_KS Node_c Nodes_rest]" as ">Res".
        { rewrite (big_sepS_delete _ _ c); try done.
          rewrite (big_sepS_delete _ _ nk); last first. 
          { destruct Hflupd as (H'&_&_&H''&H1'&_). apply H' in H''.
            clear -H'' H1'; set_solver. }
          iDestruct "Nodes_KS" as "(KS_c & KS_nk & Nodes_KS)".
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
        iAssert (dsRepI γ_r (abs s0'))%I with "[Ds]" as "Ds".
        { admit. }
        iAssert (helping_inv N γ_t γ_r γ_td1 γ_td2 γ_ght (<[(T0+1)%nat:=s0']>M0))%I 
          with "[Help]" as "Help".
        { admit. }
        iAssert (hist γ_t γ_m (<[(T0+1)%nat := s0']> M0) (T0+1)%nat)%I
          with "[Hist]" as "Hist".
        { admit. }
        iModIntro. iSplitR "AU".
        { iNext. iExists (<[(T0+1)%nat := s0']> M0), (T0+1)%nat, s0'.
          iFrame. iDestruct "SShot0'" as %SShot0'.
          iPureIntro. split; last split; last split.
          - by rewrite lookup_total_insert.
          - done.
          - intros t Ht. destruct (decide (t = T0 + 1)) as [-> | Ht'].
            + by rewrite lookup_total_insert.
            + rewrite lookup_total_insert_ne; try done.
              apply PT0. rewrite dom_insert in Ht.
              clear -Ht Ht'; set_solver.
          - intros t Ht. destruct (decide (t = T0)) as [-> | Ht'].
            + rewrite lookup_total_insert. 
              rewrite lookup_total_insert_ne; last by lia.
              apply leibniz_equiv in Habs0. by rewrite Habs0.
            + rewrite !lookup_total_insert_ne; try lia.
              apply Trans_M0. clear -Ht Ht'; lia. }
        wp_pures. clear Hflupd.
        admit.
      + iDestruct "Hif" as "%H'". destruct H' as [Mark_s0c ->].
        iAssert (past_lin_witness γ_m (deleteOp k) false t0)%I as "#PastW".
        { admit.
          (*
          iDestruct "Htr" as (s)"(Past_s & _ & %c_in_s & _)".
          assert (Marki s c 0 = false) as Mark_sc. admit.
          assert (Marki (M0 !!! T0) c 0 = true) as Mark_s0c'. 
          { unfold Marki. apply leibniz_equiv in Habs0. by rewrite Habs0. }
          iDestruct (marking_witness with "[%] [$Hist] [] [%] [%] [%]") 
            as "%H'"; try done.
          destruct H' as [t [Ht [H' H'']]].
          assert (0 ≤ t < T0) as Ht' by lia.
          apply Trans_M0 in Ht'.
          destruct Ht' as (Ht' & _).
          assert (t + 1 = S t) as H1' by lia. rewrite H1' in Ht'. clear H1'.
          pose proof Ht' c H' H'' as Ht'.
          iExists (M0 !!! S t). iSplitL. iExists (S t). admit.
          iPureIntro. simpl. assert (k = Key (M0 !!! t) c). admit.
          rewrite -H in Ht'. clear -Ht'; split; try set_solver. *)  }
        admit.
    - iModIntro. iApply "Hpost".
      iAssert (⌜0 < L⌝)%I as "H'". { admit. }
      iPoseProof ("HtrInv" with "H'") as "H''".
      iDestruct "H''" as (s) "(Hpast_s & %H' & %H'')".
      iExists s; iFrame "Hpast_s". iPureIntro. set_solver.
  Admitted.
      
End SKIPLIST1_SPEC_DELETE.