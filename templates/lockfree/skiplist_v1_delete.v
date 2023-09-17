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
Require Export skiplist_v1_util skiplist_v1_traverse list_flow_upd_marking.

Module SKIPLIST1_SPEC_DELETE.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS SKIPLIST1_UTIL SKIPLIST1_SPEC_TRAVERSE.


  Parameter try_constraint_delete_spec : ∀ (curr: Node) (i: nat),
     ⊢ (<<< ∀∀ mark next k, node curr mark next k >>>
           try_constraint #curr #i @ ⊤
       <<< ∃∃ (success: bool) mark',
              node curr mark' next k
            ∗ (match success with true => ⌜mark !!! i = false
                                            ∧ mark' = <[i := true]> mark⌝
                                | false => ⌜mark !!! i = true
                                            ∧ mark' = mark⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.

  Parameter permute_levels_spec : ∀ (L: nat),
        {{{ True }}}
           permute_levels #L
        {{{ (perm: loc) (vs: list val) (xs: list nat), RET #perm;
              perm ↦∗ vs
            ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
            ∗ ⌜xs ≡ₚ seq 1 (L-1)⌝ }}}.

  Lemma maintenanceOp_delete_rec_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght t0 c
    perm vs xs i:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        {{{ (∃ s, past_state γ_m t0 s ∗ ⌜c ∈ FP s⌝)
            ∗ perm ↦∗ vs
            ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
            ∗ ⌜xs ≡ₚ seq 1 (L-1)⌝
            ∗ (∃ s, past_state γ_m t0 s 
              ∗ ⌜∀ j, j < i → Marki s c (xs !!! j) = true⌝) }}}
           maintenanceOp_delete_rec #i #perm #c
        {{{ RET #();
              (∃ s, past_state γ_m t0 s ∗ ⌜c ∈ FP s⌝
                    ∗ ⌜∀ j, j ≤ (L - 1) → Marki s c (xs !!! j) = true⌝)
            ∗ perm ↦∗ vs }}}.
  Proof.
  (*
    iIntros "#HInv". iLöb as "IH" forall (i).
    iIntros (Φ) "!# (#FP_c & Hperm & %Def_vs & %Perm_xs & #Hmark) Hpost". 
    wp_lam. wp_pures.
    destruct (bool_decide (Z.le i (L - 2)%nat)) eqn: Hbool; wp_pures.
    - assert (is_Some (xs !! i)) as [idx Hidx].
      { admit. }
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i) (vs) #idx
        with "[Hperm]"); try done.
      { rewrite Def_vs. rewrite list_lookup_fmap. rewrite Hidx.
        by simpl. }
      iIntros "Hperm". wp_pures.
      Locate try_constraint_delete_spec.
      Check try_constraint_delete_spec.
      Check SKIPLIST1.try_constraint_delete_spec.
      
      awp_apply try_constraint_delete_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot0 & Hglob & Res & %PT0 & %Trans_M0)".
      iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iDestruct "Res" as "((Node_c & Node_crest) & Res_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node". iModIntro. iFrame.
        iNext; iExists M0, T0, s0.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
        iFrame "Res_rest". iFrame. }
      iIntros (success mark')"(Node_c & Hif)".
      iAssert (∃ s : snapshot, past_state γ_m t0 s 
        ∗ ⌜∀ j : nat, j < i + 1 → Marki s c (xs !!! j) = true⌝)%I as "#Hmark'".
      { admit. }
      iModIntro. iSplitR "Hperm Hpost".
      { admit. }
      wp_pures.
      iSpecialize ("IH" $! (i+1)).
      assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
      iEval (rewrite H') in "IH". iApply ("IH" with "[Hperm]"); try done.
      iFrame "Hperm FP_c Hmark' %".
  *)
  Admitted.

    
  Lemma maintenanceOp_delete_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght t0 c:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        {{{ ∃ s, past_state γ_m t0 s ∗ ⌜c ∈ FP s⌝ }}}
           maintenanceOp_delete #c
        {{{ RET #();
              (∃ s, past_state γ_m t0 s ∗ ⌜c ∈ FP s⌝
                    ∗ ⌜∀ i, 1 ≤ i < L → Marki s c i = true⌝) }}}.
  Proof.
  (*
    iIntros "#HInv". iIntros (Φ) "!# #FP_c Hpost".
    wp_lam. wp_pures. wp_apply permute_levels_spec; try done.
    iIntros (perm vs xs)"(Hperm & %Def_vs & %Perm_xs)". wp_pures. 
    wp_apply (maintenanceOp_delete_rec_spec with "[] [Hperm]"); try done.
    { iFrame "Hperm FP_c %". iDestruct "FP_c" as (s)"(Hs & FP_c)".
      iExists s. iFrame "Hs". iPureIntro; lia. }
    iIntros "(Hs & Hperm)". iDestruct "Hs" as (s)"(Hs & %H')".
    iApply "Hpost". iExists s; iFrame. iPureIntro.
    intros i Hi. assert (∃ j, j ≤ L - 1 ∧ (xs !!! j = i)) as [j [H1' <-]].
    { admit. }
    apply H'; try done.
  *)
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
    wp_lam. wp_pures. 
    wp_apply traverse_spec; try done.
    iIntros (preds succs ps ss p c res) 
      "(Hpreds & Hsuccs & #HtrInv & %Hps0 & %Hss0 & Hif)".  
    wp_pures. destruct res; wp_pures.
    - iDestruct "Hif" as "#Htr".
      wp_apply (wp_load_offset _ _ _ (DfracOwn (pos_to_Qp 1)) _ 
        ((λ n : loc, #n) <$> ss) #c with "[Hsuccs]"); try done.
      { rewrite list_lookup_fmap. simpl. admit. }
      { iNext. unfold is_array. admit. }
      iIntros "Hsuccs". wp_pures.
      wp_apply (maintenanceOp_delete_spec with "[] []"); try done.
      { iDestruct "Htr" as (s)"#(Hpast & _ & ? & _)". 
        iExists s; iFrame "#". }
      iIntros "#Hmnt". wp_pure credit:"Hcred". wp_pures.
      awp_apply try_constraint_delete_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
      { apply leibniz_equiv in Habs0. rewrite <-Habs0.
        iDestruct "Htr" as (s)"(Past_s & _ & %c_in_s & _)".
        iDestruct "Past_s" as (ts)"(% & Past_c)".
        iApply (in_FP with "[%] [$Hist] [] [%]"); try done. admit. }
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iDestruct "Nodes" as "(Node_c & Nodes_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node". iModIntro. 
        iSplitR "AU Hcred Hpreds Hsuccs Hpost"; try done.
        iNext; iExists M0, T0, s0. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) c); try done. 
        iFrame. iFrame. }
      iIntros (success mark')"(Node_c & Hif)".
      iApply (lc_fupd_add_later with "Hcred"). iNext.
      iAssert (∀ i, ⌜1 ≤ i < L → Marki s0 c i = true⌝)%I as "%Marki_c".
      { apply leibniz_equiv in Habs0. rewrite <-Habs0.
        iDestruct "Hmnt" as (s)"(Past_s & %c_in_s & %H')".
        iIntros (i). iDestruct "Past_s" as (ts)"(% & Past_c)". 
        iPoseProof (marking_mono c i with "[%] [$Hist] [] [%]") as "%H''"; 
          try done.
        iPureIntro. intros Hi. apply H''. apply H'. try done. admit. }
      destruct success.
      + iDestruct "Hif" as %[Mark_c0 Def_mark'].
        iDestruct "SShot0" as %[FP0 [C0 [Mk0 [Nx0 [Ky0 [I0 
          [Hs0 [Dom_Mk0 [Dom_Nx0 [Dom_Ky0 Dom_I0]]]]]]]]]].
        iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
        { iDestruct "Hist" as (M0')"(_&_&_&%&_)". iPureIntro.
          apply leibniz_equiv in Habs0. rewrite <-Habs0.
          by apply PT0. }
        assert (∀ x, x ∈ FP s0 → flow_constraints_I x (FI s0 x) 
                  (Marki s0 x 0) (Nexti s0 x 0) (Key s0 x)) as Hflow.
        { destruct PT_s0 as (_&_&H'&_).
          intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&?). }
        iAssert (⌜Key s0 c = k⌝)%I as %Key_c. 
        { apply leibniz_equiv in Habs0. rewrite <-Habs0.
          iDestruct "Htr" as (s)"(Past_s & _ & %c_in_s & _ & ->)".
          iDestruct "Past_s" as (ts)"(% & Past_c)".
          iApply (key_eq with "[%] [$Hist] [] [%]"); try done. admit. }
        iAssert (⌜∃ cn, Nexti s0 c 0 = Some cn⌝)%I as %[cn Def_cn].
        { destruct PT_s0 as ((_&_&_&_&Hk&_)&_&H'&_). apply H' in FP_c0.
          destruct FP_c0 as (_&_&H''&_). unfold Marki in H''.
          rewrite Mark_c0 in H''. iPureIntro.
          destruct (Nexti s0 c 0) as [cn | ] eqn: Hcn; try done.
          - exists cn; try done.
          - assert (false = false) as H1' by done.
            assert ((None: option Node) = None) as H1'' by done.
            pose proof H'' H1' H1'' as ->. rewrite Key_c in Hk.
            clear -Hk Range_k. lia. }
        iAssert (⌜∃ (I: gmap Node (multiset_flowint_ur nat)) (nk: Node),
                  dom I ⊆ FP s0
                ∧ hd ∉ dom I
                ∧ c ∈ dom I
                ∧ nk ∈ dom I
                ∧ c ≠ nk
                ∧ k < Key s0 nk
                ∧ (keyset (I !!! c) = ∅)
                ∧ (keyset (I !!! nk) = keyset (I0 !!! nk) ∪ keyset (I0 !!! c))
                ∧ (∀ x, x ∈ dom I ∖ {[ c; nk ]} → 
                    keyset (I !!! x) = keyset (I0 !!! x))
                ∧ ([^op set] x ∈ dom I, FI s0 x) = ([^op set] x ∈ dom I, I !!! x)
                ∧ (∀ x, x ∈ dom I → x ≠ c → flow_constraints_I x (I !!! x) 
                                        (Marki s0 x 0) (Nexti s0 x 0) (Key s0 x))
                ∧ (flow_constraints_I c (I !!! c) (true) 
                                        (Nexti s0 c 0) (Key s0 c))⌝)%I 
          as %[I [nk Hflupd]].
        { assert (∃ (Nx: gmap Node Node), ∀ x, Nx !! x = Nexti s0 x 0)
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
          assert (∀ x, Mk !!! x = Marki s0 x 0) as Def_Mk.
          { intros n. rewrite lookup_total_alt. rewrite Def_Mk'.
            unfold Marki; try done. }
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
              apply PT in H'. destruct H' as (_&_&_&H'&_).
              rewrite Hs0 in H'. unfold Next in H'.
              rewrite H1' in H'. by rewrite elem_of_dom in H'.
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
              apply PT in H'. destruct H' as (_&_&_&_&H'&_).
              rewrite Hs0 in H'. unfold Mark in H'.
              rewrite H1' in H'. by rewrite elem_of_dom in H'.
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
          assert (∀ x, I0 !!! x = FI s0 x) as I0_eq_s0.
          { intros x. rewrite Hs0; unfold FI. try done. }
          assert (✓ ([^op set] x ∈ dom I0, (I0 !!! x: multiset_flowint_ur nat))) 
            as VI.
          { destruct PT_s0 as (_&H'&_).
            unfold GFI in H'. rewrite Dom_I0.
            rewrite {2}Hs0 in H'. unfold FP in H'.
            assert (([^op set] x ∈ FP0, I0 !!! x) = 
              ([^op set] x ∈ FP0, FI s0 x)) as H1'.
            { by apply big_opS_ext. }
            by rewrite H1'. }
          assert (∀ x, x ∈ dom I0 → dom (I0 !!! x: multiset_flowint_ur nat) 
            = {[x]}) as Domm_I0.
          { rewrite Dom_I0. destruct PT_s0 as (_&_&PT&_).
            rewrite {1}Hs0 in PT. unfold FP in PT.
            intros x Hx%PT. destruct Hx as (_&_&_&_&_&Hx).
            destruct Hx as (Hx&_). by rewrite I0_eq_s0. }
          assert (c ∈ dom I0) as c_in_I0.
          { rewrite Dom_I0. rewrite {1}Hs0 in FP_c0. by unfold FP in FP_c0. }
          assert (∀ x, x ∈ dom I0 → Mk !!! x = true → 
            keyset (I0 !!! x) = ∅) as KS_mk.
          { rewrite Dom_I0. destruct PT_s0 as (_&_&PT&_).
            rewrite {1}Hs0 in PT. unfold FP in PT.
            intros x Hx%PT. destruct Hx as (_&_&_&_&_&Hx).
            destruct Hx as (_&_&Hx&_).
            by rewrite Def_Mk I0_eq_s0. }
          assert (∀ n1 n2, Nx !! n1 = Some n2 → 
            dom (out_map (I0 !!! n1: multiset_flowint_ur nat)) = {[n2]}) 
            as Nx_dom.
          { destruct PT_s0 as (_&_&PT&_).
            rewrite {1}Hs0 in PT. unfold FP in PT.
            intros n1 n2 Nx_n1.
            assert (n1 ∈ FP0) as H'.
            { apply elem_of_dom_2 in Nx_n1. by rewrite -Dom_Nx0 -Dom_Nx. } 
            apply PT in H'. destruct H' as (_&_&_&_&_&H').
            destruct H' as (_&_&_&H'). rewrite -Def_Nx Nx_n1 in H'.
            destruct H' as (H'&_). by rewrite I0_eq_s0. }
          set S := keyset (I0 !!! c).
          assert (S ⊆ insets (I0 !!! c)) as Insets_S.
          { subst S; clear; set_solver. }
          assert (S ## outsets (I0 !!! c)) as Outsets_S.
          { subst S; clear; set_solver. }
          set res := list_flow_upd_marking c Nx Mk S I0.
          assert (list_flow_upd_marking c Nx Mk S I0 = res) as Def_res by try done.
          
          rewrite <-Def_Nx in Def_cn.
          pose proof marking_flow_upd_summary Ky0 c Nx Mk S I0 res cn 
            Nx_key_rel Hcl KS_mk Nx_dom Def_cn VI Domm_I0 c_in_I0 Insets_S 
            Outsets_S Def_res as [II [nk [-> Hres]]].
          destruct Hres as [Dom_II_sub_I0 [c_in_II [nk_in_II [c_neq_nk 
            [Mk_nk [Mk_x [Nx_x [Key_x [Domm_II [Heq [II_c [II_nk [II_x 
            [KS_c KS_x]]]]]]]]]]]]]].
          
          assert (∀ k', k' ∈ S → k' ≤ k) as HSk.
          { rewrite Hs0 in FP_c0; unfold FP in FP_c0.
            rewrite {1}Hs0 in Hflow; unfold FP in Hflow.
            apply Hflow in FP_c0. unfold Marki in FP_c0.
            rewrite Mark_c0 in FP_c0. destruct FP_c0 as (_&H1'&_&_&H2'&H3').
            subst S. rewrite I0_eq_s0. assert (false = false) as H'' by done.
            pose proof H1' H'' as H1'. rewrite Key_c in H1' H2'. 
            clear -H1' H2' H3' Range_k. unfold keyset. intros k'.
            rewrite elem_of_difference. intros [Hk1 Hk2]. 
            rewrite -H2' in Hk2. rewrite elem_of_gset_seq in Hk2; last lia.
            pose proof H3' k' Hk1 as H0. lia. }
          
          assert (keyset (II !!! nk) = keyset (I0 !!! nk) ∪ S) as KS_nk.
          { rewrite II_nk. unfold keyset. rewrite inflow_insert_set_outsets.
            rewrite inflow_insert_set_insets.
            assert (S ## outsets (I0 !!! nk)) as H'.
            { assert (Hnk := nk_in_II).
              apply Dom_II_sub_I0 in nk_in_II. rewrite Dom_I0 in nk_in_II.
              rewrite {1}Hs0 in Hflow; unfold FP in Hflow.
              apply Hflow in nk_in_II.
              destruct nk_in_II as (_&_&_&_&H'&_).
              rewrite -Def_Mk in H'. rewrite lookup_total_alt in H'.
              rewrite Mk_nk in H'; simpl in H'. rewrite I0_eq_s0. 
              rewrite -H'. 
              assert (∀ k', k' ∈ gset_seq (Key s0 nk + 1) W → Key s0 nk < k') 
                as H1''. 
              { intros k' Hk'. apply elem_of_gset_seq in Hk'.
                clear -Hk'. lia. destruct PT_s0 as (_&_&_&_&_&HkW).
                assert (nk ∈ FP s0) as H''.
                { rewrite Hs0; unfold FP. rewrite -Dom_I0.
                  by apply Dom_II_sub_I0. }
                pose proof HkW nk H'' as HkW.
                clear -HkW. lia. }
              assert (nk ∈ dom II ∖ {[c]}) as H2' 
                by (clear -Hnk c_neq_nk; set_solver).
              pose proof Key_x nk H2' as H''. rewrite !Def_Ky0 in H''.
              rewrite Key_c in H''. clear -H1'' H'' HSk.
              rewrite elem_of_disjoint. intros x Hx1 Hx2.
              pose proof HSk x Hx1 as H1'. pose proof H1'' x Hx2 as H1''.
              lia. }
            clear -H'; set_solver. }
          
          assert (dom I0 = FP s0) as Dom_I0_s0.
          { rewrite Hs0. by unfold FP. }
          
          iPureIntro. exists II, nk. 
          split; last split; last split; last split; last split; 
            last split; last split; last split; last split; last split; 
            last split; try done.
          - rewrite <-Dom_I0_s0. done.
          - intros H'. destruct (decide (hd = c)) as [Hdc | Hdc].
            + destruct PT_s0 as ((_&_&_&H''&_)&_). 
              rewrite Hdc in H''. rewrite Key_c in H''. 
              clear -Range_k H''; lia. 
            + assert (hd ∈ dom II ∖ {[c]}) as H1'.
              { clear -H' Hdc; set_solver. } clear H'.
              apply Key_x in H1'. rewrite Hs0 in Key_c; unfold Key in Key_c.
              destruct PT_s0 as ((_&_&_&H''&_)&_).
              rewrite Hs0 in H''; unfold Key in H''.
              rewrite !lookup_total_alt in H1'. rewrite /inhabitant /= in H1'.
              clear -Key_c H1' H'' Range_k. 
              destruct (Ky0 !! c) eqn: H2'; destruct (Ky0 !! hd) eqn: H2'';
                rewrite H2' in Key_c; rewrite H2'' in H''; simpl in H1'; try lia.
          - rewrite -Key_c. rewrite Hs0 /Key. apply Key_x. 
            clear -nk_in_II c_neq_nk. set_solver.
          - rewrite KS_c; subst S; clear; set_solver.
          - by rewrite Hs0 Heq.
          - intros x Hx Hxc. assert (Hx' := Hx).
            apply Dom_II_sub_I0 in Hx. 
            rewrite Dom_I0_s0 in Hx. apply Hflow in Hx.
            destruct (decide (x = nk)) as [-> | Hxnk].
            + split; last split; last split; last split; last split.
              * by apply Domm_II.
              * destruct Hx as [_ [Hx _]].
                intros H'. apply Hx in H'.
                rewrite II_nk.
                rewrite inflow_insert_set_insets.
                rewrite I0_eq_s0. clear -H'; set_solver.
              * intros Hm. rewrite <-Def_Mk in Hm.
                rewrite lookup_total_alt in Hm.
                rewrite Mk_nk in Hm. clear -Hm; try done.
              * destruct Hx as [_ [_ [_ [Hx _]]]].
                rewrite II_nk. rewrite inflow_map_set_out_eq.
                rewrite I0_eq_s0. done.
              * destruct Hx as [_ [_ [_ [_ [Hx _]]]]].
                rewrite II_nk. 
                rewrite inflow_insert_set_outsets.
                rewrite I0_eq_s0. done.
              * destruct Hx as [_ [_ [_ [_ [_ Hx]]]]].
                rewrite II_nk. 
                rewrite inflow_insert_set_insets.
                rewrite I0_eq_s0. intros k'; rewrite elem_of_union.
                intros [Hk' | Hk']. apply Hx; try done.
                apply HSk in Hk'. clear -Hk' Range_k; lia.
            + assert (x ∈ dom II ∖ {[c;nk]}) as Hx1'.
              { clear -Hxc Hx' Hxnk; set_solver. }
              assert (Hx1'' := Hx1').
              apply II_x in Hx1'.
              split; last split; last split; last split; last split.
              * by apply Domm_II.
              * intros Hm. rewrite <-Def_Mk in Hm.
                rewrite lookup_total_alt in Hm.
                rewrite Mk_x in Hm; try done.
              * destruct Hx as [_ [_ [Hx _]]]. intros H'%Hx.
                rewrite KS_x; try done. by rewrite I0_eq_s0.
              * destruct Hx as [_ [_ [_ [Hx _]]]].
                assert (is_Some (Nexti s0 x 0)) as [n' Hn'].
                { rewrite <-Def_Nx. apply not_eq_None_Some. 
                  apply Nx_x. clear -Hx1''; set_solver. } 
                rewrite Hn'. rewrite Hn' in Hx.
                rewrite II_x; try done.
                assert (Nx !!! x = n') as ->. 
                { rewrite <-Def_Nx in Hn'. rewrite lookup_total_alt.
                  rewrite Hn'; try done. }
                unfold outflow_insert_set, outflow_map_set, out_map at 1.
                simpl. apply leibniz_equiv. unfold out, out_map at 1.
                unfold inflow_insert_set, inflow_map_set. simpl.
                rewrite nzmap_dom_insert_nonzero.
                rewrite I0_eq_s0. rewrite Hx; clear; set_solver.
                rewrite /ccmunit /= /lift_unit.
                intros H''. 
                assert (n' ∈ dom (out_map (FI s0 x))) as H1' 
                  by (clear -Hx; set_solver). 
                rewrite <-I0_eq_s0 in H1'.
                rewrite nzmap_elem_of_dom_total in H1'.
                rewrite /ccmunit /= /lift_unit in H1'.
                apply H1'. apply nzmap_eq. intros k'.
                rewrite nzmap_eq in H''. pose proof H'' k' as H''.
                rewrite nzmap_lookup_empty in H''.
                destruct (decide (k' ∈ S)) as [Hk' | Hk'].
                ** rewrite nzmap_lookup_total_map_set in H''; try done.
                   rewrite /ccmunit /= /nat_unit in H''.
                   clear -H''; lia.
                ** rewrite nzmap_lookup_total_map_set_ne in H''; try done.
              * destruct Hx as [_ [_ [_ [_ [Hx _]]]]].
                assert (Marki s0 x 0 = true) as H'.
                { apply Mk_x in Hx1''. rewrite <-Def_Mk.
                  rewrite {1}lookup_total_alt. by rewrite Hx1''. }
                rewrite H'. rewrite H' in Hx.
                rewrite II_x; try done.
                rewrite outflow_insert_set_outsets.
                rewrite inflow_insert_set_outsets.
                rewrite I0_eq_s0.
                clear -Hx; set_solver.
              * destruct Hx as [_ [_ [_ [_ [_ Hx]]]]].
                rewrite II_x; try done.
                rewrite outflow_insert_set_insets.
                rewrite inflow_insert_set_insets.
                rewrite I0_eq_s0. intros k'; rewrite elem_of_union.
                intros [Hk' | Hk']. apply Hx; try done.
                apply HSk in Hk'. clear -Hk' Range_k; lia.
          - apply Hflow in FP_c0. split; last split; last split; last split.
            + by apply Domm_II.  
            + intros H'; exfalso; clear -H'; try done.
            + intros _; rewrite KS_c. subst S. clear; set_solver.
            + rewrite II_c. rewrite <-Def_Nx. rewrite Def_cn.
              destruct FP_c0 as [_ [_ [_ [H' _]]]]. 
              rewrite <-Def_Nx in H'. rewrite Def_cn in H'.
              unfold outflow_insert_set, outflow_map_set, out_map at 1.
              simpl. apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero.
              rewrite I0_eq_s0. rewrite H'; clear; set_solver.
              rewrite /ccmunit /= /lift_unit.
              intros H''. 
              assert (cn ∈ dom (out_map (FI s0 c))) as H1' 
                by (clear -H'; set_solver). 
              rewrite <-I0_eq_s0 in H1'.
              rewrite nzmap_elem_of_dom_total in H1'.
              rewrite /ccmunit /= /lift_unit in H1'.
              apply H1'. apply nzmap_eq. intros k'.
              rewrite nzmap_eq in H''. pose proof H'' k' as H''.
              rewrite nzmap_lookup_empty.
              rewrite nzmap_lookup_empty in H''.
              destruct (decide (k' ∈ S)) as [Hk' | Hk'].
              * rewrite nzmap_lookup_total_map_set in H''; try done.
                rewrite /ccmunit /= /nat_unit.
                rewrite /ccmunit /= /nat_unit in H''.
                clear -H''; lia.
             * rewrite nzmap_lookup_total_map_set_ne in H''; try done.
            + rewrite II_c.
              destruct FP_c0 as [_ [_ [_ [_ H']]]]. 
              rewrite outflow_insert_set_outsets.
              unfold Marki in H'. rewrite Mark_c0 in H'.
              rewrite I0_eq_s0. clear -H'; set_solver. }
        set I0' := intf_merge I I0.
        set Mk0' := <[c := mark']> Mk0.
        set s0' := (FP0, C0 ∖ {[k]}, Mk0', Nx0, Ky0, I0'): snapshot.
        assert (abs s0 = C0) as Habs0'.
        { rewrite Hs0. by unfold abs. }
        assert (dom I ⊆ dom I0) as Dom_I_in_I0.
        { destruct Hflupd as (H'&_).
          rewrite Hs0 in H'; unfold FP in H'. by rewrite -Dom_I0 in H'. }
        iAssert (⌜snapshot_constraints s0'⌝)%I as "SShot0'".
        { iPureIntro. exists FP0, (C0 ∖ {[k]}), Mk0', Nx0, Ky0, I0'.
          repeat split; try done.
          rewrite /Mk0'. rewrite dom_insert_L.
          assert (c ∈ dom Mk0). 
          { rewrite Hs0 in FP_c0. rewrite Dom_Mk0. by unfold FP in FP_c0. }
          clear -H Dom_Mk0. set_solver.
          rewrite /I0'. rewrite intf_merge_dom; try done. }
        assert (node_inv_pure s0 c → node_inv_pure s0' c) as Hc.
        { intros [Hc1 [Hc2 [Hc3 [Hc4 [Hc5 Hc6]]]]].
          assert (Marki s0' c 0 = true) as HM.
          { unfold Marki, Mark. rewrite /s0' /Mk0'.
            rewrite lookup_insert. rewrite Def_mark'.
            by rewrite lookup_total_insert. }
          assert (Nexti s0' c 0 = Nexti s0 c 0) as HN.
          { rewrite /s0' Hs0; unfold Nexti, Next. done. }
          assert (Key s0' c = Key s0 c) as HK.
          { rewrite /s0' Hs0; unfold Key. done. }
          assert (FI s0' c = I !!! c) as HI.
          { rewrite /s0'. unfold FI. rewrite /I0'. 
            rewrite intf_merge_lookup; try done. 
            by destruct Hflupd as (_&_&H'&_). }
          split; last split; last split; last split; last split.
          - intros i. rewrite /s0'. unfold Marki, Mark. rewrite /Mk0'. 
            rewrite lookup_insert. rewrite Def_mark'.
            unfold Nexti, Next. 
            destruct (decide (i = 0)) as [-> | Hi].
            + intros _. rewrite Hs0 in Def_cn.
              unfold Nexti, Next in Def_cn. rewrite Def_cn.
              clear; try done.
            + rewrite lookup_total_insert_ne; try done.
              rewrite Hs0 in Hc1.
              unfold Marki, Nexti, Next in Hc1. 
              rewrite Hs0; try done. apply Hc1.
          - intros [i H1']. destruct (decide (i = 0)) as [-> | Hi]; try done.
            assert (1 ≤ i < L) as H'. { split; try lia. admit. }
            pose proof Marki_c i H' as H''. rewrite /s0' /Marki /= in H1'.
            rewrite /Mk0' in H1'. rewrite lookup_insert in H1'.
            rewrite Def_mark' in H1'. 
            rewrite lookup_total_insert_ne in H1'; try done.
            unfold Marki in H''. clear -H'' H1'. exfalso.
            set a : bool := Mark s0 c !!! i. 
            rewrite -/a in H'' H1'. destruct a; try done.
          - rewrite HM. clear; try done.
          - rewrite /s0'. unfold Next. rewrite Hs0 in Hc4. by unfold Next in Hc4.
          - rewrite /s0'. unfold Mark. rewrite /Mk0'.
            rewrite lookup_insert. rewrite Def_mark'.
            rewrite dom_insert_L. clear; set_solver.
          - rewrite HM HN HK HI.
            destruct Hflupd as (_&_&_&_&_&_&_&_&_&_&_&H''). done. }
        assert (∀ x, x ∈ FP s0 → node_inv_pure s0 x → node_inv_pure s0' x) 
          as Hpure.
        { intros x Hx. destruct (decide (x = c)) as [-> | Hxc]; try done.
          intros [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 Hx6]]]]].
          assert (∀ i, Marki s0' x i = Marki s0 x i) as HM.
          { rewrite /s0' Hs0. unfold Marki, Mark.
            rewrite /Mk0'. rewrite lookup_insert_ne; try done. }
          assert (∀ i, Nexti s0' x i = Nexti s0 x i) as HN.
          { rewrite /s0' Hs0. unfold Nexti, Next. done. }
          assert (Key s0' x = Key s0 x) as HK.
          { rewrite /s0' Hs0. unfold Key. done. }
          split; last split; last split; last split; last split.
          - intros i; rewrite HM HN. apply Hx1. 
          - rewrite HM. intros [i H1']. apply Hx2. 
            exists i. by rewrite <-HM.
          - by rewrite HM HN.
          - rewrite /s0'. unfold Next.
            rewrite Hs0 in Hx4. by unfold Next in Hx4.
          - rewrite /s0'. unfold Mark.
            rewrite Hs0 in Hx5. rewrite /Mk0'. 
            rewrite lookup_insert_ne; try done. 
          - rewrite HM HN HK.
            destruct (decide (x ∈ dom I)) as [Hx' | Hx'].
            + assert (FI s0' x = I !!! x) as ->.
              { rewrite /s0' /FI /=. rewrite /I0'.
                rewrite intf_merge_lookup; try done. }
              destruct Hflupd as (_&_&_&_&_&_&_&_&_&_&H''&_); 
              apply H''; try done.
            + assert (FI s0' x = FI s0 x) as ->; try done.
              { rewrite /s0' Hs0 /FI /=. rewrite /I0'.
                rewrite intf_merge_lookup_ne; try done.
                rewrite Hs0 in Hx; unfold FP in Hx.
                rewrite -Dom_I0 in Hx. clear -Hx Hx'; set_solver. } }
        assert (c ≠ hd) as c_neq_hd.
        { destruct Hflupd as (_&H'&H''&_).
          clear -H' H''; set_solver. }
        assert (FP s0' = FP s0) as FP_s0'.
        { by rewrite Hs0 /s0'; unfold FP. }
        assert (per_tick_inv s0') as PT_s0'.
        { destruct PT_s0 as (PT1&PT2&PT3&PT4&PT5&PT6).
          assert (FI s0' hd = FI s0 hd) as FI_s0_hd.
          { rewrite /s0' Hs0 /FI /=. rewrite /I0'.
            rewrite intf_merge_lookup_ne; try done.
            destruct PT1 as (_&_&_&_&_&H'&_).
            rewrite Hs0 in H'; unfold FP in H'.
            rewrite -Dom_I0 in H'.
            destruct Hflupd as (_&H''&_).
            clear -H' H''; set_solver. }
          assert (∀ i, Marki s0' hd i = Marki s0 hd i) as Mark_s0_hd.
          { rewrite /s0' Hs0. unfold Marki, Mark. simpl. rewrite /Mk0'.
            rewrite lookup_insert_ne; try done. }
          split; last split; last split; last split; last split.
          - destruct PT1 as (PT11&PT12&PT13&PT14&PT15&PT16&PT17).
            split; last split; last split; last split; last split; last split.
            + rewrite FI_s0_hd. try done.
            + rewrite FI_s0_hd. try done.
            + intros ?; rewrite Mark_s0_hd; try done.
            + rewrite /s0'; unfold Key. 
              rewrite Hs0 in PT14; by unfold Key in PT14.
            + rewrite /s0'; unfold Key. 
              rewrite Hs0 in PT15; by unfold Key in PT15.
            + rewrite FP_s0'; try done.
            + rewrite FP_s0'; try done.
          - unfold GFI. rewrite FP_s0'.
            assert (([^op set] x ∈ FP s0, FI s0' x) 
              = ([^op set] x ∈ FP s0, I0' !!! x)) as ->.
            { apply big_opS_ext. intros x Hx'.
              by rewrite /s0' /FI /=. }
            unfold GFI in PT2.
            assert (([^op set] x ∈ FP s0, I0' !!! x) 
              = ([^op set] x ∈ FP s0, FI s0 x)) as ->; last done.
            rewrite {1 3}Hs0; unfold FP. rewrite -Dom_I0.
            assert (([^op set] x ∈ dom I0, FI s0 x) 
              = ([^op set] x ∈ dom I0, I0 !!! x)) as ->.
            { apply big_opS_ext. intros x Hx'.
              by rewrite Hs0 /FI /=. }
            symmetry. apply (intf_merge_intfEq I); try done.
            assert (([^op set] x ∈ dom I, I0 !!! x)
              = ([^op set] x ∈ dom I, FI s0 x)) as ->.
            { apply big_opS_ext. intros x Hx.
              rewrite Hs0; unfold FI; try done. }
            by destruct Hflupd as (_&_&_&_&_&_&_&_&_&H'&_).
          - rewrite FP_s0'. intros n Hn; apply Hpure; by (try done || apply PT3).
          - rewrite /s0'. unfold Nexti, Next, Key.
            rewrite Hs0 in PT4. by unfold Nexti, Next, Key in PT4.
          - rewrite FP_s0'. rewrite /s0'. unfold Nexti, Next. 
            rewrite {1}Hs0 in PT5. by unfold Nexti, Next in PT5.
          - rewrite FP_s0'. rewrite /s0'; unfold Key.
            rewrite {2 3}Hs0 in PT6; unfold Key in PT6. done. }
        assert (transition_inv s0 s0') as Trans_s0.
        { split; last (repeat split).
          - intros n. destruct (decide (n = c)) as [-> | Hcn].
            + intros _ _. rewrite Key_c /s0'. unfold abs. clear; set_solver.
            + intros H' H''. rewrite /s0' in H''. unfold Marki, Mark in H''.
              rewrite /Mk0' in H''. rewrite lookup_insert_ne in H''; try done.
              rewrite Hs0 in H'. unfold Marki, Mark in H'.
              rewrite H'' in H'. done. 
          - assert (∀ n i, Nexti s0' n i = Nexti s0 n i) as HN.
            { rewrite /s0' Hs0. unfold Nexti, Next. done. }
            intros; apply HN.
          - intros n i FP_n. rewrite /s0' Hs0.
            unfold Marki, Mark. rewrite /Mk0'.
            destruct (decide (n = c)) as [-> | Hcn].
            + rewrite lookup_insert. rewrite Def_mark'.
              destruct (decide (i = 0)) as [-> | Hi0].
              * rewrite lookup_total_insert. by intros.
              * rewrite lookup_total_insert_ne; try done. rewrite Hs0.
                by unfold Mark.
            + rewrite lookup_insert_ne; try done.
          - intros. rewrite /s0' Hs0. by unfold Key.
          - rewrite /s0' Hs0. by unfold FP. }
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
            { unfold Content, Marki. destruct (Mark s0 nk !!! 0); try done.
              destruct Hflupd as (_&_&_&_&_&H1''&_).
              clear -H1''. intros Hk%elem_of_singleton. lia. }
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
        { iDestruct "Htr" as (s)"(Past_s & _ & %c_in_s & _)".
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
          iPureIntro. simpl. admit. }
        admit.
    - iModIntro. iApply "Hpost".
      unfold past_lin_witness. simpl.
      iDestruct "Hif" as (s) "(Hpast_s & %H')".
      iExists s; iFrame. iPureIntro; set_solver.
  Admitted.
      
End SKIPLIST1_SPEC_DELETE.