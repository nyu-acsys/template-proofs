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

Module SKIPLIST1_SPEC_INSERT.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS SKIPLIST1_UTIL.

  Lemma createNode_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght γ_sy t_id t0 succs ss k:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ is_array succs ss }}}
           createNode #k #succs
        {{{ (n: Node) mark next,
            RET #n;
              is_array succs ss
            ∗ node n mark next k  
            ∗ (⌜∀ i, mark !!! i = false⌝)
            ∗ (⌜∀ i, i < L → next !!! i = ss !!! i⌝) }}}.
  Proof.
  Admitted.

  Parameter try_constraint_insert_spec : ∀ (pred curr new_node: Node),
     ⊢ (<<< ∀∀ mark next k, node pred mark next k >>>
           try_constraint #pred #curr #new_node @ ⊤
       <<< ∃∃ (success: bool) next',
              node pred mark next' k
            ∗ (match success with true => ⌜next !! 0 = Some curr 
                                            ∧ mark !!! 0 = false
                                            ∧ next' = <[0 := new_node]> next⌝
                                | false => ⌜(next !! 0 ≠ Some curr ∨ 
                                              mark !!! 0 = true)
                                            ∧ next' = next⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.

  Definition traversal_inv s i k p c : Prop :=
      p ∈ FP s 
    ∧ c ∈ FP s 
    ∧ Key s p < k 
    ∧ Marki s p i = false 
    ∧ Nexti s p i = Some c.

  Lemma traverse_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght (h t: Node) γ_sy t_id t0 k:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ True }}}
           traverse #h #t #k
        {{{ (preds succs: loc) (ps ss: list Node) (p c: Node) (res: bool), 
              RET (#preds, #succs, #res);
              is_array preds ps ∗ is_array succs ss
            ∗ (∀ i, ⌜1 ≤ i < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                           ∗ ⌜traversal_inv s i k (ps !!! i) (ss !!! i)⌝)
            ∗ (⌜ps !!! 0 = p⌝) ∗ (⌜ss !!! 0 = c⌝)
            ∗ (∃ s, past_state γ_m t0 s ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝
                    ∗ if res then ⌜k ∈ keyset (FI s c)⌝ ∗ ⌜k = Key s c⌝
                      else ⌜k ∉ abs s⌝) }}}.
  Proof.  
  Admitted.


  
  Lemma insertOp_spec N γ_s γ_t γ_m γ_td1 γ_td2 γ_ght (h t: Node) γ_sy t_id t0 k:
          main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
            □ update_helping_protocol N γ_t γ_s γ_td1 γ_td2 γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     insert #h #t #k
                {{{ res, RET #res; 
                    past_lin_witness γ_m (insertOp k) res t0 }}}.
  Proof.
    iIntros "#HInv #HUpd #Thd". iLöb as "IH". iIntros (Φ) "!# _ Hpost".
    assert (0 < k < W) as Range_k. { admit. }
    wp_lam. wp_pures. wp_apply traverse_spec; try done.
    iIntros (preds succs ps ss p c res) 
      "(Hpreds & Hsuccs & #HtrInv & %Hps0 & %Hss0 & Hif)".  
    wp_pures. destruct res; wp_pures.
    - iModIntro. iApply "Hpost".
      unfold past_lin_witness. simpl.
      iDestruct "Hif" as (s) "(Hpast_s & %H')".
      assert (k ∈ abs s). admit.
      iExists s; iFrame. iPureIntro; set_solver.
    - iDestruct "Hif" as "#Htr_false".
      wp_apply (createNode_spec with "[] [] [Hsuccs]"); try done.
      iIntros (n mark next) "(Hsuccs & Node_n & %Def_mark & %Def_next)".
      wp_pures. wp_bind (! _)%E.
      iEval (rewrite /is_array) in "Hpreds".
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) _ ((λ n : loc, #n) <$> ps) #p
        with "[Hpreds]"); try done.
      { admit. }
      { iNext. admit. }
      iIntros "Hpreds". wp_pures.
      wp_bind (! _)%E.
      iEval (rewrite /is_array) in "Hsuccs".
      wp_apply (wp_load_offset _ _ _ (DfracOwn 1) _ ((λ n : loc, #n) <$> ss) #c
        with "[Hsuccs]"); try done.
      { admit. }
      { iNext. admit. }
      iIntros "Hsuccs". wp_pures.
      awp_apply try_constraint_insert_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
      { (* interpolation *) admit. }
      assert (n ∉ FP s0) as n_notin_s0. { admit. }
      assert (n ≠ p) as n_neq_p.
      { clear -FP_p0 n_notin_s0. set_solver. }
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAaccIntro with "Node_p".
      { iIntros "Node". iModIntro. iFrame.
        iNext; iExists M0, T0, s0.
        iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) p); last by eauto. 
        iFrame. }
      iIntros (success next')"(Node_p & Hif)".
      destruct success; last first.
      + iDestruct "Hif" as %[H' ->]. 
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M0, T0, s0.
          iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
          iFrame. }
        wp_pures. iApply "IH"; try done.
      + iDestruct "Hif" as %[Next_p0 [Mark_p0 Def_next']].

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
        set Mk0' := <[n := mark]> Mk0.
        set Nx0' := <[n := next]> (<[p := next']> Nx0).
        set Ky0' := <[n := k]> Ky0.
        iAssert (⌜∃ (I: gmap Node (multiset_flowint_ur nat)),
                    dom I = FP s0 ∪ {[n]}
                  ∧ ✓ ([^op set] x ∈ dom I, (I !!! x: multiset_flowint_ur nat))
                  ∧ (∀ x, x ∈ dom I → x ≠ p → x ≠ n →
                     flow_constraints_I x (I !!! x) (Marki s0 x 0) (Nexti s0 x 0) 
                                        (Key s0 x))
                  ∧ (flow_constraints_I p (I !!! p) (false) (Some n) (Key s0 p) )
                  ∧ (flow_constraints_I n (I !!! n) (false) (Some c) (k))⌝)%I
        as %[I Hflupd].
        { iPureIntro.
          set Ip0 := I0 !!! p. set Ic0 := I0 !!! c. set out_pc := out Ip0 c.
          set Ip0' := int {| infR := inf_map Ip0; outR :=  <<[n := out_pc]>> ∅ |}.
          set In0' := int {| infR := {[n := out_pc]}; 
                              outR := <<[c := out_pc]>> ∅ |}.
          assert (∀ x, I0 !!! x = FI s0 x) as I0_eq_s0.
          { intros x. rewrite Hs0; unfold FI. try done. }
          assert (Key s0 p < W) as Key_p0.
          { destruct PT_s0 as (_&_&_&_&_&PT). apply PT in FP_p0.
            clear -FP_p0; lia. }
          assert (out_pc ≠ 0%CCM) as Out_pc_nz.
          { destruct PT_s0 as (_&_&PT&_). apply PT in FP_p0.
            destruct FP_p0 as (_&_&_&_&_&H'). destruct H' as (_&_&_&H'&H''&_). 
            rewrite /Marki Mark_p0 /outsets in H''. 
            rewrite /Nexti Next_p0 in H'. rewrite H' in H''. clear H'.
            apply leibniz_equiv_iff in H''. rewrite big_opS_singleton in H''.
            rewrite /out_pc /Ip0 I0_eq_s0. rewrite /ccmunit /lift_unit.
            intros H'. rewrite nzmap_eq in H'. pose proof H' W as H'.
            rewrite nzmap_lookup_empty /ccmunit /= /nat_unit in H'.
            rewrite /outset in H''. rewrite -nzmap_elem_of_dom_total2 in H'.
            rewrite -H'' in H'. rewrite elem_of_gset_seq in H'. apply H'. 
            split; try done. all: clear - Key_p0; lia. }
          assert (p ≠ c) as p_neq_c.
          { admit. }
          assert (c ∈ FP s0) as FP_c0.
          { admit. }
          assert (n ≠ c) as n_neq_c.
          { clear -FP_c0 n_notin_s0. set_solver. }
          assert (✓ ([^op set] x ∈ dom I0, (I0 !!! x: multiset_flowint_ur nat))) 
            as VI0.
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
          assert (p ∈ dom I0) as p_in_I0.
          { by rewrite Hs0 /FP -Dom_I0 in FP_p0. }
          assert (c ∈ dom I0) as c_in_I0.
          { by rewrite Hs0 /FP -Dom_I0 in FP_c0. }
          assert (n ∉ dom I0) as n_notin_I0.
          { by rewrite Hs0 /FP -Dom_I0 in n_notin_s0. }
          assert (✓ Ip0) as Vp0.
          { assert ({[p]} ⊆ dom I0) as H'. 
            { clear -p_in_I0; set_solver. }
            pose proof (flow_big_op_valid _ (dom I0) {[p]} H' VI0) as H''.
            by rewrite big_opS_singleton in H''. }
          assert (✓ Ip0') as Vp0'.
          { rewrite /valid /=. apply Domm_I0 in p_in_I0.
            unfold dom, flowint_dom in p_in_I0.
            rewrite p_in_I0. rewrite nzmap_dom_insert_nonzero; try done.
            split. clear -n_neq_p; set_solver.
            intros H'; rewrite H' in p_in_I0. clear -p_in_I0; set_solver. }
          assert (dom Ic0 ## dom Ip0) as Disj_pc.
          { rewrite !Domm_I0; try done. clear -p_neq_c; set_solver. }
          assert (c ∈ dom Ic0) as c_in_Ic0.
          { rewrite Domm_I0; try done. clear; set_solver. }
          assert (n ∉ dom Ip0 ∪ dom Ic0) as n_notin_pc.
          { rewrite !Domm_I0; try done. clear -n_neq_p n_neq_c. set_solver. }
          assert (dom Ip0 = dom Ip0') as Dom_Ip0'.
          { apply Domm_I0 in p_in_I0.
            unfold dom, flowint_dom in p_in_I0.
            unfold dom, flowint_dom. by rewrite p_in_I0. }
          assert (out Ip0 n = 0%CCM) as Out_Ip0_n.
          { destruct PT_s0 as (_&_&PT&_).
            rewrite {1}Hs0 /FP in PT. rewrite Dom_I0 in p_in_I0.
            apply PT in p_in_I0. destruct p_in_I0 as (_&_&_&_&_&Hx).
            rewrite /Nexti Next_p0 in Hx.
            destruct Hx as (_&_&_&Hx&_). unfold out.
            rewrite -nzmap_elem_of_dom_total2. rewrite /Ip0 I0_eq_s0 Hx.
            clear -n_neq_c; set_solver. }
          assert (out Ip0' n = out Ip0 c) as Out_Ip0'_n.
          { rewrite {1}/out /out_map /Ip0' /=.
            rewrite nzmap_lookup_total_insert. done. }
          assert (out Ip0' c = 0%CCM) as Out_Ip0'_c.
          { rewrite {1}/out /out_map /Ip0' /=.
            rewrite nzmap_lookup_total_insert_ne; try done. }
          assert (∀ n0, n0 ≠ n → n0 ≠ c → out Ip0' n0 = out Ip0 n0) as Out_Ip0'. 
          { intros n' Hn' Hn''. destruct PT_s0 as (_&_&PT&_).
            rewrite {1}Hs0 /FP in PT. rewrite Dom_I0 in p_in_I0.
            apply PT in p_in_I0. destruct p_in_I0 as (_&_&_&_&_&Hx).
            rewrite /Nexti Next_p0 in Hx. destruct Hx as (_&_&_&Hx&_). 
            rewrite {1}/out /out_map /Ip0' /=. rewrite /out /Ip0 I0_eq_s0.
            rewrite nzmap_lookup_total_insert_ne; try done.
            rewrite nzmap_lookup_empty. symmetry. 
            rewrite -nzmap_elem_of_dom_total2. rewrite Hx. 
            clear -Hn''; set_solver. }
          assert (∀ n, inf Ip0' n = inf Ip0 n) as Inf_Ip0'.
          { intros ?; try done. }
          pose proof contextualLeq_insert_node _ Ip0 Ic0 Ip0' n c Vp0 Vp0'
            Disj_pc c_in_Ic0 n_notin_pc Dom_Ip0' Out_Ip0_n Out_Ip0'_n 
            Out_Ip0'_c Out_Ip0' Inf_Ip0' as ContLeq0.
          rewrite -/out_pc -/In0' in ContLeq0.
          set I0' := <[n := In0']> (<[p := Ip0']> I0).
          set Io := ([^op set] x ∈ dom I0 ∖ {[p]}, 
                          ((I0 !!! x): multiset_flowint_ur _)).
          assert (✓ (Ip0 ⋅ Io)) as Vpo.
          { assert (Ip0 ⋅ Io = 
              ([^op set] x ∈ dom I0, I0 !!! x : multiset_flowint_ur nat)) as ->.
            rewrite /Ip0 /Io. by rewrite (big_opS_delete _ (dom I0) p).
            done. }
          assert (dom In0' = {[n]}) as Dom_In0'.
          { rewrite /dom /flowint_dom /=. by rewrite dom_singleton_L. }
          assert (p ∉ dom Io) as p_notin_Io.
          { rewrite (big_opS_delete _ _ p) in VI0; try done. 
            rewrite -/Io in VI0. apply intComp_dom_disjoint in VI0.
            rewrite (Domm_I0 p p_in_I0) in VI0. clear - VI0; set_solver. }
          assert (dom ([^op set] x ∈ dom I0, I0 !!! x : multiset_flowint_ur nat)
            = FP s0) as Dom_I0_FP.
          { rewrite set_eq_subseteq. split.
            - intros x Hx. rewrite flow_big_op_dom in Hx; try done.
              destruct Hx as [x0 [Hx01 Hx02]].
              rewrite (Domm_I0 x0 Hx01) in Hx02.
              rewrite /FP Hs0 -Dom_I0.
              clear -Hx01 Hx02; set_solver.
            - intros x Hx. rewrite flow_big_op_dom; try done.
              exists x. rewrite /FP Hs0 -Dom_I0 in Hx. split; try done.
              rewrite (Domm_I0 x Hx). clear; set_solver. }
          assert (n ∉ dom Io) as n_notin_Io.
          { assert (dom Io ⊆ 
              dom ([^op set] x ∈ dom I0, I0 !!! x : multiset_flowint_ur _)) as H'. 
            { admit. }
            rewrite Dom_I0_FP in H'.
            clear -H' n_notin_s0. set_solver. }
          assert (dom (Ip0' ⋅ In0') ∩ dom Io = ∅) as Disj_Io.
          { rewrite intComp_dom. rewrite Dom_In0' -Dom_Ip0' (Domm_I0 p p_in_I0).
            clear -p_notin_Io n_notin_Io. set_solver.
            by destruct ContLeq0 as (_&?&_). }
          assert (out ([^op set] x ∈ dom I0, I0 !!! x: multiset_flowint_ur _) n 
                    = 0%CCM) as Out_s0_n.
          { admit. }
          assert (∀ n, n ∈ dom (Ip0' ⋅ In0') ∖ dom Ip0 → out_map Io !!! n = 0%CCM)
           as Out_Io.
          { intros n'. rewrite intComp_dom; last first. 
            { by destruct ContLeq0 as (_&?&_). }  
            rewrite Dom_In0' -Dom_Ip0' (Domm_I0 p p_in_I0).
            intros Hn'. assert (n' = n) as ->.
            { clear -Hn'; set_solver. } Search intComp out.
            rewrite (big_opS_delete _ _ p) in Out_s0_n. 
            rewrite intComp_unfold_out in Out_s0_n.
            rewrite /ccmunit /lift_unit /=. rewrite nzmap_eq.
            intros k'. rewrite nzmap_lookup_empty. 
            rewrite /ccmunit /= /nat_unit.
            rewrite /ccmunit /= /lift_unit in Out_s0_n.
            rewrite /ccmop /ccm_op /= in Out_s0_n.
            rewrite nzmap_eq in Out_s0_n. pose proof Out_s0_n k' as H'.
            rewrite lookup_total_lifting in H'. 
            rewrite /ccmop /ccm_op /= /nat_op in H'.
            rewrite nzmap_lookup_empty in H'.
            rewrite /ccmunit /= /nat_unit in H'.
            rewrite -/Io in H'. clear -H'.
            set a := (out (I0 !!! p: multiset_flowint_ur _) n) !!! k'.
            set b := (out Io n) !!! k'.
            rewrite -/a -/b in H'. lia.
            by rewrite (big_opS_delete _ _ p) in VI0.
            rewrite (big_opS_delete _ _ p) in Dom_I0_FP.
            by rewrite Dom_I0_FP. done. done. }
          pose proof replacement_theorem _ Io Ip0 (Ip0' ⋅ In0') Vpo Disj_Io 
            Out_Io ContLeq0 as ContLeq0'.
          assert (∃ (Nx: gmap Node Node), (∀ x, Nx !! x = (Nx0' !!! x) !! 0))
            as [Nx Def_Nx'].
          { set f_Nx := λ (n: Node) (nx: gmap nat Node) (res: gmap Node Node), 
                        match nx !! 0 with None => res 
                                        | Some n' => <[n := n']> res end.
            set Nx : gmap Node Node := map_fold f_Nx ∅ Nx0'.
            exists Nx.
            set P := λ (res: gmap Node Node) (m: gmap Node (gmap nat Node)),
                (∀ x: Node, res !! x = 
                  (match m !! x with Some mn => mn | None => ∅ end) !! 0).
            apply (map_fold_ind P); try done.
            intros n' Nx_n' m res Hmn HP. unfold P. unfold P in HP.
            intros n''. unfold f_Nx. 
            destruct (decide (n'' = n')) as [-> | Hn''].
            - destruct (Nx_n' !! 0) as [Nx_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert. by rewrite Hn0.
              + rewrite lookup_insert. rewrite Hn0.
                by rewrite (HP n') Hmn.
            - destruct (Nx_n' !! 0) as [Nx_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert_ne; try done.
              + rewrite (HP n''). by rewrite lookup_insert_ne. }
          assert (Nx !! p = Some n) as Nx_p.
          { rewrite Def_Nx' /Nx0'. rewrite lookup_total_insert_ne; try done.
            rewrite lookup_total_insert. rewrite Def_next'.
            by rewrite lookup_insert. }
          assert (Nx !! n = Some c) as Nx_n.
          { rewrite Def_Nx' /Nx0'. rewrite lookup_total_insert.
            admit. }
          assert (∀ x, x ≠ p → x ≠ n → Nx !! x = Nexti s0 x 0) as Def_Nx.
          { intros x Hxp Hxn. rewrite Def_Nx' /Nx0'. 
            rewrite lookup_total_insert_ne; try done.
            rewrite lookup_total_insert_ne; try done.
            rewrite /Nexti /Next Hs0. destruct (Nx0 !! x); try done. }
          assert (∃ (Mk: gmap Node bool), ∀ x, Mk !! x = (Mk0' !!! x) !! 0)
            as [Mk Def_Mk'].
          { set f_Mk := λ (n: Node) (nx: gmap nat bool) (res: gmap Node bool), 
                        match nx !! 0 with None => res 
                                        | Some n' => <[n := n']> res end.
            set Mk : gmap Node bool := map_fold f_Mk ∅ Mk0'.
            exists Mk.
            set P := λ (res: gmap Node bool) (m: gmap Node (gmap nat bool)),
              ∀ x: Node, res !! x = 
                (match m !! x with Some mn => mn | None => ∅ end) !! 0.
            apply (map_fold_ind P); try done.
            intros n' Mk_n m res Hmn HP. unfold P. unfold P in HP.
            intros n''. unfold f_Mk. 
            destruct (decide (n'' = n')) as [-> | Hn''].
            - destruct (Mk_n !! 0) as [Mk_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert. by rewrite Hn0.
              + rewrite lookup_insert. rewrite Hn0. 
                by rewrite (HP n') Hmn.
            - destruct (Mk_n !! 0) as [Mk_n0' | ] eqn:Hn0.
              + rewrite !lookup_insert_ne; try done. 
              + rewrite (HP n''). by rewrite lookup_insert_ne. }
          assert (Mk !! n = Some false) as Mk_n.
          { rewrite Def_Mk' /Mk0'.
            rewrite lookup_total_insert.
            admit. }
          assert (∀ x, x ≠ n → Mk !!! x = Marki s0 x 0) as Def_Mk.
          { intros n' Hn'. rewrite lookup_total_alt. rewrite Def_Mk' /Mk0'.
            rewrite lookup_total_insert_ne; try done.
            rewrite Hs0 /Marki /Mark; try done. }
          assert (dom Nx = dom Nx0 ∪ {[n]}) as Dom_Nx.
          { apply set_eq_subseteq; split.
            - intros n'. rewrite !elem_of_dom.
              destruct (decide (n' = n)) as [-> | Hn'].
              { intros _; clear; set_solver. }
              destruct (decide (n' = p)) as [-> | Hn''].
              { intros _; rewrite elem_of_union; left.
                rewrite Dom_Nx0 -Dom_I0. done. }
              rewrite elem_of_union. 
              rewrite Def_Nx; try done.
              rewrite Hs0 /Nexti /Next.
              destruct (Nx0 !! n') eqn: H'; try done.
              + apply elem_of_dom_2 in H'. intros _; left; done.
              + rewrite H'. rewrite lookup_empty. 
                intros [? H'']; try done.
            - intros n'. rewrite elem_of_union. intros [Hn' | Hn']; last first.
              { assert (n' = n) as -> by (clear -Hn'; set_solver).
                by rewrite elem_of_dom Nx_n. }
              rewrite !elem_of_dom.
              destruct (decide (n' = n)) as [-> | Hn''].
              { rewrite Dom_Nx0 in Hn'. rewrite /FP Hs0 in n_notin_s0.
                clear -n_notin_s0 Hn'. set_solver. }
              destruct (decide (n' = p)) as [-> | Hn'''].
              { rewrite Nx_p; try done. } 
              rewrite Def_Nx; try done. rewrite Hs0 /Nexti /Next.
              destruct (Nx0 !! n') eqn: H'; try done.
              + rewrite H'. assert (H1' := H'). 
                apply elem_of_dom_2 in H'.
                rewrite Dom_Nx0 in H'; try done.
                destruct PT_s0 as (_&_&PT&_).
                rewrite {1}Hs0 in PT. unfold FP in PT.
                apply PT in H'. destruct H' as (_&_&_&H'&_).
                rewrite Hs0 in H'. unfold Next in H'.
                rewrite H1' in H'. by rewrite elem_of_dom in H'.
              + rewrite -not_elem_of_dom in H'. clear -Hn' H'; set_solver. }
          assert (dom Mk = dom Mk0 ∪ {[n]}) as Dom_Mk.
          { apply set_eq_subseteq; split.
            - intros n'. 
              destruct (decide (n' = n)) as [-> | Hn'].
              { intros _; clear; set_solver. }
              intros Hn''. rewrite elem_of_dom in Hn''.
              rewrite elem_of_union. left.
              rewrite Def_Mk' /Mk0' in Hn''. 
              rewrite lookup_total_insert_ne in Hn''; try done.
              rewrite elem_of_dom.
              destruct (Mk0 !! n') eqn: H'; try done.
              rewrite lookup_total_alt in Hn''.
              rewrite H' /= in Hn''. rewrite lookup_empty in Hn''.
              destruct Hn'' as [? ?]; try done. 
            - intros n'. rewrite elem_of_union. intros [Hn' | Hn']; last first.
              { assert (n' = n) as -> by (clear -Hn'; set_solver).
                by rewrite elem_of_dom Mk_n. }
              rewrite !elem_of_dom.
              destruct (decide (n' = n)) as [-> | Hn''].
              { rewrite Dom_Mk0 in Hn'. rewrite /FP Hs0 in n_notin_s0.
                clear -n_notin_s0 Hn'. set_solver. }
              destruct (Mk !! n') eqn: H'; try done.
              rewrite Def_Mk' in H'. 
              apply not_elem_of_dom in H'. rewrite /Mk0' in H'.
              rewrite lookup_total_insert_ne in H'; try done.
              rewrite Dom_Mk0 in Hn'.
              destruct PT_s0 as (_&_&PT&_).
              rewrite {1}Hs0 /FP in PT.
              apply PT in Hn'. destruct Hn' as (_&_&_&_&Hn'&_).
              rewrite Hs0 /Mark in Hn'. done. }
          assert (∀ x, Ky0 !!! x = Key s0 x) as Def_Ky0.
          { rewrite Hs0. unfold Key. try done. }
          set S := gset_seq (Key s0 p) k.
          set res := list_flow_upd_insert n Nx Mk S I0'.
          assert (nx_key_rel Nx Ky0') as Nx_key_rel.
          { destruct PT_s0 as (_&_&_&H'&_). intros n1 n2.
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite Nx_p. intros [=<-]. rewrite /Ky0'.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. admit. } 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite Nx_n. intros [=<-]. rewrite /Ky0'.
              rewrite lookup_total_insert.
              rewrite lookup_total_insert_ne; try done. admit. }
            rewrite !Def_Nx /Ky0'; try done. 
            destruct (decide (n2 = n)) as [-> | Hn2n].
            { admit. }
            rewrite !lookup_total_insert_ne; try done.
            rewrite !Def_Ky0. apply H'. }
          assert (dom I0' = dom I0 ∪ {[n]}) as Dom_I0'.
          { rewrite /I0'. rewrite !dom_insert_L. 
            clear -p_in_I0. set_solver. }
          assert (nx_mk_closed Nx Mk (dom I0')) as Hcl.
          { split; last split. 
            - by rewrite Dom_Nx Dom_I0' Dom_Nx0 Dom_I0.
            - by rewrite Dom_Mk Dom_I0' Dom_Mk0 Dom_I0.
            - destruct PT_s0 as (_&_&_&_&H'&_). intros n1 n2.
              destruct (decide (n1 = n)) as [-> | Hn1n].
              + rewrite Nx_n. intros [=<-]. rewrite Dom_I0'.
                clear -c_in_I0; set_solver.
              + destruct (decide (n1 = p)) as [-> | Hn1p].
                * rewrite Nx_p. intros [=<-]. rewrite Dom_I0'.
                  clear; set_solver.
                * rewrite Def_Nx; try done. intros H''%H'.
                  rewrite Hs0 /FP -Dom_I0 in H''. rewrite Dom_I0'.
                  clear -H''; set_solver. } 
          assert (([^op set] x ∈ dom I0', (I0' !!! x: multiset_flowint_ur nat))
            = Ip0' ⋅ In0' ⋅ Io) as Def_I0'.
          { rewrite (big_opS_delete _ _ n); last first.
            { rewrite Dom_I0'. clear; set_solver. }
            rewrite (big_opS_delete _ _ p); last first.
            { rewrite Dom_I0' elem_of_difference. split.
              clear -p_in_I0; set_solver. clear -n_neq_p; set_solver. }
              assert (([^op set] y ∈ (dom I0' ∖ {[n]} ∖ {[p]}), I0' !!! y) = Io)
                as <-.
              { rewrite /Io. 
                assert (dom I0' ∖ {[n]} ∖ {[p]} = dom I0 ∖ {[p]}) as ->.
                { rewrite Dom_I0'. clear -n_notin_I0 n_neq_p p_in_I0. 
                  set_solver. }
                apply big_opS_ext. intros x Hx. rewrite /I0'.
                rewrite !lookup_total_insert_ne; try done.
                clear -Hx; set_solver. clear -Hx n_notin_I0. set_solver. }
              rewrite {1 2}/I0'. rewrite lookup_total_insert. 
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. by rewrite assoc (comm _ Ip0' In0'). }
          assert (✓ ([^op set] x ∈ dom I0', (I0' !!! x: multiset_flowint_ur nat))) 
            as VI0'.
          { rewrite Def_I0'. by destruct ContLeq0' as (_&?&_). }
          assert (∀ n1 n2, Nx !! n1 = Some n2 → 
            dom (out_map (I0' !!! n1: multiset_flowint_ur nat)) = {[n2]}) 
            as Nx_dom.
          { intros n1 n2. destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite Nx_n; intros [=<-]. rewrite /I0'. 
              rewrite lookup_total_insert. rewrite /In0'.
              simpl. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done. 
              clear. unfold dom, nzmap_dom. set_solver. }
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite Nx_p; intros [=<-]. rewrite /I0'.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. rewrite /Ip0'.
              simpl. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done. 
              clear. unfold dom, nzmap_dom. set_solver. }
            intros Hn1. assert (Hn1' := Hn1). apply elem_of_dom_2 in Hn1.
            rewrite Dom_Nx in Hn1. rewrite elem_of_union in Hn1.
            destruct Hn1 as [Hn1 | Hn1]; last first.
            { clear -Hn1 Hn1n; set_solver. }
            destruct PT_s0 as (_&_&PT&_).
            rewrite {1}Hs0 /FP in PT. rewrite Dom_Nx0 in Hn1.
            apply PT in Hn1. destruct Hn1 as (_&_&_&_&_&H').
            destruct H' as (_&_&_&H'&_). rewrite Def_Nx in Hn1'; try done.
            rewrite Hn1' in H'. rewrite /I0'. 
            rewrite !lookup_total_insert_ne; try done. by rewrite I0_eq_s0. }
          assert (n ∈ dom I0') as n_in_I0'.
          { rewrite Dom_I0'; clear; set_solver. }
          assert (∀ x, x ∈ dom I0' → Mk !!! x = true → 
            keyset (I0' !!! x) = ∅) as KS_mk.
          { intros x Hx Hmkx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx]; last first.
            { assert (x = n) as -> by (clear -Hx; set_solver).
              by rewrite lookup_total_alt Mk_n /= in Hmkx. }
            assert (x ≠ n) by (clear -Hx n_notin_I0; set_solver).
            destruct PT_s0 as (_&_&PT&_).
            rewrite {1}Hs0 /FP in PT. rewrite Dom_I0 in Hx.
            apply PT in Hx. destruct Hx as (_&_&_&_&_&Hx).
            destruct Hx as (_&_&Hx&_). rewrite /I0'.
            rewrite lookup_total_insert_ne; try done.
            destruct (decide (x = p)) as [-> | Hxp].
            { rewrite lookup_total_alt in Hmkx. rewrite Def_Mk' /Mk0' in Hmkx.
              rewrite lookup_total_insert_ne in Hmkx; try done.
              rewrite Hs0 /Mark in Mark_p0. rewrite lookup_total_alt in Hmkx.
              destruct (Mk0 !! p) as [mkp | ] eqn: Hmkp.
              simpl in Hmkx. rewrite Hmkp in Mark_p0.
              rewrite lookup_total_alt /inhabitant /= in Mark_p0.
              by rewrite Mark_p0 in Hmkx.
              rewrite Hmkp in Mark_p0. 
              (* Iris stdpp typo *)
              rewrite loopup_total_empty in Mark_p0. done. }
            rewrite lookup_total_insert_ne; try done.
            rewrite Def_Mk in Hmkx; try done. apply Hx in Hmkx.
            by rewrite I0_eq_s0. }
          assert (∀ x : Node, x ∈ dom I0' → dom (I0' !!! x) = {[x]}) 
            as Domm_I0'.
          { intros x Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx]; last first. 
            { assert (x = n) as -> by (clear -Hx; set_solver).
              rewrite /I0' lookup_total_insert /In0'.
              rewrite /dom /flowint_dom /=. by rewrite dom_singleton_L. }
            assert (x ≠ n) by (clear -Hx n_notin_I0; set_solver).
            rewrite /I0' lookup_total_insert_ne; try done.
            destruct (decide (x = p)) as [-> | Hxp].
            { rewrite lookup_total_insert /Ip0'. rewrite /dom /flowint_dom /=.
              apply Domm_I0 in p_in_I0. apply p_in_I0. }
            rewrite lookup_total_insert_ne; try done.
            apply Domm_I0; try done. }
          assert (∃ k, k ∈ outset nat (I0' !!! n) c ∧ k ∉ S) as Outset_n.
          { admit. }
          assert (S ⊆ insets (I0' !!! n)) as Insets_S.
          { admit. }
          assert (∀ x k', x ∈ dom I0' → 
            inf (I0' !!! x : multiset_flowint_ur _) x !!! k' ≤ 1) as Insets_x.
          { admit. }
          assert (∀ k, k ∈ S → 
            out (I0' !!! n : multiset_flowint_ur _) c !!! k = 1) as Out_n.
          { admit. }
          assert (∀ x k, x ∈ dom I0' → 
            out (I0' !!! x : multiset_flowint_ur _) (Nx !!! x) !!! k ≤ 1)
            as Out_x.
          { admit. }
          assert (list_flow_upd_insert n Nx Mk S I0' = res) as Hflow'.
          { by rewrite /res. } 
          pose proof insert_flow_updk_summary Ky0' n Nx Mk S I0' res c
            Nx_key_rel Hcl KS_mk Nx_dom Nx_n VI0' Domm_I0' n_in_I0' Outset_n
            Insets_S Insets_x Out_n Out_x Hflow' as [II [nk [-> Hres]]].
          destruct Hres as [Dom_II_sub_I0 [n_in_II [nk_in_II [Mk_nk 
          [Nx_x [Domm_II [Heq [II_n [II_nk [II_x 
          [KS_n [KS_nk KS_x]]]]]]]]]]]].
          clear Hflow'.
          assert (nk ≠  n) as nk_neq_n.
          { admit. }
          assert (∀ x, x ∈ dom II ∖ {[n; nk]} → Mk !! x = Some true) as Mk_x.
          { admit. }
          set I := intf_merge II I0'.
          assert (dom I = dom I0') as Dom_I.
          { rewrite /I intf_merge_dom; try done. }
          assert (([^op set] x ∈ dom I, I !!! x) =
          ([^op set] x ∈ dom I0', I0' !!! x : multiset_flowint_ur nat)) as Def_I.
          { pose proof intf_merge_intfEq II I0' I Dom_II_sub_I0 Heq as H'.
            rewrite Dom_I. symmetry. apply H'. by rewrite /I. }
          assert (nk ∈ FP s0) as nk_in_s0.
          { rewrite Hs0 /FP -Dom_I0. rewrite Dom_I0' in Dom_II_sub_I0.
            clear -Dom_II_sub_I0 nk_in_II nk_neq_n. set_solver. }
          assert (nk ∈ dom I0) as nk_in_I0.
          { by rewrite Hs0 /FP -Dom_I0 in nk_in_s0. }
          exists I. split; last split; last split; last split.
          - by rewrite Dom_I Dom_I0' Hs0 /FP -Dom_I0.
          - by rewrite Def_I. 
          - intros x Hx Hxp Hxn. destruct (decide (x ∈ dom II)) as [Hx' | Hx'].
            + rewrite /I intf_merge_lookup_total; try done.
              destruct (decide (x = nk)) as [-> | Hxnk].
              * rewrite II_nk -Def_Mk; try done. 
                apply lookup_total_correct in Mk_nk.
                rewrite Mk_nk /I0' !lookup_total_insert_ne; try done.
                pose proof Hflow nk nk_in_s0 as Hnk.
                rewrite -Def_Mk in Hnk; try done.
                rewrite Mk_nk -I0_eq_s0 in Hnk. 
                destruct Hnk as (H1'&H2'&H3'&H4'&H5'&H6').
                repeat split.
                { rewrite flowint_inflow_map_set_dom Domm_I0; try done.
                  clear; set_solver. }
                { intros H'%H2'. rewrite /insets. 
                  rewrite flowint_inflow_map_set_dom Domm_I0; try done.
                  assert ({[nk;nk]} = {[nk]}) as -> by (clear; set_solver).
                  rewrite big_opS_singleton.
                  rewrite inflow_delete_set_inset /S; last first.
                  { admit. }  
                  intros k' Hk'. rewrite elem_of_difference. split.
                  apply H' in Hk'. rewrite /insets in Hk'. 
                  rewrite Domm_I0 in Hk'; try done.
                  by rewrite big_opS_singleton in Hk'.
                  intros Hk''. apply elem_of_gset_seq in Hk'.
                  apply elem_of_gset_seq in Hk''.
                  assert (k < Key s0 nk) as H''. { admit. }
                  clear -H'' Hk' Hk''. lia.
                  admit. admit. }
                { intros H'; clear -H'; done. }
                { by rewrite inflow_map_set_out_eq. }
                { by rewrite inflow_delete_set_outsets. }
                { intro k'. rewrite /insets. 
                  rewrite flowint_inflow_map_set_dom Domm_I0; try done.
                  assert ({[nk;nk]} = {[nk]}) as -> by (clear; set_solver).
                  rewrite big_opS_singleton.
                  rewrite inflow_delete_set_inset /S; last first.
                  { admit. } rewrite elem_of_difference.
                  rewrite /insets in H6'. 
                  rewrite Domm_I0 in H6'; try done.
                  pose proof H6' k' as H6'.
                  rewrite big_opS_singleton in H6'.
                  by intros [H'%H6' _]. }
              * rewrite II_x; last first.
                { clear -Hx' Hxn Hxnk; set_solver. }
                rewrite /I0'. rewrite !lookup_total_insert_ne; try done.
                assert (x ∈ FP s0) as H'%Hflow.
                { rewrite Hs0 /FP -Dom_I0. rewrite Dom_I Dom_I0' in Hx.
                  clear -Hx Hxn. set_solver. }
                rewrite -I0_eq_s0 in H'. 
                destruct H' as (H1'&H2'&H3'&H4'&H5'&H6').
                repeat split.
                { rewrite flowint_outflow_map_set_domm. 
                  rewrite flowint_inflow_delete_set_dom.
                  rewrite Domm_I0. clear; set_solver.
                  rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn. set_solver. }
                { intros H'. rewrite -Def_Mk in H'; try done.
                  rewrite lookup_total_alt Mk_x /= in H'. clear -H'; done.
                  clear -Hx' Hxn Hxnk. set_solver. }
                { assert (x ∈ dom II ∖ {[n; nk]}) as H'.
                  { clear -Hx' Hxn Hxnk. set_solver. }
                  assert (H'' := H'). apply KS_x in H'.
                  rewrite II_x in H'; try done.
                  rewrite /I0' in H'. 
                  rewrite !lookup_total_insert_ne in H'; try done.
                  intros H'''%H3'. by rewrite H' H'''. }
                { assert (x ∈ dom II ∖ {[nk]}) as H'.
                  { clear -Hx' Hxnk; set_solver. }
                  pose proof Nx_x x H' as H''.
                  rewrite Def_Nx in H''; try done.
                  destruct (Nexti s0 x 0) as [x' | ] eqn: Hx''; try done.
                  rewrite /outflow_delete_set /outflow_map_set /out_map /=.
                  assert (Nx !!! x = x') as ->.
                  { rewrite lookup_total_alt Def_Nx; try done.
                    by rewrite Hx''. }
                  apply leibniz_equiv.
                  assert (out (inflow_delete_set (I0 !!! x) x S) x' =
                    out (I0 !!! x) x') as ->.
                  { rewrite /out /inflow_delete_set /inflow_map_set. 
                  by rewrite {1}/out_map /=. }
                  set m := nzmap_map_set (λ _ n0 : nat, n0 - 1) S 
                              (out (I0 !!! x) x').
                  assert (m ≠ 0%CCM) as Hm.
                  { clear H''. intros H''. 
                    rewrite /ccmunit /= /lift_unit in H''.
                    rewrite nzmap_eq in H''.
                    rewrite -Def_Mk in H5'; try done.
                    rewrite lookup_total_alt Mk_x /= in H5'; try done.
                    rewrite /outsets H4' big_opS_singleton in H5'.
                    set kx := Key s0 x + 1. rewrite -/kx in H5'.
                    assert (kx ∈ gset_seq kx W) as Hkx.
                    { apply elem_of_gset_seq. admit. admit. }
                    apply H5' in Hkx. rewrite /outset in Hkx.
                    pose proof H'' kx as H''.
                    rewrite /m nzmap_lookup_empty /ccmunit /= /nat_unit in H''.
                    rewrite nzmap_lookup_total_map_set_ne in H''.
                    rewrite nzmap_elem_of_dom_total /ccmunit /= /nat_unit in Hkx.
                    done. rewrite /S. intros Hkx'. 
                    rewrite elem_of_gset_seq in Hkx'. admit. admit.
                    clear -Hx' Hxnk Hxn. set_solver. }
                  rewrite nzmap_dom_insert_nonzero; try done.
                  rewrite H4'. clear; set_solver. }
                { assert (x ∈ dom II ∖ {[n; nk]}) as H'.
                  { clear -Hx' Hxn Hxnk. set_solver. }
                  assert (x ∈ dom II ∖ {[nk]}) as H''.
                  { clear -H'. set_solver. }
                  rewrite -Def_Mk; try done. 
                  rewrite lookup_total_alt Mk_x /=; try done.
                  rewrite -Def_Mk in H5'; try done.
                  rewrite lookup_total_alt Mk_x /= in H5'; try done.
                  set Ix := inflow_delete_set (I0 !!! x) x S.
                  pose proof Nx_x x H'' as H'''.
                  rewrite Def_Nx in H'''; try done.
                  destruct (Nexti s0 x 0) as [x' | ] eqn: Hx''; try done.     
                  rewrite lookup_total_alt Def_Nx; try done.
                  rewrite Hx'' /=. rewrite /outsets.
                  rewrite /outsets H4' big_opS_singleton in H5'.
                  assert (dom (out_map (outflow_delete_set Ix x' S)) = {[x']})
                    as ->.
                  { rewrite /outflow_delete_set /outflow_map_set {1}/out_map /=.
                    apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero.
                    rewrite H4'. clear; set_solver. 
                    rewrite /Ix.
                    assert (out (inflow_delete_set (I0 !!! x) x S) x' =
                      out (I0 !!! x) x') as ->.
                    { rewrite /out /inflow_delete_set /inflow_map_set. 
                      by rewrite {1}/out_map /=. }
                    clear H''. intros H''. 
                    rewrite /ccmunit /= /lift_unit in H''.
                    rewrite nzmap_eq in H''.
                    set kx := Key s0 x + 1. rewrite -/kx in H5'.
                    assert (kx ∈ gset_seq kx W) as Hkx.
                    { apply elem_of_gset_seq. admit. admit. }
                    apply H5' in Hkx. rewrite /outset in Hkx.
                    pose proof H'' kx as H''.
                    rewrite nzmap_lookup_empty /ccmunit /= /nat_unit in H''.
                    rewrite nzmap_lookup_total_map_set_ne in H''.
                    rewrite nzmap_elem_of_dom_total /ccmunit /= /nat_unit in Hkx.
                    done. rewrite /S. intros Hkx'. 
                    rewrite elem_of_gset_seq in Hkx'. admit. admit. }
                  rewrite big_opS_singleton. 
                  rewrite outflow_delete_set_outset; last first.
                  { admit. }
                  rewrite /Ix. rewrite inflow_map_set_outset_ne.
                  intros k' Hk'. rewrite elem_of_difference.
                  split. by apply H5'.
                  rewrite /S. intros Hk''.
                  apply elem_of_gset_seq in Hk'.
                  apply elem_of_gset_seq in Hk''.
                  admit. admit. admit. }
                { intros k'. rewrite outflow_delete_set_insets.
                  pose proof H6' k' as H6'.
                  rewrite /insets H1' big_opS_singleton in H6'.
                  rewrite /insets. 
                  rewrite flowint_inflow_map_set_dom Domm_I0; last first.
                  { rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn; set_solver. }
                  assert ({[x; x]} = {[x]}) as -> by (clear; set_solver).
                  rewrite big_opS_singleton. 
                  rewrite inflow_delete_set_inset; last first.
                  { admit. }
                  rewrite elem_of_difference. by intros [H'%H6' _]. }
            + rewrite /I intf_merge_lookup_total_ne; last first; try done.
              { rewrite Dom_I in Hx. clear -Hx Hx'; set_solver. }
              rewrite /I0'. rewrite !lookup_total_insert_ne; try done.
              rewrite I0_eq_s0. apply Hflow. rewrite Hs0 /FP -Dom_I0.
              rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn; set_solver.
          - assert (p ∉ dom II) as p_notin_II.
            { admit. }
            rewrite /I intf_merge_lookup_total_ne; try done; last first.
            { rewrite Dom_I0'. clear -p_in_I0 n_neq_p p_notin_II; set_solver. }
            rewrite /I0'. rewrite lookup_total_insert_ne; try done.
            rewrite lookup_total_insert.
            apply Hflow in FP_p0. rewrite -I0_eq_s0 in FP_p0.
            rewrite /Marki Mark_p0 /Nexti Next_p0 in FP_p0.
            destruct FP_p0 as (H1'&H2'&H3'&H4'&H5'&H6').
            repeat split; try done.
            { rewrite /Ip0' /out_map /=. apply leibniz_equiv.
              rewrite nzmap_dom_insert_nonzero; try done.
              rewrite /dom /nzmap_dom. clear; set_solver. }
            { rewrite /outsets {2}/Ip0' /out_map /=.
              assert (dom <<[ n := out_pc ]>> ∅ = {[n]}) as ->.
              { apply leibniz_equiv.
                rewrite nzmap_dom_insert_nonzero; try done.
                rewrite /dom /nzmap_dom. clear; set_solver. }
              apply leibniz_equiv. rewrite big_opS_singleton.
              rewrite /Ip0' /outset /out /out_map /=. 
              rewrite nzmap_lookup_total_insert.
              rewrite /outsets H4' in H5'.
              apply leibniz_equiv_iff in H5'. rewrite big_opS_singleton in H5'.
              rewrite /outset in H5'. by rewrite /out_pc /Ip0. } 
          - rewrite /I intf_merge_lookup_total; try done.
            rewrite II_n /I0' lookup_total_insert.
            assert (dom (out_map (outflow_delete_set In0' c S)) = {[c]}) as Hdom.
            { rewrite /In0' /outflow_delete_set /outflow_map_set /out_map /=.
              rewrite /out /out_map /=.
              apply leibniz_equiv. 
              rewrite !nzmap_dom_insert_nonzero; try done.
              rewrite /dom /nzmap_dom. clear; set_solver.
              rewrite nzmap_lookup_total_insert.
              rewrite /ccmunit /= /lift_unit. intros H'.
              rewrite nzmap_eq in H'.
              set kk := k + 1. pose proof H' kk as H'.
              rewrite nzmap_lookup_empty /ccmunit /= /nat_unit in H'.
              rewrite nzmap_lookup_total_map_set_ne in H'. 
              rewrite /out_pc in H'. admit.
              admit. }
            repeat split; try done. 
            { intros _. rewrite outflow_delete_set_insets.
              rewrite /insets Dom_In0' big_opS_singleton.
              rewrite /In0' /inset /inf /inf_map /= lookup_insert /=.
              admit. }
            { apply leibniz_equiv. rewrite /outsets Hdom big_opS_singleton.
              rewrite outflow_delete_set_outset; last first.
              { admit. }
              rewrite /In0' /outset /out /out_map /=.
              rewrite nzmap_lookup_total_insert.
              admit. }
            { intros k'. rewrite outflow_delete_set_insets.
              rewrite /insets Dom_In0' big_opS_singleton /inset /inf 
                /inf_map /= /In0' lookup_insert /=.
              admit. } }
        set s0' := (FP0 ∪ {[n]}, C0 ∪ {[k]}, Mk0', Nx0', Ky0', I): snapshot.
        assert (abs s0 = C0) as Habs0'.
        { rewrite Hs0. by unfold abs. }
        iAssert (⌜snapshot_constraints s0'⌝)%I as "SShot0'".
        { iPureIntro. exists (FP0 ∪ {[n]}), (C0 ∪ {[k]}), Mk0', Nx0', Ky0', I.
          repeat split; try done.
          rewrite /Mk0'. rewrite dom_insert_L. 
          rewrite Dom_Mk0. clear; set_solver.
          rewrite /Nx0'. rewrite !dom_insert_L.
          rewrite Dom_Nx0. rewrite Hs0 in FP_p0. unfold FP in FP_p0. 
          clear -FP_p0; set_solver.
          rewrite /Ky0'. rewrite dom_insert_L.
          rewrite Dom_Ky0. clear; set_solver.
          destruct Hflupd as (H' & _). rewrite Hs0 in H'; by unfold FP in H'. } 
        assert (node_inv_pure s0 p → node_inv_pure s0' p) as Hp.
        { intros [Hc1 [Hc2 [Hc3 [Hc4 [Hc5 Hc6]]]]]. 
          assert (∀ i, Marki s0' p i = Marki s0 p i) as HM.
          { intros i; unfold Marki, Mark. rewrite /s0' /Mk0' Hs0.
            rewrite lookup_insert_ne; try done. }
          assert (Nexti s0' p 0 = Some n) as HN.
          { unfold Nexti, Next. rewrite /s0' /Nx0'.
            rewrite lookup_insert_ne; try done.
            rewrite lookup_insert. rewrite Def_next'.
            by rewrite lookup_insert. }
          assert (∀ i, i ≠ 0 → Nexti s0' p i = Nexti s0 p i) as HN'.
          { intros i Hi. unfold Nexti, Next. rewrite /s0' /Nx0' Hs0.
            rewrite lookup_insert_ne; try done.
            rewrite lookup_insert. rewrite Def_next'.
            rewrite lookup_insert_ne; try done.
            rewrite Hs0; by unfold Next. }
          assert (Key s0' p = Key s0 p) as HK.
          { rewrite /s0' Hs0 /Key /Ky0'.
            rewrite lookup_insert_ne; try done. }
          assert (FI s0' p = I !!! p) as HI.
          { rewrite /s0'; unfold FI. done. }
          split; last split; last split; last split; last split.
          - intros i. destruct (decide (i = 0)) as [-> | Hi].
            + intros _. by rewrite HN.
            + rewrite HM HN'; try done. apply Hc1.
          - intros [i H1']. rewrite HM. by rewrite /Marki Mark_p0.
          - intros _ H'. rewrite HN in H'. done. 
          - rewrite !elem_of_dom. unfold Nexti in HN. by rewrite HN.
          - rewrite /s0' /Mark /Mk0'. rewrite lookup_insert_ne; try done.
            rewrite Hs0 /Mark /Marki in Hc5. done.
          - rewrite HI HK HM HN /Marki. rewrite Mark_p0. apply Hflupd. }
        assert (node_inv_pure s0' n) as Hn.
        { assert (∀ i, Marki s0' n i = false) as HM.
          { intros i. rewrite /s0'. unfold Marki, Mark. rewrite /Mk0'. 
            rewrite lookup_insert. by rewrite Def_mark. }
          assert (Nexti s0' n 0 = Some c) as HN.
          { rewrite /s0' /Nexti /Next /Nx0'. rewrite lookup_insert.
            rewrite lookup_lookup_total. rewrite Def_next.
            by rewrite Hss0. admit. }
          split; last split; last split; last split; last split.
          - intros i. rewrite HM. intros ?; exfalso; try done.
          - intros ?; by rewrite HM.
          - rewrite HN. intros ? ?; exfalso; try done.
          - unfold Nexti in HN. by rewrite elem_of_dom HN.
          - rewrite elem_of_dom. admit.
          - rewrite HN HM /s0' /FI /Key /Ky0'. rewrite lookup_insert.
            apply Hflupd. }
        assert (∀ x, x ∈ FP s0' → node_inv_pure s0 x → node_inv_pure s0' x) 
          as Hpure.
        { intros x Hx. destruct (decide (x = p)) as [-> | Hxp]; try done.
          destruct (decide (x = n)) as [-> | Hxn]; try done.
          intros [Hx1 [Hx2 [Hx3 [Hx4 [Hx5 Hx6]]]]].
          assert (∀ i, Marki s0' x i = Marki s0 x i) as HM.
          { rewrite /s0' Hs0. unfold Marki, Mark.
            rewrite /Mk0'. rewrite lookup_insert_ne; try done. }
          assert (∀ i, Nexti s0' x i = Nexti s0 x i) as HN.
          { rewrite /s0' Hs0. unfold Nexti, Next.
            rewrite /Nx0'. rewrite !lookup_insert_ne; try done. }
          assert (Key s0' x = Key s0 x) as HK.
          { rewrite /s0' Hs0 /Key /Ky0'. by rewrite lookup_insert_ne. }
          assert (FI s0' x = I !!! x) as HI.
          { by rewrite /FI /s0'. }
          split; last split; last split; last split; last split.
          - intros i; rewrite HM HN. apply Hx1. 
          - rewrite HM. intros [i H1']. apply Hx2. 
            exists i. by rewrite <-HM.
          - by rewrite HM HN.
          - rewrite /s0' /Next /Nx0'. rewrite !lookup_insert_ne; try done.
            rewrite Hs0 in Hx4. by unfold Next in Hx4.
          - rewrite /s0'. unfold Mark.
            rewrite Hs0 in Hx5. rewrite /Mk0'. 
            rewrite lookup_insert_ne; try done. 
          - rewrite HM HN HK HI. apply Hflupd; try done.
            rewrite /s0' /FP in Hx. destruct Hflupd as (->&_).
            rewrite Hs0 /FP. done. }
        assert (FP s0' = FP s0 ∪ {[n]}) as FP_s0'.
        { by rewrite Hs0 /s0'; unfold FP. }
        assert (n ≠ hd) as n_neq_hd. { admit. }
        assert (n ≠ tl) as n_neq_tl. { admit. }
        assert (per_tick_inv s0') as PT_s0'.
        { destruct PT_s0 as (PT1&PT2&PT3&PT4&PT5&PT6).
          assert (FI s0' hd = FI s0 hd) as FI_s0_hd.
          { admit. }
          assert (∀ i, Marki s0' hd i = Marki s0 hd i) as Mark_s0_hd.
          { rewrite /s0' Hs0 /Marki /Mark /Mk0'.
            rewrite lookup_insert_ne; try done. }
          split; last split; last split; last split; last split.
          - destruct PT1 as (PT11&PT12&PT13&PT14&PT15&PT16&PT17).
            split; last split; last split; last split; last split; last split.
            + rewrite FI_s0_hd. try done.
            + rewrite FI_s0_hd. try done.
            + intros ?; rewrite Mark_s0_hd; try done.
            + rewrite /s0' /Key Hs0 in PT14.
              rewrite /Key /s0' /Ky0'. rewrite lookup_insert_ne; try done. 
            + rewrite /s0' /Key Hs0 in PT15.
              rewrite /Key /s0' /Ky0'. rewrite lookup_insert_ne; try done. 
            + rewrite FP_s0'; clear -PT16; set_solver.
            + rewrite FP_s0'; clear -PT17; set_solver.
          - unfold GFI.
            assert (FP s0' = dom I) as ->. 
            { symmetry. rewrite FP_s0'. apply Hflupd. }
            apply Hflupd.
          - rewrite FP_s0'. intros n' Hn'. rewrite elem_of_union in Hn'.
            destruct Hn' as [Hn' | Hn'].
            + apply Hpure. rewrite FP_s0'. clear -Hn'; set_solver.
              by apply PT3.
            + assert (n' = n) as -> by (clear -Hn'; set_solver).
              done.
          - intros n1 n2 i. destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite {1}/s0' /Nexti /Next /Nx0'. 
              rewrite lookup_insert_ne; try done.
              rewrite lookup_insert. rewrite Def_next'.
              destruct (decide (i = 0)) as [-> | Hi].
              * rewrite lookup_insert. intros [= <-].
                rewrite /s0' /Key /Ky0'. rewrite lookup_insert.
                rewrite lookup_insert_ne; try done. admit.
              * rewrite lookup_insert_ne; try done.
                pose proof PT4 p n2 i as H'.
                rewrite /Nexti /Next /Key Hs0 in H'.
                rewrite /s0' /Key /Ky0'. rewrite lookup_insert_ne; try done.
                destruct (decide (n2 = n)) as [-> | Hn2n].
                -- rewrite lookup_insert. admit.
                -- rewrite lookup_insert_ne; try done.
                   rewrite Hs0 /Next. done.
            + destruct (decide (n1 = n)) as [-> | Hn1n].
              * rewrite {1}/s0' /Nexti /Next /Nx0'. 
                rewrite lookup_insert. intros H'.
                rewrite /s0' /Key /Ky0'. rewrite lookup_insert.
                admit.
              * assert (Nexti s0' n1 i = Nexti s0 n1 i) as ->.
                { rewrite /s0' /Nexti /Next /Nx0' Hs0. 
                  rewrite !lookup_insert_ne; try done. }
                assert (Key s0' n1 = Key s0 n1) as ->.
                { rewrite /s0' /Key Hs0 /Ky0'. 
                  rewrite lookup_insert_ne; try done. }
                destruct (decide (n2 = n)) as [-> | Hn2n].
                -- admit.
                -- assert (Key s0' n2 = Key s0 n2) as ->.
                   { rewrite /s0' /Key Hs0 /Ky0'. 
                     rewrite lookup_insert_ne; try done. }
                   apply PT4.
          - rewrite FP_s0'. intros n1 n2 i. 
            destruct (decide (n1 = p)) as [-> | Hn1p].
            + rewrite /s0' /Nexti /Next /Nx0'. 
              rewrite lookup_insert_ne; try done.
              rewrite lookup_insert. rewrite Def_next'.
              destruct (decide (i = 0)) as [-> | Hi].
              { rewrite lookup_insert. intros [=<-]. clear; set_solver. }
              rewrite lookup_insert_ne; try done. intros H'%PT5. 
              clear -H'; set_solver.
            + destruct (decide (n1 = n)) as [-> | Hn1n].
              * rewrite /s0' /Nexti /Next /Nx0'.
                rewrite lookup_insert.  admit.
              * assert (Nexti s0' n1 i = Nexti s0 n1 i) as ->.
                { rewrite /s0' /Nexti /Next /Nx0' Hs0.
                  rewrite !lookup_insert_ne; try done. }
                intros H'%PT5. clear -H'; set_solver.
          - intros n'. rewrite FP_s0'. rewrite elem_of_union.
            intros [Hn' | Hn'].
            + assert (n' ≠ n). { clear -Hn' n_notin_s0. set_solver. }
              apply PT6 in Hn'. rewrite /s0' /Key /Ky0'. 
              rewrite lookup_insert_ne; try done.
              rewrite Hs0 /Key in Hn'. done.
            + assert (n' = n) as -> by (clear -Hn'; set_solver).
              rewrite /Key /s0' /Ky0'. by rewrite lookup_insert. }
        assert (transition_inv s0 s0') as Trans_s0.
        { split; last (repeat split).
          - intros n'. destruct (decide (n' = n)) as [-> | Hn'].
            + intros _ H'. rewrite /Marki /Mark /s0' /Mk0' in H'.
              rewrite lookup_insert in H'. rewrite Def_mark in H'.
              clear -H'; done.
            + rewrite /Marki /Mark Hs0 /s0' /Mk0'. 
              rewrite lookup_insert_ne; try done.
              intros H' H''. rewrite H' in H''. clear -H''; done.
          - intros n' i FP_n'. 
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            destruct (decide (n' = p)) as [-> | Hn'p].
            + rewrite /Marki /Mark /s0' /Nexti /Next /Mk0' Hs0 /Nx0'.
              rewrite lookup_insert_ne; try done. 
              rewrite lookup_insert_ne; try done.
              rewrite lookup_insert. rewrite Def_next'.
              destruct (decide (i = 0)) as [-> | Hi].
              * intros H'. rewrite /Mark Hs0 in Mark_p0.
                rewrite H' in Mark_p0. clear -Mark_p0; done.
              * rewrite lookup_insert_ne; try done.
                rewrite /Next Hs0. done.
            + assert (Nexti s0' n' i = Nexti s0 n' i) as ->.
              { rewrite /s0' Hs0 /Nexti /Next /Nx0'. 
                rewrite !lookup_insert_ne; try done. }
              done.
          - intros n' i FP_n'.
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            assert (Marki s0 n' i = Marki s0' n' i) as ->.
            { rewrite /Marki /Mark /s0' /Mk0' Hs0. 
              rewrite lookup_insert_ne; try done. }
            done. 
          - intros n' FP_n'. 
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            rewrite /s0' Hs0 /Key /Ky0'. rewrite lookup_insert_ne; try done.
          - rewrite FP_s0'. clear; set_solver. }

        iAssert ([∗ set] n ∈ FP s0', node_inv γ_ks s0' n)%I 
          with "[Node_p Res_rest Node_prest Node_n]" as "Res".
        { admit. }
        assert (per_tick_inv h s0') as PT_s0'.
        { assert (per_tick_inv h s0) as [PT1 [PT2 [PT3 PT4]]]. admit. 
          assert (FI s0' h = FI s0 h) as FI_s0_h.
          { admit. }
          split; last split; last split.
          - rewrite FI_s0_h. try done.
          - rewrite FI_s0_h. try done.
          - admit.
          - admit. }
        assert (transition_inv s0 s0') as Trans_s0.
        { destruct SShot0 as [Hs SShot0]. split; last (repeat split).
          - intros n' i FP_n'. rewrite /s0' Hs.
            unfold Marki, Mark, Nexti, Next. 
            rewrite /Mk0' /Nx0'. 
            rewrite lookup_insert_ne; last first. { admit. }
            destruct (decide (n' = p)) as [-> | Hn'].
            + rewrite lookup_insert.
              rewrite Def_next'.
              destruct (decide (i = 0)) as [-> | Hi].
              * intros H'. rewrite Hs in Mark_p0.
                unfold Mark in Mark_p0. 
                assert (true = false). 
                rewrite <-H'. rewrite <-Mark_p0. 
                admit.
                try done.
              * rewrite lookup_insert_ne; try done.
                rewrite Hs. unfold Next. try done.
            + rewrite lookup_insert_ne; try done.
              rewrite lookup_insert_ne; last first. { admit. }
              try done.
          - intros n' i FP_n'. rewrite /s0' Hs.
            unfold Marki, Mark. rewrite /Mk0'.
            assert (n' ≠ n) as n'_neq_n.
            { admit. }
            rewrite lookup_insert_ne; try done.
          - intros n' FP_n'. rewrite /s0' Hs. unfold Key.
            rewrite /Ky0'.
            assert (n' ≠ n) as n'_neq_n.
            { admit. }
            rewrite lookup_insert_ne; try done.
          - rewrite /s0' Hs. unfold FP.
            clear; set_solver. }
        admit.  


  Admitted.          
      
       
    

  
