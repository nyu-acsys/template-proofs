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

  Parameter permute_levels_spec : ∀ (L: nat),
        {{{ True }}}
           permute_levels #L
        {{{ (perm: loc) (vs: list val) (xs: list nat), RET #perm;
              perm ↦∗ vs
            ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
            ∗ ⌜xs ≡ₚ seq 1 (L-1)⌝ }}}.


  Lemma createNode_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght γ_sy t_id t0 succs ss k:
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ is_array succs ss }}}
           createNode #k #succs
        {{{ (n: Node) mark next,
            RET #n;
              is_array succs ss
            ∗ node n mark next k  
            ∗ (⌜∀ i, mark !! i = Some false⌝)
            ∗ (⌜∀ i, i < L → next !! i = Some (ss !!! i)⌝) }}}.
  Proof.
  Admitted.

  Parameter try_constraint_insert_spec : ∀ (pred curr new_node: Node) (i: nat),
     ⊢ (<<< ∀∀ mark next k, node pred mark next k >>>
           try_constraint #pred #curr #new_node #i @ ⊤
       <<< ∃∃ (success: bool) next',
              node pred mark next' k
            ∗ (match success with true => ⌜next !! i = Some curr 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := new_node]> next⌝
                                | false => ⌜(next !! i ≠ Some curr ∨ 
                                              mark !!! i = true)
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

  Lemma maintenanceOp_insert_rec_spec N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght k (n: Node) 
    preds succs (ps ss: list Node) perm vs xs (i: nat):
      main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
        {{{   preds ↦∗ ((λ n0 : loc, #n0) <$> ps)
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss)
            ∗ perm ↦∗ vs
            ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
            ∗ ⌜xs ≡ₚ seq 1 (L-1)⌝ }}}
           maintenanceOp_insert_rec #k #i #perm #preds #succs #n
        {{{ (ps' ss': list Node),
            RET #();
              preds ↦∗ ((λ n0 : loc, #n0) <$> ps')
            ∗ succs ↦∗ ((λ n0 : loc, #n0) <$> ss')
            ∗ perm ↦∗ vs }}}.
  Proof.
    iIntros "#HInv". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & Hperm & %Def_vs & %Perm_xs)".
    wp_lam. wp_pures. 
    destruct (bool_decide (Z.lt i (L - 1)%nat)) eqn: Hbool; wp_pures.
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
      awp_apply try_constraint_insert_spec; try done.
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAaccIntro with "Node_p".
      { iIntros "Node". iModIntro. iFrame "Hpost Hperm Hpreds Hsuccs".
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
    wp_lam. wp_pures. wp_apply permute_levels_spec; try done.
    iIntros (perm vs xs)"(Hperm & %Def_vs & %Perm_xs)". wp_pures. 
    wp_apply (maintenanceOp_insert_rec_spec with "[] [$Hperm $Hpreds $Hsuccs]"); 
      try done.
    iIntros (ps' ss')"(Hpreds & Hsuccs & Hperm)". 
    iApply "Hpost". iFrame.
  Qed.

  Lemma insertOp_spec N γ_r γ_t γ_m γ_td1 γ_td2 γ_ght γ_sy t_id t0 k:
          main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
            □ update_helping_protocol N γ_t γ_r γ_td1 γ_td2 γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     insert #hd #tl #k
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
      iAssert (¬ ⌜n ∈ FP s0⌝)%I as %n_notin_s0. 
      { iIntros "%H'". rewrite (big_opS_delete _ (FP s0) n); try done.
        iDestruct "Nodes" as "(Node_n' & _)".
        iApply (node_sep_star with "[$Node_n] [$Node_n']"). }
      assert (n ≠ p) as n_neq_p.
      { clear -FP_p0 n_notin_s0. set_solver. }
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAaccIntro with "Node_p".
      { iIntros "Node". iModIntro. iFrame "Hpost Node_n Hpreds Hsuccs".
        iNext; iExists M0, T0, s0. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
      iIntros (success next')"(Node_p & Hif)".
      destruct success; last first.
      + iDestruct "Hif" as %[H' ->]. 
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M0, T0, s0. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
        wp_pures. iApply "IH"; try done.
      + iDestruct "Hif" as %[Next_p0 [Mark_p0 Def_next']].

        iDestruct "SShot0" as %[FP0 [C0 [Mk0 [Nx0 [Ky0 [I0 
          [Hs0 [Dom_Mk0 [Dom_Nx0 [Dom_Ky0 Dom_I0]]]]]]]]]].
        iAssert (⌜per_tick_inv s0⌝)%I as %PT_s0.
        { iDestruct "Hist" as (M0')"(_&_&_&%&_)". iPureIntro.
          apply leibniz_equiv in Habs0. rewrite <-Habs0.
          by apply PT0. }
        assert (∀ x, x ∈ FP s0 → flow_constraints_I x (FI s0 x) 
                  (Mark s0 x !!! 0) (Next s0 x !! 0) (Key s0 x)) as Hflow.
        { destruct PT_s0 as (_&_&H'&_).
          intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&?). }
        set Mk0' := <[n := mark]> Mk0.
        set Nx0' := <[n := next]> (<[p := next']> Nx0).
        set Ky0' := <[n := k]> Ky0.
        iAssert (⌜∃ (I: gmap Node (multiset_flowint_ur nat)) (nk: Node),
            dom I = FP s0 ∪ {[n]}
          ∧ nk ∈ FP s0
          ∧ n ≠ nk
          ∧ k < Key s0 nk
          ∧ Mark s0 nk !!! 0 = false
          ∧ k ∈ keyset (I !!! n)
          ∧ (Key s0 nk ∈ keyset (I0 !!! nk) → Key s0 nk ∈ keyset (I !!! nk))
          ∧ keyset (I !!! nk) ∪ keyset (I !!! n) = keyset (I0 !!! nk)
          ∧ keyset (I !!! n) ## keyset (I !!! nk)
          ∧ (∀ x, x ∈ dom I ∖ {[ n; nk ]} → 
                    keyset (I !!! x) = keyset (I0 !!! x))
          ∧ ✓ ([^op set] x ∈ dom I, (I !!! x: multiset_flowint_ur nat))
          ∧ (∀ n1 n2 i, (Nx0' !!! n1) !! i = Some n2 → Ky0' !!! n1 < Ky0' !!! n2)
          ∧ (∀ n1 n2 i, (Nx0' !!! n1) !! i = Some n2 → n2 ∈ dom I)
          ∧ (∀ x, x ∈ dom I → x ≠ p → x ≠ n →
            flow_constraints_I x (I !!! x) (Mark s0 x !!! 0) (Next s0 x !! 0) (Key s0 x))
          ∧ (flow_constraints_I p (I !!! p) (false) (Some n) (Key s0 p) )
          ∧ (flow_constraints_I n (I !!! n) (false) (Some c) (k))⌝)%I
          as %[I [nk Hflupd]].
        { iPureIntro.
          set Ip0 := I0 !!! p. set Ic0 := I0 !!! c. set out_pc := out Ip0 c.
          set Ip0' := int {| infR := inf_map Ip0; outR :=  <<[n := out_pc]>> ∅ |}.
          set In0' := int {| infR := {[n := out_pc]}; 
                              outR := <<[c := out_pc]>> ∅ |}.
          assert (∀ x, I0 !!! x = FI s0 x) as I0_eq_s0.
          { intros x. rewrite Hs0; unfold FI. try done. }
          assert (Key s0 p < Key s0 c) as Key_pc.
          { destruct PT_s0 as (_&_&_&PT&_). rewrite /Nexti in PT.
            by pose proof PT p c 0 Next_p0. }
          assert (c ∈ FP s0) as FP_c0.
          { (* interpolation *) admit. }
          assert (Key s0 p < W) as Key_p0.
          { destruct PT_s0 as (_&_&PT&_). apply PT in FP_c0.
            destruct FP_c0 as (_&_&_&_&H'&_). clear -H' Key_pc; lia. }
          assert (Key s0 p < k) as Key_pn.
          { admit. }
          assert (k < Key s0 c) as Key_nc.
          { admit. }
          assert (insets (FI s0 p) ≠ ∅) as Insets_p_ne.
          { admit. }
          assert (out_pc ≠ 0%CCM) as Out_pc_nz.
          { apply Hflow in FP_p0. rewrite /Marki Mark_p0 /Nexti Next_p0 in FP_p0.
            destruct FP_p0 as (_&H'&_&(_&H'')&_). rewrite /outsets H' in H''. 
            rewrite -leibniz_equiv_iff big_opS_singleton in H''.
            rewrite /out_pc /Ip0 I0_eq_s0. rewrite /ccmunit /lift_unit.
            clear H'; intros H'. rewrite nzmap_eq in H'. pose proof H' W as H'.
            rewrite nzmap_lookup_empty /ccmunit /= /nat_unit in H'.
            rewrite /outset in H''. rewrite -nzmap_elem_of_dom_total2 -H'' in H'.
            apply H'. rewrite elem_of_gset_seq. clear -Key_p0; split; lia.
            done. }
          assert (p ≠ c) as p_neq_c.
          { intros ->. clear -Key_pc; lia. }
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

          assert (FP s0 = dom I0) as FP_s0_I0.
          { by rewrite /FP Hs0 Dom_I0. }
          rewrite FP_s0_I0 in Hflow.
          assert (∀ x, x ∈ dom I0 → dom (I0 !!! x: multiset_flowint_ur nat) 
            = {[x]}) as Domm_I0.
          { intros x Hx%Hflow. destruct Hx as (Hx&_). by rewrite I0_eq_s0. }
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
          { apply Hflow in p_in_I0. 
            rewrite /Nexti Next_p0 in p_in_I0.
            destruct p_in_I0 as (_&Hx&_). unfold out.
            rewrite -nzmap_elem_of_dom_total2. rewrite /Ip0 I0_eq_s0 Hx.
            clear -n_neq_c; set_solver. done. }
          assert (out Ip0' n = out Ip0 c) as Out_Ip0'_n.
          { rewrite {1}/out /out_map /Ip0' /=.
            rewrite nzmap_lookup_total_insert. done. }
          assert (out Ip0' c = 0%CCM) as Out_Ip0'_c.
          { rewrite {1}/out /out_map /Ip0' /=.
            rewrite nzmap_lookup_total_insert_ne; try done. }
          assert (∀ n0, n0 ≠ n → n0 ≠ c → out Ip0' n0 = out Ip0 n0) as Out_Ip0'. 
          { intros n' Hn' Hn''. apply Hflow in p_in_I0. 
            rewrite /Nexti Next_p0 in p_in_I0. destruct p_in_I0 as (_&Hx&_). 
            rewrite {1}/out /out_map /Ip0' /=. rewrite /out /Ip0 I0_eq_s0.
            rewrite nzmap_lookup_total_insert_ne; try done.
            rewrite nzmap_lookup_empty. symmetry. 
            rewrite -nzmap_elem_of_dom_total2. rewrite Hx. 
            clear -Hn''; set_solver. done. }
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
            { rewrite (big_opS_delete _ _ p) -/Io; try done.
              rewrite intComp_dom. clear; set_solver.
              rewrite (big_opS_delete _ _ p) -/Io in VI0; try done. }
            rewrite Dom_I0_FP in H'.
            clear -H' n_notin_s0. set_solver. }
          assert (dom (Ip0' ⋅ In0') ∩ dom Io = ∅) as Disj_Io.
          { rewrite intComp_dom. rewrite Dom_In0' -Dom_Ip0' (Domm_I0 p p_in_I0).
            clear -p_notin_Io n_notin_Io. set_solver.
            by destruct ContLeq0 as (_&?&_). }
          assert (out ([^op set] x ∈ dom I0, I0 !!! x: multiset_flowint_ur _) n 
                    = 0%CCM) as Out_s0_n.
          { set a := out ([^op set] x ∈ dom I0, I0 !!! x) n.
            destruct (decide (a = 0%CCM)) as [? | Ha]; try done. exfalso.
            rewrite /a in Ha. rewrite flow_big_op_out in Ha; try done.
            rewrite /ccmunit /lift_unit /= in Ha.
            assert (([^+ set] x ∈ dom I0, out (I0 !!! x) n) = 
              ([^+ set] x ∈ dom I0, (∅ : nzmap nat nat))) as H'.
            { apply ccm_big_opS_ext. intros x Hx. rewrite /out.
              rewrite -nzmap_elem_of_dom_total2. intros Hn.
              apply Hflow in Hx. destruct Hx as (_&Hx&Hx1&_).
              destruct (decide (insets (FI s0 x) = ∅)).
              { assert (outsets (FI s0 x) = ∅) by (clear -Hx1 e; set_solver).
                rewrite /outsets in H. apply leibniz_equiv_iff in H.
                rewrite (big_opS_delete _ (dom (out_map (FI s0 x))) n) in H.
                assert (outset nat (FI s0 x) n = ∅). admit.
                rewrite /outset /out in H0. admit.  }
              rewrite I0_eq_s0 Hx in Hn.
              destruct (Next s0 x !! 0) as [n'|] eqn: Hn'.
              rewrite elem_of_singleton in Hn; subst n'.
              destruct PT_s0 as (_&_&_&_&PT).
              pose proof PT x n 0 Hn' as PT. clear -PT n_notin_s0; try done.
              clear -Hn; set_solver. done. }
            rewrite H' ccm_big_opS_unit /ccm_unit /= /lift_unit in Ha.
            clear -Ha; done. by rewrite Dom_I0_FP. }
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
          { rewrite Def_Nx' /Nx0'. rewrite lookup_total_insert Def_next.
            by rewrite Hss0. admit. }
          assert (∀ x, x ≠ p → x ≠ n → Nx !! x = Next s0 x !! 0) as Def_Nx.
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
          { rewrite Def_Mk' /Mk0'. by rewrite lookup_total_insert Def_mark. }
          assert (∀ x, x ≠ n → Mk !!! x = Mark s0 x !!! 0) as Def_Mk.
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
                apply PT in H'. destruct H' as (_&_&H'&_).
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
              apply PT in Hn'. destruct Hn' as (_&_&_&Hn'&_).
              rewrite Hs0 /Mark in Hn'. done. }
          assert (∀ x, Ky0 !!! x = Key s0 x) as Def_Ky0.
          { rewrite Hs0. unfold Key. try done. }
          set S := gset_seq (Key s0 p + 1) k.
          set res := list_flow_upd_insert n Nx Mk S I0'.
          assert (dom out_pc = gset_seq (Key s0 p + 1) W) as Dom_outpc.
          { rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
            rewrite /Marki Mark_p0 /Nexti Next_p0 in p_in_I0.
            destruct p_in_I0 as (_&H'&_&(_&->)&_).
            pose proof H' Insets_p_ne as H'.
            rewrite I0_eq_s0 /outsets H' -leibniz_equiv_iff big_opS_singleton.
            by rewrite /outset. }
          assert (S ⊂ dom out_pc) as S_sub_outpc.
          { rewrite Dom_outpc /S. rewrite elem_of_subset. split.
            - intros x; rewrite !elem_of_gset_seq. clear -Range_k; lia.
            - intros H'. pose proof H' W as H'.
              rewrite !elem_of_gset_seq in H'. clear -H' Key_p0 Range_k. lia. }
          assert (nx_key_rel Nx Ky0') as Nx_key_rel.
          { destruct PT_s0 as (_&_&_&H'&H''). intros n1 n2.
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite Nx_p. intros [=<-]. rewrite /Ky0'.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. by rewrite Def_Ky0. } 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite Nx_n. intros [=<-]. rewrite /Ky0'.
              rewrite lookup_total_insert.
              rewrite lookup_total_insert_ne; try done.
              by rewrite Def_Ky0. }
            rewrite !Def_Nx /Ky0'; try done. 
            destruct (decide (n2 = n)) as [-> | Hn2n].
            { intros H1'. pose proof H'' n1 n 0 H1' as H''.
              by apply n_notin_s0 in H''. }
            rewrite !lookup_total_insert_ne; try done.
            rewrite !Def_Ky0. apply H'. }
          assert (dom I0' = dom I0 ∪ {[n]}) as Dom_I0'.
          { rewrite /I0'. rewrite !dom_insert_L. 
            clear -p_in_I0. set_solver. }
          assert (nx_mk_closed Nx Mk (dom I0')) as Hcl.
          { split; last split. 
            - by rewrite Dom_Nx Dom_I0' Dom_Nx0 Dom_I0.
            - by rewrite Dom_Mk Dom_I0' Dom_Mk0 Dom_I0.
            - destruct PT_s0 as (_&_&_&_&H'). intros n1 n2.
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
          assert (∀ n1 n2, insets (I0' !!! n1) ≠ ∅ → Nx !! n1 = Some n2 → 
            dom (out_map (I0' !!! n1: multiset_flowint_ur nat)) = {[n2]}) 
            as Nx_dom.
          { intros n1 n2. destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite Nx_n; intros Hin [=<-]. rewrite /I0'. 
              rewrite lookup_total_insert. rewrite /In0'.
              simpl. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done. 
              clear. unfold dom, nzmap_dom. set_solver. }
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite Nx_p; intros Hin [=<-]. rewrite /I0'.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert. rewrite /Ip0'.
              simpl. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done. 
              clear. unfold dom, nzmap_dom. set_solver. }
            intros Hin Hn1. assert (Hn1' := Hn1). apply elem_of_dom_2 in Hn1.
            rewrite Dom_Nx elem_of_union in Hn1.
            destruct Hn1 as [Hn1 | Hn1]; last first.
            { clear -Hn1 Hn1n; set_solver. } rewrite Dom_Nx0 -Dom_I0 in Hn1.
            apply Hflow in Hn1. rewrite Def_Nx in Hn1'. rewrite Hn1' in Hn1.
            destruct Hn1 as (_&H'&_). 
            rewrite /I0' !lookup_total_insert_ne; try done.
            rewrite /I0' in Hin. rewrite !lookup_total_insert_ne in Hin; try done.
            rewrite -I0_eq_s0 in H'. apply H'. all: done. }
          assert (n ∈ dom I0') as n_in_I0'.
          { rewrite Dom_I0'; clear; set_solver. }
          assert (∀ x, x ∈ dom I0' → Mk !!! x = true → 
            keyset (I0' !!! x) = ∅) as KS_mk.
          { intros x Hx Hmkx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx]; last first.
            { assert (x = n) as -> by (clear -Hx; set_solver).
              by rewrite lookup_total_alt Mk_n /= in Hmkx. }
            assert (x ≠ n) by (clear -Hx n_notin_I0; set_solver).
            apply Hflow in Hx. rewrite Def_Mk in Hmkx. rewrite Hmkx in Hx.
            destruct Hx as (_&_&_&Hx&_). rewrite /I0'.
            rewrite lookup_total_insert_ne; try done.
            destruct (decide (x = p)) as [-> | Hxp].
            { rewrite /Marki Mark_p0 in Hmkx. clear -Hmkx; done. }
            rewrite lookup_total_insert_ne; try done.
            by rewrite I0_eq_s0. done. }
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
          assert (S ⊂ insets (I0' !!! n)) as Insets_S.
          { rewrite /insets Domm_I0'; try done.
            rewrite /I0' lookup_total_insert.
            assert (([^union set] x ∈ {[n]}, inset nat In0' x) =
              inset nat In0' n) as ->.
            { by rewrite -leibniz_equiv_iff big_opS_singleton. }
            by rewrite /In0' /inset /inf /= lookup_insert /=. }
          assert (S ⊂ outset _ (I0' !!! n) c) as Outset_S.
          { by rewrite /I0' lookup_total_insert /In0' /outset /out /= 
              nzmap_lookup_total_insert. }
          assert (∀ x k', x ∈ dom I0' → 
            inf (I0' !!! x : multiset_flowint_ur _) x !!! k' ≤ 1) as Inf_x.
          { intros x k' Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx].
            - assert (Hx' := Hx). apply Hflow in Hx. 
              destruct Hx as (_&_&_&_&_&H'&_). rewrite /I0'.
              rewrite lookup_total_insert_ne; last first.
              { clear -Hx' n_notin_I0. set_solver. } 
              destruct (decide (x = p)) as [-> | Hxp].
              + rewrite lookup_total_insert /Ip0' /inf /= /Ip0.
                rewrite /inf -I0_eq_s0 in H'. apply H'.
              + rewrite lookup_total_insert_ne; try done.
                rewrite I0_eq_s0. apply H'.
            - rewrite elem_of_singleton in Hx; subst x.
              rewrite /I0' lookup_total_insert /In0' /inf /= lookup_insert /=.
              rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
              destruct p_in_I0 as (_&_&_&_&_&_&H').
              rewrite I0_eq_s0; apply H'. }
          assert (∀ x x' k, x ∈ dom I0' → 
            out (I0' !!! x : multiset_flowint_ur _) x' !!! k ≤ 1)
            as Out_x.
          { intros x x' k' Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx].
            - assert (Hx' := Hx). apply Hflow in Hx. 
              destruct Hx as (_&_&_&_&_&_&H'). rewrite /I0'.
              rewrite lookup_total_insert_ne; last first.
              { clear -Hx' n_notin_I0. set_solver. } 
              destruct (decide (x = p)) as [-> | Hxp].
              + rewrite lookup_total_insert /Ip0' /out /= /Ip0.
                destruct (decide (x' = n)) as [-> | Hx'n]; last first.
                { rewrite nzmap_lookup_total_insert_ne; try done.
                  rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia. }
                rewrite nzmap_lookup_total_insert.
                rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
                destruct p_in_I0 as (_&_&_&_&_&_&H'').
                rewrite I0_eq_s0; apply H'.
              + rewrite lookup_total_insert_ne; try done.
                apply Hflow in Hx'. rewrite I0_eq_s0; apply Hx'.
            - rewrite elem_of_singleton in Hx; subst x.
              rewrite /I0' lookup_total_insert /In0' /out /=.
              destruct (decide (x' = c)) as [-> | Hx'c]; last first.
              { rewrite nzmap_lookup_total_insert_ne; try done.
                rewrite !nzmap_lookup_empty /ccmunit /= /nat_unit. clear; lia. }
              rewrite nzmap_lookup_total_insert.
              rewrite /out_pc /Ip0. apply Hflow in p_in_I0.
              destruct p_in_I0 as (_&_&_&_&_&_&H').
              rewrite I0_eq_s0; apply H'. }
          assert (∀ x, x ∈ dom I0' → Mk !!! x = false → 
            Ky0' !!! n < Ky0' !!! x → S ## outsets (I0' !!! x)) as Disj_outsets.
          { intros x Hx Mk_x Hkey. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx]; last first.
            { rewrite elem_of_singleton in Hx; subst x. 
              clear -Hkey; lia. }
            rewrite /Ky0' lookup_total_insert lookup_total_insert_ne 
                in Hkey; try done. rewrite Def_Ky0 in Hkey.
            destruct (decide (x = p)) as [-> | Hxp].
            { clear -Hkey Key_pn; lia. }
            rewrite elem_of_disjoint. intros k' Hk1' Hk2'.
            destruct PT_s0 as (_&_&H'&_). rewrite {1}Hs0 /FP -Dom_I0 in H'.
            assert (Hx1 := Hx). apply H' in Hx. 
            destruct Hx as (_&_&_&_&_&Hx &Hx'). 
            assert (Mark s0 x !!! 0 = false) as Hm.
            { rewrite -Def_Mk; try done. clear -Hx1 n_notin_I0; set_solver. } 
            rewrite Hm in Hx'. destruct Hx' as (_&_&(_&H'')&_).
            rewrite /I0' !lookup_total_insert_ne in Hk2'; try done.
            rewrite I0_eq_s0 -H'' in Hk2'. rewrite elem_of_gset_seq in Hk2'.
            rewrite /S elem_of_gset_seq in Hk1'. 
            clear -Hkey Key_pn Hk1' Hk2'; lia.
            clear -Hx1 n_notin_I0; set_solver.
            clear -Hx n_notin_I0; set_solver. }
          assert (insets (I0' !!! p) ≠ ∅) as Insets_p_ne'.
          { admit. }
          assert (insets (I0' !!! n) ≠ ∅) as Insets_n_ne'.
          { admit. }
          assert (∀ x, x ∈ dom I0' → outsets (I0' !!! x) ⊆ insets (I0' !!! x))
            as Out_In.
          { intros x Hx. rewrite Dom_I0' elem_of_union in Hx.
            destruct Hx as [Hx | Hx].
            - assert (Hx' := Hx). apply Hflow in Hx.
              destruct Hx as (Hx0&Hx1&Hx2&_).
              destruct (decide (x = p)) as [-> | Hxp].
              + rewrite /insets /outsets Domm_I0'; try done; last first.
                { rewrite Dom_I0' elem_of_union; by left. }
                rewrite (Nx_dom p n Insets_p_ne' Nx_p) !big_opS_singleton.
                rewrite /I0' lookup_total_insert_ne; last done.
                rewrite lookup_total_insert /Ip0'.
                rewrite /outset /out /inset /inf /= /Ip0.
                rewrite nzmap_lookup_total_insert.
                rewrite /Nexti Next_p0 in Hx1.
                rewrite /outsets /insets Hx0 Hx1 in Hx2. 
                rewrite !big_opS_singleton in Hx2.
                rewrite -I0_eq_s0 /outset /inset in Hx2. apply Hx2. done.
              + rewrite /I0' !lookup_total_insert_ne; try done.
                by rewrite I0_eq_s0. clear -Hx' n_notin_I0; set_solver.
            - rewrite elem_of_singleton in Hx; subst x.
              rewrite /outsets /insets Domm_I0'; try done.
              rewrite (Nx_dom n c Insets_n_ne' Nx_n) !big_opS_singleton.
              rewrite /I0' lookup_total_insert /In0' /outset /inset /out /inf 
                nzmap_lookup_total_insert lookup_insert /=. done. }
          assert (list_flow_upd_insert n Nx Mk S I0' = res) as Hflow'.
          { by rewrite /res. } 
          
          pose proof insert_flow_updk_summary Ky0' n Nx Mk S I0' res c
            Nx_key_rel Hcl KS_mk Disj_outsets Nx_dom Out_In Nx_n VI0' 
            Domm_I0' n_in_I0' Insets_S Outset_S Inf_x Out_x Hflow' 
            as [II [nk [-> Hres]]].
          destruct Hres as [Dom_II_sub_I0 [n_in_II [nk_in_II [n_neq_nk [Mk_nk 
            [Mk_x [Nx_x [Key_n [Domm_II [Heq [II_n [II_nk [II_x [Inf_x' [Out_x' 
            [Dom_out [Out_In' [KS_n [KS_nk [KS_x S_in_nk]]]]]]]]]]]]]]]]]]]].
          clear Hflow'.
          set I := intf_merge II I0'.
          assert (dom I = dom I0') as Dom_I.
          { rewrite /I intf_merge_dom; try done. }
          assert (([^op set] x ∈ dom I, I !!! x) =
          ([^op set] x ∈ dom I0', I0' !!! x : multiset_flowint_ur nat)) as Def_I.
          { pose proof intf_merge_intfEq II I0' I Dom_II_sub_I0 Heq as H'.
            rewrite Dom_I. symmetry. apply H'. by rewrite /I. }
          assert (nk ∈ FP s0) as nk_in_s0.
          { rewrite Hs0 /FP -Dom_I0. rewrite Dom_I0' in Dom_II_sub_I0.
            clear -Dom_II_sub_I0 nk_in_II n_neq_nk. set_solver. }
          assert (nk ∈ dom I0) as nk_in_I0.
          { by rewrite Hs0 /FP -Dom_I0 in nk_in_s0. }
          assert (p ∉ dom II) as p_notin_II.
          { intros H'. assert (p ∈ dom II ∖ {[n]}) as H''. clear -H' n_neq_p.
            set_solver. apply Key_n in H''. 
            rewrite /Ky0' lookup_total_insert in H''.
            rewrite lookup_total_insert_ne in H''; try done.
            rewrite Hs0 /Key in Key_pn. clear -H'' Key_pn.
            assert (Ky0 !!! p = match Ky0 !! p with Some k => k | None => 0 end)
              as H1'. done. rewrite -H1' in Key_pn. lia. }
          assert (I0' !!! nk = I0 !!! nk) as I0'_nk.
          { rewrite /I0' !lookup_total_insert_ne; try done. 
            clear -p_notin_II nk_in_II; set_solver. }
          assert (keyset (I0' !!! n) = ∅) as KS_n'.
          { rewrite /keyset /insets /outsets Domm_I0'; try done.
            rewrite (Nx_dom n c Insets_n_ne' Nx_n) -leibniz_equiv_iff !big_opS_singleton.
            rewrite /inset /outset /I0' lookup_total_insert /In0' /inf /out /=.
            rewrite lookup_insert nzmap_lookup_total_insert /=.
            clear; set_solver. }
          assert (S ⊆ keyset (I0 !!! nk)) as S_in_ksnk.
          { by rewrite -I0'_nk. }
          assert (keyset Ip0' = keyset (I0 !!! p)) as KS_Ip0'.
          { rewrite /keyset. assert (insets Ip0' = insets (I0 !!! p)) as ->. 
            rewrite /insets /Ip0' /dom /flowint_dom /= /Ip0.
            apply big_opS_ext. intros x Hx. by rewrite /inset /inf /=.
            assert (outsets Ip0' = outsets (I0 !!! p)) as ->.
            rewrite /outsets. apply Hflow in p_in_I0.
            rewrite /Nexti Next_p0 -I0_eq_s0 in p_in_I0. 
            destruct p_in_I0 as (_&->&_). pose proof Nx_dom p n Insets_p_ne' Nx_p as H'.
            rewrite /I0' lookup_total_insert_ne in H'; try done.
            rewrite lookup_total_insert in H'. rewrite H'.
            rewrite -leibniz_equiv_iff !big_opS_singleton.
            rewrite /outset /Ip0' {1}/out /= nzmap_lookup_total_insert.
            clear; done. rewrite I0_eq_s0; done. done. }
          assert (k < Key s0 nk) as k_lt_nk.
          { assert (nk ∈ dom II ∖ {[n]}) as H'.
            clear -nk_in_II n_neq_nk. set_solver.
            apply Key_n in H'. rewrite /Ky0' lookup_total_insert in H'.
            rewrite lookup_total_insert_ne in H'; try done.
            by rewrite Def_Ky0 in H'. } 
          exists I, nk. split; last split; last split; last split; 
            last split; last split; last split; last split; last split; 
            last split; last split; last split; last split; last split;
            last split.
          - by rewrite Dom_I Dom_I0' Hs0 /FP -Dom_I0.
          - done.
          - done.
          - done.
          - rewrite -Def_Mk; try done. by rewrite lookup_total_alt Mk_nk /=.
          - rewrite /I intf_merge_lookup_total; try done. rewrite KS_n.
            rewrite elem_of_union /S; right. rewrite elem_of_gset_seq.
            clear -Key_pn. split; lia.
          - intros H'. rewrite /I intf_merge_lookup_total; try done. 
            rewrite KS_nk elem_of_difference. split. by rewrite I0'_nk.
            rewrite /S elem_of_gset_seq. clear -k_lt_nk; lia. 
          - rewrite /I !intf_merge_lookup_total; try done. rewrite KS_n KS_nk.
            rewrite I0'_nk KS_n'. clear -S_in_ksnk; apply set_eq_subseteq. 
            split; first by set_solver. intros x Hx.
            rewrite !elem_of_union elem_of_difference.
            destruct (decide (x ∈ S)); try set_solver.
          - rewrite /I !intf_merge_lookup_total; try done. 
            rewrite KS_n KS_nk KS_n'. clear; set_solver.
          - intros x Hx. destruct (decide (x ∈ dom II)) as [Hx' | Hx'].
            + rewrite /I intf_merge_lookup_total; try done.
              rewrite KS_x; try done. rewrite /I0' !lookup_total_insert_ne.
              done. clear -p_notin_II Hx'; set_solver. clear -Hx; set_solver.
              clear -Hx Hx'; set_solver.
            + rewrite /I intf_merge_lookup_total_ne; try done.
              destruct (decide (x = p)) as [-> | Hxp].
              * rewrite /I0' lookup_total_insert_ne; try done.
                by rewrite lookup_total_insert.
              * rewrite /I0' !lookup_total_insert_ne; try done.
                clear -Hx; set_solver.
              * rewrite Dom_I in Hx. clear -Hx Hx'; set_solver.
          - by rewrite Def_I. 
          - intros n1 n2 i. destruct PT_s0 as (_&_&_&PT&PT'). 
            rewrite /Nexti /Next Hs0 /Key in PT. rewrite /Nx0'. 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite lookup_total_insert Def_next. rewrite /Ky0'.
              rewrite lookup_total_insert. admit. }
            rewrite lookup_total_insert_ne; try done.
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite lookup_total_insert Def_next'.
              destruct (decide (i = 0)) as [-> | Hi0].
              rewrite lookup_insert. intros [=<-].
              rewrite /Ky0' lookup_total_insert_ne; try done.
              by rewrite lookup_total_insert Def_Ky0.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_insert_ne; try done.
              destruct (decide (n2 = n)) as [-> | Hn2n].
              { rewrite /Nexti in PT'. intros H'%PT'. clear -H' n_notin_s0; done. }
              rewrite lookup_total_insert_ne; try done.
              rewrite /Next Hs0. apply PT. }
            rewrite lookup_total_insert_ne; try done.
            destruct (decide (n2 = n)) as [-> | Hn2n].
            { rewrite /Nexti /Next {1}Hs0 in PT'. intros H'%PT'. 
              clear -H' n_notin_s0; done. }
            rewrite !lookup_total_insert_ne; try done. apply PT.
          - intros n1 n2 i. destruct PT_s0 as (_&_&_&_&PT).
            rewrite /Nexti /Next {1}Hs0 FP_s0_I0 in PT. rewrite /Nx0' Dom_I Dom_I0'. 
            destruct (decide (n1 = n)) as [-> | Hn1n].
            { rewrite lookup_total_insert Def_next. admit. }
            destruct (decide (n1 = p)) as [-> | Hn1p].
            { rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert Def_next'.
              destruct (decide (i = 0)) as [-> | Hi0].
              rewrite lookup_insert. intros [=<-]. clear; set_solver.
              rewrite lookup_insert_ne; try done.
              destruct (decide (n2 = n)) as [-> | Hn2n].
              { intros _; clear; set_solver. }
              rewrite /Next Hs0. intros H'%PT. clear -H' Hn2n; set_solver. }
            rewrite !lookup_total_insert_ne; try done.
            intros H'%PT. clear -H'; set_solver.
          - intros x Hx Hxp Hxn. destruct (decide (x ∈ dom II)) as [Hx' | Hx'].
            + rewrite /I intf_merge_lookup_total; try done.
              assert (I0' !!! x = I0 !!! x) as HI. 
              { rewrite /I0' !lookup_total_insert_ne; try done. }
              assert (insets (II !!! x) = insets (FI s0 x) ∖ S) as HInset.
              { rewrite /insets Domm_II; try done.
                assert (dom (FI s0 x) = {[x]}) as ->.
                { rewrite -I0_eq_s0 Domm_I0; try done. 
                  rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn; set_solver. }
                rewrite -leibniz_equiv_iff !big_opS_singleton.
                destruct (decide (x = nk)) as [-> | Hxnk].
                rewrite II_nk HI.
                rewrite inflow_delete_set_inset I0_eq_s0. done.
                apply Hflow in nk_in_I0. destruct nk_in_I0 as (_&_&_&_&_&H'&_).
                intros k' Hk'. apply H'.
                rewrite II_x /outflow_delete_set. rewrite outflow_map_set_inset.
                rewrite inflow_delete_set_inset HI I0_eq_s0. done.
                assert (x ∈ dom I0) as x_in_I0%Hflow.
                { rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn. set_solver. }
                destruct x_in_I0 as (_&_&_&_&_&H'&_). intros k' Hk'. apply H'.
                clear -Hx' Hxnk Hxn; set_solver. }
              destruct (decide (x = nk)) as [-> | Hxnk].
              * apply Hflow in nk_in_I0 as Hnk.
                destruct Hnk as (H1'&H2'&H3'&H4'&H5'&H6'&H7').
                apply lookup_total_correct in Mk_nk.
                rewrite -Def_Mk; last done. rewrite Mk_nk.
                rewrite -Def_Nx; [|done|done]. 
                split; last split; last split; last split; last split; last split.
                { apply Domm_II; try done. }
                { rewrite Dom_out; try done. rewrite HI I0_eq_s0 H2'.
                  rewrite Def_Nx; try done. admit. }
                { apply Out_In'; try done. }
                { rewrite -Def_Mk in H4'; try done. rewrite Mk_nk in H4'.
                  destruct H4' as [H4' H4'']. split.
                  rewrite HInset. intros k' Hk'. rewrite elem_of_difference. 
                  split. by apply H4' in Hk'.
                  intros Hk''. apply elem_of_gset_seq in Hk'.
                  apply elem_of_gset_seq in Hk''.
                  clear -k_lt_nk Hk' Hk''. lia.
                  by rewrite II_nk inflow_delete_set_outsets HI I0_eq_s0. }
                { rewrite HInset. intros k'; clear -H5'; set_solver. }
                { intros k'; apply Inf_x'; try done. }
                { intros x' k'; apply Out_x'; try done. }
              * assert (x ∈ dom I0) as Hx''%Hflow. 
                { rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn. set_solver. }
                assert (Mark s0 x !!! 0 = true) as HM. 
                { rewrite -Def_Mk; try done. rewrite lookup_total_alt Mk_x /=.
                  done. clear -Hx' Hxn Hxnk; set_solver. }
                rewrite HM. rewrite HM in Hx''.
                destruct Hx'' as (H1'&H2'&H3'&H4'&H5'&H6'&H7').
                split; last split; last split; last split; last split; last split.
                { apply Domm_II; try done. }
                { rewrite Dom_out; try done. intros Hin. rewrite HI I0_eq_s0.
                  apply H2'. admit. }
                { apply Out_In'; try done. }
                { rewrite KS_x. by rewrite HI I0_eq_s0.
                  clear -Hx' Hxn Hxnk; set_solver. }
                { rewrite HInset. intros k'; clear -H5'; set_solver. }
                { intros k'; apply Inf_x'; try done. }
                { intros x' k'; apply Out_x'; try done. }
            + rewrite /I intf_merge_lookup_total_ne; last first; try done.
              { rewrite Dom_I in Hx. clear -Hx Hx'; set_solver. }
              rewrite /I0'. rewrite !lookup_total_insert_ne; try done.
              rewrite I0_eq_s0. apply Hflow.
              rewrite Dom_I Dom_I0' in Hx. clear -Hx Hxn; set_solver.
          - assert (p ∈ dom I0') as p_in_I0'.
            { rewrite Dom_I0'. clear -p_in_I0; set_solver. }
            rewrite /I intf_merge_lookup_total_ne; try done; last first.
            { rewrite Dom_I0'. clear -p_in_I0 n_neq_p p_notin_II; set_solver. }
            rewrite /I0'. rewrite lookup_total_insert_ne; try done.
            rewrite lookup_total_insert. apply Hflow in p_in_I0. 
            rewrite -I0_eq_s0 in p_in_I0.
            rewrite /Marki Mark_p0 /Nexti Next_p0 in p_in_I0.
            destruct p_in_I0 as (H1'&H2'&H3'&H4'&H5'&H6'&H7').
            repeat split; try done.
            { intros _. rewrite /Ip0' /out_map /=. apply leibniz_equiv.
              rewrite nzmap_dom_insert_nonzero; try done.
              rewrite /dom /nzmap_dom. clear; set_solver. }
            { apply Out_In in p_in_I0'. rewrite /I0' in p_in_I0'.
              rewrite lookup_total_insert_ne in p_in_I0'; try done.
              rewrite lookup_total_insert in p_in_I0'; try done. }
            { rewrite /insets -Dom_Ip0' /Ip0 H1'. rewrite big_opS_singleton.
              rewrite /Ip0' /inset /inf /= /Ip0.
              destruct H4' as [H4' _].
              rewrite /insets H1' in H4'. rewrite big_opS_singleton in H4'.
              rewrite /inset in H4'. apply H4'. }
            { assert (outsets Ip0' = outsets (I0 !!! p)) as ->.
              rewrite -I0_eq_s0 in Insets_p_ne.
              rewrite /outsets (H2' Insets_p_ne) {2}/Ip0' /out_map /=.
              assert (dom <<[ n := out_pc ]>> ∅ = {[n]}) as ->.
              rewrite -leibniz_equiv_iff. rewrite nzmap_dom_insert_nonzero; try done.
              clear; rewrite /dom. set_solver.
              rewrite -leibniz_equiv_iff !big_opS_singleton.
              rewrite /Ip0' /outset /out {1}/out_map /= nzmap_lookup_total_insert.
              rewrite /out_pc. done.
              apply H4'. }
            { intros x' k'. apply (Out_x _ x' k') in p_in_I0'. 
              rewrite /I0' in p_in_I0'.
              rewrite lookup_total_insert_ne in p_in_I0'; try done.
              rewrite lookup_total_insert in p_in_I0'; try done. }
          - rewrite /I intf_merge_lookup_total; try done.
            rewrite II_n /I0' lookup_total_insert.
            assert (dom (out_map (outflow_delete_set In0' c S)) = {[c]}) as Hdom.
            { apply Dom_out in n_in_II. rewrite II_n {1}/I0' in n_in_II.
              rewrite lookup_total_insert in n_in_II.
              rewrite n_in_II. pose proof Nx_dom n c Insets_n_ne' Nx_n as H'.
              by rewrite /I0' lookup_total_insert in H'. }
            assert (insets In0' = dom out_pc) as Hinset.
            { rewrite /insets Dom_In0' -leibniz_equiv_iff big_opS_singleton.
              by rewrite /inset /In0' /inf /= lookup_insert /=. }
            assert (∀ x' k', out In0' x' !!! k' ≤ 1) as Out_In0'.
            { apply Dom_II_sub_I0 in n_in_II.
              intros x' k'. apply (Out_x _ x' k') in n_in_II.
              rewrite /I0' lookup_total_insert in n_in_II. apply n_in_II. }
            repeat split; try done.
            { rewrite outflow_delete_set_insets /outsets Hdom.
              rewrite big_opS_singleton outflow_delete_set_outset; try done.
              rewrite Hinset /In0' /outset /out /= nzmap_lookup_total_insert.
              clear; set_solver. }
            { rewrite outflow_delete_set_insets Hinset Dom_outpc.
              intros k'; rewrite !elem_of_gset_seq. clear -Key_pn; lia. }
            { rewrite /outsets Hdom. rewrite -leibniz_equiv_iff big_opS_singleton.
              rewrite outflow_delete_set_outset; try done.
              rewrite /In0' /outset /out /= nzmap_lookup_total_insert Dom_outpc.
              rewrite /S. rewrite leibniz_equiv_iff set_eq_subseteq.
              split; intros k'; rewrite elem_of_difference !elem_of_gset_seq.
              all: clear -Key_pn; lia. }
            { rewrite outflow_delete_set_insets Hinset Dom_outpc.
              intros k'; rewrite elem_of_gset_seq. clear; lia. } 
            { intros k'. apply (Inf_x' _ k') in n_in_II.
              by rewrite II_n /I0' lookup_total_insert in n_in_II. }
            { intros x' k'. apply (Out_x' _ x' k') in n_in_II.
              by rewrite II_n /I0' lookup_total_insert in n_in_II. } }
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

        assert (FP s0' = FP s0 ∪ {[n]}) as FP_s0'.
        { by rewrite Hs0 /s0'; unfold FP. }
        assert (∀ n', n' ≠ p → n' ≠ n → Next s0' n' = Next s0 n') as HN.
        { intros n' Hp Hn. rewrite /Next /s0' Hs0 /= /Nx0'.
          rewrite !lookup_insert_ne; try done. }
        assert (Next s0' n = next) as HNn.
        { rewrite /Next /s0' /= /Nx0'. rewrite lookup_insert; try done. }
        assert (Next s0' p = <[0:=n]> (Next s0 p)) as HNp.
        { rewrite /Next /s0' Hs0 /= /Nx0'. rewrite lookup_insert_ne; try done.
          rewrite lookup_insert Def_next' /Next Hs0. done. }
        assert (∀ n', n' ≠ n → Key s0' n' = Key s0 n') as HK.
        { intros n' Hn. rewrite /Key /s0' Hs0 /= /Ky0'. 
          rewrite lookup_insert_ne; try done. }
        assert (Key s0' n = k) as HKn.
        { rewrite /Key /s0' /= /Ky0' lookup_insert; try done. }

        assert (∀ n', FI s0' n' = I !!! n') as HI.
        { by rewrite /FI /s0' /=. }
        assert (∀ n', n' ≠ n → Mark s0' n' = Mark s0 n') as HM.
        { intros n' Hn. by rewrite /FI /s0' Hs0 /Mk0' /= lookup_insert_ne. }
        assert (Mark s0' n = mark) as HMn.
        { by rewrite /FI /s0' /Mk0' /= lookup_insert. }
        assert (n ≠ hd) as n_neq_hd. 
        { intros ->. destruct PT_s0 as (PT&_). 
          destruct PT as (_&_&_&H'&_).
          clear -H' n_notin_s0. done. }
        assert (n ≠ tl) as n_neq_tl. 
        { intros ->. destruct PT_s0 as (PT&_). 
          destruct PT as (_&_&_&_&H').
          clear -H' n_notin_s0. done. }

        assert (per_tick_inv s0') as PT_s0'.
        { destruct PT_s0 as (PT1&PT2&PT3&PT4&PT5).
          split; last split; last split; last split.
          - destruct PT1 as (PT11&PT12&PT13&PT14&PT15).
            split; last split; last split; last split.
            + intros ?; rewrite /Marki HM; try done. apply PT11.
            + rewrite HK; try done. 
            + rewrite HK; try done. 
            + rewrite FP_s0'; clear -PT14; set_solver.
            + rewrite FP_s0'; clear -PT15; set_solver.
          - unfold GFI.
            assert (FP s0' = dom I) as ->. 
            { symmetry. rewrite FP_s0'. apply Hflupd. }
            apply Hflupd.
          - rewrite FP_s0'. intros n' Hn'.
            destruct (decide (n' = n)) as [-> | Hn'n].
            + rewrite HMn HNn HKn HI. 
              split; last split; last split; last split; last split.
              * intros ?; by rewrite lookup_total_alt Def_mark /=.
              * intros i; rewrite Def_next. split; try done. admit.
              * rewrite elem_of_dom Def_next; try done. admit.
              * rewrite elem_of_dom Def_mark. done.
              * clear -Range_k; lia.
              * rewrite (lookup_total_alt mark) Def_mark /= Def_next.
                rewrite Hss0. apply Hflupd. admit.
            + assert (n' ∈ FP s0) as H'. clear -Hn' Hn'n; set_solver.
              apply PT3 in H'.
              destruct H' as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6).
              destruct (decide (n' = p)) as [-> | Hn'p]; last first.
              * rewrite HM. rewrite HK. rewrite HN. rewrite HI.
                all: try done. 
                split; last split; last split; last split; last split; try done.
                apply Hflupd. assert (dom I = FP s0 ∪ {[n]}) as ->.
                apply Hflupd. clear -Hn' Hn'n; set_solver. all: done.
              * rewrite HM. rewrite HNp. rewrite HK. rewrite HI.
                all: try done.
                split; last split; last split; last split; last split; try done.
                { intros i. destruct (decide (i = 0)) as [-> | Hi]. 
                  rewrite lookup_insert. split; try done. admit. }
                { rewrite dom_insert. clear; set_solver. }
                { rewrite lookup_insert Mark_p0. apply Hflupd. }
          - intros n1 n2 i. rewrite /Nexti /Next /s0' /Key. apply Hflupd.
          - intros n1 n2 i. rewrite /Nexti /Next /s0' /FP.
            destruct Hflupd as [H' H'']. rewrite Hs0 /FP in H'.
            rewrite -H'. apply H''. }
        assert (transition_inv s0 s0') as Trans_s0.
        { repeat split.
          - intros n'. destruct (decide (n' = n)) as [-> | Hn'].
            + intros _ H'. rewrite /Marki /Mark /s0' /Mk0' in H'.
              rewrite lookup_insert in H'. 
              rewrite lookup_total_alt Def_mark /= in H'.
              clear -H'; done.
            + rewrite /Marki /Mark Hs0 /s0' /Mk0'. 
              rewrite lookup_insert_ne; try done.
              intros H' H''. rewrite H' in H''. clear -H''; done.
          - intros n' i FP_n'.
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            rewrite /Marki HM; try done.
          - intros n' FP_n'. 
            assert (n' ≠ n) by (clear -FP_n' n_notin_s0; set_solver).
            rewrite HK; try done.
          - rewrite FP_s0'. clear; set_solver. }
        
        iAssert (|={⊤ ∖ ⊤ ∖ ↑cntrN N}=> resources γ_ks s0')%I 
          with "[GKS Nodes_KS Node_n Node_p Nodes_rest]" as ">Res".
        { rewrite (big_sepS_delete _ _ nk); last first. 
          { apply Hflupd. }
          iDestruct "Nodes_KS" as "(KS_nk & Nodes_KS)".
          iDestruct (own_valid with "KS_nk") as "%H'".
          iDestruct (own_valid with "GKS") as "%H''".
          rewrite auth_frag_valid in H'. rewrite auth_auth_valid in H''.
          assert (k ∈ keyset (I !!! n)) as KS_n.
          { apply Hflupd. }
          assert (Marki s0 nk 0 = false) as Mark_nk.
          { apply Hflupd. }
          assert (Key s0 nk ∈ keyset (I !!! nk)) as KS_nk.
          { apply Hflupd. rewrite /valid /cmra_valid /= /ucmra_valid /= in H'.
            rewrite /Content Mark_nk {2}Hs0 /FI in H'. clear -H'; set_solver. }
          assert (k ≠ Key s0 nk) as k_neq_Keynk.
          { intros H1'. destruct Hflupd as (_&_&_&H1''&_).
            rewrite H1' in H1''. clear -H1''; lia. }
          assert (Marki s0' nk 0 = false) as Mark_nk'.
          { rewrite /Marki /Mark /s0' /Mk0' lookup_insert_ne.
            by rewrite /Marki /Mark Hs0 in Mark_nk.
            apply Hflupd. }
          assert (Marki s0' n 0 = false) as Mark_n'.
          { rewrite /Marki /Mark /s0' /Mk0' lookup_insert lookup_total_alt.
            by rewrite Def_mark. }
          assert (keyset (I !!! n) ## keyset (I !!! nk)) as Disj_ks.
          { apply Hflupd. }
          iMod (own_update_2 γ_ks
                  (● prodKS (KS, abs s0))
                  (◯ prodKS (keyset (FI s0 nk), Content s0 nk))
                  ((● prodKS (KS, abs s0 ∪ {[k]})) ⋅
                      (◯ prodKS (keyset (FI s0 nk), Content s0 nk ∪ {[k]})))
                  with "[$GKS] [$KS_nk]") as "H'".
          { apply auth_update. apply auth_ks_local_update_insert; try done. 
            - rewrite /FI Hs0. destruct Hflupd as (_&_&_&_&_&_&_&H1'&_).
              rewrite -H1' elem_of_union; by right.
            - rewrite /Content Mark_nk. clear -k_neq_Keynk; set_solver.
            - admit. }
          iDestruct "H'" as "(GKS & H')".
          assert (keyset (FI s0 nk) = keyset (FI s0' n) ∪ keyset (FI s0' nk)) as ->.
          { rewrite /FI Hs0 /s0'. destruct Hflupd as (_&_&_&_&_&_&_&H1'&_).
            rewrite -H1' -leibniz_equiv_iff. 
            by rewrite (comm _ (keyset (I !!! nk)) _). }
          assert (Content s0 nk ∪ {[k]} = Content s0' n ∪ Content s0' nk) as ->.
          { rewrite /Content Mark_nk Mark_nk' Mark_n'.
            rewrite /Key Hs0 /s0' /Ky0' lookup_insert lookup_insert_ne.
            clear; set_solver. apply Hflupd. }
          assert (prodKS (keyset (FI s0' n) ∪ keyset (FI s0' nk), 
                    Content s0' n ∪ Content s0' nk) = 
                  prodKS (keyset (FI s0' n), Content s0' n) ⋅ 
                    prodKS (keyset (FI s0' nk), Content s0' nk)) as ->.
          { rewrite comm. apply ksRAT_prodKS_op. apply ksRAT_valid_composable. 
            rewrite /ksRAT_composable /valid /ksRATValid /ksRAT_fst. 
            repeat split.
            - rewrite /Content Mark_n'. rewrite /s0' /Key /FI /Ky0' lookup_insert.
              clear -KS_n. set_solver.
            - rewrite /Content Mark_nk'. rewrite /s0' /Key /FI /Ky0'.
              rewrite !lookup_insert_ne. rewrite Hs0 /Key in KS_nk.
              clear -KS_nk; set_solver. apply Hflupd.
            - apply Disj_ks. }
          iDestruct "H'" as "(KS_n & KS_nk)".
          iModIntro. iSplitL "GKS".
          { by rewrite /s0' Hs0; unfold abs. }
          iSplitL "Node_p Node_n Nodes_rest". rewrite FP_s0'.
          rewrite big_sepS_union; try done. iSplitL "Node_p Nodes_rest".
          rewrite (big_opS_delete _ (FP s0) p); try done. iSplitL "Node_p".
          { rewrite Hs0 /s0' /Mark /Next /Key /Mk0' /Nx0' /Ky0'. 
            rewrite lookup_insert_ne. rewrite lookup_insert_ne.
            rewrite lookup_insert. rewrite lookup_insert_ne.
            all : done. }
          iApply (big_sepS_mono with "Nodes_rest"); try done.
          { intros x Hx. rewrite Hs0 /s0' /Mark /Next /Key /Mk0' /Nx0' /Ky0'. 
            rewrite !lookup_insert_ne; try done.
            all : clear -Hx n_notin_s0; set_solver. }
          { rewrite big_opS_singleton. 
            rewrite /s0' /Mark /Next /Key /Mk0' /Nx0' /Ky0'.
            by rewrite !lookup_insert. }
          { clear -n_notin_s0; set_solver. }
          rewrite FP_s0'. rewrite big_opS_union; last first.
          { clear -n_notin_s0; set_solver. }
          iSplitL "Nodes_KS KS_nk".
          rewrite (big_sepS_delete _ (FP s0) nk); last by apply Hflupd. 
          iFrame "KS_nk". 
          iApply (big_sepS_mono with "Nodes_KS"); try done.
          { intros x Hx. iIntros "Hks".
            assert (keyset (FI s0' x) = keyset (FI s0 x)) as ->.
            rewrite /FI /s0' Hs0. apply Hflupd.
            destruct Hflupd as [-> _]. clear -Hx n_notin_s0; set_solver.
            assert (Content s0' x = Content s0 x) as ->.
            rewrite /Content /s0' Hs0 /Marki /Mark /Key /Mk0' /Ky0'.
            rewrite !lookup_insert_ne. done. 
            all : try (clear -Hx n_notin_s0; set_solver); done. }
          by rewrite big_opS_singleton. }
        iAssert (dsRepI γ_r (abs s0'))%I with "[Ds]" as "Ds".
        { admit. }
        iAssert (helping_inv N γ_t γ_r γ_td1 γ_td2 γ_ght (<[(T0+1)%nat:=s0']>M0))%I 
          with "[Help]" as "Help".
        { admit. }
        iAssert (hist γ_t γ_m (<[(T0+1)%nat := s0']> M0) (T0+1)%nat)%I
          with "[Hist]" as "Hist".
        { admit. }
        iModIntro. iSplitR "Hpreds Hsuccs Hpost".
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
        wp_apply (maintenanceOp_insert_spec with "[] [$Hpreds $Hsuccs]"); try done.
        iIntros (ps' ss') "(Hpreds & Hsuccs)".
        wp_pures. admit.
  Admitted.          
      

    

  