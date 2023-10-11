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
Require Export skiplist_v1 skiplist_v1_util.

Module SKIPLIST1_SPEC_TRAVERSE.
  Import SKIPLIST1 SKIPLIST1_UTIL.DEFS.

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

  Parameter findNext_spec : ∀ (n: Node) (i: nat),
    ⊢ <<< ∀∀ h mark next k, node n h mark next k ∗ ⌜i < h⌝ >>>
          findNext #n #i @⊤
      <<< ∃∃ (m: bool) (opt_n': option Node),
              node n h mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !! i = opt_n'⌝,
              RET (match opt_n' with None => (#m, NONEV) 
                                    | Some n' => (#m, SOMEV #n') end) >>>.

  Parameter changeNext_spec : ∀ (n m m': Node) (i: nat),
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

  Parameter compareKey_spec : ∀ (n: Node) (k': nat),
    ⊢ <<< ∀∀ h mark next k, node n h mark next k >>>
           compareKey #n #k' @ ⊤
     <<< ∃∃ (res: nat),
            node n h mark next k 
          ∗ ⌜if decide (res = 0) then k < k'
             else if decide (res = 1) then k = k'
             else k > k'⌝,
         RET #res >>>.

  Definition traversal_inv s i k p c : Prop :=
    p ∈ FP s 
  ∧ c ∈ FP s 
  ∧ Key s p < k 
  ∧ Marki s p i = false 
  ∧ Nexti s p i = Some c
  ∧ i < Height s p
  ∧ i < Height s c.

  Lemma traverse_i_spec N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght
  γ_sy t_id t0 k (i: nat) (p c: Node):
  main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
    thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
    {{{ (∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p c⌝) }}}
      traverse_i #i #p #c #k
    {{{ (ores: option (Node * Node * bool)), 
          RET (match ores with
                None => NONEV
              | Some res =>SOMEV (#res.1.1,#res.1.2,#res.2) end);
          match ores with 
            None => True
          | Some res => 
            let p' := res.1.1 in
            let c' := res.1.2 in
            let b := res.2 in
            (∃ s, past_state γ_m t0 s 
              ∗ ⌜traversal_inv s i k p' c'⌝
              ∗ ⌜i = 0 → if b then k ∈ keyset (FI s c') ∧ k = Key s c'
                          else k ∉ abs s⌝) end }}}.
  Proof.
    iIntros "#HInv #Thd". iLöb as "IH" forall (p c).
    iIntros (Φ) "!# #HtrInv Hpost". wp_lam. wp_pures.
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Nodes" as "(Node_c & Nodes_rest)".
    iAssert ((node c (Height s0 c) (Mark s0 c) (Next s0 c) (Key s0 c)) 
      ∗ ⌜i < Height s0 c⌝)%I with "[Node_c]" as "Hpre".
    { admit. }
    iAaccIntro with "Hpre".
    { iIntros "(Node_c & _)". iModIntro. iFrame "Hpost".
      iNext; iExists M0, T0, s0. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Nodes_rest". iFrame. }
    iIntros (m c') "(Node_c & %Mark_c0 & %Next_c0)".
    iModIntro. iSplitR "Hpost".
    { iNext. iExists M0, T0, s0. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Nodes_rest". iFrame. }
    destruct c' as [cn |]; destruct m; wp_pures. 
    - awp_apply changeNext_spec; try done.
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p1.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Nodes" as "(Node_p & Nodes_rest)".
      iAssert ((node p (Height s1 p) (Mark s1 p) (Next s1 p) (Key s1 p)) 
        ∗ ⌜i < Height s1 p⌝)%I with "[Node_p]" as "Hpre".
      { admit. }
      iAaccIntro with "Hpre".
      { iIntros "(Node_p&_)". iModIntro. iFrame "Hpost".
        iNext; iExists M1, T1, s1. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) p); last by eauto. iFrame. }
      iIntros (success next') "(Node_p & Hsuccess)".
      destruct success.
      + iDestruct "Hsuccess" as %[Next_p1 [Mark_p1 Def_next']].
        destruct (decide (i = 0)) as [-> | Hi0].
        * iDestruct "SShot1" as %[FP1 [C1 [Ht1 [Mk1 [Nx1 [Ky1 [I1 
            [Hs1 [Dom_Ht1 [Dom_Mk1 [Dom_Nx1 [Dom_Ky1 Dom_I1]]]]]]]]]]]].
          set Nx1' := <[p := next']> Nx1.
          set Ip1 := I1 !!! p. set Ic1 := I1 !!! c. set out_pc := out Ip1 c.
          set Ip1' := int {| infR := inf_map Ip1; outR :=  <<[cn := out_pc]>> ∅ |}.
          set Ic1': multiset_flowint_ur nat := 
            int {| infR := {[c := (inf Ic1 c - out_pc)%CCM]}; 
                  outR := <<[cn := (out Ic1 cn - out_pc)%CCM]>> ∅ |}.
          set I1' := <[c := Ic1']> (<[p := Ip1']> I1).
          set s1' := (FP1, C1, Ht1, Mk1, Nx1', Ky1, I1'): snapshot.
          set M1' := <[T1 + 1 := s1']> M1.
          iAssert (⌜per_tick_inv s1⌝)%I as %PT_s1.
          { iDestruct "Hist" as (M')"(_&_&_&%&_)". iPureIntro.
            apply leibniz_equiv in Habs1. rewrite <-Habs1.
            by apply PT1. }
          assert (c ∈ FP s1) as FP_c1.
          { admit. }
          assert (Mark s1 c !!! 0 = true) as Mark_c1.
          { admit. }
          assert (Next s1 c !! 0 = Some cn) as Next_c1.
          { admit. }
          assert (Key s1 p < Key s1 c) as Key_pc.
          { destruct PT_s1 as (_&_&_&PT&_). rewrite /Nexti in PT.
            by pose proof PT p c 0 Next_p1. }
          assert (Key s1 p < W) as Key_p1.
          { destruct PT_s1 as (_&_&PT&_). apply PT in FP_c1.
            destruct FP_c1 as (_&_&_&_&_&H'&_). clear -H' Key_pc. lia. }
          assert (∀ x, x ∈ FP s1 → flow_constraints_I x (FI s1 x) 
                  (Mark s1 x !!! 0) (Next s1 x !! 0) (Key s1 x)) as Hflow.
          { destruct PT_s1 as (_&_&H'&_).
            intros x Hx. apply H' in Hx. by destruct Hx as (_&_&_&_&_&_&?). }
          assert (∀ x, I1 !!! x = FI s1 x) as I1_eq_s1.
          { intros x. rewrite Hs1; unfold FI. try done. }
          assert (flow_constraints_I p Ip1 false (Some c) (Key s1 p)) as Hp.
          { apply Hflow in FP_p1. by rewrite -I1_eq_s1 Next_p1 Mark_p1 in FP_p1. }
          assert (flow_constraints_I c Ic1 true (Some cn) (Key s1 c)) as Hc.
          { apply Hflow in FP_c1. by rewrite -I1_eq_s1 Next_c1 Mark_c1 in FP_c1. }
          assert (insets Ip1 ≠ ∅) as Inset_p1_ne.
          { admit. }
          assert (insets Ic1 ≠ ∅) as Inset_c1_ne.
          { admit. }
          assert (out_pc ≠ 0%CCM) as Out_pc.
          { destruct Hp as (_&H'&_&(_&H'')&_). rewrite /outsets H' in H''. 
            rewrite -leibniz_equiv_iff big_opS_singleton in H''.
            rewrite /out_pc /Ip1 I1_eq_s1. rewrite /ccmunit /lift_unit.
            clear H'; intros H'. rewrite nzmap_eq in H'. pose proof H' W as H'.
            rewrite nzmap_lookup_empty /ccmunit /= /nat_unit in H'.
            rewrite /outset in H''. rewrite -nzmap_elem_of_dom_total2 in H'.
            rewrite -I1_eq_s1 -H'' in H'. apply H'. 
            rewrite elem_of_gset_seq. clear -Key_p1; split; lia. done. }
          assert (out Ic1 cn = inf Ic1 c) as Out_Ic1.
          { admit. }
          assert (p ≠ c) as p_neq_c.
          { admit. }
          assert (p ≠ cn) as p_neq_cn.
          { admit. }
          assert (c ≠ cn) as c_neq_cn.
          { admit. }
          assert (dom Ip1 = {[p]}) as Dom_Ip1 by apply Hp.
          assert (dom Ic1 = {[c]}) as Dom_Ic1 by apply Hc.
          assert (dom Ip1' = {[p]}) as Dom_Ip1'.
          { rewrite /dom /flowint_dom /Ip1' /=. apply Dom_Ip1. }
          assert (dom Ic1' = {[c]}) as Dom_Ic1'.
          { by rewrite /dom /flowint_dom /Ip1' /= dom_singleton_L. }
          assert (dom (out_map Ip1) = {[c]}) as Domout_Ip1.
          { admit. }
          assert (dom (out_map Ic1) = {[cn]}) as Domout_Ic1.
          { admit. }
          assert (dom (out_map Ip1') = {[cn]}) as Domout_Ip1'.
          { admit. }
          assert (✓ (Ip1 ⋅ Ic1)) as Vpc1.
          { admit. }
          assert (✓ (Ip1' ⋅ Ic1')) as Vpc1'.
          { apply intValid_composable. assert (Hcomp := Vpc1). 
            apply intComposable_valid in Hcomp. 
            destruct Hcomp as (H1'&H2'&H3'&H4'&H5'). repeat split; simpl.
            - rewrite /dom /flowint_dom in Dom_Ip1. rewrite Dom_Ip1.
              rewrite nzmap_dom_insert_nonzero. clear -p_neq_cn; set_solver.
              done.
            - intros H'. rewrite /dom /flowint_dom H' in Dom_Ip1.
              clear -Dom_Ip1; set_solver.
            - clear -c_neq_cn. rewrite dom_insert dom_empty.
              destruct (decide ((out Ic1 cn - out_pc)%CCM = 0%CCM)).
              rewrite nzmap_dom_insert_zero; try done. 
              rewrite /dom /nzmap_dom. set_solver.
              rewrite nzmap_dom_insert_nonzero; try done. 
              rewrite /dom /nzmap_dom. set_solver.
            - intros H'. pose proof f_equal dom H' as H''.
              rewrite dom_singleton_L in H''. clear -H''; set_solver.
            - rewrite /flowint_dom /= dom_singleton_L. 
              rewrite /dom /flowint_dom in Dom_Ip1. rewrite Dom_Ip1.
              clear -p_neq_c; set_solver.
            - apply map_Forall_lookup. intros i x Hix. assert (Hix' := Hix).
              apply elem_of_dom_2 in Hix. rewrite /dom /flowint_dom in Dom_Ip1. 
              rewrite Dom_Ip1 elem_of_singleton in Hix. subst i.
              assert (inf Ip1' p = x) as ->. { by rewrite /inf /Ip1' Hix' /=. } 
              assert (out Ic1' p = 0%CCM) as ->. 
              { rewrite /out /Ic1' /out_map /= nzmap_lookup_total_insert_ne.
                rewrite nzmap_lookup_empty. all: done. }
              by rewrite ccm_left_id ccm_pinv_unit.
            - apply map_Forall_lookup. intros i m. 
              destruct (decide (i = c)) as [-> | Hic].
              + rewrite lookup_insert. intros [=<-].
                assert (out Ip1' c = 0%CCM) as ->.
                { rewrite /out /Ip1' /out_map /= nzmap_lookup_total_insert_ne.
                  by rewrite nzmap_lookup_empty. done. }
                assert ((inf Ic1 c - out_pc)%CCM = inf Ic1' c) as ->.
                { by rewrite /Ic1' {2}/inf /inf_map /= lookup_insert /=. }
                rewrite /inf /Ic1' /inf_map /= lookup_insert /=.
                by rewrite ccm_left_id ccm_pinv_unit.
              + rewrite lookup_insert_ne; try done. }
          assert (dom (Ip1 ⋅ Ic1) = {[p;c]}) as Dom_pc.
          { rewrite intComp_dom; try done. rewrite Dom_Ip1 Dom_Ic1; done. } 
          assert (dom (Ip1' ⋅ Ic1') = {[p;c]}) as Dom_pc'.
          { rewrite intComp_dom; try done. rewrite Dom_Ip1' Dom_Ic1'; done. } 
          assert (Ip1' ⋅ Ic1' = Ip1 ⋅ Ic1) as Heq.
          { apply intEq.
            - by rewrite Dom_pc Dom_pc'.
            - rewrite Dom_pc'; clear; set_solver. 
            - intros n. destruct (decide (n = p)) as [-> | Hnp].
              + rewrite !intComp_inf_1; try done.
                assert (inf Ip1' p = inf Ip1 p) as ->. 
                { by rewrite /inf /Ip1' /=. }
                assert (out Ic1' p = 0%CCM) as ->. 
                { rewrite /out /Ic1' /out_map /= nzmap_lookup_total_insert_ne.
                  rewrite nzmap_lookup_empty. all: done. }
                assert (out Ic1 p = 0%CCM) as ->.
                { rewrite /out -nzmap_elem_of_dom_total2.
                  destruct Hc as (_&Hc&_). rewrite Hc; try done.
                  clear -p_neq_cn; set_solver. }
                done. rewrite Dom_Ip1; clear; set_solver.
                rewrite Dom_Ip1'; clear; set_solver.
              + destruct (decide (n = c)) as [-> | Hnc]; last first.
                { assert (n ∉ dom (Ip1' ⋅ Ic1')) as H'.
                  rewrite Dom_pc'. clear -Hnp Hnc; set_solver.
                  rewrite /dom /flowint_dom not_elem_of_dom in H'.
                  assert (n ∉ dom (Ip1 ⋅ Ic1)) as H''.
                  rewrite Dom_pc. clear -Hnp Hnc; set_solver.
                  rewrite /dom /flowint_dom not_elem_of_dom in H''.
                  by rewrite /inf H' H''. }
                rewrite !intComp_inf_2; try done.
                assert (out Ip1' c = 0%CCM) as ->. 
                { rewrite /out /Ip1' /out_map /=.
                  rewrite nzmap_lookup_total_insert_ne; try done. }
                rewrite {1}/inf /Ic1' /inf_map /= lookup_insert /= /out_pc.
                by rewrite ccm_pinv_unit. rewrite Dom_Ic1. clear; set_solver. 
                rewrite Dom_Ic1'. clear; set_solver.
            - intros n. destruct (decide (n ∈ ({[p;c]}: gset Node))) as [Hn | Hn].
              { rewrite !intValid_in_dom_not_out; try done.
                by rewrite Dom_pc. by rewrite Dom_pc'. }
              rewrite !intComp_unfold_out; try done.
              destruct (decide (n = cn)) as [-> | Hncn].
              + assert (out Ip1' cn = out_pc) as ->.
                { by rewrite /out /Ip1' /= nzmap_lookup_total_insert. }
                assert (out Ic1' cn = (out Ic1 cn - out_pc)%CCM) as ->.
                { by rewrite /Ic1' /out /= nzmap_lookup_total_insert. }
                assert (out Ip1 cn = 0%CCM) as ->.
                { rewrite /out -nzmap_elem_of_dom_total2.
                  destruct Hp as (_&Hp&_). rewrite Hp; try done.
                  clear -c_neq_cn; set_solver. }
                rewrite Out_Ic1 /out_pc. rewrite ccm_left_id.
                apply intComposable_valid in Vpc1. destruct Vpc1 as (_&_&_&_&H'). 
                rewrite map_Forall_lookup in H'. pose proof H' c (inf Ic1 c) as H'.
                rewrite {2}H'. done. rewrite /inf. assert (c ∈ dom Ic1) as H''.
                rewrite Dom_Ic1; clear; set_solver. 
                rewrite /dom /flowint_dom elem_of_dom in H''. 
                destruct H'' as [m ->]. by simpl.
              + assert (out Ip1' n = 0%CCM) as ->. 
                { rewrite /out /Ip1' /= nzmap_lookup_total_insert_ne; try done. }
                assert (out Ic1' n = 0%CCM) as ->.
                { rewrite /out /Ic1' /= nzmap_lookup_total_insert_ne; try done. }
                assert (out Ip1 n = 0%CCM) as ->.
                { admit. }
                assert (out Ic1 n = 0%CCM) as ->.
                { admit. }
                done.
              + by rewrite Dom_pc.
              + by rewrite Dom_pc'. }
          assert (insets Ip1' = insets Ip1) as Insets_Ip1'.
          { rewrite /insets Dom_Ip1 Dom_Ip1' /inset /inf /=. done. }
          assert (outsets Ip1' = outsets Ip1) as Outsets_Ip1'.
          { destruct Hp as (_&Hp&_). rewrite /outsets Hp /Ip1 /=; try done.
            assert (dom <<[cn := out_pc]>> ∅ = {[cn]}) as ->.
            apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero; try done.
            rewrite /dom. clear; set_solver. apply leibniz_equiv.
            rewrite !big_opS_singleton. rewrite /outset /Ip1' {1}/out /=.
            rewrite nzmap_lookup_total_insert /out_pc /Ip1. done. }
          assert (flow_constraints_I p Ip1' false (Some cn) (Key s1 p)) as Hp'.
          { destruct Hp as (Hp1&Hp2&Hp3&Hp4&Hp5&Hp6&Hp7). 
            split; last split; last split; last split; last split; 
              last split; try done.
            - rewrite Insets_Ip1' Outsets_Ip1'. done.
            - rewrite Insets_Ip1' Outsets_Ip1'. done.
            - intros n' k'. destruct (decide (n' = cn)) as [-> | Hn'cn].
              + assert (out Ip1' cn = out_pc) as ->.
                { by rewrite /out /Ip1' /= nzmap_lookup_total_insert. }
                pose proof Hp7 c k' as H'. apply H'.
              + assert (out Ip1' n' = 0%CCM) as ->.
                { rewrite /out /Ip1' /= nzmap_lookup_total_insert_ne; try done. }
                rewrite nzmap_lookup_empty. rewrite /ccmunit /= /nat_unit. lia. }
          set S := dom out_pc.
          assert (S ⊆ insets Ic1) as S_sub_c1.
          { admit. }
          assert (∀ k', inf Ic1 c !!! k' ≤ 1) as HInf_Ic1.
          { admit. }
          assert (∀ k', out_pc !!! k' ≤ 1) as Hout_pc.
          { admit. }
          assert (insets Ic1' = insets Ic1 ∖ S) as Insets_Ic1'.
          { rewrite /insets Dom_Ic1' Dom_Ic1. apply leibniz_equiv. 
            rewrite !big_opS_singleton. 
            assert (inset _ Ic1' c = dom (inf Ic1 c - out_pc)%CCM) as ->.
            { rewrite /inset {1}/inf /=  lookup_insert /=. done. }
            rewrite /inset /S. rewrite set_equiv_subseteq.
            split. intros k' Hk'. apply nzmap_elem_of_dom_total in Hk'.
            rewrite lookup_total_lifting_inv in Hk'. rewrite elem_of_difference.
            rewrite /ccmunit /= /nat_unit /ccmop_inv /ccm_opinv /= 
              /nat_opinv in Hk'. 
            assert (inf Ic1 c !!! k' = 1 ∧ out_pc !!! k' = 0) as [H' H''].
            { pose proof HInf_Ic1 k' as H'. pose proof Hout_pc k' as H''.
              set a := inf Ic1 c !!! k'. set b := out_pc !!! k'.
              rewrite -/a in H'. rewrite -/b in H''. rewrite -/a -/b in Hk'.
              clear -H' H'' Hk'; split; try lia. }
            split. rewrite nzmap_elem_of_dom_total H' /ccmunit /= /nat_unit. 
            clear; lia. rewrite nzmap_elem_of_dom_total2 H''. 
            by rewrite /ccmunit /= /nat_unit.
            intros k' Hk'. rewrite elem_of_difference in Hk'.
            destruct Hk' as [Hk1' Hk2']. rewrite nzmap_elem_of_dom_total in Hk1'.
            rewrite /ccmunit /= /nat_unit in Hk1'.
            rewrite nzmap_elem_of_dom_total2 /ccmunit /= /nat_unit in Hk2'.
            rewrite nzmap_elem_of_dom_total /ccmunit /= /nat_unit /ccmop_inv.
            rewrite lookup_total_lifting_inv /ccmop_inv /ccm_opinv /= /nat_opinv.
            rewrite Hk2'. clear -Hk1'; lia. }
          assert (outsets Ic1' = outsets Ic1 ∖ S) as Outsets_Ic1'.
          { admit. }
          assert (flow_constraints_I c Ic1' true (Some cn) (Key s1 c)) as Hc'.
          { destruct Hc as (Hc1&Hc2&Hc3&Hc4&Hc5&Hc6&Hc7). 
            split; last split; last split; last split; last split; 
              last split; try done.
            - intros H'. rewrite /Ic1' /=. apply leibniz_equiv. 
              rewrite nzmap_dom_insert_nonzero; try done.
              rewrite /dom. clear; set_solver. rewrite Out_Ic1.
              rewrite /insets Dom_Ic1' -leibniz_equiv_iff in H'. 
              rewrite big_opS_singleton /inset /Ic1' {1}/inf /= 
                lookup_insert /= in H'.
              intros H''. rewrite H'' in H'. apply H'.
              rewrite /ccmunit /=. clear; set_solver.
            - rewrite Insets_Ic1' Outsets_Ic1'. clear -Hc3 S_sub_c1; set_solver.
            - rewrite /keyset Insets_Ic1' Outsets_Ic1'.
              clear -Hc4 S_sub_c1; set_solver.
            - rewrite Insets_Ic1'. intros k'. rewrite elem_of_difference.
              intros [Hk1' Hk2']. by apply Hc5.
            - admit.
            - admit. }
          iAssert (hist γ_t γ_m M1' (T1+1))%I with "[Hist]" as "Hist".
          { admit. }
          iAssert (▷ helping_inv N γ_t γ_r γ_td1 γ_td2 γ_ght M1')%I with
            "[Help]" as "Help".
          { admit. }
          iAssert (past_state γ_m t0 s1')%I as "Past_s1'".
          { admit. }
          assert (FP s1' = FP s1) as FP_s1'.
          { by rewrite /FP /s1' Hs1. }
          assert (abs s1' = abs s1) as Habs'.
          { by rewrite /abs /s1' Hs1. }
          iAssert (dsRepI γ_r (abs s1'))%I with "[Ds]" as "Ds".
          { by rewrite Habs'. }
          iAssert (own γ_ks (● prodKS (KS, abs s1')))%I with "[GKS]" as "GKS".
          { by rewrite Habs'. }
          assert (∀ n, n ≠ p → Next s1' n = Next s1 n) as HN.
          { intros n Hnc. 
            rewrite /Next /s1' Hs1 /= /Nx1' lookup_insert_ne; try done. }
          assert (Next s1' p = <[0:=cn]> (Next s1 p)) as HNp.
          { by rewrite /s1' Hs1 /Next /Nx1' lookup_insert Def_next' /Next Hs1. }
          assert (∀ n, Key s1' n = Key s1 n) as HK.
          { by rewrite /Key /s1' Hs1 /=. }
          assert (∀ n, n ≠ p → n ≠ c → FI s1' n = FI s1 n) as HI.
          { intros n Hnp Hnc. rewrite /FI /s1' /I1' Hs1 /= !lookup_insert_ne.
            all: done. }
          assert (FI s1' p = Ip1') as HIp.
          { rewrite /FI /s1' /I1' lookup_insert_ne; try done. 
            by rewrite lookup_insert. }
          assert (FI s1' c = Ic1') as HIc.
          { rewrite /FI /s1' /I1' lookup_insert; try done. }
          assert (∀ n, Mark s1' n = Mark s1 n) as HM.
          { by rewrite /FI /s1' Hs1. }
          assert (∀ n, Height s1' n = Height s1 n) as HT.
          { by rewrite /FI /s1' Hs1. }
          iAssert (⌜snapshot_constraints s1'⌝)%I as "SShot1'".
          { iPureIntro. exists FP1, C1, Ht1, Mk1, Nx1', Ky1, I1'.
            repeat split; try done.
            rewrite /Nx1'. rewrite dom_insert_L.
            assert (p ∈ dom Nx1) as H'. 
            { rewrite Hs1 in FP_p1. rewrite Dom_Nx1. by unfold FP in FP_p1. }
            clear -H' Dom_Nx1. set_solver.
            rewrite /I1' !dom_insert_L.
            assert ({[p;c]} ⊆ dom I1) as H'.
            { rewrite Hs1 /FP -Dom_I1 in FP_p1 FP_c1. 
              clear -FP_c1 FP_p1; set_solver. }
            clear -H' Dom_I1; set_solver. }
          assert (p ≠ tl) as p_neq_tl. admit.
          assert (per_tick_inv s1') as PT_s1'.
          { destruct PT_s1 as (PT1'&PT2'&PT3'&PT4'&PT5'&PT6').
            split; last split; last split; last split; last split.
            - destruct PT1' as (PT11'&PT12'&PT13'&PT14'&PT15'). repeat split.
              + intros i'. rewrite /Marki HM. apply PT11'.
              + rewrite HK. apply PT12'.
              + rewrite HK. apply PT13'.
              + by rewrite FP_s1'.
              + by rewrite FP_s1'.
            - rewrite /s1' /GFI /FP /FI. admit.
            - intros n Hn. rewrite FP_s1' in Hn. apply PT3' in Hn.
              destruct (decide (n = p)) as [-> | Hnp].
              + rewrite HNp HK HIp HM HT.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6&Hn7).
                split; last split; last split; last split; last split; 
                  last split; try done.
                * intros i'. destruct (decide (i' = 0)) as [-> | Hi'i].
                  rewrite lookup_insert. split; try done.
                  rewrite lookup_insert_ne; try done.
                * rewrite dom_insert_L Hn3. admit.
                * rewrite lookup_insert Mark_p1. done.
              + destruct (decide (n = c)) as [-> | Hnc]; last first.
                { rewrite HK HM HT. rewrite HN; try done. rewrite HI; try done. }
                rewrite HK HM HT HIc HN; try done.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6&Hn7).
                split; last split; last split; last split; last split; last split;
                  try done. rewrite Mark_c1 Next_c1. done.
            - intros n1 n2 i'. destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp !HK. destruct (decide (i' = 0)) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. admit.
                rewrite lookup_insert_ne; try done. apply PT4'.
              + rewrite !HK /Nexti HN; try done. apply PT4'. 
            - intros n1 n2 i'. rewrite FP_s1'. 
              destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp. destruct (decide (i' = 0)) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. admit.
                rewrite lookup_insert_ne; try done. apply PT5'.
              + rewrite /Nexti HN; try done. apply PT5'.
            - admit. }
          assert (transition_inv s1 s1') as Trans_s1.
          { repeat split; try rewrite FP_s1'; try done; last first.
            - intros n i' Hfp. rewrite /Marki HM. done.
            - intros n. rewrite /Marki HM. intros H' H''. 
              rewrite H' in H''; try done.
            - intros n' i' Hn'. destruct (decide (n' = p)) as [-> | Hnp].
              + rewrite /Marki HM /Nexti HNp. 
                destruct (decide (i' = 0)) as [-> | Hi].
                rewrite Mark_p1. clear; try done.
                rewrite lookup_insert_ne; try done.
              + rewrite /Marki /Nexti HM HN; try done. }
          iAssert (resources γ_ks s1')%I 
            with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
          { iFrame "GKS". rewrite FP_s1'. iSplitR "Nodes_KS".
            rewrite (big_opS_delete _ (FP s1) p); try done.
            iSplitL "Node_p". rewrite Def_next' HNp HM HK HT. done.
            iApply (big_sepS_mono with "Nodes_rest"); try done.
            intros x Hx. iIntros "Hn". rewrite HK HM HT HN. done.
            clear -Hx; set_solver.
            iApply (big_sepS_mono with "Nodes_KS"); try done.
            intros x Hx. iIntros "Hn". admit. 
            (*
            assert (Content s1' x = Content s1 x) as ->.
            rewrite /Content HK /Marki HM. done. done.*) }

          iAssert (∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s 0 k p cn⌝)%I 
            as "#HtrInv'".
          { iExists s1'. iFrame "#". iPureIntro. repeat split.
            rewrite FP_s1'; try done. admit. rewrite HK.
            admit. rewrite /Marki HM Mark_p1. done. rewrite /Nexti HNp.
            by rewrite lookup_insert. admit. admit. }  
          iModIntro. iSplitR "Hpost".
          { iNext. iExists M1', (T1+1), s1'. iFrame "∗#%".
            iPureIntro; rewrite /M1'; split; last split.
            - by rewrite lookup_total_insert.
            - intros t Ht. destruct (decide (t = T1+1)) as [-> | Ht'].
              + by rewrite lookup_total_insert.
              + rewrite lookup_total_insert_ne; try done. apply PT1.
                rewrite dom_insert in Ht. clear -Ht' Ht; set_solver.
            - intros t Ht. destruct (decide (t = T1)) as [-> | Ht'].
              + rewrite lookup_total_insert. rewrite lookup_total_insert_ne.
                apply leibniz_equiv in Habs1. by rewrite Habs1. clear; lia.
              + rewrite !lookup_total_insert_ne. apply Trans_M1.
                all: clear -Ht Ht'; lia. }
          wp_pures.
          iApply "IH"; try done.
        * iDestruct "SShot1" as %[FP1 [C1 [Ht1 [Mk1 [Nx1 [Ky1 [I1 
            [Hs1 [Dom_Ht1 [Dom_Mk1 [Dom_Nx1 [Dom_Ky1 Dom_I1]]]]]]]]]]]].
          set Nx1' := <[p := next']> Nx1.
          set s1' := (FP1, C1, Ht1, Mk1, Nx1', Ky1, I1): snapshot.
          set M1' := <[T1 + 1 := s1']> M1.
          iAssert (⌜per_tick_inv s1⌝)%I as %PT_s1.
          { iDestruct "Hist" as (M')"(_&_&_&%&_)". iPureIntro.
            apply leibniz_equiv in Habs1. rewrite <-Habs1.
            by apply PT1. }
          iAssert (hist γ_t γ_m M1' (T1+1))%I with "[Hist]" as "Hist".
          { admit. }
          iAssert (▷ helping_inv N γ_t γ_r γ_td1 γ_td2 γ_ght M1')%I with
            "[Help]" as "Help".
          { admit. }
          iAssert (past_state γ_m t0 s1')%I as "Past_s1'".
          { admit. }
          assert (FP s1' = FP s1) as FP_s1'.
          { by rewrite /FP /s1' Hs1. }
          assert (abs s1' = abs s1) as Habs'.
          { by rewrite /abs /s1' Hs1. }
          iAssert (dsRepI γ_r (abs s1'))%I with "[Ds]" as "Ds".
          { by rewrite Habs'. }
          iAssert (own γ_ks (● prodKS (KS, abs s1')))%I with "[GKS]" as "GKS".
          { by rewrite Habs'. }
          assert (∀ n, n ≠ p → Next s1' n = Next s1 n) as HN.
          { intros n Hnc. 
            rewrite /Next /s1' Hs1 /= /Nx1' lookup_insert_ne; try done. }
          assert (Next s1' p = <[i:=cn]> (Next s1 p)) as HNp.
          { by rewrite /s1' Hs1 /Next /Nx1' lookup_insert Def_next' /Next Hs1. }
          assert (∀ n, Key s1' n = Key s1 n) as HK.
          { by rewrite /Key /s1' Hs1 /=. }
          assert (∀ n, FI s1' n = FI s1 n) as HI.
          { by rewrite /FI /s1' Hs1 /=. }
          assert (∀ n, Mark s1' n = Mark s1 n) as HM.
          { by rewrite /FI /s1' Hs1. }
          assert (∀ n, Height s1' n = Height s1 n) as HT.
          { by rewrite /FI /s1' Hs1. }
          assert (p ≠ tl) as p_neq_tl. admit.
          assert (Key s1 p < Key s1 cn) as Key_pcn. admit.
          assert (cn ∈ FP s1) as FP_cn1. admit.
          iAssert (⌜snapshot_constraints s1'⌝)%I as "SShot1'".
          { iPureIntro. exists FP1, C1, Ht1, Mk1, Nx1', Ky1, I1.
            repeat split; try done.
            rewrite /Nx1'. rewrite dom_insert_L.
            assert (p ∈ dom Nx1). 
            { rewrite Hs1 in FP_p1. rewrite Dom_Nx1. by unfold FP in FP_p1. }
            clear -H Dom_Nx1. set_solver. }
          assert (per_tick_inv s1') as PT_s1'.
          { destruct PT_s1 as (PT1'&PT2'&PT3'&PT4'&PT5'&PT6').
            split; last split; last split; last split; last split.
            - destruct PT1' as (PT11'&PT12'&PT13'&PT14'&PT15'). repeat split.
              + intros i'. rewrite /Marki HM. apply PT11'.
              + rewrite HK. apply PT12'.
              + rewrite HK. apply PT13'.
              + by rewrite FP_s1'.
              + by rewrite FP_s1'.
            - rewrite /s1' /GFI /FP /FI. by rewrite Hs1 /GFI /FP /FI in PT2'.
            - intros n Hn. rewrite FP_s1' in Hn. apply PT3' in Hn.
              destruct (decide (n = p)) as [-> | Hnp].
              + rewrite HNp HK HI HT HM.
                destruct Hn as (Hn1&Hn2&Hn3&Hn4&Hn5&Hn6&Hn7).
                split; last split; last split; last split; last split; 
                  last split; try done.
                * intros i'. destruct (decide (i' = i)) as [-> | Hi'i].
                  rewrite lookup_insert. split; try done.
                  rewrite lookup_insert_ne; try done.
                * rewrite dom_insert_L Hn3. admit.
                * rewrite lookup_insert_ne; try done.
              + rewrite HK HT HI HM. rewrite HN; try done.
            - intros n1 n2 i'. destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp !HK. destruct (decide (i = i')) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. done. 
                rewrite lookup_insert_ne; try done. apply PT4'.
              + rewrite !HK /Nexti HN; try done. apply PT4'. 
            - intros n1 n2 i'. rewrite FP_s1'. 
              destruct (decide (n1 = p)) as [-> | Hn1p].
              + rewrite /Nexti HNp. destruct (decide (i = i')) as [-> | Hi'i].
                rewrite lookup_insert. intros [=<-]. done. 
                rewrite lookup_insert_ne; try done. apply PT5'.
              + rewrite /Nexti HN; try done. apply PT5'.
            - admit. }
          assert (transition_inv s1 s1') as Trans_s1.
          { repeat split; try rewrite FP_s1'; try done; last first.
            - intros n i' Hfp. rewrite /Marki HM. done.
            - intros n. rewrite /Marki HM. intros H' H''. 
              rewrite H' in H''; try done.
            - intros n' i' Hn'. destruct (decide (n' = p)) as [-> | Hnp].
              + rewrite /Marki HM /Nexti HNp. 
                destruct (decide (i' = i)) as [-> | Hi].
                rewrite Mark_p1. clear; try done.
                rewrite lookup_insert_ne; try done.
              + rewrite /Marki /Nexti HM HN; try done. }
          iAssert (resources γ_ks s1')%I 
            with "[GKS Nodes_KS Node_p Nodes_rest]" as "Res".
          { iFrame "GKS". rewrite FP_s1'. iSplitR "Nodes_KS".
            rewrite (big_opS_delete _ (FP s1) p); try done.
            iSplitL "Node_p". rewrite Def_next' HNp HT HM HK. done.
            iApply (big_sepS_mono with "Nodes_rest"); try done.
            intros x Hx. iIntros "Hn". rewrite HK HT HM HN. done.
            clear -Hx; set_solver.
            iApply (big_sepS_mono with "Nodes_KS"); try done.
            intros x Hx. iIntros "Hn". rewrite HI.
            assert (Content s1' x = Content s1 x) as ->.
            rewrite /Content HK /Marki HM. done. done. }

          iAssert (∃ s, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p cn⌝)%I 
            as "#HtrInv'".
          { iExists s1'. iFrame "#". iPureIntro. repeat split.
            rewrite FP_s1'; try done. rewrite FP_s1'; try done.
            admit. rewrite /Marki HM Mark_p1. done. rewrite /Nexti HNp.
            by rewrite lookup_insert. admit. admit. }  
          iModIntro. iSplitR "Hpost".
          { iNext. iExists M1', (T1+1), s1'. iFrame "∗#%".
            iPureIntro; rewrite /M1'; split; last split.
            - by rewrite lookup_total_insert.
            - intros t Ht. destruct (decide (t = T1+1)) as [-> | Ht'].
              + by rewrite lookup_total_insert.
              + rewrite lookup_total_insert_ne; try done. apply PT1.
                rewrite dom_insert in Ht. clear -Ht' Ht; set_solver.
            - intros t Ht. destruct (decide (t = T1)) as [-> | Ht'].
              + rewrite lookup_total_insert. rewrite lookup_total_insert_ne.
                apply leibniz_equiv in Habs1. by rewrite Habs1. clear; lia.
              + rewrite !lookup_total_insert_ne. apply Trans_M1.
                all: clear -Ht Ht'; lia. }
          wp_pures.
          iApply "IH"; try done.
      + iDestruct "Hsuccess" as %[Hcond ->].
        iModIntro. iSplitR "Hpost".
        { iNext. iExists M1, T1, s1. iFrame "∗%".
          rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
          iFrame "Nodes_rest". iFrame. }
        wp_pures. iSpecialize ("Hpost" $! None). by iApply "Hpost".
    - awp_apply compareKey_spec. 
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iDestruct "Templ" as "(SShot1 & Res & %PT1 & %Trans_M1)".
      iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
      iAssert (⌜c ∈ FP s1⌝)%I as %FP_c1.
      { (* interpolation *) admit. }
      rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
      iDestruct "Nodes" as "(Node_c & Nodes_rest)".
      iAaccIntro with "Node_c".
      { iIntros "Node_c". iModIntro. iFrame "Hpost".
        iNext; iExists M1, T1, s1. iFrame "∗%#". 
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto. iFrame. }
      iIntros (res)"(Node_c & %Hif)".
      iAssert (past_state γ_m t0 s1) as "#Hs1".
      { admit. }
      iModIntro. iSplitR "Hpost".
      { iNext. iExists M1, T1, s1. iFrame "∗%".
        rewrite (big_sepS_delete _ (FP s1) c); last by eauto.
        iFrame "Nodes_rest". iFrame. }
      wp_pures.
      destruct (bool_decide (#res = #0)) eqn: Hbool; first last.
      + rewrite bool_decide_eq_false in Hbool.
        assert (res ≠ 0) as Hres0. { intros ->. by apply Hbool. } 
        wp_pures. destruct (bool_decide (#res = #1)) eqn:Hbool1; first last.
        * wp_pures. iModIntro. iSpecialize ("Hpost" $! (Some (p,c,false))).
          iEval (rewrite /=) in "Hpost". iApply "Hpost".
          iDestruct "HtrInv" as (s)"(Past_s & Hpc)".
          iExists s. iFrame "#". admit.  
        * rewrite bool_decide_eq_true in Hbool1. inversion Hbool1.
          assert (res = 1) as -> by lia.
          wp_pures. iModIntro. iSpecialize ("Hpost" $! (Some (p,c,true))).
          iEval (rewrite /=) in "Hpost". iApply "Hpost".
          iDestruct "HtrInv" as (s)"(Past_s & Hpc)".
          iExists s. iFrame "#". admit.  
      + wp_pures. iApply "IH". { iExists s0. admit. }
        iFrame.
    - (* Contradiction case *) admit.
    - iModIntro. iSpecialize ("Hpost" $! (Some (p,c,false))). 
      iEval (rewrite /=) in "Hpost". iApply "Hpost".
      iDestruct "HtrInv" as (s)"(Past_s & Hpc)".
      iExists s. iFrame "#". admit.  
  Admitted.

  Lemma traverse_pop_spec N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght
    γ_sy t_id t0 k preds succs ps0 ss0 (i: nat):
    main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
      thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ is_array preds ps0 ∗ is_array succs ss0
            ∗ (∀ j, ⌜i < j < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s j k (ps0 !!! j) (ss0 !!! j)⌝) }}}
          traverse_pop traverse_rec #k #preds #succs #i
        {{{ (ores: option (loc * loc * bool)) (ps ss: list Node) (b: bool), 
              RET (match ores with 
                    None => NONEV 
                  | Some res => SOMEV (#res.1.1,#res.1.2,#res.2) end);
              match ores with 
                None => is_array preds ps0 ∗ is_array succs ss0
              | Some res =>
                ⌜res.1.1 = preds⌝ ∗ ⌜res.1.2 = succs⌝ ∗ ⌜res.2 = b⌝
              ∗ is_array preds ps ∗ is_array succs ss
              ∗ (∀ j, ⌜i-1 < j < L⌝ → 
                      ∃ s, past_state γ_m t0 s 
                          ∗ ⌜traversal_inv s j k (ps !!! j) (ss !!! j)⌝)
              ∗ (⌜i = 0⌝ →  let p := ps !!! 0 in
                            let c := ss !!! 0 in
                            (∃ s, past_state γ_m t0 s 
                            ∗ ⌜traversal_inv s 0 k p c⌝
                            ∗ ⌜if b then k ∈ keyset (FI s c) ∧ k = Key s c
                                else k ∉ abs s⌝)) end }}}.
  Proof.
    iIntros "#HInv #Thd". iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & Hj)". wp_lam. wp_pures.
    iEval (rewrite /is_array) in "Hpreds".
    assert (is_Some (ps0 !! (i+1))) as [p Hp].
    { admit. } 
    assert (Z.of_nat (i+1) = (Z.of_nat i + 1)%Z) as H' by lia.
    iEval (rewrite <-H').
    wp_apply (wp_load_offset _ _ _ (DfracOwn 1) (i+1) ((λ n : loc, #n) <$> ps0) #p
      with "[Hpreds]"); try done.
    { admit. }
    { iNext. admit. }
    iIntros "Hpreds".
    iAssert (is_array preds ps0) with "[Hpreds]" as "Hpreds".
    { unfold is_array. admit. }
    wp_pures. wp_bind (findNext _ _)%E. 
    awp_apply findNext_spec.
    iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(SShot0 & Res & %PT0 & %Trans_M0)".
    iDestruct "Res" as "(GKS & Nodes & Nodes_KS)".
    iAssert (⌜p ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) p); last by eauto.
    iDestruct "Nodes" as "(Node_p & Nodes_rest)".
    iAssert ((node p (Height s0 p) (Mark s0 p) (Next s0 p) (Key s0 p)) 
      ∗ ⌜i < Height s0 p⌝)%I with "[Node_p]" as "Hpre".
    { admit. }
    iAaccIntro with "Hpre".    
    { iIntros "(Node_p&_)". iModIntro. iFrame "Hpost Hpreds Hsuccs Hj".
      iNext; iExists M0, T0, s0. iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    iIntros (m c) "(Node_p & %Mark_p0 & %Next_p0)".
    iModIntro. iSplitR "Hpreds Hsuccs Hpost Hj".
    { iNext. iExists M0, T0, s0. iFrame "∗%".
      rewrite (big_sepS_delete _ (FP s0) p); last by eauto. iFrame. }
    destruct c as [c |]; last first; wp_pures.
    { (* Contradiction case *) admit. }
    iAssert (∃ s : snapshot, past_state γ_m t0 s ∗ ⌜traversal_inv s i k p c⌝)%I
      as "Hpc". { admit. }
    wp_apply traverse_i_spec; try done.
    iIntros (ores) "Hores".
    destruct ores as [[[p' c'] b]|]; last first.
    { wp_pures. iSpecialize ("Hpost" $! None ps0 ss0 true). iApply "Hpost".
      iFrame. done. }
    wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hpreds]").
    { iFrame "Hpreds". admit. }
    iIntros "!> Hpreds". wp_pures. wp_bind (_ <- _)%E. 
    iApply (array_store with "[Hsuccs]").
    { iFrame "Hsuccs". admit. }
    iIntros "!> Hsuccs". wp_pures.
    iSpecialize ("Hpost" $! (Some (preds,succs,b)) _ _ b).
    iEval (rewrite /=) in "Hpost Hores". iApply "Hpost".
    iModIntro. iFrame "∗%". repeat (iSplitR; first by iPureIntro).
    iDestruct "Hores" as (s)"(Past_s & Hpc' & %Hi0)".
    iSplit. iIntros (j)"%Hj". destruct (decide (j = i)) as [-> | Hij].
    { iExists s. rewrite !list_lookup_total_insert. iFrame. all: admit. }
    iAssert (⌜i < j < L⌝)%I as "Hj'". { iPureIntro. lia. }
    iPoseProof ("Hj" with "Hj'") as (s')"(Past_s' & Htr)".
    iExists s'. rewrite !list_lookup_total_insert_ne; try done. iFrame.
    iIntros "%". subst i. rewrite !list_lookup_total_insert.
    iExists s. iFrame. iPureIntro. by apply Hi0. all: admit.
  Admitted.


  Lemma traverse_rec_spec N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght γ_sy t_id 
    t0 k preds succs ps0 ss0 (i: nat):
    main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
      thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
      {{{ is_array preds ps0 ∗ is_array succs ss0
          ∗ (∀ j, ⌜i < j < L⌝ → 
                  ∃ s, past_state γ_m t0 s 
                  ∗ ⌜traversal_inv s j k (ps0 !!! j) (ss0 !!! j)⌝) }}}
        traverse_rec #k #preds #succs #i
      {{{ (ps ss: list Node) (res: bool), 
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
    iIntros "#HInv #Thd". iLöb as "IH" forall (i ps0 ss0). 
    iIntros (Φ) "!# Hpre Hpost".
    iDestruct "Hpre" as "(Hpreds & Hsuccs & #HtrInv)".
    wp_lam. wp_pures. 
    wp_apply (traverse_pop_spec with "[] [] [Hpreds Hsuccs]"); try done.
    iFrame "∗#". iIntros (ores ps ss b)"Hores".
    destruct ores as [[[preds' succs'] res] |]; last first.
    { wp_pures. iDestruct "Hores" as "(Hpreds & Hsuccs)".
      iApply ("IH" with "[Hpreds Hsuccs]"); try iFrame. iIntros (j)"%Hj".
      assert (j = L-1) as -> by lia. admit. }
    wp_pures. iDestruct "Hores" as "(%H' & %H'' & %H1' & H1'')". 
    rewrite /= in H' H'' H1'. subst preds' succs' b.  
    iDestruct "H1''" as "(Hpreds & Hsuccs & #Hj & Hi0)".
    destruct (bool_decide (#i = #0)) eqn: Hbool; wp_pures.
    - rewrite bool_decide_eq_true in Hbool. inversion Hbool. iModIntro.
      iApply "Hpost". iFrame "Hpreds Hsuccs". 
      iAssert (⌜i = 0⌝)%I as "Htr0". { iPureIntro; lia. }
      iDestruct ("Hi0" with "Htr0") as "H'".
      iIntros (j) "%Hj". destruct (decide (j = 0)) as [-> | Hj0].
      + iDestruct "H'" as (s)"(Hpast_s & #Htr & Hres)".
        iExists s; try iFrame "∗#". iIntros "_". iFrame.
      + iAssert (⌜i - 1 < j < L⌝)%I as "Hj'". { iPureIntro; lia. }
        iPoseProof ("Hj" with "Hj'") as (s)"(Past_s & Htr)".
        iExists s. iFrame "#". iIntros "%"; exfalso; lia.
    - iSpecialize ("IH" $! (i-1) ps ss).
      rewrite bool_decide_eq_false in Hbool.
      assert (i ≠ 0). { intros ->. apply Hbool. try done. }
      assert (Z.sub i 1 = (i-1)%nat) as -> by lia.
      iApply ("IH" with "[$Hpreds $Hsuccs $Hj]"). done.
  Admitted.


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
    iIntros "#HInv #Thd". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures. wp_bind (AllocN _ _)%E. 
    iApply array_repeat. admit.
    iNext. iIntros (preds) "Hpreds".
    wp_pures. wp_bind (AllocN _ _)%E.
    iApply array_repeat. admit.
    iNext. iIntros (succs) "Hsuccs". wp_pures. 
    wp_apply (traverse_rec_spec with "[] [] [Hpreds Hsuccs]"); try done.
    iFrame "Hpreds Hsuccs". iIntros (j) "%Hj". 
    assert (j = L-1) as -> by lia. rewrite !lookup_total_replicate_2.
    all : try lia. admit.  
  Admitted.

End SKIPLIST1_SPEC_TRAVERSE.
  
  
