Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
(* From Coq Require Import QArith Qcanon. *)
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export list_flow_upd.
Require Import Coq.Setoids.Setoid.

Section list_flow_upd_marking.
  Open Scope ccm_scope.
  
  Definition f_incr := λ (k x: nat), x+1.
  
  Definition list_flow_upd_marking n0 Nx Mk S I :=
    list_flow_upd f_incr n0 Nx Mk S I.

  Lemma list_flow_upd_marking_intfEq Key n R Nx Mk S I I' II' nk n0:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n0 ∈ dom I') → (n ∈ dom I') →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (FI I' n = inflow_map_set f_incr (FI I n) n S) →
    (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) →
    ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
    list_flow_upd_rec f_incr n R Nx Mk S I I' = Some (II', nk) →
        (([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x)).
  Proof.
    intros FI. apply list_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key Hcl VI Domm_I n0_in_I0 n_in_I0 Key_I0 Def_I0_n 
        Dom_I0_in_I Domm_I0 Heq [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key Hcl VI Domm_I n0_in_I0 n_in_I0 Key_I0 Def_I0_n 
        Dom_I0_in_I Domm_I0 Heq Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 Hnx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct Hcl as [_ [_ Hcl]].
        by pose proof Hcl n n1 Hnx_n as H'. }  
      assert (∀ x, x ∈ dom I0 → dom (FI (<[n:=In']> I0) x) = {[x]}) 
        as Domm_II.
      { intros x Hx. destruct (decide (n = x)) as [-> | Hxn].
        - unfold FI. rewrite lookup_total_insert.
          subst In'. rewrite flowint_outflow_map_set_domm.
          subst In. rewrite Domm_I0; try done.
        - unfold FI. rewrite lookup_total_insert_ne; try done.
          rewrite Domm_I0; try done. }
      apply HInd; try done; clear HInd.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
      + rewrite /I0' /FI. rewrite lookup_total_insert. 
        rewrite /In1'. by rewrite /In1.
      + rewrite Dom_I0'. set_solver.
      + rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * subst I0'. 
          assert (x ≠ n1) as H'.
          { clear -Hx n1_notin_I0. set_solver. }
          unfold FI.
          rewrite lookup_total_insert_ne; try done.
          subst II.
          apply Domm_II; try done.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          unfold FI. subst I0'.
          rewrite lookup_total_insert.
          subst In1'.
          rewrite flowint_inflow_map_set_dom.
          subst In1. rewrite Domm_I; try done.
          clear; set_solver.
      + rewrite Dom_I0'.
        rewrite !big_opS_union; [try done | set_solver | set_solver].
        rewrite !big_opS_singleton. 
        all: try (clear -n_notin_I0; set_solver).
        rewrite /I0'; rewrite /FI. rewrite lookup_total_insert.
        rewrite /II.
        assert (([^op set] y ∈ dom I0, FI (<[n1:=In1']> (<[n:=In']> I0)) y) = 
                  ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Def_II.
        { apply big_opS_ext. intros x Hx. unfold FI.
          rewrite lookup_total_insert_ne. done.
          clear -Hx n1_notin_I0. set_solver. }
        rewrite Def_II.
        assert (✓ ([^op set] y ∈ dom I0, FI I y)) as Valid_I.
        { apply (flow_big_op_valid _ (dom I)); try done. }
        assert (✓ ([^op set] y ∈ dom I0, FI I0 y)) as Valid_I0.
        { apply leibniz_equiv_iff in Heq. rewrite <-Heq. try done. }
        assert (✓ ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Valid_II.
        { assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) = 
                    ([^op set] y ∈ dom I0 ∖ {[n]}, FI I0 y) ⋅ In') as ->.
        { rewrite (big_opS_delete _ _ n); last done.
          unfold FI at 1. rewrite lookup_total_insert.
          rewrite intComp_comm.
          assert (([^op set] y ∈ (dom I0 ∖ {[n]}), FI (<[n:=In']> I0) y) = 
              ([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y)) as ->.
          { apply big_opS_ext. intros x Hx. unfold FI.
            rewrite lookup_total_insert_ne. done.
            clear -Hx; set_solver. }
          done. }

          apply (outflow_map_set_valid2
                        (([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y)) 
                        (I0 !!! n) (In') f_incr n1 S).
          - subst In'; try done.
          - intros Hn1. rewrite flow_big_op_dom in Hn1.
            destruct Hn1 as [x [Hx1 Hx2]].
            rewrite Domm_I0 in Hx2; last first.
            { clear -Hx1; set_solver. }
            assert (n1 = x) as <- by (clear -Hx2; set_solver).
            clear -n1_notin_I0 Hx1. set_solver.
            apply (flow_big_op_valid _ (dom I0)); try done.
            clear; set_solver.
          - rewrite Domm_I0; try done.
            assert (n1 ≠ n) as H'.
            { clear -n1_notin_I0 n_in_I0.
              set_solver. }
            clear -H'; set_solver.
          - intros H'. rewrite Domm_I0 in H'; try done.
            clear -H'; set_solver.
          - assert (([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y) ⋅ I0 !!! n =
                      ([^op set] y ∈ dom I0, FI I0 y)) as H'.
            { rewrite (big_opS_delete _ (dom I0) n); try done.
              unfold FI at 2. by rewrite intComp_comm. }
            by rewrite H'. }
        pose proof (flowint_insert_eq
                      ([^op set] y ∈ dom I0, I !!! y)
                      ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                      (I !!! n1) In1' n1 S) as Hpose.
        assert (n1 ∈ dom (FI I n1)) as n1_in_In1.
        { rewrite Domm_I; try done. clear; set_solver. }
        assert (flowint_dom ([^op set] y ∈ dom I0, I !!! y) ≠ ∅) 
          as Domm_I0_notEmpty.
        { assert (n ∈ (flowint_dom ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
          { rewrite flow_big_op_dom; try done. exists n; split; try done.
            rewrite Domm_I; last first.
            { clear -n_in_I0 Dom_I0_in_I. set_solver. } 
            clear; set_solver. }
          clear -H'; set_solver. }
        assert (flowint_dom ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)) = 
                  flowint_dom ([^op set] y ∈ dom I0, (I !!! y))) as Domm_II_eq_I.
        { assert ((flowint_dom ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y))) ⊆ 
                      (flowint_dom ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
          { intros n'. rewrite !flow_big_op_dom; try done.
            intros [x [Hx1 Hx2]]. exists x. split; try done.
            rewrite Domm_II in Hx2; try done. rewrite Domm_I; try done.
            clear -Hx1 Dom_I0_in_I. set_solver. }
          assert ((flowint_dom ([^op set] y ∈ dom I0, (I !!! y))) ⊆ 
                    (flowint_dom ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)))) 
                    as H''.
          { intros n'. rewrite !flow_big_op_dom; try done.
            intros [x [Hx1 Hx2]]. exists x. split; try done.
            rewrite Domm_II. rewrite Domm_I in Hx2; try done.
            clear -Hx1 Dom_I0_in_I. set_solver. done. }
          clear -H' H''; set_solver. }
        assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) =
          outflow_map_set f_incr ([^op set] y ∈ dom I0, I !!! y) n1 S) 
          as H0'.
        { apply intEq; try done. 
          - unfold dom. rewrite Domm_II_eq_I. try done. 
          - intros n'. unfold inf. rewrite outflow_map_set_inf.
            assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n'
              ≡ default 0 
                (inf_map ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) !! n'))
              as HL by try done.
            assert (inf ([^op set] y ∈ dom I0, FI I y) n'
              ≡ default 0 
                (inf_map ([^op set] y ∈ dom I0, I !!! y) !! n')) 
              as HR by try done.
            rewrite <-HL. rewrite <-HR.
            rewrite Heq.
            assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n' = 
                      inf ([^op set] y ∈ dom I0, FI I0 y) n') as HI0.
            { destruct (decide (n' ∈ 
                          dom ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
                as [Hn' | Hn'].
              - rewrite flow_big_op_dom in Hn'; try done.
                destruct Hn' as [n'' [n''_in_I0 n'_in_n'']].
                rewrite Domm_II in n'_in_n''; try done.
                assert (n' = n'') as <- by (clear -n'_in_n''; set_solver).
                rewrite (flow_big_op_inf _ _ n'); try done.
                + rewrite (flow_big_op_inf _ _ n'); try done.
                  * clear HL HR. 
                    assert (([^+ set] x ∈ (dom I0 ∖ {[n']}), 
                              out (FI (<[n:=In']> I0) x) n')
                            = ([^+ set] x ∈ (dom I0 ∖ {[n']}), 
                              out (FI I0 x) n')) as Hout.
                    { destruct (decide (n' = n)) as [-> | Hn'].
                      - apply ccm_big_opS_ext. intros x Hx.
                        unfold FI. rewrite lookup_total_insert_ne. done.
                        clear -Hx; set_solver.  
                      - assert (out (FI (<[n := In']> I0) n) n' 
                                  = out (FI I0 n) n') as H'.
                        { rewrite /FI. rewrite lookup_total_insert.
                          rewrite /In' /In.
                          assert (n' ≠ n1). 
                          { clear -n''_in_I0 n1_notin_I0. set_solver. }
                          unfold out. 
                          rewrite outflow_map_set_out_map_ne; try done. }
                        apply ccm_big_opS_ext. intros x Hx. unfold FI. 
                        destruct (decide (x = n)) as [-> | Hxn]; try done.
                        rewrite lookup_total_insert_ne; try done. }
                    assert (inf (FI (<[n:=In']> I0) n') n' 
                              = inf (FI I0 n') n') as Hin.
                    { destruct (decide (n' = n)) as [-> | Hn'].
                      - rewrite /FI. rewrite lookup_total_insert. 
                        subst In'. unfold inf. 
                        rewrite outflow_map_set_inf. by subst In.
                      - rewrite /FI. 
                        rewrite lookup_total_insert_ne; try done. }
                    by rewrite Hin Hout.
                  * rewrite Domm_I0; try done.
                + rewrite Domm_II; try done.
              - assert (n' ∉ dom ([^op set] y ∈ dom I0, FI I0 y)) as Hn''.
                { unfold dom in Hn'. rewrite Domm_II_eq_I in Hn'.
                  intros Hn''. rewrite flow_big_op_dom in Hn''; try done.
                  destruct Hn'' as [x0 [Hx0 Hx00]].
                  apply Hn'. rewrite flow_big_op_dom; try done.
                  exists x0. split; try done.
                  rewrite (Domm_I0 x0 Hx0) in Hx00.
                  apply Dom_I0_in_I in Hx0.
                  unfold FI in Domm_I.
                  by rewrite (Domm_I x0 Hx0). }
                unfold dom, flowint_dom in Hn''. 
                unfold dom, flowint_dom in Hn'.
                rewrite not_elem_of_dom in Hn'.
                rewrite not_elem_of_dom in Hn''.
                unfold inf. rewrite Hn' Hn''. by simpl. }
            by rewrite HI0.
          - rewrite Heq. intros n'.
            destruct (decide (n' ∈ 
                dom ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
                as [Hn' | Hn'].
            + rewrite intValid_in_dom_not_out; try done.
              rewrite intValid_in_dom_not_out; try done.
              apply outflow_map_set_valid; try done.
              intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
              destruct Hn1 as [x0 [Hx0 Hx00]].
              rewrite (Domm_I0 x0 Hx0) in Hx00.
              clear -Hx0 Hx00 n1_notin_I0. set_solver.
              assert (n ∈ dom ([^op set] x ∈ dom I0, FI I0 x)) as H'.
              { rewrite flow_big_op_dom; try done. exists n.
                rewrite (Domm_I0 n n_in_I0). split; try done.
                clear; set_solver. } clear -H'; set_solver.
              rewrite flowint_outflow_map_set_domm. 
              rewrite flow_big_op_dom; try done.
              rewrite flow_big_op_dom in Hn'; try done.
              destruct Hn' as [x0 [Hx0 Hx00]].
              destruct (decide (x0 = n)) as [-> | Hxn].
              * unfold FI in Hx00. rewrite lookup_total_insert in Hx00.
                rewrite /In' in Hx00.
                rewrite flowint_outflow_map_set_domm in Hx00.
                rewrite /In in Hx00.
                exists n; split; try done.
              * unfold FI in Hx00. 
                rewrite lookup_total_insert_ne in Hx00; try done.
                exists x0; split; try done.
            + destruct (decide (n' = n1)) as [-> | Hn1'].
              * apply nzmap_eq. intros k'. 
                destruct (decide (k' ∈ S)) as [Hk' | Hk'].
                ** rewrite outflow_lookup_total_map_set; try done.
                   rewrite !flow_big_op_out; try done.
                   { rewrite (ccm_big_opS_delete _ _ n); try done.
                     rewrite (ccm_big_opS_delete _ (dom I0) n); try done.
                     unfold ccmop, ccm_op. simpl.
                     rewrite !lookup_total_lifting.
                     unfold ccmop, ccm_op. simpl. unfold nat_op.
                     unfold FI at 1. rewrite lookup_total_insert.
                     rewrite {1}/In'. rewrite outflow_lookup_total_map_set.
                     assert (([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI (<[n:=In']> I0) y) n1) =
                             ([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI I0 y) n1)) as ->.
                     { apply ccm_big_opS_ext. intros x Hx. unfold FI. 
                       rewrite lookup_total_insert_ne; try done.
                       clear -Hx; set_solver. }
                     rewrite /In. rewrite -/(FI I0 n).
                     rewrite /f_incr /ccmop /nat_op. 
                     set a := out (FI I0 n) n1 !!! k'.
                     set b := ([^+ set] y ∈ (dom I0 ∖ {[n]}), out (FI I0 y) n1) 
                                                                         !!! k'.
                     clear; lia. done. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_I0 in Hx2; try done.
                     assert (n1 = x) as -> by (clear -Hx2; set_solver).
                     clear -Hx1 n1_notin_I0. try done. }
                ** rewrite outflow_lookup_total_map_set_ne; try done.
                   rewrite !flow_big_op_out; try done.
                   { rewrite (ccm_big_opS_delete _ _ n); try done.
                     rewrite (ccm_big_opS_delete _ (dom I0) n); try done.
                     unfold ccmop, ccm_op. simpl.
                     rewrite !lookup_total_lifting.
                     unfold FI at 1. rewrite lookup_total_insert.
                     rewrite {1}/In'. 
                     rewrite outflow_lookup_total_map_set_ne; try done.
                     assert (([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI (<[n:=In']> I0) y) n1) = 
                             ([^+ set] y ∈ (dom I0 ∖ {[n]}), 
                                out (FI I0 y) n1)) as ->.
                     { apply ccm_big_opS_ext. intros x Hx. unfold FI. 
                       rewrite lookup_total_insert_ne; try done.
                       clear -Hx; set_solver. }
                     by rewrite ccm_comm. }
                   { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                     destruct Hn1 as [x [Hx1 Hx2]].
                     rewrite Domm_I0 in Hx2; try done.
                     assert (n1 = x) as -> by (clear -Hx2; set_solver).
                     clear -Hx1 n1_notin_I0. try done. }
              * unfold out at 2.
                rewrite outflow_map_set_out_map_ne; try done.
                fold (out ([^op set] x ∈ dom I0, FI I0 x) n').
                rewrite !flow_big_op_out; try done; last first.
                { intros Hn2'. rewrite flow_big_op_dom in Hn2'; try done. 
                  destruct Hn2' as [x0 [Hx0 Hx00]].
                  apply Hn'. apply flow_big_op_dom; try done.
                  rewrite (Domm_I0 x0 Hx0) in Hx00.
                  assert (n' = x0) as -> by (clear -Hx00; set_solver).
                  exists x0. unfold FI. destruct (decide (x0 = n)) as [-> | Hx0n].
                  - rewrite lookup_total_insert. rewrite /In'.
                    rewrite flowint_outflow_map_set_domm. rewrite /In.
                    rewrite (Domm_I0 n n_in_I0). split; try done.
                  - rewrite lookup_total_insert_ne; try done.
                    rewrite (Domm_I0 x0 Hx0). split; try done. }
                apply ccm_big_opS_ext. intros x Hx.
                destruct (decide (x = n)) as [-> | Hxn].
                ** unfold FI. rewrite lookup_total_insert.
                   rewrite /In'. unfold out.
                   by rewrite outflow_map_set_out_map_ne.
                ** unfold FI. rewrite lookup_total_insert_ne; try done. }
        assert (In1' = inflow_map_set f_incr (I !!! n1) n1 S) as H0''.
        { rewrite /In1' /In1. try done. }
        assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
        { assert (dom I0 ∪ {[ n1 ]} ⊆ dom I) as Hsub.
          { clear -n1_in_I Dom_I0_in_I. set_solver. }
          pose proof (flow_big_op_valid _ _ (dom I0 ∪ {[n1]}) Hsub VI) as H'.
          rewrite big_opS_union in H'.
          by rewrite big_opS_singleton in H'.
          clear -n1_notin_I0. set_solver. }
        apply Hpose; try done. 
  Qed.

  Lemma list_flow_upd_marking_KS Key n R Nx Mk S I I' II' nk n0:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (∀ x, x ∈ dom I ∖ {[n0]} → S ## keyset (FI I x)) →
    (n ∈ dom I') → (dom I' ⊆ dom I) →
    (∀ x, x ∈ dom I' → Key !!! x ≤ Key !!! n) →
    (FI I' n = inflow_map_set f_incr (FI I n) n S) →
    (∀ x, x ∈ dom I' ∖ {[n0; n]} → keyset (FI I' x) = keyset (FI I x)) →
    list_flow_upd_rec f_incr n R Nx Mk S I I' = Some (II', nk) →
      (∀ x, x ∈ dom II' ∖ {[n0; nk]} → keyset (FI II' x) = keyset (FI I x)).
  Proof.
    intros FI. apply list_flow_upd_rec_ind; try done; last first.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n.
      intros Nx_key Hcl Disj_KS n_in_I0 Dom_I0_in_I Key_I0 Def_I0_n 
        KS_x [= -> ->].
      done.
    - clear n R Nx Mk S I I'.
      intros n R Nx Mk S I I0 n_in_R Hmk_n n1 Hnx_n In In' In1 In1' II I0'.
      intros HInd Nx_key Hcl Disj_KS n_in_I0 Dom_I0_in_I Key_I0 Def_I0_n 
        KS_x Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { pose proof Nx_key n n1 Hnx_n as H'.
        intros n1_in_I0. apply Key_I0 in n1_in_I0.
        clear -H' n1_in_I0. lia. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { destruct Hcl as [_ [_ Hcl]].
        by pose proof Hcl n n1 Hnx_n as H'. }  
      apply HInd; try done.
      + rewrite Dom_I0'. clear; set_solver.
      + rewrite Dom_I0'. clear -Dom_I0_in_I n1_in_I. set_solver.
      + pose proof Nx_key n n1 Hnx_n as H'. 
        rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        * apply Key_I0 in Hx. clear -Hx H'. lia.
        * assert (x = n1) as -> by (clear -Hx; set_solver).
          clear; try done.
      + by rewrite /I0' /FI lookup_total_insert /In1' /In1.
      + intros x Hx; rewrite Dom_I0' elem_of_difference in Hx.
        destruct Hx as [Hx1 Hx2]. rewrite elem_of_union in Hx1.
        destruct Hx1 as [Hx1 | Hx1]; last first.
        { clear -Hx1 Hx2; set_solver. }
        destruct (decide (x = n)) as [-> | Hxn]; last first.
        { rewrite /I0' /FI /II !lookup_total_insert_ne; try done. 
          apply KS_x. clear -Hx1 Hx2 Hxn; set_solver. clear -Hx2; set_solver. }
        rewrite /I0' /FI /II. 
        rewrite lookup_total_insert_ne; last first. { clear -Hx2; set_solver. }
        rewrite lookup_total_insert /In' /In.
        rewrite /keyset. rewrite outflow_insert_set_insets.
        rewrite outflow_insert_set_outsets. rewrite /FI in Def_I0_n.
        rewrite Def_I0_n. rewrite inflow_insert_set_outsets.
        rewrite inflow_insert_set_insets.
        assert (n ∈ dom I ∖ {[n0]}) as H'.
        { clear -Hx1 Hx2 Dom_I0_in_I. set_solver. }
        apply Disj_KS in H'. rewrite /keyset /FI in H'.
        clear -H'. set_solver.
  Qed.
  
  Lemma marking_flow_upd_summary Key n0 Nx Mk S I res n1:
    let FI := λ I x, I !!! x in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (∀ x, x ∈ dom I → Mk !!! x = true → keyset (FI I x) = ∅) →
    (∀ n1 n2, Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) →
    (Nx !! n0 = Some n1) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (n0 ∈ dom I) →
    (S ≠ ∅) →
    (∀ x, x ∈ dom I ∖ {[n0]} → S ## keyset (FI I x)) →
    (*
    (S ⊆ insets (FI I n0)) →
    (S ## outsets (FI I n0)) →
    *)
    list_flow_upd_marking n0 Nx Mk S I = res →
      ∃ II nk, 
        res = Some (II, nk)
      ∧ (dom II ⊆ dom I)
      ∧ (n0 ∈ dom II)
      ∧ (nk ∈ dom II)
      ∧ (n0 ≠ nk)
      ∧ (Mk !! nk = Some false)
      ∧ (∀ x, x ∈ dom II ∖ {[n0;nk]} → Mk !! x = Some true)
      ∧ (∀ x, x ∈ dom II ∖ {[nk]} → Nx !! x ≠ None)
      ∧ (∀ x, x ∈ dom II ∖ {[n0]} → Key !!! n0 < Key !!! x)
      ∧ (∀ x, x ∈ dom II → dom (FI II x) = {[x]})
      ∧ (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x))
      ∧ (FI II n0 = outflow_insert_set (FI I n0) n1 S)
      ∧ (FI II nk = inflow_insert_set (FI I nk) nk S)
      ∧ (∀ x, x ∈ dom II ∖ {[ n0; nk ]} → FI II x = 
              outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S)
      (* ∧ (keyset (FI II n0) = keyset (FI I n0) ∖ S) *)
      ∧ (∀ x, x ∈ dom II ∖ {[ n0; nk ]} → keyset (FI II x) = keyset (FI I x)).
  Proof.
    intros FI Nx_key Hcl KS_mk Nx_dom Hnx_n0 VI Domm_I n0_in_I S_nonempty
      Disj_KS Hflow.
    unfold list_flow_upd_marking, list_flow_upd in Hflow.
    rewrite Hnx_n0 in Hflow. 
    set In1 := inflow_map_set f_incr (I !!! n1) n1 S.
    set In0 := outflow_map_set f_incr (I !!! n0) n1 S.
    set I': gmap Node (multiset_flowint_ur nat) := {[n1 := In1; n0 := In0]}.
    rewrite -/In1 -/In0 -/I' in Hflow.
    assert (dom I' = {[n0; n1]}) as Dom_I' by set_solver.
    assert (n1 ∈ dom I') as n1_in_I' by set_solver.
    assert (n1 ∈ dom I) as n1_in_I.
    { destruct Hcl as [_ [_ Hcl]]. 
      by apply (Hcl n0). }
    assert (n0 ≠ n1) as n0_neq_n1.
    { pose proof Nx_key n0 n1 Hnx_n0. 
      destruct (decide (n0 = n1)) as [-> | ]; try done.
      lia. }
    assert (dom I = (dom I ∖ {[n0]}) ∪ dom I') as H'.
    { rewrite Dom_I'.
      assert ((dom I ∖ {[n0]}) ∪ {[n0; n1]} ⊆ dom I) as H'.
      { set_solver. }
      assert (dom I ⊆ (dom I ∖ {[n0]}) ∪ {[n0; n1]}) as H''.
      { clear -n0_in_I n1_in_I n0_neq_n1. intros x Hx. 
        destruct (decide (x = n0)); first by set_solver.
        destruct (decide (x = n1)); first by set_solver.
        by set_solver. }
      clear -H' H''; set_solver. }  
    assert ((dom I ∖ {[n0]}) ∩ dom I' = {[n1]}) as H''.
    { rewrite Dom_I'. set_solver. }
    assert (Key !!! n0 < Key !!! n1) as Key_n0_n1.
    { by apply Nx_key in Hnx_n0. }
    assert (∀ x : Node, x ∈ dom I' → Key !!! x ≤ Key !!! n1) as Key_I'.
    { rewrite Dom_I'. intros x; rewrite elem_of_union.
      intros [Hx | Hx].
      - assert (x = n0) as -> by set_solver. lia.
      - assert (x = n1) as -> by set_solver. try done. }
    
    pose proof list_flow_upd_rec_defined Key f_incr n1 (dom I ∖ {[n0]}) 
      Nx Mk S I I' Nx_key Hcl n1_in_I' H' H'' Key_I' as Hpose.
    clear H' H''.
    destruct (list_flow_upd_rec f_incr n1 (dom I ∖ {[n0]}) Nx Mk S I I') 
      as [ (II, nk) |] eqn: Hflow1; try done. clear Hpose.
    
    assert (n0 ∈ dom I') as n0_in_I'.
    { rewrite Dom_I'. clear; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0]} → Key !!! n0 < Key !!! x) as Key_n0.
    { intros x. rewrite Dom_I'. rewrite elem_of_difference.
      rewrite elem_of_union. intros [[Hx1 | Hx1] Hx2]; try done.
      assert (x = n1) as -> by set_solver. done. }
    assert (FI I' n1 = inflow_insert_set (FI I n1) n1 S) as Def_I'_n.
    { unfold FI. subst I'. rewrite lookup_total_insert; try done.  }    
    assert (dom I' ⊆ dom I) as Dom_I'_in_I.
    { rewrite Dom_I'; clear -n0_in_I n1_in_I; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n1]} → Nx !! x ≠ None) as Nx_x.
    { rewrite Dom_I'. intros x Hx. 
      assert (x = n0) as -> by (clear -Hx; set_solver).
      rewrite Hnx_n0. done. }
    assert (∀ x, x ∈ dom I' ∖ {[n0;n1]} → FI I' x = 
      outflow_insert_set (inflow_insert_set (FI I x) x S) (Nx !!! x) S) as I'_x.
    { rewrite Dom_I'. intros x Hx. clear -Hx; set_solver. }  
    assert (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) as Domm_I'.
    { intros x. rewrite Dom_I'. rewrite elem_of_union.
      unfold FI; subst I'. intros [Hx | Hx].
      - assert (x = n0) as -> by (clear -Hx; set_solver).
        rewrite lookup_total_insert_ne; try done.
        rewrite lookup_total_insert.
        subst In0. by apply Domm_I.
      - assert (x = n1) as -> by (clear -Hx; set_solver).
        rewrite lookup_total_insert.
        subst In1. rewrite flowint_inflow_insert_set_dom.
        rewrite Domm_I; try done. clear; set_solver. }
    assert (I' !!! n0 = In0) as Def_I'_n0.
    { subst I'. rewrite lookup_total_insert_ne; try done.
      rewrite lookup_total_insert; done. }      
    assert (✓ (I !!! n0 ⋅ I !!! n1)) as VI'.
    { assert ({[n0; n1]} ⊆ dom I) as Hsub.
      { clear -n1_in_I n0_in_I' Dom_I'_in_I. set_solver. }
      pose proof (flow_big_op_valid _ _ {[n0; n1]} Hsub VI) as VI'.
      rewrite big_opS_union in VI'.
      rewrite !big_opS_singleton in VI'.
      by unfold FI in VI'. clear -n0_neq_n1. set_solver. }
    assert (([^op set] x ∈ dom I', FI I x) = 
                ([^op set] x ∈ dom I', FI I' x)) as Heq.
    { rewrite Dom_I'. 
      rewrite !big_opS_union; [| (clear -n0_neq_n1; set_solver)..].
      rewrite !big_opS_singleton.
      rewrite /I'. unfold FI.
      rewrite lookup_total_insert_ne; try done.
      rewrite !lookup_total_insert.
      rewrite /In0 /In1. 
      apply (flowint_insert_eq _ _ _ _ n1 S); try done.
      - rewrite Domm_I; set_solver.
      - rewrite Domm_I; clear -n0_in_I' Dom_I'_in_I; set_solver. }
    
    assert (nzmap_map_set f_incr S (out (I !!! n0) n1) ≠ 0) as HS'.
    { apply set_choose_L in S_nonempty.
      destruct S_nonempty as [xs HS].
      intros H'. rewrite nzmap_eq in H'.
      pose proof H' xs as H'. rewrite nzmap_lookup_empty in H'.
      rewrite nzmap_lookup_total_map_set /f_incr in H'; try done.
      rewrite /ccmop /nat_op /ccmunit /= /nat_unit in H'. 
      clear -H'. lia. }
    assert (dom (out_map In0) = dom (out_map (FI I n0))) as Domout_map.
    { rewrite /In0 /outflow_insert_set /outflow_map_set.
      simpl. apply leibniz_equiv. rewrite nzmap_dom_insert_nonzero; try done.
      rewrite /FI (Nx_dom n0 n1 Hnx_n0).
      clear; set_solver. }
    assert (∀ x : Node, x ∈ dom I' ∖ {[n0; n1]} →  
      keyset (I' !!! x) = keyset (I !!! x)) as KS_I'.
    { rewrite Dom_I'. intros x Hx. clear -Hx; set_solver. }  

    (*
    assert (insets In0 = insets (I !!! n0)) as Insets_In0.
    { by rewrite outflow_insert_set_insets. }
    assert (outsets In0 = outsets (I !!! n0) ∪ S) as Outsets_In0.
    { unfold outsets.
      pose proof (Nx_dom n0 n1 Hnx_n0) as Nx_dom.
      unfold FI in Nx_dom. rewrite Domout_map Nx_dom.
      apply leibniz_equiv. rewrite !big_opS_singleton.
      rewrite /In0. rewrite outflow_insert_set_outset; try done. }
    assert (keyset In0 = keyset (I !!! n0) ∖ S) as KS_n0.
    { unfold keyset. rewrite Insets_In0 Outsets_In0.
      apply set_eq_subseteq.
      split. 
      split; clear -Insets_S Outsets_S; set_solver. }
    *)
    assert (∀ n1 n2, n1 ∈ dom I' → Nx !! n1 = Some n2 → 
      dom (out_map ((I' !!! n1: multiset_flowint_ur nat))) = {[n2]}) as Nx_dom'.
    { intros n2 n3. rewrite Dom_I'. rewrite elem_of_union.
      intros [Hn2 | Hn2].
      - assert (n2 = n0) as -> by (clear -Hn2; set_solver).
        rewrite Hnx_n0. intros [=<-]. rewrite /I'.
        rewrite lookup_total_insert_ne; try done.
        rewrite lookup_total_insert /In0. 
        apply set_eq_subseteq. split.
        + intros x Hx. rewrite nzmap_elem_of_dom_total in Hx.
          rewrite /outflow_map_set /= in Hx.
          destruct (decide (x = n1)) as [-> | Hxn1]; try done.
          { clear; set_solver. }
          rewrite nzmap_lookup_total_insert_ne in Hx; try done.
          rewrite -nzmap_elem_of_dom_total2 in Hx. apply dec_stable in Hx.
          rewrite /FI in Nx_dom.
          rewrite (Nx_dom n0 n1 Hnx_n0) in Hx.
          clear -Hxn1 Hx; set_solver. 
        + intros x Hx. assert (x = n1) as -> by (clear -Hx; set_solver).
          rewrite nzmap_elem_of_dom_total. rewrite /outflow_map_set /=.
          rewrite nzmap_lookup_total_insert; try done.
      - assert (n2 = n1) as -> by (clear -Hn2; set_solver).
        rewrite /I'. rewrite lookup_total_insert /In1 /=.
        apply Nx_dom. }
    assert (∀ x, x ∈ dom I' ∖ {[n0; n1]} → Mk !! x = Some true) as Mk_x.
    { intros x Hx; rewrite Dom_I' in Hx. clear -Hx; set_solver. }
    
    set R := dom I ∖ {[n0]}.
    
    exists II, nk. repeat split; try done.
    - by apply (list_flow_upd_dom Key f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_n0_dom f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_nk_dom f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_neq Key f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_Mk_nk f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_Mk f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_Nx Key f_incr n1 R Nx Mk S I I' II nk n0).
    - by apply (list_flow_upd_Key_n0 Key f_incr n1 R Nx Mk S I I' II nk n0).
    - by apply (list_flow_upd_domm Key f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_marking_intfEq Key n1 R Nx Mk S I I' II nk n0).
    - by apply (list_flow_upd_II'_n0 Key f_incr n1 R Nx Mk S I I' II nk n0).
    - by apply (list_flow_upd_II'_nk f_incr n1 R Nx Mk S I I' II nk).
    - by apply (list_flow_upd_II' f_incr n1 R Nx Mk S I I' II nk n0).
    - by apply (list_flow_upd_marking_KS Key n1 R Nx Mk S I I' II nk n0).
  Qed.
  
End list_flow_upd_marking.
