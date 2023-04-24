Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.

Section list_flow_upd.
  Context `{Countable K}.
  Open Scope ccm_scope.
  
  Parameter KS : gset K.
  
  Definition edgeset (es: gmap Node (gmap Node (gset K))) n1 n2 : gset K :=
    (es !!! n1) !!! n2.
  
  Definition find_next (esn: gmap Node (gset K)) (k: K) : option Node := 
    let f := λ (n': Node) (esn': gset K) res, 
              match res with
              | Some n'' => Some n''
              | None => if (bool_decide (k ∈ esn'))
                        then Some n'
                        else None end in
    map_fold f (None: option Node) esn.

  Function prepare_upd_rec 
    (S: gset Node) (es: gmap Node (gmap Node (gset K)))
    (n: Node) (k: K) (R: gset Node) (res: list Node) 
    {measure size R} : option (list Node) :=
    match (bool_decide (n ∈ R)) with
    | false => None
    | true =>
      match find_next (es !!! n) k with
      | None => Some res
      | Some n' => prepare_upd_rec S es n' k (R ∖ {[n]}) (res ++ [n]) end end.
  intros S es n k R res Hbool n' Hn'.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.

  Definition prepare_upd 
    (S: gset Node) (es: gmap Node (gmap Node (gset K)))
    (n: Node) (k: K) : option (list Node) := 
    prepare_upd_rec S es n k S [].
    
  Lemma prepare_upd_rec_edge S es n k R res l:
    (match (last res) with None => res = [] | Some ln => k ∈ edgeset es ln n end) → 
    (∀ i, 0 ≤ i < ((length res) - 1)%nat → k ∈ edgeset es (res !!! i) (res !!! (i+1)%nat)) →
      prepare_upd_rec S es n k R res = Some l → 
        (∀ i, 0 ≤ i < ((length l) - 1)%nat → k ∈ edgeset es (l !!! i) (l !!! (i+1)%nat)).
  Proof.
    apply prepare_upd_rec_ind.
    - clear n k R res. intros n k R res n_in_R Hlast HInd ?. try done.
    - clear n k R res. intros n k R ? n_in_R Fnext_n. 
      intros Hlast HInd [= <-]; try done.
    - clear n k R res. intros n k R res n_in_R n1 Fnext_n. 
      intros HInd Hlast HInd_res. apply HInd; try done.
      + assert (last (res ++ [n]) = Some n) as H'.
        { admit. }
        rewrite H'.
        unfold edgeset. admit.
      + intros i Hi. rewrite app_length in Hi; repeat simpl in Hi.
        assert (∀ x, (x + 1 - 1)%nat = x) as Hplusminus. 
        { lia. } rewrite Hplusminus in Hi.
        destruct (decide (i = (length res - 1)%nat)) as [H' | H'].
        * destruct (last res) as [lr | ].
          ** assert ((res ++ [n]) !!! i = lr) as ->.
             { admit. }
             assert ((res ++ [n]) !!! (i + 1)%nat = n) as ->.
             { admit. }
             done.
          ** rewrite Hlast in Hi; simpl in Hi. exfalso. lia.
        * assert ((res ++ [n]) !!! i = res !!! i) as ->.
          { admit. }
          assert ((res ++ [n]) !!! (i + 1)%nat = res !!! (i + 1)%nat) as ->.
          { admit. }
          apply HInd_res. lia.
  Admitted.
    
    
  Fixpoint flow_upd_rec k (I I': gmap Node (multiset_flowint_ur K)) l :=
    match l with
    | [] => None
    | [n] => Some (I', n)
    | n :: (n1 :: ns) as nss =>
      (* Have to pick from I' because its inflow is already updated *)
      let In := I' !!! n in
      (* Add k to outf(In, n1) *)
      let In' := outflow_insert_set In n1 {[k]} in
      (* Pick from I because n1 must be untouched so far *)
      let In1 := I !!! n1 in
      (* Add k to inf(In1, n1) *)
      let In1' := inflow_insert_set In1 n1 {[k]} in
      let II := <[n := In']> I' in
      let II' := <[n1 := In1']> II in  
      flow_upd_rec k I II' nss end.
        
  Functional Scheme flow_upd_rec_ind := Induction for flow_upd_rec Sort Prop.
    
  Definition flow_upd S es n0 (k: K) I : option (gmap Node (multiset_flowint_ur K) * Node) :=
    match find_next (es !!! n0) k with
    | None => None
    | Some n1 =>
      let In0 := I !!! n0 in
      let In0' := outflow_insert_set In0 n1 {[k]} in
      let In1 := I !!! n1 in
      let In1' := inflow_insert_set In1 n1 {[k]} in
      let I' := <[n1 := In1']> {[n0 := In0']} in
      match prepare_upd S es n1 k with
      | None => None
      | Some l => 
        flow_upd_rec k I I' l end end.  

  Lemma flow_upd_intfEq k I I' l II' nl:
    let FI := λ I x, I !!! x in 
      (NoDup l) →
      (match l with 
        | [] => True 
        | n :: ns => 
            n ∈ dom I'
          ∧ FI I' n = inflow_insert_set (FI I n) n {[k]}
          ∧ (list_to_set ns ## dom I') end) →
      (✓ ([^op set] x ∈ dom I, FI I x)) →
      (dom I' ⊆ dom I) → (list_to_set l ⊆ dom I) →
      (∀ x, x ∈ dom I → domm (FI I x) = {[x]}) →
      (∀ x, x ∈ dom I' → domm (FI I' x) = {[x]}) →
      ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
        flow_upd_rec k I I' l = Some (II', nl) → 
          (([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x)
          ∧ keyset (FI II' nl) = keyset (FI I nl) ∪ {[k]}).
  Proof.
    intros FI. apply flow_upd_rec_ind.
    - intros; try done.
    - intros I0 ? n ? -> -> _ HdomI _ _ _ _ _ Heq [= ->]. split; try done.
      Search inflow_insert_set.
    - intros I0 ? n ? -> n1 ns ->. 
      intros In In' In1 In1' II I0' HInd NoDup [n_in_I0 HdomI_disj] 
        VI Dom_I0_in_I l_in_I Domm_I Domm_I0 Heq Hflow.
      assert (n1 ∉ dom I0) as n1_notin_I0.
      { clear -HdomI_disj. set_solver. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as Dom_I0'.
      { rewrite /I0' /II.
        repeat rewrite dom_insert_L.
        clear -n_in_I0 n1_notin_I0.
        set_solver. }
      assert (n1 ∈ dom I) as n1_in_I.
      { clear -l_in_I. set_solver. }  
      assert (∀ x, x ∈ dom I0 → domm (FI (<[n:=In']> I0) x) = {[x]}) as Domm_II.
      { intros x Hx. destruct (decide (n = x)) as [-> | Hxn].
        - unfold FI. rewrite lookup_total_insert.
          subst In'. rewrite flowint_outflow_map_set_domm.
          subst In. rewrite Domm_I0; try done.
        - unfold FI. rewrite lookup_total_insert_ne; try done.
          rewrite Domm_I0; try done. }
      apply HInd; try done; clear HInd.
      { clear -NoDup. apply NoDup_cons in NoDup.
        destruct NoDup as [_ ?]; try done. }
      { rewrite Dom_I0'. split. 
        - clear; set_solver.
        - apply NoDup_cons in NoDup. destruct NoDup as [_ NoDup]. 
          apply NoDup_cons in NoDup. destruct NoDup as [NoDup _].
          clear -HdomI_disj NoDup. set_solver. }
      { rewrite Dom_I0'. clear -Dom_I0_in_I n1_in_I. set_solver. }
      { clear -l_in_I. set_solver. }
      { rewrite Dom_I0'. intros x; rewrite elem_of_union.
        intros [Hx | Hx].
        - subst I0'. 
          assert (x ≠ n1) as H'.
          { clear -Hx n1_notin_I0. set_solver. }
          unfold FI.
          rewrite lookup_total_insert_ne; try done.
          subst II.
          apply Domm_II; try done.
        - assert (x = n1) as -> by (clear -Hx; set_solver).
          unfold FI. subst I0'.
          rewrite lookup_total_insert.
          subst In1'.
          rewrite flowint_inflow_map_set_dom.
          subst In1. rewrite Domm_I; try done.
          clear; set_solver. }
      rewrite Dom_I0'. rewrite !big_opS_union; [try done | set_solver | set_solver].
      rewrite !big_opS_singleton. 
      all: try (clear -n_notin_I0; set_solver).
      rewrite /I0'; rewrite /FI. rewrite lookup_total_insert.
      rewrite /II.
      assert (([^op set] y ∈ dom I0, FI (<[n1:=In1']> (<[n:=In']> I0)) y) = 
                ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Def_II.
      { (* syntactic rewriting *) admit. }
      rewrite Def_II.
      assert (✓ ([^op set] y ∈ dom I0, FI I y)) as Valid_I.
      { apply (flow_big_op_valid _ (dom I)); try done. }
      assert (✓ ([^op set] y ∈ dom I0, FI I0 y)) as Valid_I0.
      { apply leibniz_equiv_iff in Heq. rewrite <-Heq. try done. }
      assert (✓ ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Valid_II.
      { assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) = 
                  ([^op set] y ∈ dom I0 ∖ {[n]}, FI I0 y) ⋅ In') as ->.
        { (* syntactic rewriting *) admit. }
        apply (outflow_map_set_valid2
                      (([^op set] y ∈ (dom I0 ∖ {[n]}), FI I0 y)) 
                      (I0 !!! n)  
                      (In')
                      (λ _ n, n + 1)%nat 
                      n1
                      {[k]}).
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
          { (* syntactic rewriting *) admit. }
          by rewrite H'. }

      pose proof (flowint_insert_eq
                    ([^op set] y ∈ dom I0, I !!! y)
                    ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                    (I !!! n1)
                    In1' 
                    n1 
                    {[k]}) as Hpose. 
      assert (n1 ∈ domm (FI I n1)) as n1_in_In1.
      { rewrite Domm_I; try done. clear; set_solver. }
      assert (domm ([^op set] y ∈ dom I0, I !!! y) ≠ ∅) as Domm_I0_notEmpty.
      { assert (n ∈ (domm ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
        { rewrite flow_big_op_dom; try done. exists n; split; try done.
          rewrite Domm_I; last first.
          { clear -n_in_I0 Dom_I0_in_I. set_solver. } 
          clear; set_solver. }
        clear -H'; set_solver. }
      assert (domm ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)) = 
                domm ([^op set] y ∈ dom I0, (I !!! y))) as Domm_II_eq_I.
      { assert ((domm ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y))) ⊆ 
                    (domm ([^op set] y ∈ dom I0, (I !!! y)))) as H'.
        { intros n'. rewrite !flow_big_op_dom; try done.
          intros [x [Hx1 Hx2]]. exists x. split; try done.
          rewrite Domm_II in Hx2; try done. rewrite Domm_I; try done.
          clear -Hx1 Dom_I0_in_I. set_solver. }
        assert ((domm ([^op set] y ∈ dom I0, (I !!! y))) ⊆ 
                  (domm ([^op set] y ∈ dom I0, (FI (<[n:=In']> I0) y)))) as H''.
        { intros n'. rewrite !flow_big_op_dom; try done.
          intros [x [Hx1 Hx2]]. exists x. split; try done.
          rewrite Domm_II. rewrite Domm_I in Hx2; try done.
          clear -Hx1 Dom_I0_in_I. set_solver. done. }
        clear -H' H''; set_solver. }
      assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) =
        outflow_insert_set ([^op set] y ∈ dom I0, I !!! y) n1 {[k]}) 
        as H0'.
      { apply intEq; try done. 
        - rewrite Domm_II_eq_I. try done. 
        - intros n'. unfold inf. rewrite outflow_map_set_inf.
          assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n'
            ≡ default 0 (inf_map ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) !! n'))
            as HL by try done.
          assert (inf ([^op set] y ∈ dom I0, FI I y) n'
            ≡ default 0 (inf_map ([^op set] y ∈ dom I0, I !!! y) !! n')) as HR by try done.
          rewrite <-HL. rewrite <-HR.
          rewrite Heq.
          assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n' = 
                    inf ([^op set] y ∈ dom I0, FI I0 y) n') as HI0.
          { destruct (decide (n' ∈ domm ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
              as [Hn' | Hn'].
            - rewrite flow_big_op_dom in Hn'; try done.
              destruct Hn' as [n'' [n''_in_I0 n'_in_n'']].
              rewrite Domm_II in n'_in_n''; try done.
              assert (n' = n'') as <- by (clear -n'_in_n''; set_solver).
              rewrite (flow_big_op_inf _ _ n'); try done.
              + rewrite (flow_big_op_inf _ _ n'); try done.
                * clear HL HR. 
                  assert (([^+ set] x ∈ (dom I0 ∖ {[n']}), out (FI (<[n:=In']> I0) x) n')
                    = ([^+ set] x ∈ (dom I0 ∖ {[n']}), out (FI I0 x) n')) as Hout.
                  { destruct (decide (n' = n)) as [-> | Hn'].
                    - (* forall x ∈ dom I0 ∖ {[n]}, FI (<[n:=In']> I0) x = FI I0 x *)
                      (* syntactic rewriting *)
                      admit.
                    - assert (out (FI (<[n := In']> I0) n) n' = out (FI I0 n) n') as H'.
                      { rewrite /FI. rewrite lookup_total_insert.
                        rewrite /In' /In.
                        assert (n' ≠ n1). { clear -n''_in_I0 n1_notin_I0. set_solver. }
                        unfold out. rewrite outflow_map_set_out_map_ne; try done. }
                      (* break the big sum *)
                      (* syntactic rewriting + above assert *)
                      admit. }
                  assert (inf (FI (<[n:=In']> I0) n') n' = inf (FI I0 n') n') as Hin.
                  { destruct (decide (n' = n)) as [-> | Hn'].
                    - rewrite /FI. rewrite lookup_total_insert. subst In'.
                      unfold inf. rewrite outflow_map_set_inf. by subst In.
                    - rewrite /FI. rewrite lookup_total_insert_ne; try done. }
                  by rewrite Hin Hout.
                * rewrite Domm_I0; try done.
              + rewrite Domm_II; try done.
            - (* syntactic rewriting + flow_inf lemma *) admit.
          }
          by rewrite HI0.
        - rewrite Heq.
          intros n'.
          destruct (decide (n' ∈ domm ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
              as [Hn' | Hn'].
          + (* syntactic rewriting + flow_outf lemma *) admit.     
          + destruct (decide (n' = n1)) as [-> | Hn1'].
            * apply nzmap_eq. intros k'. destruct (decide (k' ∈ ({[k]}: gset K))) as [Hk' | Hk'].
              ** rewrite outflow_lookup_total_map_set; try done.
                 rewrite !flow_big_op_out.
                 (* break the big sum + lookup_total_lifting *)
                 admit.
                 { apply leibniz_equiv_iff in Heq. rewrite <-Heq. try done. }
                 { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                   destruct Hn1 as [x [Hx1 Hx2]].
                   rewrite Domm_I0 in Hx2; try done.
                   assert (n1 = x) as -> by set_solver.
                   clear -Hx1 n1_notin_I0. try done. }
                 { try done. }
                 { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                   destruct Hn1 as [x [Hx1 Hx2]].
                   rewrite Domm_II in Hx2; try done.
                   assert (n1 = x) as -> by set_solver.
                   clear -Hx1 n1_notin_I0. try done. }
              ** rewrite outflow_lookup_total_map_set_ne; try done.
                 rewrite !flow_big_op_out.
                 (* break the big sum + lookup_total_lifting *)
                 admit.
                 { try done. }
                 { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                   destruct Hn1 as [x [Hx1 Hx2]].
                   rewrite Domm_I0 in Hx2; try done.
                   assert (n1 = x) as -> by set_solver.
                   clear -Hx1 n1_notin_I0. try done. }
                 { try done. }
                 { intros Hn1. rewrite flow_big_op_dom in Hn1; try done.
                   destruct Hn1 as [x [Hx1 Hx2]].
                   rewrite Domm_II in Hx2; try done.
                   assert (n1 = x) as -> by set_solver.
                   clear -Hx1 n1_notin_I0. try done. }
            * unfold out. rewrite outflow_map_set_out_map_ne; try done.
              (* syntactic rewriting *)
              admit. }                           
      assert (In1' = inflow_insert_set (I !!! n1) n1 {[k]}) as H0''.
      { rewrite /In1' /In1. try done. }
      assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
      {  admit. }
      by pose proof Hpose n1_in_In1 Domm_I0_notEmpty H0' H0'' H0''' as Hpose.
  Admitted.      
    
