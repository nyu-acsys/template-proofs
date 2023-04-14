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
    {measure size R} : list Node :=
    match (bool_decide (n ∈ R)) with
    | false => []
    | true =>
      match find_next (es !!! n) k with
      | None => res
      | Some n' => prepare_upd_rec S es n' k (R ∖ {[n]}) (res ++ [n]) end end.
  intros S es n k R res Hbool n' Hn'.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.

  Definition prepare_upd 
    (S: gset Node) (es: gmap Node (gmap Node (gset K)))
    (n: Node) (k: K) : list Node := 
    prepare_upd_rec S es n k S [].
    
  Lemma prepare_upd_rec_edge S es n k R res l:
    (match (last res) with None => res = [] | Some ln => k ∈ edgeset es ln n end) → 
    (∀ i, 0 ≤ i < ((length res) - 1)%nat → k ∈ edgeset es (res !!! i) (res !!! (i+1)%nat)) →
      prepare_upd_rec S es n k R res = l → 
        (∀ i, 0 ≤ i < ((length l) - 1)%nat → k ∈ edgeset es (l !!! i) (l !!! (i+1)%nat)).
  Proof.
    apply prepare_upd_rec_ind.
    - clear n k R res. intros n k R res n_in_R Hlast HInd <-.
      rewrite /length. intros i Hi. lia.
    - clear n k R res. intros n k R ? n_in_R Fnext_n. 
      intros Hlast HInd <-; try done.
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
    | [] => I'
    | [n] => I'
    | n :: (n1 :: ns as nss) =>
      (* Have to pick from I' because its inflow is already updated *)
      let In := I' !!! n in
      (* Add k to outf(In, n1) *)
      let In' := outflow_insert_set In n1 {[k]} in
      (* Pick from I because n2 must be untouched so far *)
      let In1 := I !!! n1 in
      (* Add k to inf(In1, n1) *)
      let In1' := inflow_insert_set In1 n1 {[k]} in
      let II := <[n := In']> I' in
      let II' := <[n1 := In1']> II in  
      flow_upd_rec k I II' nss end.
        
  Functional Scheme flow_upd_rec_ind := Induction for flow_upd_rec Sort Prop.
    
  Definition flow_upd S es n0 k I : gmap Node (multiset_flowint_ur K) :=
    match find_next (es !!! n0) k with
    | None => I
    | Some n1 =>
      let In0 := I !!! n0 in
      let In0' := outflow_insert_set In0 n1 {[k]} in
      let In1 := I !!! n1 in
      let In1' := inflow_insert_set In1 n1 {[k]} in
      let I' := <[n1 := In1']> {[n0 := In0']} in
      let l := prepare_upd S es n1 k in
      flow_upd_rec k I I' l end.  

  Lemma flow_upd_intfEq k I I' l II' :
    let FI := λ I x, I !!! x in 
    (* ((∀ n n1 Xn, A !! n = Some (n1, Xn) → dom (out_map (FI I n)) = {[n1]})) → *)
    (match l with [] => True 
                | n :: ns => 
                    (∀ x, x ∈ dom I' ∖ {[n]} → dom (out_map (FI I' x)) ⊆ dom I')
                    ∧ True (* (∀ n1 Xn1, A !! n = Some (n1, Xn1) → 
                                    dom (out_map (FI I' n)) = {[n1]}) *) end) →
      ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
        flow_upd_rec k I I' l = II' → 
          ([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x).
  Proof.
    intros FI. apply flow_upd_rec_ind.
    - intros ? ?  -> _ ? ->. done.
    - intros I0 ? n ? -> -> ? Heq ->. done.
    - intros I0 ? n ? -> n1 ns ->. 
      intros In In' In1 In1' II I0' HInd (* HoutI *) [Hout_dom Houtn_dom] Heq Hflow.
      apply HInd; try done.
      { destruct ns; try done. 
        assert (n0 = n1) as ->. { admit. }
        assert (dom I0' = dom I0 ∪ {[n1]}) as ->.
        { admit. } split.
        - intros x Hx.
          assert (n1 ∉ dom I0) as n1_notin_I0.
          { admit. }
          assert ((dom I0 ∪ {[n1]}) ∖ {[n1]} = dom I0) as H'.
          { set_solver. }
          rewrite H' in Hx. clear H'.
          destruct (decide (x = n)) as [-> | Hxn].
          + assert (n ≠ n1) as n_neq_n1 by set_solver.
            subst I0'. unfold FI.
            rewrite lookup_total_insert_ne; try done.
            subst II.
            rewrite lookup_total_insert.
            subst In'.
            (*
            pose proof (flowint_outflow_map_set_dom (λ (_ : K) (x : nat), x + 1) In n1 {[k]}) as H'.
            pose proof Houtn_dom n1 {[k]} HA0 as H''.
            rewrite /In in H'. rewrite /FI in H''.
            rewrite H'' in H'. clear -H'; set_solver.
            *)
            admit.
          + assert (x ∈ dom I0 ∖ {[n]}) as H' by set_solver.
            apply Hout_dom in H'. 
            subst I0'. unfold FI.
            assert (x ≠ n1) by set_solver.
            rewrite lookup_total_insert_ne; try done.
            subst II.
            rewrite lookup_total_insert_ne; try done.
            rewrite /FI in H'.
            clear -H'; set_solver.  
        - (*
          intros n2 X2 HA_n2. rewrite /I0' /FI.
          rewrite lookup_total_insert. rewrite /In1'.
          unfold out_map. unfold inflow_map_set.
          simpl. rewrite /In1.
          apply (HoutI _ _ X2); try done.
          *) done. }
      assert (n ∈ dom I0) as dom_I0.
      { admit. }
      assert (dom I0' = dom I0 ∪ {[ n1 ]}) as dom_I0'.
      { admit. }
      assert (n1 ∉ dom I0) as n_notin_I0.
      { admit. }
      rewrite dom_I0'. rewrite !big_opS_union.
      rewrite !big_opS_singleton. 
      all: try (clear -n_notin_I0; set_solver).
      rewrite /I0'; rewrite /FI. rewrite lookup_total_insert.
      rewrite /II.
      assert (([^op set] y ∈ dom I0, FI (<[n1:=In1']> (<[n:=In']> I0)) y) = 
                ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Def_II.
      { admit. }
      rewrite Def_II.
      assert (✓ ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)) as Valid_II.
      { admit. }
      assert (✓ ([^op set] y ∈ dom I0, FI I y)) as Valid_I.
      { admit. }
      assert (∀ x, domm (FI I x) = {[x]}) as domm_I.
      { admit. }
      assert (∀ x, domm (FI (<[n:=In']> I0) x) = {[x]}) as domm_II.
      { admit. }

      (*
      assert (∀ (k : K) (x y : nat),
        x ≤ y → (λ (_ : K) (x1 : nat), x1 + 1) k x ≤ (λ (_ : K) (x1 : nat), x1 + 1) k y) as H'.
      { intros; simpl. unfold ccmop, nat_op. lia. }
      *)
      pose proof (flowint_insert_eq
                    ([^op set] y ∈ dom I0, I !!! y)
                    ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                    (I !!! n1)
                    In1' 
                    n1 
                    {[k]}) as Hpose. 
      (* 
      simpl in Hpose. unfold ccmop, nat_op in Hpose.
      assert (∀ k : K,
           k ∈ Xk
           → ((inf (FI I n1) n1) !!! k - 
                ((out ([^op set] y ∈ dom I0, FI I y) n1) !!! k))%nat =
             (((inf (FI I n1) n1 !!! k) + 1) - 
              (((out ([^op set] y ∈ dom I0, FI I y) n1) !!! k) + 1))%nat)
        as H''.
      { intros k Hk. lia. }
      *)
      assert (n1 ∈ domm (FI I n1)) as n1_in_In1.
      { admit. }
      assert (domm ([^op set] y ∈ dom I0, I !!! y) ≠ ∅) as H'''.
      { admit. }
      assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) =
        outflow_insert_set ([^op set] y ∈ dom I0, I !!! y) n1 {[k]}) 
        as H0'.
      { apply intEq. 
        - rewrite flowint_outflow_map_set_domm. admit.
        - admit. 
        - intros n'. unfold inf. rewrite outflow_map_set_inf.
          assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n'
            ≡ default 0 (inf_map ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) !! n'))
            as HL by try done.
          assert (inf ([^op set] y ∈ dom I0, FI I y) n'
            ≡ default 0 (inf_map ([^op set] y ∈ dom I0, I !!! y) !! n')) as HR by try done.
          rewrite <-HL. rewrite <-HR.
          assert (inf ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) n' = 
                    inf ([^op set] y ∈ dom I0, FI I0 y) n') as HI0.
          { destruct (decide (n' ∈ domm ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y))) 
              as [Hn' | Hn'].
            - rewrite flow_big_op_dom in Hn'.
              destruct Hn' as [n'' [n''_in_I0 n'_in_n'']].
              rewrite domm_II in n'_in_n''.
              assert (n' = n'') as <- by (clear -n'_in_n''; set_solver).
              rewrite (flow_big_op_inf _ _ n'); try done.
              + rewrite (flow_big_op_inf _ _ n'); try done.
                * clear HL HR. 
                  assert (([^+ set] x ∈ (dom I0 ∖ {[n']}), out (FI (<[n:=In']> I0) x) n')
                    = ([^+ set] x ∈ (dom I0 ∖ {[n']}), out (FI I0 x) n')) as Hout.
                  { destruct (decide (n' = n)) as [-> | Hn'].
                    - (* forall x ∈ dom I0 ∖ {[n]}, FI (<[n:=In']> I0) x = FI I0 x *)
                      admit.
                    - admit. }
                  assert (inf (FI (<[n:=In']> I0) n') n' = inf (FI I0 n') n') as Hin.
                  { destruct (decide (n' = n)) as [-> | Hn'].
                    - rewrite /FI. rewrite lookup_total_insert. subst In'.
                      unfold inf. rewrite outflow_map_set_inf. by subst In.
                    - rewrite /FI. rewrite lookup_total_insert_ne; try done. }
                  by rewrite Hin Hout.
                * admit. 
                * admit.
              + rewrite domm_II; clear; set_solver.
              + apply Valid_II. 
            - admit.
          }
          by rewrite HI0 Heq.
        - rewrite Heq.
          assert (∀ x n', x ∈ dom I0 ∖ {[n]} → out (FI I0 x) n' = 0).
          { admit. }
          intros n'.  
          destruct (decide (n' = n1)) as [-> | Hn'].
          + rewrite /outflow_insert_set. unfold out at 2. unfold outflow_map_set.
            simpl. rewrite nzmap_lookup_total_insert.
            rewrite flow_big_op_out.
            * rewrite nzmap_eq. intros k'.
              assert (([^+ set] x ∈ dom I0, out (FI (<[n:=In']> I0) x) n1) !!! k'  
                         = (out In' n1) !!! k') as H1'.
              { admit. }
              rewrite H1'.
              destruct (decide (k' = k)) as [-> | ?].
              ** rewrite nzmap_lookup_total_map_set; last first. 
                 clear; set_solver.
                 assert ((out ([^op set] x ∈ dom I0, FI I0 x) n1) !!! k
                            = (out (FI I0 n) n1) !!! k) as H1''.
                 { admit. }
                 rewrite H1''.
                 rewrite /In'.
                 rewrite outflow_lookup_total_map_set; try done.
                 clear; set_solver.
              ** assert (out ([^op set] x ∈ dom I0, FI I0 x) n1
                            = out (FI I0 n) n1) as H1''.
                 { admit. }
                 rewrite H1''.
                 rewrite nzmap_lookup_total_map_set_ne; try (clear -n0; set_solver).
                 rewrite /In'.
                 rewrite outflow_lookup_total_map_set_ne; try (clear -n0; set_solver).
            * admit.
            * admit.
          + unfold out at 2. rewrite outflow_map_set_out_map_ne; try done.
            simpl. fold (out (([^op set] x ∈ dom I0, FI I0 x)) n'). 
            admit. }
      assert (In1' = inflow_insert_set (I !!! n1) n1 {[k]}) as H0''.
      { rewrite /In1' /In1. try done. }
      assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
      { admit. }
      by pose proof Hpose n1_in_In1 H''' H0' H0'' H0''' as Hpose.
  Admitted.      
    
