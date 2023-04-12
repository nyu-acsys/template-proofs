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
    
  
  (* 
    h --> 4 --> 7 --> 10x --> 15x --> 20  
    h --> 4 --> 7x --> 10x --> 15x --> 20 
  *)
  
  Function prepare_upd_rec 
    (S: gset Node) (es: gmap Node (Node * (gset K)))
    (n: Node) (R: gset Node) (res: list Node)
    (X: gset K) (A: gmap Node (Node * gset K))
    {measure size R} : list Node * gmap Node (Node * gset K) :=
    match (bool_decide (n ∈ R)) with
    | false => ([], ∅)
    | true =>
      match es !! n with
      | Some (n1, esn) =>
        let Xk := esn ∩ X in
        match (bool_decide (Xk = ∅)) with
        | true => (res ++ [n], A)
        | false => 
          prepare_upd_rec S es n1 (R ∖ {[n]}) (res ++ [n]) Xk (<[n := (n1, Xk)]> A) end
      | None => (res ++ [n], A) end end.
  intros S es n R res X A Hbool (n1, esn) n' esn' H'; inversion H'.
  subst n' esn'. intros Hesn Hbool1.
  rewrite bool_decide_eq_true in Hbool.
  assert (R ∖ {[n]} ⊂ R). 
  { set_solver. } by apply subset_size.
  Defined.
  
  Definition prepare_upd S es n0 X : list Node * gmap Node (Node * gset K) :=
    prepare_upd_rec S es n0 S [] X ∅.
    
   Definition edge_rel (es: gmap Node (Node * (gset K))) (n n': Node) : Prop := 
    ∃ esn, es !! n = Some (n', esn).   
    
  Lemma prepare_upd_rec_edge S es n R res X A l A':
    (match (last res) with None => res = [] | Some ln => edge_rel es ln n end) → 
    (∀ i, 0 ≤ i < ((length res) - 1)%nat → edge_rel es (res !!! i) (res !!! (i+1)%nat)) →
      prepare_upd_rec S es n R res X A = (l, A') → 
        (∀ i, 0 ≤ i < ((length l) - 1)%nat → edge_rel es (l !!! i) (l !!! (i+1)%nat)).
  Proof.
    apply prepare_upd_rec_ind.
    - intros n0 R0 res0 X0 A0 n0_in_R0 Hlast HInd [= <- <-].
      rewrite /length. intros i Hi. lia.
    - intros n0 R0 res0 X0 A0 n0_in_R0 n1 esn Hesn Xk HXk Hlast HInd [= <- <-] i Hi.
      rewrite app_length in Hi; repeat simpl in Hi.
      assert (∀ x, (x + 1 - 1)%nat = x) as Hplusminus. 
      { lia. } rewrite Hplusminus in Hi.
      destruct (decide (i = (length res0 - 1)%nat)) as [H' | H'].
      + subst i. 
        admit.
      + admit.
    - intros n0 R0 res0 X0 A0 n0_in_R0 n1 esn Hesn Xk HXk HInd0 Hlast HInd Hprepare.
      apply HInd0. 
      + assert (last (res0 ++ [n0]) = Some n0) as H'.
        { admit. }
        rewrite H'.
        unfold edge_rel. by exists esn.
      + admit.
      + done.
    - intros n0 R0 res0 X0 A0 n0_in_R0 Hesn Hlast HInd [= <- <-].
      admit.
  Admitted.


  Fixpoint flow_upd_helper (I I': gmap Node (multiset_flowint_ur K))
    (A: gmap Node (Node * gset K))
    (l: list Node) : gmap Node (multiset_flowint_ur K) :=
    match l with
    | [] => I'
    | n :: ns =>
      match A !! n with
      | None => ∅
      | Some (n1, Xk) =>
        (* Have to pick from I' because its inflow is already updated *)
        let In := I' !!! n in
        (* Add Xk to outf(In, n1) *)
        let In' := outflow_map_set (λ k x, x+1) In n1 Xk in
        (* Pick from I because n1 is untouched so far *)
        let In1 := I !!! n1 in
        (* Add Xk to inf(In1, n1) *)
        let In1' := inflow_map_set (λ k x, x+1) In1 n1 Xk in
        let II := <[n := In']> I' in
        let II' := <[n1 := In1']> II in  
        flow_upd_helper I II' A ns end end.
  
  Functional Scheme flow_upd_helper_ind := Induction for flow_upd_helper Sort Prop.


  
  Definition flow_upd S es I n0 : gmap Node (multiset_flowint_ur K) :=
    match es !! n0 with
    | None => ∅
    | Some (n1, es_n0) =>
      let In0 := I !!! n0 in
      let inf_n0 := inset K In0 n0 in
      let X := inf_n0 ∩ (KS ∖ es_n0) in      
      let (l, A) := prepare_upd S es n1 X in
      let In0' := outflow_map_set (λ k x, x+1) In0 n1 X in
      let In1 := I !!! n1 in
      let In1' := inflow_map_set (λ k x, x+1) In1 n1 X in
      let II := {[n0 := In0']} in
      let I' := <[n1 := In1']> II in  
      flow_upd_helper I I' A l end.
      
      
  Lemma flow_upd_intfEq I I' A l II' :
    let FI := λ I x, I !!! x in 
    ((∀ n n1 Xn, A !! n = Some (n1, Xn) → dom (out_map (FI I n)) = {[n1]})) →
    (match l with [] => True 
                | n :: ns => 
                    (∀ x, x ∈ dom I' ∖ {[n]} → dom (out_map (FI I' x)) ⊆ dom I')
                    ∧ (∀ n1 Xn1, A !! n = Some (n1, Xn1) → 
                                    dom (out_map (FI I' n)) = {[n1]}) end) →
      ([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x) →
        flow_upd_helper I I' A l = II' → 
          ([^op set] x ∈ dom II', FI I x) = ([^op set] x ∈ dom II', FI II' x).
  Proof.
    intros FI. apply flow_upd_helper_ind.
    - intros I0 II0 ? -> _ _ HInd ->. done.
    - intros I0 A0 ? n ns -> ? HA0 n1 Xk ->. 
      intros In In' In1 In1' II I0' HInd HoutI [Hout_dom Houtn_dom] Heq Hflow.
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
            pose proof (flowint_outflow_map_set_dom (λ (_ : K) (x : nat), x + 1) In n1 Xk) as H'.
            pose proof Houtn_dom n1 Xk HA0 as H''.
            rewrite /In in H'. rewrite /FI in H''.
            rewrite H'' in H'. clear -H'; set_solver.
          + assert (x ∈ dom I0 ∖ {[n]}) as H' by set_solver.
            apply Hout_dom in H'. 
            subst I0'. unfold FI.
            assert (x ≠ n1) by set_solver.
            rewrite lookup_total_insert_ne; try done.
            subst II.
            rewrite lookup_total_insert_ne; try done.
            rewrite /FI in H'.
            clear -H'; set_solver.  
        - intros n2 X2 HA_n2. rewrite /I0' /FI.
          rewrite lookup_total_insert. rewrite /In1'.
          unfold out_map. unfold inflow_map_set.
          simpl. rewrite /In1.
          apply (HoutI _ _ X2); try done. }
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

      
      assert (∀ (k : K) (x y : nat),
        x ≤ y → (λ (_ : K) (x1 : nat), x1 + 1) k x ≤ (λ (_ : K) (x1 : nat), x1 + 1) k y) as H'.
      { intros; simpl. unfold ccmop, nat_op. lia. }
      pose proof (flowint_map_set_eq 
                    (λ (_ : K) (x : nat), x + 1) 
                    ([^op set] y ∈ dom I0, I !!! y)
                    ([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y)
                    (I !!! n1)
                    In1' 
                    n1 
                    Xk H') as Hpose. 
      simpl in Hpose. unfold ccmop, nat_op in Hpose.
      assert (∀ k : K,
           k ∈ Xk
           → ((inf (FI I n1) n1) !!! k - 
                ((out ([^op set] y ∈ dom I0, FI I y) n1) !!! k))%nat =
             (((inf (FI I n1) n1 !!! k) + 1) - 
              (((out ([^op set] y ∈ dom I0, FI I y) n1) !!! k) + 1))%nat)
        as H''.
      { intros k Hk. lia. }
      assert (n1 ∈ domm (FI I n1)) as n1_in_In1.
      { admit. }
      assert (domm ([^op set] y ∈ dom I0, I !!! y) ≠ ∅) as H'''.
      { admit. }
      assert (([^op set] y ∈ dom I0, FI (<[n:=In']> I0) y) =
        outflow_map_set (λ (_ : K) (x0 : nat), (x0 + 1)%nat) ([^op set] y ∈ dom I0, I !!! y) n1 Xk) 
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
          + rewrite /outflow_map_set. unfold out at 2, out_map at 2.
            simpl. rewrite nzmap_lookup_total_insert.
            rewrite flow_big_op_out.
            * rewrite nzmap_eq. intros k.
              assert (([^+ set] x ∈ dom I0, out (FI (<[n:=In']> I0) x) n1) !!! k  
                         = (out In' n1) !!! k) as H1'.
              { admit. }
              rewrite H1'.
              destruct (decide (k ∈ Xk)).
              ** rewrite nzmap_lookup_total_map_set; try done.
                 assert ((out ([^op set] x ∈ dom I0, FI I0 x) n1) !!! k
                            = (out (FI I0 n) n1) !!! k) as H1''.
                 { admit. }
                 rewrite H1''.
                 rewrite /In'.
                 rewrite outflow_lookup_total_map_set; try done.
              ** assert (out ([^op set] x ∈ dom I0, FI I0 x) n1
                            = out (FI I0 n) n1) as H1''.
                 { admit. }
                 rewrite H1''.
                 rewrite nzmap_lookup_total_map_set_ne; try done.
                 rewrite /In'.
                 rewrite outflow_lookup_total_map_set_ne; try done.
            * admit.
            * admit.
          + unfold out at 2. rewrite outflow_map_set_out_map_ne; try done.
            simpl. fold (out (([^op set] x ∈ dom I0, FI I0 x)) n'). 
            admit. }
      assert (In1' = inflow_map_set (λ (_ : K) (x0 : nat), (x0 + 1)%nat) (I !!! n1) n1 Xk) as H0''.
      { rewrite /In1' /In1. try done. }
      assert (✓ (([^op set] y ∈ dom I0, FI I y) ⋅ (FI I n1))) as H0'''.
      { admit. }
      by pose proof Hpose H'' n1_in_In1 H''' H0' H0'' H0''' as Hpose.
    - intros I0 A0 ? n ns -> HA0_n _ _ HInd <-.
      rewrite dom_empty_L. by rewrite !big_opS_empty.
  Admitted.      
        
  Definition extract_inf (x: gset K * option (Node * gset K)) : gset K :=
    x.1.
    
  Lemma flow_upd_inflow I I' A l II' :
    let intf := λ I x, I !!! x in
    (∀ n, n ∈ dom A → 
      (inset _ (intf I' n) n) = (inset _ (intf I n) n) ∪ (extract_inf (A !!! n))) →
      flow_upd_helper I I' A l = II' → 
        (∀ n, n ∈ dom A → 
          (inset _ (intf II' n) n) = (inset _ (intf I n) n) ∪ (extract_inf (A !!! n))).
  Proof.
    intros intf. apply flow_upd_helper_ind.
    - intros ? A0 ? -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> ? HA0_n X_n ? -> (n1, X_n1) -> HInd <-.
      (* Contradiction from Some(n1, X_n1) = None *)
      admit.
    - intros I0 A0 ? n ? -> -> ? HA0_n ? ? -> -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
    - intros I0 A0 ? n ? -> n1' ns -> ? HA0_n X_n opt_n -> (n1, X_n1) ->.
      intros ? ? [= <- <-]. intros In In' In1 In1' II I0' HInd'.
      intros HInd Hflow. apply HInd'; try done.
      intros n0 Hn0. pose proof HInd n0 Hn0 as HInd.
      (* Case analysis on n0 *)
      admit.
      
      
    - intros I0 A0 ? n ? -> n1' ns -> (?, ?) HA0_n X_n ? [= -> ->] -> HInd <-.
      (* Contradiction: only for last element of l should A0 !!! n = (_, None) *)
      (* n is not the last element of l here *)
      admit.
    - intros I0 A0 ? n ? -> n1 ns -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
  Admitted.
    
  Definition extract_outf (x: gset K * option (Node * gset K)) : gset K :=
    match x with
    | (_, None) => ∅
    | (_, Some (_, X)) => X end. 
    
  Lemma flow_upd_outflow I I' A l II' :
    let intf := λ I x, I !!! x in
    (∀ n, n ∈ dom A → 
      (outset _ (intf I' n) n) = (outset _ (intf I n) n) ∪ (extract_outf (A !!! n))) →
      flow_upd_helper I I' A l = II' → 
        (∀ n, n ∈ dom A → 
          (outset _ (intf II' n) n) = (outset _ (intf I n) n) ∪ (extract_outf (A !!! n))).
  Proof.
    intros intf. apply flow_upd_helper_ind.
    - intros ? A0 ? -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> ? HA0_n X_n ? -> (n1, X_n1) -> HInd <-.
      (* Contradiction from Some(n1, X_n1) = None *)
      admit.
    - intros I0 A0 ? n ? -> -> ? HA0_n ? ? -> -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
    - intros I0 A0 ? n ? -> n1' ns -> ? HA0_n X_n opt_n -> (n1, X_n1) ->.
      intros ? ? [= <- <-]. intros In In' In1 In1' II I0' HInd'.
      intros HInd Hflow. apply HInd'; try done.
      intros n0 Hn0. pose proof HInd n0 Hn0 as HInd.
      (* Case analysis on n0 *)
      admit.
      
      
    - intros I0 A0 ? n ? -> n1' ns -> (?, ?) HA0_n X_n ? [= -> ->] -> HInd <-.
      (* Contradiction: only for last element of l should A0 !!! n = (_, None) *)
      (* n is not the last element of l here *)
      admit.
    - intros I0 A0 ? n ? -> n1 ns -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
  Admitted.

  Definition extract_ks (x: gset K * option (Node * gset K)) : gset K :=
    match x with
    | (X, None) => X
    | (X, Some (_, Xk)) => X ∖ Xk end. 

  Lemma flow_upd_keyset I I' A l II' :
    let intf := λ I x, I !!! x in
    (match l with
      | [] => (∀ n, n ∈ dom A → keyset (intf I' n) = extract_ks (A !!! n))
      | [n0] => (∀ n, n ∈ dom A → keyset (intf I' n) = extract_ks (A !!! n))
      | n0 :: ns => 
        (∀ n, n ∈ dom A ∧ n ∉ ns → keyset (intf I' n) = extract_ks (A !!! n)) end) →
      flow_upd_helper I I' A l = II' → 
        (∀ n, n ∈ dom A → keyset (intf II' n) = extract_ks (A !!! n)).
  Proof.
    intros intf. apply flow_upd_helper_ind.
    - intros ? A0 ? -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> ? HA0_n X_n ? -> (n1, X_n1) -> HInd <-.
      (* Contradiction from Some(n1, X_n1) = None *)
      admit.
    - intros I0 A0 ? n ? -> -> ? HA0_n ? ? -> -> HInd ->. done.
    - intros I0 A0 ? n ? -> -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
    - intros I0 A0 ? n ? -> n1' ns -> ? HA0_n X_n opt_n -> (n1, X_n1) ->.
      intros ? ? [= <- <-]. intros In In' In1 In1' II I0' HInd'.
      intros HInd Hflow. apply HInd'; try done.
      destruct ns as [| ?].
      + admit.
      + admit.
      
      
    - intros I0 A0 ? n ? -> n1' ns -> (?, ?) HA0_n X_n ? [= -> ->] -> HInd <-.
      (* Contradiction: only for last element of l should A0 !!! n = (_, None) *)
      (* n is not the last element of l here *)
      admit.
    - intros I0 A0 ? n ? -> n1 ns -> HA0_n HInd <-.
      (* Contradiction from A0 !! n = None *)
      admit.
  Admitted.

  Definition outflow (I: multiset_flowint_ur K) (n: Node) (es: Node * gset K) := 
    ∀ n' k, k ∈ KS → (k ∈ outset K I n' ↔ n' = es.1 ∧ k ∈ es.2 ∧ k ∈ inset K I n).

  Lemma list_marking_flow_upd1 (S: gset Node) (n: Node) (II: gmap Node (multiset_flowint_ur K))
    (es: gmap Node (Node * gset K)) (es': gmap Node (Node * gset K)) (rank: Node -> nat) :
    let I : Node → multiset_flowint_ur K := λ x, II !!! x in 
    n ∈ S →
    ✓ ([^op set] x ∈ S, I x) →
    (∀ x, x ∈ S → domm (I x) = {[ x ]}) →
    (∀ x, x ∈ S → outflow (I x) x (es !!! x)) →
    es' = <[n := ((es !!! n).1, KS) ]> es →
    (∀ n', rank(n') < rank((es !!! n').1)) →
    ∃ (II': gmap Node (multiset_flowint_ur K)),
      let I' : Node → multiset_flowint_ur K := λ x, II' !!! x in
        ✓ ([^op set] x ∈ S, I' x)
      ∧ (∀ x, x ∈ S → domm (I x) = domm (I' x))
      ∧ keyset (I' n) = ∅
      ∧ ∀ n', n' ∈ S → keyset (I n') = ∅ → keyset (I' n') = ∅
      ∧ (∀ x, x ∈ S → outflow (I' x) x (es' !!! x)).
  Proof.
    intros I n_in_S Valid Domm Outf Def_es Rank.
    destruct (decide (keyset (I n) = ∅)).
    - exists II. intros I'.
      subst I I'. split; try done.
      split; try done. split; try done.
      split; try done. split; try done.
    
  Admitted.
  
End list_flow_upd.  

