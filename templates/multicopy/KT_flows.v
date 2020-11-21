Require Import Coq.Numbers.NatInt.NZAddOrder.
From iris.algebra Require Import numbers.
(*From iris.algebra Require Export numbers. *)
Set Default Proof Using "All".
Require Export flows ccm.

Section KT_flows.

(*Definition K := Z. *)
Context `{Countable K}.

Definition KT : Type := (K * nat).

Definition KT_multiset := nzmap KT nat.

Global Instance KT_multiset_ccm : CCM KT_multiset := lift_ccm KT nat.

Definition dom_ms (m : KT_multiset) := dom (gset KT) m.

Definition inset_KT I n := dom (gset KT) (inf I n).

Definition outset_KT I n := dom_ms (out I n).

Definition out_KT I k := ∃ t n, (k, t) ∈ outset_KT I n.

Global Canonical Structure KT_flowint_ur : ucmraT := flowintUR KT_multiset.

Definition gmap_decrement (kt: KT) (m : gmap KT nat) : gmap KT nat := 
          if (1 <? m !!! kt) then <[kt := m !!! kt - 1]> m
          else delete kt m.

Lemma nzmap_decrement_wf (kt: KT) (m : gmap KT nat) :
      nzmap_wf m → nzmap_wf (gmap_decrement kt m).
Proof.
  unfold nzmap_wf, map_Forall. intros Hm.
  intros i x. destruct (decide (i = kt)).
  - replace i. unfold gmap_decrement.
    destruct (1 <? m !!! kt) eqn: Hmkt.
    + rewrite lookup_insert. intros H'; inversion H'.
      apply Nat.ltb_lt in Hmkt. 
      unfold ccmunit, ccm_unit. simpl.
      unfold nat_unit. lia.
    + rewrite lookup_delete.
      intros H'; inversion H'.
  - unfold gmap_decrement. destruct (1 <? m !!! kt);
    [ rewrite lookup_insert_ne; try done | rewrite lookup_delete_ne];
    by pose proof Hm i x.       
Qed.

Definition nzmap_decrement (kt: KT) (m : nzmap KT nat) :=
      let (m, Hm) := m in
        NZMap (gmap_decrement kt m) (bool_decide_pack _ (nzmap_decrement_wf kt m 
    (bool_decide_unpack _ Hm))).
    
Lemma nzmap_lookup_total_decrement kt m :
      nzmap_decrement kt m ! kt = m ! kt - 1.
Proof.
  unfold nzmap_decrement. unfold nzmap_total_lookup.
  destruct m as [mg prf_mg]. 
  unfold lookup, nzmap_lookup.
  unfold gmap_decrement.
  destruct (1 <? mg !!! kt) eqn : Hari.
  - apply Nat.ltb_lt in Hari.
    rewrite lookup_insert. simpl.
    unfold ccmunit, nat_unit.
    destruct (mg !! kt) eqn: Hmg.
    simpl. rewrite /(mg !!! kt).
    unfold finmap_lookup_total.
    rewrite Hmg. by simpl.
    rewrite /(mg !!! kt).
    unfold finmap_lookup_total.
    rewrite Hmg. by simpl.
  - apply Nat.ltb_ge in Hari.
    rewrite lookup_delete. simpl.    
    destruct (mg !! kt) eqn: Hmg.
    simpl. rewrite /(mg !!! kt) in Hari.
    unfold finmap_lookup_total in Hari.
    rewrite Hmg in Hari. simpl in Hari.
    unfold ccmunit, nat_unit. lia.
    simpl. by unfold ccmunit, nat_unit.
Qed.

Lemma nzmap_lookup_total_decrement_ne kt m kt' :
      kt' ≠ kt → nzmap_decrement kt m ! kt' = m ! kt'.
Proof.
  intros Hkt.
  unfold nzmap_decrement. unfold nzmap_total_lookup.
  destruct m as [mg prf_mg]. 
  unfold lookup, nzmap_lookup.
  unfold gmap_decrement.
  destruct (1 <? mg !!! kt) eqn : Hari.
  - rewrite lookup_insert_ne; try done.
  - rewrite lookup_delete_ne; try done.
Qed.

Definition nzmap_increment_set (s: gset KT) (m : nzmap KT nat) : nzmap KT nat :=
      let f := λ kt m', <<[ kt := m ! kt + 1 ]>>m' in
      set_fold f m s.

Lemma nzmap_lookup_total_increment_set_aux s m :
      ∀ kt, (kt ∈ s → nzmap_increment_set s m ! kt = m ! kt + 1)
          ∧ (kt ∉ s → nzmap_increment_set s m ! kt = m ! kt).
Proof.
    set (P := λ (m': nzmap KT nat) (X: gset KT),
                    ∀ x, (x ∈ X → m' ! x = m ! x + 1)
                         ∧ (x ∉ X → m' ! x = m ! x) ).
    apply (set_fold_ind_L P); try done.
    intros x X r Hx HP.
    unfold P in HP. unfold P.
    intros x'.
    destruct (decide (x' = x));
    split; intros Hx'.
    - rewrite e. by rewrite nzmap_lookup_total_insert.
    - assert (x ∈ X). set_solver. contradiction.
    - assert (x' ∈ X) as x'_in_X. set_solver.
      apply HP in x'_in_X.
      rewrite nzmap_lookup_total_insert_ne.
      done. done.
    - assert (x' ∉ X) as x'_nin_X. set_solver.
      apply HP in x'_nin_X.
      rewrite nzmap_lookup_total_insert_ne.
      done. done.
Qed.

Lemma nzmap_lookup_total_increment_set kt s m :
      kt ∈ s → nzmap_increment_set s m ! kt = m ! kt + 1.
Proof.
  apply nzmap_lookup_total_increment_set_aux.
Qed.

Lemma nzmap_lookup_total_increment_set_ne kt s m :
      kt ∉ s → nzmap_increment_set s m ! kt = m ! kt.
Proof.
  apply nzmap_lookup_total_increment_set_aux.
Qed.

Definition nzmap_decrement_set (s: gset KT) (m : nzmap KT nat) : nzmap KT nat :=
      let f := λ kt m', nzmap_decrement kt m' in
      set_fold f m s.

Lemma nzmap_lookup_total_decrement_set_aux kt s m :
    (kt ∈ s → nzmap_decrement_set s m ! kt = m ! kt - 1)
  ∧ (kt ∉ s → nzmap_decrement_set s m ! kt = m ! kt).
Proof.
    set (P := λ (m': nzmap KT nat) (X: gset KT),
                    ∀ x, (x ∈ X → m' ! x = m ! x - 1)
                         ∧ (x ∉ X → m' ! x = m ! x) ).
    apply (set_fold_ind_L P); try done.
    intros x X r Hx HP.
    unfold P in HP. unfold P.
    intros x'.
    destruct (decide (x' = x));
      split; intros Hx'.
    - rewrite e. rewrite nzmap_lookup_total_decrement.
      apply HP in Hx.
      rewrite Hx. trivial.
    - assert (x ∈ X). set_solver. contradiction.
    - assert (x' ∈ X) as x'_in_X. set_solver.
      apply HP in x'_in_X.
      rewrite nzmap_lookup_total_decrement_ne.
      done. done.
    - assert (x' ∉ X) as x'_nin_X. set_solver.
      apply HP in x'_nin_X.
      rewrite nzmap_lookup_total_decrement_ne.
      done. done.
Qed.

Lemma nzmap_lookup_total_decrement_set kt s m :
      kt ∈ s → nzmap_decrement_set s m ! kt = m ! kt - 1.
Proof.
  apply nzmap_lookup_total_decrement_set_aux.
Qed.

Lemma nzmap_lookup_total_decrement_set_ne kt s m :
      kt ∉ s → nzmap_decrement_set s m ! kt = m ! kt.
Proof.
  apply nzmap_lookup_total_decrement_set_aux.
Qed.

Definition outflow_insert_KT (I : KT_flowint_ur) (n: Node) 
                            (k: K) (t: nat) : KT_flowint_ur := 
           let I_out_n := (<<[(k,t) := (out I n) ! (k,t) + 1 ]>> (out I n)) in
           let I'_out := (<<[n := I_out_n]>> (out_map I)) in
           (int {| infR := inf_map I ; outR := I'_out |}).

Definition outflow_delete_KT (I : KT_flowint_ur) (n: Node) 
                            (k: K) (t: nat) :KT_flowint_ur := 
           let I_out_n := (nzmap_decrement (k,t) (out I n)) in
           let I'_out := (<<[n := I_out_n]>> (out_map I)) in
           (int {| infR := inf_map I ; outR := I'_out |}).

Definition outflow_insert_set_KT (I : KT_flowint_ur) (n: Node) 
                            (s: gset KT) : KT_flowint_ur := 
           let I_out_n := (nzmap_increment_set s (out I n)) in
           let I'_out := (<<[n := I_out_n]>> (out_map I)) in
           (int {| infR := inf_map I ; outR := I'_out |}).

Definition outflow_delete_set_KT (I : KT_flowint_ur) (n: Node) 
                            (s: gset KT) :KT_flowint_ur := 
           let I_out_n := (nzmap_decrement_set s (out I n)) in
           let I'_out := (<<[n := I_out_n]>> (out_map I)) in
           (int {| infR := inf_map I ; outR := I'_out |}).

Lemma outflow_insert_outset_ne_KT I n k t I' n' :
      n' ≠ n → I' = outflow_insert_KT I n k t
             → outset_KT I' n' = outset_KT I n'.
Proof.
  intros Hneq HeqI. unfold outset_KT.
  unfold KT_flows.dom_ms.
  replace I'. unfold outflow_insert_KT.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert_ne; try done.
Qed.  

Lemma outflow_insert_outset_KT I n k t I' :
      I' = outflow_insert_KT I n k t → 
           outset_KT I' n = (outset_KT I n) ∪ {[(k,t)]}.
Proof.
  intros Heq. unfold outset_KT.
  unfold KT_flows.dom_ms.
  replace I'. unfold outflow_insert_KT.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert.
  apply leibniz_equiv.
  rewrite nzmap_dom_insert_nonzero.
  - set_solver.
  - unfold ccmunit, ccm_unit. simpl.
    unfold nat_unit. lia.
Qed.

Lemma outflow_insert_set_outset_KT I n S I' :
      I' = outflow_insert_set_KT I n S → 
           outset_KT I' n = (outset_KT I n) ∪ S.
Proof.
  intros Heq. unfold outset_KT.
  unfold KT_flows.dom_ms.
  replace I'. unfold outflow_insert_set_KT.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert.
  apply leibniz_equiv.
  apply elem_of_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - set_solver.
  - rewrite nzmap_lookup_total_increment_set.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    unfold ccmunit, ccm_unit. simpl.
    unfold nat_unit. lia. done.
  - rewrite nzmap_lookup_total_increment_set_ne.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    intro.
    left.
    trivial. trivial.
  - rewrite elem_of_union.
    intro.
    destruct H0.
    rewrite nzmap_lookup_total_increment_set_ne.
    rewrite nzmap_elem_of_dom_total in H0 *.
    trivial. trivial.
    contradiction.
Qed.

Lemma outflow_insert_set_outset_ne_KT I n S I' n' :
      n' ≠ n → I' = outflow_insert_set_KT I n S → 
           outset_KT I' n' = outset_KT I n'.
Proof.
  intros Hneq Heq. unfold outset_KT.
  unfold KT_flows.dom_ms.
  replace I'. unfold outflow_insert_set_KT.
  unfold out. simpl.
  apply leibniz_equiv.
  apply elem_of_equiv. intros x.
  rewrite !nzmap_elem_of_dom_total.
  rewrite nzmap_lookup_total_insert_ne.
  trivial. auto.
Qed.

Lemma outflow_insert_set_lookup_out_KT I n S I' kt :
      kt ∈ S → I' = outflow_insert_set_KT I n S →
          out I' n ! kt = out I n ! kt + 1.
Proof.
  intros Hneq Heq. unfold outset_KT.
  replace I'. unfold outflow_insert_set_KT.
  unfold out. simpl.
  apply leibniz_equiv.
  rewrite nzmap_lookup_total_insert.
  rewrite nzmap_lookup_total_increment_set.
  trivial. trivial.
Qed.

Lemma outflow_insert_set_lookup_out_ne_KT I n S I' kt :
      kt ∉ S → I' = outflow_insert_set_KT I n S →
          out I' n ! kt = out I n ! kt.
Proof.
  intros Hneq Heq. unfold outset_KT.
  replace I'. unfold outflow_insert_set_KT.
  unfold out. simpl.
  apply leibniz_equiv.
  rewrite nzmap_lookup_total_insert.
  rewrite nzmap_lookup_total_increment_set_ne.
  trivial. trivial.
Qed.


Lemma outflow_delete_outset_ne_KT I n k t I' n' :
      n' ≠ n → I' = outflow_delete_KT I n k t
             → outset_KT I' n' = outset_KT I n'.
Proof.
  intros Hneq HeqI. unfold outset_KT.
  unfold KT_flows.dom_ms.
  replace I'. unfold out. simpl.
  rewrite nzmap_lookup_total_insert_ne; try done.
Qed.  

Lemma outflow_delete_outset_KT I n k t I' :
      I' = outflow_delete_KT I n k t → 
         ((out I n ! (k,t) ≤ 1 → outset_KT I' n = (outset_KT I n) ∖ {[(k,t)]})
          ∧ (1 < out I n ! (k,t) → outset_KT I' n = outset_KT I n)).
Proof.
  intros Heq. unfold outset_KT.
  unfold KT_flows.dom_ms.
  replace I'. unfold outflow_delete_KT.
  unfold out. simpl. 
  rewrite nzmap_lookup_total_insert.
  unfold nzmap_decrement.
  destruct (out_map I ! n) as [og prf_og] eqn:Ho.
  unfold dom, nzmap_dom. simpl.
  unfold gmap_decrement.
  split.
  - intros le_1.
    unfold nzmap_total_lookup, lookup, nzmap_lookup in le_1.
    destruct (1 <? og !!! (k, t)) eqn: Hog.
    + apply Nat.ltb_lt in Hog.
      rewrite /(og !!! (k, t)) in Hog.
      unfold finmap_lookup_total in Hog.
      unfold inhabitant in Hog.
      simpl in Hog.
      unfold ccmunit, ccm_unit in le_1. 
      simpl in le_1. unfold nat_unit in le_1.
      assert (∀ (x: nat), x ≤ 1 → x > 1 → False) as H'. lia. 
      exfalso. apply (H' (default 0 (og !! (k,t)))); try done.
    + rewrite Hog. apply Nat.ltb_ge in Hog.      
      apply leibniz_equiv. by rewrite dom_delete.
  - intros ge_1.
    unfold nzmap_total_lookup, lookup, nzmap_lookup in ge_1.
    assert (1 <? og !!! (k,t) = true) as H'.
    { apply PeanoNat.Nat.ltb_lt. 
      rewrite /(og !!! (k, t)).
      unfold finmap_lookup_total.
      unfold inhabitant. simpl.
      unfold ccmunit, ccm_unit in ge_1; simpl in ge_1.
      by unfold nat_unit in ge_1. }
    rewrite H'. apply leibniz_equiv.
    rewrite dom_insert.
    assert ((k,t) ∈ dom (gset KT) og).
    { rewrite elem_of_dom. destruct (og !! (k,t)) eqn: Hogkt.
      unfold is_Some; exists n0; try done. rewrite Hogkt in ge_1.
      unfold ccmunit, ccm_unit in ge_1; simpl in ge_1.
      unfold nat_unit in ge_1; lia. }
    set_solver.
Qed.      

(* assumes: n ∈ domm I *) 
Definition inflow_insert_KT (I : KT_flowint_ur) (n: Node) 
                            (k: K) (t: nat) :KT_flowint_ur := 
           let I_inf_n := (<<[(k,t) := (inf I n) ! (k,t) + 1 ]>> (inf I n)) in
           let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
           (int {| infR := I'_inf ; outR := out_map I |}).

(* assumes: n ∈ domm I *)
Definition inflow_delete_KT (I : KT_flowint_ur) (n: Node) 
                            (k: K) (t: nat) :KT_flowint_ur := 
           let I_inf_n := (nzmap_decrement (k,t) (inf I n)) in
           let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
           (int {| infR := I'_inf ; outR := out_map I |}).

(* assumes: n ∈ domm I *) 
Definition inflow_insert_set_KT (I : KT_flowint_ur) (n: Node) 
                            (s: gset KT) :KT_flowint_ur := 
           let I_inf_n := (nzmap_increment_set s (inf I n)) in
           let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
           (int {| infR := I'_inf ; outR := out_map I |}).

(* assumes: n ∈ domm I *)
Definition inflow_delete_set_KT (I : KT_flowint_ur) (n: Node) 
                            (s: gset KT) :KT_flowint_ur := 
           let I_inf_n := (nzmap_decrement_set s (inf I n)) in
           let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
           (int {| infR := I'_inf ; outR := out_map I |}).


Lemma inflow_insert_inset_ne_KT I n k t I' n' :
      n' ≠ n → I' = inflow_insert_KT I n k t → 
                inset_KT I' n' = inset_KT I n'.
Proof.
  intros Hneq Heq. unfold inset_KT.
  unfold inf at 1. replace I'. 
  unfold inflow_insert_KT. simpl.
  rewrite lookup_insert_ne; try done.
Qed.

Lemma inflow_insert_inset_KT I n k t I' :
      I' = inflow_insert_KT I n k t → 
            inset_KT I' n = (inset_KT I n) ∪ {[(k,t)]}.
Proof.
  intros Heq. unfold inset_KT.
  unfold inf at 1. replace I'. 
  unfold inflow_insert_KT. simpl.
  rewrite lookup_insert. 
  apply leibniz_equiv. simpl.
  destruct (decide (inf I n ! (k, t) + 1 = 0)); try lia.
  rewrite nzmap_dom_insert_nonzero; try done.
  set_solver.
Qed.

Lemma inflow_delete_inset_ne_KT I n k t I' n' :
      n' ≠ n → I' = inflow_delete_KT I n k t → 
            inset_KT I' n' = inset_KT I n'.
Proof.
  intros Hneq Heq. unfold inset_KT.
  unfold inf at 1. replace I'. 
  unfold inflow_delete_KT. simpl. 
  rewrite lookup_insert_ne; try done.
Qed.

Lemma inflow_delete_inset_KT I n k t I' :
      I' = inflow_delete_KT I n k t → 
          ((inf I n ! (k,t) ≤ 1 → inset_KT I' n = (inset_KT I n) ∖ {[(k,t)]})
          ∧ (inf I n ! (k,t) > 1 → inset_KT I' n = inset_KT I n)).
Proof.
  intros Heq. unfold inset_KT.
  replace I'. split.
  - intros le_1. unfold inflow_delete_KT.
    unfold inf, inf_map at 1. simpl.
    rewrite lookup_insert. simpl.
    unfold nzmap_decrement.
    destruct (inf_map I !! n) as [i | ] eqn:Hinf.
    + simpl. destruct i as [ig prf_ig].
      unfold dom, nzmap_dom. simpl.
      unfold gmap_decrement.
      rewrite /(inf I n ! (k, t)) in le_1.
      unfold finmap_lookup_total in le_1.
      unfold ccmunit, ccm_unit in le_1. 
      simpl in le_1. unfold nat_unit in le_1.
      unfold inf in le_1.
      rewrite Hinf in le_1.
      simpl in le_1.
      assert (1 <? ig !!! (k,t) = false) as H'.
      { apply PeanoNat.Nat.ltb_ge. 
        rewrite /(ig !!! (k,t)).
        unfold finmap_lookup_total.
        unfold inhabitant. by simpl. }
      rewrite H'. apply leibniz_equiv.
      by rewrite dom_delete.
    + simpl. unfold gmap_decrement.
      unfold nzmap_dom. simpl.
      assert (1 <? (∅: gmap KT nat) !!! (k, t) = false) as H'.
      { apply PeanoNat.Nat.ltb_ge.
        rewrite /(∅ !!! (k, t)). 
        unfold finmap_lookup_total. 
        unfold inhabitant. simpl.
        rewrite lookup_empty. simpl. lia. }
      rewrite H'. apply leibniz_equiv.
      by rewrite dom_delete.
  - intros ge_1. unfold inflow_delete_KT.
    unfold inf at 1, inf_map at 1. simpl.
    rewrite lookup_insert. simpl.
    unfold nzmap_decrement. 
    destruct (inf I n) as [i prf_i] eqn: Hi.
    unfold dom, nzmap_dom. simpl.
    unfold gmap_decrement. 
    rewrite <-Hi in ge_1. 
    assert (1 <? i !!! (k,t) = true) as H'. 
    { apply PeanoNat.Nat.ltb_lt.
      unfold nzmap_total_lookup in ge_1.
      rewrite /(inf I n !! (k, t)) in ge_1.
      unfold nzmap_lookup in ge_1.
      rewrite Hi in ge_1.
      rewrite /(i !!! (k, t)).
      unfold finmap_lookup_total.
      unfold inhabitant. by simpl. }
    rewrite H'. apply leibniz_equiv.
    rewrite dom_insert.
    assert ((k,t) ∈ dom (gset KT) i).
    { rewrite elem_of_dom.
      unfold nzmap_total_lookup in ge_1.
      rewrite /(inf I n !! (k, t)) in ge_1.
      unfold nzmap_lookup in ge_1.
      rewrite Hi in ge_1.
      destruct (i !! (k,t)) eqn: H''.
      exists n0; try done. rewrite H'' in ge_1.
      unfold ccmunit, ccm_unit in ge_1. 
      simpl in ge_1. unfold nat_unit in ge_1. lia. }
    set_solver.         
Qed.

Lemma inflow_insert_domm I n k t I' : 
      I' = inflow_insert_KT I n k t → domm I' = domm I ∪ {[n]}.
Proof.
  intros Heq. unfold domm, dom, flowint_dom.
  apply leibniz_equiv. apply elem_of_equiv.
  intros n'. rewrite elem_of_union.
  rewrite !elem_of_dom.
  replace I'. unfold inflow_insert_KT. simpl.
  destruct (decide (n' = n)). 
  - replace n'. rewrite lookup_insert.
    split. intros H'. right. set_solver.
    intros H'. unfold is_Some.
    by exists <<[ (k, t) := inf I n ! (k, t) + 1 ]>> (inf I n).
  - rewrite lookup_insert_ne; try done.
    split. intros; left; try done.
    intros [H' | H']; try done.
    assert (n' = n) by set_solver.
    contradiction.      
Qed.

Lemma inflow_delete_domm I n k t I' : 
      I' = inflow_delete_KT I n k t → domm I' = domm I ∪ {[n]}.
Proof.
  intros Heq. unfold domm, dom, flowint_dom.
  apply leibniz_equiv. apply elem_of_equiv.
  intros n'. rewrite elem_of_union.
  rewrite !elem_of_dom.
  replace I'. unfold inflow_delete_KT. simpl.
  destruct (decide (n' = n)). 
  - replace n'. rewrite lookup_insert.
    split. intros H'. right. set_solver.
    intros H'. unfold is_Some.
    by exists (nzmap_decrement (k, t) (inf I n)).
  - rewrite lookup_insert_ne; try done.
    split. intros; left; try done.
    intros [H' | H']; try done.
    assert (n' = n) by set_solver.
    contradiction.
Qed.

Lemma flowint_delete_infComp_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → 
        1 ≤ out I1 n ! (k,t)   →
          out I1 n ! (k,t) ≤ inf I2 n ! (k,t)  → 
            I1' = outflow_delete_KT I1 n k t →
              I2' = inflow_delete_KT I2 n k t →
                infComp I1 I2 = infComp I1' I2'.
Proof.
  intros n_in_I2 kt_outI1 I2_ge_I1 Hi1 Hi2. apply map_eq. intros n'.
  unfold infComp. rewrite !gmap_imerge_prf.
  unfold infComp_op.
  destruct (decide (n' = n)).
  - replace n'.
    assert (inf_map I1 !! n = inf_map I1' !! n) as Hin_eq.
    { replace I1'. unfold inf_map. by simpl. }
    assert (out I2 n = out I2' n) as Hon_eq.
    { replace I2'. unfold inflow_delete_KT.
      unfold out, out_map. by simpl. }  
    destruct (inf_map I1 !! n) as [i1 | ] eqn: Hi1n.
    + rewrite Hon_eq.
      destruct (inf_map I1' !! n); by inversion Hin_eq.
    + destruct (inf_map I1' !! n); inversion Hin_eq.
      destruct (inf_map I2 !! n) as [i2 | ] eqn: Hi2n.
      * replace I2'. simpl. rewrite lookup_insert.
        unfold inf. rewrite Hi2n. simpl.
        replace I1'. unfold outflow_delete_KT. 
        unfold out, out_map at 2. simpl.
        rewrite nzmap_lookup_total_insert.
        apply f_equal. unfold ccmop_inv, ccm_opinv.
        simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv.
        simpl. unfold nat_opinv.
        apply nzmap_eq. intros [k' t'].
        rewrite !nzmap_lookup_merge.
        destruct (decide ((k,t) = (k', t'))).
        ** inversion e0. replace k'. replace t'.
           rewrite !nzmap_lookup_total_decrement.
           assert (∀ (x y: nat), 1 ≤ x → 1 ≤ y → y ≤ x 
                            → x - y = x - 1 - (y - 1)) as Heq. lia.
           assert (1 ≤ (out_map I1 ! n) ! (k,t)). 
           { by unfold out in kt_outI1. }
           assert (1 ≤ i2 ! (k,t)). 
           { unfold inf in I2_ge_I1. rewrite Hi2n in I2_ge_I1. 
             simpl in I2_ge_I1. lia. }
           apply Heq; try done.
           unfold inf in I2_ge_I1. rewrite Hi2n in I2_ge_I1. 
           by simpl in I2_ge_I1.
        ** rewrite !nzmap_lookup_total_decrement_ne; try done.
      * unfold domm, dom, flowint_dom in n_in_I2.
        rewrite elem_of_dom in n_in_I2 *; intros n_in_I2.
        rewrite Hi2n in n_in_I2. exfalso. 
        destruct n_in_I2 as [x n_in_I2]. 
        inversion n_in_I2. 
  - assert (inf_map I1 !! n' = inf_map I1' !! n') as Eq1.
    { replace I1'. unfold outflow_delete_KT.
      unfold inf_map at 2. by simpl. }
    assert (out I2 n' = out I2' n') as Eq2.
    { replace I2'. unfold inflow_delete_KT. 
      unfold out, out_map at 2. by simpl. }
    assert (inf_map I2 !! n' = inf_map I2' !! n') as Eq3. 
    { replace I2'. unfold inflow_delete_KT.
      unfold inf_map at 2. simpl.
      rewrite lookup_insert_ne; try done. }
    assert (out I1 n' = out I1' n') as Eq4.
    { replace I1'. unfold outflow_delete_KT.
      unfold out, out_map at 2. simpl.
      rewrite nzmap_lookup_total_insert_ne; try done. }
    by rewrite Eq1 Eq2 Eq3 Eq4.       
Qed.

Lemma flowint_delete_outComp_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → 
        I1' = outflow_delete_KT I1 n k t →
          I2' = inflow_delete_KT I2 n k t →
            outComp I1 I2 = outComp I1' I2'.
Proof.
  intros n_in_I2 Hi1 Hi2. apply nzmap_eq. intros n'.
  unfold outComp. rewrite !nzmap_lookup_imerge.
  unfold outComp_op.
  pose proof (inflow_delete_domm I2 n k t I2' Hi2) as domm_2.
  destruct (decide (n' = n)).
  - replace n'.
    assert (n ∈ domm I2') as n_in_I2' by set_solver.
    destruct (decide (n ∈ domm I1 ∪ domm I2)); 
    last by set_solver.
    by destruct (decide (n ∈ domm I1' ∪ domm I2')); 
    last by set_solver.
  - destruct (decide (n' ∈ domm I1 ∪ domm I2)).
    + assert (n' ∈ domm I1' ∪ domm I2') as n'_in_I12' by set_solver.
      by destruct (decide (n' ∈ domm I1' ∪ domm I2')); last by set_solver.
    + assert (n' ∉ domm I1' ∪ domm I2') as n_notin_I12' by set_solver.
      destruct (decide (n' ∈ domm I1' ∪ domm I2')); first by set_solver.
      unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
      simpl. apply nzmap_eq. intros kt'.
      rewrite !nzmap_lookup_merge. unfold nat_op.
      replace I1'. unfold outflow_delete_KT. unfold out_map at 3.
      simpl. rewrite nzmap_lookup_total_insert_ne; try done.
      replace I2'. unfold inflow_delete_KT. unfold out_map at 4.
      by simpl. 
Qed.

Lemma outflow_delete_valid_KT I1 I1' n k t :
      I1' = outflow_delete_KT I1 n k t →
          ✓ I1 → ✓ I1'.
Proof.
  intros Hi1_eq Valid1.
  unfold valid, flowint_valid.
  replace I1'. unfold outflow_delete_KT.
  simpl.
  unfold nzmap_insert.
  destruct (decide (nzmap_decrement (k, t) (out I1 n) = 0%CCM)).
  - destruct (I1) as [ [i o] | ] eqn: Hi1; [| exfalso; try done].
    simpl. unfold nzmap_delete.
    destruct o as [og prf_og] eqn: Hog.
    simpl. repeat split.
    + unfold valid, flowint_valid in Valid1. 
      simpl in Valid1. 
      destruct Valid1 as [H' _].
      rewrite map_disjoint_spec in H' *; intros H'.
      rewrite map_disjoint_spec.
      intros n' mi mo Hmi Hmo.
      destruct (decide (n' = n)).
      * subst n'. rewrite lookup_delete in Hmo.
        inversion Hmo.
      * rewrite lookup_delete_ne in Hmo; try done.
        by pose proof H' n' mi mo Hmi Hmo.
   + intros Hi0. apply nzmap_eq. intros n'.
     unfold nzmap_total_lookup at 1, lookup at 1.
     unfold nzmap_lookup.
     destruct (decide (n' = n)).
     * subst n'.
       rewrite lookup_delete. simpl.
       by rewrite nzmap_lookup_empty.
     * rewrite lookup_delete_ne; try done.
       unfold valid, flowint_valid in Valid1. 
       simpl in Valid1. 
       destruct Valid1 as [_ H'].
       pose proof H' Hi0 as H'.
       rewrite nzmap_eq in H' *; intros H'.
       pose proof H' n' as H'.
       by unfold nzmap_total_lookup at 1, lookup at 1,
            nzmap_lookup at 1 in H'.
  - destruct (I1) as [ [i o] | ] eqn: Hi1; [| exfalso; try done].
    simpl. unfold out, out_map. simpl.                
    destruct o as [og prf_og] eqn: Hog.
    simpl. split.
    + unfold valid, flowint_valid in Valid1. 
      simpl in Valid1. 
      destruct Valid1 as [H' _].
      rewrite map_disjoint_spec in H' *; intros H'.
      rewrite map_disjoint_spec.
      intros n' mi mo Hmi Hmo.
      destruct (decide (n' = n)).
      * subst n'. rewrite lookup_insert in Hmo.
        inversion Hmo. rewrite <-Hog in H1.
        clear Hmo. rename H1 into Hmo. 
        unfold nzmap_decrement in Hmo.
        destruct (o !! n) as [ogn | ] eqn: Hon.
        ** rewrite Hog in Hon. 
           unfold lookup, nzmap_lookup in Hon.
           apply (H' n mi ogn); try done.
        ** unfold out, out_map in n0. simpl in n0.    
           rewrite <-Hog in n0. unfold nzmap_total_lookup in n0.
           rewrite Hon in n0. simpl in n0.
           unfold ccmunit, lift_unit in n0.
           rewrite nzmap_empty_lookup in n0 *; intros n0.
           destruct n0 as [kt' n0].
           unfold ccmunit, ccm_unit in n0. simpl in n0.
           unfold nat_unit in n0.
           unfold nzmap_total_lookup in n0.
           unfold lookup, nzmap_lookup in n0.
           unfold gmap_decrement in n0.
           assert ((∅: gmap KT nat) !!! (k,t) = 0) as H''.
           { unfold lookup_total, finmap_lookup_total.
             rewrite lookup_empty. by simpl. }
           rewrite H'' in n0.
           destruct (1 <? 0) eqn: Harith.
           apply Nat.ltb_lt in Harith. lia.
           destruct (decide (kt' = (k,t))). 
           subst kt'. rewrite lookup_delete in n0. simpl in n0.
           unfold ccmunit, nat_unit in n0. done. 
           rewrite lookup_delete_ne in n0; try done. 
      * rewrite lookup_insert_ne in Hmo; try done.
        by pose proof H' n' mi mo Hmi Hmo.
    + intros Hi0. apply nzmap_eq. intros n'.             
      unfold valid, flowint_valid in Valid1.
      destruct Valid1 as [_ H'].
      simpl in H'. pose proof H' Hi0 as H'.
      rewrite <-Hog in H'.
      unfold nzmap_total_lookup at 1, lookup at 1.
      unfold nzmap_lookup.
      destruct (decide (n' = n)).
      * subst n'. rewrite lookup_insert.
        simpl. rewrite <-Hog.
        rewrite nzmap_lookup_empty.
        apply nzmap_eq. intros kt'.
        rewrite H'.
        unfold ccmunit, ccm_unit. simpl.
        unfold lift_unit.
        rewrite nzmap_lookup_empty.
        unfold ccmunit, ccm_unit. simpl.
        unfold nat_unit. unfold nzmap_total_lookup.
        unfold lookup, nzmap_lookup.
        unfold gmap_decrement.
        assert ((∅: gmap KT nat) !!! (k,t) = 0) as H''.
        { unfold lookup_total, finmap_lookup_total.
          rewrite lookup_empty. by simpl. }
        rewrite H''.
        destruct (1 <? 0) eqn: Harith.
        apply Nat.ltb_lt in Harith. lia.
        destruct (decide (kt' = (k,t))). 
        replace kt'. rewrite lookup_delete.
        by simpl. rewrite lookup_delete_ne; try done.
      * rewrite lookup_insert_ne; try done.
        rewrite nzmap_eq in H' *; intros H'.
        pose proof H' n' as H'.
        unfold nzmap_total_lookup at 1 in H'.
        rewrite Hog in H'. 
        by unfold lookup at 1, nzmap_lookup at 1 in H'.
Qed.

Lemma inflow_delete_valid_KT I1 I1' n k t :
      n ∈ domm I1 →
        I1' = inflow_delete_KT I1 n k t →
          ✓ I1 → ✓ I1'.
Proof.
  intros n_domm Hi1_eq Valid1.
  unfold valid, flowint_valid.
  replace I1'. unfold inflow_delete_KT. 
  destruct (I1) as [ [i o] | ] eqn: Hi1; [| exfalso; try done].
  unfold valid, flowint_valid in Valid1. 
  simpl in Valid1. 
  simpl. split.
  - apply map_disjoint_dom.
    simpl.
    destruct Valid1 as [H' _].
    apply map_disjoint_dom in H'. rewrite <-Hi1 in Hi1_eq.
    pose proof (inflow_delete_domm I1 n k t I1' Hi1_eq) as Hdomm.
    rewrite <-Hi1 in n_domm.
    assert (domm I1' = domm I1) as H'' by set_solver.
    unfold domm, dom, flowint_dom in H''.
    replace I1' in H''. unfold inflow_delete_KT in H''.
    simpl in H''. rewrite Hi1 in H''. simpl in H''.
    rewrite <-Hi1 in H''. apply leibniz_equiv_iff in H''.
    rewrite (dom_insert i) in H'' *; intros H''.
    unfold domm, dom, flowint_dom in n_domm.
    replace I1 in n_domm. simpl in n_domm.
    rewrite dom_insert. set_solver.
  - intros Hi. destruct Valid1 as [_ H'].
    apply nzmap_eq. intros n'.
    rewrite <-Hi1 in Hi. 
    assert (<[n:=nzmap_decrement (k, t) (inf I1 n)]> i !! n = None) as H''.
    { rewrite Hi. by rewrite lookup_empty. }
    rewrite lookup_insert in H''.
    inversion H''.
Qed.    

Lemma flowint_delete_intComposable_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → 
        out I1 n ! (k,t) ≤ inf I2 n ! (k,t) →
          I1' = outflow_delete_KT I1 n k t →
            I2' = inflow_delete_KT I2 n k t →
              intComposable I1 I2 → 
                intComposable I1' I2'.
Proof.
  intros n_in_I2 I2_ge_I1 Hi1 Hi2 Intcomp. unfold intComposable.
  repeat split.
  - apply (outflow_delete_valid_KT I1 I1' n k t); try done.
    by destruct Intcomp as [H' _].
  - apply (inflow_delete_valid_KT I2 I2' n k t); try done.
    by destruct Intcomp as [_ [H' _]].
  - pose proof (inflow_delete_domm I2 n k t I2' Hi2) as domm_2.
    assert (domm I1' = domm I1) as domm_1. 
    { unfold domm, dom, flowint_dom. replace I1'.
      unfold outflow_delete_KT. unfold inf_map. by simpl. }
    destruct Intcomp as [_ [_ [H' _]]].
    set_solver.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros kt'.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    assert (inf_map I1' = inf_map I1) as Hinf_1.
    { replace I1'. unfold outflow_delete_KT.
      unfold inf_map. by simpl. }
    rewrite Hinf_1 in Hin'.
    destruct Intcomp as [_ [_ [_ [H' _]]]].
    unfold map_Forall in H'. pose proof H' n' m Hin' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. rewrite nzmap_eq in H' *; intros H'.
    pose proof H' kt' as H'. rewrite !nzmap_lookup_merge in H'.
    unfold nat_op, nat_opinv in H'.
    assert (out I2' n' = out I2 n') as Hout.
    { replace I2'. unfold inflow_delete_KT.
      unfold out, out_map. by simpl. }
    rewrite Hout. unfold inf. unfold inf in H'.
    by rewrite Hinf_1.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros kt'.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    destruct Intcomp as [_ [_ [_ [_ H']]]].
    unfold map_Forall in H'. pose proof H' n' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. destruct (decide (n' = n)). 
    + replace n'. replace I1'. unfold outflow_delete_KT.
      unfold out at 1, out_map at 1. simpl.
      unfold out at 2, out_map at 2. simpl.
      rewrite !nzmap_lookup_total_insert.
      destruct (decide (kt' = (k,t))).
      * replace kt'. rewrite nzmap_lookup_total_decrement.
        replace I2' in Hin'. unfold inflow_delete_KT in Hin'.
        unfold inf_map at 1 in Hin'. simpl in Hin'.
        rewrite e in Hin'. rewrite lookup_insert in Hin'.
        inversion Hin'. rewrite nzmap_lookup_total_decrement.
        replace I2'. unfold inflow_delete_KT.
        unfold inf at 2. unfold inf_map at 1. simpl.
        rewrite lookup_insert. simpl.
        rewrite nzmap_lookup_total_decrement.
        assert (∀ (x y: nat), x >= y →
            x - 1 = y - 1 + (x - 1 - (y - 1))) as Heq. lia.
        apply Heq; try done.
      * unfold inf. rewrite e in Hin'. rewrite Hin'. simpl.
        replace I2' in Hin'. unfold inflow_delete_KT in Hin'. 
        unfold inf_map at 1 in Hin'. simpl in Hin'. 
        rewrite lookup_insert in Hin'. inversion Hin'.
        rename H1 into Hin2.
        rewrite !nzmap_lookup_total_decrement_ne; try done.
        rewrite e in H'.
        assert (inf_map I2 !! n = Some (inf I2 n)) as H''.
        { unfold inf. destruct (inf_map I2 !! n) eqn: Hi2n.
          by simpl. unfold domm, dom, flowint_dom in n_in_I2.
          rewrite elem_of_dom in n_in_I2 *; intros n_in_I2.
          rewrite Hi2n in n_in_I2. 
          destruct n_in_I2 as [x Hx]; inversion Hx. } 
        pose proof H' (inf I2 n) H'' as Heq.
        rewrite nzmap_eq in Heq *; intros Heq.
        pose proof Heq kt' as Heq. 
        rewrite !nzmap_lookup_merge in Heq.
        by unfold nat_op, nat_opinv in Heq.
    + assert (inf I2' n' = inf I2 n') as Hin. 
      { replace I2'. unfold inflow_delete_KT.
      unfold inf at 1, inf_map at 1. simpl.
      rewrite lookup_insert_ne; try done. }
      rewrite Hin. replace I2' in Hin'. 
      unfold inflow_delete_KT in Hin'.
      unfold inf at 1, inf_map at 1 in Hin'. simpl in Hin'.
      rewrite lookup_insert_ne in Hin'; try done. 
      pose proof H' m Hin' as H'.
      rewrite nzmap_eq in H' *; intros H'.
      pose proof H' kt' as H'.
      rewrite !nzmap_lookup_merge in H'.
      unfold nat_op, nat_opinv in H'.
      assert (out I1' n' = out I1 n') as Hout.
      { replace I1'. unfold outflow_delete_KT.
        unfold out at 1, out_map at 1. simpl.
        rewrite nzmap_lookup_total_insert_ne; try done. }
      by rewrite Hout.  
Qed.

Lemma flowint_delete_valid_KT I1 I1' I2 I2' n k t :
        n ∈ domm I2 →
          I1' = outflow_delete_KT I1 n k t →
            I2' = inflow_delete_KT I2 n k t →
              ✓ (I1 ⋅ I2) → ✓ (I1' ⋅ I2').
Proof.
  intros n_in_I2 Hi1 Hi2 Valid_12.
  pose proof intComposable_valid I1 I2 Valid_12 as Intcomp_12.
  apply intValid_composable. 
  apply (flowint_delete_intComposable_KT I1 I1' I2 I2' n k t); try done.
  pose proof intComp_unfold_inf_2 I1 I2 Valid_12 n n_in_I2 as H'.
  unfold ccmop, ccm_op in H'. simpl in H'.
  unfold lift_op, ccmop, ccm_op in H'. simpl in H'.
  rewrite nzmap_eq in H' *; intros H'.
  pose proof H' (k,t) as H'. unfold nat_op in H'.
  rewrite nzmap_lookup_merge in H'. 
  rewrite H'.
  assert (∀ (x y: nat), x ≤ y + x) as Heq by lia.
  apply Heq.
Qed.


Lemma flowint_delete_eq_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → 
        1 ≤ out I1 n ! (k, t) →
          I1' = outflow_delete_KT I1 n k t →
            I2' = inflow_delete_KT I2 n k t →
              ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  intros n_in_I2 Hout1 Hi1 Hi2 Valid_12.
  pose proof (intComposable_valid _ _ Valid_12) as HintComp.
  pose proof (flowint_delete_valid_KT I1 I1' I2 I2' n k t 
                      n_in_I2 Hi1 Hi2 Valid_12) as Valid_12'.
  pose proof (intComposable_valid _ _ Valid_12') as HintComp'.   
  destruct (I1⋅I2) as [ [i o] | ] eqn: Hi12; [| exfalso; try done].
  unfold op, intComp in Hi12.
  destruct (decide (intComposable I1 I2)); last done.
  inversion Hi12.
  destruct (I1'⋅I2') as [ [i' o'] | ] eqn: Hi12'; [| exfalso; try done].    
  unfold op, intComp in Hi12'.
  destruct (decide (intComposable I1' I2')); last done.
  inversion Hi12'.
  apply intValid_composable in HintComp.
  assert (infComp I1 I2 = infComp I1' I2') as Hinfcomp.
  { apply (flowint_delete_infComp_KT I1 I1' I2 I2' n k t); try done.
    pose proof intComp_unfold_inf_2 I1 I2 HintComp n n_in_I2 as H'.
    unfold ccmop, ccm_op in H'. simpl in H'.
    unfold lift_op, ccmop, ccm_op in H'. simpl in H'.
    rewrite nzmap_eq in H' *; intros H'.
    pose proof H' (k,t) as H'. unfold nat_op in H'.
    rewrite nzmap_lookup_merge in H'. 
    rewrite H'.
    assert (∀ (x y: nat), x ≤ y + x) as Heq by lia.
    apply Heq. }
  pose proof (flowint_delete_outComp_KT I1 I1' I2 I2' n k t n_in_I2 Hi1 Hi2) 
                                      as Houtcomp.
  by rewrite Hinfcomp Houtcomp.
Qed.

Lemma flowint_insert_infComp_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → 
          out I1 n ! (k,t) ≤ inf I2 n ! (k,t)  → 
            I1' = outflow_insert_KT I1 n k t →
              I2' = inflow_insert_KT I2 n k t →
                infComp I1 I2 = infComp I1' I2'.
Proof.
  intros n_in_I2 I2_ge_I1 Hi1 Hi2. apply map_eq.
  intros n'. unfold infComp. rewrite !gmap_imerge_prf.
  unfold infComp_op.
  destruct (decide (n' = n)).
  - replace n'.
    assert (inf_map I1 !! n = inf_map I1' !! n) as Hin_eq.
    { replace I1'. unfold inf_map. by simpl. }
    assert (out I2 n = out I2' n) as Hon_eq.
    { replace I2'. unfold inflow_delete_KT.
      unfold out, out_map. by simpl. }  
    destruct (inf_map I1 !! n) as [i1 | ] eqn: Hi1n.
    + rewrite Hon_eq.
      destruct (inf_map I1' !! n); by inversion Hin_eq.
    + destruct (inf_map I1' !! n); inversion Hin_eq.
      destruct (inf_map I2 !! n) as [i2 | ] eqn: Hi2n.
      * replace I2'. simpl. rewrite lookup_insert.
        apply f_equal.
        unfold inf. rewrite Hi2n. simpl.
        replace I1'. unfold outflow_insert_KT. 
        unfold out, out_map at 2. simpl.
        rewrite nzmap_lookup_total_insert.
        unfold ccmop_inv, ccm_opinv.
        simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv.
        simpl. unfold nat_opinv.
        apply nzmap_eq. intros [k' t'].
        rewrite !nzmap_lookup_merge.
        destruct (decide ((k,t) = (k', t'))).
        ** inversion e0. replace k'. replace t'.
           rewrite !nzmap_lookup_total_insert.
           assert (∀ (x y: nat), y ≤ x 
                            → x - y = x + 1 - (y + 1)) as Heq. lia.
           apply Heq; try done.
           unfold inf in I2_ge_I1. rewrite Hi2n in I2_ge_I1. 
           by simpl in I2_ge_I1.
        ** rewrite !nzmap_lookup_total_insert_ne; try done.
      * unfold domm, dom, flowint_dom in n_in_I2.
        rewrite elem_of_dom in n_in_I2 *; intros n_in_I2.
        rewrite Hi2n in n_in_I2. exfalso. 
        destruct n_in_I2 as [x n_in_I2]. 
        inversion n_in_I2. 
  - assert (inf_map I1 !! n' = inf_map I1' !! n') as Eq1.
    { replace I1'. unfold outflow_delete_KT.
      unfold inf_map at 2. by simpl. }
    assert (out I2 n' = out I2' n') as Eq2.
    { replace I2'. unfold inflow_delete_KT. 
      unfold out, out_map at 2. by simpl. }
    assert (inf_map I2 !! n' = inf_map I2' !! n') as Eq3. 
    { replace I2'. unfold inflow_delete_KT.
      unfold inf_map at 2. simpl.
      rewrite lookup_insert_ne; try done. }
    assert (out I1 n' = out I1' n') as Eq4.
    { replace I1'. unfold outflow_delete_KT.
      unfold out, out_map at 2. simpl.
      rewrite nzmap_lookup_total_insert_ne; try done. }
    by rewrite Eq1 Eq2 Eq3 Eq4.
Qed.           
    
Lemma flowint_insert_outComp_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → 
        I1' = outflow_insert_KT I1 n k t →
          I2' = inflow_insert_KT I2 n k t →
            outComp I1 I2 = outComp I1' I2'.
Proof.
  intros n_in_I2 Hi1 Hi2. apply nzmap_eq. intros n'.
  unfold outComp. rewrite !nzmap_lookup_imerge.
  unfold outComp_op.
  pose proof (inflow_insert_domm I2 n k t I2' Hi2) as domm_2.
  destruct (decide (n' = n)).
  - replace n'.
    assert (n ∈ domm I2') as n_in_I2' by set_solver.
    destruct (decide (n ∈ domm I1 ∪ domm I2)); 
    last by set_solver.
    by destruct (decide (n ∈ domm I1' ∪ domm I2')); 
    last by set_solver.
  - destruct (decide (n' ∈ domm I1 ∪ domm I2)).
    + assert (n' ∈ domm I1' ∪ domm I2') as n'_in_I12' by set_solver.
      by destruct (decide (n' ∈ domm I1' ∪ domm I2')); last by set_solver.
    + assert (n' ∉ domm I1' ∪ domm I2') as n_notin_I12' by set_solver.
      destruct (decide (n' ∈ domm I1' ∪ domm I2')); first by set_solver.
      unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
      simpl. apply nzmap_eq. intros kt'.
      rewrite !nzmap_lookup_merge. unfold nat_op.
      replace I1'. unfold outflow_delete_KT. unfold out_map at 3.
      simpl. rewrite nzmap_lookup_total_insert_ne; try done.
      replace I2'. unfold inflow_delete_KT. unfold out_map at 4.
      by simpl. 
Qed.

Lemma outflow_insert_valid_KT I1 I1' n k t :
      n ∉ domm I1 → 
        domm I1 ≠ ∅ →
          I1' = outflow_insert_KT I1 n k t →
            ✓ I1 → ✓ I1'.
Proof.
  intros n_domm domm_I1 Hi1_eq Valid1.
  unfold valid, flowint_valid.
  replace I1'. unfold inflow_insert_KT. 
  destruct (I1) as [ [i o] | ] eqn: Hi1; [| exfalso; try done].
  unfold valid, flowint_valid in Valid1. 
  simpl in Valid1. 
  simpl. split.
  - apply map_disjoint_dom.
    destruct Valid1 as [H' _].
    apply map_disjoint_dom in H'.
    rewrite <-Hi1.
    unfold nzmap_insert at 1.
    destruct (decide (<<[ (k, t) := out I1 n ! (k, t) + 1 ]>> (out I1 n) = 0%CCM)).
    + simpl. destruct o as [og prf_og] eqn: Ho.
      unfold nzmap_delete. simpl. rewrite dom_delete.
      set_solver.
    + simpl. destruct o as [og prf_og] eqn: Ho.
      simpl. rewrite dom_insert.
      unfold domm, dom, flowint_dom in n_domm.
      unfold inf_map in n_domm. simpl in n_domm.
      set_solver. 
  - intros Hi. destruct Valid1 as [_ H'].
    unfold domm, dom, flowint_dom in domm_I1.
    unfold inf_map in domm_I1. simpl in domm_I1.
    exfalso. apply domm_I1. rewrite Hi. 
    apply leibniz_equiv. by rewrite dom_empty.
Qed.

Lemma inflow_insert_valid_KT I1 I1' n k t :
      n ∈ domm I1 →
        I1' = inflow_insert_KT I1 n k t →
          ✓ I1 → ✓ I1'.
Proof.
  intros n_domm Hi1_eq Valid1.
  unfold valid, flowint_valid.
  replace I1'. unfold inflow_insert_KT. 
  destruct (I1) as [ [i o] | ] eqn: Hi1; [| exfalso; try done].
  unfold valid, flowint_valid in Valid1. 
  simpl in Valid1. 
  simpl. split.
  - apply map_disjoint_dom.
    simpl.
    destruct Valid1 as [H' _].
    apply map_disjoint_dom in H'. rewrite <-Hi1 in Hi1_eq.
    pose proof (inflow_insert_domm I1 n k t I1' Hi1_eq) as Hdomm.
    rewrite <-Hi1 in n_domm.
    assert (domm I1' = domm I1) as H'' by set_solver.
    unfold domm, dom, flowint_dom in H''.
    replace I1' in H''. unfold inflow_insert_KT in H''.
    simpl in H''. rewrite Hi1 in H''. simpl in H''.
    rewrite <-Hi1 in H''. apply leibniz_equiv_iff in H''.
    rewrite (dom_insert i) in H'' *; intros H''.
    unfold domm, dom, flowint_dom in n_domm.
    replace I1 in n_domm. simpl in n_domm.
    rewrite dom_insert. set_solver.
  - intros Hi. destruct Valid1 as [_ H'].
    apply nzmap_eq. intros n'.
    rewrite <-Hi1 in Hi. 
    assert (<[n:=<<[ (k, t) := inf I1 n ! (k, t) + 1 ]>> (inf I1 n)]> i !! n 
                                  = None) as H''.
    { rewrite Hi. by rewrite lookup_empty. }
    rewrite lookup_insert in H''.
    inversion H''.
Qed.    

Lemma flowint_insert_intComposable_KT I1 I1' I2 I2' n k t :
       n ∈ domm I2 → domm I1 ≠ ∅ →
        out I1 n ! (k,t) ≤ inf I2 n ! (k,t) →
          I1' = outflow_insert_KT I1 n k t →
            I2' = inflow_insert_KT I2 n k t →
              intComposable I1 I2 → 
                intComposable I1' I2'.
Proof.
  intros n_in_I2 domm_I1 I2_ge_I1 Hi1 Hi2 Intcomp.
  assert (n ∉ domm I1) as n_notin_I1.
  { unfold intComposable in Intcomp.
    destruct Intcomp as [_ [_ [H' _]]].
    clear -H' n_in_I2. set_solver. }
  unfold intComposable. repeat split.
  - apply (outflow_insert_valid_KT I1 I1' n k t); try done.
    by destruct Intcomp as [H' _].
  - apply (inflow_insert_valid_KT I2 I2' n k t); try done.
    by destruct Intcomp as [_ [H' _]].
  - pose proof (inflow_insert_domm I2 n k t I2' Hi2) as domm_2.
    assert (domm I1' = domm I1) as domm_1. 
    { unfold domm, dom, flowint_dom. replace I1'.
      unfold outflow_insert_KT. unfold inf_map. by simpl. }
    destruct Intcomp as [_ [_ [H' _]]].
    set_solver.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros kt'.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    assert (inf_map I1' = inf_map I1) as Hinf_1.
    { replace I1'. unfold outflow_delete_KT.
      unfold inf_map. by simpl. }
    rewrite Hinf_1 in Hin'.
    destruct Intcomp as [_ [_ [_ [H' _]]]].
    unfold map_Forall in H'. pose proof H' n' m Hin' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. rewrite nzmap_eq in H' *; intros H'.
    pose proof H' kt' as H'. rewrite !nzmap_lookup_merge in H'.
    unfold nat_op, nat_opinv in H'.
    assert (out I2' n' = out I2 n') as Hout.
    { replace I2'. unfold inflow_delete_KT.
      unfold out, out_map. by simpl. }
    rewrite Hout. unfold inf. unfold inf in H'.
    by rewrite Hinf_1.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros kt'.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    destruct Intcomp as [_ [_ [_ [_ H']]]].
    unfold map_Forall in H'. pose proof H' n' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. destruct (decide (n' = n)). 
    + replace n'. replace I1'. unfold outflow_insert_KT.
      unfold out at 1, out_map at 1. simpl.
      unfold out at 3, out_map at 3. simpl.
      rewrite !nzmap_lookup_total_insert.
      destruct (decide (kt' = (k,t))).
      * replace kt'. rewrite !nzmap_lookup_total_insert.
        replace I2' in Hin'. unfold inflow_insert_KT in Hin'.
        unfold inf_map at 1 in Hin'. simpl in Hin'.
        rewrite e in Hin'. rewrite lookup_insert in Hin'.
        inversion Hin'. rewrite nzmap_lookup_total_insert.
        replace I2'. unfold inflow_insert_KT.
        unfold inf at 2. unfold inf_map at 1. simpl.
        rewrite lookup_insert. simpl.
        rewrite nzmap_lookup_total_insert.
        assert (∀ (x y: nat), x >= y →
            x + 1 = y + 1 + (x + 1 - (y + 1))) as Heq. lia.
        apply Heq; try done.
      * unfold inf. rewrite e in Hin'. rewrite Hin'. simpl.
        replace I2' in Hin'. unfold inflow_insert_KT in Hin'. 
        unfold inf_map at 1 in Hin'. simpl in Hin'. 
        rewrite lookup_insert in Hin'. inversion Hin'.
        rename H1 into Hin2.
        rewrite !nzmap_lookup_total_insert_ne; try done.
        rewrite e in H'.
        assert (inf_map I2 !! n = Some (inf I2 n)) as H''.
        { unfold inf. destruct (inf_map I2 !! n) eqn: Hi2n.
          by simpl. unfold domm, dom, flowint_dom in n_in_I2.
          rewrite elem_of_dom in n_in_I2 *; intros n_in_I2.
          rewrite Hi2n in n_in_I2. 
          destruct n_in_I2 as [x Hx]; inversion Hx. } 
        pose proof H' (inf I2 n) H'' as Heq.
        rewrite nzmap_eq in Heq *; intros Heq.
        pose proof Heq kt' as Heq. 
        rewrite !nzmap_lookup_merge in Heq.
        by unfold nat_op, nat_opinv in Heq.
    + assert (inf I2' n' = inf I2 n') as Hin. 
      { replace I2'. unfold inflow_insert_KT.
      unfold inf at 1, inf_map at 1. simpl.
      rewrite lookup_insert_ne; try done. }
      rewrite Hin. replace I2' in Hin'. 
      unfold inflow_insert_KT in Hin'.
      unfold inf at 1, inf_map at 1 in Hin'. simpl in Hin'.
      rewrite lookup_insert_ne in Hin'; try done. 
      pose proof H' m Hin' as H'.
      rewrite nzmap_eq in H' *; intros H'.
      pose proof H' kt' as H'.
      rewrite !nzmap_lookup_merge in H'.
      unfold nat_op, nat_opinv in H'.
      assert (out I1' n' = out I1 n') as Hout.
      { replace I1'. unfold outflow_insert_KT.
        unfold out at 1, out_map at 1. simpl.
        rewrite nzmap_lookup_total_insert_ne; try done. }
      by rewrite Hout.  
Qed.

Lemma flowint_insert_valid_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → domm I1 ≠ ∅ →
        I1' = outflow_insert_KT I1 n k t →
          I2' = inflow_insert_KT I2 n k t →
            ✓ (I1 ⋅ I2) → ✓ (I1' ⋅ I2').
Proof.
  intros n_in_I2 domm_I1 Hi1 Hi2 Valid_12.
  pose proof intComposable_valid I1 I2 Valid_12 as Intcomp_12.
  apply intValid_composable. 
  apply (flowint_insert_intComposable_KT I1 I1' I2 I2' n k t); try done.
  pose proof intComp_unfold_inf_2 I1 I2 Valid_12 n n_in_I2 as H'.
  unfold ccmop, ccm_op in H'. simpl in H'.
  unfold lift_op, ccmop, ccm_op in H'. simpl in H'.
  rewrite nzmap_eq in H' *; intros H'.
  pose proof H' (k,t) as H'. unfold nat_op in H'.
  rewrite nzmap_lookup_merge in H'. 
  rewrite H'.
  assert (∀ (x y: nat), x ≤ y + x) as Heq by lia.
  apply Heq.  
Qed.

Lemma flowint_insert_eq_KT I1 I1' I2 I2' n k t :
      n ∈ domm I2 → domm I1 ≠ ∅ →
        I1' = outflow_insert_KT I1 n k t →
          I2' = inflow_insert_KT I2 n k t →
            ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  intros n_in_I2 domm_I1 Hi1 Hi2 Valid_12.
  pose proof (intComposable_valid _ _ Valid_12) as HintComp.
  pose proof (flowint_insert_valid_KT I1 I1' I2 I2' n k t 
                n_in_I2 domm_I1 Hi1 Hi2 Valid_12) as Valid_12'.
  pose proof (intComposable_valid _ _ Valid_12') as HintComp'.   
  destruct (I1⋅I2) as [ [i o] | ] eqn: Hi12; [| exfalso; try done].
  unfold op, intComp in Hi12.
  destruct (decide (intComposable I1 I2)); last done.
  inversion Hi12.
  destruct (I1'⋅I2') as [ [i' o'] | ] eqn: Hi12'; [| exfalso; try done].    
  unfold op, intComp in Hi12'.
  destruct (decide (intComposable I1' I2')); last done.
  inversion Hi12'.
  apply intValid_composable in HintComp.
  assert (infComp I1 I2 = infComp I1' I2') as Hinfcomp.
  { apply (flowint_insert_infComp_KT I1 I1' I2 I2' n k t); try done.
    pose proof intComp_unfold_inf_2 I1 I2 HintComp n n_in_I2 as H'.
    unfold ccmop, ccm_op in H'. simpl in H'.
    unfold lift_op, ccmop, ccm_op in H'. simpl in H'.
    rewrite nzmap_eq in H' *; intros H'.
    pose proof H' (k,t) as H'. unfold nat_op in H'.
    rewrite nzmap_lookup_merge in H'. 
    rewrite H'.
    assert (∀ (x y: nat), x ≤ y + x) as Heq by lia.
    apply Heq. }
  pose proof (flowint_insert_outComp_KT I1 I1' I2 I2' n k t n_in_I2 Hi1 Hi2) 
                                      as Houtcomp.
  by rewrite Hinfcomp Houtcomp.  
Qed.

Lemma inflow_insert_set_out_eq_KT I n S I' n' :
      I' = inflow_insert_set_KT I n S →
          out I' n' = out I n'.
Proof.
Admitted.

Lemma outflow_insert_inf_eq_KT I n k t I' :
      I' = outflow_insert_KT I n k t → 
        ∀ n', inset_KT I' n' = inset_KT I n'.
Proof.
  intros Heq. intros n'. unfold inset_KT. 
  unfold inf. replace I'.
  unfold outflow_insert_KT. by simpl. 
Qed.

Lemma outflow_delete_inf_eq_KT I n k t I' :
      I' = outflow_delete_KT I n k t → 
        ∀ n', inset_KT I' n' = inset_KT I n'.
Proof.
  intros Heq. intros n'. unfold inset_KT. 
  unfold inf. replace I'.
  unfold outflow_insert_KT. by simpl. 
Qed.

  Lemma flowint_insert_set_eq_KT I1 I1' I2 I2' n S :
        I1' = outflow_insert_set_KT I1 n S →
          I2' = inflow_insert_set_KT I2 n S →
             I1 ⋅ I2 = I1' ⋅ I2'.
  Proof.
  Admitted.

  Lemma flowint_delete_set_eq_KT I1 I1' I2 I2' n S :
        I1' = outflow_delete_set_KT I1 n S →
          I2' = inflow_delete_set_KT I2 n S →
             I1 ⋅ I2 = I1' ⋅ I2'.
  Proof.
  Admitted.

  
  Lemma flowint_inflow_insert_set_dom_KT I n S I':
        I' = inflow_insert_set_KT I n S
          → domm I' = domm I ∪ {[n]}.
  Proof.
  Admitted. 

Lemma outflow_insert_set_inset_KT I n S I' n' :
      I' = outflow_insert_set_KT I n S → 
          inset_KT I' n' = inset_KT I n'.
Proof.
Admitted.



End KT_flows.

Arguments KT _ : assert.
Arguments KT_multiset _ {_ _} : assert.
Arguments KT_flowint_ur _ {_ _} : assert.
 
