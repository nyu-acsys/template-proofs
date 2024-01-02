Require Import Coq.Numbers.NatInt.NZAddOrder.
From iris.algebra Require Import gset.
Set Default Proof Using "All".
Require Export flows ccm.
Require Import Coq.Setoids.Setoid.

(** Flow interface cameras and auxiliary lemmas for multiset flows *)

Section multiset_flows.

Context `{Countable K}.

(** CCM of finite multisets over a countable set K *)

Definition K_multiset := nzmap K nat.

Global Instance K_multiset_ccm : CCM K_multiset := lift_ccm K nat.

Global Canonical Structure multiset_flowint_ur : ucmra := flowintUR K_multiset.

Implicit Type I : multiset_flowint_ur.

(** Insets and outsets of flow interfaces *)

Definition inset I n := dom (inf I n).

Definition outset I n := dom (out I n).

Definition in_inset k I n := k ∈ dom (inf I n).

Definition in_outset k I n := k ∈ dom (out I n).

Definition in_outsets k In := ∃ n, in_outset k In n.

Definition closed I := ∀ k n, k ∉ outset I n.

Definition set_union (f : nat → gset nat) (S: gset nat) :=
  ([^op set] x ∈ S, f x). 

Definition insets I := ([^union set] x ∈ dom I, inset I x).

Definition outsets I := ([^union set] x ∈ dom (out_map I), outset I x).

(*
Definition insets I := 
  let f := λ (n: Node) (ms: K_multiset) res, res ∪ dom ms in
    map_fold f (∅: gset K) (inf_map I).

Definition outsets I :=
  let f := λ (n: Node) (ms: K_multiset) res, res ∪ dom ms in
    map_fold f (∅: gset K) (nzmap_car (out_map I)).
*)

Definition keyset I := (insets I) ∖ (outsets I).

Lemma inset_in_insets I n k :
  k ∈ inset I n → k ∈ insets I.
Proof.
  intros Hk.
  assert (n ∈ dom I) as n_in_I.
  { unfold inset in Hk. unfold inf in Hk.
    destruct (inf_map I !! n) eqn: H'.
    - unfold dom, flowint_dom.
      rewrite elem_of_dom. exists k0; try done.
    - simpl in Hk. unfold nzmap_dom in Hk. simpl in Hk.
      set_solver. }
  unfold dom, flowint_dom in n_in_I.
  unfold insets.
  rewrite (big_opS_delete _ _ n); try done.
  set_solver.
Qed.  

Lemma outset_in_outsets I n k :
  k ∈ outset I n → k ∈ outsets I.
Proof.
  intros Hk.
  assert (n ∈ dom (out_map I)) as Hn.
  { rewrite nzmap_elem_of_dom.
    destruct (out_map I !! n) eqn: H'; try done.
    unfold outset, out in Hk.
    rewrite nzmap_lookup_total_alt in Hk.
    rewrite H' in Hk.
    simpl in Hk.
    set_solver. }  
  unfold outsets.
  rewrite (big_opS_delete _ _ n); try done.
  set_solver.
Qed.

(** Assorted lemmas for multiset flow interfaces *)

Lemma composable_outflow_leq_inflow I1 I2 k n :
  n ∈ dom I2 →
  intComposable I1 I2 →
  out I1 n !!! k ≤ inf I2 n !!! k.
Proof.
  intros Hn_in_I2 HiC.
  unfold intComposable in HiC.
  destruct HiC as (_ & _ & _ & Hinf1 & Hinf2).
  unfold map_Forall in Hinf1.
  unfold map_Forall in Hinf2.
  pose proof (Hinf2 n (inf I2 n)).
  rewrite H0.
  unfold ccmop, ccm_op, lift_op.
  simpl. unfold lift_op.
  rewrite nzmap_lookup_merge.
  unfold ccmop, ccm_op, nat_ccm, nat_op.
  unfold ccmop_inv, ccm_opinv. simpl.
  unfold lift_opinv.
  rewrite nzmap_lookup_merge.
  unfold ccmop_inv, ccm_opinv. simpl.
  unfold nat_opinv.
  apply Nat.le_add_r.
  unfold dom, flowint_dom in Hn_in_I2.
  apply elem_of_dom in Hn_in_I2.
  unfold is_Some in Hn_in_I2.
  destruct Hn_in_I2.
  unfold inf.
  rewrite H1. auto.
Qed.
  
Lemma inset_monotone I I1 I2 k n :
    ✓ I → I = I1 ⋅ I2 → k ∈ inset I n → n ∈ dom I1 → k ∈ inset I1 n.
Proof.
  intros VI ID Inset Dom.
  rewrite ID in VI.
  pose proof (intComp_unfold_inf_1 I1 I2 VI n) Dom as Inf1.
  assert (Inset1 := Inset).
  unfold inset in Inset.
  rewrite nzmap_elem_of_dom_total in Inset.
  unfold inset. rewrite nzmap_elem_of_dom_total.
  rewrite Inf1 -ID. 
  rewrite /ccmunit /=.
  rewrite /ccmunit /= in Inset.
  rewrite /ccmop /=. 
  unfold nat_unit. unfold nat_unit in Inset.
  rewrite /ccm_op /=. rewrite /lift_op /=.
  rewrite lookup_total_lifting.
  rewrite /ccmop /=. rewrite /ccm_op /=.
  rewrite /nat_op /=.  
  lia.
Qed.

Lemma intComp_out_zero (I1 I2: multiset_flowint_ur) n : 
        ✓ (I1 ⋅ I2) → n ∉ dom (I1 ⋅ I2) → 
          out (I1 ⋅ I2) n = 0%CCM → out I2 n = 0%CCM.
Proof.
  intros Hvld Hn Hout. apply nzmap_eq. intros k.       
  assert (out (I1 ⋅ I2) n = (out (I1) n) + (out I2 n))%CCM.
  { rewrite intComp_unfold_out; try done. }
  assert (out (I1 ⋅ I2) n !!! k = (out (I1) n) !!! k + (out I2 n) !!! k)%CCM.
  { rewrite H0. by rewrite lookup_total_lifting. }
  rewrite Hout in H1. rewrite nzmap_lookup_empty in H1.
  unfold ccmunit,ccm_unit in H1. simpl in H1.
  unfold nat_unit in H1. unfold ccmop, nat_op in H1.
  assert (out I2 n !!! k = 0). lia.
  rewrite H2. rewrite nzmap_lookup_empty. unfold ccmunit, ccm_unit. 
  simpl. by unfold nat_unit.
Qed. 

Lemma flowint_step :
  ∀ I I1 I2 k n,
    ✓ I →
    closed I →
    I = I1 ⋅ I2 → k ∈ outset I1 n → n ∈ dom I2.
Proof.
  intros I I1 I2 k n vI cI dI kOut.
  rewrite dI in vI.
  
  assert (dom I = dom I1 ∪ dom I2) as disj.
  pose proof (intComp_dom _ _ vI).
  rewrite dI.
  trivial.

  (* First, prove n ∉ domm I1 *)
  destruct (decide (n ∈ dom I1)).
  pose proof (intComp_valid_proj1 I1 I2 vI) as vI1.
  pose proof (intValid_in_dom_not_out I1 n vI1 e).
  unfold outset, dom in kOut.
  rewrite nzmap_elem_of_dom_total in kOut.
  unfold ccmunit, ccm_unit, K_multiset_ccm, lift_ccm, lift_unit in H0.
  rewrite H0 in kOut.
  rewrite nzmap_lookup_empty in kOut.
  contradiction.
    
  (* Now, prove n ∈ domm I *)    
  assert (n ∈ dom (I1 ⋅ I2)) as in_Inf_n.
  pose proof (intComp_unfold_out I1 I2 vI n).
  destruct (decide (n ∉ dom (I1 ⋅ I2))).
  apply H0 in n1.
  pose proof (cI k n) as not_k_out.
  unfold outset, dom in not_k_out.
  rewrite nzmap_elem_of_dom_total in not_k_out.
  apply dec_stable in not_k_out.
  unfold outset, dom in kOut.
  rewrite nzmap_elem_of_dom_total in kOut.
  assert (out I n !!! k = out (I1 ⋅ I2) n !!! k).
  rewrite dI. reflexivity.
  rewrite n1 in H1.
  rewrite lookup_total_lifting in H1.
  unfold ccmop, ccm_op in H1.
  unfold K_multiset_ccm,ccmunit,ccm_unit,nat_ccm,
    nat_unit,nat_op in kOut, not_k_out, H1.
  rewrite not_k_out in H1.  
  lia.
  apply dec_stable in n1. trivial.
    
  (* Finally, prove n ∈ domm I2 *)
  apply intComp_dom in vI.
  rewrite vI in in_Inf_n.
  set_solver.
Qed.

Lemma outset_distinct : ∀ I n, ✓ I ∧ (∃ k, k ∈ outset I n) → n ∉ dom I.
Proof.
  intros.
  destruct H0 as (VI & Out).
  destruct Out as [k Out].

  apply flowint_valid_unfold in VI.
  destruct VI as (Ir & dI & disj & _).

  unfold outset, dom, nzmap_dom, out, out_map in Out.
  rewrite dI in Out.
  rewrite nzmap_elem_of_dom_total in Out.
  destruct (decide (outR Ir !!! n = ∅)).
  rewrite e in Out.
  rewrite nzmap_lookup_empty in Out.
  contradiction.
  rewrite <- nzmap_elem_of_dom_total in n0.
  unfold dom, nzmap_dom in n0.
  
  unfold dom, flowint_dom, inf_map.
  rewrite dI.
  set_solver.
Qed.

Lemma flowint_inset_step : ∀ I1 I2 k n,
    ✓ (I1 ⋅ I2) → n ∈ dom I2 → k ∈ outset I1 n → k ∈ inset I2 n.
Proof.
  intros ? ? ? ? I12V Out Inset.
  apply intComposable_valid in I12V.
  pose proof (composable_outflow_leq_inflow I1 I2 k n Out I12V).
  unfold outset, dom in Inset.
  rewrite nzmap_elem_of_dom_total in Inset.
  unfold inset, dom.
  rewrite nzmap_elem_of_dom_total.
  unfold ccmunit, ccm_unit, nat_ccm, nat_unit in Inset.
  unfold ccmunit, ccm_unit, nat_ccm, nat_unit.
  assert (out I1 n !!! k > 0 ∨ out I1 n !!! k = 0). lia.
  destruct H1.
  assert (inf I2 n !!! k ≠ 0). lia. trivial. contradiction.
Qed.

(** Function and lemmas for frame-preserving updates of flow interfaces *)


Definition outflow_map_set f I (n: Node) (s: gset K) : multiset_flowint_ur := 
  let I_out_n := (nzmap_map_set f s (out I n)) in
  let I'_out := (<<[n := I_out_n]>> (out_map I)) in
  (int {| infR := inf_map I ; outR := I'_out |}).

Definition inflow_map_set f I (n: Node) (s: gset K) : multiset_flowint_ur := 
  let I_inf_n := (nzmap_map_set f s (inf I n)) in
  let I'_inf := (<[ n := I_inf_n ]>(inf_map I)) in
  (int {| infR := I'_inf ; outR := out_map I |}).

Lemma outflow_lookup_total_map_set f I n k s :
      k ∈ s → out (outflow_map_set f I n s) n !!! k = f k (out I n !!! k).
Proof.
  intros Heq. unfold out.
  unfold outflow_map_set.
  unfold out. simpl.
  apply leibniz_equiv.
  rewrite nzmap_lookup_total_insert.
  rewrite nzmap_lookup_total_map_set.
  trivial. trivial.
Qed.

Lemma outflow_lookup_total_map_set_ne f I n k s :
      k ∉ s → out (outflow_map_set f I n s) n !!! k = out I n !!! k.
Proof.
  intros Hneq. unfold out.
  unfold outflow_map_set.
  unfold out. simpl.
  apply leibniz_equiv.
  rewrite nzmap_lookup_total_insert.
  rewrite nzmap_lookup_total_map_set_ne.
  trivial. trivial.
Qed.  

Lemma inflow_lookup_total_map_set f I n k s :
      k ∈ s → inf (inflow_map_set f I n s) n !!! k = f k (inf I n !!! k).
Proof.
  intros Heq. unfold inf.
  unfold inflow_map_set.
  unfold inf. simpl.
  apply leibniz_equiv.
  rewrite lookup_partial_alter.
  simpl.
  rewrite nzmap_lookup_total_map_set.
  trivial. trivial.
Qed.

Lemma inflow_lookup_total_map_set_ne f I n k s :
      k ∉ s → inf (inflow_map_set f I n s) n !!! k = inf I n !!! k.
Proof.
  intros Heq. unfold inf.
  unfold inflow_map_set.
  unfold inf. simpl.
  apply leibniz_equiv.
  rewrite lookup_partial_alter.
  simpl.
  rewrite nzmap_lookup_total_map_set_ne.
  trivial. trivial.
Qed.

Lemma outflow_map_set_out_map_ne f I n S n' :
      n' ≠ n → 
           out_map (outflow_map_set f I n S) !!! n' = out_map I !!! n'.
Proof.
  intros Hneq.
  unfold outflow_map_set. simpl.
  rewrite nzmap_lookup_total_insert_ne.
  trivial. auto.
Qed.

Lemma outflow_map_set_outset_ne f I n S n' :
      n' ≠ n → 
           outset (outflow_map_set f I n S) n' = outset I n'.
Proof.
  intros Hneq. unfold outset.
  unfold out.
  rewrite (outflow_map_set_out_map_ne f I n S n').
  trivial. auto.
Qed.
  
Lemma outflow_map_set_inf f I n S :
          inf_map (outflow_map_set f I n S) = inf_map I.
Proof.
  unfold outflow_map_set.
  trivial.
Qed.

Lemma outflow_map_set_inset f I n S n': 
           inset (outflow_map_set f I n S) n' = inset I n'.
Proof.
  by rewrite /inset /outflow_map_set /inf {1}/inf_map /=.
Qed.

Lemma inflow_map_set_ne f I n S n' :
      n' ≠ n → 
           inf_map (inflow_map_set f I n S) !! n' = inf_map I !! n'.
Proof.
  intros Hneq.
  unfold inf. simpl.
  rewrite lookup_partial_alter_ne.
  auto. auto.
Qed.

Lemma inflow_map_set_out_eq f I n S :
          out_map (inflow_map_set f I n S) = out_map I.
Proof.
  unfold inflow_map_set.
  unfold outset.
  unfold inf.
  simpl.
  trivial.
Qed.

Lemma inflow_map_set_outset_ne f I n S n' :
           outset (inflow_map_set f I n S) n' = outset I n'.
Proof.
  unfold outset.
  pose proof (inflow_map_set_out_eq f I n S).
  unfold out.
  by rewrite H0.
Qed.

Definition nzmap_decrement (k: K) (m : nzmap K nat) :=
  nzmap_map (λ _ n, n - 1) k m.

Definition nzmap_increment (k: K) (m : nzmap K nat) :=
  nzmap_map (λ _ n, n - 1) k m.

Definition nzmap_decrement_set (s: gset K) (m : nzmap K nat) : nzmap K nat := 
  nzmap_map_set (λ _ n, n - 1) s m.

Definition nzmap_increment_set (s: gset K) (m : nzmap K nat) : nzmap K nat := 
  nzmap_map_set (λ _ n, n + 1) s m.


Definition outflow_insert_set I (n: Node) (s: gset K) : multiset_flowint_ur :=
  outflow_map_set (λ _ n, n + 1) I n s.

Definition outflow_delete_set I (n: Node) (s: gset K) : multiset_flowint_ur := 
  outflow_map_set (λ _ n, n - 1) I n s.

(* assumes: n ∈ domm I *)           
Definition inflow_insert_set I (n: Node) (s: gset K) : multiset_flowint_ur :=
  inflow_map_set (λ _ n, n + 1) I n s.

(* assumes: n ∈ domm I *)
Definition inflow_delete_set I (n: Node) (s: gset K) : multiset_flowint_ur := 
  inflow_map_set (λ _ n, n - 1) I n s.

Lemma outflow_insert_set_outset I n S :
           outset (outflow_insert_set I n S) n = (outset I n) ∪ S.
Proof.
  unfold outset. unfold outflow_insert_set.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - set_solver.
  - rewrite nzmap_lookup_total_map_set.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    unfold ccmunit, ccm_unit. simpl.
    unfold nat_unit. lia. done.
  - rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    intro.
    left.
    trivial. trivial.
  - rewrite elem_of_union.
    intro.
    destruct H0.
    rewrite nzmap_lookup_total_map_set_ne.
    rewrite nzmap_elem_of_dom_total in H0 *.
    trivial. trivial.
    contradiction.
Qed.

Lemma outflow_delete_set_outset I n S :
      (∀ k, k ∈ S → out I n !!! k ≤ 1) →
           outset (outflow_delete_set I n S) n = (outset I n) ∖ S.
Proof.
  intros Hkb. unfold outset.
  unfold outflow_delete_set.
  unfold out. simpl.
  rewrite nzmap_lookup_total_insert.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - intros. apply Hkb in e as HxB.
    rewrite nzmap_lookup_total_map_set in H0.
    unfold ccmunit, ccm_unit, nat_ccm, nat_unit in H0. simpl.
    assert (out I n !!! x - 1 = 0). lia.
    contradiction. done.
  - intros. set_solver.
  - intros. rewrite nzmap_lookup_total_map_set_ne in H0.
    rewrite elem_of_difference.
    split.
    rewrite nzmap_elem_of_dom_total.
    unfold out in H0.
    all: done.
  - intros. rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_difference in H0 *; intros.
    destruct H0 as [H0 _].
    rewrite nzmap_elem_of_dom_total in H0 *; intros.
    unfold out. all: done.
Qed.    

Lemma outflow_insert_set_outset_ne I n S n' :
      n' ≠ n → 
           outset (outflow_insert_set I n S) n' = outset I n'.
Proof.
  apply outflow_map_set_outset_ne.
Qed.

Lemma outflow_delete_set_outset_ne I n S n' :
      n' ≠ n → 
           outset (outflow_delete_set I n S)  n' = outset I n'.
Proof.
  apply outflow_map_set_outset_ne.
Qed.


Lemma inflow_insert_set_out_eq I n S n' :
      out (inflow_insert_set I n S) n' = out I n'.
Proof.
  unfold out.
  intros.
  rewrite (inflow_map_set_out_eq (λ _ n, n + 1) I n S).
  trivial.
Qed.

Lemma inflow_insert_set_outset_ne I n S n' :
      outset (inflow_insert_set I n S) n' = outset I n'.
Proof.
  apply inflow_map_set_outset_ne.
Qed.

Lemma outflow_insert_set_inset I n S n' :
        inset (outflow_insert_set I n S) n' = inset I n'.
Proof.
  unfold inset.
  pose proof (outflow_map_set_inf (λ _ n, n + 1) I n S).
  unfold outflow_insert_set.
  intros.
  unfold inf.
  rewrite H0. auto.
Qed.


Lemma inflow_insert_set_inset_ne I n S n' :
      n' ≠ n → 
           inset (inflow_insert_set I n S) n' = inset I n'.
Proof.
  unfold inset.
  pose proof (inflow_map_set_ne (λ _ n, n + 1) I n S n').
  intros.
  unfold inf.
  rewrite H0; done.
Qed.

Lemma flowint_outflow_map_set_dom f I n S :
      (dom (out_map (outflow_map_set f I n S)) ⊆ dom (out_map I) ∪ {[n]}).
Proof.
  apply elem_of_subseteq.
  intros n' HinI'.
  apply elem_of_union.
  destruct (decide (n = n')).
  - set_solver.
  - left.
    unfold outflow_map_set, out_map at 1 in HinI'. simpl in HinI'.
    apply nzmap_elem_of_dom_total in HinI'.
    rewrite nzmap_lookup_total_insert_ne in HinI'.
    rewrite nzmap_elem_of_dom_total.
    trivial.
    trivial.
Qed.    

Lemma flowint_inflow_map_set_dom f (I: multiset_flowint_ur) n S:
        dom (inflow_map_set f I n S) = dom I ∪ {[n]}.
Proof.
  unfold dom, flowint_dom.
  apply leibniz_equiv.
  apply set_equiv.
  intros n'.
  pose proof (inflow_map_set_ne f I n S n').
  unfold inset, inf in H0.
  destruct (decide (n = n')).
  - rewrite <- e. split.
    * intros. rewrite elem_of_union. right. set_solver.
    * rewrite elem_of_dom.
      intros.
      unfold inflow_map_set.
      simpl.
      rewrite lookup_partial_alter.
      rewrite <- not_eq_None_Some.
      discriminate.
  - split.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      rewrite H0.
      auto. auto.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      intros.
      destruct H1.
      rewrite H0.
      auto. auto. auto.
      set_solver.
Qed.      

Lemma flowint_outflow_map_set_domm f (I: multiset_flowint_ur) n S:
        dom (outflow_map_set f I n S) = dom I.
Proof.
  unfold outflow_map_set.
  unfold dom, flowint_dom. trivial.
Qed.

Lemma flowint_map_set_infComp f I1 I1' I2 I2' n S :
      (∀ k, k ∈ S → (inf I2 n !!! k) - (out I1 n !!! k) = 
              f k (inf I2 n !!! k) - f k (out I1 n !!! k)) →
      n ∈ dom I2 → 
        I1' = outflow_map_set f I1 n S →
        I2' = inflow_map_set f I2 n S →
          infComp I1 I2 = infComp I1' I2'.
Proof.
  intros Hf n_in_I2 Hi1 Hi2. apply map_eq.
  intros n'. unfold infComp. rewrite !gmap_imerge_lookup.
  unfold infComp_op.
  destruct (decide (n' = n)).
  - replace n'.
    assert (inf_map I1 !! n = inf_map I1' !! n) as Hin_eq.
    { replace I1'. unfold inf_map. by simpl. }
    assert (out I2 n = out I2' n) as Hon_eq.
    { replace I2'. unfold inflow_insert_set.
      unfold out, out_map. by simpl. }  
    destruct (inf_map I1 !! n) as [i1 | ] eqn: Hi1n.
    + rewrite Hon_eq.
      destruct (inf_map I1' !! n); by inversion Hin_eq.
    + destruct (inf_map I1' !! n); inversion Hin_eq.
      destruct (inf_map I2 !! n) as [i2 | ] eqn: Hi2n.
      * replace I2'. simpl. rewrite lookup_insert.
        apply f_equal.
        unfold inf. rewrite Hi2n. simpl.
        replace I1'. unfold inflow_insert_set. 
        unfold out, out_map at 2. simpl.
        rewrite nzmap_lookup_total_insert.
        unfold ccmop_inv, ccm_opinv.
        simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv.
        simpl. unfold nat_opinv.
        apply nzmap_eq. intros k.
        rewrite !nzmap_lookup_merge.
        destruct (decide (k ∈ S)).
        ** rewrite !nzmap_lookup_total_map_set.
           pose proof Hf k e0.
           unfold inf, out at 1 in H0.
           rewrite Hi2n in H0. simpl in H0.
           apply H0. all: done.
        ** rewrite !nzmap_lookup_total_map_set_ne; try done.
      * unfold dom, flowint_dom in n_in_I2.
        rewrite elem_of_dom in n_in_I2.
        rewrite Hi2n in n_in_I2. exfalso. 
        destruct n_in_I2 as [x n_in_I2]. 
        inversion n_in_I2. 
  - assert (inf_map I1 !! n' = inf_map I1' !! n') as Eq1.
    { replace I1'. unfold outflow_insert_set.
      unfold inf_map at 2. by simpl. }
    assert (out I2 n' = out I2' n') as Eq2.
    { replace I2'. unfold inflow_insert_set. 
      unfold out, out_map at 2. by simpl. }
    assert (inf_map I2 !! n' = inf_map I2' !! n') as Eq3. 
    { replace I2'. unfold inflow_insert_set.
      unfold inf_map at 2. simpl.
      rewrite lookup_insert_ne; try done. }
    assert (out I1 n' = out I1' n') as Eq4.
    { replace I1'. unfold outflow_map_set.
      unfold out, out_map at 2. simpl.
      rewrite nzmap_lookup_total_insert_ne; try done. }
    by rewrite Eq1 Eq2 Eq3 Eq4.
  - trivial.
  - trivial.  
Qed.

Lemma flowint_map_set_outComp f I1 I1' I2 I2' n S :
      n ∈ dom I2 → 
        I1' = outflow_map_set f I1 n S →
          I2' = inflow_map_set f I2 n S →
            outComp I1 I2 = outComp I1' I2'.
Proof.
  intros n_in_I2 Hi1 Hi2. apply nzmap_eq. intros n'.
  unfold outComp. rewrite !nzmap_lookup_imerge.
  unfold outComp_op.
  pose proof (flowint_inflow_map_set_dom f I2 n S) as domm_2.
  destruct (decide (n' = n)).
  - replace n'.
    assert (n ∈ dom I2') as n_in_I2' by set_solver.
    by rewrite !decide_True; [|set_solver..].
  - destruct (decide (n' ∈ dom I1 ∪ dom I2)).
    + assert (n' ∈ dom I1' ∪ dom I2') as n'_in_I12' by set_solver.
      by rewrite !decide_True; [|set_solver..].
    + rewrite decide_False; last by set_solver.  
      assert (n' ∉ dom I1' ∪ dom I2') as n_notin_I12' by set_solver.
      rewrite decide_False; last by set_solver.
      unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
      simpl. apply nzmap_eq. intros kt'.
      rewrite !nzmap_lookup_merge. unfold nat_op.
      subst I1' I2'.
      rewrite (outflow_map_set_out_map_ne f I1 n S n').
      rewrite (inflow_map_set_out_eq f I2 n S).
      auto. auto.
Qed.

Lemma inflow_map_set_valid f I1 n S :
      n ∈ dom I1 →
          ✓ I1 → ✓ (inflow_map_set f I1 n S).
Proof.
    intros n_domm Valid1.
  unfold valid, flowint_valid.
  unfold inflow_map_set. 
  destruct (I1) as [ [i o] | ] eqn: Hi1; [| exfalso; try done].
  unfold valid, flowint_valid in Valid1. 
  simpl in Valid1. 
  simpl. split.
  - destruct Valid1 as [H' _].
    pose proof (flowint_inflow_map_set_dom f I1 n S) as Hdomm.
    rewrite <-Hi1 in n_domm.
    assert (dom (inflow_map_set f I1 n S) = dom I1) as H'' by set_solver.
    unfold dom, flowint_dom in H''.
    unfold inflow_map_set in H''.
    simpl in H''. rewrite Hi1 in H''. simpl in H''.
    rewrite <-Hi1 in H''. apply leibniz_equiv_iff in H''.
    rewrite (dom_insert i) in H''.
    unfold dom, flowint_dom in n_domm.
    replace I1 in n_domm. simpl in n_domm.
    rewrite dom_insert. set_solver.
  - intros Hi. destruct Valid1 as [_ H'].
    apply nzmap_eq. intros n'.
    rewrite <-Hi1 in Hi. 
    assert (<[n:=nzmap_map_set f S (inf I1 n)]> i !! n = None) as H''.
    { rewrite Hi. by rewrite lookup_empty. }
    rewrite lookup_insert in H''.
    inversion H''.
Qed.    


Lemma outflow_map_set_valid f I1 n S :
      n ∉ dom I1 → 
        dom I1 ≠ ∅ →
            ✓ I1 → ✓ (outflow_map_set f I1 n S).
Proof.
  intros n_domm domm_I1 Valid1.
  apply intValid_unfold.
  split.
  - unfold outflow_map_set, outflow_map_set.
    discriminate.
  - rewrite intValid_unfold in Valid1.
    pose proof flowint_outflow_map_set_dom f I1 n S as Hi1_domm.
    split.
    + pose proof outflow_map_set_inf f I1 n S as Hi1_eq.
      rewrite Hi1_eq.
      unfold dom, flowint_dom in Hi1_domm.
      rewrite elem_of_subseteq in Hi1_domm.
      rewrite elem_of_disjoint.
      intros n' HinfI1 HoutI1'.
      destruct (decide (n = n')).
      * unfold dom, flowint_dom in n_domm.
        replace n' in HinfI1. contradiction.
      * pose proof (Hi1_domm n' HoutI1').
        apply elem_of_union in H0.
        destruct H0.
        destruct Valid1 as [_ [Valid1 _]].
        rewrite elem_of_disjoint in Valid1.
        pose proof (Valid1 n' HinfI1 H0).
        contradiction.
        set_solver.
    + intros inf_I1'_emp.
      assert (dom (outflow_map_set f I1 n S) = ∅) as domm_I1'.
      { unfold dom, flowint_dom.
        rewrite inf_I1'_emp.
        set_solver. }      
      unfold dom, flowint_dom in domm_I1'.
      rewrite (outflow_map_set_inf f I1 n S) in domm_I1'.
      unfold dom, flowint_dom in domm_I1.
      contradiction.
Qed.

Lemma flowint_map_set_intComposable f I1 I1' I2 I2' n S :
       (∀ k x y, x ≤ y → f k x ≤ f k y) →
       (∀ k, k ∈ S → (inf I2 n !!! k) - (out I1 n !!! k) = 
                        f k (inf I2 n !!! k) - f k (out I1 n !!! k)) →
       n ∈ dom I2 → dom I1 ≠ ∅ →
          I1' = outflow_map_set f I1 n S →
            I2' = inflow_map_set f I2 n S →
            intComposable I1 I2 → 
            intComposable I1' I2'.
Proof.
  intros Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Intcomp.
  assert (n ∉ dom I1) as n_notin_I1.
  { unfold intComposable in Intcomp.
    destruct Intcomp as [_ [_ [H' _]]].
    clear -H' n_in_I2. set_solver. }
  unfold intComposable. repeat split.
  - subst I1'; apply (outflow_map_set_valid f I1 n S); try done.
    by destruct Intcomp as [H' _].
  - subst I2'; apply (inflow_map_set_valid f I2 n S); try done.
    by destruct Intcomp as [_ [H' _]].
  - pose proof (flowint_inflow_map_set_dom f I2 n S) as domm_2.
    assert (dom I1' = dom I1) as domm_1. 
    { unfold dom, flowint_dom. replace I1'.
      unfold outflow_map_set. unfold inf_map. by simpl. }
    pose proof Intcomp as Intcomp0.
    destruct Intcomp0 as [_ [_ [H' _]]].
    set_solver.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros kt'.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    assert (inf_map I1' = inf_map I1) as Hinf_1.
    { replace I1'. unfold outflow_map_set.
      unfold inf_map. by simpl. }
    rewrite Hinf_1 in Hin'.
    destruct Intcomp as [_ [_ [_ [H' _]]]].
    unfold map_Forall in H'. pose proof H' n' m Hin' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. rewrite nzmap_eq in H'.
    pose proof H' kt' as H'. rewrite !nzmap_lookup_merge in H'.
    unfold nat_op, nat_opinv in H'.
    assert (out I2' n' = out I2 n') as Hout.
    { replace I2'. unfold inflow_map_set.
      unfold out, out_map. by simpl. }
    rewrite Hout. unfold inf. unfold inf in H'.
    by rewrite Hinf_1.
  - unfold map_Forall.
    intros n' m. intros Hin'. apply nzmap_eq. intros k.
    unfold ccmop, ccm_op. simpl. unfold lift_op, ccmop, ccm_op.
    simpl. unfold ccmop_inv, ccm_opinv.
    simpl. unfold lift_opinv. unfold ccmop_inv, ccm_opinv. simpl.
    rewrite !nzmap_lookup_merge. unfold nat_op, nat_opinv.
    pose proof Intcomp as Intcomp0.
    destruct Intcomp0 as [_ [_ [_ [_ H']]]].
    unfold map_Forall in H'. pose proof H' n' as H'.  
    unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op, ccmop, ccm_op in H'.
    simpl in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. unfold lift_opinv in H'. unfold ccmop_inv, ccm_opinv in H'.
    simpl in H'. destruct (decide (n' = n)). 
    + replace n'. replace I1'. unfold outflow_map_set.
      unfold out at 1, out_map at 1. simpl.
      unfold out at 2, out_map at 2. simpl.
      rewrite !nzmap_lookup_total_insert.
      destruct (decide (k ∈ S)).
      * rewrite !nzmap_lookup_total_map_set.
        replace I2' in Hin'. unfold inflow_insert_set in Hin'.
        unfold inf_map at 1 in Hin'. simpl in Hin'.
        rewrite e in Hin'. rewrite lookup_insert in Hin'.
        inversion Hin'. (*rewrite nzmap_lookup_total_insert_set.*)
        replace I2'. unfold inflow_insert_set.
        unfold inf at 2. unfold inf_map at 1. simpl.
        rewrite lookup_insert. simpl.
        rewrite nzmap_lookup_total_map_set.
        pose proof composable_outflow_leq_inflow I1 I2 k n n_in_I2 Intcomp as Hleq. 
        pose proof Hfm k (out I1 n !!! k) (inf I2 n !!! k) Hleq.
        pose proof Hf k e0. 
        set a := out I1 n !!! k.
        set b := inf I2 n !!! k.
        rewrite -/a -/b /= in Hleq H0 H2. lia.
        done. done.
      * unfold inf. rewrite e in Hin'. rewrite Hin'. simpl.
        replace I2' in Hin'. unfold inflow_map_set in Hin'. 
        unfold inf_map at 1 in Hin'. simpl in Hin'. 
        rewrite lookup_insert in Hin'. inversion Hin'.
        rename H1 into Hin2.
        rewrite !nzmap_lookup_total_map_set_ne; try done.
        rewrite e in H'.
        assert (inf_map I2 !! n = Some (inf I2 n)) as H''.
        { unfold inf. destruct (inf_map I2 !! n) eqn: Hi2n.
          by simpl. unfold dom, flowint_dom in n_in_I2.
          rewrite elem_of_dom in n_in_I2.
          rewrite Hi2n in n_in_I2. 
          destruct n_in_I2 as [x Hx]; inversion Hx. } 
        pose proof H' (inf I2 n) H'' as Heq.
        rewrite nzmap_eq in Heq.
        pose proof Heq k as Heq. 
        rewrite !nzmap_lookup_merge in Heq.
        by unfold nat_op, nat_opinv in Heq.
    + assert (inf I2' n' = inf I2 n') as Hin. 
      { replace I2'. unfold inflow_insert_set.
      unfold inf at 1, inf_map at 1. simpl.
      rewrite lookup_insert_ne; try done. }
      rewrite Hin. replace I2' in Hin'.
      unfold inflow_insert_set, inflow_map_set in Hin'.
      unfold inf at 1, inf_map at 1 in Hin'. simpl in Hin'.
      rewrite lookup_insert_ne in Hin'; try done. 
      pose proof H' m Hin' as H'.
      rewrite nzmap_eq in H'.
      pose proof H' k as H'.
      rewrite !nzmap_lookup_merge in H'.
      unfold nat_op, nat_opinv in H'.
      assert (out I1' n' = out I1 n') as Hout.
      { replace I1'. unfold outflow_map_set.
        unfold out at 1, out_map at 1. simpl.
        rewrite nzmap_lookup_total_insert_ne; try done. }
      by rewrite Hout.  
Qed.


Lemma flowint_map_set_valid f I1 I1' I2 I2' n S :
  (∀ k x y, x ≤ y → f k x ≤ f k y) →
  (∀ k, k ∈ S → (inf I2 n !!! k) - (out I1 n !!! k) = 
                  f k (inf I2 n !!! k) - f k (out I1 n !!! k)) →
      n ∈ dom I2 → dom I1 ≠ ∅ →
        I1' = outflow_map_set f I1 n S →
          I2' = inflow_map_set f I2 n S →
            ✓ (I1 ⋅ I2) → ✓ (I1' ⋅ I2').
Proof.
  intros Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Valid_12.
  pose proof intComposable_valid I1 I2 Valid_12 as Intcomp_12.
  apply intValid_composable. 
  apply (flowint_map_set_intComposable f I1 I1' I2 I2' n S); try done.
Qed.


Lemma flowint_map_set_eq f (I1 I1' I2 I2': multiset_flowint_ur) n S :
  (∀ k x y, x ≤ y → f k x ≤ f k y) →
  (∀ k, k ∈ S → (inf I2 n !!! k) - (out I1 n !!! k) = 
                    f k (inf I2 n !!! k) - f k (out I1 n !!! k)) →
  n ∈ dom I2 → dom I1 ≠ ∅ →
  I1' = outflow_map_set f I1 n S →
  I2' = inflow_map_set f I2 n S →
  ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  intros Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Valid_12.
  pose proof (intComposable_valid _ _ Valid_12) as HintComp.
  pose proof (flowint_map_set_valid f I1 I1' I2 I2' n S 
                Hfm Hf n_in_I2 domm_I1 Hi1 Hi2 Valid_12) as Valid_12'.
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
  { apply (flowint_map_set_infComp f I1 I1' I2 I2' n S); try done. }
  pose proof (flowint_map_set_outComp _ I1 I1' I2 I2' n S n_in_I2 Hi1 Hi2) as Houtcomp.
    by rewrite Hinfcomp Houtcomp.
Qed.

Lemma flowint_insert_eq (I1 I1' I2 I2': multiset_flowint_ur) n S :
  n ∈ dom I2 → dom I1 ≠ ∅ →
  I1' = outflow_insert_set I1 n S →
  I2' = inflow_insert_set I2 n S →
  ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  apply flowint_map_set_eq.
  all: lia.
Qed.

Lemma flowint_delete_eq (I1 I1' I2 I2': multiset_flowint_ur) n S :
  (∀ k, k ∈ S → 1 ≤ out I1 n !!! k) →
  n ∈ dom I2 → dom I1 ≠ ∅ →
  I1' = outflow_delete_set I1 n S →
  I2' = inflow_delete_set I2 n S →
  ✓ (I1 ⋅ I2) → I1 ⋅ I2 = I1' ⋅ I2'.
Proof.
  intros.
  apply (flowint_map_set_eq (λ _ n, n - 1) I1 I1' I2 I2' n S).
  lia.
  intros.
  pose proof H0 k H6.
  lia.
  all: auto.
Qed.

Lemma inflow_insert_set_inset I n S: 
           inset (inflow_insert_set I n S) n = inset I n ∪ S.
Proof.
  unfold inset. unfold inflow_insert_set.
  unfold inflow_map_set. unfold inf at 1; simpl.
  rewrite lookup_insert. simpl.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - set_solver.
  - rewrite nzmap_lookup_total_map_set.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    unfold ccmunit, ccm_unit. simpl.
    unfold nat_unit. lia. done.
  - rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_union.
    rewrite !nzmap_elem_of_dom_total.
    intro.
    left.
    trivial. trivial.
  - rewrite elem_of_union.
    intro.
    destruct H0.
    rewrite nzmap_lookup_total_map_set_ne.
    rewrite nzmap_elem_of_dom_total in H0 *.
    trivial. trivial.
    contradiction.
Qed.



Lemma inflow_delete_set_inset I n S :
      (∀ k, k ∈ S → inf I n !!! k ≤ 1) →
           inset (inflow_delete_set I n S) n = inset I n ∖ S.
Proof.
  intros Hkb. unfold inset. unfold inflow_delete_set.
  unfold inf at 1. simpl.
  rewrite lookup_insert. simpl.
  apply leibniz_equiv.
  apply set_equiv. intros x. 
  rewrite !nzmap_elem_of_dom_total.
  destruct (decide (x ∈ S)); split.
  - intros. apply Hkb in e as HxB.
    rewrite nzmap_lookup_total_map_set in H0.
    unfold ccmunit, ccm_unit, nat_ccm, nat_unit in H0. simpl.
    assert (inf I n !!! x - 1 = 0). lia.
    contradiction. done.
  - intros. set_solver.
  - intros. rewrite nzmap_lookup_total_map_set_ne in H0.
    rewrite elem_of_difference.
    split.
    rewrite nzmap_elem_of_dom_total.
    all: done.
  - intros. rewrite nzmap_lookup_total_map_set_ne.
    rewrite elem_of_difference in H0 *; intros.
    destruct H0 as [H0 _].
    rewrite nzmap_elem_of_dom_total in H0 *; intros.
    unfold out. all: done.
Qed.

Lemma inflow_delete_set_inset_ne I n S n' :
      n' ≠ n → 
           inset (inflow_delete_set I n S) n' = inset I n'.
Proof.
  unfold inset.
  pose proof (inflow_map_set_ne (λ _ n, n - 1) I n S n').
  intros.
  unfold inf.
  rewrite H0; done.
Qed.


Lemma flowint_inflow_delete_set_dom (I: multiset_flowint_ur) n S:
      dom (inflow_delete_set I n S) = dom I ∪ {[n]}.
Proof.
  unfold dom, flowint_dom.
  apply leibniz_equiv.
  apply set_equiv.
  intros n'.
  pose proof (inflow_map_set_ne (λ _ n, n - 1) I n S n').
  unfold inset, inf in H0.
  destruct (decide (n = n')).
  - rewrite <- e. split.
    * intros. rewrite elem_of_union. right. set_solver.
    * rewrite elem_of_dom.
      intros.
      unfold inflow_insert_set.
      unfold inflow_map_set.
      simpl.
      rewrite lookup_partial_alter.
      rewrite <- not_eq_None_Some.
      discriminate.
  - split.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      rewrite H0.
      auto. auto.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      intros.
      destruct H1.
      rewrite H0.
      auto. auto. auto.
      set_solver.
Qed.      

Lemma flowint_inflow_insert_set_dom (I: multiset_flowint_ur) n S:
        dom (inflow_insert_set I n S) = dom I ∪ {[n]}.
Proof.
  unfold dom, flowint_dom.
  apply leibniz_equiv.
  apply set_equiv.
  intros n'.
  pose proof (inflow_map_set_ne (λ _ n, n + 1) I n S n').
  unfold inset, inf in H0.
  destruct (decide (n = n')).
  - rewrite <- e. split.
    * intros. rewrite elem_of_union. right. set_solver.
    * rewrite elem_of_dom.
      intros.
      unfold inflow_insert_set.
      unfold inflow_map_set.
      simpl.
      rewrite lookup_partial_alter.
      rewrite <- not_eq_None_Some.
      discriminate.
  - split.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      rewrite H0.
      auto. auto.
    * rewrite elem_of_union.
      repeat rewrite elem_of_dom.
      intros.
      destruct H1.
      rewrite H0.
      auto. auto. auto.
      set_solver.
Qed.

Lemma inflow_insert_set_insets I n S: 
           insets (inflow_insert_set I n S) = insets I ∪ S.
Proof.
  unfold insets.
  rewrite flowint_inflow_insert_set_dom.
  apply leibniz_equiv.
  destruct (decide (n ∈ dom I)).
  - assert (dom I ∪ {[n]} = dom I) as -> by set_solver.
    rewrite (big_opS_delete _ _ n); try done.
    rewrite (big_opS_delete _ (dom I) n); try done.
    rewrite inflow_insert_set_inset.
    assert (([^union set] y ∈ (dom I ∖ {[n]}), 
                            inset (inflow_insert_set I n S) y) =
            ([^union set] y ∈ (dom I ∖ {[n]}), inset I y)) as ->.
    { apply big_opS_ext. intros x Hx. 
      rewrite inflow_insert_set_inset_ne; try done.
      set_solver. }
    set_solver.
  - rewrite big_opS_union; last by set_solver.
    rewrite big_opS_singleton.
    rewrite inflow_insert_set_inset.
    assert (inset I n = ∅) as ->.
    { unfold inset, inf.
      unfold dom, flowint_dom in n0.
      rewrite not_elem_of_dom in n0.
      rewrite n0. simpl.
      unfold nzmap_dom. simpl.
      set_solver. }
    assert (([^union set] y ∈ dom I, 
                            inset (inflow_insert_set I n S) y) =
            ([^union set] y ∈ dom I, inset I y)) as ->.
    { apply big_opS_ext. intros x Hx.
      rewrite inflow_insert_set_inset_ne; try done.
      set_solver. }
    set_solver.
Qed.

Lemma inflow_insert_set_outsets I n S: 
           outsets (inflow_insert_set I n S) = outsets I.
Proof.
  unfold outsets.
  assert (dom (out_map (inflow_insert_set I n S)) = dom (out_map I)) as ->.
  { unfold inflow_insert_set, inflow_map_set, out_map. by simpl. }
  apply big_opS_ext. intros x Hx.
  try done.
Qed.

Lemma outflow_insert_set_insets I n S: 
           insets (outflow_insert_set I n S) = insets I.
Proof.
  unfold insets.
  assert (dom (outflow_insert_set I n S) = dom I) as ->.
  { unfold outflow_insert_set, inflow_map_set, inf_map. by simpl. }
  apply big_opS_ext. intros x Hx.
  try done.
Qed.

Lemma outflow_insert_set_outsets I n S: 
           outsets (outflow_insert_set I n S) = outsets I ∪ S.
Proof.
  unfold outsets.
  destruct (decide (out I n = ∅)) as [Hout | Hout];
    destruct (decide (S = ∅)) as [-> | HS].
  - assert (n ∉ dom (out_map I)). 
    { unfold out in Hout. rewrite nzmap_elem_of_dom_total.
      unfold ccmunit, ccm_unit. simpl. unfold lift_unit.
      intros H'; try done. }
    assert (dom (out_map (outflow_insert_set I n ∅)) = dom (out_map I)) as ->.
    { unfold outflow_insert_set, outflow_map_set, out_map at 1.
      simpl. apply leibniz_equiv.
      rewrite nzmap_dom_insert_zero.
      set_solver.
      unfold ccmunit, ccm_unit. simpl.
      unfold lift_unit, nzmap_map_set.
      rewrite set_fold_empty. rewrite Hout. done. }
    rewrite union_empty_r_L. 
    apply big_opS_ext. 
    intros x Hx. rewrite outflow_insert_set_outset_ne; try done.
    set_solver.
  - assert (dom (out_map (outflow_insert_set I n S)) = 
              dom (out_map I) ∪ {[n]}) as ->.
    { unfold outflow_insert_set, outflow_map_set, out_map at 1.
      simpl. apply leibniz_equiv.
      rewrite nzmap_dom_insert_nonzero.
      set_solver. rewrite Hout.
      unfold ccmunit, ccm_unit. simpl. unfold lift_unit.
      intros H'. rewrite nzmap_eq in H'.
      apply set_choose_L in HS.
      destruct HS as [k HS].
      pose proof H' k as H'.
      rewrite nzmap_lookup_empty in H'.
      rewrite nzmap_lookup_total_map_set in H'; try done. }
    apply leibniz_equiv.
    assert (n ∉ dom (out_map I)) as Hn.
    { unfold out in Hout. rewrite nzmap_elem_of_dom_total.
      unfold ccmunit, ccm_unit. simpl. unfold lift_unit.
      intros H'; try done. }
    rewrite big_opS_union; last by set_solver.
    rewrite big_opS_singleton.
    rewrite outflow_insert_set_outset.
    assert (outset I n = ∅) as ->.
    { unfold outset, out.
      rewrite nzmap_elem_of_dom in Hn.
      destruct (out_map I !! n) eqn: H'; try done.
      - exfalso; apply Hn. try done.
      - rewrite nzmap_lookup_total_alt.
        rewrite H'. simpl.
        set_solver. }
    assert (([^union set] y ∈ (dom (out_map I)), 
                            outset (outflow_insert_set I n S) y) =
            ([^union set] y ∈ (dom (out_map I)), outset I y)) as ->.
    { apply big_opS_ext. intros x Hx.
      rewrite outflow_insert_set_outset_ne; try done.
      set_solver. }
    set_solver.
  - assert (n ∈ dom (out_map I)) as Hn.
    { unfold out in Hout. by rewrite <-nzmap_elem_of_dom_total in Hout. } 
    assert (dom (out_map (outflow_insert_set I n ∅)) = dom (out_map I)) as ->.
    { unfold outflow_insert_set, outflow_map_set, out_map at 1.
      simpl. apply leibniz_equiv.
      rewrite nzmap_dom_insert_nonzero.
      set_solver.
      unfold ccmunit, ccm_unit. simpl.
      unfold lift_unit, nzmap_map_set.
      rewrite set_fold_empty. done. }
    rewrite union_empty_r_L. 
    apply big_opS_ext.
    intros x Hx. destruct (decide (x = n)) as [-> |Hxn].
    + rewrite outflow_insert_set_outset. set_solver.
    + rewrite outflow_insert_set_outset_ne; try done.
  - assert (dom (out_map (outflow_insert_set I n S)) = 
              dom (out_map I) ∪ {[n]}) as ->.
    { unfold outflow_insert_set, outflow_map_set, out_map at 1.
      simpl. apply leibniz_equiv.
      rewrite nzmap_dom_insert_nonzero.
      set_solver.
      unfold ccmunit, ccm_unit. simpl. unfold lift_unit.
      intros H'. rewrite nzmap_eq in H'.
      apply set_choose_L in HS.
      destruct HS as [k HS].
      pose proof H' k as H'.
      rewrite nzmap_lookup_empty in H'.
      unfold ccmunit, ccm_unit in H'. simpl in H'. unfold nat_unit in H'.
      rewrite nzmap_lookup_total_map_set in H'. lia. done. }  
    apply leibniz_equiv.
    destruct (decide (n ∈ dom (out_map I))).
    + assert (dom (out_map I) ∪ {[n]} = dom (out_map I)) as -> by set_solver.
      rewrite (big_opS_delete _ _ n); try done.
      rewrite (big_opS_delete _ (dom (out_map I)) n); try done.
      rewrite outflow_insert_set_outset.
      assert (([^union set] y ∈ (dom (out_map I) ∖ {[n]}), 
                              outset (outflow_insert_set I n S) y) =
              ([^union set] y ∈ (dom (out_map I) ∖ {[n]}), outset I y)) as ->.
      { apply big_opS_ext. intros x Hx. 
        rewrite outflow_insert_set_outset_ne; try done.
        set_solver. }
      set_solver.
    + rewrite big_opS_union; last by set_solver.
      rewrite big_opS_singleton.
      rewrite outflow_insert_set_outset.
      assert (outset I n = ∅) as ->.
      { unfold outset, out.
        rewrite nzmap_elem_of_dom in n0.
        destruct (out_map I !! n) eqn: H'; try done.
        - exfalso; apply n0. try done.
        - rewrite nzmap_lookup_total_alt.
          rewrite H'. simpl.
          set_solver. }
      assert (([^union set] y ∈ (dom (out_map I)), 
                              outset (outflow_insert_set I n S) y) =
              ([^union set] y ∈ (dom (out_map I)), outset I y)) as ->.
      { apply big_opS_ext. intros x Hx.
        rewrite outflow_insert_set_outset_ne; try done.
        set_solver. }
      set_solver.
Qed.

Lemma inflow_delete_set_outsets I n S: 
           outsets (inflow_delete_set I n S) = outsets I.
Proof.
  unfold outsets.
  assert (dom (out_map (inflow_delete_set I n S)) = dom (out_map I)) as ->.
  { unfold inflow_delete_set, inflow_map_set, out_map. by simpl. }
  apply big_opS_ext. intros x Hx.
  try done.
Qed.



Lemma outflow_delete_set_insets I n S: 
           insets (outflow_delete_set I n S) = insets I.
Proof.
  unfold insets.
  assert (dom (outflow_delete_set I n S) = dom I) as ->.
  { unfold outflow_delete_set, inflow_map_set, inf_map. by simpl. }
  apply big_opS_ext. intros x Hx.
  try done.
Qed.



Lemma outflow_map_set_valid2 I1 I2 I2' f n S : 
  I2' = outflow_map_set f I2 n S → 
    n ∉ dom I1 → n ∉ dom I2 → 
      dom I2 ≠ ∅ → 
        ✓ (I1 ⋅ I2) → 
          ✓ (I1 ⋅ I2').
Proof.
  intros Def_I2' n_notin_I1 n_notin_I2 I2_notEmpty Valid_12.
  assert (VValid_12 := Valid_12). 
  apply intValid_composable.
  apply intComposable_valid in Valid_12.
  destruct Valid_12 as [Valid1 [Valid2 [Domm_disj [MF1 MF2]]]].
  repeat split; try done.
  - rewrite Def_I2'. apply outflow_map_set_valid; try done.
  - rewrite Def_I2'. by rewrite flowint_outflow_map_set_domm.
  - rewrite map_Forall_lookup. intros n' x Hx.
    unfold inf. rewrite Hx; simpl.
    assert (n' ≠ n). 
    { assert (n' ∈ dom I1). 
      apply (flowint_contains _ _ _ x); try done.
      set_solver. }
    rewrite Def_I2'. unfold out. 
    rewrite outflow_map_set_out_map_ne; try done.
    fold (out I2 n').
    rewrite map_Forall_lookup in MF1.
    pose proof MF1 n' x Hx as MF1.
    unfold inf in MF1. rewrite Hx in MF1; 
    by simpl in MF1.
  - rewrite map_Forall_lookup. intros n' x Hx.
    unfold inf. rewrite Hx; simpl.
    rewrite map_Forall_lookup in MF2.
    assert (inf_map I2 !! n' = Some x) as H'.
    { subst I2'. by rewrite outflow_map_set_inf in Hx. }
    pose proof MF2 n' x H' as MF2.
    unfold inf in MF2. rewrite H' in MF2.
    by simpl in MF2. 
Qed.  

End multiset_flows.

Arguments multiset_flowint_ur _ {_ _} : assert.
Arguments inset _ {_ _} _ _ : assert.
Arguments outset _ {_ _} _ _ : assert.
Arguments in_inset _ {_ _} _ _ _ : assert.
Arguments in_outset _ {_ _} _ _ _ : assert.
Arguments in_outsets _ {_ _} _ _ : assert.
Arguments closed _ {_ _} _ : assert.
