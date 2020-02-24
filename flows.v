From iris.heap_lang Require Import proofmode.
From iris.algebra Require Export auth.

From stdpp Require Export gmap.
From stdpp Require Import mapset finite.
Require Export ccm gmap_more.

Require Import Coq.Setoids.Setoid.

(* ---------- Flow Interface encoding and camera definitions ---------- *)

Definition Node := nat.

Section flowint.

Context `{CCM flowdom}.

Open Scope ccm_scope.

Record flowintR :=
  {
    infR : gmap Node flowdom;
    outR : gmap Node flowdom;
  }.

Inductive flowintT :=
| int: flowintR → flowintT
| intUndef: flowintT.

Definition I_emptyR := {| infR := ∅; outR := ∅ |}.
Definition I_empty := int I_emptyR.
Instance flowint_empty : Empty flowintT := I_empty.


Definition out_map (I: flowintT) :=
  match I with
    | int Ir => outR Ir
    | intUndef => ∅
  end.

Definition inf_map (I: flowintT) :=
  match I with
    | int Ir => infR Ir
    | intUndef => ∅
  end.

Definition inf (I: flowintT) (n: Node) := default 0 (inf_map I !! n).
Definition out (I: flowintT) (n: Node) := default 0 (out_map I !! n).

Instance flowint_dom : Dom flowintT (gset Node) :=
  λ I, dom (gset Node) (inf_map I).
Definition domm (I : flowintT) := dom (gset Node) I.

Instance flowint_elem_of : ElemOf Node flowintT :=
  λ n I, n ∈ domm I.

(* Composition and proofs - some of these have counterparts in flows.spl in GRASShopper *)

Instance flowdom_eq_dec: EqDecision flowdom.
Proof.
  apply ccm_eq.
Qed.

Canonical Structure flowintRAC := leibnizO flowintT.

Instance int_eq_dec: EqDecision flowintT.
Proof.
  unfold EqDecision.
  unfold Decision.
  repeat decide equality.
  all: apply gmap_eq_eq.
Qed.

Instance flowint_valid : Valid flowintT :=
  λ I, match I with
       | int Ir =>
         infR Ir ##ₘ outR Ir
         ∧ (infR Ir = ∅ → outR Ir = ∅)
       | intUndef => False
       end.

Instance flowint_valid_dec : ∀ I: flowintT, Decision (✓ I).
Proof.
  intros.
  unfold valid; unfold flowint_valid.
  destruct I; last first.
  all: solve_decision.
Qed.

Definition intComposable (I1: flowintT) (I2: flowintT) :=
  ✓ I1 ∧ ✓ I2 ∧
  domm I1 ## domm I2 ∧
  map_Forall (λ (n: Node) (m: flowdom), m = out I2 n + (inf I1 n - out I2 n)) (inf_map I1) ∧
  map_Forall (λ (n: Node) (m: flowdom), m = out I1 n + (inf I2 n - out I1 n)) (inf_map I2).

Instance intComposable_dec (I1 I2: flowintT) : Decision (intComposable I1 I2).
Proof. solve_decision. Qed.

Definition outComp I1 I2 :=
  let f_out n o1 o2 : option flowdom :=
      match o1, o2 with
      | Some m1, None =>
        if decide (n ∈ (domm I2)) then None else Some m1
      | None, Some m2 =>
        if decide (n ∈ (domm I1)) then None else Some m2
      | Some m1, Some m2 => Some (m1 + m2)
      | _, _ => None
      end
  in
  gmap_imerge f_out (out_map I1) (out_map I2).

Lemma outComp_inv I1 I2 :
  ∀ n, n ∉ domm I1 ∪ domm I2 → default 0 (outComp I1 I2 !! n) = out I1 n + out I2 n.
Proof.
  intros n D.
  unfold outComp.
  rewrite gmap_imerge_prf.
  unfold out.
  destruct (decide (n ∈ domm I2)).
  set_solver.
  destruct (decide (n ∈ domm I1)).
  set_solver.
  destruct (out_map I1 !! n); destruct (out_map I2 !! n); simpl.
  all: auto using ccm_right_id, ccm_left_id.
Qed.


Instance intComp : Op flowintT :=
  λ I1 I2, if decide (intComposable I1 I2) then
             let f_inf n o1 o2 :=
                 match o1, o2 with
                 | Some m1, _ => Some (m1 - out I2 n)
                 | _, Some m2 => Some (m2 - out I1 n)
                 | _, _ => None
                 end
             in
             let inf12 := gmap_imerge f_inf (inf_map I1) (inf_map I2) in
             int {| infR := inf12; outR := outComp I1 I2 |}
           else if decide (I1 = ∅) then I2
           else if decide (I2 = ∅) then I1
           else intUndef.

Lemma intEmp_valid : ✓ I_empty.
Proof.
  unfold valid.
  unfold flowint_valid.
  unfold I_empty.
  simpl.
  split.
  refine (map_disjoint_empty_l _).
  trivial.
Qed.

Lemma intEmp_unique I : ✓ I → domm I ≡ ∅ → I = ∅.
Proof.
  intros V D.
  unfold valid, flowint_valid in V.
  destruct I as [Ir |].
  destruct V as (? & V).
  unfold domm, dom, flowint_dom, inf_map in D.
  unfold empty, flowint_empty, I_empty.
  apply f_equal.
  unfold I_emptyR.
  destruct Ir as [Iinf Iout].
  simpl in V.
  simpl in D.
  apply (dom_empty_inv Iinf) in D.
  pose proof (V D) as O.
  rewrite D.
  rewrite O.
  reflexivity.
  contradiction.
Qed.


Lemma intUndef_not_valid : ¬ ✓ intUndef.
Proof. unfold valid, flowint_valid; auto. Qed.

Lemma intComposable_invalid : ∀ I1 I2, ¬ ✓ I1 → ¬ (intComposable I1 I2).
Proof.
  intros.
  unfold intComposable.
  unfold not.
  intros H_false.
  destruct H_false as [H_false _].
  now contradict H_false.
Qed.

Lemma intComp_invalid : ∀ I1 I2: flowintT, ¬ ✓ I1 → ¬ ✓ (I1 ⋅ I2).
Proof.
  intros.
  unfold op, intComp.
  rewrite decide_False; last by apply intComposable_invalid.
  rewrite decide_False; last first.
  unfold not. intros H_false.
  contradict H0.
  rewrite H_false.
  apply intEmp_valid.
  destruct (decide (I2 = ∅)).
  auto.
  apply intUndef_not_valid.
Qed.


Lemma intComp_undef_op : ∀ I, intUndef ⋅ I ≡ intUndef.
Proof.
  intros.
  unfold op; unfold intComp.
  rewrite decide_False.
  unfold empty.
  unfold flowint_empty.
  rewrite decide_False.
  destruct (decide (I = I_empty)).
  1, 2: trivial.
  discriminate.
  unfold intComposable.
  cut (¬ (✓ intUndef)); intros.
  rewrite stdpp.base.LeftAbsorb_instance_0.
  trivial.
  unfold valid; unfold flowint_valid.
  auto.
Qed.

Lemma intComp_unit : ∀ (I: flowintT), I ⋅ I_empty ≡ I.
Proof.
  intros.
  unfold op, intComp, outComp.
  simpl.
  repeat rewrite gmap_imerge_empty.
  destruct I as [Ir|].
  destruct (decide (intComposable (int Ir) I_empty)).
  - (* True *)
    destruct Ir.
    simpl.
    auto.
  - (* False *)
    unfold empty, flowint_empty.
    destruct (decide (int Ir = I_empty)).
    auto.
    rewrite decide_True.
    all: auto.
  - unfold intComposable.
    rewrite decide_False.
    rewrite decide_False.
    rewrite decide_True.
    all: auto.
    unfold not; intros (H_false & _).
    contradict H_false.
  - intros.
    case y.
    2: auto.
    intros.
    case (gset_elem_of_dec i (domm I_empty)).
    2: auto.
    intros H_false; contradict H_false.
    unfold domm.
    replace I_empty with (empty : flowintT).
    replace (dom (gset Node) empty) with (empty : gset Node).
    apply not_elem_of_empty.
    symmetry.
    apply dom_empty_L.
    unfold empty.
    unfold flowint_empty.
    reflexivity.
  - intros.
    case y.
    intros.
    unfold out.
    rewrite lookup_empty.
    simpl.
    rewrite ccm_pinv_unit.
    all: easy.
Qed.

(*Lemma intComp_unit : ∀ (I: flowintT), I ⋅ I_empty ≡ I.
Proof.
  intros.
  assert (✓ I ∨ ¬ ✓ I).
  destruct (decide (✓ I)); auto.
  case H0; intro.
  - apply intComp_unit_valid. auto.
  - unfold op, intComp.
    destruct (decide (intComposable _ _)).
    * unfold intComposable in i.
      destruct i.
      contradiction.
    * destruct (decide _).
      trivial.
      destruct (decide _).
      trivial.
      assert (I_empty = ∅).
      trivial.
      contradiction.
Qed.*)


Lemma intComposable_comm_1 : ∀ (I1 I2 : flowintT), intComposable I1 I2 → intComposable I2 I1.
Proof.
  intros.
  unfold intComposable.
  repeat split.
  3: apply disjoint_intersection; rewrite intersection_comm_L; apply disjoint_intersection.
  unfold intComposable in H0.
  all: try apply H0.
Qed.

Lemma intComposable_comm : ∀ (I1 I2 : flowintT), intComposable I1 I2 ↔ intComposable I2 I1.
Proof.
  intros. split.
  all: refine (intComposable_comm_1 _ _).
Qed.

Lemma intComp_dom : ∀ I1 I2, ✓ (I1 ⋅ I2) → domm (I1 ⋅ I2) = domm I1 ∪ domm I2.
Proof.
  intros I1 I2 H_valid.
  unfold domm.
  set_unfold.
  intros.
  unfold dom.
  rewrite ?elem_of_dom.
  unfold op, intComp.
  case_eq (decide (intComposable I1 I2)).
  - intros H_comp H_comp_dec.
    rewrite gmap_imerge_prf; auto.
    case_eq (inf_map I1 !! x).
    + intros ? H1.
      (*rewrite H1.*)
      rewrite ?is_Some_alt; simpl.
      naive_solver.
    + intros H1.
      (*rewrite H1.*)
      case_eq (inf_map I2 !! x).
      * intros ? H2.
        (*rewrite H2.*)
        rewrite ?is_Some_alt; simpl.
        naive_solver.
      * intros H2.
        (*rewrite H2.*)
        split.
        apply or_introl.
        intros.
        destruct H.
        all: clear - H0; firstorder.
  - intros.
    case_eq (decide (I1 = ∅)).
    + intros H1 H1_dec.
      rewrite H1.
      simpl.
      rewrite lookup_empty.
      split.
      apply or_intror.
      intros H_or; destruct H_or as [H_false | H2].
      contradict H_false.
      exact is_Some_None.
      exact H2.
    + intros H1 H1_dec.
      case_eq (decide (I2 = ∅)).
      * intros H2 H2_dec.
        rewrite H2; simpl.
        rewrite lookup_empty.
        split.
        apply or_introl.
        intros H_or; destruct H_or.
        assumption.
        contradict H3.
        exact is_Some_None.
      * intros H2 H2_dec.
        contradict H_valid.
        unfold op, intComp.
        rewrite H0. rewrite H1_dec. rewrite H2_dec.
        exact intUndef_not_valid.
Qed.

Lemma intComp_comm : ∀ (I1 I2: flowintT), I1 ⋅ I2 ≡ I2 ⋅ I1.
Proof.
  intros.
  cut (∀ I, intUndef ⋅ I ≡ I ⋅ intUndef).
  intros H_undef_comm.
  destruct I1 as [ir1|] eqn:H_eq1, I2 as [ir2|] eqn:H_eq2; revgoals.
  all: try rewrite H_undef_comm; auto.
  unfold op, intComp, outComp; simpl.
  case_eq (decide (intComposable (int ir1) (int ir2))).
  - (* if composable *)
    intros H_comp H_comp_dec.
    rewrite decide_True; last rewrite intComposable_comm; auto.
    f_equal.
    f_equal.
    + (* infR equality *)
      rewrite map_eq_iff.
      intros.
      repeat rewrite gmap_imerge_prf; auto.
      case_eq (infR ir1 !! i).
      all: case_eq (infR ir2 !! i).
      * (* i in both *)
        intros f1 H_lookup2 f2 H_lookup1.
        exfalso.
        generalize H_comp.
        unfold intComposable.
        intros (_ & _ & H_false & _).
        unfold domm, dom, flowint_dom in H_false.
        simpl in *.
        rewrite <- map_disjoint_dom in H_false.
        generalize H_false. clear H_false.
        rewrite map_disjoint_alt.
        intros H_false.
        assert (H_contra := H_false i).
        destruct H_contra.
        contradict H0.
        now rewrite H_lookup1.
        contradict H0.
        now rewrite H_lookup2.
      * (* in I1 but not in I2 *)
        intros H_lookup2 f1 H_lookup1.
        (*rewrite H_lookup1. rewrite H_lookup2.*)
        auto.
      * (* in I2 but not in I1 *)
        intros f2 H_lookup2 H_lookup1.
        (*rewrite H_lookup1. rewrite H_lookup2.*)
        auto.
      * (* in neither *)
        intros H_lookup2 H_lookup1.
        (*rewrite H_lookup1. rewrite H_lookup2.*)
        auto.
    + (* outR equality *)
      rewrite map_eq_iff.
      intros.
      rewrite ?gmap_imerge_prf.
      case_eq (outR ir1 !! i).
      all: auto.
      * intros f1 H_lookup1.
        (*rewrite H_lookup1.*)
        case_eq (outR ir2 !! i).
        intros f2 H_lookup2.
        (*rewrite H_lookup2.*)
        f_equal.
        apply ccm_comm.
        intros H_lookup2.
        (*rewrite H_lookup2.*)
        auto.
  - (* if not composable *)
    intros H_not_comp H_not_comp_dec.
    symmetry.
    rewrite decide_False; last by rewrite intComposable_comm.
    case_eq (decide (int ir2 = ∅)).
    case_eq (decide (int ir1 = ∅)).
    all: auto.
    intros.
    now rewrite e e0.
  - (* proof of H_undef_comm *)
    intros.
    rewrite intComp_undef_op.
    unfold op, flowint_valid, intComp.
    rewrite decide_False.
    case (decide (I = ∅)).
    all: auto.
    intros _.
    rewrite decide_False.
    all: auto.
    unfold intComposable.
    rewrite ?not_and_l.
    right. left.
    exact intUndef_not_valid.
Qed.

Lemma intComp_unit2 : ∀ I : flowintT, ✓ I → I_empty ⋅ I ≡ I.
Proof.
  intros.
  rewrite intComp_comm.
  now apply intComp_unit.
Qed.

Lemma intComp_valid_proj1 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I1.
Proof.
  intros I1 I2.
  rewrite <- Decidable.contrapositive.
  apply intComp_invalid.
  unfold Decidable.decidable.
  generalize (flowint_valid_dec I1).
  unfold Decision.
  intros.
  destruct H0.
  all: auto.
Qed.

Lemma intComp_valid_proj2 : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → ✓ I2.
Proof.
  intros I1 I2.
  rewrite intComp_comm.
  apply intComp_valid_proj1.
Qed.

Lemma intComp_positive_1 : ∀ (I1 I2: flowintT), I1 ⋅ I2 = ∅ → I1 = ∅.
Proof.
  intros ? ? C.
  pose proof intEmp_valid as V.
  unfold empty, flowint_empty in C.
  rewrite <- C in V.
  pose proof (intComp_valid_proj1 _ _ V) as V1.
  pose proof (intComp_valid_proj2 _ _ V) as V2.
  assert (inf_map I1 = ∅) as D1.
  apply map_eq.
  intros n.
  assert (inf_map (I1 ⋅ I2) !! n = inf_map (I_empty) !! n) as CL.
    by rewrite C; reflexivity.
  unfold op, intComp in CL.
  unfold op, intComp in C.
  destruct (decide (intComposable I1 I2)).
  - unfold inf_map at 1 in CL. simpl in CL.
    rewrite gmap_imerge_prf in CL.
    rewrite lookup_empty.
    rewrite lookup_empty in CL.
    destruct (inf_map I1 !! n);
      destruct (inf_map I2 !! n);
      inversion CL.
    reflexivity.
    trivial.
  - destruct (decide (I1 = ∅)).
    * rewrite e.
      unfold inf_map, empty at 1, flowint_empty, I_empty, I_emptyR.
      simpl.
      reflexivity.
    * destruct (decide (I2 = ∅)).
      + unfold empty, flowint_empty in n1.
        contradiction.
      + unfold I_empty in C.
        inversion C.
  - assert (domm I1 ≡ ∅).
    unfold domm, dom, flowint_dom.
    rewrite D1.
    rewrite dom_empty.
    reflexivity.
    pose proof (intEmp_unique _ V1 H0).
    trivial.
Qed.

Lemma intComp_positive_2 : ∀ (I1 I2: flowintT), I1 ⋅ I2 = ∅ → I2 = ∅.
Proof.
  intros ? ? C.
  rewrite intComp_comm in C *.
  apply intComp_positive_1.
Qed.

Lemma intComposable_empty : ∀ I: flowintT, ✓ I → intComposable ∅ I.
Proof.
  intros I IV.
  case_eq I; last first.
  intros.
  rewrite H0 in IV.
  unfold valid, flowint_valid in IV.
  contradiction.
  intros Ir Idef.
  rewrite <- Idef.
  unfold intComposable.
  repeat split.
  - trivial.
  - unfold domm, dom, flowint_dom, inf_map, empty, flowint_empty, I_empty, I_emptyR. simpl.
    rewrite dom_empty.
    apply disjoint_empty_l.
  - unfold map_Forall.
    intros n x.
    unfold inf_map, empty, flowint_empty, I_empty, I_emptyR. simpl.
    rewrite lookup_empty.
    intros.
    inversion H0.
  - unfold map_Forall.
    intros n x.
    intros.
    unfold out, out_map, empty, flowint_empty, I_empty, I_emptyR. simpl.
    rewrite lookup_empty.
    unfold default.
    rewrite ccm_left_id.
    unfold inf.
    rewrite H0.
    simpl.
    rewrite <- (ccm_right_id x) at 2.
    auto using ccm_pinv.
Qed.

Lemma intComposable_valid : ∀ (I1 I2: flowintT), ✓ (I1 ⋅ I2) → intComposable I1 I2.
Proof.
  intros I1 I2 IV.
  pose proof (intComp_valid_proj1 I1 I2 IV) as I1V.
  pose proof (intComp_valid_proj2 I1 I2 IV) as I2V.
  case_eq (I1 ⋅ I2).
  - intros Ir Idef.
    unfold op, intComp in Idef.
    destruct (decide (intComposable I1 I2)).
    trivial.
    destruct (decide (I1 = ∅)).
    pose proof (intComposable_empty I2).
    apply H0 in I2V.
    rewrite e.
    trivial.
    destruct (decide (I2 = ∅)).
    pose proof (intComposable_empty I1).
    apply H0 in I1V.
    rewrite intComposable_comm.
    rewrite e.
    trivial.
    inversion Idef.
  - intros.
    rewrite H0 in IV.
    unfold valid, flowint_valid in IV.
    contradiction.
Qed.

Lemma intValid_composable : ∀ (I1 I2: flowintT), intComposable I1 I2 → ✓ (I1 ⋅ I2).
Proof.
  intros ? ? V.
  unfold op, intComp.
  destruct (decide (intComposable I1 I2)).
  unfold valid, flowint_valid.
  simpl.
  split.
  rewrite map_disjoint_spec.
  intros.
  rewrite gmap_imerge_prf in H0.
  rewrite gmap_imerge_prf in H1.
  unfold intComposable in V.
  destruct V as (V1 & V2 & Dom12 & _).
  unfold valid, flowint_valid in V1.
  destruct I1 as [I1r |].
  destruct V1 as (D1 & IO1).
  rewrite map_disjoint_alt in D1 *.
  intros D1.
  pose proof (D1 i0) as D1i0.
  
  unfold valid, flowint_valid in V2.
  destruct I2 as [I2r |].
  destruct V2 as (D2 & IO2).
  rewrite map_disjoint_alt in D2 *.
  intros D2.
  pose proof (D2 i0) as D2i0.
  rewrite elem_of_disjoint in Dom12 *.
  intros Dom12.
  pose proof (Dom12 i0) as Dom12i0.
  (*unfold domm, dom, flowint_dom in Dom12i0.*)
  (*repeat (rewrite elem_of_dom in Dom12i0 *;
          intros Dom12i0).*)
  unfold inf_map in Dom12i0.
  unfold inf_map in H0.
  (*unfold domm, dom, flowint_dom in H1.*)
  unfold out_map, inf_map in H1.
  destruct (decide (i0 ∈ domm (int I1r))) as [e | e];
  destruct (decide (i0 ∈ domm (int I2r))) as [n | n].
  pose proof Dom12i0 e n; trivial.
  all: try (unfold domm, dom, flowint_dom, inf_map in e).
  all: try (unfold domm, dom, flowint_dom, inf_map in n).
  all: try (rewrite elem_of_dom in e *; intros e).
  all: try (rewrite elem_of_dom in n *; intros n).
  all: try (unfold is_Some in e).
  all: try (unfold is_Some in n).
    
  all: try (destruct (outR I1r !! i0);
    destruct (outR I2r !! i0);
    destruct (infR I1r !! i0);
    destruct (infR I2r !! i0);
    first [destruct D2i0; inversion H2; destruct D1i0; inversion H1; inversion H2; inversion H3; inversion H0
           ; try apply Dom12i0 in e; trivial]).
  all: try (destruct e as [? e]; inversion e).
  all: try (destruct n as [? n]; inversion n).
  all: try (assert (∃ x, Some f0 = Some x); try (exists f0; reflexivity); try contradiction).
  contradiction.
  contradiction.
  trivial.
  trivial.

  intros.
  apply map_eq.
  intros n.
  rewrite gmap_imerge_prf.
  rewrite lookup_empty.

  assert (∀ x, inf_map (I1 ⋅ I2) !! x = None).
  intros x.
  unfold inf_map, op, intComp.
  destruct (decide (intComposable I1 I2)).
  simpl.
  rewrite H0.
  rewrite lookup_empty.
  reflexivity.
  contradiction.

  
  assert (domm I1 ≡ ∅) as DI1.
  unfold domm, dom, flowint_dom.
  rewrite elem_of_equiv.
  intros.
  rewrite elem_of_empty.
  split.
  intro D.
  pose proof (H1 x).
  unfold inf_map, op, intComp in H2.
  destruct (decide (intComposable I1 I2)).
  simpl in H1.
  rewrite gmap_imerge_prf in H2.
  rewrite elem_of_dom in D *.
  intros D.
  unfold is_Some in D.
  destruct D as [y D].
  rewrite D in H2.
  inversion H2.
  trivial.
  contradiction.
  contradiction.

  assert (domm I2 ≡ ∅) as DI2.
  unfold domm, dom, flowint_dom.
  rewrite elem_of_equiv.
  intros.
  rewrite elem_of_empty.
  split.
  intro D.
  pose proof (H1 x).
  unfold inf_map, op, intComp in H2.
  destruct (decide (intComposable I1 I2)).
  simpl in H1.
  rewrite gmap_imerge_prf in H2.
  rewrite elem_of_dom in D *.
  intros D.
  unfold is_Some in D.
  destruct D as [y D].
  rewrite D in H2.
  inversion H2.
  destruct (inf_map I1 !! x); inversion H2.
  trivial.
  contradiction.
  contradiction.
  
  unfold intComposable in V.
  destruct V as (V1 & V2 & _).
  unfold valid, flowint_valid in V1.
  destruct I1.
  destruct V1 as (Disj1 & E1).
  unfold domm, dom, flowint_dom in DI1.
  apply dom_empty_inv in DI1.
  unfold inf_map in DI1.
  apply E1 in DI1.
  unfold out_map.
  rewrite DI1.
  rewrite lookup_empty.
  unfold valid, flowint_valid in V2.
  destruct I2.
  destruct V2 as (Disj2 & E2).
  unfold domm, dom, flowint_dom in DI2.
  apply dom_empty_inv in DI2.
  unfold inf_map in DI2.
  apply E2 in DI2.
  rewrite DI2.
  rewrite lookup_empty.
  reflexivity.
  contradiction.
  contradiction.
  trivial.
  contradiction.
Qed.
  
Lemma intComp_unfold_inf_1 : ∀ (I1 I2: flowintT),
    ✓ (I1 ⋅ I2) →
    ∀ n, n ∈ domm I1 → inf I1 n = inf (I1 ⋅ I2) n + out I2 n.
Proof.
  intros I1 I2 V n D.
  unfold domm, dom, flowint_dom in D.
  apply elem_of_dom in D.
  unfold is_Some in D.
  destruct D as [x D].
  pose proof (intComposable_valid I1 I2 V).
  assert (IC := H0).
  unfold intComposable in H0.
  destruct H0 as (I1v & I2v & Disjoint & I1inf & I2inf).
  unfold map_Forall in I1inf.
  pose proof (I1inf n (inf I1 n)).
  unfold inf in H0.
  rewrite D in H0.
  unfold default, id in H0.
  assert (Some x = Some x) by reflexivity.
  apply H0 in H1.
  unfold valid, flowint_valid in V.
  case_eq (I1 ⋅ I2).
  - intros Ir Idef. rewrite Idef in V.
    unfold op, intComp in Idef.
    destruct (decide (intComposable I1 I2)).
    + unfold inf.
      rewrite <- Idef.
      unfold inf_map at 1; simpl.
      rewrite gmap_imerge_prf.
      * rewrite D.
        unfold default, id.
        rewrite ccm_comm in H1.
        trivial.
      * intro.
        trivial.
    + contradiction.
  - intros.
    rewrite H2 in V.
    contradiction.
Qed.

Lemma intComp_unfold_inf_2 : ∀ (I1 I2: flowintT),
    ✓ (I1 ⋅ I2) →
    ∀ n, n ∈ domm I2 → inf I2 n = inf (I1 ⋅ I2) n + out I1 n.
Proof.
  intros.
  rewrite intComp_comm.
  apply intComp_unfold_inf_1.
  rewrite intComp_comm.
  trivial.
  exact H1.
Qed.

Lemma intComp_unfold_out I1 I2 :
  ✓ (I1 ⋅ I2) → (∀ n, n ∉ domm (I1 ⋅ I2) → out (I1 ⋅ I2) n = out I1 n + out I2 n).
Proof.
  intros.
  apply intComp_dom in H0 as D.
  rewrite D in H1.
  pose proof (outComp_inv I1 I2 n H1).
  apply intComposable_valid in H0.
  unfold op, intComp, out at 1, out_map at 1.
  destruct (decide (intComposable I1 I2)); last first.
  contradiction.
  simpl.
  trivial.
Qed.

Lemma intComp_inf_1 I1 I2 :
  ✓ (I1 ⋅ I2) → (∀ n, n ∈ domm I1 → inf (I1 ⋅ I2) n = inf I1 n - out I2 n).
Proof.
  intros V n D.
  apply intComposable_valid in V.
  unfold op, intComp.
  destruct (decide (intComposable I1 I2)); last first.
  contradiction.
  unfold inf at 1, inf_map at 1.
  simpl.
  rewrite gmap_imerge_prf.
  unfold domm, dom, flowint_dom in D.
  apply elem_of_dom in D.
  unfold is_Some in D.
  destruct D as [x D].
  unfold inf at 1.
  rewrite D.
  simpl.
  reflexivity.
  trivial.
Qed.

Lemma intComp_inf_2 I1 I2 :
  ✓ (I1 ⋅ I2) → (∀ n, n ∈ domm I2 → inf (I1 ⋅ I2) n = inf I2 n - out I1 n).
Proof.
  intros.
  rewrite intComp_comm.
  generalize H1.
  generalize n.
  rewrite intComp_comm in H0 *.
  apply intComp_inf_1.
Qed.


Lemma intComp_fold I1 I2 I :
  I ≠ intUndef → ✓ I1 → ✓ I2 →
  domm I1 ## domm I2 →
  domm I = domm I1 ∪ domm I2 →
  (∀ n, n ∈ domm I1 → inf I1 n = out I2 n + inf I n) →
  (∀ n, n ∈ domm I2 → inf I2 n = out I1 n + inf I n) →
  out_map I = outComp I1 I2 →
  I = I1 ⋅ I2 ∧ ✓ (I1 ⋅ I2).
Proof.
  intros Iint V1 V2 Disj D Inf1 Inf2 Out.
  assert (intComposable I1 I2) as C.
  { unfold intComposable.
    repeat split; try trivial.
    - unfold map_Forall.
      intros n x xDef.
      unfold domm, dom, flowint_dom in Inf1.
      pose proof (Inf1 n).
      rewrite elem_of_dom in H0 *.
      intro.
      apply mk_is_Some in xDef as H1.
      apply H0 in H1.
      rewrite H1.
      rewrite (ccm_comm _ (inf I n)).
      rewrite ccm_pinv.
      unfold inf at 1 in H1.
      rewrite xDef in H1.
      simpl in H1.
      rewrite H1.
      reflexivity.
    - unfold map_Forall.
      intros n x xDef.
      unfold domm, dom, flowint_dom in Inf2.
      pose proof (Inf2 n).
      rewrite elem_of_dom in H0 *.
      intro.
      apply mk_is_Some in xDef as H1.
      apply H0 in H1.
      rewrite H1.
      rewrite (ccm_comm _ (inf I n)).
      rewrite ccm_pinv.
      unfold inf at 1 in H1.
      rewrite xDef in H1.
      simpl in H1.
      rewrite H1.
      reflexivity.
  }
  split.
  apply intValid_composable in C.
  destruct I as [Ir |].
  unfold op, intComp.
  destruct (decide (intComposable I1 I2)).
  f_equal.
  case_eq Ir.
  intros.
  f_equal.
  - apply map_eq.
    intros n.
    rewrite gmap_imerge_prf.
    case_eq (inf_map I1 !! n).
    + intros x xDef.
      assert (n ∈ domm I1) as nI1.
      apply mk_is_Some in xDef.
      unfold domm, dom, flowint_dom.
      apply elem_of_dom.
      trivial.
      assert (n ∈ domm (int Ir)) as nI.
      set_solver.
      unfold domm, dom, flowint_dom in nI.
      apply elem_of_dom in nI.
      unfold is_Some in nI.
      destruct nI as [y nI].
      unfold inf_map in nI.
      rewrite H0 in nI.
      simpl in nI.
      rewrite nI.
      f_equal.
      pose proof (Inf1 _ nI1) as In1n.
      unfold inf in In1n.
      rewrite xDef in In1n.
      simpl in In1n.
      rewrite ccm_comm in In1n.
      rewrite In1n.
      rewrite H0.
      simpl.
      rewrite nI.
      auto using ccm_pinv.
    + intros.
      assert (n ∉ domm I1).
      unfold domm, dom, flowint_dom.
      rewrite elem_of_dom.
      rewrite H1.
      apply is_Some_None.
      case_eq (inf_map I2 !! n).
      * intros x xDef.
        assert (n ∈ domm I2) as nI2.
        apply mk_is_Some in xDef.
        unfold domm, dom, flowint_dom.
        apply elem_of_dom.
        trivial.
        assert (n ∈ domm (int Ir)) as nI.
        set_solver.
        unfold domm, dom, flowint_dom in nI.
        apply elem_of_dom in nI.
        unfold is_Some in nI.
        destruct nI as [y nI].
        unfold inf_map in nI.
        rewrite H0 in nI.
        simpl in nI.
        rewrite nI.
        f_equal.
        pose proof (Inf2 _ nI2) as In2n.
        unfold inf in In2n.
        rewrite xDef in In2n.
        simpl in In2n.
        rewrite ccm_comm in In2n.
        rewrite In2n.
        rewrite H0.
        simpl.
        rewrite nI.
        auto using ccm_pinv.
      * intros.
        assert (n ∉ domm I2).
        unfold domm, dom, flowint_dom.
        rewrite elem_of_dom.
        rewrite H3.
        apply is_Some_None.
        assert (n ∉ domm (int Ir)).
        set_solver.
        unfold domm, dom, flowint_dom, inf_map in H5.
        rewrite elem_of_dom in H5 *.
        intros.
        rewrite H0 in H5.
        simpl in H5.
        rewrite <- eq_None_not_Some in H5.
        trivial.
    + trivial.
  - unfold out_map in Out.
    rewrite H0 in Out.
    simpl in Out.
    trivial.
  - apply intComposable_valid in C.
    contradiction.
  - contradiction.
  - apply intValid_composable in C. trivial.
Qed.

(*
Lemma intComp_out_None I1 I2 : ✓ (I1 ⋅ I2) → ∀ n, out_map (I1 ⋅ I2) !! n = None → out_map I1 !! n = None ∨ out_map I2 !! n = None.
Proof.
  intros.
  apply intComposable_valid in H0.
  unfold op, intComp in H1.
  destruct (decide (intComposable I1 I2)).
  unfold out_map in H1.
  simpl in H1.
  unfold outComp in H1.
  rewrite gmap_imerge_prf in H1.
  unfold intComposable in H0.
  destruct H0 as (_ & _ & Disj & _).
  case_eq (out_map I1 !! n);
    try intros x1 x1Def; try intros x1Def;
      case_eq (out_map I2 !! n);
      try intros x2 x2Def; try intros x2Def;
  rewrite x1Def in H1;
    rewrite x2Def in H1;
    destruct (decide (n ∈ domm I2)); 
    destruct (decide (n ∈ domm I1)); 
    try inversion H1.
  all: try (right; reflexivity).
  all: try (left; reflexivity).
  trivial.
  contradiction.
Qed.

Lemma intValid_out_not_dom I : ✓ I → ∀ n, is_Some (out_map I !! n) → n ∉ domm I.
Proof.
  intros V ? O.
  unfold valid, flowint_valid in V.
  destruct I.
  destruct V as (D & _).
  assert (dom (gset Node) (infR f) ## dom (gset Node) (outR f)).
  apply map_disjoint_dom.
  trivial.
  assert (n ∈ dom (gset Node) (outR f)).
  rewrite elem_of_dom.
  unfold out_map in O.
  trivial.
  set_solver.
  contradiction.
Qed.
 *)

Lemma intComp_assoc_valid (I1 I2 I3 : flowintT) : ✓ (I1 ⋅ (I2 ⋅ I3)) → I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.
Proof.
  intros V.
  remember (I1 ⋅ (I2 ⋅ I3)) as I.
  remember (I2 ⋅ I3) as I23.
  remember (outComp I1 I2) as out12.
  remember (gmap_imerge (λ n o1 o2,
                         match o1, o2 with
                         | Some _, _ => Some (inf I n + out I3 n)
                         | _, Some _ => Some (inf I n + out I3 n)
                         | None, None => None
                         end)
                        (inf_map I1) (inf_map I2)) as inf12.
  remember (int {| infR := inf12; outR := out12 |}) as I12.
  rewrite HeqI in V.
  apply intComp_valid_proj1 in V as V1.
  apply intComp_valid_proj2 in V as V23.
  rewrite HeqI23 in V23.
  apply intComp_valid_proj1 in V23 as V2.
  apply intComp_valid_proj2 in V23 as V3.
  apply intComposable_valid in V as C.
  apply intComposable_valid in V23 as C23.
  assert (CU := C).
  unfold intComposable in CU.
  destruct CU as (_ & _ & Disj & Inf1 & Inf23).
  assert (CU23 := C23).
  unfold intComposable in CU23.
  destruct CU23 as (_ & _ & Disj23 & Inf2 & Inf3).
  apply intComp_dom in V as D.
  apply intComp_dom in V23 as D23.
  rewrite HeqI23 in Disj.
  rewrite D23 in Disj.
  unfold map_Forall in Inf1.
  unfold map_Forall in Inf23.
  unfold map_Forall in Inf2.
  unfold map_Forall in Inf3.
  assert (I12 ≡ I1 ⋅ I2 ∧ ✓ (I1 ⋅ I2)) as I12Def.
  { apply intComp_fold.
    - rewrite HeqI12. auto.
    - trivial.
    - trivial.
    - set_solver.
    - rewrite elem_of_equiv_L.
      intros n.
      rewrite elem_of_union.
      split.
      * intros nD.
        unfold domm, dom, flowint_dom, inf_map in nD.
        rewrite HeqI12 in nD.
        simpl in nD.
        rewrite Heqinf12 in nD.
        rewrite elem_of_dom in nD *.
        intros nD.
        rewrite gmap_imerge_prf in nD.
        unfold domm, dom, flowint_dom.
        repeat rewrite elem_of_dom.
        destruct (inf_map I1 !! n).
        unfold is_Some.
        left.
        exists f.
        reflexivity.
        destruct (inf_map I2 !! n).
        right.
        exists f.
        reflexivity.
        apply is_Some_None in nD.
        contradiction.
        trivial.
      * intros nD.
        unfold domm, dom, flowint_dom, inf_map.
        rewrite HeqI12.
        simpl.
        rewrite Heqinf12.
        rewrite elem_of_dom.
        rewrite gmap_imerge_prf.
        destruct nD as [nD | nD];
        unfold domm, dom, flowint_dom in nD;
        rewrite elem_of_dom in nD *;
        intros nD;
        unfold is_Some in nD;
        destruct nD as [x nD];
        rewrite nD;
        destruct (inf_map I1 !! n);
        apply not_eq_None_Some;
        auto.
        trivial.
    - intros ? n_in_I1.
      assert (n_in_I11 := n_in_I1).
      unfold domm, dom, flowint_dom in n_in_I11.
      apply elem_of_dom in n_in_I11.
      unfold is_Some in n_in_I11.
      destruct n_in_I11 as [x n_inf].
      apply Inf1 in n_inf as xDef.
      unfold inf at 2.
      rewrite HeqI12.
      unfold inf_map.
      simpl.
      rewrite Heqinf12.
      rewrite gmap_imerge_prf.
      rewrite n_inf.
      simpl.
      rewrite HeqI.
      pose proof (intComp_inf_1 _ _ V _ n_in_I1).
      rewrite H0.
      unfold inf at 2.
      rewrite n_inf.
      simpl.
      rewrite xDef.
      rewrite (ccm_comm (out I23 n)).
      rewrite ccm_pinv.
      rewrite ccm_comm.
      rewrite <- ccm_assoc.
      rewrite (ccm_comm (out I3 n)).
      assert (n ∉ domm (I2 ⋅ I3)).
      rewrite D23.
      set_solver.
      apply intComp_unfold_out in H1.
      unfold inf at 1.
      rewrite n_inf.
      simpl.
      rewrite xDef.
      rewrite ccm_comm.
      rewrite <- H1.
      rewrite <- HeqI23.
      reflexivity.
      trivial.
      trivial.
    - intros ? n_in_I2.
      assert (n_in_I21 := n_in_I2).
      unfold domm, dom, flowint_dom in n_in_I21.
      apply elem_of_dom in n_in_I21.
      unfold is_Some in n_in_I21.
      destruct n_in_I21 as [x n_inf].
      apply Inf2 in n_inf as xDef.
      unfold inf at 2.
      rewrite HeqI12.
      unfold inf_map.
      simpl.
      rewrite Heqinf12.
      rewrite gmap_imerge_prf.
      rewrite n_inf.
      simpl.
      rewrite HeqI.
      assert (n ∈ domm I2 ∪ domm I3) as n_in_I23.
      set_solver.
      rewrite <- D23 in n_in_I23.
      rewrite <- HeqI23 in n_in_I23.
      unfold inf at 2.
      assert (n ∉ domm I1) as n_nin_I1.
      set_solver.
      unfold domm, dom, flowint_dom in n_nin_I1.
      rewrite elem_of_dom in n_nin_I1 *.
      intros n_nin_I1.
      rewrite <- eq_None_not_Some in n_nin_I1.
      rewrite n_nin_I1.
      simpl.
      rewrite ccm_comm.
      rewrite <- ccm_assoc.
      rewrite (ccm_comm (out I3 n)).
      rewrite ccm_assoc.
      pose proof (intComp_unfold_inf_2 I1 I23 V n n_in_I23).
      rewrite <- H0.
      pose proof (intComp_unfold_inf_1 I2 I3 V23 n n_in_I2).
      rewrite H1.
      rewrite HeqI23.
      reflexivity.
      trivial.
    - rewrite HeqI12.
      unfold out_map.
      auto. }
  destruct I12Def as (I12Def & V12).
  assert (I ≡ I12 ⋅ I3) as IDef.
  { apply intComp_fold.
    - rewrite HeqI.
      destruct (I1 ⋅ I23).
      * auto.
      * apply intUndef_not_valid in V.
        contradiction.
    - rewrite <- I12Def in V12.
      trivial.
    - trivial.
    - rewrite I12Def.
      rewrite intComp_dom.
      set_solver.
      trivial.
    - rewrite I12Def.
      rewrite intComp_dom.
      rewrite HeqI.
      rewrite D.
      rewrite HeqI23.
      rewrite D23.
      set_solver.
      trivial.
    - intros n nI12.
      rewrite HeqI12.
      unfold inf at 1, inf_map.
      simpl.
      rewrite Heqinf12.
      rewrite gmap_imerge_prf.
      rewrite I12Def in nI12 *.
      intro nI12.
      rewrite intComp_dom in nI12.
      rewrite elem_of_union in nI12 *.
      intro nI12.
      destruct nI12 as [nI1 | nI2].
      * unfold domm, dom, flowint_dom in nI1.
        apply elem_of_dom in nI1.
        unfold is_Some in nI1.
        destruct nI1 as [x nI1].
        rewrite nI1.
        simpl.
        auto using ccm_comm.
      * destruct (inf_map I1 !! n).
        ** simpl.
           auto using ccm_comm.
        ** unfold domm, dom, flowint_dom in nI2.
           apply elem_of_dom in nI2.
           unfold is_Some in nI2.
           destruct nI2 as [x nI2].
           rewrite nI2.
           simpl.
           auto using ccm_comm.
      * trivial.
      * trivial.
    - intros n nI3.
      assert (n ∉ domm I1 ∪ domm I2) as n_not_I12.
      set_solver.
      rewrite <- intComp_dom in n_not_I12.
      pose proof (intComp_unfold_out I1 I2 V12 n n_not_I12).
      rewrite I12Def.
      rewrite H0.
      assert (n ∈ domm I23) as nI23.
      set_solver.
      pose proof (intComp_unfold_inf_2 I1 I23 V n nI23).
      rewrite <- HeqI in H1.
      rewrite ccm_comm.
      rewrite ccm_assoc.
      rewrite <- H1.
      pose proof (intComp_unfold_inf_2 I2 I3 V23 n nI3).
      rewrite <- HeqI23 in H2.
      rewrite <- H2.
      reflexivity.
      trivial.
    - rewrite HeqI.
      unfold op, intComp.
      destruct (decide (intComposable I1 I23)); last first.
      contradiction.
      simpl.
      unfold outComp.
      apply map_eq.
      intros n.
      repeat rewrite gmap_imerge_prf.
      pose proof (intComp_unfold_out I1 I2 V12 n).
      rewrite <- I12Def in H0.
      pose proof (intComp_unfold_out I2 I3 V23 n).
      rewrite <- HeqI23 in H1.
      unfold out in H0.
      unfold out in H1.
      rewrite HeqI23.
      rewrite D23.
      assert (I12 = I1 ⋅ I2) as I12def.
      rewrite I12Def; reflexivity.
      rewrite I12def.
      pose proof (intComp_dom _ _ V12) as D12.
      rewrite D12.
      
      unfold op, intComp.
      destruct (decide (intComposable I2 I3)); last first.
      contradiction.
      unfold out_map at 2. simpl.
      destruct (decide (intComposable I1 I2)); last first.
      apply intComposable_valid in V12.
      contradiction.
      unfold out_map at 2. simpl.
      unfold outComp.
      repeat rewrite gmap_imerge_prf.
      
      destruct (decide (n ∈ domm I1 ∪ domm I2)) as [n_in_I12 | n_nin_I12];      
      try (rewrite not_elem_of_union in n_nin_I12 *;
           intros n_nin_I12;
           destruct n_nin_I12 as (n_nin_I1 & n_nin_I2));
      try (rewrite elem_of_union in n_in_I12 *;
           intros n_in_I12;
           destruct n_in_I12 as [n_in_I1 | n_in_I2]);
      destruct (decide (n ∈ domm I1));
      destruct (decide (n ∈ domm I2));
      try contradiction;
      destruct (decide (n ∈ domm I2 ∪ domm I3)) as [n_in_I23 | n_nin_I23];      
      try (rewrite not_elem_of_union in n_nin_I23 *;
           intros n_nin_I23;
           destruct n_nin_I23 as (n_nin_I2_2 & n_nin_I3));
      try (rewrite elem_of_union in n_in_I23 *;
           intros n_in_I23;
           destruct n_in_I23 as [n_in_I2_2 | n_in_I3]);
      destruct (decide (n ∈ domm I3));
      try contradiction;
      destruct (out_map I1 !! n);
        destruct (out_map I2 !! n);
        destruct (out_map I3 !! n);
      try rewrite ccm_assoc;
      try reflexivity.
      all: trivial.
  }

  rewrite I12Def in IDef *.
  intros.
  trivial.
Qed.

Lemma intComp_assoc_invalid (I1 I2 I3 : flowintT) : ¬(✓ (I1 ⋅ (I2 ⋅ I3))) → ¬(✓ (I1 ⋅ I2 ⋅ I3)) → I1 ⋅ (I2 ⋅ I3) ≡ I1 ⋅ I2 ⋅ I3.
Proof.
  intros IV1 IV2.
  pose proof (intValid_composable I1 (I2 ⋅ I3)) as NC1.
  rewrite <- Decidable.contrapositive in NC1.
  pose proof (NC1 IV1).
  pose proof (intValid_composable (I1 ⋅ I2) I3) as NC2.
  rewrite <- Decidable.contrapositive in NC2.
  pose proof (NC2 IV2).
  all: try (unfold Decidable.decidable; auto).

  destruct (decide (I1 = ∅)).
  - rewrite e.
    rewrite intComp_comm.
    rewrite intComp_unit.
    rewrite (intComp_comm _ I2).
    rewrite intComp_unit.
    reflexivity.
  - destruct (decide (I2 = ∅)).
    + rewrite e.
      rewrite (intComp_comm _ I3).
      repeat rewrite intComp_unit.
      reflexivity.
    + destruct (decide ((I1 ⋅ I2) = ∅)).
      apply intComp_positive_1 in e.
      contradiction.
      * destruct (decide ((I2 ⋅ I3) = ∅)).
        ** apply intComp_positive_1 in e.
           contradiction.
        ** destruct (decide (I3 = empty)).
           rewrite e.
           repeat rewrite intComp_unit.
           reflexivity.
           unfold op at 1, intComp at 1.
           destruct (decide (intComposable I1 (I2 ⋅ I3))).
           apply H0 in i.
           contradiction.
           unfold op at 8, intComp.
           destruct (decide (intComposable (I1 ⋅ I2) I3)).
           apply H1 in i.
           contradiction.
           destruct (decide (I1 = ∅)); try contradiction.
           destruct (decide (I2 ⋅ I3 = ∅)); try contradiction.
           destruct (decide (I1 ⋅ I2 = ∅)); try contradiction.
           destruct (decide (I3 = ∅)); try contradiction.
           reflexivity.
Qed.

Lemma intComp_assoc : Assoc (≡) intComp.
Proof.
  unfold Assoc.
  intros I1 I2 I3.
  destruct (decide (✓ (I1 ⋅ (I2 ⋅ I3)))).
  - apply intComp_assoc_valid in v.
    trivial.
  - destruct (decide (✓ (I1 ⋅ I2 ⋅ I3))).
    * rewrite (intComp_comm I1) in v *.
      intros v.
      rewrite (intComp_comm _ I3) in v *.
      intros v.
      apply intComp_assoc_valid in v.
      rewrite intComp_comm in v *.
      intros v.
      rewrite (intComp_comm I3) in v *.
      intros v.
      rewrite (intComp_comm I2) in v *.
      intros v.
      rewrite (intComp_comm _ I1) in v *.
      trivial.
    * apply intComp_assoc_invalid.
      all: trivial.
Qed.


Instance flowintRAcore : PCore flowintT :=
  λ I, match I with
       | int Ir => Some I_empty
       | intUndef => Some intUndef
       end.

Instance flowintRAunit : cmra.Unit flowintT := I_empty.

Definition flowintRA_mixin : RAMixin flowintT.
Proof.
  split; try apply _; try done.
  - (* Core is unique? *)
    intros ? ? cx -> ?. exists cx. done.
  - (* Associativity *)
    eauto using intComp_assoc.
  - (* Commutativity *)
    unfold Comm. eauto using intComp_comm.
  - (* Core-ID *)
    intros x cx.
    destruct cx eqn:?; unfold pcore, flowintRAcore; destruct x eqn:?;
      try (intros H1; inversion H1).
    + rewrite intComp_comm.
      apply intComp_unit.
    + apply intComp_undef_op.
  - (* Core-Idem *)
    intros x cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x;
      try (intros H0; inversion H0); try done.
  - (* Core-Mono *)
    intros x y cx.
    destruct cx; unfold pcore, flowintRAcore; destruct x; intros H0;
      intros H1; inversion H1; destruct y; try eauto.
    + exists I_empty. split; try done.
      exists (int I_emptyR). by rewrite intComp_unit.
    + exists intUndef. split; try done. exists intUndef.
      rewrite intComp_comm. by rewrite intComp_unit.
    + exists I_empty. split; try done.
      destruct H0 as [a H0].
      assert (intUndef ≡ intUndef ⋅ a); first by rewrite intComp_undef_op.
      rewrite <- H0 in H2.
      inversion H2.
  - (* Valid-Op *)
    intros x y. unfold valid. apply intComp_valid_proj1.
Qed.


Canonical Structure flowintRA := discreteR flowintT flowintRA_mixin.

Instance flowintRA_cmra_discrete : CmraDiscrete flowintRA.
Proof. apply discrete_cmra_discrete. Qed.

Instance flowintRA_cmra_total : CmraTotal flowintRA.
Proof.
  rewrite /CmraTotal. intros. destruct x.
  - exists I_empty. done.
  - exists intUndef. done.
Qed.

Lemma flowint_ucmra_mixin : UcmraMixin flowintT.
Proof.
  split; try apply _; try done.
  unfold ε, flowintRAunit, valid.
  unfold LeftId.
  intros I.
  rewrite intComp_comm.
  apply intComp_unit.
Qed.

End flowint.

Section cmra.

Context (flowdom: Type) `{CCM flowdom}.

Canonical Structure flowintUR : ucmraT := UcmraT (@flowintT flowdom) flowint_ucmra_mixin.

Parameter contextualLeq : flowintUR → flowintUR → Prop.

Definition flowint_update_P (I I_n I_n': flowintUR) (x : authR flowintUR) : Prop :=
  match (auth_auth_proj x) with
  | Some (q, z) => ∃ I', (z = to_agree(I')) ∧ q = 1%Qp ∧ (I_n' = auth_frag_proj x)
                        ∧ contextualLeq I I' ∧ ∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o
  | _ => False
  end.

Lemma flowint_valid_defined I : ✓ I → ∃ Ir, I = int Ir.
Proof.
  intros IV.
  destruct I.
  - exists f.
    reflexivity.
  - apply intUndef_not_valid in IV.
    contradiction.
Qed.

Lemma flowint_valid_unfold (I : flowintUR) : ✓ I → ∃ Ir, I = int Ir ∧ infR Ir ##ₘ outR Ir
                                                      ∧ (infR Ir = ∅ → outR Ir = ∅).
Proof.
  intros.
  unfold valid, cmra_valid in H0.
  simpl in H0.
  unfold ucmra_valid in H0.
  simpl in H0.
  unfold flowint_valid in H0.
  destruct I.
  - exists f.
    naive_solver.
  - contradiction.
Qed.


Hypothesis flowint_update : ∀ I I_n I_n',
  contextualLeq I_n I_n' → (● I ⋅ ◯ I_n) ~~>: (flowint_update_P I I_n I_n').
Lemma flowint_comp_fp : ∀ I1 I2, ✓(I1 ⋅ I2) → domm (I1 ⋅ I2) = domm I1 ∪ domm I2.
Proof.
  apply intComp_dom.
Qed.

End cmra.
