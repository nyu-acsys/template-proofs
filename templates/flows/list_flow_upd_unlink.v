Require Import Program Coq.Logic.Decidable Coq.Program.Wf.
Require Import Coq.Numbers.NatInt.NZAddOrder.
(* From Coq Require Import QArith Qcanon. *)
Require Import FunInd Recdef.
Set Default Proof Using "All".
Require Export multiset_flows flows_big_op.
Require Import Coq.Setoids.Setoid.
Require Export list_flow_upd.

Section list_flow_upd_unlink.
  Open Scope ccm_scope.
  
  Implicit Types I II : gmap Node (multiset_flowint_ur nat).
  Implicit Types ls : list Node.
  Implicit Types S : nzmap nat nat.
  Implicit Types R : gset Node.
  Implicit Type Key : gmap Node nat.
  Implicit Type p pn : Node.
  Implicit Type Nx : gmap Node Node.
  Implicit Type Mk : gmap Node bool.
  
  Function list_flow_upd_unlink_rec p pn ls c S Nx Mk 
  (I I': gmap Node (multiset_flowint_ur nat)) :=
    match ls with 
    | [] => 
      let Ip := I !!! p in
      let Ip' := int {| infR := inf_map Ip; outR :=  <<[c := S]>> ∅ |} in
      let Ipn : multiset_flowint_ur nat := int {| infR := {[pn := ∅]}; outR := ∅ |} in
      let II' := <[pn := Ipn]> (<[p := Ip']> I') in
      II'
    | n :: lss =>
      let Ip := I !!! p in
      let Ip' := int {| infR := inf_map Ip; outR :=  <<[n := S]>> ∅ |} in
      let Ipn : multiset_flowint_ur nat := int {| infR := {[pn := ∅]}; outR := ∅ |} in
      let II' := <[pn := Ipn]> (<[p := Ip']> I') in
      list_flow_upd_unlink_rec p n lss c S Nx Mk I II' end. 

  Definition list_flow_upd_unlink p pn ls c S Nx Mk I :=
    list_flow_upd_unlink_rec p pn ls c S Nx Mk I {[p := I !!! p]}.

  Definition marked_segment Nx Mk pn ls c :=
    Mk !!! pn = true
  ∧ (∀ x, x ∈ ls → Mk !!! x = true)
  ∧ (match ls with
      | [] => Nx !! pn = Some c
      | _ => 
        Nx !! pn = Some (ls !!! 0)
        ∧ (∀ i, i < length ls - 1 → Nx !! (ls !!! i) = Some (ls !!! (i+1)%nat))
        ∧ Nx !! (ls !!! (length ls - 1)%nat) = Some c end).

  Lemma marked_segment_rec Nx Mk pn n ls c :
    marked_segment Nx Mk pn (n :: ls) c → marked_segment Nx Mk n ls c.
  Proof.
    intros Hms.
    rewrite /marked_segment. rewrite /marked_segment /= in Hms.
    split. destruct Hms as (_&H'&_). apply H'. clear; set_solver.
    split. intros x Hx. destruct Hms as (_&H'&_). apply H'. clear -Hx; set_solver.
    destruct ls as [|n1 lss]. rewrite /= in Hms. apply Hms.
    rewrite /=. rewrite /= in Hms. repeat split.
    * destruct Hms as (_&_&_&Hms&_). pose proof Hms 0 as Hms.
      assert (0 < Datatypes.S (length lss)) as H' by lia.
      apply Hms in H'. by rewrite /= in H'.
    * intros i Hi. destruct Hms as (_&_&_&Hms&_). pose proof Hms (i+1)%nat as Hms.
      assert ((n1 :: lss) !!! i = (n :: n1 :: lss) !!! (i+1)%nat) as ->.
      { clear -Hi. rewrite !list_lookup_total_alt Nat.add_1_r.
        by rewrite (lookup_cons _ _ (S i)). }
      assert ((n1 :: lss) !!! (i+1)%nat = (n :: n1 :: lss) !!! (i+1+1)%nat) 
        as ->. 
      { clear -Hi. rewrite !list_lookup_total_alt !Nat.add_1_r.
        rewrite (lookup_cons _ _ (S i)). by rewrite !lookup_cons. }
      apply Hms. lia.
    * assert ((length lss - 0)%nat = length lss) as ->.
      { lia. } apply Hms.
  Qed.

  Lemma unlink_flow_upd_dom p pn ls c S Nx Mk I II I' :
    list_flow_upd_unlink_rec p pn ls c S Nx Mk I II = I' →
      dom I' = dom II ∪ {[p; pn]} ∪ list_to_set ls.
  Proof.
    apply list_flow_upd_unlink_rec_ind; try done.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II -> Ip Ip' Ipn II' <-. 
      rewrite /II' !dom_insert_L /=. set_solver.
    - clear pn ls c S Nx Mk I II.
      intros pn ls c S Nx Mk I II n lss -> Ip Ip' Ipn II' HInd Hflow.
      rewrite HInd; try done. rewrite /II' !dom_insert_L. set_solver.
  Qed.

  Lemma unlink_flow_upd_dom_sub p pn ls c S Nx Mk I II I' :
    (nx_mk_closed Nx Mk (dom I)) →
    (marked_segment Nx Mk pn ls c) →
    (dom II ⊆ dom I) →
    (p ∈ dom II) → (pn ∈ dom I) →
    list_flow_upd_unlink_rec p pn ls c S Nx Mk I II = I' →
      dom I' ⊆ dom I.
  Proof.
    apply list_flow_upd_unlink_rec_ind; try done.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II -> Ip Ip' Ipn II'. 
      intros Hcl Hms Dom_II_in_I p_in_II pn_in_I <-. 
      rewrite /II' !dom_insert_L /=. set_solver.
    - clear pn ls c S Nx Mk I II.
      intros pn ls c S Nx Mk I II n lss -> Ip Ip' Ipn II' HInd. 
      intros Hcl Hms Dom_II_in_I p_in_II pn_in_I Hflow.
      assert (dom II' = dom II ∪ {[pn]}) as Dom_II'.
      { rewrite /II' !dom_insert_L. clear -p_in_II; set_solver. }
      assert (Nx !! pn = Some n) as Nx_pn.
      { rewrite /marked_segment /= in Hms. apply Hms. }
      apply HInd; try done.
      + apply marked_segment_rec in Hms. done.
      + rewrite Dom_II'. clear -pn_in_I Dom_II_in_I; set_solver.
      + rewrite Dom_II'. clear -p_in_II; set_solver.
      + destruct Hcl as (_&_&H'&_). by apply H' in Nx_pn.
  Qed.


  Lemma unlink_flow_valid p pn c S minf :
    let Ip := int {| infR := minf; outR := <<[ pn := S ]>> ∅ |} in
    let Ipn := int {| infR := {[pn := S]}; outR := <<[ c := S ]>> ∅ |} in 
    let Ip' := int {| infR := minf; outR := <<[ c := S ]>> ∅ |} in
    let Ipn' := int {| infR := {[pn := ∅]}; outR := ∅ |} in
    p ≠ pn → p ≠ c → pn ≠ c →
    dom Ip = {[p]} →
    ✓ (Ip ⋅ Ipn) →
      ✓ (Ip' ⋅ Ipn').
  Proof.
    intros Ip Ipn Ip' Ipn' p_neq_pn p_neq_c pn_neq_c Dom_Ip VI.
    apply intValid_composable. assert (Hcomp := VI). 
    apply intComposable_valid in Hcomp. 
    destruct Hcomp as (H1'&H2'&H3'&H4'&H5'). repeat split; simpl.
    - rewrite /dom /flowint_dom /Ip /inf_map /= in Dom_Ip. rewrite Dom_Ip.
      destruct (decide (S = 0%CCM)) as [-> | HS].
      rewrite nzmap_dom_insert_zero. clear; set_solver. done.
      rewrite nzmap_dom_insert_nonzero; try done. rewrite /dom.
      clear -p_neq_c; set_solver.
    - intros H'. rewrite /dom /flowint_dom /Ip /inf_map H' in Dom_Ip.
      clear -Dom_Ip; set_solver.
    - clear.
      rewrite dom_insert dom_empty /dom /nzmap_dom. set_solver.
    - rewrite /flowint_dom /= dom_singleton_L. 
      rewrite /dom /flowint_dom /Ip /inf_map /= in Dom_Ip. rewrite Dom_Ip.
      clear -p_neq_pn; set_solver.
    - apply map_Forall_lookup. intros i x Hix. assert (Hix' := Hix).
      apply elem_of_dom_2 in Hix. rewrite /dom /flowint_dom /Ip /inf_map /= in Dom_Ip. 
      rewrite Dom_Ip elem_of_singleton in Hix. subst i.
      assert (inf Ip' p = x) as ->. { by rewrite /inf /Ip' Hix' /=. } 
      assert (out Ipn' p = 0%CCM) as ->. 
      { rewrite /out /Ipn' /out_map /= nzmap_lookup_empty. done. }
      by rewrite ccm_left_id ccm_pinv_unit.
    - apply map_Forall_lookup. intros i m. 
      destruct (decide (i = pn)) as [-> | Hipn].
      + rewrite lookup_insert. intros [=<-].
        assert (out Ip' pn = 0%CCM) as ->.
        { rewrite /out /Ip' /out_map /= nzmap_lookup_total_insert_ne.
          by rewrite nzmap_lookup_empty. done. }
        assert (inf Ipn' pn = 0%CCM) as ->.
        { by rewrite /Ipn' /inf /inf_map /= lookup_insert /=. }
        by rewrite ccm_left_id ccm_pinv_unit.
      + rewrite lookup_insert_ne; try done.
  Qed.

  Lemma unlink_flow_eq p pn c S minf :
    let Ip := int {| infR := minf; outR := <<[ pn := S ]>> ∅ |} in
    let Ipn := int {| infR := {[pn := S]}; outR := <<[ c := S ]>> ∅ |} in 
    let Ip' := int {| infR := minf; outR := <<[ c := S ]>> ∅ |} in
    let Ipn' := int {| infR := {[pn := ∅]}; outR := ∅ |} in
    p ≠ pn → p ≠ c → pn ≠ c →
    dom Ip = {[p]} →
    ✓ (Ip ⋅ Ipn) →
    ✓ (Ip' ⋅ Ipn') →
      Ip ⋅ Ipn = Ip' ⋅ Ipn'.
  Proof.
    intros Ip Ipn Ip' Ipn' p_neq_pn p_neq_c pn_neq_c Dom_Ip VI VI'.
    assert (dom Ipn = {[pn]}) as Dom_Ipn.
    { rewrite /Ipn; set_solver. }
    assert (dom Ip' = {[p]}) as Dom_Ip'.
    { rewrite /Ip'; set_solver. }
    assert (dom Ipn' = {[pn]}) as Dom_Ipn'.
    { rewrite /Ipn'; set_solver. }
    assert (dom (Ip ⋅ Ipn) = {[p;pn]}) as Dom_ppn.
    { rewrite intComp_dom; try done. rewrite Dom_Ip Dom_Ipn; done. } 
    assert (dom (Ip' ⋅ Ipn') = {[p;pn]}) as Dom_ppn'.
    { rewrite intComp_dom; try done. rewrite Dom_Ip' Dom_Ipn'; done. } 

    apply intEq. 
    - rewrite !intComp_dom; try done. set_solver.
    - rewrite Dom_ppn; set_solver.
    - intros n. destruct (decide (n = p)) as [-> | Hnp].
      + rewrite !intComp_inf_1; try done.
        assert (inf Ip p = inf Ip' p) as ->. 
        { rewrite /Ip /Ip' /inf /=. done. }
        assert (out Ipn p = 0%CCM) as ->. 
        { rewrite /Ipn /out /= nzmap_lookup_total_insert_ne; try done. }
        assert (out Ipn' p = 0%CCM) as ->.
        { rewrite /Ipn' /out /= -nzmap_elem_of_dom_total2. set_solver. }
        done. all: set_solver.
      + destruct (decide (n = pn)) as [-> | Hnpn]; last first.
        { assert (n ∉ dom (Ip ⋅ Ipn)) as H'.
          rewrite Dom_ppn. clear -Hnp Hnpn; set_solver.
          rewrite /dom /flowint_dom not_elem_of_dom in H'.
          assert (n ∉ dom (Ip' ⋅ Ipn')) as H''.
          rewrite Dom_ppn'. clear -Hnp Hnpn; set_solver.
          rewrite /dom /flowint_dom not_elem_of_dom in H''.
          by rewrite /inf H' H''. }
        rewrite !intComp_inf_2; try done.
        assert (out Ip' pn = 0%CCM) as ->. 
        { rewrite /out /Ip' /out_map /= nzmap_lookup_total_insert_ne; try done. }
        assert (inf Ipn pn = S) as ->.
        { rewrite /Ipn /inf /= lookup_insert /=. done. }
        assert (out Ip pn = S) as ->.
        { rewrite /Ip /out /= nzmap_lookup_total_insert. done. }
        assert (inf Ipn' pn = 0%CCM) as ->.
        { rewrite /Ipn' /inf /= lookup_insert /=. done. }
        rewrite ccm_pinv_inv ccm_pinv_unit. done. rewrite Dom_Ipn'. 
        clear; set_solver. rewrite Dom_Ipn. clear; set_solver.
    - intros n. destruct (decide (n ∈ ({[p;pn]}: gset Node))) as [Hn | Hn].
      { rewrite !intValid_in_dom_not_out; try done.
        by rewrite Dom_ppn'. by rewrite Dom_ppn. }
      rewrite !intComp_unfold_out; try done.
      destruct (decide (n = c)) as [-> | Hnc].
      + assert (out Ip' c = S) as ->.
        { rewrite /Ip'/out /= nzmap_lookup_total_insert. done. }
        assert (out Ipn' c = 0%CCM) as ->.
        { by rewrite /Ipn' /out /= nzmap_lookup_empty. }
        assert (out Ip c = 0%CCM) as ->.
        { rewrite /Ip /out /= -nzmap_elem_of_dom_total2.
          destruct (decide (S = 0%CCM)) as [-> | HS].
          rewrite nzmap_dom_insert_zero. clear; set_solver. done.
          rewrite nzmap_dom_insert_nonzero; try done. rewrite /dom.
          clear -pn_neq_c; set_solver. }
        assert (out Ipn c = S) as ->.
        { rewrite /Ipn /out /= nzmap_lookup_total_insert. done. } 
        by rewrite ccm_left_id ccm_right_id.
      + assert (out Ip' n = 0%CCM) as ->. 
        { rewrite /out /Ip' /= nzmap_lookup_total_insert_ne; try done. }
        assert (out Ipn' n = 0%CCM) as ->.
        { rewrite /Ipn' /out  /= nzmap_lookup_empty; try done. }
        assert (out Ip n = 0%CCM) as ->.
        { rewrite /Ip /out /= -nzmap_elem_of_dom_total2.
          destruct (decide (S = 0%CCM)) as [-> | HS].
          rewrite nzmap_dom_insert_zero. clear; set_solver. done.
          rewrite nzmap_dom_insert_nonzero; try done. rewrite /dom.
          clear -Hn; set_solver. }
        assert (out Ipn n = 0%CCM) as ->.
        { rewrite /Ipn /out /= -nzmap_elem_of_dom_total2.
          destruct (decide (S = 0%CCM)) as [-> | HS].
          rewrite nzmap_dom_insert_zero. clear; set_solver. done.
          rewrite nzmap_dom_insert_nonzero; try done. rewrite /dom.
          clear -Hnc; set_solver. }
        done.
      + by rewrite Dom_ppn'.
      + by rewrite Dom_ppn.    
  Qed.

  Lemma unlink_intf_out (Ix: multiset_flowint_ur nat) x xn :
    dom Ix = {[x]} →
    dom (out_map Ix) = {[xn]} →
    outsets Ix ⊆ insets Ix →
    keyset Ix = ∅ →
    (∀ k, inf Ix x !!! k ≤ 1) →
    (∀ x' k, out Ix x' !!! k ≤ 1) →
      out Ix xn = inf Ix x.
  Proof.
    intros Dom_Ix Domout_Ix Out_In KS_Ix Inf_x Out_x.
    assert (insets Ix ⊆ outsets Ix) as H1'. 
    clear -KS_Ix; set_solver.
    assert (insets Ix = outsets Ix) as H1''. 
    clear -H1' Out_In; set_solver.
    rewrite /insets /outsets Dom_Ix Domout_Ix in H1''.
    rewrite -leibniz_equiv_iff !big_opS_singleton in H1''. 
    apply nzmap_eq. intros k'.
    destruct (decide (k' ∈ inset _ Ix x)) as [Hk' | Hk'].
    - assert (Hk'' := Hk'). rewrite H1'' in Hk''.
      rewrite /inset nzmap_elem_of_dom_total in Hk'.
      rewrite /ccmunit /= /nat_unit in Hk'.
      pose proof Inf_x k' as Inf_x.
      rewrite /outset nzmap_elem_of_dom_total in Hk''.
      rewrite /ccmunit /= /nat_unit in Hk''.
      pose proof Out_x xn k' as Out_x.
      set a := inf Ix x !!! k'. set b := out Ix xn !!! k'.
      rewrite -/a -/b in Hk' Hk'' Inf_x Out_x. clear -Hk' Hk'' Inf_x Out_x; lia.
    - assert (Hk'' := Hk'). rewrite H1'' in Hk''.
      rewrite /inset nzmap_elem_of_dom_total2 in Hk'.
      rewrite /outset nzmap_elem_of_dom_total2 in Hk''.
      by rewrite Hk' Hk''.
  Qed.

  Lemma unlink_intf_shape Ix x xn S :
    ✓ Ix →
    dom Ix = {[x]} →
    dom (out_map Ix) = {[xn]} →
    outsets Ix ⊆ insets Ix →
    keyset Ix = ∅ →
    inf Ix x = S →
    (∀ k, inf Ix x !!! k ≤ 1) →
    (∀ x' k, out Ix x' !!! k ≤ 1) →
      Ix = int {| infR := {[x := S]}; outR := <<[xn := S]>> ∅ |}
      ∧ out Ix xn = inf Ix x.
  Proof.
    intros VI Dom_Ix Domout_Ix Out_In KS_Ix Inf_Ix Inf_x Out_x.
    assert (out Ix xn = inf Ix x) as Out_Ix.
    { apply unlink_intf_out; try done. } split; try done.
    destruct Ix as [[minf mout] | ]; try done. apply f_equal.
    apply f_equal2. apply map_eq. intros i. 
    rewrite /dom /flowint_dom /= in Dom_Ix.
    destruct (decide (i = x)) as [-> | Hix]. rewrite lookup_insert.
    rewrite /inf /= in Inf_Ix. rewrite /dom /flowint_dom /= in Dom_Ix.
    assert (x ∈ dom minf) as H'. clear -Dom_Ix; set_solver. 
    rewrite elem_of_dom in H'. destruct H' as [S' HS'].
    rewrite HS' /= in Inf_Ix. by subst S'. 
    rewrite lookup_insert_ne; try done. rewrite lookup_empty -not_elem_of_dom.
    rewrite Dom_Ix. clear -Hix; set_solver. 
    apply nzmap_eq. intros i. destruct (decide (i = xn)) as [-> | Hixn].
    rewrite /out /= Inf_Ix in Out_Ix. by rewrite Out_Ix nzmap_lookup_total_insert.
    rewrite nzmap_lookup_total_insert_ne; try done.
    rewrite nzmap_lookup_empty -nzmap_elem_of_dom_total2. 
    rewrite /= in Domout_Ix. clear -Domout_Ix Hixn; set_solver. 
  Qed.


  Lemma unlink_flow_upd_intfEq Key p pn ls c S Nx Mk I II I':
    let FI := λ I x, I !!! x in
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (marked_segment Nx Mk pn ls c) →
    (dom S ≠ ∅) →
    (dom II ⊆ dom I) →
    (p ∈ dom II) → (pn ∈ dom I) →
    (∀ x, x ∈ dom II → Key !!! x < Key !!! pn) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (∀ n1 n2, insets (FI I n1) ≠ ∅ → 
              Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) →
    (inf (FI I pn) pn = S) →
    (∀ x, x ∈ dom I → Mk !!! x = true → keyset (FI I x) = ∅) →
    (∀ x y, Nx !! x = Some y → insets (FI I x) ≠ ∅ → 
        inf (FI I y) y = out (FI I x) y) →
    (∀ x, x ∈ dom I → outsets (FI I x) ⊆ insets (FI I x)) →
    (∀ x k, x ∈ dom I → inf (FI I x) x !!! k ≤ 1) →
    (∀ x x' k, x ∈ dom I → out (FI I x) x' !!! k ≤ 1) →
    (FI II p = int {| infR := inf_map (FI I p); outR := <<[ pn := S ]>> ∅ |}) →
    (([^op set] x ∈ dom II, FI I x) = ([^op set] x ∈ dom II, FI II x)) →
    list_flow_upd_unlink_rec p pn ls c S Nx Mk I II = I' →
      (([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x)).
  Proof.
    intros FI. apply list_flow_upd_unlink_rec_ind; try done.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II -> Ip Ip' Ipn II'.
      intros Nx_key Hcl Hms S_nempty Dom_II_in_I p_in_II pn_in_I 
        Key_pn Valid Domm_I Nx_dom Inf_pn KS_mk Inf_eq_out Out_In 
        Inf_x Out_x II_p Heq <-.
       
      set R := dom II ∖ {[p]}.
      assert (dom II = R ∪ {[p]}) as R_dom_II.
      { rewrite /R. clear -p_in_II. rewrite set_eq_subseteq. split; try set_solver.
        intros x; destruct (decide (x = p)) as [-> | Hxp]; set_solver. }
      assert (dom II' = R ∪ {[p]} ∪ {[pn]}) as R_dom_II'.
      { rewrite /II' !dom_insert_L. clear -R_dom_II. set_solver. }
      assert (Key !!! p < Key !!! pn) as Key_ppn.
      { by apply Key_pn. }
      assert (p ≠ pn) as p_neq_pn.
      { intros <-. lia. }
      assert (Nx !! pn = Some c) as Nx_pn.
      { rewrite /marked_segment /= in Hms. apply Hms. }
      assert (Key !!! pn < Key !!! c) as Key_pnn.
      { by apply Nx_key. }
      assert (p ≠ c) as p_neq_c.
      { intros <-; lia. }
      assert (pn ≠ c) as pn_neq_c.
      { intros <-; lia. }
      assert (pn ∉ dom II) as pn_notin_II.
      { intros Hpn. apply Key_pn in Hpn. lia. }

      assert (dom II' = dom II ∪ {[pn]}) as Dom_II'.
      { rewrite /II' !dom_insert_L. clear -p_in_II; set_solver. }
      assert (dom II' ⊆ dom I) as Dom_II'_in_I. 
      { rewrite Dom_II'. clear -Dom_II_in_I pn_in_I; set_solver. }
      assert (✓ (FI II p ⋅ FI I pn)) as VI.
      { pose proof flow_big_op_valid _ _ _ Dom_II'_in_I Valid as Valid'. 
        rewrite Dom_II' big_opS_union in Valid'; last first. 
        clear -pn_notin_II; set_solver. rewrite big_opS_singleton in Valid'.
        rewrite Heq in Valid'. rewrite R_dom_II big_opS_union in Valid'; last first.
        clear; set_solver. rewrite big_opS_singleton in Valid'.
        rewrite -(assoc _ _ (FI II p) (FI I pn)) in Valid'.
        apply (cmra_valid_op_r _ _ Valid'). }

      assert (dom (FI I pn) = {[pn]}) as Dom_Ipn.
      { by apply Domm_I. }
      assert (insets (FI I pn) ≠ ∅) as Insets_pn.
      { rewrite /insets Dom_Ipn -leibniz_equiv_iff. rewrite big_opS_singleton. 
        rewrite /inset Inf_pn. by rewrite leibniz_equiv_iff. }

      assert ((FI I pn = int {| infR := {[pn := S]}; outR := <<[ c := S ]>> ∅ |})) 
        as I_pn.
      { apply unlink_intf_shape; try done.
        - apply (cmra_valid_op_r _ (FI I pn)) in VI. done.
        - apply Nx_dom; try done.
        - by apply Out_In.
        - apply KS_mk. done. destruct Hms as (Hms&_). done.
        - intros k; by apply Inf_x.
        - intros x k; by apply Out_x. }

      rewrite R_dom_II' !big_opS_union; last first. 
      clear -p_neq_pn pn_notin_II; set_solver. 
      clear; set_solver. clear -p_neq_pn pn_notin_II; set_solver.
      clear; set_solver. rewrite !big_opS_singleton.
      rewrite R_dom_II !big_opS_union in Heq; last first. 
      clear; set_solver. clear; set_solver.
      rewrite !big_opS_singleton in Heq. rewrite Heq.
      assert (([^op set] y ∈ R, FI II y) = ([^op set] y ∈ R, FI II' y)) as ->.
      { apply big_opS_ext. intros x Hx. rewrite /FI /II'. 
        rewrite !lookup_total_insert_ne. done. clear -Hx; set_solver.
        clear -Hx pn_notin_II; set_solver. }
      rewrite -(assoc _ _ (FI II p) (FI I pn)).
      rewrite -(assoc _ _ (FI II' p) (FI II' pn)).
      assert (dom (inf_map Ip) = {[p]}) as Dom_Ip.
      { pose proof Domm_I p (Dom_II_in_I p p_in_II) as H'. apply H'. }

      assert (✓ (FI II' p ⋅ FI II' pn)) as VI'.
      { rewrite /FI /II' lookup_total_insert_ne; try done.
        rewrite !lookup_total_insert /Ip' /Ipn. apply (unlink_flow_valid p); try done.
        - rewrite II_p I_pn in VI. by rewrite /Ip. }

      assert (FI II p ⋅ FI I pn = FI II' p ⋅ FI II' pn) as H'.
      { rewrite II_p I_pn /FI /II' lookup_total_insert_ne; try done.
        rewrite !lookup_total_insert /Ip' /Ipn. apply (unlink_flow_eq p); try done.
        - rewrite II_p I_pn in VI. by rewrite /Ip.
        - rewrite /FI /II' lookup_total_insert_ne in VI'; try done.
          rewrite !lookup_total_insert /Ip' /Ipn in VI'. done. }
      rewrite H'. done.
    - clear pn ls c S Nx Mk I II.
      intros pn ls c S Nx Mk I II n lss -> Ip Ip' Ipn II' HInd.
      intros Nx_key Hcl Hms S_nempty Dom_II_in_I p_in_II pn_in_I 
        Key_pn Valid Domm_I Nx_dom Inf_pn KS_mk Inf_eq_out Out_In 
        Inf_x Out_x II_p Heq Hflow. 
      set R := dom II ∖ {[p]}.
      assert (dom II = R ∪ {[p]}) as R_dom_II.
      { rewrite /R. clear -p_in_II. rewrite set_eq_subseteq. split; try set_solver.
        intros x; destruct (decide (x = p)) as [-> | Hxp]; set_solver. }
      assert (dom II' = R ∪ {[p]} ∪ {[pn]}) as R_dom_II'.
      { rewrite /II' !dom_insert_L. clear -R_dom_II. set_solver. }
      assert (dom II' = dom II ∪ {[pn]}) as Dom_II'.
      { rewrite /II' !dom_insert_L. clear -p_in_II; set_solver. }

      assert (Key !!! p < Key !!! pn) as Key_ppn.
      { by apply Key_pn. }
      assert (p ≠ pn) as p_neq_pn.
      { intros <-. lia. }
      assert (Nx !! pn = Some n) as Nx_pn.
      { rewrite /marked_segment /= in Hms. apply Hms. }
      assert (Key !!! pn < Key !!! n) as Key_pnn.
      { by apply Nx_key. }
      assert (p ≠ n) as p_neq_n.
      { intros <-; lia. }
      assert (pn ≠ n) as pn_neq_n.
      { intros <-; lia. }
      assert (pn ∉ dom II) as pn_notin_II.
      { intros Hpn. apply Key_pn in Hpn. lia. }
      assert (n ∉ dom II') as n_notin_II'.
      { rewrite /II' !dom_insert_L !elem_of_union !elem_of_singleton.
        intros [-> | [-> | Hn]]; try done. pose proof Key_pn n Hn as H'. lia. }
      assert (dom II' ⊆ dom I) as Dom_II'_in_I. 
      { rewrite Dom_II'. clear -Dom_II_in_I pn_in_I; set_solver. }
      assert (✓ (FI II p ⋅ FI I pn)) as VI.
      { pose proof flow_big_op_valid _ _ _ Dom_II'_in_I Valid as Valid'. 
        rewrite Dom_II' big_opS_union in Valid'; last first. 
        clear -pn_notin_II; set_solver. rewrite big_opS_singleton in Valid'.
        rewrite Heq in Valid'. rewrite R_dom_II big_opS_union in Valid'; last first.
        clear; set_solver. rewrite big_opS_singleton in Valid'.
        rewrite -(assoc _ _ (FI II p) (FI I pn)) in Valid'.
        apply (cmra_valid_op_r _ _ Valid'). }
      
      assert (dom (FI I pn) = {[pn]}) as Dom_Ipn.
      { by apply Domm_I. }
      assert (insets (FI I pn) ≠ ∅) as Insets_pn.
      { rewrite /insets Dom_Ipn -leibniz_equiv_iff. rewrite big_opS_singleton. 
        rewrite /inset Inf_pn. by rewrite leibniz_equiv_iff. }

      assert ((FI I pn = int {| infR := {[pn := S]}; outR := <<[ n := S ]>> ∅ |})
        ∧ (out (FI I pn) n = inf (FI I pn) pn)) as [I_pn Out_Ipn].
      { apply unlink_intf_shape; try done.
        - apply (cmra_valid_op_r _ (FI I pn)) in VI. done.
        - apply Nx_dom; try done.
        - by apply Out_In.
        - apply KS_mk. done. destruct Hms as (Hms&_). done.
        - intros k; by apply Inf_x.
        - intros x k; by apply Out_x. }
      
      apply HInd; try done.
      + apply marked_segment_rec in Hms. done.
      + rewrite R_dom_II'. clear; set_solver.
      + destruct Hcl as (_&_&H'&_). apply H' in Nx_pn. done.
      + intros x Hx. rewrite Dom_II' elem_of_union elem_of_singleton in Hx.
        destruct Hx as [Hx | ->]; try done. pose proof Key_pn x Hx as H'. lia. 
      + rewrite (Inf_eq_out pn n); try done. by rewrite Out_Ipn. 
      + rewrite /FI /II' lookup_total_insert_ne; try done. rewrite lookup_total_insert.
        rewrite /Ip' /Ip. done.
      + rewrite R_dom_II' !big_opS_union; last first. 
        clear -p_neq_pn pn_notin_II; set_solver. 
        clear; set_solver. clear -p_neq_pn pn_notin_II; set_solver.
        clear; set_solver. rewrite !big_opS_singleton.
        rewrite R_dom_II !big_opS_union in Heq; last first. clear; set_solver. 
        clear; set_solver.
        rewrite !big_opS_singleton in Heq. rewrite Heq.
        assert (([^op set] y ∈ R, FI II y) = ([^op set] y ∈ R, FI II' y)) as ->.
        { apply big_opS_ext. intros x Hx. rewrite /FI /II'. 
          rewrite !lookup_total_insert_ne. done. clear -Hx; set_solver.
          clear -p_neq_pn Hx pn_notin_II; set_solver. }
        rewrite -(assoc _ _ (FI II p) (FI I pn)).
        rewrite -(assoc _ _ (FI II' p) (FI II' pn)).
        
        assert (dom (inf_map Ip) = {[p]}) as Dom_Ip.
        { pose proof Domm_I p (Dom_II_in_I p p_in_II) as H'. apply H'. }
        assert (✓ (FI II' p ⋅ FI II' pn)) as VI'.
        { rewrite /FI /II' lookup_total_insert_ne; try done.
          rewrite !lookup_total_insert /Ip' /Ipn. apply (unlink_flow_valid p); try done.
          rewrite II_p I_pn in VI. by rewrite /Ip. }

        assert (FI II p ⋅ FI I pn = FI II' p ⋅ FI II' pn) as H'.
        { rewrite II_p I_pn /FI /II' lookup_total_insert_ne; try done.
          rewrite !lookup_total_insert /Ip' /Ipn. apply (unlink_flow_eq p); try done.
          - rewrite II_p I_pn in VI. by rewrite /Ip.
          - rewrite /FI /II' lookup_total_insert_ne in VI'; try done.
            rewrite !lookup_total_insert /Ip' /Ipn in VI'. done. }
        rewrite H'. done.
  Qed.

  Lemma unlink_flow_upd_Ip Key p pn ls c S Nx Mk I II I' :
    let FI := λ I x, I !!! x in
    nx_key_rel Nx Key →
    marked_segment Nx Mk pn ls c →
    (p ∈ dom II) →
    (∀ x, x ∈ dom II → Key !!! x < Key !!! pn) →
    (FI II p = int {| infR := inf_map (FI I p); outR := <<[ pn := S ]>> ∅ |}) →
    list_flow_upd_unlink_rec p pn ls c S Nx Mk I II = I' →
      (FI I' p = int {| infR := inf_map (FI I p); outR := <<[ c := S ]>> ∅ |}).
  Proof.
    intros FI. apply list_flow_upd_unlink_rec_ind; try done.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II -> Ip Ip' Ipn II'.
      intros Nx_key Hms p_in_II Key_pn II_p <-.

      assert (Key !!! p < Key !!! pn) as Key_ppn.
      { by apply Key_pn. }
      assert (p ≠ pn) as p_neq_pn.
      { intros <-. lia. }
      rewrite /FI /II' lookup_total_insert_ne; try done.
      rewrite lookup_total_insert /Ip' /Ip. done.
    - clear pn ls c S Nx Mk I II.
      intros pn ls c S Nx Mk I II n lss -> Ip Ip' Ipn II' HInd.
      intros Nx_key Hms p_in_II Key_pn II_p Hflow.

      assert (dom II' = dom II ∪ {[pn]}) as Dom_II'.
      { rewrite /II' !dom_insert_L. clear -p_in_II; set_solver. }
      assert (Nx !! pn = Some n) as Nx_pn.
      { rewrite /marked_segment /= in Hms. apply Hms. }
      assert (Key !!! pn < Key !!! n) as Key_pnn.
      { by apply Nx_key. }
      assert (Key !!! p < Key !!! pn) as Key_ppn.
      { by apply Key_pn. }
      assert (p ≠ pn) as p_neq_pn.
      { intros <-. lia. }

      apply HInd; try done.
      + apply marked_segment_rec in Hms. done.
      + rewrite Dom_II'. clear -p_in_II; set_solver.
      + intros x Hx. rewrite Dom_II' elem_of_union elem_of_singleton in Hx.
        destruct Hx as [Hx | ->]; try done. pose proof Key_pn x Hx as H'. lia.
      + rewrite /FI /II' lookup_total_insert_ne; try done.
        rewrite lookup_total_insert /Ip' /Ip. done.
  Qed.

  Lemma unlink_flow_upd_Ix Key p pn ls c S Nx Mk I II I' :
    let FI := λ I x, I !!! x in
    nx_key_rel Nx Key →
    marked_segment Nx Mk pn ls c →
    (p ∈ dom II) →
    (∀ x, x ∈ dom II → Key !!! x < Key !!! pn) →
    (∀ x, x ∈ dom II → x ≠ p → FI II x = int {| infR := {[x := ∅]}; outR := ∅ |}) →
    list_flow_upd_unlink_rec p pn ls c S Nx Mk I II = I' →
      (∀ x, x ∈ dom I' → x ≠ p → FI I' x = int {| infR := {[x := ∅]}; outR := ∅ |}).
  Proof.
  intros FI. apply list_flow_upd_unlink_rec_ind; try done.
  - clear pn ls c S Nx Mk I II. 
    intros pn ls c S Nx Mk I II -> Ip Ip' Ipn II'.
    intros Nx_key Hms p_in_II Key_pn II_x <-. 
    intros x. rewrite /II' !dom_insert_L !elem_of_union !elem_of_singleton.
    intros [-> | [-> | Hx]] Hxp; try done.
    rewrite /FI lookup_total_insert /Ipn. done.
    rewrite /FI !lookup_total_insert_ne; try done. apply II_x.
    all: try done. intros <-. apply Key_pn in Hx. lia.
  - clear pn ls c S Nx Mk I II. 
    intros pn ls c S Nx Mk I II n lss -> Ip Ip' Ipn II' HInd.
    intros Nx_key Hms p_in_II Key_pn II_x Hflow.

    assert (Nx !! pn = Some n) as Nx_pn.
    { rewrite /marked_segment /= in Hms. apply Hms. }
    assert (Key !!! pn < Key !!! n) as Key_pnn.
    { by apply Nx_key. }
    assert (Key !!! p < Key !!! pn) as Key_ppn.
    { by apply Key_pn. }
    assert (p ≠ pn) as p_neq_pn.
    { intros <-. lia. }
    assert (dom II' = dom II ∪ {[pn]}) as Dom_II'.
    { rewrite /II' !dom_insert_L. clear -p_in_II; set_solver. }

    apply HInd; try done.
    + apply marked_segment_rec in Hms. done.
    + rewrite Dom_II'. clear -p_in_II; set_solver.
    + intros x Hx. rewrite Dom_II' elem_of_union elem_of_singleton in Hx.
      destruct Hx as [Hx | ->]; try done. pose proof Key_pn x Hx as H'. lia.
    + intros x. rewrite /II' !dom_insert_L !elem_of_union !elem_of_singleton.
      intros [-> | [-> | Hx]] Hxp; try done.
      rewrite /FI lookup_total_insert /Ipn. done.
      rewrite /FI !lookup_total_insert_ne; try done. apply II_x.
      all: try done. intros <-. apply Key_pn in Hx. lia.
  Qed.

  Lemma unlink_flow_upd_c_notin Key p pn ls c S Nx Mk I II I' :
  let FI := λ I x, I !!! x in
  nx_key_rel Nx Key →
  marked_segment Nx Mk pn ls c →
  (p ∈ dom II) →
  (∀ x, x ∈ dom II → Key !!! x < Key !!! pn) →
  list_flow_upd_unlink_rec p pn ls c S Nx Mk I II = I' →
    (c ∉ dom I').
  Proof.
    intros FI. apply list_flow_upd_unlink_rec_ind; try done.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II -> Ip Ip' Ipn II'.
      intros Nx_key Hms p_in_II Key_pn <-.
      intros Hc. 
      assert (dom II' = dom II ∪ {[pn]}) as Dom_II'.
      { rewrite /II' !dom_insert_L. clear -p_in_II; set_solver. }
      assert (Nx !! pn = Some c) as Nx_pn.
      { apply Hms. }
      apply Nx_key in Nx_pn. 
      rewrite Dom_II' elem_of_union elem_of_singleton in Hc.
      destruct Hc as [Hc | ->]. apply Key_pn in Hc; lia. lia.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II n lss -> Ip Ip' Ipn II' HInd.
      intros Nx_key Hms p_in_II Key_pn Hflow.
      assert (dom II' = dom II ∪ {[pn]}) as Dom_II'.
      { rewrite /II' !dom_insert_L. clear -p_in_II; set_solver. }
      assert (Nx !! pn = Some n) as Nx_pn.
      { rewrite /marked_segment /= in Hms. apply Hms. }
      assert (Key !!! pn < Key !!! n) as Key_pnn.
      { by apply Nx_key. }
      assert (Key !!! p < Key !!! pn) as Key_ppn.
      { by apply Key_pn. }
      assert (p ≠ pn) as p_neq_pn.
      { intros <-. lia. }

      apply HInd; try done.
      + apply marked_segment_rec in Hms. done.
      + rewrite Dom_II'. clear -p_in_II; set_solver.
      + intros x Hx. rewrite Dom_II' elem_of_union elem_of_singleton in Hx.
        destruct Hx as [Hx | ->]; try done. pose proof Key_pn x Hx as H'. lia.
  Qed.

  Lemma unlink_flow_upd_key_pc Key p pn ls c S Nx Mk I II I' :
  nx_key_rel Nx Key →
  marked_segment Nx Mk pn ls c →
  (Key !!! p < Key !!! pn) →
  list_flow_upd_unlink_rec p pn ls c S Nx Mk I II = I' →
    (Key !!! p < Key !!! c).
  Proof.
    apply list_flow_upd_unlink_rec_ind; try done.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II -> Ip Ip' Ipn II'.
      intros Nx_key Hms Key_ppn <-.
      rewrite /marked_segment in Hms. destruct Hms as (_&_&Nx_pn).
      apply Nx_key in Nx_pn. lia.
    - clear pn ls c S Nx Mk I II. 
      intros pn ls c S Nx Mk I II n lss -> Ip Ip' Ipn II' HInd.
      intros Nx_key Hms Key_ppn Hflow.
      
      assert (Nx !! pn = Some n) as Nx_pn.
      { rewrite /marked_segment /= in Hms. apply Hms. }
      assert (Key !!! pn < Key !!! n) as Key_pnn.
      { by apply Nx_key. }

      apply HInd; try done.
      + apply marked_segment_rec in Hms. done.
      + lia.
  Qed.

  Lemma unlink_flow_upd_summary Key p pn ls c Nx Mk I I' :
    let FI := λ I x, I !!! x in
    let S := out (FI I p) pn in 
    (nx_key_rel Nx Key) →
    (nx_mk_closed Nx Mk (dom I)) →
    (marked_segment Nx Mk pn ls c) →
    (dom S ≠ ∅) →
    (Nx !! p = Some pn) →
    (✓ ([^op set] x ∈ dom I, FI I x)) →
    (∀ x, x ∈ dom I → dom (FI I x) = {[x]}) →
    (∀ n1 n2, insets (FI I n1) ≠ ∅ → 
              Nx !! n1 = Some n2 → dom (out_map (FI I n1)) = {[n2]}) →
    (∀ x, x ∈ dom I → Mk !!! x = true → keyset (FI I x) = ∅) →
    (∀ x y, Nx !! x = Some y → insets (FI I x) ≠ ∅ → 
        inf (FI I y) y = out (FI I x) y) →
    (∀ x, x ∈ dom I → outsets (FI I x) ⊆ insets (FI I x)) →
    (∀ x k, x ∈ dom I → inf (FI I x) x !!! k ≤ 1) →
    (∀ x x' k, x ∈ dom I → out (FI I x) x' !!! k ≤ 1) →
    (insets (FI I p) ≠ ∅) →
    list_flow_upd_unlink p pn ls c S Nx Mk I = I' →
        (dom I' = {[p; pn]} ∪ list_to_set ls)
      ∧ (dom I' ⊆ dom I)
      (* ∧ (c ∉ dom I') *)
      ∧ (Key !!! p < Key !!! c)
      (* ∧ (∀ x, x ∈ dom I' ∖ {[p]} → Key !!! p < Key !!! x) *)
      (* ∧ (∀ x, x ∈ dom I' → dom (FI I' x) = {[x]}) *)
      ∧ (([^op set] x ∈ dom I', FI I x) = ([^op set] x ∈ dom I', FI I' x))
      ∧ (FI I' p = int {| infR := inf_map (FI I p); outR := <<[ c := S ]>> ∅ |})
      ∧ (∀ x, x ∈ dom I' → x ≠ p → FI I' x = int {| infR := {[x := ∅]}; outR := ∅ |}).
  Proof.
    intros FI S Nx_key Hcl Hms Dom_S Nx_p VI Domm_I Nx_dom KS_mk 
      Inf_eq_Out Out_In Inf_x Out_x Insets_p_ne Hflow.
    rewrite /list_flow_upd_unlink in Hflow.
    set II : gmap Node (multiset_flowint_ur nat) := {[p := I !!! p]}.
    assert (dom II = {[p]}) as Dom_II.
    { clear; set_solver. }
    assert (p ∈ dom II) as p_in_II.
    { clear; set_solver. }
    assert (p ∈ dom I) as p_in_I.
    { destruct Hcl as (H'&_). apply elem_of_dom_2 in Nx_p. by apply H' in Nx_p. }

    assert (∀ x, x ∈ dom II → Key !!! x < Key !!! pn) as Key_pn.
    { intros x. rewrite Dom_II elem_of_singleton. intros ->. apply Nx_key. done. }
    assert (dom II ⊆ dom I) as Dom_II_in_I.
    { rewrite Dom_II. clear -p_in_I; set_solver. }
    assert (pn ∈ dom I) as pn_in_I.
    { destruct Hcl as (_&_&H'&_). apply H' in Nx_p. done. }
    assert (✓ FI I p) as VI_p.
    { rewrite Dom_II in Dom_II_in_I. apply (flow_big_op_valid _ _ {[p]}) in VI.
      rewrite big_opS_singleton in VI. done. done. }
    assert (FI II p = int {| infR := inf_map (I !!! p); outR := <<[ pn := S ]>> ∅ |})
      as II_p. 
    { rewrite /FI lookup_total_insert. rewrite /FI in VI_p.
      destruct (I !!! p) as [[minf mout] | ] eqn: H'; try done. 
      apply f_equal. apply f_equal2. rewrite /inf_map /=. done. 
      apply nzmap_eq. intros n. pose proof Nx_dom p pn Insets_p_ne Nx_p as Domout_p.
      rewrite /FI H' /= in Domout_p. destruct (decide (n = pn)) as [-> | Hnpn].
      rewrite nzmap_lookup_total_insert /S. rewrite /FI H' /out /=. done.
      rewrite nzmap_lookup_total_insert_ne; try done. rewrite nzmap_lookup_empty.
      rewrite -nzmap_elem_of_dom_total2. clear -Domout_p Hnpn; set_solver. }
    assert (inf (FI I pn) pn = S) as Inf_pn.
    { pose proof Inf_eq_Out p pn Nx_p Insets_p_ne as H'. rewrite H'. done. }
    assert (([^op set] x ∈ dom II, I !!! x) = ([^op set] x ∈ dom II, FI II x)) as Heq.
    { rewrite Dom_II. rewrite !big_opS_singleton /FI /II lookup_total_insert. done. }
    assert (∀ x, x ∈ dom II → x ≠ p → 
      FI II x = int {| infR := {[x := ∅]}; outR := ∅ |}) as II_x.
    { intros x. rewrite Dom_II. clear; set_solver. }
    assert (Key !!! p < Key !!! pn) as Key_ppn.
    { by apply Nx_key in Nx_p. }
    repeat split; try done.
    - apply unlink_flow_upd_dom in Hflow; try done. clear -Hflow; set_solver.
    - apply unlink_flow_upd_dom_sub in Hflow; try done.
    - apply (unlink_flow_upd_key_pc Key) in Hflow; try done.
    (* - apply (unlink_flow_upd_c_notin Key) in Hflow; try done. *)
    - apply (unlink_flow_upd_intfEq Key) in Hflow; try done.
    - apply (unlink_flow_upd_Ip Key) in Hflow; try done.
    - pose proof (unlink_flow_upd_Ix Key p pn ls c S Nx Mk I II I' Nx_key Hms
        p_in_II Key_pn II_x Hflow). done. 
  Qed.
  
End list_flow_upd_unlink.