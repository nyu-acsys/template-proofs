(** Verification of lock coupling template algorithm *)

Require Import lock.
From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "All".
Require Export inset_flows.
Require Import auth_ext.

(** We use integers as keys. *)
Definition K := Z.

(** Definitions of cameras used in the template verification *)
Section Coupling_Cameras.

  (* RA for authoritative flow interfaces over multisets of keys *)
  Class flowintG Σ :=
    FlowintG { flowint_inG :> inG Σ (authR (inset_flowint_ur K)) }.
  Definition flowintΣ : gFunctors := #[GFunctor (authR (inset_flowint_ur K))].

  Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
  Proof. solve_inG. Qed.

  (* RA for authoritative set of nodes *)
  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR Node)) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR Node))].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.

  (* RA for pair of keysets and contents *)
  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.

  (* RA for set of contents *)
  Class contentG Σ :=
    ContentG { content_inG :> inG Σ (authR (optionUR (exclR (gsetR K)))) }.
  Definition contentΣ : gFunctors :=
    #[GFunctor (authR (optionUR (exclR (gsetR K))))].

End Coupling_Cameras.

(** Verification of the template *)
Section Coupling_Template.

  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !(@keysetG K _ _) Σ, !contentG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (** The code of the coupling template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b+-tree.spl and
   * hashtbl-give-up.spl for the concrete implementations. *)

  Parameter findNext : val.
  Parameter decisiveOp : (dOp → val).
  Parameter alloc : val.

  Definition traverse : val :=
    rec: "tr" "p" "n" "k" :=
      match: Fst (findNext "n" "k") with
        NONE => (("p", "n"), Snd (findNext "n" "k"))
      | SOME "n'" =>
        lockNode "n'";; unlockNode "p";; "tr" "n" "n'" "k"
      end.

  Definition CSS_insertOp (root: Node) : val :=
    λ: "k",
    lockNode #root;;
    let: "n0" := Fst (findNext #root "k") in
    match: "n0" with
      NONE => ""
    | SOME "n0" =>
      lockNode "n0";;
      let: "tr_res" := traverse #root "n0" "k" in
      let: "b" := Snd "tr_res" in
      if: "b" then 
        #false
      else
        let: "pn" := Fst "tr_res" in 
        let: "p" := Fst "pn" in
        let: "n" := Snd "pn" in
        let: "m" := alloc #() in
        let: "res" := (decisiveOp insertOp) "p" "n" "k" in
        unlockNode "p";; unlockNode "n";; "res" end.

  (** Assumptions on the implementation made by the template proofs.
   * Matching definitions can be found in GRASShopper file list-coupling.spl *)

  (* The node predicate is specific to each template implementation. *)
  Parameter node : Node → Node → inset_flowint_ur K → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * root-order separation logic. *)
  Parameter node_timeless_proof : ∀ root n I C, Timeless (node root n I C).
  Instance node_timeless root n I C: Timeless (node root n I C).
  Proof. apply node_timeless_proof. Qed.

  (* Spatial part of node predicate. *)
  Parameter hrepSpatial : Node → iProp.

  (* The node-local invariant. 
   * See list-coupling.spl for the corresponding GRASShopper definition.*)
  (* TODO there's a slight discrepancy between this and grasshopper. *)
  Definition nodeinv root n (In : inset_flowint_ur K) Cn : Prop :=
    domm In = {[n]}
    ∧ Cn ⊆ keyset K In n
    ∧ (∀ k : K, default 0 (inf In n !! k) ≤ 1)
    ∧ (n = root → ∀ k1 : K, k1 ∈ KS → in_outsets K k1 In).

  (* The following hypotheses are proved as GRASShopper lemmas in
   * list-coupling.spl *)
  Hypothesis node_implies_nodeinv : ∀ root n In C,
    (⌜✓In⌝)%I ∗ node root n In C
    -∗ node root n In C ∗ (⌜nodeinv root n In C⌝)%I.

  Hypothesis node_sep_star: ∀ root n In In' C C',
    node root n In C ∗ node root n In' C' -∗ False.

  Lemma successor_not_root : ∀ (I I1 I2 I3 : flowintT) C root n k,
      globalinv K root I →
      I = I1 ⋅ I2 ⋅ I3 →
      k ∈ outset K I1 n →
      k ∈ KS →
      nodeinv root n I2 C →
      n ≠ root.
  Proof.
    intros ? ? ? ? ? ? ? ? GI IDef k_in_out1 k_in_KS NI.
    destruct (decide (n = root)).
    destruct GI as (VI & root_in_I & I_closed & I_inf_out).
    rewrite <- cmra_assoc in IDef.
    (*unfold op, cmra_op, ucmra_cmraR, inset_flowint_ur, flowintUR, ucmra_op in IDef.*)
    rewrite IDef in VI.
    pose proof (intComp_valid_proj1 _ _ VI) as V1.
    pose proof (intComp_valid_proj2 _ _ VI) as V23.
    pose proof (intComp_unfold_inf_1 _ _ VI n) as inf_I1.
    pose proof (intComp_unfold_inf_1 _ _ V23) as inf_I2.
    destruct NI as (domm_I2 & _ & inf_bound & _).
    assert (n ∈ domm I2 ∪ domm I3) as n_in_I23 by set_solver.
    pose proof (intComp_unfold_inf_2 _ _ VI n) as inf_I23.
    rewrite intComp_dom in inf_I23.
    apply inf_I23 in n_in_I23 as n_inf_I23.
    unfold cmra_op, flowintRA, cmra_car, K_multiset at 5, K_multiset at 5 in n_inf_I23.
(* <<<<<<< HEAD *)
    pose proof (I_inf_out k k_in_KS) as root_out_k.
    assert (default 0 (inf I n !! k) ≠ 0).
    rewrite e.
    unfold inset, dom_ms in root_out_k.
    apply nzmap_elem_of_dom in root_out_k.
    unfold lookup, nzmap_lookup.
    pose proof (nzmap_is_wf (inf I root)) as inf_root_wf.
    pose proof (nzmap_lookup_wf _ k inf_root_wf).
    destruct (inf I root).
    simpl in root_out_k.
    unfold is_Some in root_out_k.
    destruct root_out_k as [x root_out_k].
    unfold lookup, nzmap_lookup in root_out_k.
    rewrite root_out_k.
    simpl in H0.
    simpl.
    naive_solver.
    pose proof (lookup_op _ _ (inf I n) (out I1 n) k) as inf_I23_def.

    rewrite IDef in inf_I23_def.
    unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I23_def.
    unfold ccm_op, lift_ccm in n_inf_I23.

    unfold K_multiset_ccm at 4, lift_ccm in n_inf_I23.
    rewrite <- n_inf_I23 in inf_I23_def.
    unfold cmra_op, flowintRA, cmra_car in IDef.
    rewrite <- IDef in inf_I23_def.
    
    assert (n ∈ domm I2) as n_in_I2 by set_solver.
    pose proof (inf_I2 n n_in_I2) as n_inf_I2.
    pose proof (lookup_op _ _ (inf (I2 ⋅ I3) n) (out I3 n) k) as inf_I2_def.
    unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I2_def.
    unfold K_multiset_ccm, ccmop, ccm_op, lift_ccm in n_inf_I2.    
    setoid_rewrite <- n_inf_I2 in inf_I2_def.
    setoid_rewrite inf_I23_def in inf_I2_def.

    assert (default 0 (out I1 n !! k) ≠ 0).
    unfold outset, dom_ms in k_in_out1.
    apply nzmap_elem_of_dom in k_in_out1.
    pose proof (nzmap_is_wf (out I1 n)) as out_n_wf.
    pose proof (nzmap_lookup_wf _ k out_n_wf).
    destruct (out I1 n).
    simpl in k_in_out1.
    unfold is_Some in k_in_out1.
    destruct k_in_out1 as [x k_in_out1].
    rewrite k_in_out1.
    simpl in H0.
    simpl.
    naive_solver.
    unfold ccmunit, ccmop, ccm_unit, ccm_op, nat_ccm, nat_unit, nat_op in inf_I23_def.
    unfold ccmunit, ccmop, ccm_unit, ccm_op, nat_ccm, nat_unit, nat_op in inf_I2_def.
    pose proof (inf_bound k).
    remember (inf I2 n !! k) as x2.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx2.
    setoid_rewrite <- Heqx2 in inf_I2_def.
    remember (inf I n !! k) as x.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx.
    rewrite <- Heqx in inf_I2_def.
    remember (out I1 n !! k) as x1.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx1.
    rewrite <- Heqx1 in inf_I2_def.
    lia.
    all: trivial.
  Qed.


  (** Helper functions specs *)

  (* The following functions are proved for each implementation in GRASShopper
   * (see list-coupling.spl) *)

  (* TODO ghp spec doesn't match *)
  Parameter findNext_spec : ∀ (n: Node) (k: K) (In : inset_flowint_ur K) (C: gset K) root,
     ⊢ ({{{ node root n In C ∗ ⌜in_inset K k In n⌝ }}}                
           findNext #n #k
       {{{ (succ: bool) (np: Node) (res: bool),
              RET (match succ with true => ((SOMEV #np), #res) | false => (NONEV, #res) end);
                  node root n In C ∗ ⌜res ↔ k ∈ C⌝ 
               ∗ (match succ with true  => ⌜in_outset K k In np⌝
                                | false => ⌜¬in_outsets K k In⌝ ∗ ⌜n ≠ root⌝ end) }}})%I.

  Parameter decisiveOp_insert_spec : ∀ root (p n m: Node) (k: K) (Ip In: inset_flowint_ur K) (Cp Cn: gset K),
     ⊢ ({{{       ⌜k ∈ KS⌝ 
                ∗ ⌜keyset K Ip p ## keyset K In n⌝ 
                ∗ node root p Ip Cp 
                ∗ node root n In Cn
                ∗ hrepSpatial m
                ∗ ⌜✓ (Ip ⋅ In)⌝ 
                ∗ ⌜out (Ip ⋅ In) m = 0%CCM⌝  
                ∗ ⌜m ≠ root⌝ 
                ∗ ⌜n ≠ root⌝ 
                ∗ ⌜k ∉ Cn⌝
                ∗ ⌜in_outset K k Ip n⌝ 
                ∗ ⌜in_inset K k Ip p⌝  
                ∗ ⌜¬in_outsets K k In⌝ }}}
                
           decisiveOp insertOp #p #n #k
           
       {{{ (Cp1 Cn1 Cm1: gset K) (Ip1 In1 Im1: flowintUR K_multiset) (res: bool), RET  #res;
                  node root p Ip1 Cp1
                ∗ node root n In1 Cn1
                ∗ node root m Im1 Cm1
                ∗ Ψ insertOp k (Cp ∪ Cn) (Cp1 ∪ Cn1 ∪ Cm1) res
                ∗ ⌜contextualLeq _ (Ip ⋅ In) (Ip1 ⋅ In1 ⋅ Im1)⌝
                ∗ ⌜inf (Ip1 ⋅ In1 ⋅ Im1) m = 0%CCM⌝
                ∗ ⌜keyset K Ip1 p ## keyset K In1 n⌝
                ∗ ⌜keyset K Ip1 p ## keyset K Im1 m⌝
                ∗ ⌜keyset K Im1 m ## keyset K In1 n⌝
                ∗ ⌜keyset K Ip1 p ∪ keyset K In1 n ∪ keyset K Im1 m = keyset K Ip p ∪ keyset K In n⌝ }}})%I.

  Parameter alloc_spec :
     ⊢ ({{{ True }}}
           alloc #()
       {{{ (m: Node) (l:loc), RET #m; hrepSpatial m ∗ ⌜lockLoc m = l⌝ ∗ l ↦ #false }}})%I.


  (** The concurrent search structure invariant *)

  Definition cssN : namespace := N .@ "css".

  Definition css_inv (γ γ_fp γ_k γ_c : gname) root : iProp :=
    (∃ (I: inset_flowint_ur K) (C: gsetO K),
        own γ_k (● prod (KS, C)) ∗ own γ (● I) ∗ ⌜globalinv K root I⌝
        ∗ own γ_fp (● domm I)
        ∗ own γ_c (● (Some (Excl C)))
        ∗ ([∗ set] n ∈ (domm I), (∃ b: bool,
          (lockLoc n) ↦ #b
          ∗ if b then True
            else (∃ (I_n: inset_flowint_ur K) (C_n: gset K),
                 own γ (◯ I_n) ∗ ⌜domm I_n = {[n]}⌝ ∗ node root n I_n C_n
                 ∗ own γ_k (◯ prod (keyset K I_n n, C_n)))))
    )%I.

  Definition css (γ γ_fp γ_k γ_c : gname) root : iProp :=
    inv N (css_inv γ γ_fp γ_k γ_c root).

  Definition css_cont (γ_c: gname) (C: gset K) : iProp :=
    (own γ_c (◯ (Some ((Excl C)))))%I.

  Instance css_inv_timeless  γ γ_fp γ_k γ_c root :
    Timeless (css_inv γ γ_fp γ_k γ_c root).
  Proof.
    rewrite /css_inv. repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    apply big_sepS_timeless. intros. apply bi.exist_timeless. intros.
    apply bi.sep_timeless; try apply _.
    destruct x2; try apply _.
  Qed.

  (** Assorted useful lemmas *)

  Lemma auth_agree γ xs ys :
  own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.


  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P K_multiset I I_n I_n' x⌝ ∧ own γ x -∗
    ∃ I', ⌜contextualLeq K_multiset I I'⌝
          ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
          ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (auth_auth_proj x); last first.
    - intros Hx. iIntros "(% & ?)". iExFalso. done.
    - intros p. intros Hx. case_eq p. intros q a Hp.
      iIntros "[HI' Hown]". iDestruct "HI'" as %HI'.
      destruct HI' as [I' HI'].
      destruct HI' as [Hagree [Hq [HIn [Hcontxl HIo]]]].
      iExists I'.
      iSplit. by iPureIntro.
      iSplit. by iPureIntro.
      assert (Auth (auth_auth_proj x) (auth_frag_proj x) = x) as Hdefx.
      { destruct x. reflexivity. }
      assert (x = (Auth (Some (1%Qp, to_agree(I'))) (I_n'))) as H'.
      { rewrite <-Hdefx. by rewrite Hx Hp Hq Hagree HIn. }
      iEval (rewrite -auth_both_op). by iEval (rewrite <-H').
  Qed.


  (** Proof of the lock-coupling template *)

  Lemma traverse_spec (γ γ_fp γ_k γ_c: gname) (root: Node) (k: K) (p n: Node) (Ns: gset Node) I_p C_p I_n C_n:
    ⊢ ⌜k ∈ KS⌝ ∗ css γ γ_fp γ_k γ_c root -∗
    {{{ own γ_fp (◯ Ns) ∗ ⌜p ∈ Ns⌝ ∗ ⌜n ∈ Ns⌝ ∗ ⌜root ∈ Ns⌝ ∗ ⌜n ≠ root⌝
        ∗ node root p I_p C_p ∗ own γ (◯ I_p) ∗ ⌜domm I_p = {[p]}⌝ ∗  ⌜in_inset K k I_p p⌝ ∗ ⌜in_outset K k I_p n⌝
        ∗ own γ_k (◯ prod (keyset K I_p p, C_p)) ∗ node root n I_n C_n ∗ own γ (◯ I_n) ∗ ⌜domm I_n = {[n]}⌝
        ∗ own γ_k (◯ prod (keyset K I_n n, C_n))
    }}}
      traverse #p #n #k @ ⊤
    {{{ (p' n': Node) (Ns': gsetUR Node) (I_p' I_n': inset_flowint_ur K) (C_p' C_n': gset K) (res: bool),
        RET ((#p', #n'), #res);
        own γ_fp (◯ Ns') ∗ ⌜p' ∈ Ns'⌝ ∗ ⌜n' ∈ Ns'⌝ ∗ own γ (◯ I_p') ∗ ⌜domm I_p' = {[p']}⌝ ∗ own γ (◯ I_n')
        ∗ ⌜domm I_n' = {[n']}⌝ ∗ node root p' I_p' C_p' ∗ node root n' I_n' C_n' ∗ ⌜n' ≠ root⌝
        ∗ own γ_k (◯ prod (keyset K I_p' p', C_p'))
        ∗ own γ_k (◯ prod (keyset K I_n' n', C_n'))
        ∗ ⌜in_inset K k I_p' p'⌝ ∗ ⌜in_outset K k I_p' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝ ∗ ⌜res ↔ k ∈ C_n'⌝
    }}}.
  Proof.
    iIntros "(% & #HInv)". iIntros (Φ) "!# H HCont". iLöb as "IH" forall (Ns p n I_p I_n C_p C_n).
    iDestruct "H" as "(#Hfp & % & % & % & % & Hnodep & HIp & % & % & % & Hksp & Hnoden & HIn & % & Hksn)".
    wp_lam. wp_pures. wp_bind (findNext _ _)%E.
    iPoseProof ((own_op γ (◯ I_p) (◯ I_n)) with "[HIp HIn]") as "H"; first by eauto with iFrame.
    iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H9.
    assert (✓ (I_p ⋅ I_n)). { apply (auth_frag_valid (◯ (I_p ⋅ I_n))). done. }
    assert (in_inset K k I_n n).
    { unfold in_inset. fold (inset K I_n n).
      apply (flowint_inset_step I_p I_n k n); try done. set_solver. }
    iDestruct "H" as "(HIp & HIn)".
    wp_apply ((findNext_spec n k I_n C_n root) with "[Hnoden]"). iFrame "∗ % #".
    iIntros (b n' res) "(Hnoden & % & Hb)". rename H12 into Hres. destruct b.
    - iDestruct "Hb" as "%". wp_pures.
      wp_bind (lockNode _)%E.
      awp_apply (lockNode_spec n') without "HCont".
      iInv "HInv" as ">H". iDestruct "H" as (I0 C0) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iPoseProof ((auth_own_incl _ I0 I_n) with "[$HInt $HIn]") as (I2)"%".
      iPoseProof (own_valid with "HIn") as "%".
      iPoseProof (own_valid with "HInt") as "%".
      assert (✓ I_n) as HInv. { apply (auth_frag_valid (◯ I_n)). done. }
      assert (✓ I0) as HI0. { apply (auth_auth_valid (I0)). done. }
      assert (n' ∈ domm I2). { apply (flowint_step I0 I_n I2 k n' root); try done. }
      assert (n' ∈ domm I0).
      { rewrite H14. rewrite flowint_comp_fp. set_solver. rewrite <-H14. done. }
      iMod (own_update γ_fp (● (domm I0)) (● (domm I0) ⋅ ◯ (domm I0)) with "HFP") as "H".
      apply auth_update_core_id. apply gset_core_id. done.
      iDestruct "H" as "(HFP & #Hfp0)".
      rewrite (big_sepS_elem_of_acc _ (domm I0) n'); last by eauto.
      iDestruct "Hstar" as "[Hb Hstar]".
      iDestruct "Hb" as (b) "[Hlock Hb]".
      iAaccIntro with "Hlock". { iIntros "H". iModIntro. iFrame "∗ # %".
      iNext. iExists I0, C0. iFrame "∗ # %". iApply "Hstar".
      iExists b. iFrame "∗ # %". }
      iIntros "(Hlock & H)". destruct b. { iDestruct "H" as %Ht.
      pose proof (diff_false_true) as Hbeq. unfold not in Hbeq.
      exfalso; apply Hbeq. rewrite Ht. done. } iClear "H".
      iDestruct "Hb" as (I_n' C_n') "(HIn' & % & Hnoden' & Hksn')".
      iPoseProof ((own_op γ (◯ I_n) (◯ I_n' )) with "[HIn HIn']") as "H"; first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H20.
      assert (✓ (I_n ⋅ I_n')). { apply (auth_frag_valid (◯ (I_n ⋅ I_n'))). done. }
      iEval (rewrite -auth_frag_op) in "H".
      iPoseProof ((auth_own_incl _ I0 _) with "[$HInt $H]") as (I3)"%".
      iAssert (node root n' I_n' C_n' ∗ ⌜nodeinv root n' I_n' C_n'⌝)%I with "[Hnoden']" as "(Hnoden' & %)".
      { iApply (node_implies_nodeinv _ _ _). iFrame "∗ # %". iPureIntro.
        apply cmra_valid_op_r in H21. done. }
      assert (n' ≠ root) as Hnotf'.
      { apply (successor_not_root I0 I_n I_n' I3 C_n' root n' k); try done. }
      iModIntro. iSplitL "HKS HInt HFP Hcont Hstar Hlock".
      { iNext. iExists I0, C0. iFrame "∗ # %". iApply "Hstar".
      iExists true. iFrame. } iDestruct "H" as "(HIn & HIn')". iIntros "Hc".
      wp_pures. wp_bind (unlockNode _)%E. awp_apply (unlockNode_spec p) without "Hc".
      iInv "HInv" as ">H". iDestruct "H" as (I1 C1) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iAssert (⌜p ∈ domm I1⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I1) (Ns)) with "[$]") as "%".
        apply gset_included in H25.
        iPureIntro. set_solver. }
      iAssert (⌜n ∈ domm I1⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I1) Ns) with "[$]") as "%".
        apply gset_included in H26.
        iPureIntro. set_solver. }
      iAssert (⌜n' ∈ domm I1⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I1)) with "[$]") as "%".
        apply gset_included in H27.
        iPureIntro. set_solver. }
      assert (root ∈ domm I1). { apply globalinv_root_fp. done. }
      rewrite (big_sepS_elem_of_acc _ (domm I1) p); last by eauto.
      iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
      destruct b; last first. { iDestruct "Hb" as (In1 Cn1) "(_ & _ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep' Hnodep]" as %Hf. { iApply (node_sep_star root p In1 I_p _ _).
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros. iModIntro. iFrame "∗ # %". iNext. iExists I1, C1.
      iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
      iMod (own_update γ_fp (● (domm I1)) (● (domm I1) ⋅ ◯ (domm I1)) with "HFP") as "H".
      apply auth_update_core_id. apply gset_core_id. done.
      iDestruct "H" as "(HFP & #Hfp1)".
      iIntros "Hlock". iModIntro. iSplitL "HKS HInt HFP Hcont Hstar Hlock Hnodep HIp Hksp".
      iNext. iExists I1, C1. iFrame "∗ # %". iApply "Hstar". iExists false. iFrame.
      iExists I_p, C_p. iFrame "∗ # %". iIntros "Hc". wp_pures.
      iSpecialize ("IH" $! (domm I1) n n' I_n I_n' C_n C_n').
      iApply ("IH" with "[-Hc]"). iFrame "∗ # %". iNext. done.
    - wp_pures. wp_bind (findNext _ _)%E.
      wp_apply (findNext_spec with "[Hnoden]"). iFrame "∗ %".
      iIntros (suc n0 res0)"(Hnoden & Hres & Hsuc)". iDestruct "Hb" as "(% & %)".
      iDestruct "Hres" as "%". iSpecialize ("HCont" $! p n Ns I_p I_n C_p C_n).
      destruct suc; wp_pures; iApply "HCont"; iFrame "∗ # %".    
  Qed.

  Theorem searchStrOp_spec (γ γ_fp γ_k γ_c: gname) root (k: K):
    ⊢ ⌜k ∈ KS⌝ ∗ css γ γ_fp γ_k γ_c root -∗
    <<< ∀ (C: gset K), css_cont γ_c C >>>
      CSS_insertOp root #k @ ⊤ ∖ ↑N
    <<< ∃ C' (res: bool), css_cont γ_c C' ∗ (Ψ insertOp k C C' res : iProp), RET #res >>>.
  Proof.
    iIntros "(% & #HInv)". iIntros (Φ) "AU". wp_lam. wp_bind (lockNode _)%E.
    awp_apply (lockNode_spec root). iInv "HInv" as ">H".
    iDestruct "H" as (I0 C0) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iMod (own_update γ_fp (● (domm I0)) (● (domm I0) ⋅ ◯ (domm I0)) with "HFP") as "H".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "H" as "(HFP & #Hfp)".
    assert (root ∈ domm I0). { apply globalinv_root_fp. done. }
    rewrite (big_sepS_elem_of_acc _ (domm I0) root); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitR "AU".
    iNext. iExists I0, C0. iFrame "∗ # %". iApply "Hstar".
    iExists b. iFrame "∗ # %". done. }
    iIntros "(Hlock & H)". destruct b. { iDestruct "H" as %Ht.
    pose proof (diff_false_true) as Hbeq. unfold not in Hbeq.
    exfalso; apply Hbeq. rewrite Ht. done. } iClear "H".
    iDestruct "Hb" as (If Cf) "(HIf & % & Hnodef & HCf)".
    iPoseProof ((auth_own_incl _ I0) with "[$HInt $HIf]") as (Io)"%".
    iModIntro. iSplitR "AU HIf Hnodef HCf". iNext.
    iExists I0, C0. iFrame "∗ # %".
    iApply "Hstar". iExists true. iFrame "∗ # %".
    wp_pures. wp_bind(findNext _ _)%E.
    assert (in_inset K k If root). 
    { unfold globalinv in H1. destruct H1 as [? [? [? ?]]].
    specialize (H7 k). apply (inset_monotone I0 If Io k root); try done.
    by apply H7. set_solver. }
    wp_apply ((findNext_spec root k If Cf root) with "[Hnodef]").
    { iFrame "∗ # %". } iIntros (b n res0) "(Hnodef & Hres & Hb)".
    iDestruct "Hres" as %Hres.
    destruct b; last first. wp_pures. iDestruct "Hb" as "(% & %)".
    exfalso. apply H6. done. iDestruct "Hb" as "%". wp_pures.
    wp_bind (lockNode _)%E. awp_apply (lockNode_spec n). iInv "HInv" as ">H".
    iDestruct "H" as (I2 C2) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iPoseProof (own_valid with "HInt") as "%". rename H7 into Hcheck.
    assert (✓ I2) as HI2. { apply (auth_auth_valid (I2)). done. }
    iPoseProof ((auth_own_incl _ I2) with "[$HInt $HIf]") as (Io')"%".
    assert (n ∈ domm I2).
    { assert (n ∈ domm Io').
      { apply (flowint_step I2 If Io' k n root); try done. }
      rewrite H7. rewrite flowint_comp_fp. set_solver. rewrite <-H7. done. }
    rewrite (big_sepS_elem_of_acc _ (domm I2) n); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitR "AU HIf HCf Hnodef".
    iNext. iExists I2, C2. iFrame "∗ # %". iApply "Hstar".
    iExists b. iFrame "∗ # %". iFrame "∗ # %". }
    iIntros "(Hlock & H)". destruct b. { iDestruct "H" as %Ht.
    pose proof (diff_false_true) as Hbeq. unfold not in Hbeq.
    exfalso; apply Hbeq. rewrite Ht. done. } iClear "H".
    assert (root ∈ domm I2). { apply globalinv_root_fp. done. }
    iMod (own_update γ_fp (● (domm I2)) (● (domm I2) ⋅ ◯ (domm I2)) with "HFP") as "H".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "H" as "(HFP & #Hfp2)".
    iDestruct "Hb" as (In Cn) "(HIn & % & Hnoden & HCn)".
    iPoseProof ((own_op γ (◯ If) (◯ In)) with "[HIf HIn]") as "H"; first by eauto with iFrame.
    iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H12.
    assert (✓ (If ⋅ In)). { apply (auth_frag_valid (◯ (If ⋅ In))). done. }
    iEval (rewrite -auth_frag_op) in "H".
    iPoseProof ((auth_own_incl _ I2) with "[$HInt $H]") as (Iu)"%".
    iAssert (node root n In Cn ∗ ⌜nodeinv root n In Cn⌝)%I with "[Hnoden]" as "(Hnoden & %)".
    { iApply (node_implies_nodeinv root n In Cn). iFrame "∗ # %". iPureIntro.
      apply cmra_valid_op_r in H12. done. }  iDestruct "H" as "(HIf & HIn)".
    assert (n ≠ root).
    { apply (successor_not_root I2 If In Iu Cn root n k); try done. }
    iModIntro. iSplitR "AU HIf HCf Hnodef HIn Hnoden HCn". { iNext. iExists I2, C2.
    iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
    wp_pures. wp_bind (traverse _ _ _)%E.
    wp_apply ((traverse_spec γ γ_fp γ_k γ_c root k root n (domm I2) If Cf In Cn)
                 with "[] [HIf HCf Hnodef HIn HCn Hnoden]").
    iFrame "∗ # %". iFrame "∗ # %".
    iIntros (p' n' Ns Ip' In' Cp' Cn' res1) "(#HNs & % & % & HIp' & % & HIn' & % & Hnodep' & Hnoden'
                        & % & Hksp' & Hksn' & % & % & %)".
    wp_pures. destruct res1.
    {  
      iInv "HInv" as ">H".
      iDestruct "H" as (I3 C3) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iPoseProof (own_valid with "HKS") as "%".
      iPoseProof (own_valid with "Hksn'") as "%".
      iPoseProof ((auth_own_incl γ_k (prod (KS, C3)) _) with "[HKS Hksn']") as "%".
      iFrame. rewrite auth_auth_valid in H26 *; intros H26.
      rewrite auth_frag_valid in H27 *; intros H27.
      pose proof (auth_ks_included (keyset K In' n') KS Cn' C3 H27 H26 H28).
      iMod "AU" as (C') "[Hc [_ Hclose]]". iEval (rewrite /css_cont) in "Hc".
      iDestruct (auth_agree with "Hcont Hc") as %<-.
      wp_pures. 
      iSpecialize ("Hclose" $! C3 false).
      iMod ("Hclose" with "[Hc]") as "HΦ". iFrame.
      unfold Ψ. iPureIntro. destruct H24 as (_ & H24).
      assert (k ∈ Cn'). apply H24. done.
      assert (Cn' ⊆ C3). destruct H29.
      clear -H29. set_solver. destruct H29 as [a [b [_ [H29 _]]]].
      clear -H29. set_solver. clear -H30 H31. split; set_solver.
      iModIntro. iModIntro. iSplitR "HΦ". iNext. iExists I3, C3. iFrame "∗ %".
      done.
    }
    {
      wp_pures.      
      wp_apply (alloc_spec); first done.
      iIntros (m lm) "(Hrepm & % & Hlm)". wp_pures. wp_bind (decisiveOp _ _ _ _)%E.
      iApply fupd_wp. iInv "HInv" as ">H".
      iDestruct "H" as (I3 C3) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      destruct (decide (m ∈ domm I3)). { rewrite (big_sepS_elem_of_acc _ (domm I3) m); last by eauto.
      iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
      iEval (rewrite H25) in "Hlockm". iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%".
      exfalso. done. }
      assert (root ∈ domm I3). { apply globalinv_root_fp. done. }
      assert (m ≠ root). { set_solver. }
      iPoseProof ((own_op γ (◯ Ip') (◯ In')) with "[HIp' HIn']") as "HIpn'"; first by eauto with iFrame.
      iPoseProof (own_valid with "HIpn'") as "%". rename H29 into Valid_Ipn'.
      rewrite -auth_frag_op in Valid_Ipn'. rewrite auth_frag_valid in Valid_Ipn' *; intros Valid_Ipn'.
      iPoseProof ((own_op γ_k _ _) with "[Hksp' Hksn']") as "Hkspn'"; first by eauto with iFrame.
      iPoseProof (own_valid with "Hkspn'") as "%". rename H29 into Valid_kspn'.
      rewrite -auth_frag_op in Valid_kspn'. rewrite auth_frag_valid in Valid_kspn' *; intros Valid_kspn'.
      unfold op, cmra_op in Valid_kspn'. simpl in Valid_kspn'.
      unfold ucmra_op in Valid_kspn'. simpl in Valid_kspn'. repeat case_decide; try done .
      rename H29 into Subset_c_ks_n'. rename H30 into Subset_c_ks_p'.
      rename H31 into Disj_ks_pn'. rename H32 into Disj_c_pn'. iEval (rewrite -auth_frag_op) in "HIpn'".
      iPoseProof ((auth_own_incl _ I3) with "[$HInt $HIpn']") as (Iw)"%". rename H29 into Valid_I3.
      assert (out (Ip'⋅In') m = 0%CCM) as Out_zero_pn'.
      { 
        apply (intComp_out_zero Iw (Ip'⋅In') m).
        rewrite intComp_comm. destruct H26 as [H26 _].
        by rewrite <-Valid_I3.
        rewrite intComp_comm. by rewrite <-Valid_I3.
        rewrite intComp_comm. rewrite <-Valid_I3.
        unfold globalinv in H26. destruct H26 as (_ & _ & H26 & _).
        apply nzmap_eq. intros k0. pose proof (H26 k0 m).
        unfold outset, dom_ms in H29. 
        rewrite (nzmap_elem_of_dom_total) in H29 *; intros H29.
        apply dec_stable in H29. by rewrite nzmap_lookup_empty. 
      }    
      iModIntro. iSplitL "HKS HInt HFP Hcont Hstar". iNext.
      iExists I3, C3. iFrame "∗ # %". iModIntro. destruct H24 as [H24 Hk_not0].
      assert (k ∉ Cn') as Hk_not1. { unfold not. apply Hk_not0. }
      wp_apply ((decisiveOp_insert_spec root p' n' m k Ip' In' Cp' Cn')
            with "[Hnodep' Hnoden' Hrepm]"). { iFrame "∗ % #". iPureIntro. set_solver. }
      iIntros (Cp'' Cn'' Cm'' Ip'' In'' Im'' res) "(Hnodep' & Hnoden' & Hnodem' & #HΨ & % & Hminf & H)".
      iDestruct "H" as "(% & % & % & %)".
      iDestruct "Hminf" as %Hminf. 
      iApply fupd_wp. iInv "HInv" as ">H".
      iDestruct "H" as (I4 C4) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iMod "AU" as (C') "[Hc [_ Hclose]]". iEval (rewrite /css_cont) in "Hc".
      iDestruct (auth_agree with "Hcont Hc") as %<-.
  
      (* ------ keyset update -------*)
      
      iAssert (⌜Cp'' ⊆ keyset K Ip'' p' ∧ domm Ip'' = {[p']}⌝)%I with "[Hnodep']" as "%".
      { iPoseProof (node_implies_nodeinv with "[Hnodep']") as "H". iFrame.
        iPureIntro. unfold contextualLeq in H29. destruct H29 as [_ [H29 _]].
        by repeat apply cmra_valid_op_l in H29. iDestruct "H" as "(_ & %)".
        unfold nodeinv in H35. destruct H35 as [Hdom [H35 ]]. by iPureIntro. } 
      iAssert (⌜Cn'' ⊆ keyset K In'' n' ∧ domm In'' = {[n']}⌝)%I with "[Hnoden']" as "%".
      { iPoseProof (node_implies_nodeinv with "[Hnoden']") as "H". iFrame.
        iPureIntro. unfold contextualLeq in H29. destruct H29 as [_ [H29 _]].
        apply cmra_valid_op_l in H29. by apply cmra_valid_op_r in H29.
        iDestruct "H" as "(_ & %)". unfold nodeinv in H36.
        destruct H36 as [Hdom [H36 ]]. by iPureIntro. } 
      iAssert (⌜Cm'' ⊆ keyset K Im'' m ∧ domm Im'' = {[m]}⌝)%I with "[Hnodem']" as "%".
      { iPoseProof (node_implies_nodeinv with "[Hnodem']") as "H". iFrame.
        iPureIntro. unfold contextualLeq in H29. destruct H29 as [_ [H29 _]].
      by repeat apply cmra_valid_op_r in H29. iDestruct "H" as "(_ & %)".
      unfold nodeinv in H37. destruct H37 as [Hdom [H37 ]]. by iPureIntro. }
      destruct H35 as [Sub_p Dom_p]. destruct H36 as [Sub_n Dom_n].
      destruct H37 as [Sub_m Dom_m].
      assert (Cp'' ## Cn'') as Disj_pn. { clear -Sub_p Sub_n H30. set_solver. }
      assert (Cn'' ## Cm'') as Disj_nm. { clear -Sub_m Sub_n H32. set_solver. }
      assert (Cm'' ## Cp'') as Disj_pm. { clear -Sub_p Sub_m H31. set_solver. }
      iEval (rewrite -auth_frag_op) in "Hkspn'".
      assert (prod (keyset K Ip'' p', Cp'') ⋅ prod (keyset K In'' n', Cn'') ⋅ prod (keyset K Im'' m, Cm'')
                   = prod (keyset K Ip'' p' ∪ keyset K In'' n' ∪ keyset K Im'' m, Cp'' ∪ Cn'' ∪ Cm'')).
      { unfold op, prodOp. repeat case_decide; try done. exfalso. apply H42. set_solver by eauto.
        exfalso. apply H41. clear - H30 H31 H32. set_solver by eauto. exfalso. apply H39. set_solver by eauto. }
      assert (◯ (prod (keyset K Ip'' p', Cp'') ⋅ prod (keyset K In'' n', Cn'') ⋅ prod (keyset K Im'' m, Cm''))
                   = ◯ (prod (keyset K Ip'' p' ∪ keyset K In'' n' ∪ keyset K Im'' m, Cp'' ∪ Cn'' ∪ Cm''))).
      { rewrite H35. reflexivity. }
      assert ((prod (keyset K Ip' p', Cp') ⋅ prod (keyset K In' n', Cn'))
                    = prod (keyset K Ip' p' ∪ keyset K In' n', Cp' ∪ Cn')).
      { unfold op, prodOp. repeat case_decide; try done. }
      assert (in_inset K k In' n'). {
        apply (flowint_inset_step Ip' In' k n'); try done. rewrite H20. clear. set_solver. }
      assert (k ∈ keyset K In' n'). { apply keyset_def; try done. }
      iMod ((ghost_update_keyset γ_k insertOp k (Cp' ∪ Cn') (Cp'' ∪ Cn'' ∪ Cm'') res
                   (keyset K Ip' p' ∪ keyset K In' n') C4) with "[HKS Hkspn']") as "Hgks".
      iEval (rewrite comm) in "Hkspn'".             
      iEval (rewrite H37) in "Hkspn'". iFrame "∗ # %". iPureIntro.
      split. rewrite <-H33. clear -Sub_p Sub_n Sub_m. set_solver. clear -H39. set_solver.
      iDestruct "Hgks" as (C4') "(#HΨ' & HKS & H)". iEval (rewrite <-H33) in "H".
      iAssert (own γ_k (◯ (prod (keyset K Ip'' p', Cp'') ⋅ prod (keyset K In'' n', Cn'') ⋅ prod (keyset K Im'' m, Cm''))))
            with "[H]" as "Hv". { iEval (rewrite H35). done. }
      iDestruct "Hv" as "((Hksp' & Hksn') & Hksm')".
      iMod (auth_excl_update γ_c (C4') with "Hcont Hc") as "[Hcont Hc]".
      clear H39 H37 H36 H35 Disj_pm Disj_nm Disj_pn Sub_m Sub_n Sub_p H30 H31 H32 H33
            Hk_not1 Hk_not0 Valid_I3 Out_zero_pn' Iw Valid_kspn' Disj_c_pn' Disj_ks_pn'
            Subset_c_ks_p' Subset_c_ks_n' H27 n0 H26 C3 I3 H15 H14 H16 Iu H13 H12 H11 
            Cn In H10 H9 H7 Io' HI2 H8 Hcheck C2 H6 Hres res0 n H5 H4 Io H3 Cf If 
            H2 H1 C0.
            
      (* ------ interface update -------*)
  
      destruct (decide (m ∈ domm I4)). { rewrite (big_sepS_elem_of_acc _ (domm I4) m); last by eauto.
      iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
      iEval (rewrite H25) in "Hlockm". iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%".
      exfalso. done. }
      assert (◯ Ip' ⋅ ◯ In' = ◯ (Ip' ⋅ In')).
      by rewrite auth_frag_op. iCombine "HInt" "HIpn'" as "Hownint".
      iPoseProof (own_valid with "Hownint") as "%".
      apply auth_both_valid in H2. destruct H2. destruct H2 as [Iz H2].
      iDestruct "Hownint" as "[HInt H']".
      destruct H29 as (Hvldpn & Hvldpnm & Hsub & Hinf & Hout).
      assert (domm (Ip'' ⋅ In'' ⋅ Im'') = domm Ip'' ∪ domm In'' ∪ domm Im''). 
      repeat rewrite (flowint_comp_fp); try done. by apply cmra_valid_op_l in Hvldpnm.
      rewrite Dom_p Dom_n Dom_m in H4.
      assert (m ∉ domm Iz). { apply leibniz_equiv in H2. rewrite H2 in n.
      rewrite (flowint_comp_fp) in n. set_solver. apply leibniz_equiv_iff in H2.
      rewrite <-H2. done. }
      unfold globalinv in H34. destruct H34 as (Hv & H4root & H4out & H4in).
      assert (out Iz m = 0%CCM).
      { 
        apply (intComp_out_zero (Ip'⋅In') Iz m). by rewrite <-H2.
        rewrite <-H2. done. rewrite <-H2. apply nzmap_eq.
        intros km. pose proof (H4out km m).
        unfold outset, dom_ms in H6. rewrite (nzmap_elem_of_dom_total) in H6 *; intros.
        apply dec_stable in H6. rewrite H6.
        by rewrite nzmap_lookup_empty.
      }    
      iMod (own_updateP (flowint_update_P K_multiset I4 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')) γ
                            (● I4 ⋅ ◯ (Ip' ⋅ In')) with "[HInt H']") as (Io'') "H0".
      {
        rewrite H2.
        apply (flowint_update K_multiset (Iz) (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')).
        repeat split; try done. apply leibniz_equiv in H2. assert (H4valid := H3).
        rewrite H2 in H3. apply intComposable_valid in H3. unfold intComposable in H3.
        destruct H3 as (_ & _ & Hdisj & _). rewrite flowint_comp_fp in Hdisj; last first.
        rewrite H2 in H4valid; by apply cmra_valid_op_l in H4valid.
        rewrite H4. rewrite H19 H20 in Hdisj. clear -Hdisj H5. set_solver.
        intros nf. rewrite flowint_comp_fp; try done. 
        repeat rewrite (flowint_comp_fp); last by apply cmra_valid_op_l in Hvldpnm.
        rewrite Dom_p Dom_n Dom_m H19 H20. intros Hnf. assert (nf = m). set_solver. replace nf.
        unfold out in H6. done. done.
      }
      { try repeat rewrite own_op; iFrame. }
      iPoseProof ((flowint_update_result γ I4 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im''))
                        with "H0") as (I') "(% & % & HIIpnm)".
      iEval (rewrite own_op) in "HIIpnm". iDestruct "HIIpnm" as "(HI' & HIpnm'')".
      iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
      iPoseProof (own_valid with "HIpnm''") as "%".
      assert (✓ (Ip'' ⋅ In'' ⋅ Im'')) as HIpnmcheck.
      { apply (auth_frag_valid (◯ (Ip'' ⋅ In'' ⋅ Im''))). done. }
      iEval (rewrite auth_frag_op) in "HIpnm''".
      iDestruct "HIpnm''" as "(HIpn'' & HIm'')".
      iPoseProof (own_valid with "HIpn''") as "%".
      assert (✓ (Ip'' ⋅ In'')) as HIpncheck.
      { apply (auth_frag_valid (◯ (Ip'' ⋅ In''))). done. }
      iEval (rewrite auth_frag_op) in "HIpn''".
      iDestruct "HIpn''" as "(HIp'' & HIn'')".
      destruct (decide (m ∈ domm I4)). { rewrite (big_sepS_elem_of_acc _ (domm I4) m); last by eauto.
      iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
      iEval (rewrite H25) in "Hlockm". iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%".
      exfalso. done. }
      iMod (own_update γ_fp (● domm I4) (● (domm I4 ∪ {[m]}) ⋅ ◯ (domm I4 ∪ {[m]})) with "[HFP]") as "H".
      { apply (auth_update_alloc (domm I4) (domm I4 ∪ {[m]}) (domm I4 ∪ {[m]})).
        apply gset_local_update. set_solver. }
      done. iDestruct "H" as "(HFP & #Hfp4)".
      assert (domm I' = domm I4 ∪ {[m]}).
      {
        destruct H8 as [I_o H8]. destruct H8.
        assert (domm I' = {[p']} ∪ {[n']} ∪ {[m]} ∪ domm I_o).
        {
          subst I'. repeat rewrite flowint_comp_fp; try congruence; try done.
          by apply (auth_auth_valid).
        }
        assert (domm I4 = {[p']} ∪ {[n']} ∪ domm I_o).
        {
          subst I4. repeat rewrite flowint_comp_fp; try congruence; try done.
        }
        rewrite H13 H14.
        clear. set_solver.
      }
      
      assert (globalinv K root I'). {
        apply (contextualLeq_impl_globalinv I4 I').
        all : trivial.
        unfold globalinv. repeat split; try done.
        intros.
        assert (n1 = m). { clear - H12 n0 H13. set_solver. } subst n1.
        unfold inset. unfold dom_ms. unfold inf. case_eq (inf_map I' !! m); last first.
        - intros Hm. unfold ccmunit, ccm_unit. simpl. unfold nzmap_dom. simpl. set_solver.
        - intros k0 Hk0. simpl. destruct H8 as [Iz' [H8 ?]]. 
          rewrite H8 in H2. apply intComp_cancelable in H2; last by rewrite H8 in H3.
          apply leibniz_equiv in H2. subst Iz'.
          assert (inf (Ip'' ⋅ In'' ⋅ Im'' ⋅ Iz) m = (inf (Ip'' ⋅ In''⋅ Im'') m) - (out Iz m))%CCM.
          { apply intComp_inf_1. apply leibniz_equiv_iff in H14. rewrite <-H14.
            by apply auth_auth_valid.
            assert (domm (Ip'' ⋅ In'' ⋅ Im'') = domm Ip'' ∪ domm In'' ∪ domm Im''). 
            repeat rewrite (flowint_comp_fp); try done. rewrite H2.
            rewrite Dom_m. clear. set_solver.
          }
          rewrite Hminf in H2. rewrite <-H14 in H2.
          rewrite H6 in H2. rewrite ccm_pinv_unit in H2. unfold inf in H2. rewrite Hk0 in H2.
          simpl in H2. rewrite H2. unfold ccmunit, lift_unit, nzmap_unit. simpl.
          unfold nzmap_dom. simpl. set_solver.
      }
      iEval (rewrite <-H12) in "HFP". assert (domm I'∖ {[m]} = domm I4). 
      { clear -n0 H12. set_solver. }
  
      (* ------ updates over -------*)
  
      iMod ("Hclose" with "[Hc]") as "HΦ". iFrame "∗ % #".
      iModIntro. iSplitL "Hstar Hlm Hnodem' HKS Hcont HI' HIm'' HFP Hksm'". iNext. iExists I', C4'.
      iFrame "∗ # %". rewrite (big_sepS_delete _ (domm I') m); last set_solver. iEval (rewrite H14).
      iFrame. iExists false. iEval (rewrite H25). iFrame. iExists Im'', Cm''. eauto with iFrame.
      iModIntro. wp_pures. wp_bind (unlockNode _)%E.
  
      (* ------ linearization over -------*)
  
      awp_apply (unlockNode_spec p') without "HΦ". iInv "HInv" as ">H".
      iDestruct "H" as (I6 C6) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iAssert (⌜p' ∈ domm I6⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I6) Ns) with "[$]") as "%".
        apply gset_included in H16.
        iPureIntro. clear -H16 H17. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I6) p'); last by eauto.
      iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
      destruct b; last first. { iDestruct "Hb" as (In0 Cn0) "(_ & _ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hnodep' Hrep']" as %Hf. { iApply (node_sep_star root p' Ip'' In0 _ _).
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". 
      { iIntros. iModIntro. iFrame "∗". iNext. iExists I6, C6.
        iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
      iIntros. iModIntro.
      iSplitR "Hnoden' Hksn' HIn''". iNext. iExists I6, C6.
      iFrame "∗ # %". iApply "Hstar". iExists false. iFrame. iExists Ip'', Cp''. iFrame "∗ %".
  
      iIntros "HΦ".
      wp_pures. wp_bind (unlockNode _)%E.
      awp_apply (unlockNode_spec n') without "HΦ".
      iInv "HInv" as ">H". iDestruct "H" as (I7 C7) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iAssert (⌜n' ∈ domm I7⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I7) Ns) with "[$]") as "%".
        apply gset_included in H27.
      iPureIntro. clear -H18 H27. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I7) n'); last by eauto.
      iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
      destruct b; last first. { iDestruct "Hb" as (In0 Cn0) "(_ & _ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hnoden' Hrep']" as %Hf. { iApply (node_sep_star root n' In'' In0 _ _).
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock".
      { iIntros. iModIntro. iFrame "∗ # %". iNext. iExists I7, C7.
        iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
      iIntros. iModIntro.
      iSplitL. iNext. iExists I7, C7.
      iFrame "∗ # %". iApply "Hstar". iExists false. iFrame. iExists In'', Cn''. iFrame "∗ %".
  
      iIntros "HΦ". wp_pures. done.
      }
    Qed.

End Coupling_Template.
