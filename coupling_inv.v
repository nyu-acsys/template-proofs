(** Verification of lock coupling template algorithm *)

From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "All".
Require Export keyset_ra inset_flows ccm flows.

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
  Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (authUR (keysetUR K)) }.
  Definition keysetΣ : gFunctors := #[GFunctor (authUR (keysetUR K))].

  Instance subG_keysetΣ {Σ} : subG keysetΣ Σ → keysetG Σ.
  Proof. solve_inG. Qed.

  (* RA for set of contents *)
  Class contentG Σ :=
    ContentG { content_inG :> inG Σ (authR (optionUR (exclR (gsetR K)))) }.
  Definition contentΣ : gFunctors :=
    #[GFunctor (authR (optionUR (exclR (gsetR K))))].

End Coupling_Cameras.

(** Verification of the template *)
Section Coupling_Template.

  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ, !contentG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (** The code of the coupling template. *)

  Inductive dOp := memberOp | insertOp | deleteOp.

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b+-tree.spl and
   * hashtbl-give-up.spl for the concrete implementations. *)

  Parameter findNext : val.
  Parameter decisiveOp : (dOp → val).
  Parameter lockLoc : Node → loc.
  Parameter getLockLoc : val.
  Parameter alloc : val.

  Definition lockNode : val :=
    rec: "lockN" "x" :=
      let: "l" := getLockLoc "x" in
      if: CAS "l" #false #true
      then #()
      else "lockN" "x".

  Definition unlockNode : val :=
    λ: "x",
    let: "l" := getLockLoc "x" in
    "l" <- #false.

  Definition traverse : val :=
    rec: "tr" "p" "n" "k" :=
      match: (findNext "n" "k") with
        NONE => ("p", "n")
      | SOME "n'" =>
        lockNode "n'";; unlockNode "p";; "tr" "n" "n'" "k"
      end.

  Definition CSSOp (Ψ: dOp) (root: Node) : val :=
    λ: "k",
    lockNode #root;;
    let: "n0" := (findNext #root "k") in
    match: "n0" with
      NONE => ""
    | SOME "n0" =>
      lockNode "n0";;
      let: "pn" := traverse #root "n0" "k" in
      let: "p" := Fst "pn" in
      let: "n" := Snd "pn" in
      let: "m" := alloc #() in
      let: "res" := (decisiveOp Ψ) "p" "n" "k" in
      unlockNode "p";; unlockNode "n";; "res" end.


  (** Assumptions on the implementation made by the template proofs.
   * Matching definitions can be found in GRASShopper file list-coupling.spl *)

  (* The node predicate is specific to each template implementation. *)
  Parameter node : Node → Node → inset_flowint_ur K → gset K → iProp.
  (* TODO change node n root I C → node root n I C*)

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ n root I C, Timeless (node n root I C).
  Instance node_timeless n root I C: Timeless (node n root I C).
  Proof. apply node_timeless_proof. Qed.

  (* Spatial part of node predicate. *)
  Parameter hrep_spatial : Node → iProp.


  (* TODO: can we get rid of the following? *)
  Instance ccm_ms : CCM (@K_multiset K _ _) := @K_multiset_ccm K _ _.

  (* The node-local invariant. 
   * See list-coupling.spl for the corresponding GRASShopper definition.*)
  (* TODO there's a slight discrepancy between this and grasshopper. *)
  Definition nodeinv root n (I_n : inset_flowint_ur K) C_n : Prop :=
    n ∈ domm I_n
    ∧ C_n ⊆ keyset K I_n n
    ∧ (∀ k : K, default 0 (inf I_n n !! k) ≤ 1)
    ∧ (n = root → ∀ k : K, k ∈ KS → in_outsets K k I_n).

  (* The following hypotheses are proved as GRASShopper lemmas in
   * list-coupling.spl *)
  Hypothesis node_implies_nodeinv : ∀ n I_n C root,
    (⌜✓I_n⌝)%I ∗ node n root I_n C
    -∗ node n root I_n C ∗ (⌜nodeinv root n I_n C⌝)%I.

  Hypothesis node_sep_star: ∀ n I_n I_n' C C' root,
    node n root I_n C ∗ node n root I_n' C' -∗ False.

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
    destruct NI as (n_in_I2 & _ & inf_bound & _).
    assert (n ∈ domm I2 ∪ domm I3) as n_in_I23 by set_solver.
    pose proof (intComp_unfold_inf_2 _ _ VI n) as inf_I23.
    rewrite intComp_dom in inf_I23.
    apply inf_I23 in n_in_I23 as n_inf_I23.
    unfold cmra_op, flowintRA, cmra_car, K_multiset at 5, K_multiset at 5, ccm_ms at 3 in n_inf_I23.
    pose proof (I_inf_out root) as (root_out & _).
    assert (root = root) by reflexivity.
    pose proof (root_out H k) as root_out_k.

    assert (default 0 (inf I n !! k) ≠ 0).
    rewrite e.
    unfold inset, dom_ms, nzmap_dom in root_out_k.
    apply elem_of_dom in root_out_k.
    unfold lookup, nzmap_lookup.
    pose proof (nzmap_is_wf _ _ (inf I root)) as inf_root_wf.
    pose proof (nzmap_lookup_wf _ _ _ k inf_root_wf).
    destruct (inf I root).
    simpl in root_out_k.
    unfold is_Some in root_out_k.
    destruct root_out_k as [x root_out_k].
    rewrite root_out_k.
    simpl in H0.
    simpl.
    naive_solver.
    pose proof (lookup_op _ _ (inf I n) (out I1 n) k) as inf_I23_def.

    rewrite IDef in inf_I23_def.
    unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I23_def.
    unfold ccm_op, lift_ccm in n_inf_I23.

    unfold K_multiset_ccm at 1, lift_ccm in n_inf_I23.
    rewrite <- n_inf_I23 in inf_I23_def.
    unfold cmra_op, flowintRA, cmra_car in IDef.
    rewrite <- IDef in inf_I23_def.

    pose proof (inf_I2 n n_in_I2) as n_inf_I2.
    pose proof (lookup_op _ _ (inf (I2 ⋅ I3) n) (out I3 n) k) as inf_I2_def.
    unfold cmra_op, flowintRA, cmra_car, nzmap_total_lookup in inf_I2_def.
    unfold cmra_op, flowintRA, cmra_car, K_multiset at 3, ccm_ms at 2 in n_inf_I2.
    unfold K_multiset_ccm, ccm_op, lift_ccm in n_inf_I2.
    rewrite <- n_inf_I2 in inf_I2_def.
    rewrite inf_I23_def in inf_I2_def.

    assert (default 0 (out I1 n !! k) ≠ 0).
    unfold outset, dom_ms, nzmap_dom in k_in_out1.
    apply elem_of_dom in k_in_out1.
    unfold lookup, nzmap_lookup.
    pose proof (nzmap_is_wf _ _ (out I1 n)) as out_n_wf.
    pose proof (nzmap_lookup_wf _ _ _ k out_n_wf).
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
    rewrite <- Heqx2 in inf_I2_def.
    remember (inf I n !! k) as x.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx.
    rewrite <- Heqx in inf_I2_def.
    remember (out I1 n !! k) as x1.
    unfold K_multiset at 1, nat_ccm, nat_unit, nat_op in Heqx1.
    rewrite <- Heqx1 in inf_I2_def.
    lia.
    all: trivial.
  Qed.

  (** Coarse-grained specification *)

  Definition Ψ dop k (C: gsetO K) (C': gsetO K) (res: bool) : Prop :=
    match dop with
    | memberOp => C' = C ∧ if res then k ∈ C else k ∉ C
    | insertOp => C' = union C {[k]} ∧ if res then k ∉ C else k ∈ C
    | deleteOp => C' = difference C {[k]} ∧ if res then k ∈ C else k ∉ C
    end.



  (** Helper functions specs *)

  (* Sid: we can also try to get rid of getLockLoc and just do CAS (lockLoc "l") #true #false in lock, etc. *)
  Parameter getLockLoc_spec : ∀ (n: Node),
      ({{{ True }}}
           getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  (* The following functions are proved for each implementation in GRASShopper
   * (see list-coupling.spl) *)

  Parameter findNext_spec : ∀ root (n: Node) (I_n : inset_flowint_ur K) (C: gset K) (k: K),
      ({{{ node n root I_n C ∗ ⌜in_inset K k I_n n⌝ }}}
           findNext #n #k
       {{{ (b: bool) (n': Node),
              RET (match b with true => (SOMEV #n') | false => NONEV end);
               node n root I_n C ∗ (match b with true => ⌜in_outset K k I_n n'⌝ |
                                          false => ⌜¬in_outsets K k I_n⌝ ∗ ⌜n ≠ root⌝ end) }}})%I.

  Parameter decisiveOp_insert_spec : ∀ dop root (p n m: Node) (k: K) (I_p I_n: inset_flowint_ur K) (C_p C_n: gset K),
      ({{{ node p root I_p C_p ∗ node n root I_n C_n ∗ hrep_spatial m ∗ ⌜n ≠ root⌝ ∗ ⌜m ≠ root⌝
                          ∗ ⌜in_inset K k I_p p⌝ ∗ ⌜in_outset K k I_p n ⌝ ∗ ⌜¬in_outsets K k I_n⌝ }}}
           decisiveOp dop #p #n #k
       {{{ (C_p' C_n' C_m': gset K) (I_p' I_n' I_m': flowintUR K_multiset) (res: bool), RET  #res;
                           node p root I_p' C_p' ∗ node n root I_n' C_n' ∗ node m root I_m' C_m'
                         ∗ ⌜Ψ dop k (C_p ∪ C_n) (C_p' ∪ C_n' ∪ C_m') res⌝
                         ∗ ⌜contextualLeq _ (I_p ⋅ I_n) (I_p' ⋅ I_n' ⋅ I_m')⌝
                         ∗ ⌜domm I_p' = {[p]}⌝ ∗ ⌜domm I_n' = {[n]}⌝ ∗ ⌜domm I_m' = {[m]}⌝
                         ∗ ⌜C_p' ⊆ keyset K I_p' p⌝ ∗ ⌜C_n' ⊆ keyset K I_n' n⌝ ∗ ⌜C_m' ⊆ keyset K I_m' m⌝
                         ∗ ⌜keyset K I_p' p ## keyset K I_n' n⌝ ∗ ⌜keyset K I_p' p ## keyset K I_m' m⌝
                         ∗ ⌜keyset K I_m' m ## keyset K I_n' n⌝ ∗ ⌜C_p' ## C_n'⌝ ∗ ⌜C_m' ## C_n'⌝ ∗ ⌜C_p' ## C_m'⌝
                         ∗ ⌜keyset K I_p' p ∪ keyset K I_n' n ∪ keyset K I_m' m = keyset K I_p p ∪ keyset K I_n n⌝ }}})%I.

  Parameter alloc_spec :
      ({{{ True }}}
           alloc #()
       {{{ (m: Node) (l:loc), RET #m; hrep_spatial m ∗ ⌜lockLoc m = l⌝ ∗ l ↦ #false }}})%I.


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
                 own γ (◯ I_n) ∗ ⌜domm I_n = {[n]}⌝ ∗ node n root I_n C_n
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

  Lemma globalinv_root_fp: ∀ I root, globalinv K root I → root ∈ domm I.
  Proof.
    intros I root Hglob. unfold globalinv in Hglob.
    destruct Hglob as [H1 [H2 H3]]. done.
  Qed.

  Lemma auth_set_incl (γ_fp: gname) (Ns: gsetUR Node) Ns' :
    own γ_fp (◯ Ns) ∗ own γ_fp (● Ns') -∗ ⌜Ns ⊆ Ns'⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro.
    rewrite auth_valid_discrete. simpl. rewrite ucmra_unit_right_id_L.
    intros. destruct H. inversion H0 as [m H1].
    destruct H1. destruct H2. apply gset_included in H2.
    apply to_agree_inj in H1. set_solver.
  Qed.

  Lemma auth_own_incl γ (x y: inset_flowint_ur K) :
    own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro.
    apply auth_both_valid.
  Qed.

  Lemma auth_own_incl_ks γ (x y: keysetUR K) :
    own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H. destruct H. destruct H0 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y = y) as Hy.
    { rewrite /(⋅) /=. destruct y; try done. }
    rewrite Hy in Hb. rewrite <- Ha in Hb. done.
  Qed.

  Lemma auth_agree γ xs ys :
  own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

  Lemma auth_update γ ys xs1 xs2 :
    own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { apply auth_update. apply option_local_update. apply exclusive_local_update. done. }
    done.
  Qed.

  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P K_multiset I I_n I_n' x⌝ ∧ own γ x -∗
    ∃ I', ⌜contextualLeq K_multiset I I'⌝
          ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
          ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (auth_auth_proj x); last first.
    - intros H. iIntros "(% & ?)". iExFalso. done.
    - intros p. intros H. case_eq p. intros q a Hp.
      iIntros "[% Hown]". destruct H0 as [I' H0].
      destruct H0. destruct H1. destruct H2. destruct H3.
      iExists I'.
      iSplit. iPureIntro. apply H3.
      iSplit. iPureIntro. apply H4.
      assert (Auth (auth_auth_proj x) (auth_frag_proj x) = x) as Hx.
      { destruct x. reflexivity. }
      assert (x = (Auth (Some (1%Qp, to_agree(I'))) (I_n'))) as H'.
      { rewrite <-Hx. rewrite H. rewrite <-H2. rewrite Hp. rewrite H1.
       rewrite H0. reflexivity. }
      assert (● I' = Auth (Some (1%Qp, to_agree(I'))) ε) as HI'. { reflexivity. }
      assert (◯ I_n' = Auth ε I_n') as HIn'. { reflexivity. }
      assert (ε ⋅ I_n' = I_n') as HeIn.
      { rewrite /(⋅) /=. rewrite left_id. done. }
      assert (Some (1%Qp, to_agree I') ⋅ None = Some (1%Qp, to_agree I')) as Hs.
      { rewrite /(⋅) /=.
        rewrite /(cmra_op (optionR (prodR fracR (agreeR (inset_flowint_ur K)))) (Some (1%Qp, to_agree I')) (None)) /=.
        reflexivity. }
      assert (● I' ⋅ ◯ I_n' = (Auth (Some (1%Qp, to_agree(I'))) (I_n'))) as Hd.
      { rewrite /(● I') /= /(◯ I_n') /=. rewrite /(⋅) /=.
        rewrite /(cmra_op (authR (inset_flowint_ur K)) (Auth (Some (1%Qp, to_agree I')) ε) (Auth None I_n')) /=.
        rewrite /auth_op /=. rewrite HeIn. rewrite Hs. reflexivity. }
      iEval (rewrite Hd). iEval (rewrite <- H'). done.
  Qed.


  (** Lock module proofs *)

  Lemma lockNode_spec (n: Node):
    <<< ∀ (b: bool), (lockLoc n) ↦ #b >>>
        lockNode #n    @ ⊤
    <<< (lockLoc n) ↦ #true ∗ if b then False else True, RET #() >>>. (* rewrite if then else *)
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind(getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "#Hl". wp_let. wp_bind (CmpXchg _ _ _)%E.
    iMod "AU" as (b) "[Hb HAU]". iDestruct "Hl" as %Hl.
    iEval (rewrite Hl) in "Hb". destruct b.
    - wp_cmpxchg_fail. iDestruct "HAU" as "[HAU _]".
      iEval (rewrite Hl) in "HAU".
      iMod ("HAU" with "Hb") as "H".
      iModIntro. wp_pures. iApply "IH".
      iEval (rewrite <-Hl) in "H". done.
    - wp_cmpxchg_suc. iDestruct "HAU" as "[_ HAU]".
      iEval (rewrite Hl) in "HAU".
      iMod ("HAU" with "[Hb]") as "HΦ". iFrame; done.
      iModIntro. wp_pures. done.
  Qed.

  Lemma unlockNode_spec (n: Node) :
          <<< lockLoc n ↦ #true >>>
                unlockNode #n    @ ⊤
          <<< lockLoc n ↦ #false, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". wp_lam. wp_bind(getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "#Hl". wp_let.
    iMod "AU" as "[Hy [_ Hclose]]".
    iDestruct "Hl" as %Hl.
    iEval (rewrite Hl) in "Hy".
    wp_store. iEval (rewrite Hl) in "Hclose".
    iMod ("Hclose" with "Hy") as "HΦ".
    iModIntro. done.
  Qed.

  (** Proof of the lock-coupling template *)

  Lemma traverse_spec (γ γ_fp γ_k γ_c: gname) (root: Node) (k: K) (p n: Node) (Ns: gset Node) I_p C_p I_n C_n:
    ⌜k ∈ KS⌝ ∗ css γ γ_fp γ_k γ_c root -∗
    {{{ own γ_fp (◯ Ns) ∗ ⌜p ∈ Ns⌝ ∗ ⌜n ∈ Ns⌝ ∗ ⌜root ∈ Ns⌝ ∗ ⌜n ≠ root⌝
        ∗ node p root I_p C_p ∗ own γ (◯ I_p) ∗ ⌜domm I_p = {[p]}⌝ ∗  ⌜in_inset K k I_p p⌝ ∗ ⌜in_outset K k I_p n⌝
        ∗ own γ_k (◯ prod (keyset K I_p p, C_p)) ∗ node n root I_n C_n ∗ own γ (◯ I_n) ∗ ⌜domm I_n = {[n]}⌝
        ∗ own γ_k (◯ prod (keyset K I_n n, C_n))
    }}}
      traverse #p #n #k @ ⊤
    {{{ (p' n': Node) (Ns': gsetUR Node) (I_p' I_n': inset_flowint_ur K) (C_p' C_n': gset K),
        RET (#p', #n');
        own γ_fp (◯ Ns') ∗ ⌜p' ∈ Ns'⌝ ∗ ⌜n' ∈ Ns'⌝ ∗ own γ (◯ I_p') ∗ ⌜domm I_p' = {[p']}⌝ ∗ own γ (◯ I_n')
        ∗ ⌜domm I_n' = {[n']}⌝ ∗ node p' root I_p' C_p' ∗ node n' root I_n' C_n' ∗ ⌜n' ≠ root⌝
        ∗ own γ_k (◯ prod (keyset K I_p' p', C_p'))
        ∗ own γ_k (◯ prod (keyset K I_n' n', C_n'))
        ∗ ⌜in_inset K k I_p' p'⌝ ∗ ⌜in_outset K k I_p' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝
    }}}.
  Proof.
    iIntros "(% & #HInv)". iIntros (Φ) "!# H HCont". iLöb as "IH" forall (Ns p n I_p I_n C_p C_n).
    iDestruct "H" as "(#Hfp & % & % & % & % & Hnodep & HIp & % & % & % & Hksp & Hnoden & HIn & % & Hksn)".
    wp_lam. wp_pures. wp_bind (findNext _ _)%E.
    iPoseProof ((own_op γ (◯ I_p) (◯ I_n)) with "[HIp HIn]") as "H"; first by eauto with iFrame.
    iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H8.
    assert (✓ (I_p ⋅ I_n)). { apply (auth_frag_valid (◯ (I_p ⋅ I_n))). done. }
    assert (in_inset K k I_n n).
    { unfold in_inset. fold (inset K I_n n).
      apply (flowint_inset_step I_p I_n k n); try done. set_solver. }
    iDestruct "H" as "(HIp & HIn)".
    wp_apply ((findNext_spec root n I_n C_n k) with "[Hnoden]"). iFrame "∗ % #".
    iIntros (b n') "(Hnoden & Hb)". destruct b.
    - iDestruct "Hb" as "%". wp_pures.
      wp_bind (lockNode _)%E.
      awp_apply (lockNode_spec n') without "HCont".
      iInv "HInv" as ">H". iDestruct "H" as (I0 C0) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iPoseProof (auth_own_incl with "[$HInt $HIn]") as (I2)"%".
      iPoseProof (own_valid with "HIn") as "%".
      iPoseProof (own_valid with "HInt") as "%".
      assert (✓ I_n) as HInv. { apply (auth_frag_valid (◯ I_n)). done. }
      assert (✓ I0) as HI0. { apply (auth_auth_valid (I0)). done. }
      assert (n' ∈ domm I2). { apply (flowint_step I0 I_n I2 k n' root); try done. }
      assert (n' ∈ domm I0).
      { rewrite H13. rewrite flowint_comp_fp. set_solver. rewrite <-H13. done. }
      iMod (own_update γ_fp (● (domm I0)) (● (domm I0) ⋅ ◯ (domm I0)) with "HFP") as "H".
      apply auth_update_core_id. apply gset_core_id. done.
      iDestruct "H" as "(HFP & #Hfp0)".
      rewrite (big_sepS_elem_of_acc _ (domm I0) n'); last by eauto.
      iDestruct "Hstar" as "[Hb Hstar]".
      iDestruct "Hb" as (b) "[Hlock Hb]".
      iAaccIntro with "Hlock". { iIntros "H". iModIntro. iFrame "∗ # %".
      iNext. iExists I0, C0. iFrame "∗ # %". iApply "Hstar".
      iExists b. iFrame "∗ # %". }
      iIntros "(Hlock & H)". destruct b. { iExFalso. done. } iClear "H".
      iDestruct "Hb" as (I_n' C_n') "(HIn' & % & Hnoden' & Hksn')".
      iPoseProof ((own_op γ (◯ I_n) (◯ I_n' )) with "[HIn HIn']") as "H"; first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H19.
      assert (✓ (I_n ⋅ I_n')). { apply (auth_frag_valid (◯ (I_n ⋅ I_n'))). done. }
      iEval (rewrite -auth_frag_op) in "H".
      iPoseProof (auth_own_incl with "[$HInt $H]") as (I3)"%".
      iAssert (node n' root I_n' C_n' ∗ ⌜nodeinv root n' I_n' C_n'⌝)%I with "[Hnoden']" as "(Hnoden' & %)".
      { iApply (node_implies_nodeinv _ _ _). iFrame "∗ # %". iPureIntro.
        apply cmra_valid_op_r in H20. done. }
      assert (n' ≠ root) as Hnotf'.
      { apply (successor_not_root I0 I_n I_n' I3 C_n' root n' k); try done. }
      iModIntro. iSplitL "HKS HInt HFP Hcont Hstar Hlock".
      { iNext. iExists I0, C0. iFrame "∗ # %". iApply "Hstar".
      iExists true. iFrame. } iDestruct "H" as "(HIn & HIn')". iIntros "Hc".
      wp_pures. wp_bind (unlockNode _)%E. awp_apply (unlockNode_spec p) without "Hc".
      iInv "HInv" as ">H". iDestruct "H" as (I1 C1) "(HKS & HInt & % & HFP & Hcont & Hstar)".
      iAssert (⌜p ∈ domm I1⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (domm I1)) with "[$]") as "%".
        iPureIntro. set_solver. }
      iAssert (⌜n ∈ domm I1⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (domm I1)) with "[$]") as "%".
        iPureIntro. set_solver. }
      iAssert (⌜n' ∈ domm I1⌝)%I with "[HFP]" as "%".
      { iPoseProof ((auth_set_incl γ_fp (domm I0) (domm I1)) with "[$]") as "%".
        iPureIntro. set_solver. }
      assert (root ∈ domm I1). { apply globalinv_root_fp. done. }
      rewrite (big_sepS_elem_of_acc _ (domm I1) p); last by eauto.
      iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
      destruct b; last first. { iDestruct "Hb" as (In1 Cn1) "(_ & _ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep' Hnodep]" as %Hf. { iApply (node_sep_star p In1 I_p _ _ root).
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros. iModIntro. iFrame "∗ # %". iNext. iExists I1, C1.
      iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
      iMod (own_update γ_fp (● (domm I1)) (● (domm I1) ⋅ ◯ (domm I1)) with "HFP") as "H".
      apply auth_update_core_id. apply gset_core_id. done.
      iDestruct "H" as "(HFP & #Hfp1)".
      iIntros "Hlock". iModIntro. iSplitL "HKS HInt HFP Hcont Hstar Hlock Hnodep HIp Hksp".
      iNext. iExists I1, C1. iFrame "∗ # %". iApply "Hstar". iExists false. iFrame.
      iExists I_p, C_p. iFrame "∗ # %". iIntros "Hc". wp_pures. iSpecialize ("IH" $! (domm I1) n n' I_n I_n' C_n C_n').
      iApply ("IH" with "[-Hc]"). iFrame "∗ # %". iNext. done.
    - wp_pures. iDestruct "Hb" as "(% & %)". iSpecialize ("HCont" $! p n Ns I_p I_n C_p C_n).
      iApply "HCont". iFrame "∗ # %".
  Qed.

  Lemma ghost_update_keyset γ_k dop k Cn Cn' res K1 C:
    ⌜Ψ dop k Cn Cn' res⌝ ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
    ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝
    ==∗ ∃ C', ⌜Ψ dop k C C' res⌝ ∗ own γ_k (● prod (KS, C')) ∗ own γ_k (◯ prod (K1, Cn')).
  Proof.
  Admitted.

  Theorem searchStrOp_spec (γ γ_fp γ_k γ_c: gname) root (k: K) (dop: dOp):
    ⌜k ∈ KS⌝ ∗ css γ γ_fp γ_k γ_c root -∗
    <<< ∀ (C: gset K), css_cont γ_c C >>>
      CSSOp dop root #k @ ⊤ ∖ ↑N
    <<< ∃ C' (res: bool), css_cont γ_c C' ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
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
    iIntros "(Hlock & H)". destruct b. { iExFalso. done. } iClear "H".
    iDestruct "Hb" as (If Cf) "(HIf & % & Hnodef & HCf)".
    iPoseProof (auth_own_incl with "[$HInt $HIf]") as (Io)"%".
    iModIntro. iSplitR "AU HIf Hnodef HCf". iNext. iExists I0, C0. iFrame "∗ # %".
    iApply "Hstar". iExists true. iFrame "∗ # %".
    wp_pures. wp_bind(findNext _ _)%E.
    assert (in_inset K k If root). { unfold globalinv in H0. destruct H0 as [? [? [? ?]]].
    specialize (H6 root). destruct H6 as [H6 _]. apply (inset_monotone I0 If Io k root); try done; set_solver. }
    wp_apply ((findNext_spec root root If Cf k) with "[Hnodef]").
    { iFrame "∗ # %". } iIntros (b n) "(Hnodef & Hb)".
    destruct b; last first. wp_pures. iDestruct "Hb" as "(% & %)".
    exfalso. apply H5. done. iDestruct "Hb" as "%". wp_pures.
    wp_bind (lockNode _)%E. awp_apply (lockNode_spec n). iInv "HInv" as ">H".
    iDestruct "H" as (I2 C2) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iPoseProof (own_valid with "HInt") as "%". rename H7 into Hcheck.
    assert (✓ I2) as HI2. { apply (auth_auth_valid (I2)). done. }
    iPoseProof (auth_own_incl with "[$HInt $HIf]") as (Io')"%". assert (n ∈ domm I2).
    { assert (n ∈ domm Io').
      { apply (flowint_step I2 If Io' k n root); try done. }
      rewrite H7. rewrite flowint_comp_fp. set_solver. rewrite <-H7. done. }
    rewrite (big_sepS_elem_of_acc _ (domm I2) n); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitR "AU HIf HCf Hnodef".
    iNext. iExists I2, C2. iFrame "∗ # %". iApply "Hstar".
    iExists b. iFrame "∗ # %". iFrame "∗ # %". }
    iIntros "(Hlock & H)". destruct b. { iExFalso. done. } iClear "H".
    assert (root ∈ domm I2). { apply globalinv_root_fp. done. }
    iMod (own_update γ_fp (● (domm I2)) (● (domm I2) ⋅ ◯ (domm I2)) with "HFP") as "H".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "H" as "(HFP & #Hfp2)".
    iDestruct "Hb" as (In Cn) "(HIn & % & Hnoden & HCn)".
    iPoseProof ((own_op γ (◯ If) (◯ In)) with "[HIf HIn]") as "H"; first by eauto with iFrame.
    iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H11.
    assert (✓ (If ⋅ In)). { apply (auth_frag_valid (◯ (If ⋅ In))). done. }
    iEval (rewrite -auth_frag_op) in "H".
    iPoseProof (auth_own_incl with "[$HInt $H]") as (Iu)"%".
    iAssert (node n root In Cn ∗ ⌜nodeinv root n In Cn⌝)%I with "[Hnoden]" as "(Hnoden & %)".
    { iApply (node_implies_nodeinv n In Cn root). iFrame "∗ # %". iPureIntro.
      apply cmra_valid_op_r in H12. done. }  iDestruct "H" as "(HIf & HIn)".
    assert (n ≠ root).
    { apply (successor_not_root I2 If In Iu Cn root n k); try done. }
    iModIntro. iSplitR "AU HIf HCf Hnodef HIn Hnoden HCn". { iNext. iExists I2, C2.
    iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
    wp_pures. wp_bind (traverse _ _ _)%E.
    wp_apply ((traverse_spec γ γ_fp γ_k γ_c root k root n (domm I2) If Cf In Cn)
                 with "[] [HIf HCf Hnodef HIn HCn Hnoden]").
    iFrame "∗ # %". iFrame "∗ # %".
    iIntros (p' n' Ns Ip' In' Cp' Cn') "(#HNs & % & % & HIp' & % & HIn' & % & Hnodep' & Hnoden'
                        & % & Hksp' & Hksn' & % & % & %)".
    wp_pures. wp_apply (alloc_spec); first done.
    iIntros (m lm) "(Hrepm & % & Hlm)". wp_pures. wp_bind (decisiveOp _ _ _ _)%E.
    iApply fupd_wp. iInv "HInv" as ">H".
    iDestruct "H" as (I3 C3) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    destruct (decide (m ∈ domm I3)). { rewrite (big_sepS_elem_of_acc _ (domm I3) m); last by eauto.
    iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
    iEval (rewrite H24) in "Hlockm". iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%".
    exfalso. done. }
    assert (root ∈ domm I3). { apply globalinv_root_fp. done. }
    assert (m ≠ root). { set_solver. }
    iModIntro. iSplitL "HKS HInt HFP Hcont Hstar". iNext.
    iExists I3, C3. iFrame "∗ # %". iModIntro.
    wp_apply ((decisiveOp_insert_spec dop root p' n' m k Ip' In' Cp' Cn')
          with "[Hnodep' Hnoden' Hrepm]"). { iFrame "∗ % #". }
    iIntros (Cp'' Cn'' Cm'' Ip'' In'' Im'' res) "(Hnodep' & Hnoden' & Hnodem' & % & % & % & H)".
    iDestruct "H" as "(% & % & % & % & % & % & % & % & % & % & % & %)".
    iApply fupd_wp. iInv "HInv" as ">H".
    iDestruct "H" as (I4 C4) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iMod "AU" as (C') "[Hc [_ Hclose]]". iEval (rewrite /css_cont) in "Hc".
    iDestruct (auth_agree with "Hcont Hc") as %<-.

    (* ------ keyset update -------*)

    iPoseProof ((own_op γ_k (◯ prod (keyset K Ip' p', Cp')) (◯ prod (keyset K In' n', Cn'))
                      with "[Hksp' Hksn']")) as "H"; first by eauto with iFrame.
    assert (◯ prod (keyset K Ip' p', Cp') ⋅ ◯ prod (keyset K In' n', Cn') =
               ◯ (prod (keyset K Ip' p', Cp') ⋅ prod (keyset K In' n', Cn'))).
    { apply (auth_frag_op (prod (keyset K Ip' p', Cp')) (prod (keyset K In' n', Cn'))). }
    iEval (rewrite H44) in "H". iPoseProof (own_valid with "H") as "%".
    assert (✓ (prod (keyset K Ip' p', Cp') ⋅ prod (keyset K In' n', Cn'))).
    { apply (auth_frag_valid (◯ (prod (keyset K Ip' p', Cp') ⋅ prod (keyset K In' n', Cn')))). done. }
    unfold op,prodOp in H46. repeat case_decide;
        [ simpl | try exfalso; eauto | try exfalso; eauto | try exfalso; eauto | try exfalso; eauto].
    assert (prod (keyset K Ip'' p', Cp'') ⋅ prod (keyset K In'' n', Cn'') ⋅ prod (keyset K Im'' m, Cm'')
                 = prod (keyset K Ip'' p' ∪ keyset K In'' n' ∪ keyset K Im'' m, Cp'' ∪ Cn'' ∪ Cm'')).
    { unfold op, prodOp. repeat case_decide; try done. exfalso. apply H58. set_solver by eauto.
      exfalso. apply H57. set_solver by eauto. exfalso. apply H55. set_solver by eauto. }
    assert (◯ (prod (keyset K Ip'' p', Cp'') ⋅ prod (keyset K In'' n', Cn'') ⋅ prod (keyset K Im'' m, Cm''))
                 = ◯ (prod (keyset K Ip'' p' ∪ keyset K In'' n' ∪ keyset K Im'' m, Cp'' ∪ Cn'' ∪ Cm''))).
    { rewrite H51. reflexivity. }
    assert ((prod (keyset K Ip' p', Cp') ⋅ prod (keyset K In' n', Cn'))
                  = prod (keyset K Ip' p' ∪ keyset K In' n', Cp' ∪ Cn')).
    { unfold op, prodOp. repeat case_decide; try done. }
    iPoseProof ((own_op γ (◯ Ip') (◯ In')) with "[HIp' HIn']") as "H'"; first by eauto with iFrame.
    iPoseProof (own_valid with "H'") as "%". rewrite -auth_frag_op in H54.
    assert (✓ (Ip' ⋅ In')). { apply (auth_frag_valid (◯ (Ip' ⋅ In'))). done. }
    assert (in_inset K k In' n'). {
      apply (flowint_inset_step Ip' In' k n'); try done. set_solver. }
    assert (k ∈ keyset K In' n'). { apply keyset_def; try done. }
    iMod ((ghost_update_keyset γ_k dop k (Cp' ∪ Cn') (Cp'' ∪ Cn'' ∪ Cm'') res
                 (keyset K Ip' p' ∪ keyset K In' n') C4) with "[HKS H]") as "Hgks".
    iEval (rewrite H53) in "H". iFrame "∗ # %". iPureIntro.
    split. rewrite <-H42. set_solver by eauto. set_solver by eauto.
    iDestruct "Hgks" as (C4') "(% & HKS & H)". iEval (rewrite <-H42) in "H".
    iAssert (own γ_k (◯ (prod (keyset K Ip'' p', Cp'') ⋅ prod (keyset K In'' n', Cn'') ⋅ prod (keyset K Im'' m, Cm''))))
          with "[H]" as "Hv". { iEval (rewrite H52). done. }
    iDestruct "Hv" as "((Hksp' & Hksn') & Hksm')".
    iMod (auth_update γ_c (C4') with "Hcont Hc") as "[Hcont Hc]".

    (* ------ interface update -------*)

    iPoseProof (own_valid with "HInt") as "%".
    iMod (own_updateP (flowint_update_P K_multiset I4 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')) γ
                          (● I4 ⋅ ◯ (Ip' ⋅ In')) with "[HInt H']") as (Io'') "H0".
    {
      admit.                    (* TODO need to debug *)
      (* apply (flowint_update K_multiset I4 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')). done. *)
    }
    { try repeat rewrite own_op; iFrame. rewrite auth_frag_op. rewrite own_op. iFrame.  }
    iPoseProof ((flowint_update_result γ I4 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im''))
                      with "H0") as (I') "(% & % & HIIpnm)".
    iEval (rewrite own_op) in "HIIpnm". iDestruct "HIIpnm" as "(HI' & HIpnm'')".
    iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
    iPoseProof (own_valid with "HIpnm''") as "%".
    assert (✓ (Ip'' ⋅ In'' ⋅ Im'')) as HIpnmcheck.
    { apply (auth_frag_valid (◯ (Ip'' ⋅ In'' ⋅ Im''))). done. }
    iDestruct "HIpnm''" as "(HIpn'' & HIm'')".
    iPoseProof (own_valid with "HIpn''") as "%".
    assert (✓ (Ip'' ⋅ In'')) as HIpncheck.
    { apply (auth_frag_valid (◯ (Ip'' ⋅ In''))). done. }
    iDestruct "HIpn''" as "(HIp'' & HIn'')".
    destruct (decide (m ∈ domm I4)). { rewrite (big_sepS_elem_of_acc _ (domm I4) m); last by eauto.
    iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
    iEval (rewrite H24) in "Hlockm". iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%".
    exfalso. done. }
    iMod (own_update γ_fp (● domm I4) (● (domm I4 ∪ {[m]}) ⋅ ◯ (domm I4 ∪ {[m]})) with "[HFP]") as "H".
    { apply (auth_update_alloc (domm I4) (domm I4 ∪ {[m]}) (domm I4 ∪ {[m]})).
      apply gset_local_update. set_solver. }
    done. iDestruct "H" as "(HFP & #Hfp4)".
    assert (domm I' = domm I4 ∪ {[m]}).
    {
      destruct H61 as [I_o H61]. destruct H61.
      assert (domm I' = {[p']} ∪ {[n']} ∪ {[m]} ∪ domm I_o).
      {
        subst I'. repeat rewrite flowint_comp_fp; try congruence; try done.
        by apply (auth_auth_valid).
      }
      rewrite H66.
      assert (domm I4 = {[p']} ∪ {[n']} ∪ domm I_o).
      {
        subst I4. repeat rewrite flowint_comp_fp; try congruence; try done.
        by apply (auth_auth_valid).
      }
      rewrite H67.
      clear. set_solver.
    }
    
    assert (globalinv K root I'). {
      apply (contextualLeq_impl_globalinv I4 I').
      all: try trivial.
      intros.
      assert (n2 = m). { clear - H65 H66. set_solver. }
      rewrite H67. admit.
    }
    iEval (rewrite <-H65) in "HFP". assert (domm I'∖ {[m]} = domm I4). { set_solver. }

    (* ------ updates over -------*)

    iMod ("Hclose" with "[Hc]") as "HΦ". iFrame "∗ % #".
    iModIntro. iSplitL "Hstar Hlm Hnodem' HKS Hcont HI' HIm'' HFP Hksm'". iNext. iExists I', C4'.
    iFrame "∗ # %". rewrite (big_sepS_delete _ (domm I') m); last set_solver. iEval (rewrite H67).
    iFrame. iExists false. iEval (rewrite H24). iFrame. iExists Im'', Cm''. eauto with iFrame.
    iModIntro. wp_pures. wp_bind (unlockNode _)%E.

    (* ------ linearization over -------*)

    awp_apply (unlockNode_spec p') without "HΦ". iInv "HInv" as ">H".
    iDestruct "H" as (I6 C6) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iAssert (⌜p' ∈ domm I6⌝)%I with "[HFP]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns (domm I6)) with "[$]") as "%".
      iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (domm I6) p'); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
    destruct b; last first. { iDestruct "Hb" as (In0 Cn0) "(_ & _ & Hrep' & _)".
    iAssert (⌜False⌝)%I with "[Hnodep' Hrep']" as %Hf. { iApply (node_sep_star p' Ip'' In0 _ _ _).
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
    iInv "HInv" as ">H". iDestruct "H" as (I5 C5) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iAssert (⌜n' ∈ domm I5⌝)%I with "[HFP]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns (domm I5)) with "[$]") as "%".
      iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (domm I5) n'); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
    destruct b; last first. { iDestruct "Hb" as (In0 Cn0) "(_ & _ & Hrep' & _)".
    iAssert (⌜False⌝)%I with "[Hnoden' Hrep']" as %Hf. { iApply (node_sep_star n' In'' In0 _ _ _).
    iFrame. } exfalso. done. }
    iAaccIntro with "Hlock".
    { iIntros. iModIntro. iFrame "∗ # %". iNext. iExists I5, C5.
      iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
    iIntros. iModIntro.
    iSplitL. iNext. iExists I5, C5.
    iFrame "∗ # %". iApply "Hstar". iExists false. iFrame. iExists In'', Cn''. iFrame "∗ %".

    iIntros "HΦ". wp_pures. done.
  Admitted.
