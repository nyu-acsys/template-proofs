(** Verification of Give-up template algorithm *)

From iris.algebra Require Import excl auth gmap agree gset frac.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "All".
Require Export keyset_ra linkset_flows.

(** We use integers as keys. *)
Definition K := Z.

(** Definitions of cameras used in the template verification *)
Section Link_Cameras.

  (* RA for authoritative flow interfaces over pairs of multisets of keys *)
  Class flowintG Σ :=
    FlowintG { flowint_inG :> inG Σ (authR (linkset_flowint_ur K)) }.
  Definition flowintΣ : gFunctors := #[GFunctor (authR (linkset_flowint_ur K))].

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

  (* RA for authoritative inreach sets *)
  Class inreachG Σ := InreachG { inreach_inG :> inG Σ (authR (gsetUR K)) }.
  Definition inreachΣ : gFunctors := #[GFunctor (authR (gsetUR K))].

  Instance subG_inreachΣ {Σ} : subG inreachΣ Σ → inreachG Σ.
  Proof. solve_inG. Qed.

  (* RA for fractional interfaces *)
  Class fracintG Σ :=
    FracinthG { fracint_inG :> inG Σ (authR (linkset_flowint_ur K)) }.
  Definition fracintΣ : gFunctors := #[GFunctor (authR (linkset_flowint_ur K))].

  Instance subG_fracintΣ {Σ} : subG fracintΣ Σ → fracintG Σ.
  Proof. solve_inG. Qed.

End Link_Cameras.

(** Verification of the template *)
Section Link_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ, !inreachG Σ,
    !fracintG Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the link template. *)

  Inductive dOp := memberOp | insertOp | deleteOp.

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b-link.spl and
   * hashtbl-link.spl for the concrete implementations. *)

  Parameter findNext : val.
  Parameter decisiveOp : (dOp → val).
  Parameter lockLoc : Node → loc.
  Parameter getLockLoc : val.

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
    rec: "tr" "n" "k" :=
      lockNode "n";;
      match: (findNext "n" "k") with
        NONE => "n"
      | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
      end.

  Definition CSSOp (Ψ: dOp) (root: Node) : val :=
    rec: "dictOp" "k" :=
      let: "n" := traverse #root "k" in
      match: ((decisiveOp Ψ) "n" "k") with
        NONE => unlockNode "n";; "dictOp" "k"
      | SOME "res" => unlockNode "n";; "res"
      end.

  (** Assumptions on the implementation made by the template proofs. *)

  (* The node predicate is specific to each template implementation. See GRASShopper files
     b-link.spl and hashtbl-link.spl for the concrete definitions. *)
  Parameter node : Node → linkset_flowint_ur K → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ n I C, Timeless (node n I C).
  Instance node_timeless n I C: Timeless (node n I C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-link.spl and b-link.spl *)
  Hypothesis node_sep_star: ∀ n I_n I_n' C C',
    node n I_n C ∗ node n I_n' C' -∗ False.

  (* The node-level invariant (γ in the paper).
   * See also link.spl for the matching GRASShopper definition *)
  Definition nodeinv I_n n: Prop :=
    (∀ k, k ∈ linkset K I_n n ∧ ¬ in_outsets K k I_n → in_inset K k I_n n).

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-link.spl and b-link.spl *)
  Hypothesis node_implies_nodeinv : ∀ n I_n C,
    (⌜✓I_n⌝)%I ∗ node n I_n C -∗ node n I_n C ∗ (⌜nodeinv I_n n⌝)%I.

  (** Coarse-grained specification *)

  Definition Ψ dop k (C: gset K) (C': gset K) (res: bool) : iProp :=
    match dop with
    | memberOp => (⌜C' = C ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    | insertOp => (⌜C' = union C {[k]} ∧ (if res then k ∉ C else k ∈ C)⌝)%I
    | deleteOp => (⌜C' = difference C {[k]} ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    end.

  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.

  (** Helper functions specs *)
  (* These are proved for each implementation in GRASShopper *)

  Parameter getLockLoc_spec : ∀ (n: Node),
    ({{{ True }}}
      getLockLoc #n
    {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  (* The following functions are proved for each implementation in GRASShopper
   * (see b-link.spl and hashtbl-link.spl *)

  (* Todo: Can we simplify the match to ⌜b → in_inset k I_n n⌝? *)
  Parameter findNext_spec : ∀ (n: Node) (I_n : linkset_flowint_ur K) (C: gset K) (k: K),
    ({{{ node n I_n C ∗ ⌜k ∈ inset K I_n n ∨ k ∈ linkset K I_n n⌝ }}}
      findNext #n #k
    {{{ (b: bool) (n': Node),
        RET (match b with true => (SOMEV #n') | false => NONEV end);
        node n I_n C ∗ (match b with true => ⌜in_outset K k I_n n'⌝ |
                                    false => ⌜¬in_outsets K k I_n⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K)
      (I_n: linkset_flowint_ur K) (C: gset K),
    ({{{ node n I_n C ∗ ⌜in_inset K k I_n n⌝ ∗ ⌜¬in_outsets K k I_n⌝ }}}
      decisiveOp dop #n #k
    {{{ (b: bool) (C': gset K) (res: bool),
        RET (match b with false => NONEV | true => (SOMEV #res) end);
        match b with false => node n I_n C |
                      true => node n I_n C' ∗ Ψ dop k C C' res
                              ∗ ⌜ C' ⊆ keyset K I_n n⌝
        end }}})%I.

  (** The concurrent search structure invariant *)

  Definition CSS γ γ_fp γ_k γ_inr γ_fi root I C : iProp :=
    (own γ (● I) ∗ own γ_k (● prod (KS, C)) ∗ own γ_fp (● domm I)
    ∗ ⌜globalinv K root I⌝
    ∗ ([∗ set] n ∈ (domm I), (∃ (b: bool) (I_n: linkset_flowint_ur K),
      (lockLoc n) ↦ #b
      ∗ (if b then True
        else (∃ C_n, node n I_n C_n ∗ own (γ_fi n) ((●{1/2} I_n))
                     ∗ own γ_k (◯ prod (keyset K I_n n, C_n))))
      ∗ own γ (◯ I_n) ∗ ⌜domm I_n = {[n]}⌝ ∗ own (γ_fi n) ((●{1/2} I_n))
      ∗ own (γ_inr n) (● (inset K I_n n ∪ linkset K I_n n))))
    )%I.

  Definition is_CSS γ γ_fp γ_k γ_inr γ_fi root C :=
    (∃ I, (CSS γ γ_fp γ_k γ_inr γ_fi root I C))%I.

  (** Assorted useful lemmas *)

  Lemma globalinv_root_fp: ∀ I root, globalinv K root I → root ∈ domm I.
  Proof.
    intros I root Hglob. unfold globalinv in Hglob.
    destruct Hglob as [H1 [H2 H3]]. done.
  Qed.

  Lemma globalinv_root_inr : ∀ I Ir root k,
    globalinv K root I ∧ Ir ≼ I ∧ domm Ir = {[root]}
    → k ∈ inset K Ir root ∨ k ∈ linkset K Ir root.
  Proof.
    intros I Ir root k ((Hv & _ & _ & Hl & _) & [I2 Hincl] & Hdom).
    right. specialize (Hl k). destruct Hl.
    apply (linkset_monotone I Ir I2 k root); try done.
    set_solver.
  Qed.

  Lemma auth_set_incl {A: Type} `{Countable A} `{inG Σ (authR (gsetUR A))}
      (γ_fp: gname) (Ns Ns': gset A) :
    own γ_fp (◯ Ns) ∗ own γ_fp (● Ns') -∗ ⌜Ns ⊆ Ns'⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro.
    rewrite auth_valid_discrete. simpl. rewrite ucmra_unit_right_id_L.
    intros (_ & [a (Hagree & Hincl & _)]).
    apply gset_included in Hincl.
    apply to_agree_inj in Hagree. set_solver.
  Qed.

  Lemma auth_own_incl γ (x y: linkset_flowint_ur K) :
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


  (** Lock module proofs *)

  Lemma lockNode_spec (n: Node): (* TODO rewrite if then else *)
    <<< ∀ (b: bool), (lockLoc n) ↦ #b >>>
      lockNode #n    @ ⊤
    <<< (lockLoc n) ↦ #true ∗ if b then False else True, RET #() >>>.
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


  (** Proofs of traverse and CSSOp *)

  Lemma traverse_spec (γ γ_fp γ_k: gname) (γ_inr γ_fi: Node → gname)
      (root: Node) (k: K) (n: Node) (Ns: gset Node) (I_n:linkset_flowint_ur K):
    ⌜n ∈ Ns⌝ ∗ own γ_fp (◯ Ns)
    ∗ own (γ_inr n) (◯ (inset K I_n n ∪ linkset K I_n n))
    ∗ ⌜k ∈ inset K I_n n ∨ k ∈ linkset K I_n n⌝ -∗
    <<< ∀ C, is_CSS γ γ_fp γ_k γ_inr γ_fi root C >>>
      traverse #n #k @ ⊤
    <<< ∃ (n': Node) (Ns': gsetUR Node) (I_n': linkset_flowint_ur K) (Cn': gset K),
        is_CSS γ γ_fp γ_k γ_inr γ_fi root C ∗ ⌜n' ∈ Ns'⌝
        ∗ own γ_fp (◯ Ns') ∗ node n' I_n' Cn' ∗ own (γ_fi n') ((●{1/2} I_n'))
        ∗ own γ_k (◯ prod (keyset K I_n' n', Cn')) ∗ ⌜domm I_n' = {[n']}⌝
        ∗ ⌜in_inset K k I_n' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns I_n). iIntros "(#Hinn & #Hfp & #Hinrfp & #Hkinr)".
    iDestruct "Hinn" as %Hinn.
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n). iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "Hst". iDestruct "Hst" as (I) "(HI & HKS & HNDS & Hglob & Hstar)".
    iAssert (⌜n ∈ domm I⌝)%I with "[HNDS]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns (domm I)) with "[$]") as "%".
      iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b In) "(Hlock & Hb & HIn & #HNds & Hfis & Hks)".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitL. iFrame "∗ % #".
    iExists I. iFrame "∗ % #". iApply "Hstar". iExists b, In.
    iFrame "# % ∗". eauto with iFrame. } iIntros "(Hloc & ?)".
    destruct b. { iExFalso. done. } iModIntro.
    iPoseProof ((auth_set_incl (γ_inr n)) with "[$Hks $Hinrfp]") as "%".
    iDestruct "Hkinr" as "%".
    assert (k ∈ inset K In n ∨ k ∈ linkset K In n) as Hkinr; first by set_solver.
    iPoseProof (own_valid with "HIn") as "%". rename H2 into HInV.
    assert (✓ In) as HInv. { apply (auth_frag_valid (◯ In)). done. }
    iSplitR "Hb". iFrame "∗ % #". iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In.
    iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (Cn) "(Hrep & Hfil & Hks)". iDestruct "HNds" as %HNds.
    wp_bind (findNext _ _)%E. wp_apply ((findNext_spec n In Cn k) with "[Hrep]").
    iFrame; iPureIntro; done. iIntros (b n') "(Hrep & Hb)". destruct b.
    - wp_pures. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
      iDestruct "Hst" as (I1) "(HI & HKS & HNDS & Hglob & Hstar)".
      iAssert (⌜n ∈ domm I1⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (domm I1)) with "[$]") as "%".
        iPureIntro. set_solver. }
      rewrite (big_sepS_delete _ (domm I1) n); last by eauto. iDestruct "Hstar" as "(Hcln & Hstar)".
      iDestruct "Hcln" as (b In1) "(Hlock & Hbb & HIn & #HNds1 & Hfis & Hks1)".
      destruct b; first last. { iDestruct "Hbb" as (Cn') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In1).
      iFrame. } exfalso. done. }
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H3. apply leibniz_equiv in H3. replace In1.
      iDestruct "Hb" as %Hb. iDestruct "HNds1" as %HNds1. iDestruct "Hglob" as %Hglob.
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof (own_valid with "HI") as "%". iAssert (⌜n' ∈ domm I1⌝)%I as "%".
      { iPureIntro. assert (n' ∈ domm I2).
        { apply (flowint_step I1 In I2 k n' root); try done. }
        assert (domm I1 = domm In ∪ domm I2).
        { rewrite H4. apply flowint_comp_fp.
          rewrite H4 in H5 * => H5.
          rewrite <-H4.
          apply auth_auth_valid.
          rewrite <-H4 in H5. done.
        }
        rewrite H7.
        set_solver. }
      (* apply Hglob. } *)
      assert (n ≠ n') as Hneq.
      { assert (n' ∉ domm In).
        { apply (outset_distinct In n').
          split. done.
          exists k. done. }
        rewrite HNds1 in H7. set_solver. }
      rewrite (big_sepS_delete _ (domm I1 ∖ {[n]}) n'); last first.
      set_solver. iDestruct "Hstar" as "(Hcln' & Hstar)".
      iDestruct "Hcln'" as (b In') "(Hlock' & Hbb' & HIn' & #HNds' & Hfis' & Hks1')".
      iPoseProof ((own_op γ (◯ In) (◯ In' )) with "[HIn HIn']") as "H"; first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H7.
      assert (✓ (In ⋅ In')). { apply (auth_frag_valid (◯ (In ⋅ In'))). done. }
      iDestruct "HNds'" as %HNds'.
      assert (k ∈ inset K In' n' ∨ k ∈ linkset K In' n').
      {
        apply or_comm.
        apply (flowint_linkset_step In In' k n'). done. set_solver.  
        unfold in_outset in Hb. done.
      }
      assert (root ∈ domm I1). { apply globalinv_root_fp. done. } iDestruct "H" as "(HIn & HIn')".
      iMod (own_update (γ_inr n') _
                       (● (inset K In' n' ∪ linkset K In' n')
                          ⋅ ◯ (inset K In' n' ∪ linkset K In' n'))
              with "Hks1'") as "HNs".
      apply auth_update_core_id. 
      apply gset_core_id. done. iDestruct "HNs" as "(Hks1' & #Hinr1')".
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hks Hrep". iFrame "∗ # %".
      iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (domm I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists true, In. iFrame "# % ∗".
      rewrite (big_sepS_delete _ (domm I1 ∖ {[n]}) n'); last first. set_solver. iFrame. iExists b, In'.
      iFrame "# % ∗".  iIntros "AU". iModIntro. iFrame "# % ∗". } iIntros "Hlock".
      iMod (own_update γ_fp (● domm I1) (● domm I1 ⋅ ◯ domm I1) with "HNDS") as "HNs".
      apply auth_update_core_id. apply gset_core_id. done. iDestruct "HNs" as "(HAfp & #Hfp1)".
      iModIntro. iSplitL. iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (domm I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists false, In. iFrame "# % ∗". iExists Cn. iFrame.
      rewrite (big_sepS_delete _ (domm I1 ∖ {[n]}) n'); last first. set_solver. iFrame. iExists b, In'.
      iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures. iSpecialize ("IH" $! n' (domm I1) In').
      iApply "IH". iFrame "∗ # %". done.
    - iApply fupd_wp. iMod "AU" as (C) "[Hst [_ Hclose]]". iSpecialize ("Hclose" $! n Ns In Cn).
      iMod ("Hclose" with "[Hst Hfil Hks Hrep Hb]") as "HΦ". iDestruct "Hb" as %Hnotout.
      iAssert (node n In Cn ∗ ⌜nodeinv In n⌝)%I with "[Hrep]" as "(Hrep & Hninv)".
      { iApply (node_implies_nodeinv _ _ _). iFrame "∗ # %". }
      iDestruct "Hninv" as %Hninv.
      iFrame "∗ # %". iPureIntro. unfold nodeinv in Hninv.
      destruct Hkinr.
      * unfold in_inset. done.
      * apply Hninv. split; try done.
      * iModIntro. wp_pures. done.
  Qed.


  (* Ghost state manipulation to make final proof cleaner *)

  (* Todo: I think k ∈ KS follows from k ∈ K1, so we can drop it here,
    and in CSSOp_spec. *)
  Lemma ghost_update_keyset γ_k dop k Cn Cn' res K1 C:
    Ψ dop k Cn Cn' res ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
    ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝
    ==∗ ∃ C', Ψ dop k C C' res ∗ own γ_k (● prod (KS, C'))
      ∗ own γ_k (◯ prod (K1, Cn')).
  Proof.
    iIntros "(#HΨ & Ha & Hf & % & % & HKS)". iPoseProof (auth_own_incl_ks γ_k (prod (KS, C)) (prod (K1, Cn))
                with "[$Ha $Hf]") as "%". iDestruct "HKS" as %HKS.
    iPoseProof ((own_valid γ_k (● prod (KS, C))) with "Ha") as "%".
    iPoseProof ((own_valid γ_k (◯ prod (K1, Cn))) with "Hf") as "%".
    assert ((K1 = KS ∧ Cn = C) ∨
            (∃ a0 b0, KS = K1 ∪ a0 ∧ C = Cn ∪ b0 ∧ K1 ## a0 ∧ Cn ## b0 ∧ Cn ⊆ K1 ∧ C ⊆ KS ∧ b0 ⊆ a0)) as Hs.
    { apply (auth_ks_included K1 KS Cn C); try done. apply auth_auth_valid. done. }
    destruct Hs.
    - iEval (unfold Ψ) in "HΨ". destruct H4. destruct dop.
      + iDestruct "HΨ" as "%". destruct H6.
        iModIntro. iExists C. iEval (rewrite <-H6) in "Hf". iFrame. unfold Ψ.
        iPureIntro. split; try done. rewrite <-H5. done.
      + iDestruct "HΨ" as "%". destruct H6. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∪ {[k]}) ⋅ ◯ prod (K1, Cn ∪ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_insert.
            split; try done. apply auth_auth_valid. done.   }
          iModIntro. iExists (C ∪ {[k]}). iEval (rewrite H6). iFrame.
          unfold Ψ. iPureIntro. split; try done. rewrite <-H5. done.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H8) in "Hf".
          iFrame. unfold Ψ. iPureIntro. rewrite <- H5. split; try done. rewrite H8 in H6. done.
      + iDestruct "HΨ" as "%". destruct H6. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∖ {[k]}) ⋅ ◯ prod (K1, Cn ∖ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_delete. split; try done. apply auth_auth_valid. done. }
          iModIntro. iExists (C ∖ {[k]}). iEval (rewrite H6). iFrame.
          unfold Ψ. iPureIntro. split; try done. rewrite <-H5. done.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H8) in "Hf".
          iFrame. unfold Ψ. iPureIntro. rewrite <- H5. split; try done. rewrite H8 in H6. done.
    - destruct H4 as [Ko [Co [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]. destruct dop.
      + iDestruct "HΨ" as "%". destruct H11.
        iModIntro. iExists C. iEval (rewrite <-H11) in "Hf". iFrame. unfold Ψ.
        iPureIntro. split; try done. destruct res; set_solver.
      + iDestruct "HΨ" as "%". destruct H11. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∪ {[k]}) ⋅ ◯ prod (K1, Cn ∪ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_insert. split; try done. }
          iModIntro. iExists (C ∪ {[k]}). iEval (rewrite H11). iFrame.
          unfold Ψ. iPureIntro. split; try done. set_solver.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H13) in "Hf".
          iFrame. unfold Ψ. iPureIntro. set_solver.
      + iDestruct "HΨ" as "%". destruct H11. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∖ {[k]}) ⋅ ◯ prod (K1, Cn ∖ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_delete. split; try done. }
          iModIntro. iExists (C ∖ {[k]}). iEval (rewrite H11). iFrame.
          unfold Ψ. iPureIntro. split; try done. set_solver.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H13) in "Hf".
          iFrame. unfold Ψ. iPureIntro. set_solver.
  Qed.

  (** Verification of abstract specification of the search structure operation. *)

  Theorem CSSOp_spec (γ γ_fp γ_k: gname) γ_inr γ_fi root (k: K) (dop: dOp):
    ⌜k ∈ KS⌝ -∗ <<< ∀ C, is_CSS γ γ_fp γ_k γ_inr γ_fi root C >>>
      CSSOp dop root #k @ ⊤
    <<< ∃ C' (res: bool), is_CSS γ γ_fp γ_k γ_inr γ_fi root C'
        ∗ Ψ dop k C C' res, RET #res >>>.
  Proof.
    iIntros "HKin" (Φ) "AU". iLöb as "IH". wp_lam.
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I0) "(HI & HKS & HNDS & #Hglob & Hstar)".
    iDestruct "Hglob" as %Hglob. iDestruct "HKin" as %HKin.
    assert (root ∈ domm I0)%I as Hroot. { apply globalinv_root_fp. done. }
    iMod (own_update γ_fp (● domm I0) (● domm I0 ⋅ ◯ domm I0) with "HNDS") as "H".
    { apply auth_update_core_id. apply gset_core_id. done. }
    iDestruct "H" as "(HNDS & #Hfp0)".
    rewrite (big_sepS_elem_of_acc _ (domm I0) root); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b Ir) "(H1 & H2 & H3 & H4 & H5 & Hksr)".
    iPoseProof (auth_own_incl with "[$HI $H3]") as "%". iDestruct "H4" as %HNdsr.
    iMod (own_update (γ_inr root) _
                     (● (inset K Ir root ∪ linkset K Ir root)
                      ⋅ ◯ (inset K Ir root ∪ linkset K Ir root))
            with "Hksr") as "H".
    apply auth_update_core_id. apply gset_core_id. done. iDestruct "H" as "(Hksr & #Hinr)".
    iMod ("HAU" with "[HI HKS H1 H2 H3 H5 Hstar HNDS Hksr] ") as "AU".
    { iExists I0. iFrame "∗ % #". iApply "Hstar". iExists b, Ir. iFrame "∗ # %". }
    iModIntro. wp_bind (traverse _ _)%E.
    awp_apply (traverse_spec γ γ_fp γ_k γ_inr γ_fi root k root (domm I0) Ir). iFrame "∗ # %".
    iPureIntro. apply (globalinv_root_inr I0 Ir root k); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "Hst". iAaccIntro with "Hst"; first by eauto with iFrame.
    iIntros (n Ns In Cn) "(Hst & #Hinn & #Hfp & Hrepn & Hfil & Hks & #HNdsn & #Hinset & #Hnotout)".
    iDestruct "Hinn" as %Hinn. iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hrepn]"). eauto with iFrame.
    iIntros (b' Cn' res). iIntros "Hb". destruct b'.
    - iDestruct "Hb" as "(Hrep & #HΨ & #Hsub)".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(HI & HKS & HNDS & #Hglob & Hstar)".
      iDestruct "Hglob" as %Hglob'.
      iAssert (⌜n ∈ domm I⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (domm I)) with "[$]") as "%".
      iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
      iDestruct "Hstar" as "[Hn Hstar]".
      iDestruct "Hn" as (b' In1) "(Hlock & Hb & HIn & #HNds & Hfis & Hinreach)".
      destruct b'; first last. { iDestruct "Hb" as (Cn'') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In1).
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hrep Hks".
      iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In1.
      iFrame "∗ # %". eauto with iFrame. } iIntros "Hlock".
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof ((own_valid γ (● I)) with "HI") as "%".
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H3. apply leibniz_equiv in H3. replace In1.
      iPoseProof ((own_valid γ (◯ In)) with "HIn") as "%". rename H4 into HInV.
      assert (✓ In) as HInv. { apply (auth_frag_valid (◯ In)). done. }
      iAssert (node n In Cn' ∗ ⌜nodeinv In n⌝)%I with "[Hrep]" as "(Hrep & Hninv)".
      { iApply (node_implies_nodeinv _ _ _). iFrame "% ∗ #". } iDestruct "Hninv" as %Hninv.
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C2) with "[HKS Hks]") as "Hgks".
      iFrame "% ∗ #". iPureIntro. apply keyset_def; try done.
      iDestruct "Hgks" as (C2') "(#HΨC & Ha & Hf)".
      iModIntro. iExists (C2'), res. iSplitL. iSplitR "HΨC".
      { iExists I. iFrame "∗ % #".
      iApply "Hstar". iExists false, In.
      iFrame "∗ % #". iExists Cn'. eauto with iFrame. } done.
      iIntros "HΦ". iModIntro. wp_pures. done.
    - wp_match. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(HI & HKS & HNDS & #Hglob & Hstar)".
      iDestruct "Hglob" as %Hglob'.
      iAssert (⌜n ∈ domm I⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (domm I)) with "[$]") as "%".
      iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
      iDestruct "Hstar" as "[Hn Hstar]".
      iDestruct "Hn" as (b' In1) "(Hlock & Hb' & HIn & #HNds & Hfis & Hinreach)".
      destruct b'; first last. { iDestruct "Hb'" as (Cn'') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf. { iApply (node_sep_star n In In1).
      iFrame "∗ # %". } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hb Hks".
      iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In1.
      iFrame "∗ # %". eauto with iFrame. } iIntros "Hlock". iModIntro.
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H1. apply leibniz_equiv in H1. replace In1.
      iSplitR "". iExists I. iFrame "∗ % #". iApply "Hstar". iExists false, In. iFrame "∗ % #".
      iExists Cn. iFrame. iIntros "AU". iModIntro. wp_pures. iApply "IH"; try done.
  Qed.

End Link_Template.
