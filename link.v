Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Require Export flows.
Set Default Proof Using "All".

(* ---------- The program ---------- *)

Inductive dOp := memberOp | insertOp | deleteOp.

Variable findNext : val.
Variable decisiveOp : (dOp → val).
Variable searchStrSpec : (dOp → val).
Variable lockLoc : node → loc.
Variable getLockLoc : val.

Variable in_inset : key → flowintUR → node → Prop.
Variable in_edgeset : key → flowintUR → node → node → Prop.
Variable not_in_outset : key → flowintUR → node → Prop.
Variable cont : flowintUR → gset key.
Variable inreach : flowintUR → node → gset key.
Variable contextualLeq : flowintUR → flowintUR → Prop.
Variable is_empty_flowint : flowintUR → Prop.

Definition lockNode : val :=
  rec: "lockN" "x" :=
    let: "l" := getLockLoc "x" in
    if: CAS "l" #false #true
    then #()
    else "lockN" "x" .

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

Definition searchStrOp (Ψ: dOp) (root: node) : val :=
  rec: "dictOp" "k" :=
    let: "n" := traverse #root "k" in
    match: ((decisiveOp Ψ) "n" "k") with
      NONE => unlockNode "n";; "dictOp" "k"
    | SOME "res" => unlockNode "n";; "res"
    end.

(* ---------- Cameras used in the following proofs ---------- *)

(* RA for authoritative flow interfaces *)
Class flowintG Σ := FlowintG { flowint_inG :> inG Σ (authR flowintUR) }.
Definition flowintΣ : gFunctors := #[GFunctor (authR flowintUR)].

Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
Proof. solve_inG. Qed.

(* RA for authoritative set of nodes *)
Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR node)) }.
Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR node))].

Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
Proof. solve_inG. Qed.

(* RA for authoritative inreach sets *)
Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (authR (gsetUR key)) }.
Definition keysetΣ : gFunctors := #[GFunctor (authR (gsetUR key))].

Instance subG_keysetΣ {Σ} : subG keysetΣ Σ → keysetG Σ.
Proof. solve_inG. Qed.

(* RA for set of contents *)
Class contentG Σ := ContentG { content_inG :> inG Σ (authR (optionUR (exclR (gsetR key)))) }.
Definition contentΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (gsetR key))))].

Instance subG_contentΣ {Σ} : subG contentΣ Σ → contentG Σ.
Proof. solve_inG. Qed.

Section Link_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ, !contentG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* ---------- Flow interface set-up specific to this proof ---------- *)

  Variable root : node.

  Variable hrep : node → flowintUR → iProp.
  Parameter hrep_timeless_proof : ∀ n I, Timeless (hrep n I).
  Instance hrep_timeless n I : Timeless (hrep n I).
  Proof. apply hrep_timeless_proof. Qed.
  Parameter hrep_fp : ∀ n I_n, hrep n I_n -∗ ⌜Nds I_n = {[n]}⌝.

  Variable globalint : flowintUR → Prop.
  Hypothesis globalint_root_fp : ∀ I, globalint I → root ∈ Nds I.
  (* Hypothesis globalint_fpo : ∀ I, globalint I → FPo I = ∅. *)
  Hypothesis globalint_root_inr : ∀ I k, globalint I → k ∈ inreach I root.
  Hypothesis contextualLeq_impl_globalint :
    ∀ I I', globalint I → contextualLeq I I' → globalint I'.
  Hypothesis globalint_inreach :
    ∀ I1 I n, I1 ≼ I → Nds I1 = {[n]} → globalint I → inreach I1 n = inreach I n.
  Hypothesis globalint_preserve_inreach : ∀ I I' I_n I_n' n,
      ✓ I → ✓ I' → (∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o) → globalint I
      → Nds I_n = {[n]} → Nds I_n' = {[n]} → inreach I_n n = inreach I_n' n
      → ∀ n', n' ∈ Nds I' → inreach I n' = inreach I' n'.

  (* ---------- Coarse-grained specification ---------- *)

  Definition Ψ dop k (C: gsetO key) (C': gsetO key) (res: bool) : iProp :=
    match dop with
    | memberOp => (⌜C' = C ∧ (Is_true res ↔ k ∈ C)⌝)%I
    | insertOp => (⌜C' = union C {[k]} ∧ (Is_true res ↔ k ∉ C)⌝)%I
    | deleteOp => (⌜C' = difference C {[k]} ∧ (Is_true res ↔ k ∈ C)⌝)%I
    end.

  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.

  Lemma Ψ_determines_res dop k C1 C1' C2 C2' res1 res2 :
    Ψ dop k C1 C1' res1 ∗ Ψ dop k C2 C2' res2 ∗ ⌜C1 = C2⌝ -∗ ⌜res1 = res2⌝.
  Proof.
    destruct dop; iPureIntro; destr_bool;
      destruct H as ((HC1 & HkC1) & (HC2 & HkC2) & HEq);
      exfalso; rewrite HEq in HkC1; rewrite <- HkC2 in HkC1; inversion HkC1; contradiction.
  Qed.

  Lemma Ψ_determines_C' dop k C1 C1' C2 C2' res1 res2 :
    Ψ dop k C1 C1' res1 ∗ Ψ dop k C2 C2' res2 ∗ ⌜C1 = C2⌝ -∗ ⌜C1' = C2'⌝.
  Proof.
    destruct dop; iPureIntro; simpl; destr_bool;
      destruct H as ((HC1 & HkC1) & (HC2 & HkC2) & HEq); congruence.
  Qed.

  Axiom Ψ_keyset_theorem : ∀ dop k n I_n I_n' I I' res,
      ⌜globalint I⌝ ∗ ⌜Nds I_n = {[n]}⌝ ∗ ⌜in_inset k I_n n⌝ ∗ ⌜not_in_outset k I_n n⌝
      ∗ ⌜(∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o)⌝ ∗ ✓ I ∗ ✓ I'
      -∗ Ψ dop k (cont I_n) (cont I_n') res -∗ Ψ dop k (cont I) (cont I') res.


  (* ---------- Helper functions specs - proved for each implementation in GRASShopper ---------- *)

  Parameter getLockLoc_spec : ∀ (n: node),
                  (<<< True >>> getLockLoc #n @ ⊤
                           <<< ∃ l:loc, ⌜lockLoc n = l⌝, RET #l >>>)%I.


  Parameter findNext_spec : ∀ (n: node) (I_n : flowintUR) (k: key),
                  (<<< hrep n I_n >>> findNext #n #k @ ⊤
                              <<< ∃ (b: bool) (n': node), hrep n I_n ∗ 
                                                          (match b with true => ⌜in_edgeset k I_n n n'⌝ |
                                                                        false => ⌜not_in_outset k I_n n⌝ end),
                                  RET (match b with true => (SOMEV #n') | 
                                                    false => NONEV end) >>>)%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (I_n: flowintUR) (n: node) (k: key),
                  (<<< hrep n I_n ∗ ⌜in_inset k I_n n⌝ ∗ ⌜not_in_outset k I_n n⌝ ∗ ⌜Nds I_n = {[n]}⌝ >>>
                        decisiveOp dop #n #k @ ⊤
                   <<< ∃ (b: bool) (I_n': flowintUR) (res: bool), match b with false => hrep n I_n |
                                                              true => hrep n I_n' ∗ ⌜Ψ dop k (cont I_n) (cont I_n') res⌝
                                                                    ∗ ⌜contextualLeq I_n I_n'⌝ ∗ ⌜Nds I_n' = {[n]}⌝ end,
                       RET (match b with false => NONEV |
                                         true => (SOMEV #res) end) >>>)%I.

  (* ---------- The invariant ---------- *)

  Definition dictN : namespace := nroot .@ "dict".

  (* Also add FP I_n = {[n]} to invariant? *)
  Definition main_inv (γ: gname) (γ_fp: gname) (γ_inr: node → gname) (γ_c: gname) I N C
    : iProp :=
    (own γ_c (● (Some (Excl C))) ∗ ⌜C = cont I⌝
        ∗ own γ (● I) ∗ ⌜globalint I⌝
        ∗ ([∗ set] n ∈ (Nds I), (∃ b: bool, (lockLoc n) ↦ #b ∗ if b then True else (∃ (In: flowintUR),
                                                             own γ (◯ In) ∗ hrep n In)))
        ∗ own γ_fp (● N) ∗ ⌜N = (Nds I)⌝
        ∗ ([∗ set] n ∈ (Nds I), (∃ (Inr_n: gsetUR key), own (γ_inr n) (● Inr_n) ∗ ⌜Inr_n = inreach I n⌝))
    )%I.

  Definition is_dict γ γ_fp γ_inr γ_c :=
    inv dictN (∃ I N C, main_inv γ γ_fp γ_inr γ_c I N C)%I.

  Instance main_inv_timeless γ γ_fp γ_inr γ_c I N C :
    Timeless (main_inv γ γ_fp γ_inr γ_c I N C).
  Proof.
    rewrite /main_inv. repeat apply bi.sep_timeless; try apply _.
    apply big_sepS_timeless. intros. apply bi.exist_timeless. intros.
    apply bi.sep_timeless; try apply _.
    destruct x0; try apply _.
  Qed.

  (* ---------- Assorted useful lemmas ---------- *)

  Lemma auth_set_incl γ_fp Ns Ns' :
    own γ_fp (◯ Ns) ∗ own γ_fp (● Ns') -∗ ⌜Ns ⊆ Ns'⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro.
    rewrite auth_valid_discrete. simpl. rewrite ucmra_unit_right_id_L.
    intros. destruct H. inversion H0 as [m H1].
    destruct H1. destruct H2. apply gset_included in H2. rewrite /to_agree in H1.
    Admitted.

  (* TODO If you make the premise ✓ (◯ X), can move to util.v *)
  Lemma auth_frag_valid γ (X: flowintUR) : own γ (◯ X) -∗ ⌜✓ X⌝.
  Proof.
    rewrite own_valid. iPureIntro. by rewrite auth_valid_discrete.
  Qed.

  Lemma auth_own_incl γ (x y: flowintUR) : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. rewrite ucmra_unit_left_id_L. Admitted.

  Lemma auth_agree γ xs ys :
    own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
   iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

  (** The view of the authority can be updated together with the local view. *)
  Lemma auth_update γ ys xs1 xs2 :
    own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.


  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P I I_n I_n' x⌝ ∧ own γ x -∗
                  ∃ I', ⌜contextualLeq I I'⌝ ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝ ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P. simpl.
    case_eq (auth_auth_proj x); last first.
    - intros H. iIntros "(% & ?)". iExFalso. done.
    - intros p. intros H. case_eq p. intros q a Hp. case_eq a.
      intros intl b Ha. destruct intl as [ | I' ?]. iIntros "(% & ?)". iExFalso. done.
      case_eq intl; last first. intros u0 l _. iIntros "(% & ?)". iExFalso. done.
      + intros Hintl. simpl in b. assert (b = eq_refl) as H0. { admit. }
        rewrite H0. iIntros "(Hfr & Hown)". iDestruct "Hfr" as %Hfr. destruct Hfr as [Hfrag Hcon].
        destruct Hcon as [Hcon HIo]. destruct HIo as [Io HIo]. iExists I'.
        iSplitR. iPureIntro. { admit. }
        iSplitR. iPureIntro. exists Io. done.
  Admitted.


  Lemma inv_impl_fp n Ns γ γ_fp γ_inr γ_c I Ns' C:
    main_inv γ γ_fp γ_inr γ_c I Ns' C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗ ⌜n ∈ Nds I⌝.
  Proof.
    iIntros "(HInv & HNs & %)".
    iDestruct "HInv" as "(? & ? & ? & ? & HIns & HNs' & % & ?)".
    iPoseProof (auth_set_incl with "[$HNs $HNs']") as "%".
    iPureIntro. set_solver.
  Qed.

  Lemma inv_impl_inreach γ γ_fp γ_inr γ_c Inr n I Ns C :
    main_inv γ γ_fp γ_inr γ_c I Ns C ∗ own (γ_inr n) (◯ Inr) ∗ ⌜n ∈ Nds I⌝
    -∗ ⌜Inr ⊆ inreach I n⌝.
  Proof.
    iIntros "(HInv & HInr & %)".
    iDestruct "HInv" as "(? & ? & ? & ? & HIns & HNs' & % & HInrs)".
    iPoseProof ((big_sepS_elem_of_acc _ (Nds I) n) with "[$HInrs]") as "(HInr' & HInrRest)";
      first done.
    iDestruct "HInr'" as (Inr') "(HInr' & %)".
    rewrite <- H1.
    iApply (auth_set_incl with "[$HInr $HInr']").
  Qed.

  Lemma inv_impl_inreach_eq n γ γ_fp γ_inr γ_c I_n I Ns C :
    main_inv γ γ_fp γ_inr γ_c I Ns C ∗ own γ (◯ I_n) ∗ hrep n I_n
    -∗ ⌜inreach I n = inreach I_n n⌝.
  Proof.
    iIntros "(HInv & HIn & Hg)".
    iDestruct "HInv" as "(? & ? & HI & % & HIns & HNs' & % & HInrs)".
    iPoseProof (auth_own_incl γ I I_n with "[$HI $HIn]") as "%".
    iPoseProof (hrep_fp n I_n with "Hg") as "%".
    iPureIntro.
    by rewrite (globalint_inreach I_n I).
  Qed.

  Lemma rewrite_inside_big_sep I I' γ_inr :
    ([∗ set] n ∈ Nds I', (∃ Inr_n : gsetUR key,
                            own (γ_inr n) (● Inr_n) ∗ ⌜Inr_n = inreach I n⌝))
      -∗ ⌜∀ n', n' ∈ Nds I' → inreach I n' = inreach I' n'⌝
      -∗ ([∗ set] n ∈ Nds I', (∃ Inr_n : gsetUR key,
                                 own (γ_inr n) (● Inr_n) ∗ ⌜Inr_n = inreach I' n⌝)).
  Proof.
    iIntros "Hbig %" .
    iApply (big_sepS_mono _ _ (Nds I') with "Hbig").
    intros. iIntros "H".
    specialize a with x. apply a in H. rewrite H. done.
  Qed.

  (* ---------- Lock module proofs ---------- *)

  Lemma lockNode_spec (γ: gname) (γ_fp: gname) (γ_inr: node → gname) (γ_c: gname) (n: node) (Ns: gset node):
    is_dict γ γ_fp γ_inr γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗
          <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑dictN
          <<< ∃ (I_n: flowintUR), own γ (◯ I_n) ∗ hrep n I_n, RET #() >>>.
  Proof.
    iIntros "#HInv [Hl1 Hl2]" (Φ) "AU". iLöb as "IH".
    wp_lam. awp_apply getLockLoc_spec.
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (l) "#Hl". iModIntro. wp_let. wp_bind (CmpXchg _ _ _)%E.
    iInv dictN as ">HI".
    iDestruct "HI" as (I' N' C') "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)". iDestruct "Hl" as %Hl.
    iAssert (⌜n ∈ Nds I'⌝)%I with "[Hl1 Hl2 H6 H7]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns N') with "[$]") as "%". iDestruct "H7" as %H7.
      iDestruct "Hl2" as %Hl2. iEval (rewrite <-H7). iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I') n); last by eauto.
    iDestruct "H5" as "[ho hoho]".
    iDestruct "ho" as (b) "[Hlock Hlock']". iEval (rewrite Hl) in "Hlock". destruct b.
      - wp_cmpxchg_fail. iModIntro. iSplitR "Hl1 Hl2 AU". iNext. iExists I', N', C'. iFrame. iApply "hoho".
        iExists true. iEval (rewrite <-Hl) in "Hlock". iSplitL "Hlock". done. done. wp_pures.
        iDestruct "Hl1" as "#Hl1". iDestruct "Hl2" as "#Hl2". iApply "IH". done. done. done.
      - iMod "AU" as "[Ht [_ Hcl]]". iDestruct "Hlock'" as (In) "hehe".
        wp_cmpxchg_suc. iMod ("Hcl" with "hehe") as "HΦ".
        iModIntro. iModIntro. iSplitR "HΦ".
          * iNext. iExists I', N', C'. rewrite /main_inv. iFrame.
                iApply "hoho". iExists true. iEval (rewrite <-Hl) in "Hlock". iFrame.
          * wp_pures. done.
  Qed.

  Lemma unlockNode_spec (γ: gname) (γ_fp: gname) (γ_inr: node → gname) (γ_c: gname) (n: node) (Ns: gset node) :
    is_dict γ γ_fp γ_inr γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗
          <<< ∀ (I_n: flowintUR), hrep n I_n ∗ own γ (◯ I_n) >>>
                unlockNode #n    @ ⊤ ∖ ↑dictN
          <<< True, RET #() >>>.
  Proof.
    iIntros "#Hinv (Hfp & Hin)" (Φ) "AU". wp_lam. awp_apply getLockLoc_spec.
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (l) "Hl". iDestruct "Hl" as %Hl. iModIntro. wp_let. iInv dictN as ">HI".
    iDestruct "HI" as (I' N' C') "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)".
    iAssert (⌜n ∈ Nds I'⌝)%I with "[Hfp Hin H6 H7]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns N') with "[$]") as "%". iDestruct "H7" as %H7.
      iDestruct "Hin" as %Hl2. iEval (rewrite <-H7). iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I') n); last by eauto.
    iDestruct "H5" as "[ho hoho]".
    iDestruct "ho" as (b) "[Hlock Hlock']".
    iEval (rewrite Hl) in "Hlock".
    iMod "AU" as (I_n) "[Hr [_ Hcl]]". wp_store.
    iAssert (True)%I as "Ht". done.
    iMod ("Hcl" with "Ht") as "HΦ".
    iModIntro. iModIntro. iSplitR "HΦ". iNext. iExists I', N', C'. rewrite /main_inv. iFrame.
    iApply "hoho". iExists false. iEval (rewrite <-Hl) in "Hlock". iFrame. iExists I_n. 
    iDestruct "Hr" as "(? & ?)". eauto with iFrame. done.
  Qed.

  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)

  Lemma ghost_update_step γ γ_fp γ_inr γ_c (n n': node) (k:key) (Ns: gset node) (I_n: flowintUR) (Inr: gset key):
          is_dict γ γ_fp γ_inr γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝∗ own (γ_inr n) (◯ Inr) ∗ ⌜k ∈ Inr⌝ ∗ own γ (◯ I_n)
                                      ∗ ⌜Nds I_n = {[n]}⌝ ∗ ⌜in_edgeset k I_n n n'⌝
                    ={ ⊤ }=∗ ∃ Ns' Inr', own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ ∗ own (γ_inr n') (◯ Inr') ∗ ⌜k ∈ Inr'⌝
                                        ∗ own γ (◯ I_n).
  Proof.
  Admitted.

  Lemma ghost_update_traverse γ γ_fp γ_inr γ_c (k:key):
          is_dict γ γ_fp γ_inr γ_c -∗ True ={ ⊤ }=∗ ∃ Ns Inr, own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝ 
                                                              ∗ own (γ_inr root) (◯ Inr) ∗ ⌜k ∈ Inr⌝.
  Proof.
  Admitted.

  Lemma ghost_update_decisiveOp γ γ_fp γ_inr γ_c (n: node) (k:key) (Ns: gset node) (I_n: flowintUR) (Inr: gset key):
          is_dict γ γ_fp γ_inr γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ own (γ_inr n) (◯ Inr) ∗ ⌜k ∈ Inr⌝
                                        ∗ own γ (◯ I_n) ∗ hrep n I_n ∗ ⌜not_in_outset k I_n n⌝
                    ={ ⊤ }=∗ ⌜in_inset k I_n n⌝ ∗ hrep n I_n ∗ own γ (◯ I_n).
  Proof.
  Admitted.

  (* ---------- Refinement proofs ---------- *)

  Lemma traverse_spec (γ γ_fp γ_c: gname) γ_inr (k: key) (n: node) (Ns: gsetUR node) (Inr: gsetUR key):
        is_dict γ γ_fp γ_inr γ_c -∗ 
              own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ own (γ_inr n) (◯ Inr) ∗ ⌜k ∈ Inr⌝ -∗
          <<< True >>>
                traverse #n #k
                    @ ⊤∖↑dictN
          <<< ∃ (n': node) (Ns': gsetUR node) (Inr': gsetUR key) (I_n': flowintUR),
                    own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ ∗ own (γ_inr n') (◯ Inr') ∗ ⌜k ∈ Inr'⌝
                  ∗ own γ (◯ I_n') ∗ hrep n' I_n' ∗ ⌜not_in_outset k I_n' n'⌝, RET #n' >>>.
  Proof.
    iIntros "#HInv H". iLöb as "IH" forall (n Ns Inr). iIntros (Φ) "AU".
    iDestruct "H" as "(#Hfp & #HinN & Hinreach & #Hkin)". wp_lam. wp_let.
    awp_apply (lockNode_spec γ γ_fp γ_inr γ_c n Ns). done. eauto with iFrame.
    iAssert (True)%I as "Ht". done. iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (In) "(HIn & HrepN)". iModIntro. wp_pures. wp_bind (findNext _ _).
    awp_apply (findNext_spec n In k). iAaccIntro with "HrepN". eauto with iFrame.
    iIntros (b n') "(HrepN & Hb)". destruct b.
    - iModIntro. wp_match. iDestruct "Hb" as %Hb.
      iPoseProof (hrep_fp n In with "HrepN") as "%". rename H into HNds.
      iDestruct (ghost_update_step γ γ_fp γ_inr γ_c n n' k Ns In  with "[HInv] [Hfp HinN Hinreach Hkin HIn ]") as ">hoho".
      { done. } { iFrame "Hfp HinN Hinreach Hkin HIn". iPureIntro. done. }
      iDestruct "hoho" as (Ns' Inr') "(#Hfp' & #Hin' & Hinreach' & #Hkin' & HIn)".
      wp_bind (unlockNode _)%E. awp_apply(unlockNode_spec γ γ_fp γ_inr γ_c n Ns).
      done. eauto with iFrame. iAssert (hrep n In ∗ own γ (◯ In))%I with "[HrepN HIn]" as "Haac".
      { eauto with iFrame. } iAaccIntro with "Haac". eauto with iFrame.
      iIntros. iModIntro. wp_pures. iSpecialize ("IH" $! n' Ns' Inr'). iApply ("IH" with "[Hinreach']").
      iFrame "∗ # %". done.
    - iMod "AU" as "[_ [_ Hclose]]". iSpecialize ("Hclose" $! n Ns Inr In).
      iMod ("Hclose" with "[Hfp HinN Hinreach Hkin HIn HrepN Hb]") as "HΦ".
      eauto with iFrame. iModIntro. wp_pures. done.
  Qed.

  Lemma searchStrOp_spec (γ γ_fp γ_c: gname) γ_inr (dop:dOp) (k: key):
        is_dict γ γ_fp γ_inr γ_c -∗ 
          <<< ∀ (C: gset key), own γ_c (◯ (Some (Excl C))) >>>
                (searchStrOp dop root) #k
                    @ ⊤∖↑dictN
          <<< ∃ (C': gset key) (res: bool), own γ_c (◯ (Some (Excl C'))) ∗ Ψ dop k C C' res, RET #res >>>.
  Proof.
    iIntros "#HInv". iLöb as "IH". iIntros (Φ) "AU".
    wp_lam. wp_bind (traverse _ _)%E. iAssert (True)%I as "#Ht". done.
    iDestruct (ghost_update_traverse γ γ_fp γ_inr γ_c k with "[HInv] [Ht]") as ">hoho".             (*Why is Hfp persistent *)
    { done. } { done. } iDestruct "hoho" as (Ns Inr) "(#Hfp & #HinR & HINR & #Hkin)". 
    awp_apply (traverse_spec γ γ_fp γ_c γ_inr k root Ns Inr with "[] [HINR]"). done. 
    eauto with iFrame. iAaccIntro with "Ht". eauto with iFrame.
    iIntros (n Ns' Inr' In) "(#Hfp' & #HinN & Hinreach & #Hkin' & HIn & HrepN & #Hnotout)".
    iModIntro. wp_let. wp_bind (decisiveOp _ _ _)%E.
    iDestruct (ghost_update_decisiveOp γ γ_fp γ_inr γ_c n k Ns' In Inr' with "[HInv] [Hinreach HIn HrepN]") as ">hoho".
    { done. } { eauto with iFrame. } iDestruct "hoho" as "(#Hinset & HrepN & HIn)".
    iPoseProof (hrep_fp n In with "HrepN") as "%". rename H into HNds.
    awp_apply (decisiveOp_spec dop In n k). 
    iAssert (hrep n In ∗ ⌜in_inset k In n⌝ ∗ ⌜not_in_outset k In n⌝ ∗ ⌜Nds In = {[n]}⌝)%I with "[HrepN]" as "Haac".
    { iFrame "∗ # %". } iAaccIntro with "Haac". iIntros "(Hrep & _)". iModIntro. iFrame "∗ # %".
    iIntros (b In' res) "Hb". destruct b; last first.
    - iModIntro. wp_match. awp_apply (unlockNode_spec γ γ_fp γ_inr γ_c n Ns'). done. eauto with iFrame.
      iAssert (hrep n In ∗ own γ (◯ In))%I with "[HIn Hb]" as "Haac". { eauto with iFrame. }
      iAaccIntro with "Haac". iIntros "(Hrep & HIn)". iModIntro. eauto with iFrame.
      iIntros. iModIntro. wp_pures. iApply "IH". done.
    - iInv dictN as ">HI". iDestruct "HI" as (I Nd Cs) "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)".
      iDestruct "H2" as %H2. iDestruct "H4" as %H4. iEval (rewrite H2) in "H1".
      iPoseProof (auth_own_incl with "[$H3 $HIn]") as (I2)"%".
      iPoseProof ((own_valid γ (● I)) with "H3") as "%".
      iDestruct "Hb" as "(HrepN & #HΨ & #Hcon & #HNds')". iDestruct "Hcon" as %Hcon. iDestruct "HNds'" as %HNds'.
      iMod (own_updateP (flowint_update_P I In In') γ (● I ⋅ ◯ In) with "[H3 HIn]") as (?) "H0".
      { apply (flowint_update I In In'). admit. } { rewrite own_op. iFrame. }
      iPoseProof ((flowint_update_result γ I In In') with "H0") as (I') "(% & % & HIIn)".
      iAssert (own γ (● I') ∗ own γ (◯ In'))%I with "[HIIn]" as "(HI' & HIn')". { by rewrite own_op. }
      iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
      iPoseProof ((Ψ_keyset_theorem dop k n In In' I I' res) with "[Hinset Hnotout] [HΨ]") as "HΨI".
      { repeat iSplitL; try done; iPureIntro; apply auth_auth_valid; done. } { admit. }
      iMod "AU" as (C) "[hoho [_ Hcl]]".
      iDestruct (auth_agree with "H1 hoho") as %Hauth.
      iMod (auth_update γ_c (cont I') with "H1 hoho") as "[H1 hoho]".
      iSpecialize ("Hcl" $! (cont I') res). iEval (rewrite <-Hauth) in "Hcl".
      iMod ("Hcl" with "[hoho HΨI]") as "HΦ". eauto with iFrame.
      iModIntro. iSplitR "HrepN HIn' HΦ".
        + iNext. iExists I', Nd, (cont I').
          unfold main_inv. assert (globalint I') as HI'. { (* by apply (contextualLeq_impl_globalint I I')*) admit. }
          assert (Nds I = Nds I') as HH. { (*by apply (contextualLeq_impl_fp I I').*) admit. }
          iEval (rewrite HH) in "H5 H7 H8". iFrame "∗ % #".
          iPoseProof ((rewrite_inside_big_sep I I' γ_inr) with "[H8] [%]") as "?"; first done. 
          { apply (globalint_preserve_inreach I I' In In' n); try apply auth_auth_valid; try done. admit. }
          iFrame. iPureIntro. reflexivity.
        + iModIntro. wp_pures. wp_bind (unlockNode _)%E.
          iDestruct "HΦ" as "_". awp_apply (unlockNode_spec γ γ_fp γ_inr γ_c n Ns'). done.
          iSplitL. iApply "Hfp'". iApply "HinN".
          iAssert (hrep n In' ∗ own γ (◯ In'))%I with "[HrepN HIn']" as "Haac".
          { eauto with iFrame. } iAaccIntro with "Haac". iIntros "(Hrep & HInt)". iModIntro. 
          iFrame "Hrep". iFrame "HInt". iIntros . iModIntro. wp_pures.
 

















