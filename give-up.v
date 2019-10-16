(*  1) what to keep outside (persistant stuff)
*)
Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Require Import flows.
Set Default Proof Using "Type*".

(* ---------- The program ---------- *)

Inductive dOp := memberOp | insertOp | deleteOp.

Variable findNext : val.
Variable inRange : val.
Variable decisiveOp : (dOp → val).
Variable searchStrSpec : (dOp → val).
Variable lockLoc : node → loc.
Variable getLockLoc : val.

Variable in_inset : key → flowintUR → node → Prop.                    (* Couldn't load from flows.v *)
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
    else "lockN" "x".

Definition unlockNode : val :=
  λ: "x",
  let: "l" := getLockLoc "x" in
  "l" <- #false.

Definition traverse (root: node) : val :=
  rec: "tr" "n" "k" :=
    lockNode "n";;
    if: inRange "n" "k" then
      match: (findNext "n" "k") with
        NONE => "n"
      | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
      end
    else
      unlockNode "n";;
      "tr" #root "k".

Definition searchStrOp (Ψ: dOp) (root: node) : val :=
  rec: "dictOp" "k" :=
    let: "n" := (traverse root) #root "k" in
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

(* RA for set of contents *)
Class contentG Σ := ContentG { content_inG :> inG Σ (gsetR key) }.
Definition contentΣ : gFunctors := #[GFunctor (gsetR key)].

Instance subG_contentΣ {Σ} : subG contentΣ Σ → contentG Σ.
Proof. solve_inG. Qed.

Section Give_Up_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !contentG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  Variable (Δ : list (prodO valO valO -n> iProp)).

  (* ---------- Flow interface set-up specific to this proof ---------- *)

  Variable root : node.
  Variable hrep : node → flowintUR → iProp.
  Parameter hrep_timeless_proof : ∀ n I, Timeless (hrep n I).
  Instance hrep_timeless n I : Timeless (hrep n I).
  Proof. apply hrep_timeless_proof. Qed.
  Parameter hrep_fp : ∀ n I_n, hrep n I_n -∗ ⌜Nds I_n = {[n]}⌝.

  Variable globalint : flowintUR → Prop.
  Hypothesis globalint_root_fp: ∀ I, globalint I → root ∈ Nds I.

 (* Hypothesis globalint_fpo : ∀ I, globalint I → ∀ n:node, outf I n = 0.   
                                                         Can't figure out (outf I n). Also is it appropriate?  *)

  Lemma contextualLeq_impl_globalint :
    ∀ I I', globalint I →  contextualLeq I I' → globalint I'.

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

(*  Axiom cg_decisive_op_spec :
    ∀ dop Γ K E t τ C γ_c k,
    (own γ_c C -∗                                   (* Precondition *)
     (∀ res C', own γ_c C' ∗ Ψ dop k C C' res -∗    (* Postcondition *)
      ({E;Δ;Γ} ⊨ t ≤log≤ fill K (#res) : τ)) -∗
     {E;Δ;Γ} ⊨ t ≤log≤ fill K (searchStrSpec dop #k) : τ)%I.

To add what is needed later.
*)

  Axiom Ψ_keyset_theorem : ∀ dop k n I_n I_n' I I' res,
      ⌜globalint I⌝ ∗ ⌜Nds I_n = {[n]}⌝ ∗ ⌜in_inset k I_n n⌝ ∗ ⌜not_in_outset k I_n n⌝
      ∗ ⌜(∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o)⌝ ∗ ✓ I ∗ ✓ I'
      -∗ Ψ dop k (cont I_n) (cont I_n') res -∗ Ψ dop k (cont I) (cont I') res.


  (* ---------- Helper functions specs - proved for each implementation in GRASShopper ---------- *)

Parameter getLockLoc_spec : ∀ (n: node),
                  (<<< True >>> getLockLoc #n @ ⊤
                           <<< ∃ l:loc, ⌜lockLoc n = l⌝, RET #l >>>)%I.

  Parameter inRange_spec : ∀ (n: node) (I_n : flowintUR) (k: key),
                  (<<< hrep n I_n >>> inRange #n #k @ ⊤
                              <<< ∃ b: bool, hrep n I_n ∗ (match b with true => ⌜in_inset k I_n n⌝ |
                                                                        false => ⌜True⌝ end),
                                  RET #b >>>)%I.

  Parameter findNext_spec : ∀ (n: node) (I_n : flowintUR) (k: key),
                  (<<< hrep n I_n >>> findNext #n #k @ ⊤
                              <<< ∃ (b: bool) (n': node), hrep n I_n ∗ (match b with true => ⌜in_edgeset k I_n n n'⌝ |
                                                                                     false => ⌜not_in_outset k I_n n⌝ end),
                                  RET (match b with true => (SOMEV #n') | 
                                                    false => NONEV end) >>>)%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (I_n: flowintUR) (n: node) (k: key),
                  (<<< hrep n I_n ∗ ⌜in_inset k I_n n⌝ ∗ ⌜not_in_outset k I_n n⌝ >>>
                        decisiveOp dop #n #k @ ⊤
                   <<< ∃ (b: bool) (I_n': flowintUR) (res: bool), match b with false => hrep n I_n |
                                                                         true => hrep n I_n' ∗ Ψ dop k (cont I_n) (cont I_n') res
                                                                                ∗ ⌜contextualLeq I_n I_n'⌝ ∗ ⌜Nds I_n' = {[n]}⌝ end,
                       RET (match b with false => NONEV |
                                         true => (SOMEV #res) end) >>>)%I. 

(*
  Parameter decisiveOp_spec :
    ∀ dop (I_n: flowintUR) Γ K t τ  n (k: key),
    (hrep n I_n ∗ ⌜in_inset k I_n n⌝ ∗ ⌜not_in_outset k I_n n⌝ -∗
      ((hrep n I_n -∗ ({Δ;Γ} ⊨ fill K (Fold NONE) ≤log≤ t : τ))
       ∧ (∀ res (I_n': flowintUR), hrep n I_n' ∗ Ψ dop k (cont I_n) (cont I_n') res
           ∗ ⌜contextualLeq I_n I_n'⌝ ∗ ⌜FP I_n' = {[n]}⌝
          -∗ ({Δ;Γ} ⊨ fill K (Fold (SOME #res)) ≤log≤ t : τ)))
     -∗ {Δ;Γ} ⊨ fill K (decisiveOp dop #n #k) ≤log≤ t : τ)%I.

  *)

  (* ---------- The invariant ---------- *)

  Definition dictN : namespace := N .@ "dict".

  Definition main_inv (γ: gname) (γ_fp: gname) (γ_c: gname) I Ns C
    : iProp :=
    (own γ_c C ∗ ⌜C = cont I⌝
        ∗ own γ (● I) ∗ ⌜globalint I⌝
        ∗ ([∗ set] n ∈ (Nds I), (∃ b: bool, (lockLoc n) ↦ #b
                                ∗ if b then True else (∃ (In: flowintUR),
                                                         own γ (◯ In) ∗ hrep n In ∗ ⌜Nds In = {[n]}⌝)))
        ∗ own γ_fp (● Ns) ∗ ⌜Ns = (Nds I)⌝
    )%I.

  Definition is_dict γ γ_fp γ_c :=
    inv dictN (∃ I Ns C, (main_inv γ γ_fp γ_c I Ns C))%I.

  Instance main_inv_timeless γ γ_fp γ_c I N C :
    Timeless (main_inv γ γ_fp γ_c I N C).
  Proof.
    rewrite /main_inv. repeat apply bi.sep_timeless; try apply _.
    try apply big_sepS_timeless. intros. apply bi.exist_timeless. intros.
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

  Lemma auth_own_incl γ (x y: flowintUR) : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. rewrite ucmra_unit_left_id_L. Admitted.

  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P I I_n I_n' x⌝ ∧ own γ x -∗
                                          ∃ I', ⌜contextualLeq I I'⌝ ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝ 
                                                                     ∗ own γ (● I' ⋅ ◯ I_n').
  Proof. Admitted.
(* flowint_update_P is undefined

    unfold flowint_update_P. simpl.
    case_eq x.
    case_eq (● x).
    - intros e Hax xa xo Hx.
      case_eq e.
      + intros u He. rewrite <- Hx. rewrite -> Hax. rewrite -> He.
        iIntros "[(% & % & %) Hown]".
        iExists u. repeat iSplit; try done.
        replace I_n'. rewrite <- auth_both_op.
        assert (∀ I: flowintUR, Some (Excl I) = Excl' I).
        { intros. done. }
        replace (Excl' u) with (authoritative x).
        replace (Auth (authoritative x) (auth_own x)) with x. done.
        destruct x. done. 
        congruence.
      + intros He.
        replace (authoritative (Auth xa xo)) with (Some (ExclBot: excl flowintUR)).
        iIntros "(% & ?)". iExFalso. done.
        congruence.
    - intros Hax xa xo Hx.
      rewrite <- Hx. rewrite Hax.
      iIntros "(% & ?)". iExFalso. done.
  Qed.
*)

  Lemma inv_impl_fp n Ns γ γ_fp γ_c I Ns' C:
    main_inv γ γ_fp γ_c I Ns' C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗ ⌜n ∈ Nds I⌝.
  Proof.
    iIntros "(HInv & HNs & %)".
    iDestruct "HInv" as "(? & ? & ? & ? & HIns & HNs' & %)".
    iPoseProof (auth_set_incl with "[$HNs $HNs']") as "%".
    iPureIntro. set_solver.
  Qed.                                       (* Made Proof using Type* *)

  (* ---------- Lock module proofs ---------- *)

  Lemma lockNode_spec (γ: gname) (γ_fp: gname) (γ_c: gname) (n: node) (Ns: gset node):
    is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗
          <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑dictN
          <<< ∃ (I_n: flowintUR), own γ (◯ I_n) ∗ hrep n I_n ∗ ⌜Nds I_n = {[n]}⌝, RET #() >>>.
  Proof.
    iIntros "#HInv [Hl1 Hl2]" (Φ) "AU". iLöb as "IH".
    wp_lam. awp_apply getLockLoc_spec.
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (l) "#Hl". iModIntro. wp_let. wp_bind (CmpXchg _ _ _)%E.
    iInv dictN as ">HI".
    iDestruct "HI" as (I' N' C') "(H1 & H2 & H3 & H4 & H5 & H6 & H7)". iDestruct "Hl" as %Hl.
    iAssert (⌜n ∈ Nds I'⌝)%I with "[Hl1 Hl2 H6 H7]" as "%".
    { (*iEval (rewrite <- H1).*) iPoseProof ((auth_set_incl γ_fp Ns N') with "[$]") as "%".
      iDestruct "H7" as %H7. iDestruct "Hl2" as %Hl2. iEval (rewrite <-H7). iPureIntro. set_solver. }
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

  Lemma unlockNode_spec (γ: gname) (γ_fp: gname) (γ_c: gname) (n: node) (Ns: gset node) (I_n: flowintUR) :
    is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ ⌜Nds I_n = {[n]}⌝ -∗
          <<< hrep n I_n ∗ own γ (◯ I_n) >>>
                unlockNode #n    @ ⊤ ∖ ↑dictN
          <<< True, RET #() >>>.
  Proof.
    iIntros "#Hinv (Hfp & Hin & Hnds)" (Φ) "AU". wp_lam. awp_apply getLockLoc_spec.
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (l) "#Hl". iModIntro. wp_let. iInv dictN as ">HI".
    iDestruct "HI" as (I' N' C') "(H1 & H2 & H3 & H4 & H5 & H6 & H7)".  iDestruct "Hl" as %Hl.
    iAssert (⌜n ∈ Nds I'⌝)%I with "[Hfp Hin H6 H7]" as "%".
    { (*iEval (rewrite <- H1).*) iPoseProof ((auth_set_incl γ_fp Ns N') with "[$]") as "%".
      iDestruct "H7" as %H7. iDestruct "Hin" as %Hl2. iEval (rewrite <-H7). iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I') n); last by eauto.
    iDestruct "H5" as "[ho hoho]".
    iDestruct "ho" as (b) "[Hlock Hlock']".
    iEval (rewrite Hl) in "Hlock".
    iMod "AU" as "[[Hrep Hs] [_ Hcl]]". wp_store.
    iAssert (True)%I as "Ht". done.
    iMod ("Hcl" with "Ht") as "HΦ".
    iModIntro. iModIntro. iSplitR "HΦ". iNext. iExists I', N', C'. rewrite /main_inv. iFrame.
    iApply "hoho". iExists false. iEval (rewrite <-Hl) in "Hlock". iFrame. iExists I_n. iFrame. done.
  Qed.


  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)

  Lemma ghost_update_step γ γ_fp γ_c (n n': node) (k:key) (Ns: gset node) (I_n: flowintUR):
          is_dict γ γ_fp γ_c ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ own γ (◯ I_n) ∗ ⌜Nds I_n = {[n]}⌝
       ∗ ⌜in_inset k I_n n⌝ ∗ ⌜in_edgeset k I_n n n'⌝ ={ ⊤ }=∗ ∃ (Ns': gset node), own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ 
                                                        ∗ ⌜root ∈ Ns'⌝.
  Proof. 
    iIntros "(Hinv & HNs & % & HIn & % & % & %)".
    iInv dictN as ">HInv" "Hclose".
    iDestruct "HInv" as (I Ns' C) "HInv".
    iPoseProof (inv_impl_fp n Ns with "[$HInv $HNs //]") as "%".
    iDestruct "HInv" as "(? & % & HI & % & ? & HNs' & %)".
    iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
    iAssert (⌜n' ∈ Nds I⌝)%I as "%".
    { iPureIntro.
      assert (n' ∈ Nds I2).
      { apply (flowint_step I I_n _ k n). done. admit.
        replace (Nds I_n). set_solver. admit. (*apply globalint_fpo. *) }
      apply flowint_comp_fp in H7. set_solver.
    }
    iMod (own_update γ_fp (● Ns') (● Ns' ⋅ ◯ Ns') with "HNs'") as "HNs'".
      admit. iDestruct "HNs'" as "(HNs0 & HNs')".
    iMod ("Hclose" with "[-HNs' HIn]"). { iNext. iExists I, Ns', C.  iFrame "# % ∗". }
    iModIntro. iExists Ns'. iFrame "# % ∗".
    rewrite <-H6 in H8. iSplit. iPureIntro. done.
    iPureIntro. rewrite H6. apply globalint_root_fp. done.
  Admitted.
    
  
(*
  Lemma ghost_update_step γ γ_fp γ_c n n' (k: key) (Ns: gsetUR node) I_n Γ t t' τ :
    is_dict γ γ_fp γ_c
        ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ own γ (◯ I_n) ∗ ⌜FP I_n = {[n]}⌝
        ∗ ⌜in_inset k I_n n⌝ ∗ ⌜in_edgeset k I_n n n'⌝
     -∗ ((∀ Ns', own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ ∗ ⌜root ∈ Ns'⌝ ∗ own γ (◯ I_n)
                 -∗ ({Δ;Γ} ⊨ t ≤log≤ t' : τ))
           -∗ {Δ;Γ} ⊨ t ≤log≤ t' : τ)%I.
  Proof.
    iIntros "(Hinv & HNs & % & HIn & % & % & %) HPost".
    iInv dictN as ">HInv" "HClose".
    iDestruct "HInv" as (I Ns' C) "HInv".
    iPoseProof (inv_impl_fp n Ns with "[$HInv $HNs //]") as "%".
    (* I = I_n ⋅ I2 *)
    iDestruct "HInv" as "(? & % & HI & % & ? & HNs' & %)".
    iPoseProof (auth_own_incl with "[$HI $HIn]") as "%".
    unfold included in H8. destruct H8 as [I2 Hmult].
    (* n' ∈ FP I *)
    iPoseProof ((own_valid γ (● I)) with "HI") as "%".
    iAssert (⌜n' ∈ FP I⌝)%I as "%".
    { iPureIntro.
      assert (n' ∈ FP I2).
      { apply (flowint_step I I_n _ k n). done.
        by apply auth_auth_valid.
        replace (FP I_n). set_solver. done. by apply globalint_fpo. }
      apply flowint_comp_fp in Hmult. set_solver.
    }
    (* snapshot fp to get Ns' *)
    iMod (own_update γ_fp (● Ns') (● Ns' ⋅ ◯ Ns') with "HNs'") as "HNs'";
      first by apply auth_set_snapshot.
    iEval (rewrite own_op) in "HNs'". iDestruct "HNs'" as "(HNs0 & HNs')".

    iMod ("HClose" with "[-HPost HNs' HIn]").
    {
      iNext. iExists I, Ns', C. iFrame "# % ∗".
    }
    iApply ("HPost" with "[-]").
    iFrame. iPureIntro. split; replace Ns'; try done.
    by apply globalint_root_fp.
  Qed.
*)
  (* ---------- Refinement proofs ---------- *)

(*  Lemma traverse_spec (γ: gname) (γ_fp: gname) γ_c (Ns: gsetUR node)
        Γ K t τ (n: node) (k: key) :
    is_dict γ γ_fp γ_c -∗
    (own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ ⌜root ∈ Ns⌝ -∗
     (∀ (n': node) (Ns': gsetUR node) (I_n': flowintUR),
       own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ ∗ own γ (◯ I_n') ∗ hrep n' I_n' ∗ ⌜FP I_n' = {[n']}⌝
       ∗ ⌜in_inset k I_n' n'⌝ ∗ ⌜not_in_outset k I_n' n'⌝ -∗
       ({Δ;Γ} ⊨ fill K (#n') ≤log≤ t : τ)) -∗
     {Δ;Γ} ⊨ fill K (traverse root #n #k) ≤log≤ t : τ)%I.
*)

  Lemma traverse_spec (γ γ_fp γ_c: gname) (k: key) :
        ∀ (n: node) (Ns: gsetUR node),
        is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ ⌜root ∈ Ns⌝ -∗
          <<< True >>>
                traverse root #n #k
                    @ ⊤∖↑dictN
          <<< ∃ (n': node) (Ns': gsetUR node) (I_n': flowintUR), ⌜n' ∈ Ns'⌝ ∗ own γ_fp (◯ Ns')
                 ∗ own γ (◯ I_n') ∗ hrep n' I_n' ∗ ⌜Nds I_n' = {[n']}⌝ 
                 ∗ ⌜in_inset k I_n' n'⌝ ∗ ⌜not_in_outset k I_n' n'⌝, RET #n' >>>.
  Proof. 
    iIntros (n Ns). iIntros "#HInv H". iLöb as "IH" forall (n Ns).
    iIntros (Φ) "AU". iDestruct "H" as "(#Hfp & #Hin & #Hr)".
    wp_lam. wp_let. awp_apply (lockNode_spec γ γ_fp γ_c n Ns).
    - done.
    - iSplit. done. done.
    - iAssert (True)%I as "Ht". done.
      iAaccIntro with "Ht". eauto 4 with iFrame. iIntros (In) "(HInt & Hrep & #Hdom)". iModIntro. wp_pures.
      wp_bind (inRange _ _)%E. awp_apply (inRange_spec n In k). iAaccIntro with "Hrep". eauto with iFrame.
      iIntros (b) "(Hrep & H1)". iModIntro. destruct b.
        + (* inRange succeeds *)
          wp_if. wp_bind (findNext _ _)%E. awp_apply (findNext_spec n In k).
          iAaccIntro with "Hrep". eauto with iFrame. iIntros (b n') "(Hrep & H2)". 
          destruct b.
            * (* findNext succeeds *) 
               iModIntro. wp_pures. awp_apply (unlockNode_spec γ γ_fp γ_c n Ns In).
               { done. } { eauto with iFrame. } iCombine "Hrep" "HInt" as "Haac".
               iAaccIntro with "Haac". { iIntros "(Hrep & HInt)". iModIntro. iFrame. } iIntros "Ht". iModIntro.
               wp_pures. iApply "IH". (*iMod ghost_update_step.*) admit. done.
            * (* findNext fails *)
              iMod "AU" as "[Ht [_ HClose]]". iSpecialize ("HClose" $! n Ns In).
              iMod ("HClose" with "[Hfp HInt Hrep Hdom H1 H2]") as "HΦ". eauto with iFrame.
              iModIntro. wp_pures. done.
        + (*inRange fails *)                                 (* Don't understand how the context is broken up with intro *)
          wp_if. awp_apply (unlockNode_spec γ γ_fp γ_c n Ns In). done. eauto with iFrame.  iCombine "Hrep" "HInt" as "Haac".
          iAaccIntro with "Haac". { iIntros "(Hrep & HInt)". iModIntro. iFrame. } 
          iIntros. iModIntro. wp_pures. iApply "IH". eauto with iFrame. done.
  Admitted.

  Theorem searchStrOp_spec (γ γ_fp γ_c: gname) (dop: dOp) (k: key):
          ∀ (Ns: gsetUR node) (C: gsetUR key),
          is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜ root ∈ Ns ⌝ ∗ own γ_c (◯ C) -∗
      <<< True >>>
            (searchStrOp dop root) #k
                  @ ⊤∖↑dictN
      <<< ∃ (C': gsetUR key) (res: bool), own γ_c (◯ C') ∗ Ψ dop k C C' res, RET #res >>>.
  Proof.
    iIntros (Ns C). iIntros "#HInv H" (Φ) "AU". iLöb as "IH" forall (Ns).
    wp_lam. wp_bind(traverse _ _ _)%E. iDestruct "H" as "#(H1 & H2 &H3)".
    awp_apply (traverse_spec γ γ_fp γ_c). done. eauto with iFrame.
    iAssert (True)%I as "Ht". done. iAaccIntro with "Ht". eauto with iFrame.
    iIntros (n Ns' In) "(#Hin & #Hfp & HInt & Hrep & #HNds & #Hinset & #Hout)". iModIntro. wp_let.
    wp_bind(decisiveOp dop _ _)%E. awp_apply (decisiveOp_spec dop In n k).
    iAssert (⌜in_inset k In n⌝ ∗ ⌜not_in_outset k In n⌝)%I as "Haac1". { eauto with iFrame. }
    iCombine "Hrep" "Haac1" as "Haac".
    iAaccIntro with "Haac". { iIntros "(Hrep & ?)". iModIntro. iFrame. }
    iIntros (b In' res) "Hb". destruct b.
    - iMod "AU" as "[Ht [_ Hcl]]". iDestruct "Hb" as "(Hf & H4 & H5 & H6)".
      iSpecialize ("Hcl" $! (cont In') res). iAssert (⌜C = cont In⌝)%I as %Hcont. { admit. }
      iEval (rewrite Hcont) in "H3". iEval (rewrite Hcont) in "Hcl". iMod ("Hcl" with "[H3 H4]"). wp_pures. iDestruct "Hb" as "(Hf & H4 & H5 & H6)". iMod "AU" as "[Ht [_ Hcl]]".
      wp_bind(unlockNode _)%E. 
      awp_apply (unlockNode_spec γ γ_fp γ_c n Ns' In').
    - iModIntro. wp_pures. awp_apply (unlockNode_spec γ γ_fp γ_c n Ns' In). done. iSplit. done. iSplit. done. done.
      iAaccIntro with "[$Hb $HInt]". iIntros "(Hb & HInt)". eauto with iFrame. iIntros. iModIntro.
      wp_pures. iApply "IH". iSplit. iApply "H1". iSplit. done. done. done.
f
(*
  Theorem searchStrOp_refinement dop Γ γ γ_fp γ_c (k: key) :
    is_dict γ γ_fp γ_c -∗
    {Δ;Γ} ⊨ (searchStrOp dop root) #k ≤log≤ (searchStrSpec dop) #k : TBool.
  Proof.
    iIntros "#Hinv".
    iLöb as "IH".
    rewrite {2}/searchStrOp. unlock. simpl. rel_rec_l.
    (* Open inv and make some frame preserving updates to get traverse's precondition *)
    iInv dictN as ">HInv" "HClose".
    iDestruct "HInv" as (I Ns C) "(? & ? & ? & Hgi & ? & HNs & HFP)".
    iMod (own_update γ_fp (● Ns : authR (gsetUR node)) (● Ns ⋅ ◯ Ns) with "HNs") as "HNs".
    { apply auth_set_snapshot. }
    iAssert (⌜root ∈ Ns⌝)%I with "[HFP Hgi]" as "%".
    { iDestruct "HFP" as "%". iDestruct "Hgi" as "%".
      iPureIntro. rewrite H0. by apply globalint_root_fp. }
    iEval (rewrite own_op) in "HNs".
    iDestruct "HNs" as "(HNs0 & HNs)".
    iMod ("HClose" with "[-HNs]").
    {  iNext. iExists I, Ns, C. iFrame. }
    clear I. clear C.
    (* Now execute traverse *)
    rel_apply_l ((traverse_spec γ γ_fp γ_c Ns) with "[//] [$HNs //]").
    iIntros (n' Ns' I_n') "(#HN & % & HIn & Hg & % & % & %)".
    rel_rec_l.
    (* Execute decisiveOp *)
    rel_apply_l (decisiveOp_spec with "[$Hg //]"). iSplit.
    - (* decisiveOp fails *)
      iIntros "Hg". rel_unfold_l. rel_case_l. rel_rec_l.
      rel_apply_l (unlockNode_spec with "[# $] [$HN $HIn $Hg //]").
      rel_rec_l. rewrite /searchStrOp. unlock. simpl.
      iApply "IH".
    - (* decisiveOp succeeds *)
      iIntros (res I_n'') "(Hg' & #HΨIn & % & %)".
      rel_unfold_l. rel_case_l. rel_rec_l.
      (* Open invariant, execute RHS, linearize *)
      iInv dictN as ">HInv" "HClose".
      iDestruct "HInv" as (I Ns'' C) "(HC & % & HI & % & HInvRest)".
      (* Execute RHS *)
      rel_apply_r (cg_decisive_op_spec with "[$]").
      iIntros (res' C') "[HC' #HΨC]".
      (* Update the flow interface *)
      iPoseProof ((own_valid γ (● I)) with "HI") as "%".
      iMod (own_updateP (flowint_update_P I I_n' I_n'') γ (● I ⋅ ◯ I_n') with "[HI HIn]") as (?) "H0".
      { by apply (flowint_update I I_n' I_n''). }
      { rewrite own_op. iFrame. }
      iPoseProof ((flowint_update_result γ I I_n' I_n'') with "H0") as (I') "(% & % & HIIn)".
      iAssert (own γ (● I') ∗ own γ (◯ I_n''))%I with "[HIIn]" as "(HI' & HIn')".
      { by rewrite own_op. }
      iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
      iPoseProof ((Ψ_keyset_theorem dop k n' I_n' I_n'' I I' res) with "[-] [$HΨIn]") as "#HΨI".
      { iPureIntro. repeat split; try done; by apply auth_auth_valid. }
      assert (FP I = FP I') as HFP. { by apply contextualLeq_impl_fp. }
                                    (* Close inv *)
                                    iMod ("HClose" with "[HC' HI' HInvRest]").
      {
        iNext. iExists I', Ns'', C'.
        iEval (rewrite HFP) in "HInvRest".
        iPoseProof ((Ψ_determines_C' dop k C C' (cont I) (cont I')) with "[]") as "%". by iFrame "# %".
        assert (globalint I'). by apply (contextualLeq_impl_globalint I I').
        iDestruct "HInvRest" as "(? & ? & %)".
        iFrame "# ∗ %".
      }
      (* Execute unlockNode *)
      rel_bind_l (unlockNode #n').
      rel_apply_l (unlockNode_spec with "[//] [$HN $HIn' $Hg' //]").
      rel_rec_l.
      iAssert (⌜res = res'⌝)%I as "%".
      { iApply Ψ_determines_res. iFrame "HΨC".
        iSplit.
        iApply ((Ψ_keyset_theorem dop k n' I_n' I_n'' I I' res) with "[-] [$HΨIn]").
        { iPureIntro. repeat split; try done; eauto using auth_auth_valid. }
          by iPureIntro.
      }
      replace res.
      iApply bin_log_related_bool.
  Qed.
*)
