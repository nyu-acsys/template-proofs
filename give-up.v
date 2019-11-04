Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "All".
Require Export flows.

(* ---------- The program ---------- *)

Inductive dOp := memberOp | insertOp | deleteOp.

Variable findNext : val.
Variable inRange : val.
Variable decisiveOp : (dOp → val).
Variable searchStrSpec : (dOp → val).
Variable lockLoc : node → loc.
Variable getLockLoc : val.


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

(* ---------- Flow interface set-up specific to this proof ---------- *)

  Variable root : node.
  Variable hrep : node → flowintUR → iProp.
  Parameter hrep_timeless_proof : ∀ n I, Timeless (hrep n I).
  Instance hrep_timeless n I : Timeless (hrep n I).
  Proof. apply hrep_timeless_proof. Qed.
  Parameter hrep_fp : ∀ n I_n, hrep n I_n -∗ ⌜Nds I_n = {[n]}⌝.

  Hypothesis globalint_root_fp: ∀ I, globalint I → root ∈ Nds I.

 (* Hypothesis globalint_fpo : ∀ I, globalint I → ∀ n:node, outf I n = 0.
                                           Can't figure out (outf I n). Also is it appropriate?  *)

  Hypothesis contextualLeq_impl_globalint :
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

  Axiom Ψ_keyset_theorem : ∀ (dop: dOp) (k: key) (n: node) (I_n I_n' I I': flowintUR) (res: bool),
      ⌜globalint I⌝ ∗ ⌜Nds I_n = {[n]}⌝ ∗ ⌜in_inset k I_n n⌝ ∗ ⌜not_in_outset k I_n n⌝
      ∗ ⌜(∃ (I_o: flowintUR), I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o)⌝ ∗ ✓ I ∗ ✓ I'
      -∗ Ψ dop k (cont I_n) (cont I_n') res -∗ ⌜Ψ dop k (cont I) (cont I') res⌝.


  (* ---------- Helper functions specs - proved for each implementation in GRASShopper ---------- *)

  Parameter getLockLoc_spec : ∀ (n: node),
      (<<< True >>>
           getLockLoc #n @ ⊤
       <<< ∃ l:loc, ⌜lockLoc n = l⌝, RET #l >>>)%I.

  Parameter inRange_spec : ∀ (n: node) (I_n : flowintUR) (k: key),
      (<<< hrep n I_n >>>
           inRange #n #k @ ⊤
       <<< ∃ b: bool, hrep n I_n
                    ∗ (match b with true => ⌜in_inset k I_n n⌝ |
                               false => ⌜True⌝ end),
         RET #b >>>)%I.

  Parameter findNext_spec : ∀ (n: node) (I_n : flowintUR) (k: key),
      (<<< hrep n I_n >>>
           findNext #n #k @ ⊤
       <<< ∃ (b: bool) (n': node), hrep n I_n
                                 ∗ (match b with true => ⌜in_edgeset k I_n n n'⌝ |
                                            false => ⌜not_in_outset k I_n n⌝ end),
         RET (match b with true => (SOMEV #n') |
                      false => NONEV end) >>>)%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: node) (k: key),
      (<<< ∀ (I_n: flowintUR), hrep n I_n ∗ ⌜in_inset k I_n n⌝ 
                    ∗ ⌜not_in_outset k I_n n⌝ ∗ ⌜Nds I_n = {[n]}⌝ >>>
           decisiveOp dop #n #k @ ⊤
       <<< ∃ (b: bool) (I_n': flowintUR) (res: bool),
           match b with false => hrep n I_n |
                   true => hrep n I_n' ∗ Ψ dop k (cont I_n) (cont I_n') res
         ∗ ⌜contextualLeq I_n I_n'⌝ ∗ ⌜Nds I_n' = {[n]}⌝ end,
           RET (match b with false => NONEV |
                        true => (SOMEV #res) end) >>>)%I.

  (* ---------- The invariant ---------- *)

  Definition dictN : namespace := N .@ "dict".

  (* Sid: I think we don't need γ_c anymore. *)
  Definition main_searchStr (γ: gname) (γ_fp: gname) (γ_c: gname) I Ns C
    : iProp :=
    (own γ_c C ∗ ⌜C = cont I⌝
        ∗ own γ (● I) ∗ ⌜globalint I⌝
        ∗ ([∗ set] n ∈ (Nds I), (∃ b: bool,
           (lockLoc n) ↦ #b
           ∗ if b then True
             else (∃ (In: flowintUR), own γ (◯ In) ∗ hrep n In ∗ ⌜Nds In = {[n]}⌝)))
        ∗ own γ_fp (● Ns) ∗ ⌜Ns = (Nds I)⌝
    )%I.

  Definition is_searchStr γ γ_fp γ_c C := (∃ I Ns, (main_searchStr γ γ_fp γ_c I Ns C))%I.

  Instance main_searchStr_timeless γ γ_fp γ_c I N C :
    Timeless (main_searchStr γ γ_fp γ_c I N C).
  Proof.
    rewrite /main_searchStr. repeat apply bi.sep_timeless; try apply _.
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
    destruct H1. destruct H2. apply gset_included in H2.
    apply to_agree_inj in H1. set_solver.
  Qed.

  Lemma auth_own_incl γ (x y: flowintUR) : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H. destruct H. destruct H0 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y = y) as Hy.
    { rewrite /(⋅) /=. rewrite left_id. done. }
    rewrite Hy in Hb. rewrite <- Ha in Hb. done.
  Qed.

(*  Lemma auth_agree γ xs ys :
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
*)

  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P I I_n I_n' x⌝ ∧ own γ x -∗
                       ∃ I', ⌜contextualLeq I I'⌝ ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
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
        rewrite /(cmra_op (optionR (prodR fracR (agreeR flowintUR))) (Some (1%Qp, to_agree I')) (None)) /=.
        reflexivity. }
      assert (● I' ⋅ ◯ I_n' = (Auth (Some (1%Qp, to_agree(I'))) (I_n'))) as Hd.
      { rewrite /(● I') /= /(◯ I_n') /=. rewrite /(⋅) /=.
        rewrite /(cmra_op (authR flowintUR) (Auth (Some (1%Qp, to_agree I')) ε) (Auth None I_n')) /=.
        rewrite /auth_op /=. rewrite HeIn. rewrite Hs. reflexivity. }
      iEval (rewrite Hd). iEval (rewrite <- H'). done.
  Qed.

  Lemma inv_impl_fp n Ns γ γ_fp γ_c I Ns' C:
    main_searchStr γ γ_fp γ_c I Ns' C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗ ⌜n ∈ Nds I⌝.
  Proof.
    iIntros "(HInv & HNs & %)".
    iDestruct "HInv" as "(? & ? & ? & ? & HIns & HNs' & %)".
    iPoseProof (auth_set_incl with "[$HNs $HNs']") as "%".
    iPureIntro. set_solver.
  Qed.                                       (* Made Proof using Type* *)

  (* ---------- Lock module proofs ---------- *)

  (* Sid: shouldn't the postcondition also have is_searchStr? *)
  Lemma lockNode_spec (γ: gname) (γ_fp: gname) (γ_c: gname) (n: node) (Ns: gset node):
    <<< ∀ C, is_searchStr γ γ_fp γ_c C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ >>>
        lockNode #n    @ ⊤
    <<< ∃ (I_n: flowintUR), own γ (◯ I_n) ∗ hrep n I_n ∗ ⌜Nds I_n = {[n]}⌝, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind(getLockLoc _)%E.
    awp_apply getLockLoc_spec.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C) "(Hst & Hfp & Hin)".
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". iIntros "_". eauto 4 with iFrame.
    iIntros (l) "#Hl". iModIntro. iSplitL. iFrame. iIntros "AU".
    iModIntro. wp_let. wp_bind (CmpXchg _ _ _)%E.
    iMod "AU" as (C') "[(Hst & Hfp & Hin) HAU]".
    iDestruct "Hst" as (I N0) "(H1 & H2 & H3 & H4 & H5 & H6 & H7)". iDestruct "Hl" as %Hl.
    iAssert (⌜n ∈ Nds I⌝)%I with "[Hfp Hin H6 H7]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns N0) with "[$]") as "%".
      iDestruct "H7" as %H7. iDestruct "Hin" as %Hin. iEval (rewrite <-H7). iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I) n); last by eauto.
    iDestruct "H5" as "[ho hoho]".
    iDestruct "ho" as (b) "[Hlock Hlock']". iEval (rewrite Hl) in "Hlock". destruct b.
      - wp_cmpxchg_fail. iDestruct "HAU" as "[HAU _]".
        iMod ("HAU" with "[H1 H2 H3 H4 Hlock Hlock' hoho H6 H7 Hfp Hin]") as "H".
        iFrame. iExists I, N0. iFrame. iApply "hoho". iExists true.
        iEval (rewrite <-Hl) in "Hlock". iFrame.
        iModIntro. wp_pures. iApply "IH". done.
      - wp_cmpxchg_suc. iDestruct "HAU" as "[_ HAU]".
        iDestruct "Hlock'" as (In) "HPost".
        iMod ("HAU" with "HPost") as "HΦ".
        iModIntro. wp_pures. done.
  Qed.

  (* Shouldn't the pre have own γ (◯ I_n) ∗ hrep n I_n ∗ ⌜Nds I_n = {[n]}⌝?
     And the post should also have is_searchStr? *)
  Lemma unlockNode_spec (γ: gname) (γ_fp: gname) (γ_c: gname) (n: node) (Ns: gset node) :
          <<< ∀ C, is_searchStr γ γ_fp γ_c C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝  >>>
                unlockNode #n    @ ⊤
          <<< is_searchStr γ γ_fp γ_c C, RET #() >>>.
  Proof.
  Admitted.

  Lemma traverse_spec (γ γ_fp γ_c: gname) (k: key) (n: node):
    <<< ∀ C, ∃ (Ns: gsetUR node), is_searchStr γ γ_fp γ_c C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ ⌜root ∈ Ns⌝ >>>
                traverse root #n #k
                    @ ⊤
          <<< ∃ (n': node) (Ns': gsetUR node) (I_n': flowintUR), is_searchStr γ γ_fp γ_c C ∗ ⌜n' ∈ Ns'⌝ 
                  ∗ own γ_fp (◯ Ns') ∗ own γ (◯ I_n') ∗ hrep n' I_n' ∗ ⌜Nds I_n' = {[n']}⌝
                  ∗ ⌜in_inset k I_n' n'⌝ ∗ ⌜not_in_outset k I_n' n'⌝, RET #n' >>>.
  Proof.
  Admitted.

  Lemma ghost_update_root_fp γ γ_fp γ_c C:
          is_searchStr γ γ_fp γ_c C ==∗
                 ∃ (Ns: gsetUR node), is_searchStr γ γ_fp γ_c C ∗ own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝.
  Proof.
    iIntros "Hst". iModIntro.
    iDestruct "Hst" as (I Ns) "(H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iExists Ns.
  Admitted.


  Theorem searchStrOp_spec (γ γ_fp γ_c: gname) (dop: dOp) (k: key):
      <<< ∀ (C: gset key), is_searchStr γ γ_fp γ_c C >>>
            searchStrOp dop root #k
                  @ ⊤
      <<< ∃ (C': gset key) (res: bool), is_searchStr γ γ_fp γ_c C' ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    wp_bind (traverse _ _ _)%E.
    awp_apply (traverse_spec γ γ_fp γ_c k root).
    rewrite /atomic_acc /=. iMod "AU" as (C0) "[H [H' _]]".
    iDestruct (ghost_update_root_fp γ γ_fp γ_c C0 with "[H]") as ">Ho".
    done. iDestruct "Ho" as (Ns) "(Hst & #Hfp & #HinR)".
    iModIntro. iExists C0. iSplitL "Hst Hfp HinR". iExists Ns.
    eauto with iFrame. iSplit. iIntros "Hst".
    iDestruct "Hst" as (Ns') "(Hst & _)". iMod ("H'" with "Hst") as "AU".
    iModIntro. done. iIntros (n Ns' In) "(Hst & #HinN & #Hfp' & HIn & HrepN & #HNdsn & #Hinset & #Hnotout)".
    iMod ("H'" with "Hst") as "AU".
    iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    awp_apply (decisiveOp_spec dop n k).
    iAssert (hrep n In ∗ ⌜in_inset k In n⌝ ∗ ⌜not_in_outset k In n⌝ ∗ ⌜Nds In = {[n]}⌝)%I
        with "[HrepN]" as "Haac".
    { eauto with iFrame. } iAaccIntro with "Haac". iIntros "(Hrep & _)".
    iModIntro. eauto with iFrame. iIntros (b In' res). iIntros "Hb". destruct b.
    - iDestruct "Hb" as "(Hrep & HΨ & #Hcon & #HNds')".
      iModIntro. wp_pures. wp_bind(unlockNode _)%E.
      iDestruct "HΨ" as "#HΨ".
      awp_apply (unlockNode_spec γ γ_fp γ_c n Ns').
      iApply (aacc_aupd_commit with "AU"); first done.
      iIntros (C1) "Hst". iAssert (is_searchStr γ γ_fp γ_c C1 ∗ own γ_fp (◯ Ns') ∗ ⌜n ∈ Ns'⌝)%I
      with "[Hst]" as "Haac". eauto with iFrame. iAaccIntro with "Haac".
      iIntros "(Hst & _)". iModIntro. iSplitL "Hst"; try done. iIntros "AU".
      iModIntro. iFrame "HIn AU Hrep". iIntros "Hst".
      iDestruct "Hst" as (I Nd) "(H3 & H4 & H5 & H6 & H7 & H8 & H9)".
      iDestruct "H4" as %H4. iDestruct "H6" as %H6. iEval (rewrite H4) in "H3".
      iPoseProof (auth_own_incl with "[$H5 $HIn]") as (I2)"%".
      iPoseProof ((own_valid γ (● I)) with "H5") as "%". iDestruct "Hcon" as %Hcon.
      iMod (own_updateP (flowint_update_P I In In') γ (● I ⋅ ◯ In) with "[H5 HIn]") as (?) "H0".
      { apply (flowint_update I In In'). done. } { rewrite own_op. iFrame. }
      iPoseProof ((flowint_update_result γ I In In') with "H0") as (I') "(% & % & HIIn)".
      iAssert (own γ (● I') ∗ own γ (◯ In'))%I with "[HIIn]" as "(HI' & HIn')". { by rewrite own_op. }
      iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
      iPoseProof ((Ψ_keyset_theorem dop k n In In' I I' res) with "[HNdsn Hinset Hnotout] [HΨ]") as "HΨI".
      { repeat iSplitL; try done; iPureIntro; apply auth_auth_valid; done. } { done. }
      iMod (own_update γ_c (cont I) (cont I') with "[H3]") as "H3'".
      { apply (gset_update (cont I) (cont I')). } done.
      iModIntro. iExists (cont I'), res. iSplitL. iEval (rewrite H4). iFrame.
      iExists I', Nd. assert (globalint I') as HI'.
      { apply (contextualLeq_impl_globalint I I'). done. done. }
      assert (Nds I = Nds I') as HH. { apply (contextualLeq_impl_fp I I'). done. }
      iEval (rewrite HH) in "H7 H9". iFrame "∗ % #". iPureIntro. reflexivity.
      iIntros "HΦ". iModIntro. wp_pures. done.
    - iModIntro. wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec γ γ_fp γ_c n Ns').
      iApply (aacc_aupd_abort with "AU"); first done.
      iIntros (C2) "Hst". iAssert (is_searchStr γ γ_fp γ_c C2 ∗ own γ_fp (◯ Ns') ∗ ⌜n ∈ Ns'⌝)%I
      with "[Hst]" as "Haac". eauto with iFrame. iAaccIntro with "Haac".
      iIntros "(Hst & _)". iModIntro. iFrame "Hst". iIntros "AU". eauto with iFrame.
      iIntros "Hst". iModIntro. iFrame "Hst". iIntros "AU". iModIntro.
      wp_pures. iApply "IH". done.
  Qed.


  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)

  Lemma unlockNode_spec (γ: gname) (γ_fp: gname) (γ_c: gname) (n: node) (Ns: gset node) :
          <<< ∀ C, is_searchStr γ γ_fp γ_c C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗  >>>
                unlockNode #n    @ ⊤ ∖ ↑dictN
          <<< True, RET #() >>>.
  Proof.
    iIntros "#Hinv (Hfp & Hin)" (Φ) "AU". wp_lam. awp_apply getLockLoc_spec.
    iAssert (True)%I as "Ht". done.
    iAaccIntro with "Ht". eauto 4 with iFrame.
    iIntros (l) "Hl". iDestruct "Hl" as %Hl. iModIntro. wp_let. iInv dictN as ">HI".
    iDestruct "HI" as (I' N' C') "(H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iAssert (⌜n ∈ Nds I'⌝)%I with "[Hfp Hin H6 H7]" as "%".
    { (*iEval (rewrite <- H1).*) iPoseProof ((auth_set_incl γ_fp Ns N') with "[$]") as "%".
      iDestruct "H7" as %H7. iDestruct "Hin" as %Hl2. iEval (rewrite <-H7). iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I') n); last by eauto.
    iDestruct "H5" as "[ho hoho]".
    iDestruct "ho" as (b) "[Hlock Hlock']".
    iEval (rewrite Hl) in "Hlock".
    iMod "AU" as (I_n) "[Hr [_ Hcl]]". wp_store.
    iAssert (True)%I as "Ht". done.
    iMod ("Hcl" with "Ht") as "HΦ".
    iModIntro. iModIntro. iSplitR "HΦ". iNext. iExists I', N', C'. rewrite /main_inv. iFrame.
    iApply "hoho". iExists false. iEval (rewrite <-Hl) in "Hlock". iFrame. iExists I_n.
    iDestruct "Hr" as "(? & ? & ?)". eauto with iFrame. done.
  Qed.


  Lemma ghost_update_step γ γ_fp γ_c (n n': node) (k:key) (Ns: gset node) (I_n: flowintUR):
          is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ own γ (◯ I_n) ∗ ⌜Nds I_n = {[n]}⌝
       ∗ ⌜in_inset k I_n n⌝ ∗ ⌜in_edgeset k I_n n n'⌝
              ={ ⊤ }=∗ ∃ (Ns': gset node), own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝
                                                        ∗ own γ (◯ I_n) ∗ ⌜root ∈ Ns'⌝.
  Proof.
    iIntros "#Hinv (HNs & % & HIn & % & % & %)".
    iInv dictN as ">HInv" "Hclose".
    iDestruct "HInv" as (I Ns' C) "HInv".
    iPoseProof (inv_impl_fp n Ns with "[$HInv $HNs //]") as "%".
    iDestruct "HInv" as "(? & % & HI & % & ? & HNs' & %)".
    iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
    iPoseProof (own_valid with "HI") as "%".
    iAssert (⌜n' ∈ Nds I⌝)%I as "%".
    { iPureIntro.
      assert (n' ∈ Nds I2).
      { apply (flowint_step I I_n _ k n). done. apply auth_auth_valid. done.
        replace (Nds I_n). set_solver. done. done. }
      apply flowint_comp_fp in H7. set_solver.
    }
    iMod (own_update γ_fp (● Ns') (● Ns' ⋅ ◯ Ns') with "HNs'") as "HNs'".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "HNs'" as "(HNs0 & HNs')".
    iMod ("Hclose" with "[-HNs' HIn]"). { iNext. iExists I, Ns', C.  iFrame "# % ∗". }
    iModIntro. iExists Ns'. iFrame "# % ∗".
    rewrite <-H6 in H9. iSplit. iPureIntro. done.
    iPureIntro. rewrite H6. apply globalint_root_fp. done.
  Qed.

  (* ---------- Refinement proofs ---------- *)

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
               iModIntro. wp_pures.
               iDestruct (ghost_update_step γ γ_fp γ_c n n' k Ns In
                                  with "[HInv] [Hfp Hin HInt Hdom H1 H2]") as ">hoho".
               { done. } { eauto with iFrame. } iDestruct "hoho" as (Ns') "(#Hfp' & #Hin' & HInt & #Hr')".
               awp_apply (unlockNode_spec γ γ_fp γ_c n Ns).
               { done. } { eauto with iFrame. }
               iAssert (hrep n In ∗ own γ (◯ In) ∗ ⌜Nds In = {[n]}⌝)%I with "[Hrep HInt Hdom]" as "Haac".
               { eauto with iFrame. }
               iAaccIntro with "Haac". { iIntros "(Hrep & HInt & HNds)". iModIntro. iFrame. } iIntros "Ht".
               iModIntro. wp_pures. iSpecialize ("IH" $! n' Ns'). iApply "IH". eauto with iFrame. done.
            * (* findNext fails *)
              iMod "AU" as "[Ht [_ HClose]]". iSpecialize ("HClose" $! n Ns In).
              iMod ("HClose" with "[Hfp HInt Hrep Hdom H1 H2]") as "HΦ". eauto with iFrame.
              iModIntro. wp_pures. done.
        + (*inRange fails *)
          wp_if. awp_apply (unlockNode_spec γ γ_fp γ_c n Ns). done. eauto with iFrame.
          iAssert (hrep n In ∗ own γ (◯ In) ∗ ⌜Nds In = {[n]}⌝)%I with "[Hrep HInt Hdom]" as "Haac".
          { eauto with iFrame. }
          iAaccIntro with "Haac". { iIntros "(Hrep & HInt & HNds)". iModIntro. iFrame. }
          iIntros. iModIntro. wp_pures. iApply "IH". eauto with iFrame. done.
  Qed.

  Theorem searchStrOp_spec (γ γ_fp γ_c: gname) (dop: dOp) (k: key):
          ∀ (Ns: gsetUR node),
          is_dict γ γ_fp γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜ root ∈ Ns ⌝ -∗
      <<< ∀ (C: gset key), own γ_c (◯ (Some (Excl C))) >>>
            (searchStrOp dop root) #k
                  @ ⊤∖↑dictN
      <<< ∃ (C': gset key) (res: bool), own γ_c (◯ (Some (Excl C'))) ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros (Ns). iIntros "#HInv H" (Φ) "AU". iLöb as "IH" forall (Ns).
    wp_lam. wp_bind(traverse _ _ _)%E. iDestruct "H" as "#(H1 & H2)".
    awp_apply (traverse_spec γ γ_fp γ_c). done. eauto with iFrame.
    iAssert (True)%I as "Ht". done. iAaccIntro with "Ht". eauto with iFrame.
    iIntros (n Ns' In) "(#Hin & #Hfp & HInt & Hrep & #HNds & #Hinset & #Hout)". iModIntro. wp_let.
    wp_bind(decisiveOp dop _ _)%E. awp_apply (decisiveOp_spec dop In n k).
    iAssert (hrep n In ∗ ⌜in_inset k In n⌝ ∗ ⌜not_in_outset k In n⌝ ∗ ⌜Nds In = {[n]}⌝)%I
                                      with "[Hrep Hinset Hout HNds]" as "Haac".
    { eauto with iFrame. }
    iAaccIntro with "Haac". { iIntros "(Hrep & ?)". iModIntro. iFrame. }
    iIntros (b In' result) "Hb". destruct b; last first.
    - iModIntro. wp_pures. awp_apply (unlockNode_spec γ γ_fp γ_c n Ns'). done. iSplit. done. iApply "Hin".
      iAssert (hrep n In ∗ own γ (◯ In) ∗ ⌜Nds In = {[n]}⌝)%I with "[Hb HInt HNds]" as "Haac".
      { eauto with iFrame. }
      iAaccIntro with "Haac". iIntros "(Hb & HInt & _)". eauto with iFrame. iIntros. iModIntro.
      wp_pures. iApply "IH". iSplit. iApply "H1". done. done.
    - iInv dictN as ">HI". iDestruct "HI" as (I Nd Cs) "(H3 & H4 & H5 & H6 & H7 & H8 & H9)".
      iDestruct "H4" as %H4. iDestruct "H6" as %H6. iEval (rewrite H4) in "H3".
      iPoseProof (auth_own_incl with "[$H5 $HInt]") as (I2)"%".
      iPoseProof ((own_valid γ (● I)) with "H5") as "%".
      iDestruct "Hb" as "(Hrep & #Hdop & Hctx & HNds')". iDestruct "Hctx" as %Hctx.
      iMod (own_updateP (flowint_update_P I In In') γ (● I ⋅ ◯ In) with "[H5 HInt]") as (?) "H0".
      { apply (flowint_update I In In'). done. } { rewrite own_op. iFrame. }
      iPoseProof ((flowint_update_result γ I In In') with "H0") as (I') "(% & % & HIIn)".
      iAssert (own γ (● I') ∗ own γ (◯ In'))%I with "[HIIn]" as "(HI' & HIn')". { by rewrite own_op. }
      iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
      iPoseProof ((Ψ_keyset_theorem dop k n In In' I I' result) with "[HNds Hinset Hout] [Hdop]") as "HΨI".
      { repeat iSplitL; try done; iPureIntro; apply auth_auth_valid; done. } { done. }
      iMod "AU" as (C) "[hoho [_ Hcl]]".
      iDestruct (auth_agree with "H3 hoho") as %Hauth.
      iMod (auth_update γ_c (cont I') with "H3 hoho") as "[H3 hoho]".
      iSpecialize ("Hcl" $! (cont I') result). iEval (rewrite <-Hauth) in "Hcl".
      iMod ("Hcl" with "[hoho HΨI]") as "HΦ". eauto with iFrame.
      iModIntro. iSplitR "Hrep HIn' HNds' HΦ".
        + iNext. iExists I', Nd, (cont I').
          unfold main_inv. assert (globalint I') as HI'.
          { apply (contextualLeq_impl_globalint I I'). done. done. }
          assert (Nds I = Nds I') as HH. { apply (contextualLeq_impl_fp I I'). done. }
          iEval (rewrite HH) in "H7 H9". iFrame "∗ % #". iPureIntro. reflexivity.
        + iModIntro. wp_pures. wp_bind (unlockNode _)%E.
          iDestruct "HΦ" as "_".
          awp_apply (unlockNode_spec γ γ_fp γ_c n Ns'). done.
          iSplitL. iApply "Hfp". iApply "Hin".
          iAssert (Φ #result)%I as "HΦ". { admit. }
          iAssert (hrep n In' ∗ own γ (◯ In') ∗ ⌜Nds In' = {[n]}⌝)%I with "[Hrep HIn' HNds']" as "Haac".
          { eauto with iFrame. }
          iAaccIntro with "Haac". iIntros "(Hrep & HInt & HNds')". iModIntro. eauto with iFrame.
          iIntros. iModIntro. wp_pures. done.
  Admitted.
