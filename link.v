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

Definition traverse : val :=
  rec: "tr" "n" "k" :=
    lockNode "n";;
    match: (findNext "n" "k") with
      NONE => "n"
    | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
    end.

(* TODO make this always succeed - needs decisiveOp to return more than one node. *)
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
Class contentG Σ := ContentG { content_inG :> inG Σ (gsetR key) }.
Definition contentΣ : gFunctors := #[GFunctor (gsetR key)].

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
  (* TODO: instead have hrep n I_n -∗ n ↦ _ and use
     iDestruct (mapsto_valid_2 with "H1 H2") as %[]
     to say n ↦ _ ∗ n ↦ _ -∗ False *)
  Parameter hrep_sep_star: ∀ n I_n I_n', hrep n I_n ∗ hrep n I_n' -∗ False.

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
      -∗ Ψ dop k (cont I_n) (cont I_n') res -∗ ⌜Ψ dop k (cont I) (cont I') res⌝.


  (* ---------- Helper functions specs - proved for each implementation in GRASShopper ---------- *)

  Parameter getLockLoc_spec : ∀ (n: node),
    ({{{ True }}}
      getLockLoc #n
    {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.


  Parameter findNext_spec : ∀ (n: node) (I_n : flowintUR) (k: key),
    ({{{ hrep n I_n }}}
      findNext #n #k
    {{{ (b: bool) (n': node), 
      RET (match b with true => (SOMEV #n') | false => NONEV end); 
      hrep n I_n ∗ (match b with true => ⌜in_outset k I_n n n'⌝ |
                                false => ⌜not_in_outset k I_n n⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: node) (k: key) (I_n: flowintUR),
    ({{{ hrep n I_n ∗ ⌜in_inset k I_n n⌝
        ∗ ⌜not_in_outset k I_n n⌝ ∗ ⌜Nds I_n = {[n]}⌝ }}}
      decisiveOp dop #n #k
    {{{ (b: bool) (I_n': flowintUR) (res: bool),
      RET (match b with false => NONEV | true => (SOMEV #res) end);
      match b with false => hrep n I_n |
                    true => hrep n I_n' ∗ Ψ dop k (cont I_n) (cont I_n') res
                            ∗ ⌜contextualLeq I_n I_n'⌝ ∗ ⌜Nds I_n' = {[n]}⌝ 
                            ∗ ⌜inreach I_n n = inreach I_n' n⌝ end }}})%I.

  (* ---------- The invariant ---------- *)

  Definition searchStr γ γ_fp γ_inr γ_c C : iProp :=
    (∃ I N,
      own γ_c C ∗ ⌜C = cont I⌝
      ∗ own γ (● I) ∗ ⌜globalint I⌝
      ∗ ([∗ set] n ∈ (Nds I), (∃ b: bool,
          (lockLoc n) ↦ #b
          ∗ if b then True
            else (∃ (In: flowintUR), own γ (◯ In) ∗ hrep n In ∗ ⌜Nds In = {[n]}⌝)))
      ∗ own γ_fp (● N) ∗ ⌜N = (Nds I)⌝
      ∗ ([∗ set] n ∈ (Nds I), (∃ (Inr_n: gsetUR key),
          own (γ_inr n) (● Inr_n) ∗ ⌜Inr_n = inreach I n⌝))
    )%I.


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


  (* ---------- Lock module proofs ---------- *)

  Lemma lockNode_spec (n: node):
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

  Lemma unlockNode_spec (n: node) :
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


  (* ---------- Refinement proofs ---------- *)

  Lemma own_fp_Nds γ_fp I Ns Ns' n:
    own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ own γ_fp (● Ns') ∗ ⌜Ns' = (Nds I)⌝ -∗ ⌜n ∈ Nds I⌝.
  Proof.
    iIntros "(HNs & % & Hns' & %)".
    iPoseProof ((auth_set_incl γ_fp Ns Ns') with "[$]") as "%".
    iPureIntro. set_solver.
  Qed.
  
  Lemma traverse_spec γ γ_fp γ_c γ_inr (k: key) (n: node) Ns Inr:
    own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝  ∗ own (γ_inr n) (◯ Inr) ∗ ⌜k ∈ Inr⌝ -∗
    <<< ∀ C, searchStr γ γ_fp γ_inr γ_c C >>>
      traverse #n #k @ ⊤
    <<< ∃ (n': node) (Ns': gsetUR node) (Inr': gsetUR key) (I_n': flowintUR),
      searchStr γ γ_fp γ_inr γ_c C ∗ hrep n' I_n' ∗ own γ (◯ I_n')
      ∗ own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ ∗ own (γ_inr n') (◯ Inr') ∗ ⌜k ∈ Inr'⌝
      ∗ ⌜not_in_outset k I_n' n'⌝ , RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns Inr). iIntros "(#Hfp & #Hnfp & #Hinr & #Hkinr)".
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n).
    (* Execute lockNode *)
    iApply (aacc_aupd_abort with "AU"); first done. (* Open AU *)
    iIntros (C0) "Hst".
    iDestruct "Hst" as (I Ns0)"(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)".
    iPoseProof ((own_fp_Nds γ_fp I Ns Ns0 n)%I with "[$]") as "%".
    rewrite (big_sepS_elem_of_acc _ (Nds I) n); last by eauto.
    iDestruct "H5" as "[Hb H5]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock".
    { iIntros "H". iModIntro. iSplitL.
    iExists I, Ns0. iFrame "∗ % #". iApply "H5". iExists b.
    iFrame. eauto with iFrame. }
    iIntros "(Hloc & ?)".
    destruct b. { iExFalso. done. } iModIntro.
    iSplitR "Hb". iExists I, Ns0. iFrame "∗ % #". iApply "H5". iExists true.
    iFrame. iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (In) "(HIn & Hrep & #HNds)". iDestruct "HNds" as %HNds.
    (* Execute findNext *)
    wp_bind (findNext _ _)%E.
    wp_apply ((findNext_spec n In k) with "Hrep").
    iIntros (b n') "(Hrep & Hbb)". destruct b.
    - (* findNext returns Some n' *)
      wp_pures. awp_apply (unlockNode_spec n).
      (* Execute unlockNode *)
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
      iDestruct "Hst" as (I1 Ns1)"(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)".
      iPoseProof ((own_fp_Nds γ_fp I1 Ns Ns1 n)%I with "[$]") as "%".
      rewrite (big_sepS_elem_of_acc _ (Nds I1) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last.
      { (* Impossible case: n ↦ _ in local & shared state *)
        iDestruct "Hl" as (In') "(_ & Hrep' & _)".
        iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf.
        { iApply (hrep_sep_star n In In'). iFrame. }
        exfalso. done. }
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro. iSplitR "HIn Hrep Hbb".
        iExists I1, Ns1. iFrame "∗ % #". iApply "H5". iExists true.
        iFrame. iIntros "AU". iModIntro. iFrame. }
      iIntros "Hlock". iDestruct "H7" as %H7.
      iDestruct "Hbb" as %Hbb. iDestruct "H4" as %H4.
      iAssert (⌜n' ∈ Ns1⌝ ∗ ⌜root ∈ Ns1⌝ ∗ own γ (● I1)
                ∗ own γ_fp (● Ns1) ∗ own γ (◯ In))%I
        with "[HIn H3 H6]" as "Hghost".
      { iPoseProof (auth_set_incl with "[$Hfp $H6]") as "%".
        iPoseProof (auth_own_incl with "[$H3 $HIn]") as (I2)"%".
        iPoseProof (own_valid with "H3") as "%".
        iAssert (⌜n' ∈ Nds I1⌝)%I as "%".
        { iPureIntro. assert (n' ∈ Nds I2).
          { apply (flowint_step I1 In _ k n). done. 
            apply auth_auth_valid. done.
            replace (Nds In). set_solver. done. done. }
          apply flowint_comp_fp in H2. set_solver. }
        iFrame. iPureIntro. replace Ns1. auto. }
      iDestruct "Hghost" as "(% & % & HAIn & HAfp & HIn)".
      (* Snapshot the FP *)
      iMod (own_update γ_fp (● Ns1) (● Ns1 ⋅ ◯ Ns1) with "HAfp") as "HNs".
      apply auth_update_core_id. apply gset_core_id. done.
      iDestruct "HNs" as "(HAfp & #Hfp1)".
      (* Snapshot the inreach of n' *)
      iAssert (∃ Inr', own (γ_inr n') (◯ Inr') ∗ ⌜k ∈ Inr'⌝)%I as (Inr') "(#Hinr' & %)".
      { (* Need to unroll H8 on n' and take snapshot of its inreach *)
        (* Also need to use flowint_inreach_step to get k ∈ Inr' *)
        admit. }
      iModIntro. iSplitL. iExists I1, Ns1.
      iFrame "∗ % #". iApply "H5". iExists false. iFrame. iExists In. eauto with iFrame.
      iIntros "AU". iModIntro. wp_pures. iApply "IH". iFrame "∗ % #". done.
    - (* findNext returns None *)
      iApply fupd_wp. iMod "AU" as (C) "[Hst [_ Hclose]]". (* Commit the AU *)
      iSpecialize ("Hclose" $! n Ns Inr In).
      iMod ("Hclose" with "[$]") as "HΦ".
      iModIntro. wp_match. done.
  Admitted.

  Lemma searchStrOp_spec γ γ_fp γ_c γ_inr (dop:dOp) (k: key):
    <<< ∀ (C: gset key), searchStr γ γ_fp γ_inr γ_c C >>>
      searchStrOp dop root #k @ ⊤
    <<< ∃ (C': gset key) (res: bool), searchStr γ γ_fp γ_inr γ_c C'
        ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    (* Open AU to get precondition of traverse *)
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I Ns0) "(H1 & H2 & H3 & % & H5 & H6 & % & H8)".
    assert (root ∈ Ns0)%I as Hroot. { replace Ns0. apply globalint_root_fp. done. }
    iMod (own_update γ_fp (● Ns0) (● Ns0 ⋅ ◯ Ns0) with "H6") as "HNs".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "HNs" as "(HAfp & #Hfp0)".
    iAssert (∃ Inr, own (γ_inr root) (◯ Inr) ∗ ⌜k ∈ Inr⌝)%I as (Inr) "(#Hinr & %)".
    { (* Unroll and take snapshot, use globalint_root_inr. *) admit. }
    iMod ("HAU" with "[$H1 H2 H3 H5 H8 HAfp] ") as "AU".
    { iExists I, Ns0. iFrame "∗ % #". }
    iModIntro. wp_pures.
    (* Execute traverse *)
    wp_bind (traverse _ _)%E.
    awp_apply (traverse_spec γ γ_fp γ_c γ_inr k root Ns0). eauto with iFrame.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "Hst". iAaccIntro with "Hst"; first by eauto with iFrame.
    iIntros (n Ns1 Inr1 In)
            "(Hst & Hrepn & HIn & #Hfp1 & % & #Hinr1 & % & #Hnotout)".
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures.
    (* Execute decisiveOp *)
    wp_bind (decisiveOp _ _ _)%E.
    wp_apply ((decisiveOp_spec dop n k In) with "[Hrepn]"). eauto with iFrame.
    iIntros (b In' res). iIntros "Hb". destruct b.
    - iDestruct "Hb" as "(Hrep & #HΨ & #Hcon & #HNds')".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I1 Ns2)"(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)". 
      iAssert (⌜n ∈ Nds I1⌝)%I with "[Hfp1 Hinn H6 H7]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns1 Ns2) with "[$]") as "%".
        iDestruct "H7" as %H7. iDestruct "Hinn" as %Hinn. iEval (rewrite <-H7).
        iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (Nds I1) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In'') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (hrep_sep_star n In' In''). 
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "HIn Hrep".
      iExists I1, Ns2. iFrame "∗ % #". iApply "H5". iExists true. iFrame. eauto with iFrame. }
      iIntros "Hlock". iDestruct "H4" as %H4. iDestruct "H7" as %H7.
      iDestruct "H2" as %H2. iEval (rewrite H2) in "H1".
      iPoseProof (auth_own_incl with "[$H3 $HIn]") as (I2)"%".
      iPoseProof ((own_valid γ (● I1)) with "H3") as "%". iDestruct "Hcon" as %Hcon.
      iMod (own_updateP (flowint_update_P I1 In In') γ (● I1 ⋅ ◯ In) with "[H3 HIn]") as (?) "H0".
      { apply (flowint_update I1 In In'). done. } { rewrite own_op. iFrame. }
      iPoseProof ((flowint_update_result γ I1 In In') with "H0") as (I1') "(% & % & HIIn)".
      iAssert (own γ (● I1') ∗ own γ (◯ In'))%I with "[HIIn]" as "(HI' & HIn')". { by rewrite own_op. }
      iPoseProof ((own_valid γ (● I1')) with "HI'") as "%".
      iPoseProof ((Ψ_keyset_theorem dop k n In In' I1 I1' res) with "[HNdsn Hinset Hnotout] [HΨ]") as "HΨI".
      { repeat iSplitL; try done; iPureIntro; apply auth_auth_valid; done. } { done. }
      iMod (own_update γ_c (cont I1) (cont I1') with "[H1]") as "H1'".
      { apply (gset_update (cont I1) (cont I1')). } done.
      iModIntro. iExists (cont I1'), res. iSplitL. iSplitR "HΨI".
      { iExists I1', Ns2. assert (globalint I1') as HI'.
      { apply (contextualLeq_impl_globalint I1 I1'). done. done. }
      assert (Nds I1 = Nds I1') as HH. { apply (contextualLeq_impl_fp I1 I1'). done. }
      iFrame "∗ % #". iSplitR. iPureIntro. reflexivity. iSplitL. iEval (rewrite HH) in "H5".
      iApply "H5". iExists false. iFrame. iExists In'. eauto with iFrame. iPureIntro. set_solver. }
      iEval (rewrite H2). done. iIntros "HΦ". iModIntro. wp_pures. done.
    - wp_match. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I1 Ns2)"(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)". 
      iAssert (⌜n ∈ Nds I1⌝)%I with "[Hfp1 Hinn H6 H7]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns1 Ns2) with "[$]") as "%".
        iDestruct "H7" as %H7. iDestruct "Hinn" as %Hinn. iEval (rewrite <-H7).
        iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (Nds I1) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In'') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf. { iApply (hrep_sep_star n In In''). 
      iFrame. } exfalso. done. } iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro.
      iSplitR "HIn Hb". iExists I1, Ns2. iFrame "∗ % #". iApply "H5". iExists true. iFrame.
      eauto with iFrame. } iIntros "Hlock". iModIntro. iSplitL. iExists I1, Ns2. iFrame "∗ % #".
      iApply "H5". iExists false. eauto with iFrame. iIntros "AU". iModIntro.
      wp_pures. iApply "IH". done.
  Qed.

(* TODOs

   Don't need γ_c anymore!

   why do we need Auth(FI)? Why not just have FI?

   Idea: you don't need to remove the In from the shared state since anyway none 
   of the helper functions need it.
   Do split and maintenance operations need it?
   Don't think so: we can always update the interfaces after the helpers have
     returned.
   If the interface is always in the shared state, then we can talk about inreach
      of locked nodes too?
   Might still need Auth(Set) to say inreach is only increased.
   Inreach-step lemma is easier now, can say it in terms of the two relevant
     singleton interfaces?


     decisiveOp returns lockLoc for new nodes - this should tell us that they're not part of the global interface
     Add a constraint that the global interface is closed
     Then we can get the side condition for REPL.
     
     TODO: in_outset k I x y doesn't need x parameter

     in_inset k I n --> k ∈ inset I n

     lockNode spec should take searchStr and return the node?

     Hypothesis globalint_root_inr : ∀ I Ir k,
     globalint I ∧ Ir ≼ I ∧ Nds Ir = {[root]} → k ∈ inreach Ir root.

 *)
  
