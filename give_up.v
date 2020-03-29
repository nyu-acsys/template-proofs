(** Verification of Give-up template algorithm *)

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
Section Give_Up_Cameras.

  (* RA for authoritative flow interfaces over multisets of keys *)
  Class flowintG Σ :=
    FlowintG { flowint_inG :> inG Σ (authR (inset_flowint_ur K)) }.
  Definition flowintΣ : gFunctors := #[GFunctor (authR (inset_flowint_ur K))].

  Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
  Proof. solve_inG. Qed.

  (* RA for authoritative sets of nodes *)
  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR Node)) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR Node))].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.
  
  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.

End Give_Up_Cameras.

(** Verification of the template *)
Section Give_Up_Template.

  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !(@keysetG K _ _) Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (*Definition val := heap_lang.val.*)
  (** The code of the give-up template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b+-tree.spl and
   * hashtbl-give-up.spl for the concrete implementations. *)

  Parameter findNext : val.
  Parameter inRange : val.
  Parameter decisiveOp : (dOp → val).

  Definition traverse (root: Node) : val :=
    rec: "tr" "n" "k"  :=
      lockNode "n";;
      if: inRange "n" "k" then
        match: (findNext "n" "k") with
          NONE => "n"
        | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
        end
      else
        unlockNode "n";;
        "tr" #root "k".

  Definition CSSOp (Ψ: dOp) (root: Node) : val :=
    rec: "dictOp" "k" :=
      let: "n" := (traverse root) #root "k" in
      match: ((decisiveOp Ψ) "n" "k") with
        NONE => unlockNode "n";; "dictOp" "k"
      | SOME "res" => unlockNode "n";; "res"
      end.

  (** Assumptions on the implementation made by the template proofs. *)

  (* The node predicate is specific to each template implementation. See GRASShopper files
     b+-tree.spl and hashtbl-give-up.spl for the concrete definitions. *)
  Parameter node : Node → inset_flowint_ur K → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ n I C, Timeless (node n I C).
  Instance node_timeless n I C: Timeless (node n I C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-give-up.spl and b+-tree.spl *)
  Hypothesis node_sep_star: ∀ n I_n I_n' C C',
    node n I_n C ∗ node n I_n' C' -∗ False.

  (** Helper functions specs *)

  (* The following functions are proved for each implementation in GRASShopper
   * (see b+-tree.spl and hashtbl-give-up.spl) *)

  Parameter inRange_spec : ∀ (n: Node) (k: K) (In : inset_flowint_ur K) (C: gset K),
   ⊢ ({{{ node n In C }}}
        inRange #n #k
      {{{ (res: bool), RET #res; node n In C ∗ ⌜res → in_inset K k In n⌝ }}})%I.

  Parameter findNext_spec : ∀ (n: Node) (k: K) (In : inset_flowint_ur K) (C: gset K),
    ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝ }}}
         findNext #n #k
       {{{ (succ: bool) (n': Node),
           RET (match succ with true => (SOMEV #n') | false => NONEV end);
           node n In C ∗ (match succ with true => ⌜in_outset K k In n'⌝ |
                                  false => ⌜¬in_outsets K k In⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K)
      (In: inset_flowint_ur K) (C: gset K),
      ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝
             ∗ ⌜¬in_outsets K k In⌝ }}}
           decisiveOp dop #n #k
         {{{ (succ: bool) (res: bool) (C1: gset K),
             RET (match succ with false => NONEV | true => (SOMEV #res) end);
             node n In C1 ∗ (match succ with false => ⌜C = C1⌝
                                        | true => Ψ dop k C C1 res
                             end) }}})%I.

  (** The concurrent search structure invariant *)

  Definition CSS (γ γ_fp γ_k : gname) root I (C: gset K) : iProp :=
    (own γ_k (● prod (KS, C)) ∗ own γ (● I) ∗ ⌜globalinv K root I⌝
    ∗ ([∗ set] n ∈ (domm I), (∃ b: bool, (lockLoc n) ↦ #b
      ∗ if b then True
        else (∃ (I_n: inset_flowint_ur K) (C_n: gset K),
              own γ (◯ I_n) ∗ node n I_n C_n
              ∗ ⌜domm I_n = {[n]}⌝ ∗ own γ_k (◯ prod (keyset K I_n n, C_n)))))
    ∗ own γ_fp (● domm I)
    )%I.

  Definition is_CSS γ γ_fp γ_k root C :=
    (∃ I, (CSS γ γ_fp γ_k root I C))%I.

  (** Proofs of traverse and CSSOp *)

  Lemma traverse_spec (γ γ_fp γ_k: gname) (k: K) (root n: Node) (Ns: gset Node):
   ⊢ ⌜k ∈ KS⌝ ∗ ⌜n ∈ Ns⌝ ∗ own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝ -∗
     <<< ∀ C, is_CSS γ γ_fp γ_k root C >>>
       traverse root #n #k @ ⊤
     <<< ∃ (n': Node) (Ns': gsetUR Node) (I_n': inset_flowint_ur K) (C_n': gset K),
        is_CSS γ γ_fp γ_k root C ∗ ⌜n' ∈ Ns'⌝ ∗ own γ_fp (◯ Ns')
        ∗ own γ (◯ I_n') ∗ node n' I_n' C_n'
        ∗ own γ_k (◯ prod (keyset K I_n' n', C_n')) ∗ ⌜domm I_n' = {[n']}⌝
        ∗ ⌜in_inset K k I_n' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns). iIntros "(#Hks & #Hinn & #Hfp & #Hroot)".
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n). iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "Hst". iDestruct "Hst" as (I)"(H2 & H3 & H4 & H5 & H6)".
    iAssert (⌜n ∈ domm I⌝)%I with "[Hfp Hinn H6]" as "%".
    { iPoseProof ((auth_own_incl γ_fp (domm I) Ns) with "[$]") as "%".
      apply gset_included in H0.
      iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "H5" as "[Hb H5]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitL.
    iExists I. iFrame "∗ % #". iApply "H5". iExists b.
    iFrame. eauto with iFrame. } iIntros "(Hloc & %)".
    destruct b. { iExFalso. done. } clear H1. iModIntro.
    iSplitR "Hb". iExists I. iFrame "∗ % #". iApply "H5". iExists true.
    iFrame. iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (In Cn) "(HIn & Hrep & #HNds & HKS)". iDestruct "HNds" as %HNds.
    wp_bind (inRange _ _)%E. wp_apply ((inRange_spec n k In Cn) with "Hrep").
    iIntros (b) "(Hrep & Hb)". destruct b.
    - wp_pures. wp_bind (findNext _ _)%E. iSimpl in "Hb".
      iDestruct "Hb" as %Hinset. specialize (Hinset Coq.Init.Logic.I).
      wp_apply ((findNext_spec n k In Cn) with "[Hrep]"). iFrame "∗ # %".
      iIntros (b n') "(Hrep & Hbb)". destruct b.
      + wp_pures. awp_apply (unlockNode_spec n).
        iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
        iDestruct "Hst" as (I1)"(H1 & H2 & % & H5 & H6)".
        iAssert (⌜n ∈ domm I1⌝)%I with "[Hfp Hinn H6]" as "%".
        { iPoseProof ((auth_own_incl γ_fp (domm I1) Ns) with "[$]") as "%".
          apply gset_included in H2.
          iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
        rewrite (big_sepS_elem_of_acc _ (domm I1) n); last by eauto.
        iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
        destruct b; first last. { iDestruct "Hl" as (In' Cn') "(_ & Hrep' & _)".
        iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In').
        iFrame. } exfalso. done. }
        iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "HIn HKS Hrep Hbb".
        iExists I1. iFrame "∗ % #". iApply "H5". iExists true. iFrame. iIntros "AU".
        iModIntro. iFrame. } iIntros "Hlock".
        iDestruct "Hbb" as %Hbb.
        iAssert (⌜n' ∈ (domm I1)⌝ ∗ ⌜root ∈ (domm I1)⌝ ∗ own γ (● I1) ∗ own γ_fp (● (domm I1)) ∗ own γ (◯ In))%I
                with "[HIn H2 H6]" as "Hghost".
        { iPoseProof ((auth_own_incl γ_fp (domm I1) Ns) with "[$]") as "%".
          apply gset_included in H3.
          iPoseProof ((auth_own_incl γ I1 In) with "[$H2 $HIn]") as (I2)"%".
          iPoseProof (own_valid with "H2") as "%".
          iAssert (⌜n' ∈ domm I1⌝)%I as "%".
          { iPureIntro. assert (n' ∈ domm I2).
            { apply (flowint_step I1 In I2 k n' root); try done. }
            unfold globalinv in H1. destruct H1 as [HI1 H1].
            apply leibniz_equiv in H4. rewrite H4 in HI1.
            assert (domm (In⋅I2) = domm (In) ∪ domm (I2)). { apply intComp_dom. done. } rewrite H4.
            rewrite H7. set_solver. }
            iFrame. iPureIntro. split; try done. apply globalinv_root_fp. auto. }
        iDestruct "Hghost" as "(% & % & HAIn & HAfp & HIn)".
        iMod (own_update γ_fp (● (domm I1)) (● (domm I1) ⋅ ◯ (domm I1)) with "HAfp") as "HNs".
        apply auth_update_core_id. apply gset_core_id. done.
        iDestruct "HNs" as "(HAfp & #Hfp1)".
        iModIntro. iSplitL. iExists I1.
        iFrame "∗ % #". iApply "H5". iExists false. iFrame. iExists In. eauto with iFrame.
        iIntros "AU". iModIntro. wp_pures. iApply "IH". iFrame "∗ % #". done.
      + iApply fupd_wp. iMod "AU" as (C) "[Hst [_ Hclose]]". iSpecialize ("Hclose" $! n Ns In).
        iMod ("Hclose" with "[Hst HIn Hrep Hbb HKS]") as "HΦ".
        iFrame "∗ % #". iModIntro. wp_match. done.
    - wp_if. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
      iDestruct "Hst" as (I1)"(H1 & H2 & % & H5 & H6)".
      iAssert (⌜n ∈ domm I1⌝)%I with "[Hfp Hinn H6]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I1) Ns) with "[$]") as "%".
        apply gset_included in H2.
        iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I1) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In' Cn') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In').
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hrep HIn HKS".
      iExists I1. iFrame "∗ % #". iApply "H5". iExists true. iFrame. iIntros "AU".
      iModIntro. eauto with iFrame. } iIntros "Hlock". iModIntro.
      iSplitL. iExists I1. iFrame "∗ % #". iApply "H5". iExists false. iFrame.
      iExists In, Cn. eauto with iFrame. iIntros "AU". iModIntro. wp_pures.
      iApply "IH". eauto with iFrame. done.
  Qed.


  (** Verification of abstract specification of the search structure operation. *)
  
  (*Instance Ψ_persistent dop (k : K) C C' res : Persistent (Ψ dop k C C' res : iProp).
  Proof. destruct dop; apply _. Qed.*)

  Theorem CSSOp_spec (γ γ_fp γ_k: gname) root (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ <<< ∀ C, is_CSS γ γ_fp γ_k root C >>>
      CSSOp dop root #k @ ⊤
    <<< ∃ C' (res: bool), is_CSS γ γ_fp γ_k root C'
        ∗ (Ψ dop k C C' res : iProp), RET #res >>>.
  Proof.
    iIntros "HKin" (Φ) "AU". iLöb as "IH". wp_lam.
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I0) "(H1 & H2 & % & H5 & H6)".
    assert (root ∈ (domm I0))%I as Hroot. { apply globalinv_root_fp. done. }
    iMod (own_update γ_fp (● (domm I0)) (● (domm I0) ⋅ ◯ (domm I0)) with "H6") as "HNs".
    { apply auth_update_core_id. apply gset_core_id. done. }
    iDestruct "HNs" as "(HAfp & #Hfp0)". iDestruct "HKin" as %HKin.
    iMod ("HAU" with "[H1 H2 H5 HAfp] ") as "AU". { iExists I0. iFrame "∗ % #". }
    iModIntro. wp_bind (traverse _ _ _)%E.
    awp_apply (traverse_spec γ γ_fp γ_k k root root (domm I0)). eauto with iFrame.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "Hst". iAaccIntro with "Hst"; first by eauto with iFrame.
    iIntros (n Ns1 In Cn) "(Hst & #Hinn & #Hfp1 & HIn & Hrepn & HKS & #HNdsn & #Hinset & #Hnotout)".
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hrepn]"). eauto with iFrame.
    iIntros (b res Cn'). iIntros "Hb". destruct b.
    - iDestruct "Hb" as "(Hrep & #HΨ)".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(H2 & H3 & % & H6 & H7)".
      iAssert (⌜n ∈ domm I⌝)%I with "[Hfp1 Hinn H7]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I) Ns1) with "[$]") as "%".
        apply gset_included in H2.
        iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
      iDestruct "H6" as "[Hl H6]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In'' Cn'') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In'').
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "HIn Hrep HKS".
      iExists I. iFrame "∗ % #". iApply "H6". iExists true.
      iFrame "Hlock". eauto with iFrame. } iIntros "Hlock".
      iPoseProof (own_valid with "HIn") as "%". rename H3 into Hvldn. 
      iPoseProof (own_valid with "HKS") as "%". rename H3 into HvldCn.
      rewrite auth_frag_valid in HvldCn *; intros HvldCn. unfold valid, cmra_valid in HvldCn.
      simpl in HvldCn. unfold ucmra_valid in HvldCn. simpl in HvldCn.
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C2) with "[H2 HKS]") as "Hgks".
      iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout. 
      assert (k ∈ keyset K In n) as K_in_ksIn. apply keyset_def; try done.
      iFrame "% ∗ #". iEval (unfold Ψ) in "HΨ".
      { destruct dop.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. subst Cn'. done.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver. }
      iDestruct "Hgks" as (C2') "(#HΨC & Ha & Hf)".
      iModIntro. iExists (C2'), res. iSplitL. iSplitR "HΨC".
      { iExists I. iFrame "∗ % #". iApply "H6". iExists false. iFrame "∗ # %".
        iExists In, Cn'. eauto with iFrame. } done. iIntros "HΦ". iModIntro. wp_pures. done.
    - wp_match. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I1)"(H2 & H3 & % & H6 & H7)".
      iAssert (⌜n ∈ domm I1⌝)%I with "[Hfp1 Hinn H7]" as "%".
      { iPoseProof ((auth_own_incl γ_fp (domm I1) Ns1) with "[$]") as "%".
        apply gset_included in H2.
        iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I1) n); last by eauto.
      iDestruct "H6" as "[Hl H6]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last.
      { iDestruct "Hl" as (In'' Cn'') "(_ & Hrep' & _)".
        iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf.
        { iDestruct "Hb" as "(Hrep & %)".
          iApply (node_sep_star n In In'').
          iFrame. }
        exfalso. done. }
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro.
        iSplitR "HIn Hb HKS". iExists I1. iFrame "∗ % #". iApply "H6".
        iExists true. iFrame. eauto with iFrame. }
      iIntros "Hlock". iModIntro. iSplitL. iExists I1.
      iDestruct "Hb" as "(Hb & %)". subst Cn.
      iFrame "∗ % #".
      iApply "H6". iExists false. eauto with iFrame. iIntros "AU". iModIntro.
      wp_pures. iApply "IH"; try done.
  Qed.

End Give_Up_Template.
