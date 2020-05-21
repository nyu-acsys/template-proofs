(** Verification of a simple example template: a two-node structure *)

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
Require Import search_str keyset_ra.

(** We use integers as keys. *)
Definition K := Z.


(** Definitions of cameras used in the template verification *)
Section Two_Node_Cameras.

  (* keyset RA *)
  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.

End Two_Node_Cameras.

(** Verification of the template *)
Section Two_Node_Template.

  Context `{!heapG Σ, !(@keysetG K _ _) Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. *)

  Parameter decisiveOp : (dOp → val).
  Parameter findNode : val.

  Definition CSSOp (n1 n2: Node) (o: dOp) : val :=
    rec: "dictOp" "k" :=
      let: "n" := (findNode #n1 #n2 "k") in
      lockNode "n";;
      let: "res" := ((decisiveOp o) "n" "k") in
      unlockNode "n";;
      "res".

  (** Assumptions on the implementation made by the template proofs. *)

  (* The node predicate is specific to each template implementation. *)
  Parameter node : Node → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ n C, Timeless (node n C).
  Instance node_timeless n C: Timeless (node n C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-give-up.spl and b+-tree.spl *)
  Hypothesis node_sep_star: ∀ n C C',
    node n C ∗ node n C' -∗ False.

  (* Predicate that defines the keyset of each node *)
  Parameter nodeKS : K → Node → Prop.

  (** The concurrent search structure invariant *)

  Definition inFP (n1 n2 x: Node) : iProp :=
    ⌜x = n1 ∨ x = n2⌝.

  Definition nodePred γ n : iProp :=
    ∃ (Kn Cn: gset K),
      node n Cn
      ∗ own γ (◯ prod (Kn, Cn))
      ∗ ⌜∀ k: K, k ∈ Kn ↔ nodeKS k n⌝.

  Definition CSS γ n1 n2 (C: gset K) : iProp :=
    ∃ (b1 b2: bool),
      own γ (● prod (KS, C))
      ∗ lockLoc n1 ↦ #b1
      ∗ (if b1 then True else nodePred γ n1)
      ∗ lockLoc n2 ↦ #b2
      ∗ (if b2 then True else nodePred γ n2).

  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper *)

  Parameter findNode_spec : ∀ (n1 n2: Node) (k: K),
      ⊢ ({{{ ⌜k ∈ KS⌝ }}}
           findNode #n1 #n2 #k
         {{{ (n: Node), RET #n; inFP n1 n2 n ∗ ⌜nodeKS k n⌝ }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K) (C: gset K),
      ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n C }}}
           decisiveOp dop #n #k
         {{{ (res: bool) (C1: gset K),
             RET #res;
             node n C1 ∗ ⌜Ψ dop k C C1 res⌝ }}})%I.

  (** High-level lock specs **)

  Lemma lockNode_spec_high γ (n1 n2 n: Node) :
    ⊢  inFP n1 n2 n -∗
       <<< ∀ (C: gset K), CSS γ n1 n2 C >>>
         lockNode #n @ ⊤
       <<< CSS γ n1 n2 C ∗ nodePred γ n, RET #() >>>.
  Proof.
    iIntros "#Hfp". iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iDestruct "Hcss" as (b1 b2) "(HKS & Hlock1 & Hb1 & Hlock2 & Hb2)".
    iDestruct "Hfp" as "[%|%]".
    - (* n = n1 *)
      subst n.
      iAaccIntro with "Hlock1".
      { iIntros "Hlockn". iModIntro. iSplitL.
        iFrame. iExists b1, b2. iFrame.
        eauto with iFrame.
      }
      iIntros "(Hlockn & %)". iModIntro.
      subst b1. iSplitL.
      iFrame. iExists true, b2. iFrame.
      eauto with iFrame.
    - (* n = n2 *)
      subst n.
      iAaccIntro with "Hlock2".
      { iIntros "Hlockn". iModIntro. iSplitL.
        iFrame. iExists b1, b2. iFrame.
        eauto with iFrame.
      }
      iIntros "(Hlockn & %)". iModIntro.
      subst b2. iSplitL.
      iFrame. iExists b1, true. iFrame.
      eauto with iFrame.
  Qed.

  (** Proof of CSSOp *)

  Theorem CSSOp_spec (γ: gname) n1 n2 (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ n1 n2 C >>>
                          CSSOp n1 n2 dop #k @ ⊤
                 <<< ∃ C' (res: bool), CSS γ n1 n2 C'
                                     ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "%" (Φ) "AU". wp_lam. wp_bind (findNode _ _ _)%E.
    wp_apply (findNode_spec n1 n2); first done.
    iIntros (n) "(#Hfp & %)". wp_pures. wp_bind (lockNode _)%E.
    (* Open AU to get lockNode precondition *)
    awp_apply (lockNode_spec_high γ n1 n2); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "HInv". iAaccIntro with "HInv".
    { iIntros "HInv". iModIntro. eauto with iFrame. }
    iIntros "(HInv & Hnode)".
    (* Close AU and move on *)
    iModIntro. iFrame. iIntros "AU". iModIntro.
    (* Execute decisiveOp *)
    wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Hnode" as (Kn Cn) "(Hn & Hks & %)".
    wp_apply ((decisiveOp_spec dop n k) with "[Hn]"). eauto with iFrame.
    iIntros (res Cn') "(Hn & %)".
    wp_pures. wp_bind(unlockNode _)%E.
    awp_apply (unlockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C2) "HInv".
    (* Unfold CSS to execute unlockNode *)
    iDestruct "HInv" as (b1 b2) "(HKS & Hlock1 & Hb1 & Hlock2 & Hb2)".
    iDestruct "Hfp" as "[%|%]".
    - (* n = n1 *)
      subst n.
      iAssert (⌜b1 = true⌝)%I with "[-]" as "%".
      {
        destruct b1.
        - by iPureIntro.
        - iExFalso. iDestruct "Hb1" as (? ?) "(? & ?)".
          iApply (node_sep_star n1 with "[$]").
      }
      subst b1.
      iAaccIntro with "Hlock1".
      { iIntros "Hlock1". iModIntro.
        iFrame. iSplitL. iExists true, b2. iFrame.
        eauto with iFrame.
      }
      iIntros "Hlock1".
      (* Commit AU *)
      iMod ((ghost_update_keyset γ dop k Cn Cn' res Kn C2)
              with "[HKS Hks]") as (C2') "(#HΨC & Hks & HkIn)".
      {
        iPoseProof (keyset_valid with "Hks") as "%".
        assert (k ∈ Kn). by apply H1.
        assert (Cn' ⊆ Kn).
        { apply (Ψ_impl_C_in_K dop k Cn Cn' res); try done. }
        iFrame "∗ #". by iPureIntro.
      }
      iModIntro.
      (* Close AU *)
      iExists C2', res. iSplitL. iSplitL.
      iExists false, b2.
      iFrame. iExists Kn, Cn'. iFrame. by iPureIntro. by iFrame.
      iIntros. iModIntro. by wp_pures.
    - (* n = n2. TODO can we refactor? *)
      subst n.
      iAssert (⌜b2 = true⌝)%I with "[-]" as "%".
      {
        destruct b2.
        - by iPureIntro.
        - iExFalso. iDestruct "Hb2" as (? ?) "(? & ?)".
          iApply (node_sep_star n2 with "[$]").
      }
      subst b2.
      iAaccIntro with "Hlock2".
      { iIntros "Hlock2". iModIntro.
        iFrame. iSplitL. iExists b1, true. iFrame.
        eauto with iFrame.
      }
      iIntros "Hlock2".
      (* Commit AU *)
      iMod ((ghost_update_keyset γ dop k Cn Cn' res Kn C2)
              with "[HKS Hks]") as (C2') "(#HΨC & Hks & HkIn)".
      {
        iPoseProof (keyset_valid with "Hks") as "%".
        assert (k ∈ Kn). by apply H1.
        assert (Cn' ⊆ Kn).
        { apply (Ψ_impl_C_in_K dop k Cn Cn' res); try done. }
        iFrame "∗ #". by iPureIntro.
      }
      iModIntro.
      (* Close AU *)
      iExists C2', res. iSplitL. iSplitL.
      iExists b1, false.
      iFrame. iExists Kn, Cn'. iFrame. by iPureIntro. by iFrame.
      iIntros. iModIntro. by wp_pures.
  Qed.
End Two_Node_Template.
