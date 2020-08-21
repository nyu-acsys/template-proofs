(** Verification of a simple example template: a single-node structure *)

Require Import lock.
From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Import auth_ext search_str.

(** We use integers as keys. *)
Definition K := Z.

(* The keyspace is some arbitrary finite subset of K. *)
Parameter KS : gset K.


(** Definitions of cameras used in the template verification *)
Section One_Node_Cameras.

  (* RA for fractional set of keys *)
  Definition frackeysCmra : cmraT := prodR fracR (agreeR (gsetUR K)).

  Class frackeysG Σ :=
    FrackeyshG { frackeys_inG :> inG Σ  frackeysCmra}.
  Definition frackeysΣ : gFunctors := #[GFunctor frackeysCmra].

  Instance subG_frackeysΣ {Σ} : subG frackeysΣ Σ → frackeysG Σ.
  Proof. solve_inG. Qed.

End One_Node_Cameras.

Section Frac_Agree_Cmra.

  Context `{!frackeysG Σ}.

  Definition makeElem (q : Qp) (C : gsetUR K) : frackeysCmra := (q, to_agree C).
  Typeclasses Opaque makeElem.

  Notation "γ ⤇[ q ] m" := (own γ (makeElem q m))
    (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
  Notation "γ ⤇½ m" := (own γ (makeElem (1/2) m))
    (at level 20, format "γ ⤇½  m") : bi_scope.

  Global Instance makeElem_fractional γ m: Fractional (λ q, γ ⤇[q] m)%I.
  Proof.
    intros p q. rewrite /makeElem.
    rewrite -own_op; f_equiv.
    split; first done.
    by rewrite /= agree_idemp.
  Qed.

  Global Instance makeElem_as_fractional γ m q:
    AsFractional (own γ (makeElem q m)) (λ q, γ ⤇[q] m)%I q.
  Proof.
    split. done. apply _.
  Qed.

  Global Instance makeElem_Exclusive m: Exclusive (makeElem 1 m).
  Proof.
    rewrite /makeElem. intros [y ?] [H _]. apply (exclusive_l _ _ H).
  Qed.

  Lemma makeElem_op p q n:
    makeElem p n ⋅ makeElem q n ≡ makeElem (p + q) n.
  Proof.
    rewrite /makeElem; split; first done.
    by rewrite /= agree_idemp.
  Qed.

  Lemma makeElem_eq γ p q (n m : gsetUR K):
    γ ⤇[p] n -∗ γ ⤇[q] m -∗ ⌜n = m⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %HValid.
    destruct HValid as [_ H2].
    iIntros "!%"; by apply agree_op_invL'.
  Qed.

  Lemma makeElem_entail γ p q (n m : gsetUR K):
    γ ⤇[p] n -∗ γ ⤇[q] m -∗ γ ⤇[p + q] n.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_eq with "H1 H2") as %->.
    iCombine "H1" "H2" as "H".
    by rewrite makeElem_op.
  Qed.

  Lemma makeElem_update γ (n m k : gsetUR K):
    γ ⤇½ n -∗ γ ⤇½ m ==∗ γ ⤇[1] k.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_entail with "H1 H2") as "H".
    rewrite Qp_div_2.
    iApply (own_update with "H"); by apply cmra_update_exclusive.
  Qed.

End Frac_Agree_Cmra.

(** Syntactic sugar for fraction-set RA *)
Notation "γ ⤇[ q ] m" := (own γ (makeElem q m))
  (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
Notation "γ ⤇½ m" := (own γ (makeElem (1/2) m))
  (at level 20, format "γ ⤇½  m") : bi_scope.

(** Verification of the template *)
Section One_Node_Template.

  Context `{!heapG Σ, !frackeysG Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. *)

  Parameter decisiveOp : (dOp → val).

  Definition CSSOp (Ψ: dOp) (r: Node) : val :=
    rec: "dictOp" "k" :=
      lockNode #r;;
      let: "res" := ((decisiveOp Ψ) #r "k") in
      unlockNode #r;;
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


  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper *)

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K) (C: gset K),
      ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n C }}}
           decisiveOp dop #n #k
         {{{ (res: bool) (C1: gset K),
             RET #res;
             node n C1 ∗ ⌜Ψ dop k C C1 res⌝ }}})%I.

  (** The concurrent search structure invariant *)

  Definition nodePred γ n C : iProp :=
    node n C
    ∗ γ ⤇½ C.

  Definition CSS γ r (C: gset K) : iProp :=
    ∃ (b: bool),
      γ ⤇½ C
      ∗ lockLoc r ↦ #b
      ∗ (if b then True else nodePred γ r C).

  (** High-level lock specs **)

  Lemma lockNode_spec_high γ (r: Node) :
    ⊢  <<< ∀ (C: gset K), CSS γ r C >>>
         lockNode #r @ ⊤
       <<< CSS γ r C ∗ nodePred γ r C, RET #() >>>.
  Proof.
    iIntros (Φ) "AU".
    awp_apply (lockNode_spec r).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss". iDestruct "Hcss" as (b) "(HC & Hlock & Hb)".
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro. iSplitL.
      iFrame. iExists b. iFrame.
      eauto with iFrame.
    }
    iIntros "(Hlockn & %)". iModIntro.
    subst b. iSplitL.
    iFrame. iExists true. iFrame.
    eauto with iFrame.
  Qed.

  (** Proof of CSSOp *)

  Theorem CSSOp_spec (γ: gname) r (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ r C >>>
                          CSSOp dop r #k @ ⊤
                 <<< ∃ C' (res: bool), CSS γ r C'
                                     ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "%" (Φ) "AU". wp_lam. wp_bind(lockNode _)%E.
    (* Open AU to get lockNode precondition *)
    awp_apply (lockNode_spec_high γ r); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "HInv". iAaccIntro with "HInv".
    { iIntros "HInv". iModIntro. eauto with iFrame. }
    iIntros "(HInv & Hnode)".
    (* Close AU and move on *)
    iModIntro. iFrame. iIntros "AU". iModIntro.
    (* Execute decisiveOp *)
    wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Hnode" as "(Hn & HCn)".
    wp_apply ((decisiveOp_spec dop r k) with "[Hn]"). eauto with iFrame.
    iIntros (res C1) "(Hn & %)".
    wp_pures. wp_bind(unlockNode _)%E.
    awp_apply (unlockNode_spec r).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C2) "HInv".
    (* Unfold CSS to execute unlockNode *)
    iDestruct "HInv" as (b) "(HC & Hlock & Hb)".
    iAssert (⌜b = true⌝)%I with "[-]" as "%".
    {
      destruct b.
      - by iPureIntro.
      - iExFalso. iDestruct "Hb" as "(? & ?)".
        iApply (node_sep_star r with "[$]").
    }
    subst b.
    iAaccIntro with "Hlock".
    { iIntros "Hlock". iModIntro.
      iFrame. iSplitL. iExists true. iFrame.
      iIntros. iModIntro. iFrame.
    }
    iIntros "Hlock".
    (* Commit AU *)
    iPoseProof (makeElem_eq with "[$HC] [$HCn]") as "%".
    subst C2.
    iMod (makeElem_update _ _ _ C1 with "HC HCn") as "(HC & HCn)".
    iModIntro.
    (* Close AU *)
    iExists C1, res. iSplitL. iFrame. iSplitL.
    iExists false. iFrame.
    by iPureIntro.
    iIntros. iModIntro. by wp_pures.
  Qed.

End One_Node_Template.
