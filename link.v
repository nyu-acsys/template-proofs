(** Verification of Give-up template algorithm *)

Require Import lock.
From iris.algebra Require Import excl auth gmap agree gset frac.
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
Section Link_Cameras.

  (* RA for authoritative flow interfaces over pairs of multisets of keys *)
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

  Instance subG_keysetΣ {Σ} : subG (@keysetΣ K _ _) Σ → (@keysetG K _ _) Σ.
  Proof. solve_inG. Qed.
  
  (* RA for authoritative inreach sets *)
  Class inreachG Σ := InreachG { inreach_inG :> inG Σ (authR (gsetUR K)) }.
  Definition inreachΣ : gFunctors := #[GFunctor (authR (gsetUR K))].

  Instance subG_inreachΣ {Σ} : subG inreachΣ Σ → inreachG Σ.
  Proof. solve_inG. Qed.

  (* RA for fractional interfaces *)
  Class fracintG Σ :=
    FracinthG { fracint_inG :> inG Σ (authR (inset_flowint_ur K)) }.
  Definition fracintΣ : gFunctors := #[GFunctor (authR (inset_flowint_ur K))].

  Instance subG_fracintΣ {Σ} : subG fracintΣ Σ → fracintG Σ.
  Proof. solve_inG. Qed.

End Link_Cameras.

(** Verification of the template *)
Section Link_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !(@keysetG K _ _) Σ, !inreachG Σ,
    !fracintG Σ}.
  Notation iProp := (iProp Σ).

  (** The code of the link template. *)

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b-link-core.spl and
   * hashtbl-link.spl for the concrete implementations. *)

  (* TODO add alias inreach = inset for this file. *)

  Parameter findNext : val.
  Parameter decisiveOp : (dOp → val).

  Definition traverse : val :=
    rec: "tr" "n" "k" :=
      lockNode "n";;
      match: (findNext "n" "k") with
        NONE => "n"
      | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
      end.

  Definition CSSOp (Ψ: dOp) (r: Node) : val :=
    rec: "dictOp" "k" :=
      let: "n" := traverse #r "k" in
      match: ((decisiveOp Ψ) "n" "k") with
        NONE => unlockNode "n";; "dictOp" "k"
      | SOME "res" => unlockNode "n";; "res"
      end.

  (** Assumptions on the implementation made by the template proofs. *)

  (* The node predicate is specific to each template implementation. See GRASShopper files
     b-link.spl and hashtbl-link.spl for the concrete definitions. *)
  Parameter node : Node → inset_flowint_ur K → gset K → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ n I C, Timeless (node n I C).
  Instance node_timeless n I C: Timeless (node n I C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis is proved as GRASShopper lemmas in
   * hashtbl-link.spl and b-link.spl *)
  Hypothesis node_sep_star: ∀ n I_n I_n' C C',
    node n I_n C ∗ node n I_n' C' -∗ False.


  (** Helper functions specs *)
  (* These are proved for each implementation in GRASShopper *)

  (* The following functions are proved for each implementation in GRASShopper
   * (see b-link.spl and hashtbl-link.spl *)

  Parameter findNext_spec : ∀ (n: Node) (k: K) (In : inset_flowint_ur K) (C: gset K),
    ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝ }}}
         findNext #n #k
       {{{ (succ: bool) (np: Node),
           RET (match succ with true => (SOMEV #np) | false => NONEV end);
           node n In C ∗ (match succ with
                            true => ⌜in_outset K k In np⌝
                          | false => ⌜¬in_outsets K k In⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K)
      (In: inset_flowint_ur K) (C: gset K),
    ⊢ ({{{ ⌜k ∈ KS⌝ ∗ node n In C ∗ ⌜in_inset K k In n⌝ ∗ ⌜¬in_outsets K k In⌝ }}}
         decisiveOp dop #n #k
       {{{ (succ: bool) (res: bool) (C1: gset K),
           RET (match succ with false => NONEV | true => (SOMEV #res) end);
           node n In C1 ∗ (match succ with false => ⌜C = C1⌝
                                         | true => Ψ dop k C C1 res
                           end) }}})%I.

  (** The concurrent search structure invariant *)

  Definition inFP γ_f n : iProp :=
    ∃ (N: gset Node), own γ_f (◯ N) ∗ ⌜n ∈ N⌝.

  Definition inInr γ_i k (n: Node) : iProp :=
    ∃ (Ks: gset K), own (γ_i n) (◯ Ks) ∗ ⌜k ∈ Ks⌝.

  Definition nodePred γ_f γ_h γ_k n In Cn : iProp :=
    node n In Cn
    ∗ own (γ_h n) ((●{1/2} In))
    ∗ own γ_k (◯ prod (keyset K In n, Cn))
    ∗ inFP γ_f n
    ∗ ⌜domm In = {[n]}⌝.

  Definition nodeShared γ_I γ_i γ_h n In : iProp :=
    own γ_I (◯ In)
    ∗ own (γ_h n) ((●{1/2} In))
    ∗ ⌜domm In = {[n]}⌝    (* Needed for globalinv_root_ins *)
    ∗ own (γ_i n) (● (inset K In n)).

  Definition CSSi γ_I γ_f γ_k γ_i γ_h r C I : iProp :=
    (own γ_I (● I) ∗ ⌜globalinv K r I⌝
     ∗ own γ_k (● prod (KS, C))
     ∗ own γ_f (● domm I)
     ∗ ([∗ set] n ∈ (domm I), (∃ (b: bool) (In: inset_flowint_ur K),
         (lockLoc n) ↦ #b
         ∗ (if b then True else (∃ Cn, nodePred γ_f γ_h γ_k n In Cn))
         ∗ nodeShared γ_I γ_i γ_h n In))
    )%I.

  Definition CSS γ_I γ_f γ_k γ_i γ_h r C : iProp :=
    (∃ I, CSSi γ_I γ_f γ_k γ_i γ_h r C I)%I.

  (** Some useful lemmas *)

  Lemma inFP_domm γ_I γ_f γ_k γ_i γ_h r C I n :
    inFP γ_f n -∗ CSSi γ_I γ_f γ_k γ_i γ_h r C I -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "#Hfp Hcss".
    iDestruct "Hcss" as "(HI & Hglob & Hks & Hdom & Hbigstar)".
    iDestruct "Hfp" as (N) "(#Hdom' & n_in_N)". iDestruct "n_in_N" as %n_in_N.
    iPoseProof ((auth_own_incl γ_f (domm I) N) with "[$]") as "#N_incl".
    iDestruct "N_incl" as %N_incl.
    apply gset_included in N_incl.
    iPureIntro. set_solver.
  Qed.
  
  Lemma frac_int_equal (γ_h: Node → gname) n In In' :
    own (γ_h n) (●{1/2} In) -∗ own (γ_h n) (●{1/2} In') -∗ ⌜In = In'⌝.
  Proof.
    iIntros.
    iPoseProof ((own_valid_2 (γ_h n) (●{1/2} In) (●{1/2} In'))
                  with "[$] [$]") as "%"; try done.
    iPureIntro.
    apply (auth_auth_frac_op_inv _ _ _ _) in H0.
    by apply leibniz_equiv.
  Qed.
    
  Lemma CSS_unfold γ_I γ_f γ_k γ_i γ_h r C n :
    let globalGhost γ_I γ_k γ_f r I C : iProp :=
        (own γ_I (● I) ∗ ⌜globalinv K r I⌝ ∗ own γ_k (● prod (KS, C))
        ∗ own γ_f (● domm I))%I
    in
    CSS γ_I γ_f γ_k γ_i γ_h r C -∗ inFP γ_f n
    -∗ (∃ I,
        globalGhost γ_I γ_k γ_f r I C
        ∗ (∃ (b: bool) (In: inset_flowint_ur K),
              lockLoc n ↦ #b
              ∗ (if b then True else (∃ Cn, nodePred γ_f γ_h γ_k n In Cn))
              ∗ nodeShared γ_I γ_i γ_h n In)
        ∗ (∀ C',
           (globalGhost γ_I γ_k γ_f r I C'
           ∗ (∃ (b: bool) (In: inset_flowint_ur K),
                 lockLoc n ↦ #b
                 ∗ (if b then True else (∃ Cn, nodePred γ_f γ_h γ_k n In Cn))
                 ∗ nodeShared γ_I γ_i γ_h n In))
            -∗ CSS γ_I γ_f γ_k γ_i γ_h r C')).
  Proof.
    iIntros "Hcss #Hfp".
    iDestruct "Hcss" as (I) "(HI & Hglob & Hks & Hdom & Hbigstar)".
    iPoseProof (inFP_domm with "[$] [$]") as "%".
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)". iExists I. iFrame "∗".
    iIntros (C') "((HI & Hglob & Hks & Hdom) & H)".
    iExists I. iFrame "∗". by iApply "Hbigstar".
  Qed.

  Lemma CSS_unfold_node γ_I γ_f γ_k γ_i γ_h r C n In Cn :
    let globalGhost γ_I γ_k γ_f r I C : iProp :=
        (own γ_I (● I) ∗ ⌜globalinv K r I⌝ ∗ own γ_k (● prod (KS, C))
        ∗ own γ_f (● domm I))%I
    in
    CSS γ_I γ_f γ_k γ_i γ_h r C -∗ node n In Cn -∗ inFP γ_f n
    -∗ own (γ_h n) (●{1/2} In)
    -∗ (∃ I,
        node n In Cn ∗ own (γ_h n) (●{1/2} In)
        ∗ globalGhost γ_I γ_k γ_f r I C
        ∗ lockLoc n ↦ #true ∗ nodeShared γ_I γ_i γ_h n In
        ∗ (∀ C',
           (globalGhost γ_I γ_k γ_f r I C'
           ∗ (∃ (b: bool) (In: inset_flowint_ur K),
                 lockLoc n ↦ #b
                 ∗ (if b then True else (∃ Cn, nodePred γ_f γ_h γ_k n In Cn))
                 ∗ nodeShared γ_I γ_i γ_h n In))
            -∗ CSS γ_I γ_f γ_k γ_i γ_h r C')).
  Proof.
    iIntros "Hcss Hn #Hfp HfIn".
    iPoseProof (CSS_unfold with "[$] [$]") as (I) "(Hg & Hns & Hcss')".
    iExists I.
    iDestruct "Hns" as (b In') "(Hlock & Hnp & Hns)". destruct b.
    - (* Case n locked *)
      iDestruct "Hg" as "(HI & Hglob & Hks & Hdom)".
      iDestruct "Hns" as "(HIn & HhIn' & HdomIn & Hins)".
      iPoseProof (frac_int_equal with "[$] [$]") as "%". subst In'.
      iFrame "∗".
    - (* Case n unlocked: impossible *)
      iDestruct "Hnp" as (?C) "(Hn' & _)".
      iExFalso. iApply (node_sep_star n In In' with "[$]").
  Qed.

  (* TODO try just using CSS_unfold instead: *)
  Lemma CSS_fold γ_I γ_f γ_k γ_i γ_h r C n In Cn :
    nodePred γ_f γ_h γ_k n In Cn -∗ CSS γ_I γ_f γ_k γ_i γ_h r C
    -∗ (lockLoc n ↦ #true ∗ nodePred γ_f γ_h γ_k n In Cn
        ∗ ((∃ (b: bool), lockLoc n ↦ #b
             ∗ (if b then True else (∃ Cn, nodePred γ_f γ_h γ_k n In Cn)))
           -∗ CSS γ_I γ_f γ_k γ_i γ_h r C)).
  Proof.
    iIntros "Hnp Hcss".
    iDestruct "Hcss" as (I) "(HI & Hglob & Hks & Hdom & Hbigstar)".
    iDestruct "Hnp" as "(Hn & HnhIn & HkIn & #Hinfp & domIn)".
    iPoseProof (inFP_domm with "[$] [$]") as "%".
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hns & Hbigstar)".
    iDestruct "Hns" as (b In') "(Hlock & Hb & HIn & HhIn & HdomIn & Hins)".
    destruct b; first last.
    - (* Case n unlocked: impossible *)
      iDestruct "Hb" as (?C) "(Hn' & _)".
      iExFalso. iApply (node_sep_star n In In' with "[$]").
    - (* Case n locked *)
      iPoseProof (frac_int_equal with "[$] [$]") as "%". subst In'.
      iFrame "Hlock Hn HnhIn HkIn Hinfp domIn".
      iIntros "H". iClear "Hb". iDestruct "H" as (b) "(Hlock & Hb)".
      iExists I. iFrame "∗". iApply "Hbigstar".
      iExists b, In. iFrame "∗". 
  Qed.

  Lemma inInr_impl_inset γ_I γ_f γ_k γ_i γ_h r C n In Cn k :
    CSS γ_I γ_f γ_k γ_i γ_h r C -∗ nodePred γ_f γ_h γ_k n In Cn
    -∗ inInr γ_i k n
    -∗ ⌜in_inset K k In n⌝.
  Proof.
    iIntros "Hcss Hnp Hinr".
    iDestruct "Hnp" as "(Hn & HnhIn & HkIn & #Hinfp & domIn)".
    iPoseProof (CSS_unfold_node with "[$] [$] [$] [$]")
      as (I) "(Hn & HhIn & Hg & Hlock & Hns & Hcss')".
    iDestruct "Hg" as "(HI & Hglob & Hks & Hdom)".
    iDestruct "Hns" as "(HIn & HhIn' & HdomIn & Hins)".
    iDestruct "Hinr" as (R) "(Hinr & %)".
    iPoseProof ((auth_own_incl (γ_i n) (inset K In n) R) with "[$]")
      as "incl".
    iDestruct "incl" as %incl. iPureIntro.
    apply gset_included in incl. set_solver.
  Qed.

  Lemma ghost_snapshot_fp γ_f (Ns: gset Node) n:
    ⊢ own γ_f (● Ns) -∗ ⌜n ∈ Ns⌝ ==∗ own γ_f (● Ns) ∗ inFP γ_f n.
  Proof.
    iIntros. 
    iMod (own_update γ_f (● Ns) (● Ns ⋅ ◯ Ns) with "[$]")
      as "H".
    { apply auth_update_core_id. apply gset_core_id. done. }
    iDestruct "H" as "(Haa & Haf)". iFrame. iModIntro.
    iExists Ns. by iFrame.
  Qed.
    
  Lemma ghost_update_step γ_I γ_f γ_k γ_i γ_h r C n In Cn k n' :
    ⊢ CSS γ_I γ_f γ_k γ_i γ_h r C
      -∗ nodePred γ_f γ_h γ_k n In Cn
      -∗ ⌜in_inset K k In n⌝
      -∗ ⌜in_outset K k In n'⌝
      ==∗ CSS γ_I γ_f γ_k γ_i γ_h r C ∗ nodePred γ_f γ_h γ_k n In Cn
      ∗ inFP γ_f n' ∗ inInr γ_i k n'.
  Proof.
    iIntros "Hcss Hnp % %".
    iDestruct "Hnp" as "(Hn & HnhIn & HkIn & #Hinfp & domIn)".
    (* Can't use CSS_unfold_node because need to unroll bigstar twice. *)
    iDestruct "Hcss" as (I) "Hcss".
    iPoseProof (inFP_domm with "[$] [$]") as "%".
    iDestruct "Hcss" as "(HI & % & Hks & Hdom & Hbigstar)".
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hns & Hbigstar)".
    
    iDestruct "Hns" as "(HIn & HhIn' & HdomIn & Hins)".
    (* In ≼ I *)
    iPoseProof ((auth_own_incl γ_I I In) with "[$]")
      as (Io) "incl".
    iDestruct "incl" as %incl.
    assert (n' ∈ domm Io).
      by eauto using flowint_step. 
    assert (n' ∈ domm I).
      by admit.
    (* Take snapshot of fp to get inFP n' *)
    iMod (ghost_snapshot_fp γ_f (domm I) n' with "[$Hdom] [% //]")
        as "(Hdom & #Hinfp')".

      
    (* unroll star again using n' ∈ domm (I - In) and get In' *)
    (* somehow get ✓ (In ⋅ In') *)
    (* flowint_inset_step gives me k ∈ inset In' *)
    (* snapshot In' inreach to get inInr k n' *)
  Admitted.

  Lemma ghost_update_root γ_I γ_f γ_k γ_i γ_h r C k :
    ⊢ CSS γ_I γ_f γ_k γ_i γ_h r C -∗ ⌜k ∈ KS⌝
      ==∗
      CSS γ_I γ_f γ_k γ_i γ_h r C ∗ inFP γ_f r ∗ inInr γ_i k r.
  Proof.
    iIntros "Hcss %".
    iDestruct "Hcss" as (I) "(HI & #Hglob & Hks & Hdom & Hbigstar)".
    iDestruct "Hglob" as %Hglob.
    (* Snapshot FP for inFP: *)
    iMod (own_update γ_f (● domm I) (● domm I ⋅ ◯ domm I) with "Hdom")
      as "(Hdom & #Hfp)".
    { apply auth_update_core_id. apply gset_core_id. done. }
    (* Unfold bigstar *)
    assert (r ∈ domm I)%I as Hroot.
    { apply globalinv_root_fp. done. }
    rewrite (big_sepS_elem_of_acc _ (domm I) r); last by eauto.
    iDestruct "Hbigstar" as "[Hn Hbigstar]".
    iDestruct "Hn" as (b Ir) "(H1 & H2 & H3 & H4 & % & Hksr)". (* TODO rename *)
    (* Get Ir ≼ I needed for globalinv_root_ins *)
    iPoseProof (auth_own_incl with "[$HI $H3]") as "%".
    iAssert (inFP γ_f r)%I as "#Hinfp".
    {
      unfold inFP. iExists (domm I). iFrame "Hfp".
      iPureIntro. by apply globalinv_root_fp.
    }
    iMod (own_update (γ_i r) _ (● (inset K Ir r) ⋅ ◯ (inset K Ir r))
            with "Hksr") as "(Hksr & #Hinr)".
    { apply auth_update_core_id. apply gset_core_id. done. }
    (* Hksr -> Hinr *)
    iAssert (inInr γ_i k r)%I as "#Hininr".
    {
      iExists (inset K Ir r). iFrame "Hinr". iPureIntro.
      apply (globalinv_root_ins I). done. 
    }
    iModIntro. iSplitL. iExists I. iFrame "∗". iSplitR; first by iPureIntro.
    iApply "Hbigstar". iExists b, Ir. iFrame "∗". by iPureIntro.
    iFrame "#".
  Qed.

  Lemma ghost_update_CSS γ_I γ_f γ_k γ_i γ_h r C n In Cn Cn' (k: K) :
    ⊢ CSS γ_I γ_f γ_k γ_i γ_h r C -∗ ⌜k ∈ KS⌝
      -∗ node n In Cn'
      -∗ own (γ_h n) (●{1/2} In) -∗ own γ_k (◯ prod (keyset K In n, Cn))
      ==∗ ∃ C', CSS γ_I γ_f γ_k γ_i γ_h r C' ∗ nodePred γ_f γ_h γ_k n In Cn'.
  Proof.
(* Proof of ghost_update_CSS: *)
      (* iAssert (⌜n ∈ domm I⌝)%I with "[Hdom]" as "%". *)
      (* { iPoseProof ((auth_own_incl γ_f (domm I) Ns) with "[$]") as "%". *)
      (*   apply gset_included in H1. *)
      (* iPureIntro. set_solver. } *)
      (* rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto. *)
      (* iDestruct "Hbigstar" as "[Hn Hbigstar]". *)
      (* iDestruct "Hn" as (b In1) "(Hlock & Hb & HIn & #HNds & Hfis & Hinreach)". *)
      (* destruct b; first last. { iDestruct "Hb" as (Cn'') "(Hn' & _)". *)
      (* iAssert (⌜False⌝)%I with "[Hn Hn']" as %Hf. { iApply (node_sep_star n In In1). *)
      (* iFrame. } exfalso. done. } *)
      (* iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hn Hks". *)
      (* iExists I. iFrame "∗ % #". iApply "Hbigstar". iExists true, In1. *)
      (* iFrame "∗ # %". eauto with iFrame. } iIntros "Hlock". *)
      (* iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%". *)
      (* iPoseProof ((own_valid γ_I (● I)) with "HI") as "%". *)
      (* iPoseProof ((own_valid_2 (γ_h n) (●{1/2} In) (●{1/2} In1)) with "[Hfil] [Hfis]") as "%"; try done. *)
      (* apply (auth_auth_frac_op_inv _ _ _ _) in H4. apply leibniz_equiv in H4. replace In1. *)
      (* iPoseProof ((own_valid γ_I (◯ In)) with "HIn") as "%". rename H5 into HInV. *)
      (* assert (✓ In) as HInv. { apply (auth_frag_valid (◯ In)). done. }     *)
      (* iPoseProof (own_valid with "Hks") as "%". rename H5 into HvldCn. *)
      (* rewrite auth_frag_valid in HvldCn *; intros HvldCn. unfold valid, cmra_valid in HvldCn. *)
      (* simpl in HvldCn. unfold ucmra_valid in HvldCn. simpl in HvldCn. *)
      (* iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C) with "[HKS Hks]") as "Hgks". *)
      (* assert (k ∈ keyset K In n). apply keyset_def; try done. iFrame "% ∗ #". *)
      (* iEval (unfold Ψ) in "HΨ". *)
      (* { destruct dop. *)
      (*   - iDestruct "HΨ" as %(HΨ & _). iPureIntro. subst Cn'. done. *)
      (*   - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver. *)
      (*   - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver. } *)
      (* iDestruct "Hgks" as (C') "(#HΨC & Ha & Hf)". *)
  Admitted.

  (** High-level lock specs *)

  Lemma lockNode_spec_high γ_I γ_f γ_k γ_i γ_h r n :
    ⊢ inFP γ_f n
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h r C >>>
           lockNode #n @ ⊤
         <<< ∃ In Cn, CSS γ_I γ_f γ_k γ_i γ_h r C
                      ∗ nodePred γ_f γ_h γ_k n In Cn,
             RET #() >>>.
  Proof.
    iIntros "#HFp". iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iPoseProof (CSS_unfold with "[$] [$]")
      as (I) "(Hg & Hn & Hcss')".
    iDestruct "Hn" as (b In) "(Hlock & Hnp & Hother)".
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro.
      iPoseProof ("Hcss'" with "[-]") as "Hcss"; first eauto with iFrame.
      iFrame "Hcss". iIntros "AU". by iModIntro.
    }
    iIntros "(Hlockn & %)". iModIntro.
    subst b. iDestruct "Hnp" as (Cn) "Hn".
    iPoseProof ("Hcss'" with "[-Hn]") as "Hcss"; first eauto with iFrame.
    iExists In, Cn. iFrame "∗". iIntros "H". by iModIntro.
  Qed.
  
  Lemma unlockNode_spec_high γ_I γ_f γ_k γ_i γ_h r n In Cn :
    ⊢ nodePred γ_f γ_h γ_k n In Cn
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h r C >>>
           unlockNode #n @ ⊤
         <<< CSS γ_I γ_f γ_k γ_i γ_h r C, RET #() >>>.
  Proof.
    iIntros "Hn". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "Hcss".
    iPoseProof (CSS_fold with "[$Hn] [$Hcss]") as "(Hlock & Hn & Hcss')".
    iAaccIntro with "Hlock".
    { iIntros "Hlock". iModIntro.
      iPoseProof ("Hcss'" with "[Hlock]") as "Hcss"; first eauto with iFrame.
      iFrame "Hcss". iIntros "AU". iModIntro. by iFrame. 
    }
    iIntros "Hlock". iModIntro.
    iPoseProof ("Hcss'" with "[Hlock Hn]") as "Hcss"; first eauto with iFrame.
    iFrame "∗". iIntros "H". by iModIntro.
 Qed.

  (** Proofs of traverse and CSSOp *)

  Lemma traverse_spec γ_I γ_f γ_k γ_i γ_h (r: Node) (k: K) (n: Node) :
    ⊢ ⌜k ∈ KS⌝ -∗ inFP γ_f n -∗ inInr γ_i k n -∗
        <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h r C >>>
            traverse #n #k @ ⊤
        <<< ∃ (n': Node) (In': inset_flowint_ur K) (Cn': gset K),
            CSS γ_I γ_f γ_k γ_i γ_h r C
            ∗ nodePred γ_f γ_h γ_k n' In' Cn'
            ∗ ⌜in_inset K k In' n'⌝ ∗ ⌜¬in_outsets K k In'⌝,
            RET #n'
        >>>.
  Proof.
    iLöb as "IH" forall (n). iIntros "% #Hinfp #Hininr".
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply lockNode_spec_high; first done.
    (* Open AU to get lockNode pre *)
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C) "Hcss".
    iAaccIntro with "Hcss".
    { iIntros "H". iModIntro. iFrame. iIntros. iModIntro. iFrame. }
    iIntros (In Cn) "(Hcss & Hnp)". iModIntro.
    (* Before closing AU, use CSS to get findNext pre *)
    iPoseProof (inInr_impl_inset with "[$] [$] [$]")
      as "%".
    (* Close AU and move on *)
    iFrame. iIntros "AU". iModIntro.
    wp_pures.
    iDestruct "Hnp" as "(Hn & HnhIn & HkIn & _ & %)".
    wp_bind (findNext _ _)%E. wp_apply ((findNext_spec n k In Cn) with "[$Hn]").
    { iPureIntro; split; done. }
    iIntros (b n') "(Hn & Hout)". destruct b.
    - (* Case: findNext returns Some n' *)
      wp_pures. wp_bind (unlockNode _).
      iDestruct "Hout" as %Hout.
      (* Fold nodePred again *)
      iAssert (nodePred γ_f γ_h γ_k n In Cn)%I
        with "[$Hn $HnhIn $HkIn $Hinfp]" as "Hnp"; first by iPureIntro.
      (* Get traverse's pre before giving up (node n) when calling unlock *)
      iApply fupd_wp. clear C. iMod "AU" as (C) "[Hcss [Hclose _]]".
      iMod (ghost_update_step with "[$] [$] [% //] [% //]")
        as "(Hcss & Hnp & #Hinfp' & #Hininr')".
      (* Close AU after getting traverse's pre *)
      iMod ("Hclose" with "Hcss") as "AU". clear C. iModIntro.
      awp_apply (unlockNode_spec_high with "Hnp").
      (* Open AU for unlockNode's pre *)
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C) "Hcss".
      iAaccIntro with "Hcss".
      { iIntros. iModIntro. iFrame. iIntros "AU". iModIntro. iFrame. }
      (* The last line should really be a tactic.. *)
      iIntros "Hcss". iModIntro.
      (* Close up AU again *)
      iFrame. iIntros "AU". iModIntro. 
      wp_pures. iSpecialize ("IH" $! n').
      iApply ("IH" with "[% //] [$] [$]"). done.
    - (* Case: findNext returns None *)
      (* Open AU and commit *)
      iApply fupd_wp. clear C. iMod "AU" as (C) "[Hcss [_ Hclose]]".
      iSpecialize ("Hclose" $! n In Cn).
      iAssert (nodePred γ_f γ_h γ_k n In Cn)%I
        with "[$Hn $HnhIn $HkIn $Hinfp]" as "Hnp"; first by iPureIntro.
      iMod ("Hclose" with "[$Hcss $Hnp $Hout]") as "HΦ"; first by iPureIntro.
      iModIntro. wp_pures. done.
  Qed.

  (** Verification of abstract specification of the search structure operation. *)
    
  Theorem CSSOp_spec (γ_I γ_f γ_k: gname) γ_i γ_h r (k: K) (dop: dOp):
    ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h r C >>>
      CSSOp dop r #k @ ⊤
    <<< ∃ C' (res: bool), CSS γ_I γ_f γ_k γ_i γ_h r C'
        ∗ (Ψ dop k C C' res : iProp), RET #res >>>.
  Proof.
    iIntros "%" (Φ) "AU". iLöb as "IH". wp_lam.
    (* Open AU for traverse's pre *)
    iApply fupd_wp. iMod "AU" as (?) "[Hcss [Hclose _]]".
    iMod (ghost_update_root with "[$] [% //]") as "(Hcss & ? & ?)".
    iMod ("Hclose" with "[$] ") as "AU".
    iModIntro. wp_bind (traverse _ _)%E.
    awp_apply (traverse_spec with "[% //] [$] [$]").
    (* Open AU for traverse's atomic pre *)
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (?) "Hcss".
    iAaccIntro with "Hcss"; first by eauto with iFrame.
    (* Get traverse's post and close AU *)
    iIntros (n In Cn) "(Hcss & Hnp & Hinset & Hnotout)".
    iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
    iModIntro. iFrame. iIntros "AU". iModIntro.
    (* Execute decisiveOp *)
    wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Hnp" as "(Hn & HnhIn & HkIn & #Hinfp & domIn)".
    wp_apply (decisiveOp_spec with "[$Hn]"); first by iPureIntro.
    iIntros (b res Cn'). iIntros "(Hn & Hb)". destruct b.
    - (* Case: decisiveOp succeeds *)
      iDestruct "Hb" as "#HΨ".
      wp_pures. wp_bind(unlockNode _)%E.
      (* Note: cannot use unlockNode_spec_high here because 
         that needs nodePred, which we won't have until we linearize,
         which we can't do until we open the AU.
         We can't open the AU before unlockNode, because linearizing will
         mean committing the AU and giving up CSS (needed by unlockNode).
         So we manually execute unlockNode_spec and linearize simultaneously.
         TODO: would it work if nodePred was inside atomic pre of lockNode?
       *)
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done.
      iIntros (C) "Hcss".
      (* Now unfold CSS to execute unlockNode *)
      iPoseProof (CSS_unfold_node with "[$] [$] [$] [$]")
        as (I) "(Hn & HhIn & Hg & Hlock & Hns & Hcss')".
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro.
        iPoseProof ("Hcss'" with "[Hg Hlock Hns]") as "Hcss";
          first eauto with iFrame.
        iFrame "Hcss". iIntros "AU". iModIntro. iFrame "∗".
      }
      iIntros "Hlock". (* unlockNode finished executing *)
      (* Linearization Point *)
      iDestruct "Hg" as "(HI & Hglob & Hks & Hdom)".
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C)
              with "[HkIn Hks]") as (C') "(#HΨC & Hks & HkIn)".
      {
        iPoseProof (keyset_valid with "HkIn") as "%".
        assert (k ∈ keyset K In n); first by apply keyset_def.
        iPoseProof ((Ψ_impl_C_in_K _ _ _ _ _ (keyset K In n))
                      with "[$HΨ] [% //] [% //]") as "%".
        iFrame "∗ #". by iPureIntro.
      }
      (* Close everything up, return *)
      iModIntro. iExists C', res. iSpecialize ("Hcss'" $! C').
      iPoseProof ("Hcss'" with "[-]") as "Hcss".
      { iFrame "∗". iExists false, In. iFrame. iExists Cn'. iFrame "∗ #". }
      iFrame "Hcss HΨC". iIntros "H". iModIntro. wp_pures. done.
    - (* Case: decisiveOp fails *)
      wp_pures. iDestruct "Hb" as "%". subst Cn'.
      iAssert (nodePred γ_f γ_h γ_k n In Cn)%I
        with "[$Hn $HnhIn $HkIn $Hinfp $domIn]" as "Hnp".
      awp_apply (unlockNode_spec_high with "Hnp").
      (* Open AU for unlockNode's pre *)
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C) "Hcss".
      iAaccIntro with "Hcss".
      { iIntros. iModIntro. iFrame. iIntros "AU". iModIntro. iFrame. }
      iIntros "Hcss". iModIntro.
      (* Close up AU again *)
      iFrame. iIntros "AU". iModIntro. 
      wp_pures. by iApply "IH".
  Qed.

End Link_Template.

