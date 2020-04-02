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

  Parameter findNext : val.
  Parameter decisiveOp : (dOp → val).

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

  Definition nodePred γ_h γ_k n I_n C_n : iProp :=
    node n I_n C_n ∗ own (γ_h n) ((●{1/2} I_n))
      ∗ own γ_k (◯ prod (keyset K I_n n, C_n)) ∗ ⌜domm I_n = {[n]}⌝.

  Definition CSS γ_I γ_f γ_k γ_i γ_h root C : iProp :=
    (∃ I, own γ_I (● I) ∗ ⌜globalinv K root I⌝
        ∗ own γ_k (● prod (KS, C))
        ∗ own γ_f (● domm I)
        ∗ ([∗ set] n ∈ (domm I), (∃ (b: bool) (I_n: inset_flowint_ur K),
            (lockLoc n) ↦ #b
            ∗ (if b then True
               else (∃ C_n, nodePred γ_h γ_k n I_n C_n))
            ∗ own γ_I (◯ I_n)
            ∗ own (γ_h n) ((●{1/2} I_n))
            ∗ ⌜domm I_n = {[n]}⌝ (* TODO Can this be removed? *)
            ∗ own (γ_i n) (● (inset K I_n n))))
    )%I.

  (** Some useful lemmas *)
  
  Lemma CSS_unfold γ_I γ_f γ_k γ_i γ_h root C n :
    inFP γ_f n ∗ CSS γ_I γ_f γ_k γ_i γ_h root C
    -∗ (∃ (I_n: inset_flowint_ur K),
          (∃ (b: bool), lockLoc n ↦ #b
          ∗ (if b then True else (∃ C_n, nodePred γ_h γ_k n I_n C_n)))
        ∗ ((∃ (b: bool), lockLoc n ↦ #b
             ∗ (if b then True else (∃ C_n, nodePred γ_h γ_k n I_n C_n)))
           -∗ CSS γ_I γ_f γ_k γ_i γ_h root C)).
  Proof.
    iIntros "(#Hfp & Hcss)".
    iDestruct "Hcss" as (I) "(HI & Hglob & Hks & Hdom & Hbigstar)".
    iDestruct "Hfp" as (N) "(#Hdom' & n_in_N)". iDestruct "n_in_N" as %n_in_N.
    iPoseProof ((auth_own_incl γ_f (domm I) N) with "[$]") as "#N_incl".
    iDestruct "N_incl" as %N_incl.
    apply gset_included in N_incl.
    assert (n ∈ domm I) as n_in_I by set_solver.
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)".
    iDestruct "Hn" as (b In) "(Hlock & Hb & HIn & HhIn & HdomIn & Hins)".
    iExists In. iSplitL "Hlock Hb".
    - iExists b. by iFrame "∗".
    - iIntros "Hn".  clear b. iDestruct "Hn" as (b) "(Hn & Hite)". 
      iExists I. iFrame "∗". iApply "Hbigstar".
      iExists b, In. auto with iFrame. 
  Qed.

  Lemma CSS_fold γ_I γ_f γ_k γ_i γ_h root C n I_n C_n :
    nodePred γ_h γ_k n I_n C_n ∗ CSS γ_I γ_f γ_k γ_i γ_h root C
    -∗ (lockLoc n ↦ #true ∗ nodePred γ_h γ_k n I_n C_n
        ∗ ((∃ (b: bool), lockLoc n ↦ #b
             ∗ (if b then True else (∃ C_n, nodePred γ_h γ_k n I_n C_n)))
           -∗ CSS γ_I γ_f γ_k γ_i γ_h root C)).
  Proof.
    iIntros "(Hn & Hcss)".
    iDestruct "Hcss" as (I) "(HI & Hglob & Hks & Hdom & Hbigstar)".
    iDestruct "Hn" as "(Hnode & ? & ? & domIn)".
    iDestruct "domIn" as %domIn.
    (* TODO CONTINUE: either thread inFP through the proof or put the frac singleton interface inside nodePred *)
    iPoseProof ((auth_own_incl γ_I (I) (I_n)) with "[$]") as "%".
    rename H0 into I_incl. destruct I_incl as [Io I_incl].
    iPoseProof (own_valid with "H●I") as "%". rename H0 into Valid_I.
    assert (n ∈ domm I) as n_in_I.
    { rewrite I_incl. rewrite flowint_comp_fp.
      rewrite domIn. set_solver. rewrite <- I_incl.
      by apply auth_auth_valid. } 
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)".
    iDestruct "Hn" as (b In) "(Hlock & Hb)".
    iEval (rewrite <-Hloc).
    wp_store. iMod ("Hclose" with "[Hnode H◯k H◯I H●I Hglob H●k H●f Hlock Hb Hbigstar]") as "HΦ".
    iExists I. iFrame "∗". iApply "Hbigstar".
    iExists false, I_n. iFrame. destruct b.
    iExists C_n. iFrame "∗ %". iDestruct "Hb" as (Cn') "Hn'".
    unfold nodePred.
    iDestruct "Hn'" as "(Hnode' & _)". 
    iExFalso. iApply node_sep_star. iFrame. 
    iModIntro. done.


  Admitted.
    

  (** High-level lock specs *)

  Lemma lockNode_spec_high γ_I γ_f γ_k γ_i γ_h root n :
    ⊢ inFP γ_f n
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h root C >>>
           lockNode #n @ ⊤
         <<< ∃ I_n C_n, CSS γ_I γ_f γ_k γ_i γ_h root C
                      ∗ nodePred γ_h γ_k n I_n C_n,
             RET #() >>>.
  Proof.
    iIntros "#HFp". iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "HCSS".
    iPoseProof (CSS_unfold with "[$HFp $HCSS]") as (In) "(Hn & HCSS')".
    iDestruct "Hn" as (b) "(Hlock & Hn)".
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro.
      iPoseProof ("HCSS'" with "[Hlockn Hn]") as "HCSS"; first eauto with iFrame.
      iFrame "HCSS". iIntros "AU". by iModIntro.
    }
    iIntros "(Hlockn & %)". iModIntro.
    subst b. iDestruct "Hn" as (Cn) "Hn".
    iPoseProof ("HCSS'" with "[Hlockn]") as "HCSS"; first eauto with iFrame.
    iExists In, Cn. 
    iFrame "∗". iIntros "H". by iModIntro.
  Qed.
  
  Lemma unlockNode_spec_high γ_I γ_f γ_k γ_i γ_h root n I_n C_n :
    ⊢ nodePred γ_h γ_k n I_n C_n
      -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h root C >>>
           unlockNode #n @ ⊤
         <<< CSS γ_I γ_f γ_k γ_i γ_h root C, RET #() >>>.
  Proof.
    iIntros "Hn". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "HCSS".
    iPoseProof (CSS_fold with "[$Hn $HCSS]") as "(Hlock & Hn & HCSS')".
    iAaccIntro with "Hlock".
    { iIntros "Hlock". iModIntro.
      iPoseProof ("HCSS'" with "[Hlock]") as "HCSS"; first eauto with iFrame.
      iFrame "HCSS". iIntros "AU". iModIntro. by iFrame. 
    }
    iIntros "Hlock". iModIntro.
    iPoseProof ("HCSS'" with "[Hlock Hn]") as "HCSS"; first eauto with iFrame.
    iFrame "∗". iIntros "H". by iModIntro.
 Qed.

  (** Proofs of traverse and CSSOp *)

  Lemma traverse_spec (γ_I γ_f γ_k: gname) (γ_i γ_h: Node → gname)
      (root: Node) (k: K) (n: Node) (Ns: gset Node) (I_n:inset_flowint_ur K):
    ⊢ ⌜k ∈ KS⌝ ∗ ⌜n ∈ Ns⌝ ∗ own γ_f (◯ Ns)
      ∗ own (γ_i n) (◯ (inset K I_n n))
      ∗ ⌜k ∈ inset K I_n n⌝ -∗
        <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h root C >>>
            traverse #n #k @ ⊤
        <<< ∃ (n': Node) (Ns': gsetUR Node) (I_n': inset_flowint_ur K) (Cn': gset K),
            CSS γ_I γ_f γ_k γ_i γ_h root C ∗ ⌜n' ∈ Ns'⌝
            ∗ own γ_f (◯ Ns') ∗ node n' I_n' Cn' ∗ own (γ_h n') ((●{1/2} I_n'))
            ∗ own γ_k (◯ prod (keyset K I_n' n', Cn')) ∗ ⌜domm I_n' = {[n']}⌝
            ∗ ⌜in_inset K k I_n' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns I_n). iIntros "(#Hkks & #Hinn & #Hfp & #Hinrfp & #Hkinr)".
    iDestruct "Hinn" as %Hinn.
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n). iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "Hst". iDestruct "Hst" as (I) "(HI & HKS & HNDS & Hglob & Hstar)".
    iAssert (⌜n ∈ domm I⌝)%I with "[HNDS]" as "%".
    { iPoseProof ((auth_own_incl γ_f (domm I) Ns) with "[$]") as "%".
      apply gset_included in H0.
      iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b In) "(Hlock & Hb & HIn & #HNds & Hfis & Hks)".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitL. iFrame "∗ % #".
    iExists I. iFrame "∗ % #". iApply "Hstar". iExists b, In.
    iFrame "# % ∗". eauto with iFrame. } iIntros "(Hloc & %)".
    destruct b. { iExFalso. done. } iModIntro. clear H1.
    iPoseProof ((auth_own_incl (γ_i n) (inset K In n) (inset K I_n n)) with "[$Hks $Hinrfp]") as "%".
    apply gset_included in H1.
    iDestruct "Hkinr" as "%".
    assert (k ∈ inset K In n) as Hkinr; first by set_solver.
    iPoseProof (own_valid with "HIn") as "%". rename H3 into HInV.
    assert (✓ In) as HInv. { apply (auth_frag_valid (◯ In)). done. }
    iSplitR "Hb". iFrame "∗ % #". iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In.
    iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (Cn) "(Hrep & Hfil & Hks)". iDestruct "HNds" as %HNds.
    wp_bind (findNext _ _)%E. wp_apply ((findNext_spec n k In Cn) with "[Hrep]").
    iDestruct "Hkks" as "%".
    iFrame; iPureIntro; split; done. iIntros (b n') "(Hrep & Hb)". destruct b.
    - wp_pures. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
      iDestruct "Hst" as (I1) "(HI & HKS & HNDS & Hglob & Hstar)".
      iAssert (⌜n ∈ domm I1⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_own_incl γ_f (domm I1) Ns) with "[$]") as "%".
        apply gset_included in H3.
        iPureIntro. set_solver. }
      rewrite (big_sepS_delete _ (domm I1) n); last by eauto. iDestruct "Hstar" as "(Hcln & Hstar)".
      iDestruct "Hcln" as (b In1) "(Hlock & Hbb & HIn & #HNds1 & Hfis & Hks1)".
      destruct b; first last. { iDestruct "Hbb" as (Cn') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In1).
      iFrame. } exfalso. done. }
      iPoseProof ((own_valid_2 (γ_h n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H4. apply leibniz_equiv in H4. replace In1.
      iDestruct "Hb" as %Hb. iDestruct "HNds1" as %HNds1. iDestruct "Hglob" as %Hglob.
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof (own_valid with "HI") as "%". iAssert (⌜n' ∈ domm I1⌝)%I as "%".
      { iPureIntro. assert (n' ∈ domm I2).
        { apply (flowint_step I1 In I2 k n' root); try done. }
        assert (domm I1 = domm In ∪ domm I2).
        { rewrite H5. apply flowint_comp_fp.
          rewrite H5 in H6 * => H6.
          rewrite <-H5.
          apply auth_auth_valid.
          rewrite <-H5 in H6. done.
        }
        rewrite H8.
        set_solver. }
      (* apply Hglob. } *)
      assert (n ≠ n') as Hneq.
      { assert (n' ∉ domm In).
        { apply (outset_distinct In n').
          split. done.
          exists k. done. }
        rewrite HNds1 in H8. set_solver. }
      rewrite (big_sepS_delete _ (domm I1 ∖ {[n]}) n'); last first.
      set_solver. iDestruct "Hstar" as "(Hcln' & Hstar)".
      iDestruct "Hcln'" as (b In') "(Hlock' & Hbb' & HIn' & #HNds' & Hfis' & Hks1')".
      iPoseProof ((own_op γ_I (◯ In) (◯ In' )) with "[HIn HIn']") as "H"; first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H8.
      assert (✓ (In ⋅ In')). { apply (auth_frag_valid (◯ (In ⋅ In'))). done. }
      iDestruct "HNds'" as %HNds'.
      assert (k ∈ inset K In' n').
      {
        apply (flowint_inset_step In In' k n'). done. set_solver.
        unfold in_outset in Hb. done.
      }
      assert (root ∈ domm I1). { apply globalinv_root_fp. done. } iDestruct "H" as "(HIn & HIn')".
      iMod (own_update (γ_i n') _
                       (● (inset K In' n')
                          ⋅ ◯ (inset K In' n'))
              with "Hks1'") as "HNs".
      apply auth_update_core_id.
      apply gset_core_id. done. iDestruct "HNs" as "(Hks1' & #Hinr1')".
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hks Hrep". iFrame "∗ # %".
      iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (domm I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists true, In. iFrame "# % ∗".
      rewrite (big_sepS_delete _ (domm I1 ∖ {[n]}) n'); last first. set_solver. iFrame. iExists b, In'.
      iFrame "# % ∗".  iIntros "AU". iModIntro. iFrame "# % ∗". } iIntros "Hlock".
      iMod (own_update γ_f (● domm I1) (● domm I1 ⋅ ◯ domm I1) with "HNDS") as "HNs".
      apply auth_update_core_id. apply gset_core_id. done. iDestruct "HNs" as "(HAfp & #Hfp1)".
      iModIntro. iSplitL. iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (domm I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists false, In. iFrame "# % ∗". iExists Cn. iFrame.
      rewrite (big_sepS_delete _ (domm I1 ∖ {[n]}) n'); last first. set_solver. iFrame. iExists b, In'.
      iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures. iSpecialize ("IH" $! n' (domm I1) In').
      iApply "IH". iFrame "∗ # %". done.
    - iApply fupd_wp. iMod "AU" as (C) "[Hst [_ Hclose]]". iSpecialize ("Hclose" $! n Ns In Cn).
      iMod ("Hclose" with "[Hst Hfil Hks Hrep Hb]") as "HΦ". iDestruct "Hb" as %Hnotout.
      iFrame "∗ # %". iModIntro. wp_pures. done.
  Qed.

  (** Verification of abstract specification of the search structure operation. *)
  
  Theorem CSSOp_spec (γ_I γ_f γ_k: gname) γ_i γ_h root (k: K) (dop: dOp):
    ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ_I γ_f γ_k γ_i γ_h root C >>>
      CSSOp dop root #k @ ⊤
    <<< ∃ C' (res: bool), CSS γ_I γ_f γ_k γ_i γ_h root C'
        ∗ (Ψ dop k C C' res : iProp), RET #res >>>.
  Proof.
    iIntros "HKin" (Φ) "AU". iLöb as "IH". wp_lam.
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I0) "(HI & HKS & HNDS & #Hglob & Hstar)".
    iDestruct "Hglob" as %Hglob. iDestruct "HKin" as %HKin.
    assert (root ∈ domm I0)%I as Hroot. { apply globalinv_root_fp. done. }
    iMod (own_update γ_f (● domm I0) (● domm I0 ⋅ ◯ domm I0) with "HNDS") as "H".
    { apply auth_update_core_id. apply gset_core_id. done. }
    iDestruct "H" as "(HNDS & #Hfp0)".
    rewrite (big_sepS_elem_of_acc _ (domm I0) root); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b Ir) "(H1 & H2 & H3 & H4 & H5 & Hksr)".
    iPoseProof (auth_own_incl with "[$HI $H3]") as "%". iDestruct "H4" as %HNdsr.
    iMod (own_update (γ_i root) _
                     (● (inset K Ir root)
                      ⋅ ◯ (inset K Ir root))
            with "Hksr") as "H".
    apply auth_update_core_id. apply gset_core_id. done. iDestruct "H" as "(Hksr & #Hinr)".
    iMod ("HAU" with "[HI HKS H1 H2 H3 H5 Hstar HNDS Hksr] ") as "AU".
    { iExists I0. iFrame "∗ % #". iApply "Hstar". iExists b, Ir. iFrame "∗ # %". }
    iModIntro. wp_bind (traverse _ _)%E.
    awp_apply (traverse_spec γ_I γ_f γ_k γ_i γ_h root k root (domm I0) Ir). iFrame "∗ # %".
    iPureIntro. apply (globalinv_root_ins I0 Ir root k); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "Hst". iAaccIntro with "Hst"; first by eauto with iFrame.
    iIntros (n Ns In Cn) "(Hst & #Hinn & #Hfp & Hrepn & Hfil & Hks & #HNdsn & #Hinset & #Hnotout)".
    iDestruct "Hinn" as %Hinn. iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hrepn]"). eauto with iFrame.
    iIntros (b' res Cn'). iIntros "Hb". destruct b'.
    - iDestruct "Hb" as "(Hrep & #HΨ)".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(HI & HKS & HNDS & #Hglob & Hstar)".
      iDestruct "Hglob" as %Hglob'.
      iAssert (⌜n ∈ domm I⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_own_incl γ_f (domm I) Ns) with "[$]") as "%".
        apply gset_included in H1.
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
      iPoseProof ((own_valid γ_I (● I)) with "HI") as "%".
      iPoseProof ((own_valid_2 (γ_h n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H4. apply leibniz_equiv in H4. replace In1.
      iPoseProof ((own_valid γ_I (◯ In)) with "HIn") as "%". rename H5 into HInV.
      assert (✓ In) as HInv. { apply (auth_frag_valid (◯ In)). done. }    
      iPoseProof (own_valid with "Hks") as "%". rename H5 into HvldCn.
      rewrite auth_frag_valid in HvldCn *; intros HvldCn. unfold valid, cmra_valid in HvldCn.
      simpl in HvldCn. unfold ucmra_valid in HvldCn. simpl in HvldCn.
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C2) with "[HKS Hks]") as "Hgks".
      assert (k ∈ keyset K In n). apply keyset_def; try done. iFrame "% ∗ #".
      iEval (unfold Ψ) in "HΨ".
      { destruct dop.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. subst Cn'. done.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver. }
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
      { iPoseProof ((auth_own_incl γ_f (domm I) Ns) with "[$]") as "%".
        apply gset_included in H1.
      iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
      iDestruct "Hstar" as "[Hn Hstar]".
      iDestruct "Hn" as (b' In1) "(Hlock & Hb' & HIn & #HNds & Hfis & Hinreach)".
      destruct b'; first last.
      { iDestruct "Hb'" as (Cn'') "(Hrep' & _)".
        iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf.
        { iDestruct "Hb" as "(Hrep & %)".
          iApply (node_sep_star n In In1).
          iFrame "∗ # %". }
        exfalso. done. }
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro. iSplitR "Hfil Hb Hks".
        iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In1.
        iFrame "∗ # %". eauto with iFrame. }
      iIntros "Hlock". iModIntro.
      iPoseProof ((own_valid_2 (γ_h n) (●{1 / 2} In) (●{1 / 2} In1))
                    with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H2.
      apply leibniz_equiv in H2. replace In1.
      iSplitR "". iExists I.
      iDestruct "Hb" as "(Hb & %)". subst Cn'.
      iFrame "∗ % #". iApply "Hstar". iExists false, In. iFrame "∗ % #".
      iExists Cn. iFrame. iIntros "AU". iModIntro. wp_pures.
      iApply "IH"; try done.
  Qed.

End Link_Template.
