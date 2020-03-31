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

  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !(@keysetG K _ _) Σ}.
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

  Definition inFP γ_f n : iProp := ∃ (N: gset Node), own γ_f (◯ N) ∗ ⌜n ∈ N⌝.

  Definition nodePred γ_I γ_k n I_n C_n  :iProp := node n I_n C_n ∗ own γ_k (◯ prod (keyset K I_n n, C_n))
                                                 ∗ own γ_I (◯ I_n) ∗ ⌜domm I_n = {[n]}⌝.

  Definition CSS (γ_I γ_f γ_k : gname) root (C: gset K) : iProp :=
    ∃ I, own γ_I (● I) ∗ ⌜globalinv K root I⌝ 
       ∗ own γ_k (● prod (KS, C))
       ∗ own γ_f (● domm I) 
       ∗ ([∗ set] n ∈ (domm I), (∃ (b: bool) (I_n: inset_flowint_ur K),
            ((lockLoc n) ↦ #b ∗ if b then True 
                               else (∃ (C_n: gset K), nodePred γ_I γ_k n I_n C_n)))).
    
  (** High-level lock specs **)

  Lemma lockNode_spec_high (γ_I γ_f γ_k : gname) root n :
    ⊢ inFP γ_f n -∗ <<< ∀ C, CSS γ_I γ_f γ_k root C >>>
                             lockNode #n @ ⊤
                    <<< ∃ I_n C_n, CSS γ_I γ_f γ_k root C ∗ nodePred γ_I γ_k n I_n C_n, RET #() >>>.
  Proof.
    iIntros "HFp". iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "HInv".
    iDestruct "HInv" as (I) "(H●I & Hglob & H●k & H●f & Hbigstar)".
    unfold inFP. iDestruct "HFp" as (N0) "(#H◯f & n_in_N)".
    iDestruct "n_in_N" as %n_in_N.
    iPoseProof ((auth_own_incl γ_f (domm I) N0) with "[$]") as "%".
    apply gset_included in H0.
    assert (n ∈ domm I) as n_in_I by set_solver.
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)".
    iDestruct "Hn" as (b In) "(Hlock & Hb)".
    iAaccIntro with "Hlock".
    { iIntros. iModIntro. iSplitL.
      iExists I. iFrame "∗". iApply "Hbigstar".
      iExists b, In. iFrame. iIntros. iModIntro. 
      iFrame. iExists N0. iFrame "# %". }
    iIntros "(Hlock & %)". subst b.
    iModIntro. iDestruct "Hb" as (Cn) "NodePred". 
    iExists In, Cn. iSplitL.
    iFrame. iExists I. iFrame. iApply "Hbigstar".
    iExists true, In. iFrame.
    iIntros; iModIntro; done.
  Qed.
  
  Lemma unlockNode_spec_high (γ_I γ_f γ_k : gname) root n I_n C_n :
    ⊢ nodePred γ_I γ_k n I_n C_n -∗ <<< ∀ C, CSS γ_I γ_f γ_k root C >>>
                                              unlockNode #n @ ⊤
                                      <<< CSS γ_I γ_f γ_k root C, RET #() >>>.
  Proof.
    iIntros "HN". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (C) "HInv".
    iDestruct "HInv" as (I) "(H●I & Hglob & H●k & H●f & Hbigstar)".
    iDestruct "HN" as "(Hnode & H◯k & H◯I & Dom_In)".
    iDestruct "Dom_In" as %Dom_In.
    iPoseProof ((auth_own_incl γ_I (I) (I_n)) with "[$]") as "%".
    rename H0 into I_incl. destruct I_incl as [Io I_incl].
    iPoseProof (own_valid with "H●I") as "%". rename H0 into Valid_I.
    assert (n ∈ domm I) as n_in_I.
    { rewrite I_incl. rewrite flowint_comp_fp.
      rewrite Dom_In. set_solver. rewrite <- I_incl.
      by apply auth_auth_valid. } 
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)".
    iDestruct "Hn" as (b In) "(Hlock & Hb)".
    destruct b; last first.
    { iDestruct "Hb" as (Cn) "HN'".
    iDestruct "HN'" as "(Hnode' & _)".
    iExFalso. iApply node_sep_star.
    iFrame "Hnode Hnode'". }
    iAaccIntro with "Hlock".
    { iIntros "Hlock". iModIntro. iSplitR "Hnode H◯k H◯I".
      iExists I. iFrame "∗". iApply "Hbigstar".
      iExists true, In. iFrame "Hlock". iIntros. iModIntro. 
      iFrame "∗ %". }
    iIntros "Hlock". iModIntro. iSplitL.
    iExists I. iFrame "∗". iApply "Hbigstar".
    iExists false, I_n. iFrame.
    iExists C_n. iFrame "∗ # %".
    iIntros; iModIntro; done.
  Qed.

  (** Proofs of traverse and CSSOp *)

  Lemma traverse_spec (γ_I γ_f γ_k: gname) (k: K) (root n: Node):
   ⊢ ⌜k ∈ KS⌝ ∗ inFP γ_f n -∗
     <<< ∀ C, CSS γ_I γ_f γ_k root C >>>
       traverse root #n #k @ ⊤
     <<< ∃ (n': Node) (I_n': inset_flowint_ur K) (C_n': gset K),
          CSS γ_I γ_f γ_k root C
        ∗ nodePred γ_I γ_k n' I_n' C_n' 
        ∗ ⌜in_inset K k I_n' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n). iIntros "(#Hks & #Hfp)".
    iDestruct "Hks" as %k_in_KS.
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec_high γ_I γ_f γ_k root n); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "HInv". iAaccIntro with "HInv".
    { iIntros "HInv". iModIntro. eauto with iFrame. }
    iIntros (In Cn) "(HInv & Nodepred)".
    iModIntro. iFrame. iIntros "AU". iModIntro.
    wp_pures. wp_bind (inRange _ _)%E.
    iDestruct "Nodepred" as "(Hnode & H◯k & H◯I & Dom_In)".
    iApply fupd_wp. iMod "AU" as (C1) "[HInv [Hclose _]]".
    iDestruct "HInv" as (I) "(H●I & Hglob & H●k & H●f & Hbigstar)".
    iDestruct "Dom_In" as %Dom_In.
    iPoseProof ((auth_own_incl γ_I (I) (In)) with "[$]") as "%".
    rename H0 into I_incl. destruct I_incl as [Io I_incl].
    iPoseProof (own_valid with "H●I") as "%". rename H0 into Valid_I.
    iDestruct "Hglob" as %Hglob.
    iMod (own_update γ_f (● (domm I)) (● (domm I) ⋅ ◯ (domm I)) with "H●f") as "H".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "H" as "(H●f & #H◯_dommI)".
    iMod ("Hclose" with "[H●I H●k H●f Hbigstar]") as "AU".
    iExists I. iFrame "∗ %". iModIntro.    
    wp_apply ((inRange_spec n k In Cn) with "Hnode").
    iIntros (b) "(Hnode & Hb)". destruct b.
    - wp_pures. wp_bind (findNext _ _)%E. iSimpl in "Hb".
      iDestruct "Hb" as %Hinset. specialize (Hinset Coq.Init.Logic.I).
      wp_apply ((findNext_spec n k In Cn) with "[Hnode]"). iFrame "∗ %".
      iIntros (b n') "(Hnode & Hbb)". destruct b.
      + wp_pures. iDestruct "Hbb" as %in_outset.  
        awp_apply ((unlockNode_spec_high γ_I γ_f γ_k root n) with "[-AU]").
        iFrame "∗ %". iApply (aacc_aupd_abort with "AU"); first done.
        iIntros (C2) "HInv". iAaccIntro with "HInv".
        { iIntros "HInv". iModIntro. eauto with iFrame. }
        iIntros "HInv". iModIntro. iFrame. iIntros "AU".
        iModIntro. wp_pures. iApply "IH"; try done. iFrame "%".
        iExists (domm I). iFrame "#". iPureIntro.
        assert (n' ∈ domm Io).
        { apply (flowint_step I In Io k n' root); try done. }
        rewrite I_incl. rewrite intComp_dom. set_solver.
        rewrite <-I_incl. by apply auth_auth_valid.     
      + iDestruct "Hbb" as %not_in_outset.
        iApply fupd_wp. iMod "AU" as (C) "[HInv [_ Hclose]]".
        iSpecialize ("Hclose" $! n In Cn).
        iMod ("Hclose" with "[H◯k H◯I HInv Hnode]").
        iFrame "∗ # %". iModIntro. wp_pures. done.
    - wp_pures. iDestruct "Hb" as %Hnot_in_inset.
      awp_apply ((unlockNode_spec_high γ_I γ_f γ_k root n) with "[-AU]").
      iFrame "∗ # %". iApply (aacc_aupd_abort with "AU"); first done.
      iIntros (C) "HInv". iAaccIntro with "HInv".
      { iIntros. iModIntro. eauto with iFrame. }
      iIntros "HInv". iModIntro. iFrame. iIntros "AU".
      iModIntro. wp_pures. iApply "IH"; try done. iFrame "%".
      iExists (domm I). iFrame "H◯_dommI". iPureIntro.
      unfold globalinv in Hglob. by destruct Hglob as (_ & Hglob & _).
  Qed.

  (** Verification of abstract specification of the search structure operation. *)
  
  (*Instance Ψ_persistent dop (k : K) C C' res : Persistent (Ψ dop k C C' res : iProp).
  Proof. destruct dop; apply _. Qed.*)

  Theorem CSSOp_spec (γ_I γ_f γ_k: gname) root (dop: dOp) (k: K):
   ⊢ ⌜k ∈ KS⌝ -∗ <<< ∀ C, CSS γ_I γ_f γ_k root C >>>
      CSSOp dop root #k @ ⊤
    <<< ∃ C' (res: bool), CSS γ_I γ_f γ_k root C'
        ∗ (Ψ dop k C C' res : iProp), RET #res >>>.
  Proof.
    iIntros "HKin" (Φ) "AU". iLöb as "IH". wp_lam.
    iDestruct "HKin" as %k_in_KS.
    iApply fupd_wp. iMod "AU" as (C0) "[HInv [HAU _]]".
    iDestruct "HInv" as (I0) "(H●I & Hglob & H●k & H●f & Hbigstar)".
    iMod (own_update γ_f (● (domm I0)) (● (domm I0) ⋅ ◯ (domm I0)) with "H●f") as "H".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "H" as "(H●f & #H◯domm)". iDestruct "Hglob" as %Hglob.
    iMod ("HAU" with "[-IH]") as "AU". iExists I0. iFrame "∗ # %".
    iModIntro. wp_bind (traverse _ _ _)%E.
    awp_apply (traverse_spec γ_I γ_f γ_k k root root).
    { iFrame "%". iExists (domm I0). iFrame "#". iPureIntro.
    unfold globalinv in Hglob. by destruct Hglob as (_ & Hglob & _). }
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "HInv". iAaccIntro with "HInv"; first by eauto with iFrame.
    iIntros (n In Cn) "(HInv & Nodepred & % & %)".
    rename H0 into in_inset. rename H1 into not_in_outset. 
    iModIntro. iFrame. iIntros "AU".
    iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    iDestruct "Nodepred" as "(Hnode & H◯k & H◯I & Dom_In)".
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hnode]"). eauto with iFrame.
    iIntros (b res Cn'). iIntros "(Hnode & Hb)". destruct b.
    - iDestruct "Hb" as "#HΨ".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "HInv".
      iDestruct "HInv" as (I2) "(H●I & Hglob & H●k & H●f & Hbigstar)".
      iDestruct "Dom_In" as %Dom_In.
      iPoseProof ((auth_own_incl γ_I (I2) (In)) with "[$]") as "%".
     rename H0 into I_incl. destruct I_incl as [Io I_incl].
      iPoseProof (own_valid with "H●I") as "%". rename H0 into Valid_I.
      assert (n ∈ domm I2) as n_in_I2.
      { rewrite I_incl. rewrite flowint_comp_fp.
        rewrite Dom_In. set_solver. rewrite <- I_incl.
        by apply auth_auth_valid. } 
      rewrite (big_sepS_elem_of_acc _ (domm I2) n); last by eauto.
      iDestruct "Hbigstar" as "(Hn & Hbigstar)".
      iDestruct "Hn" as (b In') "(Hlock & Hb)".
      destruct b; last first.
      { iDestruct "Hb" as (Cn'') "HN'".
      iDestruct "HN'" as "(Hnode' & _)".
      iExFalso. iApply node_sep_star.
      iFrame "Hnode Hnode'". }
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro. iSplitR "Hnode H◯k H◯I".
        iExists I2. iFrame "∗". iApply "Hbigstar".
        iExists true, In. iFrame "Hlock". iIntros. iModIntro. 
        iFrame "∗ %". }
      iIntros "Hlock".
      iPoseProof (own_valid with "H◯I") as "%". rename H0 into Hvldn. 
      iPoseProof (own_valid with "H◯k") as "%". rename H0 into HvldCn.
      rewrite auth_frag_valid in HvldCn *; intros HvldCn. unfold valid, cmra_valid in HvldCn.
      simpl in HvldCn. unfold ucmra_valid in HvldCn. simpl in HvldCn.
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C2) with "[H●k H◯k]") as "Hgks".
      assert (k ∈ keyset K In n) as K_in_ksIn. apply keyset_def; try done.
      iFrame "% ∗ #". iEval (unfold Ψ) in "HΨ".
      { destruct dop.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. subst Cn'. done.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver.
        - iDestruct "HΨ" as %(HΨ & _). iPureIntro. set_solver. }
      iDestruct "Hgks" as (C2') "(#HΨC & H●k & H◯k)".
      iModIntro. iExists (C2'), res. iSplitL. iFrame "HΨC".
      iExists I2. iFrame "∗ % #". iApply "Hbigstar". iExists false, In. iFrame "∗ # %".
      iExists Cn'. iFrame. iIntros. iModIntro. by wp_pures. 
    - wp_match. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "HInv".
      iDestruct "HInv" as (I1) "(H●I & Hglob & H●k & H●f & Hbigstar)".
      iDestruct "Dom_In" as %Dom_In.
      iPoseProof ((auth_own_incl γ_I (I1) (In)) with "[$]") as "%".
     rename H0 into I_incl. destruct I_incl as [Io I_incl].
      iPoseProof (own_valid with "H●I") as "%". rename H0 into Valid_I.
      assert (n ∈ domm I1) as n_in_I1.
      { rewrite I_incl. rewrite flowint_comp_fp.
        rewrite Dom_In. set_solver. rewrite <- I_incl.
        by apply auth_auth_valid. } 
      rewrite (big_sepS_elem_of_acc _ (domm I1) n); last by eauto.
      iDestruct "Hbigstar" as "(Hn & Hbigstar)".
      iDestruct "Hn" as (b In') "(Hlock & HN)".
      destruct b; last first.
      { iDestruct "HN" as (Cn'') "HN'".
      iDestruct "HN'" as "(Hnode' & _)".
      iExFalso. iApply node_sep_star.
      iFrame "Hnode Hnode'". }
      iDestruct "Hb" as %Hb.
      iAaccIntro with "Hlock".
      { iIntros "Hlock". iModIntro. iSplitR "Hnode H◯k H◯I".
        iExists I1. iFrame "∗". iApply "Hbigstar".
        iExists true, In. iFrame "Hlock". iIntros. iModIntro. 
        iFrame "∗ %". }
      iIntros "Hlock". iModIntro. iSplitL.
      iExists I1. iFrame. iApply "Hbigstar".
      iExists false, In. iFrame. iExists Cn.
      replace Cn'. iFrame "∗ % #".
      iIntros "AU". iModIntro. wp_pures.
      iApply "IH"; try done.
  Qed.      

End Give_Up_Template.
