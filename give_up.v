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
    iIntros "HFp". iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind(getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "H". iDestruct "H" as %Hloc.
    wp_pures. wp_bind (CmpXchg _ _ _)%E.
    iMod "AU" as (C) "[HInv HAU]".
    iDestruct "HInv" as (I) "(H●I & Hglob & H●k & H●f & Hbigstar)".
    unfold inFP. iDestruct "HFp" as (N0) "(#H◯f & n_in_N)".
    iDestruct "n_in_N" as %n_in_N.
    iPoseProof ((auth_own_incl γ_f (domm I) N0) with "[$]") as "%".
    apply gset_included in H0.
    assert (n ∈ domm I) as n_in_I by set_solver.
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "Hbigstar" as "(Hn & Hbigstar)".
    iDestruct "Hn" as (b In) "(Hlock & Hb)".
    iEval (rewrite <-Hloc). destruct b.
    - wp_cmpxchg_fail. iDestruct "HAU" as "[HAU _]".
      iMod ("HAU" with "[-Hb]") as "H". iExists I.
      iFrame "∗". iApply "Hbigstar". iExists true, In. iFrame.
      iModIntro. wp_pures. iApply "IH".
      iExists N0. iFrame "# %". done.
    - wp_cmpxchg_suc. iDestruct "HAU" as "[_ HAU]".
      iDestruct "Hb" as (Cn) "HN".
      iMod ("HAU" with "[-IH]") as "HΦ". iFrame.
      iExists I. iFrame "∗". iApply "Hbigstar". 
      iExists true, In. iFrame "∗".
      iModIntro. wp_pures. done.
  Qed.
  
  Lemma unlockNode_spec_high (γ_I γ_f γ_k : gname) root n I_n C_n :
    ⊢ nodePred γ_I γ_k n I_n C_n -∗ <<< ∀ C, CSS γ_I γ_f γ_k root C >>>
                                              unlockNode #n @ ⊤
                                      <<< CSS γ_I γ_f γ_k root C, RET #() >>>.
  Proof.
    iIntros "HN". iIntros (Φ) "AU". wp_lam.
    wp_bind(getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "Hloc". iDestruct "Hloc" as %Hloc.
    wp_let. iMod "AU" as (C) "[HInv [_ Hclose]]".
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
    iEval (rewrite <-Hloc).
    wp_store. iMod ("Hclose" with "[Hnode H◯k H◯I H●I Hglob H●k H●f Hlock Hb Hbigstar]") as "HΦ".
    iExists I. iFrame "∗". iApply "Hbigstar".
    iExists false, I_n. iFrame. destruct b.
    iExists C_n. iFrame "∗ %". iDestruct "Hb" as (Cn') "HN'".
    unfold nodePred.
    iDestruct "HN'" as "(Hnode' & _)". 
    iExFalso. iApply node_sep_star. iFrame. 
    iModIntro. done.
 Qed.

  (** Proofs of traverse and CSSOp *)

  Lemma traverse_spec (γ_I γ_f γ_k: gname) (k: K) (root n: Node):
   ⊢ ⌜k ∈ KS⌝ ∗ inFP γ_f n -∗
     <<< ∀ C, CSS γ_I γ_f γ_k root C >>>
       traverse root #n #k @ ⊤
     <<< ∃ (n': Node) (I_n': inset_flowint_ur K) (C_n': gset K),
        CSS γ_I γ_f γ_k root C ∗ inFP γ_f n'
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
  Admitted.
(*  
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
*)
End Give_Up_Template.
