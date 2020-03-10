(** Verification of Give-up template algorithm *)

From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "All".
Require Export keyset_ra inset_flows.

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

  (* RA for authoritative set of nodes *)
  Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR Node)) }.
  Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR Node))].

  Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
  Proof. solve_inG. Qed.

  (* RA for pair of keysets and contents *)
  Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (authUR (keysetUR K)) }.
  Definition keysetΣ : gFunctors := #[GFunctor (authUR (keysetUR K))].

  Instance subG_keysetΣ {Σ} : subG keysetΣ Σ → keysetG Σ.
  Proof. solve_inG. Qed.

End Give_Up_Cameras.

(** Verification of the template *)
Section Give_Up_Template.

  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (** The code of the give-up template. *)

  Inductive dOp := memberOp | insertOp | deleteOp.

  (* The following parameters are the implementation-specific helper functions
   * assumed by the template. See GRASShopper files b+-tree.spl and
   * hashtbl-give-up.spl for the concrete implementations. *)

  Parameter findNext : val.
  Parameter inRange : val.
  Parameter decisiveOp : (dOp → val).
  Parameter lockLoc : Node → loc.
  Parameter getLockLoc : val.

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

  (** Coarse-grained specification *)

  Definition Ψ dop k (C: gsetO K) (C': gsetO K) (res: bool) : iProp :=
    match dop with
    | memberOp => (⌜C' = C ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    | insertOp => (⌜C' = union C {[k]} ∧ (if res then k ∉ C else k ∈ C)⌝)%I
    | deleteOp => (⌜C' = difference C {[k]} ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    end.

  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.

  (** Helper functions specs *)

  (* Todo: we can also try to get rid of getLockLoc and just do CAS (lockLoc "l") #true #false in lock, etc. *)
  Parameter getLockLoc_spec : ∀ (n: Node),
    ({{{ True }}}
      getLockLoc #n
    {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  (* The following functions are proved for each implementation in GRASShopper
   * (see b+-tree.spl and hashtbl-give-up.spl) *)

  Parameter inRange_spec : ∀ (n: Node) (I_n : inset_flowint_ur K) (C: gset K) (k: K),
    ({{{ node n I_n C }}}
      inRange #n #k
    {{{ (b: bool), RET #b; node n I_n C
      ∗ (match b with true => ⌜in_inset K k I_n n⌝ |
                     false => ⌜True⌝ end) }}})%I.

  (* Todo: Can we simplify the match to ⌜b → in_inset k I_n n⌝? *)
  Parameter findNext_spec : ∀ (n: Node) (I_n : inset_flowint_ur K) (C: gset K) (k: K),
    ({{{ node n I_n C ∗ ⌜in_inset K k I_n n⌝ }}}
      findNext #n #k
    {{{ (b: bool) (n': Node),
        RET (match b with true => (SOMEV #n') | false => NONEV end);
        node n I_n C ∗ (match b with true => ⌜in_outset K k I_n n'⌝ |
                                    false => ⌜¬in_outsets K k I_n⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: K)
      (I_n: inset_flowint_ur K) (C: gset K),
    ({{{ node n I_n C ∗ ⌜in_inset K k I_n n⌝
        ∗ ⌜¬in_outsets K k I_n⌝ ∗ ⌜domm I_n = {[n]}⌝ }}}
      decisiveOp dop #n #k
    {{{ (b: bool) (C': gset K) (res: bool),
        RET (match b with false => NONEV | true => (SOMEV #res) end);
        match b with false => node n I_n C |
                      true => node n I_n C' ∗ Ψ dop k C C' res
                              ∗ ⌜ C' ⊆ keyset K I_n n⌝
        end }}})%I.

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

  (** Assorted useful lemmas *)

  Lemma globalinv_root_fp: ∀ I root, globalinv K root I → root ∈ domm I.
  Proof.
    intros I root Hglob. unfold globalinv in Hglob.
    destruct Hglob as [H1 [H2 H3]]. done.
  Qed.

  Lemma auth_set_incl (γ_fp: gname) (Ns: gsetUR Node) Ns' :
    own γ_fp (◯ Ns) ∗ own γ_fp (● Ns') -∗ ⌜Ns ⊆ Ns'⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro.
    rewrite auth_valid_discrete. simpl. rewrite ucmra_unit_right_id_L.
    intros. destruct H. inversion H0 as [m H1].
    destruct H1. destruct H2. apply gset_included in H2.
    apply to_agree_inj in H1. set_solver.
  Qed.

  Lemma auth_own_incl_ks γ (x y: keysetUR K) :
    own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H. destruct H. destruct H0 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y = y) as Hy.
    { rewrite /(⋅) /=. destruct y; try done. }
    rewrite Hy in Hb. rewrite <- Ha in Hb. done.
  Qed.

  Lemma auth_own_incl γ (x y: inset_flowint_ur K) :
    own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H1. destruct H1 as [z H2]. destruct H2 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y ≡ y) as Hy.
    { rewrite intComp_comm.
      unfold flowintRAunit.
      rewrite intComp_unit.
      done.
    }
    (*{ rewrite /(⋅) /=. destruct y; try done. }*)
    rewrite Hy in Hb *. intros Hb. rewrite <- Ha in Hb. done.
  Qed.
  
  (* Try generic version of this lemma... *)
  Lemma auth_own_incl_gen `{authR A} `{inG Σ (authR A)} `{CmraDiscrete A} γ (x y: ucmra_car A) :
    own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H1. destruct H1. destruct H2 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y ≡ y) as Hy by apply ucmra_unit_left_id.
    (*{ rewrite /(⋅) /=. destruct y; try done. }*)
    rewrite Hy in Hb *. intros Hb. rewrite <- Ha in Hb. done.
  Qed.


  (** Lock module proofs *)

  Lemma lockNode_spec (n: Node): (* TODO rewrite if then else *)
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

  Lemma unlockNode_spec (n: Node) :
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


  (** Proofs of traverse and CSSOp *)

  Lemma traverse_spec (γ γ_fp γ_k: gname) (k: K) (root n: Node) (Ns: gset Node):
    ⌜n ∈ Ns⌝ ∗ own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝ -∗
    <<< ∀ C, is_CSS γ γ_fp γ_k root C >>>
      traverse root #n #k @ ⊤
    <<< ∃ (n': Node) (Ns': gsetUR Node) (I_n': inset_flowint_ur K) (C_n': gset K),
        is_CSS γ γ_fp γ_k root C ∗ ⌜n' ∈ Ns'⌝ ∗ own γ_fp (◯ Ns')
        ∗ own γ (◯ I_n') ∗ node n' I_n' C_n'
        ∗ own γ_k (◯ prod (keyset K I_n' n', C_n')) ∗ ⌜domm I_n' = {[n']}⌝
        ∗ ⌜in_inset K k I_n' n'⌝ ∗ ⌜¬in_outsets K k I_n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns). iIntros "(#Hinn & #Hfp & #Hroot)".
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n). iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "Hst". iDestruct "Hst" as (I)"(H2 & H3 & H4 & H5 & H6)".
    iAssert (⌜n ∈ domm I⌝)%I with "[Hfp Hinn H6]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns (domm I)) with "[$]") as "%".
      iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
    iDestruct "H5" as "[Hb H5]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitL.
    iExists I. iFrame "∗ % #". iApply "H5". iExists b.
    iFrame. eauto with iFrame. } iIntros "(Hloc & ?)".
    destruct b. { iExFalso. done. } iModIntro.
    iSplitR "Hb". iExists I. iFrame "∗ % #". iApply "H5". iExists true.
    iFrame. iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (In Cn) "(HIn & Hrep & #HNds & HKS)". iDestruct "HNds" as %HNds.
    wp_bind (inRange _ _)%E. wp_apply ((inRange_spec n In Cn k) with "Hrep").
    iIntros (b) "(Hrep & Hb)". destruct b.
    - wp_pures. wp_bind (findNext _ _)%E. iDestruct "Hb" as %Hinset.
      wp_apply ((findNext_spec n In Cn k) with "[Hrep]"). iFrame "∗ # %".
      iIntros (b n') "(Hrep & Hbb)". destruct b.
      + wp_pures. awp_apply (unlockNode_spec n).
        iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
        iDestruct "Hst" as (I1)"(H1 & H2 & % & H5 & H6)".
        iAssert (⌜n ∈ domm I1⌝)%I with "[Hfp Hinn H6]" as "%".
        { iPoseProof ((auth_set_incl γ_fp Ns (domm I1)) with "[$]") as "%".
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
        { iPoseProof (auth_set_incl with "[$Hfp $H6]") as "%".
          iPoseProof (auth_own_incl with "[$H2 $HIn]") as (I2)"%".
          iPoseProof (own_valid with "H2") as "%".
          iAssert (⌜n' ∈ domm I1⌝)%I as "%".
          { iPureIntro. assert (n' ∈ domm I2).
            { apply (flowint_step I1 In I2 k n' root); try done. }
            unfold globalinv in H0. destruct H0 as [HI1 H0]. apply leibniz_equiv in H3. rewrite H3 in HI1.
            assert (domm (In⋅I2) = domm (In) ∪ domm (I2)). { apply intComp_dom. done. } rewrite H3.
            rewrite H6. set_solver. }
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
      { iPoseProof ((auth_set_incl γ_fp Ns (domm I1)) with "[$]") as "%".
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


  (* Ghost state manipulation to make final proof cleaner *)

  Lemma ghost_update_keyset γ_k dop k Cn Cn' res K1 C:
    Ψ dop k Cn Cn' res ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
    ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝
    ==∗ ∃ C', Ψ dop k C C' res ∗ own γ_k (● prod (KS, C'))
      ∗ own γ_k (◯ prod (K1, Cn')).
  Proof.
    iIntros "(#HΨ & Ha & Hf & % & % & HKS)". iPoseProof (auth_own_incl_ks γ_k (prod (KS, C)) (prod (K1, Cn))
                with "[$Ha $Hf]") as "%". iDestruct "HKS" as %HKS.
    iPoseProof ((own_valid γ_k (● prod (KS, C))) with "Ha") as "%".
    iPoseProof ((own_valid γ_k (◯ prod (K1, Cn))) with "Hf") as "%".
    assert ((K1 = KS ∧ Cn = C) ∨
            (∃ a0 b0, KS = K1 ∪ a0 ∧ C = Cn ∪ b0 ∧ K1 ## a0 ∧ Cn ## b0 ∧ Cn ⊆ K1 ∧ C ⊆ KS ∧ b0 ⊆ a0)) as Hs.
    { apply (auth_ks_included K1 KS Cn C); try done. apply auth_auth_valid. done. }
    destruct Hs.
    - iEval (unfold Ψ) in "HΨ". destruct H4. destruct dop.
      + iDestruct "HΨ" as "%". destruct H6.
        iModIntro. iExists C. iEval (rewrite <-H6) in "Hf". iFrame. unfold Ψ.
        iPureIntro. split; try done. rewrite <-H5. done.
      + iDestruct "HΨ" as "%". destruct H6. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∪ {[k]}) ⋅ ◯ prod (K1, Cn ∪ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_insert.
            split; try done. apply auth_auth_valid. done.   }
          iModIntro. iExists (C ∪ {[k]}). iEval (rewrite H6). iFrame.
          unfold Ψ. iPureIntro. split; try done. rewrite <-H5. done.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H8) in "Hf".
          iFrame. unfold Ψ. iPureIntro. rewrite <- H5. split; try done. rewrite H8 in H6. done.
      + iDestruct "HΨ" as "%". destruct H6. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∖ {[k]}) ⋅ ◯ prod (K1, Cn ∖ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_delete. split; try done. apply auth_auth_valid. done. }
          iModIntro. iExists (C ∖ {[k]}). iEval (rewrite H6). iFrame.
          unfold Ψ. iPureIntro. split; try done. rewrite <-H5. done.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H8) in "Hf".
          iFrame. unfold Ψ. iPureIntro. rewrite <- H5. split; try done. rewrite H8 in H6. done.
    - destruct H4 as [Ko [Co [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]. destruct dop.
      + iDestruct "HΨ" as "%". destruct H11.
        iModIntro. iExists C. iEval (rewrite <-H11) in "Hf". iFrame. unfold Ψ.
        iPureIntro. split; try done. destruct res; set_solver.
      + iDestruct "HΨ" as "%". destruct H11. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∪ {[k]}) ⋅ ◯ prod (K1, Cn ∪ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_insert. split; try done. }
          iModIntro. iExists (C ∪ {[k]}). iEval (rewrite H11). iFrame.
          unfold Ψ. iPureIntro. split; try done. set_solver.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H13) in "Hf".
          iFrame. unfold Ψ. iPureIntro. set_solver.
      + iDestruct "HΨ" as "%". destruct H11. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn))
          (● prod (KS, C ∖ {[k]}) ⋅ ◯ prod (K1, Cn ∖ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_delete. split; try done. }
          iModIntro. iExists (C ∖ {[k]}). iEval (rewrite H11). iFrame.
          unfold Ψ. iPureIntro. split; try done. set_solver.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H13) in "Hf".
          iFrame. unfold Ψ. iPureIntro. set_solver.
  Qed.

  (** Verification of abstract specification of the search structure operation. *)

  Theorem CSSOp_spec (γ γ_fp γ_k: gname) root (dop: dOp) (k: K):
    ⌜k ∈ KS⌝ -∗ <<< ∀ C, is_CSS γ γ_fp γ_k root C >>>
      CSSOp dop root #k @ ⊤
    <<< ∃ C' (res: bool), is_CSS γ γ_fp γ_k root C'
        ∗ Ψ dop k C C' res, RET #res >>>.
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
    iIntros (b Cn' res). iIntros "Hb". destruct b.
    - iDestruct "Hb" as "(Hrep & #HΨ & #Hsub)".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(H1 & H2 & % & H5 & H6)".
      iAssert (⌜n ∈ domm I⌝)%I with "[Hfp1 Hinn H6]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns1 (domm I)) with "[$]") as "%".
        iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In'' Cn'') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In'').
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "HIn Hrep HKS".
      iExists I. iFrame "∗ % #". iApply "H5". iExists true.
      iFrame "Hlock". eauto with iFrame. } iIntros "Hlock".
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset K In n) C2) with "[H1 HKS]") as "Hgks".
      iFrame "% ∗ #". iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
      iPureIntro. apply keyset_def; try done.
      iDestruct "Hgks" as (C2') "(#HΨC & Ha & Hf)".
      iModIntro. iExists (C2'), res. iSplitL. iSplitR "HΨC".
      { iExists I. iFrame "∗ % #". iApply "H5". iExists false. iFrame "∗ # %".
        iExists In, Cn'. eauto with iFrame. } done. iIntros "HΦ". iModIntro. wp_pures. done.
    - wp_match. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I1)"(H1 & H2 & % & H5 & H6)".
      iAssert (⌜n ∈ domm I1⌝)%I with "[Hfp1 Hinn H6]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns1 (domm I1)) with "[$]") as "%".
        iDestruct "Hinn" as %Hinn. iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (domm I1) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In'' Cn'') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf. { iApply (node_sep_star n In In'').
      iFrame. } exfalso. done. } iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro.
      iSplitR "HIn Hb HKS". iExists I1. iFrame "∗ % #". iApply "H5". iExists true. iFrame.
      eauto with iFrame. } iIntros "Hlock". iModIntro. iSplitL. iExists I1. iFrame "∗ % #".
      iApply "H5". iExists false. eauto with iFrame. iIntros "AU". iModIntro.
      wp_pures. iApply "IH"; try done.
  Qed.

End Give_Up_Template.
