Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset big_op.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "All".
Require Export flows keyset_ra.

(* ---------- The program ---------- *)

Inductive dOp := memberOp | insertOp | deleteOp.

Variable findNext : val.
Variable inRange : val.
Variable decisiveOp : (dOp → val).
Variable searchStrSpec : (dOp → val).
Variable lockLoc : node → loc.
Variable getLockLoc : val.
Variable ks: node → gset key.

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

(* RA for pair of keysets and contents *)
Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (authUR (prodUR)) }.
Definition keysetΣ : gFunctors := #[GFunctor (authUR (prodUR))].

Instance subG_keysetΣ {Σ} : subG keysetΣ Σ → keysetG Σ.
Proof. solve_inG. Qed.

Section Give_Up_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

(* ---------- Flow interface set-up specific to this proof ---------- *)

  Variable root : node.
  Variable KS : gset key.
  Variable hrep : node → flowintUR → gset key → iProp.
  Parameter hrep_timeless_proof : ∀ n I C, Timeless (hrep n I C).
  Instance hrep_timeless n I C: Timeless (hrep n I C).
  Proof. apply hrep_timeless_proof. Qed.
  Parameter hrep_fp : ∀ n I_n C, hrep n I_n C -∗ ⌜Nds I_n = {[n]}⌝.
  Parameter hrep_sep_star: ∀ n I_n I_n' C C', hrep n I_n C ∗ hrep n I_n' C' -∗ False.
  Parameter KS_full : ∀ k, k ∈ KS.
  
  Hypothesis globalint_root_fp: ∀ I, globalint I → root ∈ Nds I.

 (* Hypothesis globalint_fpo : ∀ I, globalint I → ∀ n:node, outf I n = 0.
                                           Can't figure out (outf I n). Also is it appropriate?  *)

  Hypothesis contextualLeq_impl_globalint :
    ∀ I I', globalint I →  contextualLeq I I' → globalint I'.

  Hypothesis keyset_in_out : ∀ k In n, in_inset k In n → not_in_outset k In n → k ∈ ks n.
  
  (* ---------- Coarse-grained specification ---------- *)

  Definition Ψ dop k (C: gset key) (C': gset key) (res: bool) : iProp :=
    match dop with
    | memberOp => (⌜C' = C ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    | insertOp => (⌜C' = union C {[k]} ∧ (if res then k ∉ C else k ∈ C)⌝)%I
    | deleteOp => (⌜C' = difference C {[k]} ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    end.

  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.

  (* ---------- Helper functions specs - proved for each implementation in GRASShopper ---------- *)

  Parameter getLockLoc_spec : ∀ (n: node),
      ({{{ True }}}
           getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  Parameter inRange_spec : ∀ (n: node) (I_n : flowintUR) (C: gset key) (k: key),
      ({{{ hrep n I_n C }}}
           inRange #n #k
       {{{ (b: bool), RET #b; hrep n I_n C ∗ (match b with true => ⌜in_inset k I_n n⌝ |
                                    false => ⌜True⌝ end) }}})%I.

  Parameter findNext_spec : ∀ (n: node) (I_n : flowintUR) (C: gset key) (k: key),
      ({{{ hrep n I_n C }}}
           findNext #n #k
       {{{ (b: bool) (n': node), 
              RET (match b with true => (SOMEV #n') | false => NONEV end); 
               hrep n I_n C ∗ (match b with true => ⌜in_edgeset k I_n n n'⌝ |
                                          false => ⌜not_in_outset k I_n n⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: node) (k: key) (I_n: flowintUR) (C: gset key),
      ({{{ hrep n I_n C ∗ ⌜in_inset k I_n n⌝
                    ∗ ⌜not_in_outset k I_n n⌝ ∗ ⌜Nds I_n = {[n]}⌝ }}}
           decisiveOp dop #n #k
       {{{ (b: bool) (I_n': flowintUR) (C': gset key) (res: bool),
                  RET (match b with false => NONEV | true => (SOMEV #res) end);
                  match b with false => hrep n I_n C |
                              true => hrep n I_n' C' ∗ Ψ dop k C C' res ∗ ⌜ C' ⊆ ks n⌝
                                      ∗ ⌜contextualLeq I_n I_n'⌝ ∗ ⌜Nds I_n' = {[n]}⌝ end }}})%I.

  (* ---------- The invariant ---------- *)

  Definition main_searchStr (γ γ_fp γ_k : gname) I Ns (C: gset key)
    : iProp :=
       ( own γ_k (● prod (KS, C)) ∗ own γ (● I) ∗ ⌜globalint I⌝
        ∗ ([∗ set] n ∈ (Nds I), (∃ b: bool, (lockLoc n) ↦ #b ∗ if b then True
                                 else (∃ (In: flowintUR) (Cn: gset key), own γ (◯ In) ∗ hrep n In Cn 
                                                ∗ ⌜Nds In = {[n]}⌝ ∗ own γ_k (◯ prod (ks(n), Cn)))))
        ∗ own γ_fp (● Ns) ∗ ⌜Ns = (Nds I)⌝
    )%I.

  Definition is_searchStr γ γ_fp γ_k C := (∃ I Ns, (main_searchStr γ γ_fp γ_k I Ns C))%I.

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

  Lemma auth_own_incl_ks γ x y : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iIntros "Hown".
    iEval (rewrite /(✓ (_)) /=) in "Hown".
    iEval (rewrite /(cmra_op) /=) in "Hown".
  Admitted.
  
  Lemma auth_ks_included (a1 a2 b1 b2: gset key) : prod (a1, b1) ≼ prod (a2, b2) 
                → (a1 = a2 ∧ b1 = b2) ∨ 
                    (∃ a0 b0, a2 = a1 ∪ a0 ∧ b2 = b1 ∪ b0 ∧ a1 ## a0 ∧ b1 ## b0 ∧ b1 ⊆ a1 ∧ b2 ⊆ a2 ∧ b0 ⊆ a0).
  Proof.
  Admitted.  
  
  Lemma auth_ks_local_update_insert K1 C Cn k: k ∈ K1 ∧ k ∉ Cn →
             (prod (KS, C), prod (K1, Cn)) ~l~> (prod (KS, C ∪ {[k]}), prod (K1, Cn ∪ {[k]})).
  Proof. 
  Admitted.

  Lemma auth_ks_local_update_delete K1 C Cn k: k ∈ K1 ∧ k ∈ Cn →
             (prod (KS, C), prod (K1, Cn)) ~l~> (prod (KS, C ∖ {[k]}), prod (K1, Cn ∖ {[k]})).
  Proof. 
  Admitted.

         
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

  Lemma inv_impl_fp n Ns γ γ_fp γ_k I Ns' C:
    main_searchStr γ γ_fp γ_k I Ns' C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗ ⌜n ∈ Nds I⌝.
  Proof.
    iIntros "(HInv & HNs & %)".
    iDestruct "HInv" as "(? & HIns & ? & ? & HNs' & %)".
    iPoseProof (auth_set_incl with "[$HNs $HNs']") as "%".
    iPureIntro. set_solver.
  Qed.                                       (* Made Proof using Type* *)

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

  Lemma traverse_spec (γ γ_fp γ_k: gname) (k: key) (n: node) (Ns: gset node):
       ⌜n ∈ Ns⌝ ∗ own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝ -∗ <<< ∀ C, is_searchStr γ γ_fp γ_k C >>>
                traverse root #n #k
                    @ ⊤
          <<< ∃ (n': node) (Ns': gsetUR node) (I_n': flowintUR) (Cn: gset key), is_searchStr γ γ_fp γ_k C
                      ∗ ⌜n' ∈ Ns'⌝ ∗ own γ_fp (◯ Ns') ∗ own γ (◯ I_n') ∗ hrep n' I_n' Cn 
                      ∗ own γ_k (◯ prod (ks(n'), Cn)) ∗ ⌜Nds I_n' = {[n']}⌝ ∗ ⌜in_inset k I_n' n'⌝ 
                      ∗ ⌜not_in_outset k I_n' n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns). iIntros "(#Hinn & #Hfp & #Hroot)".
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n). iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "Hst". iDestruct "Hst" as (I Ns0)"(H2 & H3 & H4 & H5 & H6 & H7)".
    iAssert (⌜n ∈ Nds I⌝)%I with "[Hfp Hinn H6 H7]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns Ns0) with "[$]") as "%".
      iDestruct "H7" as %H7. iDestruct "Hinn" as %Hinn. iEval (rewrite <-H7).
      iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I) n); last by eauto.
    iDestruct "H5" as "[Hb H5]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitL.
    iExists I, Ns0. iFrame "∗ % #". iApply "H5". iExists b.
    iFrame. eauto with iFrame. } iIntros "(Hloc & ?)".
    destruct b. { iExFalso. done. } iModIntro.
    iSplitR "Hb". iExists I, Ns0. iFrame "∗ % #". iApply "H5". iExists true.
    iFrame. iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (In Cn) "(HIn & Hrep & #HNds & HKS)". iDestruct "HNds" as %HNds.
    wp_bind (inRange _ _)%E. wp_apply ((inRange_spec n In Cn k) with "Hrep").
    iIntros (b) "(Hrep & Hb)". destruct b.
    - wp_pures. wp_bind (findNext _ _)%E.
      wp_apply ((findNext_spec n In Cn k) with "Hrep").
      iIntros (b n') "(Hrep & Hbb)". destruct b.
      + wp_pures. awp_apply (unlockNode_spec n). 
        iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
        iDestruct "Hst" as (I1 Ns1)"(H1 & H2 & % & H5 & H6 & %)".
        iAssert (⌜n ∈ Nds I1⌝)%I with "[Hfp Hinn H6]" as "%".
        { iPoseProof ((auth_set_incl γ_fp Ns Ns1) with "[$]") as "%".
          iDestruct "Hinn" as %Hinn. iEval (rewrite <-H1).
          iPureIntro. set_solver. }
        rewrite (big_sepS_elem_of_acc _ (Nds I1) n); last by eauto.
        iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
        destruct b; first last. { iDestruct "Hl" as (In' Cn') "(_ & Hrep' & _)".
        iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (hrep_sep_star n In In'). 
        iFrame. } exfalso. done. }
        iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "HIn HKS Hb Hrep Hbb".
        iExists I1, Ns1. iFrame "∗ % #". iApply "H5". iExists true. iFrame. iIntros "AU".
        iModIntro. iFrame. } iIntros "Hlock".
        iDestruct "Hb" as %Hb. iDestruct "Hbb" as %Hbb.
        iAssert (⌜n' ∈ Ns1⌝ ∗ ⌜root ∈ Ns1⌝ ∗ own γ (● I1) ∗ own γ_fp (● Ns1) ∗ own γ (◯ In))%I 
                with "[HIn H2 H6]" as "Hghost".
        { iPoseProof (auth_set_incl with "[$Hfp $H6]") as "%".
          iPoseProof (auth_own_incl with "[$H2 $HIn]") as (I2)"%".
          iPoseProof (own_valid with "H2") as "%".
          iAssert (⌜n' ∈ Nds I1⌝)%I as "%".
          { iPureIntro. assert (n' ∈ Nds I2).
            { apply (flowint_step I1 In _ k n). done. 
              apply auth_auth_valid. done.
              replace (Nds In). set_solver. done. done. }
            apply flowint_comp_fp in H4. set_solver. }
            iFrame. iPureIntro. replace Ns1. auto. }
        iDestruct "Hghost" as "(% & % & HAIn & HAfp & HIn)".
        iMod (own_update γ_fp (● Ns1) (● Ns1 ⋅ ◯ Ns1) with "HAfp") as "HNs".
        apply auth_update_core_id. apply gset_core_id. done.
        iDestruct "HNs" as "(HAfp & #Hfp1)".
        iModIntro. iSplitL. iExists I1, Ns1.
        iFrame "∗ % #". iApply "H5". iExists false. iFrame. iExists In. eauto with iFrame.
        iIntros "AU". iModIntro. wp_pures. iApply "IH". iFrame "∗ % #". done.
      + iApply fupd_wp. iMod "AU" as (C) "[Hst [_ Hclose]]". iSpecialize ("Hclose" $! n Ns In).
        iMod ("Hclose" with "[Hst HIn Hrep Hb Hbb HKS]") as "HΦ".
        iFrame "∗ % #". iModIntro. wp_match. done.
    - wp_if. awp_apply (unlockNode_spec n). 
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
      iDestruct "Hst" as (I1 Ns1)"(H1 & H2 & % & H5 & H6 & %)".
      iAssert (⌜n ∈ Nds I1⌝)%I with "[Hfp Hinn H6]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns Ns1) with "[$]") as "%".
        iDestruct "Hinn" as %Hinn. iEval (rewrite <-H1).
        iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (Nds I1) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In' Cn') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (hrep_sep_star n In In'). 
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hrep HIn HKS".
      iExists I1, Ns1. iFrame "∗ % #". iApply "H5". iExists true. iFrame. iIntros "AU".
      iModIntro. eauto with iFrame. } iIntros "Hlock". iModIntro.
      iSplitL. iExists I1, Ns1. iFrame "∗ % #". iApply "H5". iExists false. iFrame.
      iExists In, Cn. eauto with iFrame. iIntros "AU". iModIntro. wp_pures.
      iApply "IH". eauto with iFrame. done.
  Qed.


  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)

  Lemma ghost_update_keyset γ_k dop k Cn Cn' res K1 C:
          Ψ dop k Cn Cn' res ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
                             ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝  ==∗
                 ∃ C', Ψ dop k C C' res ∗ own γ_k (● prod (KS, C')) ∗ own γ_k (◯ prod (K1, Cn')).
  Proof.
    iIntros "(#HΨ & Ha & Hf & % & %)". iPoseProof (auth_own_incl_ks γ_k (prod (KS, C)) (prod (K1, Cn))
                with "[$Ha $Hf]") as "%". apply (auth_ks_included _ _ _ _) in H1. destruct H1.
    - iEval (unfold Ψ) in "HΨ". destruct H1. destruct dop. 
      + iDestruct "HΨ" as "%". destruct H3.
        iModIntro. iExists C. iEval (rewrite <-H3) in "Hf". iFrame. unfold Ψ.
        iPureIntro. split; try done. rewrite <-H2. done.
      + iDestruct "HΨ" as "%". destruct H3. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn)) 
          (● prod (KS, C ∪ {[k]}) ⋅ ◯ prod (K1, Cn ∪ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_insert. split; try done. }
          iModIntro. iExists (C ∪ {[k]}). iEval (rewrite H3). iFrame.
          unfold Ψ. iPureIntro. split; try done. rewrite <-H2. done.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H5) in "Hf".
          iFrame. unfold Ψ. iPureIntro. rewrite <- H2. split; try done. rewrite H5 in H3. done.
      + iDestruct "HΨ" as "%". destruct H3. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn)) 
          (● prod (KS, C ∖ {[k]}) ⋅ ◯ prod (K1, Cn ∖ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_delete. split; try done. }
          iModIntro. iExists (C ∖ {[k]}). iEval (rewrite H3). iFrame.
          unfold Ψ. iPureIntro. split; try done. rewrite <-H2. done.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H5) in "Hf".
          iFrame. unfold Ψ. iPureIntro. rewrite <- H2. split; try done. rewrite H5 in H3. done.
    - destruct H1 as [Ko [Co [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]. destruct dop.
      + iDestruct "HΨ" as "%". destruct H8.
        iModIntro. iExists C. iEval (rewrite <-H8) in "Hf". iFrame. unfold Ψ.
        iPureIntro. split; try done. destruct res; set_solver.
      + iDestruct "HΨ" as "%". destruct H8. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn)) 
          (● prod (KS, C ∪ {[k]}) ⋅ ◯ prod (K1, Cn ∪ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_insert. split; try done. }
          iModIntro. iExists (C ∪ {[k]}). iEval (rewrite H8). iFrame.
          unfold Ψ. iPureIntro. split; try done. set_solver.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H10) in "Hf".
          iFrame. unfold Ψ. iPureIntro. set_solver.
      + iDestruct "HΨ" as "%". destruct H8. destruct res.
        * iMod (own_update_2 γ_k (● prod (KS, C)) (◯ prod (K1, Cn)) 
          (● prod (KS, C ∖ {[k]}) ⋅ ◯ prod (K1, Cn ∖ {[k]})) with "[Ha] [Hf]") as "(Ha & Hf)"; try done.
          { apply auth_update. apply auth_ks_local_update_delete. split; try done. }
          iModIntro. iExists (C ∖ {[k]}). iEval (rewrite H8). iFrame.
          unfold Ψ. iPureIntro. split; try done. set_solver.
        * assert (Cn' = Cn). { set_solver. } iModIntro. iExists C. iEval (rewrite <-H10) in "Hf".
          iFrame. unfold Ψ. iPureIntro. set_solver.
  Qed.

  Theorem searchStrOp_spec (γ γ_fp γ_k: gname) (dop: dOp) (k: key):
      <<< ∀ C, is_searchStr γ γ_fp γ_k C >>>
            searchStrOp dop root #k
                  @ ⊤
      <<< ∃ C' (res: bool), is_searchStr γ γ_fp γ_k C' 
                                        ∗ Ψ dop k C C' res, RET #res >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I0 Ns0) "(H1 & H2 & % & H5 & H6 & %)".
    assert (root ∈ Ns0)%I as Hroot. { replace Ns0. apply globalint_root_fp. done. }
    iMod (own_update γ_fp (● Ns0) (● Ns0 ⋅ ◯ Ns0) with "H6") as "HNs".
    { apply auth_update_core_id. apply gset_core_id. done. } 
    iDestruct "HNs" as "(HAfp & #Hfp0)".
    iMod ("HAU" with "[H1 H2 H5 HAfp] ") as "AU". { iExists I0, Ns0. iFrame "∗ % #". }
    iModIntro. wp_bind (traverse _ _ _)%E.
    awp_apply (traverse_spec γ γ_fp γ_k k root Ns0). eauto with iFrame.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "Hst". iAaccIntro with "Hst"; first by eauto with iFrame.
    iIntros (n Ns1 In Cn) "(Hst & #Hinn & #Hfp1 & HIn & Hrepn & HKS & #HNdsn & #Hinset & #Hnotout)".
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hrepn]"). eauto with iFrame.
    iIntros (b In' Cn' res). iIntros "Hb". destruct b.
    - iDestruct "Hb" as "(Hrep & #HΨ & #Hsub & #Hcon & #HNds')".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I Ns2) "(H1 & H2 & % & H5 & H6 & %)".
      iAssert (⌜n ∈ Nds I⌝)%I with "[Hfp1 Hinn H6]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns1 Ns2) with "[$]") as "%".
        iDestruct "Hinn" as %Hinn. iEval (rewrite <-H2).
        iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (Nds I) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In'' Cn'') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (hrep_sep_star n In' In''). 
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "HIn Hrep HKS".
      iExists I, Ns2. iFrame "∗ % #". iApply "H5". iExists true. 
      iFrame "Hlock". eauto with iFrame. } iIntros "Hlock".
      iPoseProof (auth_own_incl with "[$H2 $HIn]") as (I2)"%".
      iPoseProof ((own_valid γ (● I)) with "H2") as "%". iDestruct "Hcon" as %Hcon.
      iMod (own_updateP (flowint_update_P I In In') γ (● I ⋅ ◯ In) with "[H2 HIn]") as (?) "H0".
      { apply (flowint_update I In In'). done. } { rewrite own_op. iFrame. }
      iPoseProof ((flowint_update_result γ I In In') with "H0") as (I') "(% & % & HIIn)".
      iAssert (own γ (● I') ∗ own γ (◯ In'))%I 
                                with "[HIIn]" as "(HI' & HIn')". { by rewrite own_op. }
      iPoseProof ((own_valid γ (● I')) with "HI'") as "%". iDestruct "Hsub" as "%".
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (ks n) C2) with "[H1 HKS]") as "Hgks".
      iFrame "% ∗ #". iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
      iPureIntro. apply (keyset_in_out k In n); try done. 
      iDestruct "Hgks" as (C2') "(#HΨC & Ha & Hf)".
      iModIntro. iExists (C2'), res. iSplitL. iSplitR "HΨC".
      { iExists I', Ns2. assert (globalint I') as HI'.
      { apply (contextualLeq_impl_globalint I I'). done. done. }
      assert (Nds I = Nds I') as HH. { apply (contextualLeq_impl_fp I I'). done. }
      rewrite HH in H2. iFrame "∗ % #". iEval (rewrite HH) in "H5".
      iApply "H5". iExists false. iFrame. iExists In', Cn'. eauto with iFrame. } done.
      iIntros "HΦ". iModIntro. wp_pures. done.
    - wp_match. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I1 Ns2)"(H1 & H2 & % & H5 & H6 & %)". 
      iAssert (⌜n ∈ Nds I1⌝)%I with "[Hfp1 Hinn H6]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns1 Ns2) with "[$]") as "%".
        iDestruct "Hinn" as %Hinn. iEval (rewrite <-H2).
        iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (Nds I1) n); last by eauto.
      iDestruct "H5" as "[Hl H5]". iDestruct "Hl" as (b) "[Hlock Hl]".
      destruct b; first last. { iDestruct "Hl" as (In'' Cn'') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf. { iApply (hrep_sep_star n In In''). 
      iFrame. } exfalso. done. } iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro.
      iSplitR "HIn Hb HKS". iExists I1, Ns2. iFrame "∗ % #". iApply "H5". iExists true. iFrame.
      eauto with iFrame. } iIntros "Hlock". iModIntro. iSplitL. iExists I1, Ns2. iFrame "∗ % #".
      iApply "H5". iExists false. eauto with iFrame. iIntros "AU". iModIntro.
      wp_pures. iApply "IH". done.
  Qed.
