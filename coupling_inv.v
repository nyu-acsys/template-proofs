Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset.   
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Require Export keyset_ra.
Set Default Proof Using "All".

Inductive dOp := memberOp | insertOp | deleteOp.

Variable findNext : val.
Variable decisiveOp : (dOp → val).
Variable searchStrSpec : (dOp → val).
Variable lockLoc : Node → loc.
Variable getLockLoc : val.
Variable alloc : val.

Definition lockNode : val :=
  rec: "lockN" "x" :=
    let: "l" := getLockLoc "x" in
    if: CAS "l" #false #true
    then #()
    else "lockN" "x" .

Definition unlockNode : val :=
  λ: "x",
  let: "l" := getLockLoc "x" in
  "l" <- #false.

Definition traverse : val :=  
  rec: "tr" "p" "n" "k" :=
    match: (findNext "n" "k") with
      NONE => ("p", "n")
    | SOME "n'" =>
      lockNode "n'";; unlockNode "p";; "tr" "n" "n'" "k"
    end.

Definition searchStrOp (Ψ: dOp) (first: Node) : val :=
  λ: "k",
    lockNode #first;;
    let: "n0" := (findNext #first "k") in
    match: "n0" with 
      NONE => ""
    | SOME "n0" => lockNode "n0";;
                  let: "pn" := traverse #first "n0" "k" in
                  let: "p" := Fst "pn" in
                  let: "n" := Snd "pn" in
                  let: "m" := alloc #() in
                  let: "res" := (decisiveOp Ψ) "p" "n" "k" in
                  unlockNode "n";; unlockNode "p";; "res" end.

(* ---------- Cameras used in the following proofs ---------- *)

(* RA for authoritative flow interfaces *)
Class flowintG Σ := FlowintG { flowint_inG :> inG Σ (authR flowintUR) }.
Definition flowintΣ : gFunctors := #[GFunctor (authR flowintUR)].

Instance subG_flowintΣ {Σ} : subG flowintΣ Σ → flowintG Σ.
Proof. solve_inG. Qed.

(* RA for authoritative set of nodes *)
Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR Node)) }.
Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR Node))].

Instance subG_nodesetΣ {Σ} : subG nodesetΣ Σ → nodesetG Σ.
Proof. solve_inG. Qed.

(* RA for set of contents *)
Class contentG Σ := ContentG { content_inG :> inG Σ (authR (optionUR (exclR (gsetR key)))) }.
Definition contentΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (gsetR key))))].

Instance subG_contentΣ {Σ} : subG contentΣ Σ → contentG Σ.
Proof. solve_inG. Qed.

(* RA for pair of keysets and contents *)
Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (authUR (keysetUR)) }.
Definition keysetΣ : gFunctors := #[GFunctor (authUR (keysetUR))].

Instance subG_keysetΣ {Σ} : subG keysetΣ Σ → keysetG Σ.
Proof. solve_inG. Qed.

Section Lock_Coupling_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !contentG Σ, !keysetG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  
  (* ---------- Flow interface set-up specific to this proof ---------- *)

  Parameter in_inset : key → flowintUR → Node → Prop.
  Parameter in_outset : key → flowintUR → Node → Prop.      
  Parameter linkset : flowintUR → Node → gset key.
  Parameter is_empty_flowint : flowintUR → Prop.
  Parameter keyset : flowintUR → Node → gset key.            
  Parameter hrep_spatial : Node → iProp.

  Parameter node : Node → Node → flowintUR → gset key → iProp.
  Parameter node_timeless_proof : ∀ n first I C, Timeless (node n first I C).
  Instance node_timeless n first I C: Timeless (node n first I C).
  Proof. apply node_timeless_proof. Qed.

  Definition in_outsets k In := ∃ n, in_outset k In n.

  Definition globalint first I : Prop :=
    ✓I ∧ (first ∈ dom I) ∧ (∀ k n, ¬ (in_outset k I n)) 
    ∧ ∀ n, ((n = first) → (∀ k, in_inset k I n))
           ∧ ((n ≠ first) → (∀ k, ¬ in_inset k I n)).  

  Definition nodeinv first n I_n  C_n : Prop :=
    C_n = keyset I_n n ∧ (n = first → ∀ k, k ∈ KS → in_outsets k I_n).    

  (** Coarse-grained specification *)

  Definition Ψ dop k (C: gsetO key) (C': gsetO key) (res: bool) : Prop :=
    match dop with
    | memberOp => C' = C ∧ if res then k ∈ C else k ∉ C
    | insertOp => C' = union C {[k]} ∧ if res then k ∉ C else k ∈ C
    | deleteOp => C' = difference C {[k]} ∧ if res then k ∈ C else k ∉ C
    end.

  Hypothesis node_sep_star: ∀ first n I_n I_n' C C', node n first I_n C ∗ node n first I_n' C' -∗ False.

  (** Helper functions specs *)

  (* Sid: we can also try to get rid of getLockLoc and just do CAS (lockLoc "l") #true #false in lock, etc. *)
  Parameter getLockLoc_spec : ∀ (n: Node),
      ({{{ True }}}
           getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  (* the following functions are proved for each implementation in GRASShopper
                                  (see b+-tree.spl and hashtbl-give-up.spl) *)

  Parameter findNext_spec : ∀ first (n: Node) (I_n : flowintUR) (C: gset key) (k: key),
      ({{{ node first n I_n C ∗ ⌜in_inset k I_n n⌝ }}}
           findNext #n #k
       {{{ (b: bool) (n': Node), 
              RET (match b with true => (SOMEV #n') | false => NONEV end); 
               node first n I_n C ∗ (match b with true => ⌜in_outset k I_n n'⌝ |
                                          false => ⌜¬in_outsets k I_n⌝ ∗ ⌜n ≠ first⌝ end) }}})%I.

  Parameter decisiveOp_insert_spec : ∀ dop first (p n m: Node) (k: key) (I_p I_n: flowintUR) (C_p C_n: gset key),
      ({{{ node p first I_p C_p ∗ node n first I_n C_n ∗ hrep_spatial m ∗ ⌜n ≠ first⌝ ∗ ⌜m ≠ first⌝
                          ∗ ⌜in_inset k I_p p⌝ ∗ ⌜in_outset k I_p n ⌝ ∗ ⌜¬in_outsets k I_n⌝ }}}
           decisiveOp dop #p #n #k
       {{{ (C_p' C_n' C_m': gset key) (I_p' I_n' I_m': flowintUR) (res: bool), RET  #res;
                           node p first I_p' C_p' ∗ node n first I_n' C_n' ∗ node m first I_m' C_m'
                         ∗ ⌜Ψ dop k (C_p ∪ C_n) (C_p' ∪ C_n' ∪ C_m') res⌝ 
                         ∗ ⌜contextualLeq (I_p ⋅ I_n) (I_p' ⋅ I_n' ⋅ I_m')⌝
                         ∗ ⌜C_p' ⊆ keyset I_p' p⌝ ∗ ⌜C_n' ⊆ keyset I_n' n⌝ ∗ ⌜C_m' ⊆ keyset I_m' m⌝
                         ∗ ⌜keyset I_p' p ## keyset I_n' n⌝ ∗ ⌜keyset I_p' p ## keyset I_m' m⌝
                         ∗ ⌜keyset I_m' m ## keyset I_n' n⌝ ∗ ⌜C_p' ## C_n'⌝ ∗ ⌜C_m' ## C_n'⌝ ∗ ⌜C_p' ## C_m'⌝
                         ∗ ⌜keyset I_p' p ∪ keyset I_n' n ∪ keyset I_m' m = keyset I_p p ∪ keyset I_n n⌝ }}})%I.

  Parameter alloc_spec : 
      ({{{ True }}}
           alloc #()
       {{{ (m: Node) (l:loc), RET #m; hrep_spatial m ∗ ⌜lockLoc m = l⌝ ∗ l ↦ #false }}})%I.


  (** The concurrent search structure invariant *)

  Definition cssN : namespace := N .@ "css".

  Definition css_inv (γ γ_fp γ_k γ_c : gname) root : iProp :=
    (∃ I (C: gset key),
        own γ_k (● prod (KS, C)) ∗ own γ (● I) ∗ ⌜globalint root I⌝
        ∗ own γ_fp (● dom I) ∗ own γ_c (● (Some ((Excl C))))
        ∗ ([∗ set] n ∈ (dom I), (∃ b: bool,
          (lockLoc n) ↦ #b ∗ if b then True
                             else (∃ (I_n: flowintUR) (C_n: gset key),
                                      own γ (◯ I_n) ∗ node n root I_n C_n 
                                      ∗ own γ_k (◯ prod (keyset I_n n, C_n)))))
    )%I.

  Definition css (γ γ_fp γ_k γ_c : gname) root : iProp :=
    inv N (css_inv γ γ_fp γ_k γ_c root).
  
  Definition css_cont (γ_c: gname) (C: gset key) : iProp :=
    (own γ_c (◯ (Some ((Excl C)))))%I.

  Instance css_inv_timeless  γ γ_fp γ_k γ_c root :
    Timeless (css_inv γ γ_fp γ_k γ_c root).
  Proof.
    rewrite /css_inv. repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    apply big_sepS_timeless. intros. apply bi.exist_timeless. intros.
    apply bi.sep_timeless; try apply _.
    destruct x2; try apply _.
  Qed.
  
  (* ---------- Useful Lemmas ----------- *)
  
  Lemma auth_agree γ xs ys :
  own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

  Lemma auth_update γ ys xs1 xs2 :
    own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { apply auth_update. apply option_local_update. apply exclusive_local_update. done. }
    done.
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

  Lemma lockNode_spec (n: Node):
    <<< ∀ (b: bool), (lockLoc n) ↦ #b >>>
        lockNode #n    @ ⊤
    <<< (lockLoc n) ↦ #true ∗ if b then False else True, RET #() >>>. (* rewrite if then else *)
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

  (* ---------- Proof of the lock coupling template  ---------- *)

  Lemma traverse_spec (γ γ_fp γ_k γ_c: gname) first (k: key) (p n: Node) (Ns: gset Node) I_p C_p I_n C_n:
    css γ γ_fp γ_k γ_c first -∗
    {{{ own γ_fp (◯ Ns) ∗ ⌜p ∈ Ns⌝ ∗ ⌜n ∈ Ns⌝ ∗ ⌜first ∈ Ns⌝ ∗ ⌜n ≠ first⌝
        ∗ node p first I_p C_p ∗ own γ (◯ I_p) ∗ ⌜in_inset k I_p p⌝ ∗ ⌜in_outset k I_p n⌝
        ∗ own γ_k (◯ prod (keyset I_p p, C_p)) ∗ node n first I_n C_n ∗ own γ (◯ I_n)
        ∗ own γ_k (◯ prod (keyset I_n n, C_n))
    }}}
      traverse #p #n #k @ ⊤
    {{{ (p' n': Node) (Ns': gsetUR Node) (I_p' I_n': flowintUR) (C_p' C_n': gset key), 
        RET (#p', #n');
        own γ_fp (◯ Ns') ∗ ⌜p' ∈ Ns'⌝ ∗ ⌜n' ∈ Ns'⌝ ∗ own γ (◯ I_p') ∗ own γ (◯ I_n') 
        ∗ node p' first I_p' C_p' ∗ node n' first I_n' C_n' ∗ ⌜n' ≠ first⌝
        ∗ own γ_k (◯ prod (keyset I_p' p', C_p'))
        ∗ own γ_k (◯ prod (keyset I_n' n', C_n')) 
        ∗ ⌜in_inset k I_p' p'⌝ ∗ ⌜in_outset k I_p' n'⌝ ∗ ⌜¬in_outsets k I_n'⌝
    }}}.
  Proof. Admitted.

  Lemma ghost_update_keyset γ_k dop k Cn Cn' res K1 C:
          ⌜Ψ dop k Cn Cn' res⌝ ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
                             ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝  ==∗
                 ∃ C', ⌜Ψ dop k C C' res⌝ ∗ own γ_k (● prod (KS, C')) ∗ own γ_k (◯ prod (K1, Cn')).
  Proof.
  Admitted.


  Theorem searchStrOp_spec (γ γ_fp γ_k γ_c: gname) first (k: key) (dop: dOp):
    ⌜k ∈ KS⌝ ∗ css γ γ_fp γ_k γ_c first -∗
    <<< ∀ (C: gset key), css_cont γ_c C >>>
      searchStrOp dop first #k @ ⊤ ∖ ↑N
    <<< ∃ C' (res: bool), css_cont γ_c C' ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "(% & #HInv)". iIntros (Φ) "AU". wp_lam. wp_bind (lockNode _)%E.
    awp_apply (lockNode_spec first). iInv "HInv" as ">H".
    iDestruct "H" as (I0 C0) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iMod (own_update γ_fp (● (dom I0)) (● (dom I0) ⋅ ◯ (dom I0)) with "HFP") as "H".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "H" as "(HFP & #Hfp)".
    assert (first ∈ dom I0). { admit. }
    rewrite (big_sepS_elem_of_acc _ (dom I0) first); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitR "AU".
    iNext. iExists I0, C0. iFrame "∗ # %". iApply "Hstar".
    iExists b. iFrame "∗ # %". done. }
    iIntros "(Hlock & H)". destruct b. { iExFalso. done. } iClear "H".
    iModIntro. iSplitR "AU Hb". iNext. iExists I0, C0. iFrame "∗ # %".
    iApply "Hstar". iExists true. iFrame "∗ # %".
    iDestruct "Hb" as (If Cf) "(HIf & Hnodef & HCf)".
    wp_pures. wp_bind(findNext _ _)%E. 
    wp_apply ((findNext_spec first first If Cf k) with "[Hnodef]").
    { iFrame "∗ # %". admit. } iIntros (b n) "(Hnodef & Hb)".
    destruct b; last first. wp_pures. iDestruct "Hb" as "(% & %)".
    exfalso. apply H3. done. iDestruct "Hb" as "%". wp_pures.
    wp_bind (lockNode _)%E. awp_apply (lockNode_spec n). iInv "HInv" as ">H".
    iDestruct "H" as (I2 C2) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    assert (n ∈ dom I2). { admit. }
    rewrite (big_sepS_elem_of_acc _ (dom I2) n); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]".
    iDestruct "Hb" as (b) "[Hlock Hb]".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitR "AU HIf HCf Hnodef".
    iNext. iExists I2, C2. iFrame "∗ # %". iApply "Hstar".
    iExists b. iFrame "∗ # %". iFrame "∗ # %". }
    iIntros "(Hlock & H)". destruct b. { iExFalso. done. } iClear "H".
    assert (first ∈ dom I2). { admit. }
    iMod (own_update γ_fp (● (dom I2)) (● (dom I2) ⋅ ◯ (dom I2)) with "HFP") as "H".
    apply auth_update_core_id. apply gset_core_id. done.
    iDestruct "H" as "(HFP & #Hfp2)". 
    iModIntro. iSplitR "AU HIf HCf Hnodef Hb". { iNext. iExists I2, C2.
    iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
    iDestruct "Hb" as (In Cn) "(HIn & Hnoden & HCn)".
    wp_pures. wp_bind (traverse _ _ _)%E. 
    wp_apply ((traverse_spec γ γ_fp γ_k γ_c first k first n (dom I2) If Cf In Cn)
                 with "[] [HIf HCf Hnodef HIn HCn Hnoden]"). 
    done. iFrame "∗ # %". admit.
    iIntros (p' n' Ns Ip' In' Cp' Cn') "(#HNs & % & % & HIp' & HIn' & Hnodep' & Hnoden'
                        & % & Hksp' & Hksn' & % & % & %)".  
    wp_pures. wp_apply (alloc_spec); first done.
    iIntros (m lm) "(Hrepm & % & Hlm)". wp_pures. wp_bind (decisiveOp _ _ _ _)%E.
    wp_apply ((decisiveOp_insert_spec dop first p' n' m k Ip' In' Cp' Cn') 
          with "[Hnodep' Hnoden' Hrepm]").
    { iFrame "∗ % #". admit. }
    iIntros (Cp'' Cn'' Cm'' Ip'' In'' Im'' res) "(Hrepp' & Hrepn' & Hrepm' & % & H)".  
    iDestruct "H" as "(% & % & % & % & % & % & % & % & % & % & %)".
    iApply fupd_wp. iInv "HInv" as ">H".
    iDestruct "H" as (I3 C3) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    iMod "AU" as (C') "[Hc [_ Hclose]]". iEval (rewrite /css_cont) in "Hc".
    iDestruct (auth_agree with "Hcont Hc") as %<-.

    (* ------ keyset update -------*)

    iPoseProof ((own_op γ_k (◯ prod (keyset Ip' p', Cp')) (◯ prod (keyset In' n', Cn')) 
                      with "[Hksp' Hksn']")) as "H"; first by eauto with iFrame.
    assert (◯ prod (keyset Ip' p', Cp') ⋅ ◯ prod (keyset In' n', Cn') =
               ◯ (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn'))).
    { apply (auth_frag_op (prod (keyset Ip' p', Cp')) (prod (keyset In' n', Cn'))). }
    iEval (rewrite H26) in "H". iPoseProof (own_valid with "H") as "%". 
    assert (✓ (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn'))).
    { apply (auth_frag_valid (◯ (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn')))). done. }
    unfold op,prodOp in H28. repeat case_decide; 
        [ simpl | try exfalso; eauto | try exfalso; eauto | try exfalso; eauto | try exfalso; eauto].
(*
    assert (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn') = 
       prod (keyset Ip'' p', Cp'') ⋅ prod (keyset In'' n', Cn'') ⋅ prod (keyset Im'' m, Cm'')).
    { admit. }
*)
    assert (prod (keyset Ip'' p', Cp'') ⋅ prod (keyset In'' n', Cn'') ⋅ prod (keyset Im'' m, Cm'')
                 = prod (keyset Ip'' p' ∪ keyset In'' n' ∪ keyset Im'' m, Cp'' ∪ Cn'' ∪ Cm'')).
    { admit. }
    assert (◯ (prod (keyset Ip'' p', Cp'') ⋅ prod (keyset In'' n', Cn'') ⋅ prod (keyset Im'' m, Cm''))
                 = ◯ (prod (keyset Ip'' p' ∪ keyset In'' n' ∪ keyset Im'' m, Cp'' ∪ Cn'' ∪ Cm''))).
    { admit. }            
    assert ((prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn')) 
                  = prod (keyset Ip' p' ∪ keyset In' n', Cp' ∪ Cn')).
    { admit. }
    iPoseProof ((own_op γ (◯ Ip') (◯ In')) with "[HIp' HIn']") as "H'"; first by eauto with iFrame.
    iPoseProof (own_valid with "H'") as "%". rewrite -auth_frag_op in H36.
    assert (✓ (Ip' ⋅ In')). { apply (auth_frag_valid (◯ (Ip' ⋅ In'))). done. }
    assert (in_inset k In' n'). { admit. }
    assert (k ∈ keyset In' n'). { admit. } 
    iMod ((ghost_update_keyset γ_k dop k (Cp' ∪ Cn') (Cp'' ∪ Cn'' ∪ Cm'') res 
                 (keyset Ip' p' ∪ keyset In' n') C3) with "[HKS H]") as "Hgks".
    iEval (rewrite H35) in "H". iFrame "∗ # %". iPureIntro. 
    split. rewrite <-H24. set_solver by eauto. set_solver by eauto.
    iDestruct "Hgks" as (C3') "(% & HKS & H)". iEval (rewrite <-H24) in "H".
    iAssert (own γ_k (◯ (prod (keyset Ip'' p', Cp'') ⋅ prod (keyset In'' n', Cn'') ⋅ prod (keyset Im'' m, Cm''))))
          with "[H]" as "Hv". { admit. (* iEval (rewrite <-H33) in "H". *) }
    iDestruct "Hv" as "((Hksp' & Hksn') & Hksm')".
    iMod (auth_update γ_c (C3') with "Hcont Hc") as "[Hcont Hc]".    

    (* ------ interface update -------*)  

    iPoseProof (own_valid with "HInt") as "%". 
    iMod (own_updateP (flowint_update_P I3 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')) γ
                          (● I3 ⋅ ◯ (Ip' ⋅ In')) with "[HInt H']") as (Io'') "H0".
    { apply (flowint_update I3 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')). done. }
    { try repeat rewrite own_op; iFrame. rewrite auth_frag_op. rewrite own_op. iFrame.  }
    iPoseProof ((flowint_update_result γ I3 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im''))
                      with "H0") as (I') "(% & % & HIIpnm)".
    iEval (rewrite own_op) in "HIIpnm". iDestruct "HIIpnm" as "(HI' & HIpnm'')".
    iPoseProof ((own_valid γ (● I')) with "HI'") as "%". iDestruct "HIpnm''" as "((HIp & HIn) & HIm)".
    destruct (decide (m ∈ dom I3)). { rewrite (big_sepS_elem_of_acc _ (dom I3) m); last by eauto.
    iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
    iEval (rewrite H12) in "Hlockm". iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%".
    assert (False) as Hf. { done. } exfalso. done. }
    iMod (own_update γ_fp (● dom I3) (● (dom I3 ∪ {[m]}) ⋅ ◯ (dom I3 ∪ {[m]})) with "[HFP]") as "H".
    { apply (auth_update_alloc (dom I3) (dom I3 ∪ {[m]}) (dom I3 ∪ {[m]})).
      apply gset_local_update. set_solver. } done. iDestruct "H" as "(HFP & #Hfp3)".
      assert (dom I' = dom I3 ∪ {[m]}). { destruct H43 as [I_o H43]. destruct H43.
      apply flowint_comp_fp in H43. assert (dom (Ip' ⋅ In') = dom Ip' ∪ dom In').
      apply flowint_comp_fp. done. rewrite H46 in H43. admit. }
    assert (globalint first I'). { admit. } iEval (rewrite <-H45) in "HFP".
    assert (dom I'∖ {[m]} = dom I3). { set_solver. }

    (* ------ updates over -------*)  

    iMod ("Hclose" with "[Hc]") as "HΦ". iFrame "∗ % #".
    iModIntro. iSplitL "Hstar Hlm Hrepm' HKS Hcont HI' HIm HFP Hksm'". iNext. iExists I', C3'.
    iFrame "∗ # %". rewrite (big_sepS_delete _ (dom I') m); last set_solver. iEval (rewrite H47).
    iFrame. iExists false. iEval (rewrite H12). iFrame. iExists Im'', Cm''. eauto with iFrame.
    iModIntro. wp_pures. wp_bind (unlockNode _)%E.
    
    (* ------ awp_apply issue -------*)  
     
    iClear "HΦ". 

    (* ------------------------------*)  

    awp_apply (unlockNode_spec n'). iInv "HInv" as ">H".
    iDestruct "H" as (I4 C4) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    assert (n' ∈ dom I4). { admit. } 
    rewrite (big_sepS_elem_of_acc _ (dom I4) n'); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
    destruct b; last first. { iDestruct "Hb" as (In0 Cn0) "(_ & Hrep' & _)".
    iAssert (⌜False⌝)%I with "[Hrepn' Hrep']" as %Hf. { iApply (node_sep_star first n' In'' In0). 
    iFrame. } exfalso. done. }
    iAaccIntro with "Hlock". { iIntros. iModIntro. iFrame "∗ # %". iNext. iExists I4, C4.  
    iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
    iIntros. iModIntro. iSplitR "Hrepp' Hksp' HIp". iNext. iExists I4, C4. 
    iFrame "∗ # %". iApply "Hstar". iExists false. iFrame. iExists In'', Cn''. iFrame.
    wp_pures. wp_bind (unlockNode _)%E.
    awp_apply (unlockNode_spec p'). iInv "HInv" as ">H".
    iDestruct "H" as (I5 C5) "(HKS & HInt & % & HFP & Hcont & Hstar)".
    assert (p' ∈ dom I5). { admit. } 
    rewrite (big_sepS_elem_of_acc _ (dom I5) p'); last by eauto.
    iDestruct "Hstar" as "[Hb Hstar]". iDestruct "Hb" as (b) "[Hlock Hb]".
    destruct b; last first. { iDestruct "Hb" as (In0 Cn0) "(_ & Hrep' & _)".
    iAssert (⌜False⌝)%I with "[Hrepp' Hrep']" as %Hf. { iApply (node_sep_star first p' Ip'' In0). 
    iFrame. } exfalso. done. }
    iAaccIntro with "Hlock". { iIntros. iModIntro. iFrame "∗ # %". iNext. iExists I5, C5.  
    iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. }
    iIntros. iModIntro. iSplitL. iNext. iExists I5, C5. 
    iFrame "∗ # %". iApply "Hstar". iExists false. iFrame. iExists Ip'', Cp''. iFrame.
    wp_pures.
  Admitted.