Add LoadPath "/home/nisarg/Academics/templates".
From iris.algebra Require Import excl auth gmap agree gset frac.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Require Export flows keyset_ra.
Set Default Proof Using "All".

(* ---------- The program ---------- *)

Inductive dOp := memberOp | insertOp | deleteOp.

Variable findNext : val.
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
    else "lockN" "x" .

Definition unlockNode : val :=
  λ: "x",
  let: "l" := getLockLoc "x" in
  "l" <- #false.

Definition traverse : val :=
  rec: "tr" "n" "k" :=
    lockNode "n";;
    match: (findNext "n" "k") with
      NONE => "n"
    | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
    end.

Definition searchStrOp (Ψ: dOp) (root: node) : val :=
  rec: "dictOp" "k" :=
    let: "n" := traverse #root "k" in
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
Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (authUR (keysetUR)) }.
Definition keysetΣ : gFunctors := #[GFunctor (authUR (keysetUR))].

Instance subG_keysetΣ {Σ} : subG keysetΣ Σ → keysetG Σ.
Proof. solve_inG. Qed.

(* RA for authoritative inreach sets *)
Class inreachG Σ := InreachG { inreach_inG :> inG Σ (authR (gsetUR key)) }.
Definition inreachΣ : gFunctors := #[GFunctor (authR (gsetUR key))].

Instance subG_inreachΣ {Σ} : subG inreachΣ Σ → inreachG Σ.
Proof. solve_inG. Qed.

(* RA for fractional interfaces *)
Class fracintG Σ := FracinthG { fracint_inG :> inG Σ (authR flowintUR) }.
Definition fracintΣ : gFunctors := #[GFunctor (authR flowintUR)].

Instance subG_fracintΣ {Σ} : subG fracintΣ Σ → fracintG Σ.
Proof. solve_inG. Qed.

Section Link_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ, !inreachG Σ, !fracintG Σ}.
  Notation iProp := (iProp Σ).

  (* ---------- Flow interface set-up specific to this proof ---------- *)

  Variable root : node.    (* make root parameter of the specs *)
  Variable KS : gset key.
  Variable hrep : node → flowintUR → gset key → iProp.
  Parameter hrep_timeless_proof : ∀ n I C, Timeless (hrep n I C).
  Instance hrep_timeless n I C: Timeless (hrep n I C).
  Proof. apply hrep_timeless_proof. Qed.
  Parameter hrep_fp : ∀ n I_n C, hrep n I_n C -∗ ⌜Nds I_n = {[n]}⌝.
  Parameter hrep_sep_star: ∀ n I_n I_n' C C', hrep n I_n C ∗ hrep n I_n' C' -∗ False.
  Parameter KS_full : ∀ k, k ∈ KS.
  
  Hypothesis globalint_root_fp: ∀ I, globalint I → root ∈ Nds I.

  Hypothesis contextualLeq_impl_globalint :
    ∀ I I', globalint I →  contextualLeq I I' → globalint I'.

  Hypothesis keyset_in_out : ∀ k In n, in_inset k In n → not_in_outset k In n → k ∈ ks n.
  
  Hypothesis globalint_root_inr : ∀ I k, globalint I → k ∈ inreach I root.

  Hypothesis globalint_inreach :
    ∀ I1 I n, I1 ≼ I → Nds I1 = {[n]} → globalint I → inreach I1 n = inreach I n.

  Hypothesis globalint_preserve_inreach : ∀ I I' I_n I_n' n,
      ✓ I → ✓ I' → (∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o) → globalint I
      → Nds I_n = {[n]} → Nds I_n' = {[n]} → inreach I_n n = inreach I_n' n
      → ∀ n', n' ∈ Nds I' → inreach I n' = inreach I' n'.

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

  Parameter findNext_spec : ∀ (n: node) (I_n : flowintUR) (C: gset key) (k: key),
      ({{{ hrep n I_n C ∗ ⌜k ∈ inreach I_n n⌝ }}}
           findNext #n #k
       {{{ (b: bool) (n': node), 
              RET (match b with true => (SOMEV #n') | false => NONEV end); 
               hrep n I_n C ∗ (match b with true => ⌜in_edgeset k I_n n n'⌝ |
                                          false => ⌜not_in_outset k I_n n⌝ end) }}})%I.

(* deal with contextualLeq *)
  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: node) (k: key) (I_n: flowintUR) (C: gset key),
      ({{{ hrep n I_n C ∗ ⌜in_inset k I_n n⌝
                    ∗ ⌜not_in_outset k I_n n⌝ }}}
           decisiveOp dop #n #k
       {{{ (b: bool) (I_n': flowintUR) (C': gset key) (res: bool),
                  RET (match b with false => NONEV | true => (SOMEV #res) end);
                  match b with false => hrep n I_n C |
                              true => hrep n I_n' C' ∗ Ψ dop k C C' res ∗ ⌜ C' ⊆ ks n⌝
                                      ∗ ⌜contextualLeq I_n I_n'⌝ ∗ ⌜Nds I_n' = {[n]}⌝ 
                                      ∗ ⌜inreach I_n n = inreach I_n' n⌝  end }}})%I.

  (* ---------- The invariant ---------- *)

  Definition searchStr γ γ_fp γ_k γ_inr γ_fi I C : iProp :=
    (own γ (● I) ∗ own γ_k (● prod (KS, C)) ∗ own γ_fp (● Nds I) ∗ ⌜globalint I⌝
      ∗ ([∗ set] n ∈ (Nds I), (∃ (b: bool) (In: flowintUR),
          (lockLoc n) ↦ #b
          ∗ (if b then True
            else (∃ Cn, hrep n In Cn ∗ own (γ_fi n) ((●{1/2} In)) ∗ own γ_k (◯ prod (ks(n), Cn))))
          ∗ own γ (◯ In) ∗ ⌜Nds In = {[n]}⌝ ∗ own (γ_fi n) ((●{1/2} In)) ∗ own (γ_inr n) (● (inreach In n))
        ))
    )%I.    

  Definition is_searchStr γ γ_fp γ_k γ_inr γ_fi C := (∃ I, (searchStr γ γ_fp γ_k γ_inr γ_fi I C))%I.

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
    rewrite -own_op. rewrite own_valid. iPureIntro.
    apply auth_both_valid.
  Qed.

  Lemma auth_own_incl_ks γ (x y: keysetUR) : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H. destruct H. destruct H0 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y = y) as Hy.
    { rewrite /(⋅) /=. destruct y; try done. }
    rewrite Hy in Hb. rewrite <- Ha in Hb. done.
  Qed.
  
  Lemma auth_ks_included (a1 a2 b1 b2: gset key) : 
             ✓ prod (a1, b1) → ✓ prod (a2, b2) → prod (a1, b1) ≼ prod (a2, b2) 
                → (a1 = a2 ∧ b1 = b2) ∨ 
                    (∃ a0 b0, a2 = a1 ∪ a0 ∧ b2 = b1 ∪ b0 ∧ a1 ## a0 ∧ b1 ## b0 ∧ b1 ⊆ a1 ∧ b2 ⊆ a2 ∧ b0 ⊆ a0).
  Proof.
    intros H1 H2 H. destruct H as [z H]. assert (✓ z). { apply (cmra_valid_op_r (prod (a1, b1))).
    rewrite <-H. done. } rewrite /(✓ prod (a1, b1)) /= in H1. rewrite /(✓ prod (a2, b2)) /= in H2.
    destruct z.
    - destruct p. rewrite /(✓ prod (g, g0)) /= in H0. rewrite /(⋅) /= in H.
      destruct (decide (b1 ⊆ a1)). destruct (decide (g0 ⊆ g)). destruct (decide (a1 ## g)).
      destruct (decide (b1 ## g0)). right. exists g, g0. set_solver. inversion H. inversion H.
      inversion H. inversion H.
    - rewrite /(✓ prodTop) /= in H0. exfalso. done.
    - rewrite /(⋅) /= in H. inversion H. left. done.
  Qed.  
  
  Lemma auth_ks_local_update_insert K1 C Cn k: 
              ✓ prod (KS, C) ∧ ✓ prod (K1, Cn) ∧ k ∈ K1 ∧ k ∉ Cn →
             (prod (KS, C), prod (K1, Cn)) ~l~> (prod (KS, C ∪ {[k]}), prod (K1, Cn ∪ {[k]})).
  Proof.
  Admitted.
(*  
    intros [H1 [H2 [H3 H4]]]. apply local_update_discrete. intros z.
    intros _. intros. split. rewrite /(✓ prod (KS, C ∪ {[k]})) /=. 
    rewrite /(cmra_valid keysetRA) /=. rewrite /(✓ prod (KS, C)) /= in H1.
    assert (k ∈ KS). { apply KS_full. } set_solver. rewrite /(opM) /= in H.
    destruct z. rewrite /(opM) /=. destruct c. destruct p. rewrite /(op) /= in H.
    rewrite /(cmra_op keysetRA) /= in H. destruct (decide (Cn ⊆ K1)).
    destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ## g0)).
    inversion H. rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. destruct (decide (Cn ∪ {[k]} ⊆ K1)).
    destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ∪ {[k]} ## g0)).
    assert (Cn ∪ g0 ∪ {[k]} = Cn ∪ {[k]} ∪ g0). { set_solver. } rewrite H0. done.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
    rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
    rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. done.
    rewrite /(opM) /=. inversion H. done.
  Qed.
*)
  Lemma auth_ks_local_update_delete K1 C Cn k:
              ✓ prod (KS, C) ∧ ✓ prod (K1, Cn) ∧ k ∈ K1 ∧ k ∈ Cn →
             (prod (KS, C), prod (K1, Cn)) ~l~> (prod (KS, C ∖ {[k]}), prod (K1, Cn ∖ {[k]})).
  Proof.
  Admitted.
(*
    intros [H1 [H2 [H3 H4]]]. apply local_update_discrete. intros z.
    intros _. intros. split. rewrite /(✓ prod (KS, C ∖ {[k]})) /=. 
    rewrite /(cmra_valid keysetRA) /=. rewrite /(✓ prod (KS, C)) /= in H1.
    set_solver. rewrite /(opM) /= in H.
    destruct z. rewrite /(opM) /=. destruct c. destruct p. rewrite /(op) /= in H.
    rewrite /(cmra_op keysetRA) /= in H. destruct (decide (Cn ⊆ K1)).
    destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ## g0)).
    inversion H. rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. destruct (decide (Cn ∖ {[k]} ⊆ K1)).
    destruct (decide (g0 ⊆ g)). destruct (decide (K1 ## g)). destruct (decide (Cn ∖ {[k]} ## g0)).
    assert (k ∉ g0). { set_solver. }
    assert ((Cn ∪ g0) ∖ {[k]} = Cn ∖ {[k]} ∪ g0). { set_solver. } rewrite H7. done.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    unfold not in n. exfalso. apply n. set_solver. unfold not in n. exfalso. apply n. set_solver.
    rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
    rewrite /(op) /= in H. rewrite /(cmra_op keysetRA) /= in H. inversion H.
    rewrite /(op) /=. rewrite /(cmra_op keysetRA) /=. done.
    rewrite /(opM) /=. inversion H. done.
  Qed.
*)
         
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

  Lemma inv_impl_fp γ γ_fp γ_k γ_inr γ_fi n I Ns C:
    searchStr γ γ_fp γ_k γ_inr γ_fi I C ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗ ⌜n ∈ Nds I⌝.
  Proof. Admitted.

(*    iIntros "(HInv & HNs & %)".
    iDestruct "HInv" as "(? & HIns & ? & ? & HNs' & %)".
    iPoseProof (auth_set_incl with "[$HNs $HNs']") as "%".
    iPureIntro. set_solver.
  Qed.                                       (* Made Proof using Type* *)
*)

  Lemma inv_impl_inreach γ γ_fp γ_k γ_inr γ_fi n I C Inr :
    searchStr γ γ_fp γ_k γ_inr γ_fi I C ∗ own (γ_inr n) (◯ Inr) ∗ ⌜n ∈ Nds I⌝
    -∗ ⌜Inr ⊆ inreach I n⌝.
  Proof. Admitted.

(*    iIntros "(HInv & HInr & %)".
    iDestruct "HInv" as "(? & ? & ? & ? & HIns & HNs' & % & HInrs)".
    iPoseProof ((big_sepS_elem_of_acc _ (Nds I) n) with "[$HInrs]") as "(HInr' & HInrRest)";
      first done.
    iDestruct "HInr'" as (Inr') "(HInr' & %)".
    rewrite <- H1.
    iApply (auth_set_incl with "[$HInr $HInr']").
  Qed.
*)

  Lemma inv_impl_inreach_eq γ γ_fp γ_k γ_inr γ_fi I C n I_n C_n :
    searchStr γ γ_fp γ_k γ_inr γ_fi I C ∗ own γ (◯ I_n) ∗ hrep n I_n C_n
    -∗ ⌜inreach I n = inreach I_n n⌝.
  Proof. Admitted.

(*    iIntros "(HInv & HIn & Hg)".
    iDestruct "HInv" as "(? & ? & HI & % & HIns & HNs' & % & HInrs)".
    iPoseProof (auth_own_incl γ I I_n with "[$HI $HIn]") as "%".
    iPoseProof (hrep_fp n I_n with "Hg") as "%".
    iPureIntro.
    by rewrite (globalint_inreach I_n I).
  Qed.
*)

(*  Lemma rewrite_inside_big_sep I I' γ_inr :
    ([∗ set] n ∈ Nds I', (∃ Inr_n : gsetUR key,
                            own (γ_inr n) (● Inr_n) ∗ ⌜Inr_n = inreach I n⌝))
      -∗ ⌜∀ n', n' ∈ Nds I' → inreach I n' = inreach I' n'⌝
      -∗ ([∗ set] n ∈ Nds I', (∃ Inr_n : gsetUR key,
                                 own (γ_inr n) (● Inr_n) ∗ ⌜Inr_n = inreach I' n⌝)).
  Proof.
    iIntros "Hbig %" .
    iApply (big_sepS_mono _ _ (Nds I') with "Hbig").
    intros. iIntros "H".
    specialize a with x. apply a in H. rewrite H. done.
  Qed.
*)
  (* ---------- Lock module proofs ---------- *)

  Lemma lockNode_spec (n: node):
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

  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)
(*
  Lemma ghost_update_step γ γ_fp γ_inr γ_c (n n': node) (k:key) (Ns: gset node) (I_n: flowintUR) (Inr: gset key):
          is_dict γ γ_fp γ_inr γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝∗ own (γ_inr n) (◯ Inr) ∗ ⌜k ∈ Inr⌝ ∗ own γ (◯ I_n)
                                      ∗ ⌜Nds I_n = {[n]}⌝ ∗ ⌜in_edgeset k I_n n n'⌝
                    ={ ⊤ }=∗ ∃ Ns' Inr', own γ_fp (◯ Ns') ∗ ⌜n' ∈ Ns'⌝ ∗ own (γ_inr n') (◯ Inr') ∗ ⌜k ∈ Inr'⌝
                                        ∗ own γ (◯ I_n).
  Proof.
    iIntros "#HInv (#Hfp & #Hin & #Hinr & #Hkin & HIn & #HNds & #Hedge)".
    iInv dictN as ">H". iDestruct "H" as (I Ns' C) "H". 
    iPoseProof (inv_impl_fp n Ns with "[$H $Hfp $Hin]") as "%".
    iPoseProof (inv_impl_inreach with "[$H $Hinr //]") as "%".
    iDestruct "H" as "(HC & #HCI & HI & #Hglob & Hstar & HAuthfp & #HINds & Hbinr)".
    iPoseProof (auth_own_incl with "[$HI $HIn]") as "%".
    unfold included in H1. destruct H1 as [I2 Hmult].
    iPoseProof ((own_valid γ (● I)) with "HI") as "%".
    iDestruct "HNds" as %HNds. iDestruct "Hglob" as %Hglob.
    iDestruct "Hedge" as %Hedge. iDestruct "Hkin" as %Hkin.
    assert (n' ∈ Nds I2).
    { apply (flowint_step I I_n _ k n). done. apply auth_auth_valid; try done.
      replace (Nds I_n). set_solver. done. done. }
    iAssert (⌜n' ∈ Nds I⌝)%I as "%".
    { iPureIntro.
      apply flowint_comp_fp in Hmult. set_solver.
    }
    iMod (own_update γ_fp (● Ns') (● Ns' ⋅ ◯ Ns') with "HAuthfp") as "HNs".
    apply auth_update_core_id. apply gset_core_id. done.
    iEval (rewrite own_op) in "HNs". iDestruct "HNs" as "(HNs0 & HNs')".
    iPoseProof ((big_sepS_elem_of_acc _ (Nds I) n') with "[$Hbinr]") as "(HInrn' & HInrRest)";
      first done.
    iDestruct "HInrn'" as (Inr') "[HInr' %]".
    iMod (own_update (γ_inr n') (● Inr') (● Inr' ⋅ ◯ Inr') with "HInr'") as "HInr'".
    apply auth_update_core_id. apply gset_core_id. done.
    iEval (rewrite own_op) in "HInr'". iDestruct "HInr'" as "(HInr0 & HInr')".
    iPoseProof ("HInrRest" with "[HInr0]") as "HInrs".
    { iExists (Inr'). by iFrame. }
    iAssert (⌜k ∈ Inr'⌝)%I as "%".
    { replace Inr'. iPureIntro.
      apply (flowint_inreach_step I I_n I2 _ n); try done.
        apply auth_auth_valid. done. try set_solver.
    }
    iModIntro. iSplitR "HNs' HInr' HIn". iNext. iExists I, Ns', C.
    iFrame "HC HI Hstar HNs0 HInrs". try repeat iSplitL; done.
    iModIntro. iExists Ns', Inr'. iFrame "HNs' HInr' HIn".
    iDestruct "HINds" as %HINds. iPureIntro. set_solver. 
  Qed.

  Lemma ghost_update_traverse γ γ_fp γ_inr γ_c (k:key):
          is_dict γ γ_fp γ_inr γ_c -∗ True ={ ⊤ }=∗ ∃ Ns Inr, own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝ 
                                                              ∗ own (γ_inr root) (◯ Inr) ∗ ⌜k ∈ Inr⌝.
  Proof.  
    iIntros "#HInv #Ht". iInv dictN as ">H".
    iDestruct "H" as (I Ns C) "(HC & % & HI & % & HIns & HNs & % & HInrs)".
    iMod (own_update γ_fp (● Ns) (● Ns ⋅ ◯ Ns) with "HNs") as "HNs".
    apply auth_update_core_id. apply gset_core_id. done.
    iEval (rewrite own_op) in "HNs". iDestruct "HNs" as "(HNs & #HNs')".
    iAssert (⌜root ∈ Nds I⌝ ∗ ⌜k ∈ inreach I root⌝)%I as "[% %]".
    { iPureIntro. split. by apply globalint_root_fp. by apply globalint_root_inr. }
    iPoseProof ((big_sepS_elem_of_acc _ (Nds I) root) with "[$HInrs]") as "(HInrRoot & HInrRest)";
    first done. iDestruct "HInrRoot" as (Inr) "[HInr %]".
    iMod (own_update (γ_inr root) (● Inr) (● Inr ⋅ ◯ Inr) with "HInr") as "HInr".
    apply auth_update_core_id. apply gset_core_id. done.
    iEval (rewrite own_op) in "HInr". iDestruct "HInr" as "(HInr0 & HInr)".
    iPoseProof ("HInrRest" with "[HInr0]") as "HInrs".
    { iExists (Inr). by iFrame. }
    iAssert (⌜k ∈ Inr⌝)%I as "%". by replace Inr.
    iModIntro. iSplitR "HNs' HInr". iNext. iExists I, Ns, C. iFrame "# % ∗".
    iModIntro. iExists Ns, Inr. iFrame "HInr HNs'". iPureIntro. set_solver. 
  Qed.

  Lemma ghost_update_decisiveOp γ γ_fp γ_inr γ_c (n: node) (k:key) (Ns: gset node) (I_n: flowintUR) (Inr: gset key):
          is_dict γ γ_fp γ_inr γ_c -∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ ∗ own (γ_inr n) (◯ Inr) ∗ ⌜k ∈ Inr⌝
                                        ∗ own γ (◯ I_n) ∗ hrep n I_n ∗ ⌜not_in_outset k I_n n⌝
                    ={ ⊤ }=∗ ⌜in_inset k I_n n⌝ ∗ hrep n I_n ∗ own γ (◯ I_n).
  Proof.
    iIntros "#Hinv  (HNs & % & HInr & % & HIn & Hg & %)".
    iInv dictN as ">HInv" "HClose".
    iDestruct "HInv" as (I Ns' C) "HInv".
    iPoseProof (inv_impl_fp n Ns with "[$HInv $HNs //]") as "%".
    (* k ∈ Inr → k ∈ inreach I n *)
    iPoseProof (inv_impl_inreach with "[$HInv $HInr //]") as "%".
    iPoseProof (inv_impl_inreach_eq n with "[$HInv $HIn $Hg //]") as "%".
    iPoseProof (auth_frag_valid γ with "HIn") as "%".
    iMod ("HClose" with "[-HInr Hg HIn]").
    { iNext. iExists I, Ns', C. done. }
    iPoseProof (hrep_fp n I_n with "Hg") as "%".
    iModIntro. iFrame. iPureIntro.
    apply inreach_impl_inset; try done. repeat split; try done.
    set_solver.
  Qed.
*)
  (* ---------- Refinement proofs ---------- *)

  Lemma traverse_spec (γ γ_fp γ_k: gname) γ_inr γ_fi (k: key) (n: node) (Ns: gset node) (I_n:flowintUR) :
       ⌜n ∈ Ns⌝ ∗ own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝ ∗ own (γ_inr n) (◯ (inreach I_n n)) ∗ ⌜k ∈ inreach I_n n⌝ -∗ 
          <<< ∀ C, is_searchStr γ γ_fp γ_k γ_inr γ_fi C >>>
                traverse #n #k
                    @ ⊤
          <<< ∃ (n': node) (Ns': gsetUR node) (I_n': flowintUR) (Cn': gset key),
                           is_searchStr γ γ_fp γ_k γ_inr γ_fi C ∗ ⌜n' ∈ Ns'⌝ ∗ own γ_fp (◯ Ns') ∗  hrep n' I_n' Cn' 
                         ∗ own (γ_fi n') ((●{1/2} I_n')) ∗ own γ_k (◯ prod (ks(n'), Cn'))
                         ∗ ⌜in_inset k I_n' n'⌝ ∗ ⌜not_in_outset k I_n' n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns I_n). iIntros "(#Hinn & #Hfp & #Hroot & #Hinrfp & #Hkinr)".
    iDestruct "Hinn" as %Hinn. iDestruct "Hroot" as %Hroot.
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n). iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "Hst". iDestruct "Hst" as (I) "(HI & HKS & HNDS & Hglob & Hstar)".
    iAssert (⌜n ∈ Nds I⌝)%I with "[HNDS]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns (Nds I)) with "[$]") as "%".
      iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (Nds I) n); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b In) "(Hlock & Hb & HIn & #HNds & Hfis & Hks)".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitL. iFrame "∗ % #".
    iExists I. iFrame "∗ % #". iApply "Hstar". iExists b, In.
    iFrame "# % ∗". eauto with iFrame. } iIntros "(Hloc & ?)".
    destruct b. { iExFalso. done. } iModIntro. 
    iPoseProof (auth_set_incl with "[$Hks $Hinrfp]") as "%".
    iDestruct "Hkinr" as "%". assert (k ∈ inreach In n) as Hkinr. { set_solver. } 
    iSplitR "Hb". iFrame "∗ % #". iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In.
    iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (Cn) "(Hrep & Hfil & Hks)". iDestruct "HNds" as %HNds.
    wp_bind (findNext _ _)%E. wp_apply ((findNext_spec n In Cn k) with "[Hrep]").
    iFrame; iPureIntro; done. iIntros (b n') "(Hrep & Hb)". destruct b. 
    - wp_pures. awp_apply (unlockNode_spec n). 
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
      iDestruct "Hst" as (I1) "(HI & HKS & HNDS & Hglob & Hstar)".
      iAssert (⌜n ∈ Nds I1⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (Nds I1)) with "[$]") as "%".
        iPureIntro. set_solver. }
      rewrite (big_sepS_delete _ (Nds I1) n); last by eauto. iDestruct "Hstar" as "(Hcln & Hstar)".
      iDestruct "Hcln" as (b In1) "(Hlock & Hbb & HIn & #HNds1 & Hfis & Hks1)".
      destruct b; first last. { iDestruct "Hbb" as (Cn') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (hrep_sep_star n In In1). 
      iFrame. } exfalso. done. }
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H3. apply leibniz_equiv in H3. replace In1.            
      iDestruct "Hb" as %Hb. iDestruct "HNds1" as %HNds1. iDestruct "Hglob" as %Hglob.
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof (own_valid with "HI") as "%". iAssert (⌜n' ∈ Nds I1⌝)%I as "%".
      { iPureIntro. assert (n' ∈ Nds I2). { apply (flowint_step I1 In _ k n). done. 
        apply auth_auth_valid. done. replace (Nds In). set_solver. done. done. }
        apply flowint_comp_fp in H4. set_solver. }
      rewrite (big_sepS_delete _ (Nds I1 ∖ {[n]}) n'); last first. admit. iDestruct "Hstar" as "(Hcln' & Hstar)".
      iDestruct "Hcln'" as (b In') "(Hlock' & Hbb' & HIn' & #HNds' & Hfis' & Hks1')".
      assert (k ∈ inreach In' n'). { admit. } assert (root ∈ Nds I1). { apply globalint_root_fp. done. }
      iMod (own_update (γ_inr n') (● inreach In' n') (● inreach In' n' ⋅ ◯ inreach In' n') with "Hks1'") as "HNs".
      apply auth_update_core_id. apply gset_core_id. done. iDestruct "HNs" as "(Hks1' & #Hinr1')".
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hks Hrep". iFrame "∗ # %".
      iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (Nds I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists true, In. iFrame "# % ∗". 
      rewrite (big_sepS_delete _ (Nds I1 ∖ {[n]}) n'); last first. admit. iFrame. iExists b, In'.
      iFrame "# % ∗".  iIntros "AU". iModIntro. iFrame "# % ∗". } iIntros "Hlock".
      iMod (own_update γ_fp (● Nds I1) (● Nds I1 ⋅ ◯ Nds I1) with "HNDS") as "HNs".
      apply auth_update_core_id. apply gset_core_id. done. iDestruct "HNs" as "(HAfp & #Hfp1)".
      iModIntro. iSplitL. iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (Nds I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists false, In. iFrame "# % ∗". iExists Cn. iFrame. 
      rewrite (big_sepS_delete _ (Nds I1 ∖ {[n]}) n'); last first. admit. iFrame. iExists b, In'.
      iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures. iSpecialize ("IH" $! n' (Nds I1) In').
      iApply "IH". iFrame "∗ # %". done.
    - iApply fupd_wp. iMod "AU" as (C) "[Hst [_ Hclose]]". iSpecialize ("Hclose" $! n Ns In Cn).
      iMod ("Hclose" with "[Hst Hfil Hks Hrep Hb]") as "HΦ". iFrame "∗ # %". admit.
      iModIntro. wp_pures. done.
  Admitted.

  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)

  Lemma ghost_update_keyset γ_k dop k Cn Cn' res K1 C:
          Ψ dop k Cn Cn' res ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
                             ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝  ==∗
                 ∃ C', Ψ dop k C C' res ∗ own γ_k (● prod (KS, C')) ∗ own γ_k (◯ prod (K1, Cn')).
  Proof. Admitted.
(*    iIntros "(#HΨ & Ha & Hf & % & %)". iPoseProof (auth_own_incl_ks γ_k (prod (KS, C)) (prod (K1, Cn))
                with "[$Ha $Hf]") as "%".
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
          { apply auth_update. apply auth_ks_local_update_insert. split; try done. apply auth_auth_valid. done. }
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
*)

  Theorem searchStrOp_spec (γ γ_fp γ_k: gname) γ_inr γ_fi (k: key) (dop: dOp):
      <<< ∀ C, is_searchStr γ γ_fp γ_k γ_inr γ_fi C >>>
            searchStrOp dop root #k
                  @ ⊤
      <<< ∃ C' (res: bool), is_searchStr γ γ_fp γ_k γ_inr γ_fi C' 
                                        ∗ Ψ dop k C C' res, RET #res >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH". wp_lam.
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I0) "(HI & HKS & HNDS & #Hglob & Hstar)".
    iDestruct "Hglob" as %Hglob. 
    assert (root ∈ Nds I0)%I as Hroot. { apply globalint_root_fp. done. }
    iMod (own_update γ_fp (● Nds I0) (● Nds I0 ⋅ ◯ Nds I0) with "HNDS") as "H".
    { apply auth_update_core_id. apply gset_core_id. done. } 
    iDestruct "H" as "(HNDS & #Hfp0)".
    rewrite (big_sepS_elem_of_acc _ (Nds I0) root); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b Ir) "(H1 & H2 & H3 & H4 & H5 & Hksr)".
    iMod (own_update (γ_inr root) (● inreach Ir root) (● inreach Ir root ⋅ ◯ inreach Ir root) with "Hksr") as "H".
    apply auth_update_core_id. apply gset_core_id. done. iDestruct "H" as "(Hksr & #Hinr)".
    iMod ("HAU" with "[HI HKS H1 H2 H3 H4 H5 Hstar HNDS Hksr] ") as "AU". 
    { iExists I0. iFrame "∗ % #". iApply "Hstar". iExists b, Ir. iFrame "∗ # %". }
    iModIntro. wp_bind (traverse _ _)%E.
    awp_apply (traverse_spec γ γ_fp γ_k γ_inr γ_fi k root (Nds I0) Ir). iFrame "∗ # %". admit.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "Hst". iAaccIntro with "Hst"; first by eauto with iFrame.
    iIntros (n Ns In Cn) "(Hst & #Hinn & #Hfp & Hrepn & Hfil & Hks & #Hinset & #Hnotout)".
    iDestruct "Hinn" as %Hinn. iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hrepn]"). eauto with iFrame.
    iIntros (b' In' Cn' res). iIntros "Hb". destruct b'.
    - iDestruct "Hb" as "(Hrep & #HΨ & #Hsub & #Hcon & #HNds' & #Hinreq)".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(HI & HKS & HNDS & #Hglob & Hstar)". 
      iDestruct "Hglob" as %Hglob'.
      iAssert (⌜n ∈ Nds I⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (Nds I)) with "[$]") as "%".
      iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (Nds I) n); last by eauto.
      iDestruct "Hstar" as "[Hn Hstar]".
      iDestruct "Hn" as (b' In1) "(Hlock & Hb & HIn & #HNds & Hfis & Hinreach)".
      destruct b'; first last. { iDestruct "Hb" as (Cn'') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (hrep_sep_star n In' In1). 
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hrep Hks".
      iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In1. 
      iFrame "∗ # %". eauto with iFrame. } iIntros "Hlock".
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof ((own_valid γ (● I)) with "HI") as "%". iDestruct "Hcon" as %Hcon.
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H2. apply leibniz_equiv in H2. replace In1.            
      iMod (own_updateP (flowint_update_P I In In') γ (● I ⋅ ◯ In) with "[HI HIn]") as (?) "H0".
      { apply (flowint_update I In In'). done. } { rewrite own_op. iFrame. }
      iPoseProof ((flowint_update_result γ I In In') with "H0") as (I') "(% & % & HIIn)".
      iAssert (own γ (● I') ∗ own γ (◯ In'))%I 
                                with "[HIIn]" as "(HI' & HIn')". { by rewrite own_op. }
      iPoseProof ((own_valid γ (● I')) with "HI'") as "%". iDestruct "Hsub" as "%".
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (ks n) C2) with "[HKS Hks]") as "Hgks".
      iFrame "% ∗ #". iPureIntro. apply (keyset_in_out k In n); try done. 
      iDestruct "Hgks" as (C2') "(#HΨC & Ha & Hf)".
      iAssert (own (γ_fi n) (●{1/2} In ⋅ ●{1/2} In))%I with "[Hfil Hfis]" as "H".
      { rewrite own_op. iFrame. } assert (∀ Iv: flowintUR, ●{1 / 2} Iv ⋅ ●{1 / 2} Iv ≡ ●{1/2 + 1/2} Iv) as Hv. 
      { intros Iv. rewrite (auth_auth_frac_op ((1/2)%Qp) ((1/2)%Qp) Iv). done. } 
      assert ((1/2 + 1/2)%Qp = (1)%Qp) as Hadd. { apply (Qp_div_2 1). }
      rewrite Hadd in Hv. iEval (rewrite Hv) in "H". 
      iPoseProof ((own_update (γ_fi n) (●In) (●In')) with "H") as ">Hγir".
      { apply (auth_update_auth In In' ε). apply local_update_discrete. intros mz.
        intros. admit. (* use contextualLeq *) } 
      iModIntro. iExists (C2'), res. iSplitL. iSplitR "HΨC".
      { iExists I'. assert (globalint I') as HI'.
      { apply (contextualLeq_impl_globalint I I'). done. done. }
      assert (Nds I = Nds I') as HH. { apply (contextualLeq_impl_fp I I'). done. }
      iEval (rewrite HH) in "Hstar". iEval (rewrite HH) in "HNDS". iFrame "∗ % #".
      iApply "Hstar". iExists false, In'. iEval (rewrite <-Hv) in "Hγir".
      iEval (rewrite own_op) in "Hγir". iDestruct "Hγir" as "(Hfil & Hfis)".
      iDestruct "Hinreq" as %Hinreq. iEval (rewrite Hinreq) in "Hinreach". 
      iFrame "∗ % #". iExists Cn'. eauto with iFrame. } done.
      iIntros "HΦ". iModIntro. wp_pures. done.
    - wp_match. awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(HI & HKS & HNDS & #Hglob & Hstar)". 
      iDestruct "Hglob" as %Hglob'.
      iAssert (⌜n ∈ Nds I⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (Nds I)) with "[$]") as "%".
      iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (Nds I) n); last by eauto.
      iDestruct "Hstar" as "[Hn Hstar]".
      iDestruct "Hn" as (b' In1) "(Hlock & Hb' & HIn & #HNds & Hfis & Hinreach)".
      destruct b'; first last. { iDestruct "Hb'" as (Cn'') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf. { iApply (hrep_sep_star n In' In1). 
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hb Hks".
      iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In1. 
      iFrame "∗ # %". eauto with iFrame. } iIntros "Hlock". iModIntro.
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H0. apply leibniz_equiv in H0. replace In1.            
      iSplitR "". iExists I. iFrame "∗ % #". iApply "Hstar". iExists false, In. iFrame "∗ % #".
      iExists Cn. iFrame. iIntros "AU". iModIntro. wp_pures. iApply "IH". done.
  Admitted.
 

















