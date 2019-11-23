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
                  unlockNode "p";; unlockNode "n";; "res" end.

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

(* RA for pair of keysets and contents *)
Class keysetG Σ := KeysetG { keyset_inG :> inG Σ (authUR (keysetUR)) }.
Definition keysetΣ : gFunctors := #[GFunctor (authUR (keysetUR))].

Instance subG_keysetΣ {Σ} : subG keysetΣ Σ → keysetG Σ.
Proof. solve_inG. Qed.

Section Lock_Coupling_Template.
  Context `{!heapG Σ, !flowintG Σ, !nodesetG Σ, !keysetG Σ}.
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

  Definition globalint first I : Prop := ✓I ∧ (first ∈ dom I) ∧ (∀ k n, ¬ (in_outset k I n)) 
                                  ∧ ∀ n, ((n = first) → (∀ k, in_inset k I n))
                                      ∧ ((n ≠ first) → (∀ k, ¬ in_inset k I n)).  

  Definition nodeinv first n I_n  C_n : Prop := C_n = keyset I_n n 
                                       ∧ (n = first → ∀ k, k ∈ KS → in_outsets k I_n).    

  (* ---------- Proved in GRASShopper for each implementation: ---------- *)

  Hypothesis node_implies_nodeinv : ∀ n I_n C first, (⌜✓I_n⌝)%I ∗ node n first I_n C -∗ node n first I_n C 
                                                                                      ∗ (⌜nodeinv first n I_n C⌝)%I. 

  Hypothesis keyset_def : ∀ k I_n n, in_inset k I_n n → ¬ in_outsets k I_n → k ∈ keyset I_n n.

  Hypothesis node_sep_star: ∀ n I_n I_n' C C' first, node n first I_n C ∗ node n first I_n' C' -∗ False.
                                                                     (* change node n first I C → node first n I C*)
  Hypothesis flowint_step :
    ∀ I I1 I2 k n first, I = I1 ⋅ I2 → in_outset k I1 n → globalint first I → n ∈ dom I2.

  Hypothesis globalint_add : ∀ I I' I_m first,
      globalint first I → I' = I ⋅ I_m → is_empty_flowint I_m → globalint first I'.

  Hypothesis contextualLeq_impl_globalint :
    ∀ I I' first, globalint first I → contextualLeq I I' → globalint first I'.
    
  Hypothesis outset_impl_inset: ∀ I1 I2 k n n',
    ✓ (I1⋅I2) → n' ∈ (dom I2) → in_inset k I1 n → in_outset k I1 n' → in_inset k I2 n'.
    
  Hypothesis successor_not_first : ∀ I I1 I2 I3 first n k C,
    I = I1⋅I2⋅I3 → globalint first I → in_outset k I1 n → nodeinv first n I2 C → n ≠ first. 

  Hypothesis inset_monotone : ∀ I I1 I2 k n,
    ✓ I → I = I1⋅I2 → n ∈ dom I1 → in_inset k I n → in_inset k I1 n.

  Hypothesis outset_distinct : ∀ I n, ✓I → (∃ k, in_outset k I n) → n ∉ dom I. 

(*   Hypothesis flowint_keyset_mono : ∀ k I1 I2, k ∈ keyset I1  → in_keyset k (I1 ⋅ I2). *)

  (* ---------- Coarse-grained specification ---------- *)

  Definition Ψ dop k (C: gset key) (C': gset key) (res: bool) : Prop :=
    match dop with
    | memberOp => (C' = C ∧ (if res then k ∈ C else k ∉ C))
    | insertOp => (C' = union C {[k]} ∧ (if res then k ∉ C else k ∈ C))
    | deleteOp => (C' = difference C {[k]} ∧ (if res then k ∈ C else k ∉ C))
    end.
(*
  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.
*)
  (* ---------- Helper functions specs - proved for each implementation in GRASShopper ---------- *)

  Parameter getLockLoc_spec : ∀ (n: Node),
      ({{{ True }}}
           getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  Parameter findNext_spec : ∀ first (n: Node) (I_n : flowintUR) (C: gset key) (k: key),
      ({{{ node n first I_n C ∗ ⌜in_inset k I_n n⌝ }}}
           findNext #n #k
       {{{ (b: bool) (n': Node), 
              RET (match b with true => (SOMEV #n') | false => NONEV end); 
               node n first I_n C ∗ (match b with true => ⌜in_outset k I_n n'⌝ |
                                          false => ⌜¬in_outsets k I_n⌝ ∗ ⌜n ≠ first⌝ end) }}})%I.

  Parameter decisiveOp_insert_spec : ∀ first (p n m: Node) (k: key) (I_p I_n: flowintUR) (C_p C_n: gset key),
      ({{{ node p first I_p C_p ∗ node n first I_n C_n ∗ hrep_spatial m ∗ ⌜n ≠ first⌝ ∗ ⌜m ≠ first⌝
                          ∗ ⌜in_inset k I_p p⌝ ∗ ⌜in_outset k I_p n ⌝ ∗ ⌜¬in_outsets k I_n⌝ }}}
           decisiveOp insertOp #p #n #k
       {{{ (C_p' C_n' C_m': gset key) (I_p' I_n' I_m': flowintUR) (res: bool), RET  #res;
                           node p first I_p' C_p' ∗ node n first I_n' C_n' ∗ node m first I_m' C_m'
                         ∗ ⌜Ψ insertOp k (C_p ∪ C_n) (C_p' ∪ C_n' ∪ C_m') res⌝ 
                         ∗ ⌜contextualLeq (I_p ⋅ I_n) (I_p' ⋅ I_n' ⋅ I_m')⌝
                         ∗ ⌜dom I_p' = {[p]}⌝ ∗ ⌜dom I_n' = {[n]}⌝ ∗ ⌜dom I_m' = {[m]}⌝
                         ∗ ⌜C_p' ⊆ keyset I_p' p⌝ ∗ ⌜C_n' ⊆ keyset I_n' n⌝ ∗ ⌜C_m' ⊆ keyset I_m' m⌝
                         ∗ ⌜keyset I_p' p ## keyset I_n' n⌝ ∗ ⌜keyset I_p' p ## keyset I_m' m⌝
                         ∗ ⌜keyset I_m' m ## keyset I_n' n⌝ 
                         ∗ ⌜keyset I_p' p ∪ keyset I_n' n ∪ keyset I_m' m = keyset I_p p ∪ keyset I_n n⌝ }}})%I.

  Parameter alloc_spec : 
      ({{{ True }}}
           alloc #()
       {{{ (m: Node) (l:loc), RET #m; hrep_spatial m ∗ ⌜lockLoc m = l⌝ ∗ l ↦ #false }}})%I.

  (* ---------- The invariant ---------- *)

  Definition main_searchStr (γ γ_fp γ_k : gname) first I (C: gset key)
    : iProp :=
       ( own γ_k (● prod (KS, C)) ∗ own γ (● I) ∗ ⌜globalint first I⌝
        ∗ ([∗ set] n ∈ (dom I), (∃ b: bool, (lockLoc n) ↦ #b ∗ if b then True
                                 else (∃ (I_n: flowintUR) (C_n: gset key), own γ (◯ I_n) ∗ node n first I_n C_n 
                                                ∗ ⌜dom I_n = {[n]}⌝ ∗ own γ_k (◯ prod (keyset I_n n, C_n)))))
        ∗ own γ_fp (● dom I)
    )%I.

  Definition is_searchStr γ γ_fp γ_k first C := (∃ I, (main_searchStr γ γ_fp γ_k first I C))%I.

  (* ---------- Assorted useful lemmas ---------- *)
  
  Lemma Ψ_insert_relation : ∀ (C C':gset key) k res, Ψ insertOp k C C' res → (C' = C ∧ k ∈ C ∧ res = false)
                                                                            ∨ C' = C ∪ {[k]}.
  Proof. Admitted.

  Lemma globalint_root_fp: ∀ I root, globalint root I → root ∈ dom I.
  Proof. 
    intros I root Hglob. unfold globalint in Hglob.
    destruct Hglob as [H1 [H2 H3]]. done.
  Qed.    

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
  
  (* ---------- Ghost state manipulation to make final proof cleaner ---------- *)



  (* ---------- Proofs of traverse and searchStrOp  ---------- *)

  Lemma traverse_spec (γ γ_fp γ_k: gname) first (k: key) (p n: Node) (Ns: gset Node) I_p C_p I_n C_n:
        ⌜p ∈ Ns⌝ ∗ ⌜n ∈ Ns⌝ ∗ own γ_fp (◯ Ns) ∗ ⌜first ∈ Ns⌝ ∗ ⌜in_inset k I_p p⌝ ∗ ⌜in_outset k I_p n⌝ ∗ ⌜n ≠ first⌝
                 ∗ own γ (◯ I_p) ∗ node p first I_p C_p ∗ ⌜dom I_p = {[p]}⌝ ∗ own γ_k (◯ prod (keyset I_p p, C_p))
                 ∗ own γ (◯ I_n) ∗ node n first I_n C_n ∗ ⌜dom I_n = {[n]}⌝ ∗ own γ_k (◯ prod (keyset I_n n, C_n)) -∗
          <<< ∀ C, is_searchStr γ γ_fp γ_k first C >>>
                traverse #p #n #k
                    @ ⊤
          <<< ∃ (p' n': Node) (Ns': gsetUR Node) (I_p' I_n': flowintUR) (C_p' C_n': gset key), 
                      is_searchStr γ γ_fp γ_k first C
                      ∗ ⌜p' ∈ Ns'⌝ ∗ ⌜n' ∈ Ns'⌝ ∗ own γ_fp (◯ Ns') ∗ own γ (◯ I_p') ∗ own γ (◯ I_n') 
                      ∗ node p' first I_p' C_p' ∗ node n' first I_n' C_n' ∗ ⌜n' ≠ first⌝
                      ∗ own γ_k (◯ prod (keyset I_p' p', C_p')) ∗ own γ_k (◯ prod (keyset I_n' n', C_n')) 
                      ∗ ⌜dom I_p' = {[p']}⌝ ∗ ⌜dom I_n' = {[n']}⌝
                      ∗ ⌜in_inset k I_p' p'⌝ ∗ ⌜in_outset k I_p' n'⌝ ∗ ⌜¬in_outsets k I_n'⌝, RET (#p', #n') >>>.
  Proof. Admitted.
(*    iLöb as "IH" forall (p n I_p I_n C_p C_n Ns).
    iIntros "(#Hinp & #Hinn & #Hfp & #Hfirst & #Hinset & #Hnotout & Hnotf 
                        & HIp & HrepP & #HdomP & HksP & HIn & HrepN & #HdomN & HksN)".
    iDestruct "Hinn" as %Hinn. iDestruct "Hinp" as %Hinp. iDestruct "Hfirst" as %Hfirst.
    iDestruct "Hnotf" as %Hnotf. iDestruct "Hnotout" as %Hnotout. 
    iDestruct "Hinset" as %Hinset. iDestruct "HdomP" as %HdomP. iDestruct "HdomN" as %HdomN.
    iIntros (Φ) "AU". wp_lam. wp_pures. wp_bind (findNext _ _)%E.
    iPoseProof ((own_op γ (◯ I_p) (◯ I_n)) with "[HIp HIn]") as "H"; first by eauto with iFrame.
    iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H.
    assert (✓ (I_p ⋅ I_n)). { apply (auth_frag_valid (◯ (I_p ⋅ I_n))). done. }
    assert (in_inset k I_n n). { apply (outset_impl_inset I_p I_n k p n); try done. set_solver. }
    wp_apply ((findNext_spec first n I_n C_n k) with "[HrepN]"). iFrame "∗ # %".
    iDestruct "H" as "(HIp & HIn)". iIntros (b n') "(HrepN & Hb)". destruct b.
    - wp_pures. wp_bind (lockNode _)%E.
      awp_apply (lockNode_spec n'). iApply (aacc_aupd_abort with "AU"); first done.
      iIntros (C0) "Hst". iDestruct "Hst" as (I)"(HKS & HI & Hglob & Hstar & HFP)".
      iDestruct "Hglob" as %Hglob. iDestruct "Hb" as %Hb.
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof (own_valid with "HIn") as "%".
      assert (✓ I_n) as HInv. { apply (auth_frag_valid (◯ I_n)). done. }
      assert (n' ∈ dom I2). { apply (flowint_step I I_n I2 k n' first); try done. }
      assert (n' ∈ dom I). { apply flowint_comp_fp in H2. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (dom I) n'); last by eauto.
      iDestruct "Hstar" as "[H Hstar]". iDestruct "H" as (b) "[Hlock Hn']".
      iAaccIntro with "Hlock". { iIntros "Hlock'". iModIntro. iSplitL "HI Hn' HKS Hstar HFP Hlock'".
      iExists I. iFrame "∗ % #". iApply "Hstar". iExists b. iFrame. eauto with iFrame. }
      iIntros "(Hlock' & ?)". destruct b. { iExFalso. done. }
      assert (first ∈ dom I). { apply globalint_root_fp. done. }
      iPoseProof ((auth_set_incl γ_fp Ns (dom I)) with "[$]") as "%".
      iMod (own_update γ_fp (● dom I) (● dom I ⋅ ◯ dom I) with "HFP") as "H".
      { apply auth_update_core_id. apply gset_core_id. done. }
      iDestruct "H" as "(HFP & #HIH)". iModIntro.
      iDestruct "Hn'" as (I_n' C_n') "(HIn' & HrepN' & HdomN' & HksN')".      
      iPoseProof ((own_op γ (◯ I_n) (◯ I_n' )) with "[HIn HIn']") as "H"; first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H8.
      assert (✓ (I_n ⋅ I_n')). { apply (auth_frag_valid (◯ (I_n ⋅ I_n'))). done. }
      iEval (rewrite -auth_frag_op) in "H". 
      iPoseProof (auth_own_incl with "[$HI $H]") as (I3)"%".
      iAssert (node n' first I_n' C_n' ∗ ⌜nodeinv first n' I_n' C_n'⌝)%I with "[HrepN']" as "(HrepN' & Hninv)". 
      { iApply (node_implies_nodeinv _ _ _). iFrame "∗ # %". iPureIntro.
        apply cmra_valid_op_r in H9. done. } iDestruct "Hninv" as %Hninv. 
      assert (n' ≠ first) as Hnotf'. { apply (successor_not_first I I_n I_n' I3 first n' k C_n'); try done. }
      iSplitL "HI HKS Hstar HFP Hlock'". iExists I. iFrame "∗ % #". iApply "Hstar". 
      iExists true. iFrame. iIntros "AU". iModIntro. wp_pures.
      awp_apply (unlockNode_spec p). iApply (aacc_aupd_abort with "AU"); first done. 
      iIntros (C1) "Hst". iDestruct "Hst" as (I1) "(HKS & HI & Hglob & Hstar & HNDS)".
      iDestruct "Hglob" as %Hglob1.
      iAssert (⌜p ∈ dom I1⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (dom I1)) with "[$]") as "%".
        iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (dom I1) p); last by eauto. iDestruct "Hstar" as "(Hclp & Hstar)".
      iDestruct "Hclp" as (b) "(Hlock & Hb)".
      destruct b; first last. { iDestruct "Hb" as (Ip' Cp') "(_ & Hrep' & _)".
      iAssert (⌜False⌝)%I with "[HrepP Hrep']" as %Hf. { iApply (node_sep_star p I_p Ip'); try iFrame. }
      exfalso. done. } iAaccIntro with "Hlock". { iIntros "Hlockp". iModIntro.    
      iSplitL "HI HKS Hstar HNDS Hlockp". iExists I1. iFrame "∗ % #". iApply "Hstar". 
      iExists true. iFrame. iIntros "AU"; eauto with iFrame. } iIntros "Hlockp". iModIntro.
      iSplitL "HIp HrepP HksP HKS HI Hstar HNDS Hlockp". iExists I1. iFrame "∗ % #". iApply "Hstar". 
      iExists false. iFrame. iExists I_p, C_p; iFrame "∗ # %". iIntros "AU".
      iModIntro. wp_pures. iSpecialize ("IH" $! n n' I_n I_n' C_n C_n' (dom I)).
      iApply ("IH" with "[-AU]"). iDestruct "HdomN'" as "%". iFrame "∗ # %".
      iDestruct "H" as "(HIn & HIn')". iFrame. iPureIntro. set_solver. done.
    - iApply fupd_wp. iMod "AU" as (C)"[Hst [_ Hclose]]". iSpecialize ("Hclose" $! p n Ns I_p I_n C_p C_n).
      iMod ("Hclose" with "[HIp HrepP HksP HIn HksN Hst HrepN Hb]") as "HΦ".
      iDestruct "Hb" as "(% & _)". iFrame "∗ # %". iModIntro. wp_pures. done.
  Qed.
*)
  Theorem searchStrOp_spec (γ γ_fp γ_k: gname) first (dop: dOp) (k: key):
      ⌜k ∈ KS⌝ -∗ <<< ∀ (C: gset key), is_searchStr γ γ_fp γ_k first C >>>
            searchStrOp dop first #k
                  @ ⊤
      <<< ∃ C' (res: bool), is_searchStr γ γ_fp γ_k first C' 
                                        ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "HKin" (Φ) "AU". iLöb as "IH". wp_lam.
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I0) "(H1 & H2 & % & H5 & H6)".
    assert (first ∈ (dom I0))%I as Hfirst. { apply globalint_root_fp. done. }
    iMod (own_update γ_fp (● (dom I0)) (● (dom I0) ⋅ ◯ (dom I0)) with "H6") as "HNs".
    { apply auth_update_core_id. apply gset_core_id. done. } 
    iDestruct "HNs" as "(HAfp & #Hfp0)". iDestruct "HKin" as %HKin.
    iMod ("HAU" with "[H1 H2 H5 HAfp]") as "AU". { iExists I0. iFrame "∗ # %". }
    iModIntro. wp_bind (lockNode _)%E. awp_apply (lockNode_spec first).
    iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst". 
    iDestruct "Hst" as (I1) "(HKS & HI & % & Hstar & Hdom)".
    assert (first ∈ dom I1). { apply globalint_root_fp. done. } 
    rewrite (big_sepS_elem_of_acc _ (dom I1) first); last by eauto.
    iDestruct "Hstar" as "(Hfirst & Hstar)". iDestruct "Hfirst" as (b) "(Hlockf & Hb)".
    iAaccIntro with "Hlockf". { iIntros "Hlockf". iModIntro. iSplitL.
    iExists I1. iFrame "∗ # %". iApply "Hstar". iExists b. iFrame. eauto. }
    iIntros "(Hlock & Hbb)". destruct b. { iDestruct "Hbb" as "%". exfalso. done. }
    iModIntro. iDestruct "Hb" as (I_f C_f) "(HIf & Hrepf & % & Hksf)". 
    iPoseProof (auth_own_incl with "[$HI $HIf]") as (Io)"%".
    iSplitR "HIf Hrepf Hksf". iExists I1. iFrame "∗ # %". iApply "Hstar".
    iExists true. iFrame. iIntros "AU". iModIntro.
    wp_pures. wp_bind (findNext _ _)%E. wp_apply ((findNext_spec first first I_f C_f k) with "[Hrepf]").
    iFrame. iPureIntro. unfold globalint in H0. destruct H0 as [? [? [? ?]]]. specialize (H6 first). 
    destruct H6 as [H6 _]. apply (inset_monotone I1 I_f Io k first); try done. set_solver. apply H6.
    done. iIntros (b n) "(Hrepf & Hb)". destruct b; last first.
    iDestruct "Hb" as "(_ & %)". unfold not in H4. exfalso. apply H4. done.
    wp_pures. wp_bind (lockNode _)%E. iDestruct "Hb" as "%". awp_apply (lockNode_spec n).
    iApply (aacc_aupd_abort with "AU"); first done. iIntros (C2) "Hst". 
    iDestruct "Hst" as (I2) "(HKS & HI & % & Hstar & Hdom)".
    iPoseProof (auth_own_incl with "[$HI $HIf]") as (Io')"%". assert (n ∈ dom I2).
    { assert (n ∈ dom Io'). { apply (flowint_step I2 I_f Io' k n first); try done. }
      apply flowint_comp_fp in H6. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (dom I2) n); last by eauto.
    iDestruct "Hstar" as "(Hn & Hstar)". iDestruct "Hn" as (b) "(Hlockn & Hb)".
    iAaccIntro with "Hlockn". { iIntros "Hlockf". iModIntro. iSplitR "HIf Hksf Hrepf".
    iExists I2. iFrame "∗ # %". iApply "Hstar". iExists b. iFrame. eauto with iFrame. }
    iIntros "(Hlock & Hbb)". destruct b. { iDestruct "Hbb" as "%". exfalso. done. }
    iMod (own_update γ_fp (● (dom I2)) (● (dom I2) ⋅ ◯ (dom I2)) with "Hdom") as "HNs".
    { apply auth_update_core_id. apply gset_core_id. done. } 
    iDestruct "HNs" as "(Hdom & #Hfp2)". iModIntro. iSplitL "HI Hdom HKS Hstar Hlock".
    iExists I2. iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. iIntros "AU". iModIntro.
    iDestruct "Hb" as (I_n C_n) "(HIn & Hrepn & % & Hksn)". wp_pures.
    assert (first ∈ dom I2). { apply globalint_root_fp. done. } wp_bind (traverse _ _ _)%E. 
    awp_apply ((traverse_spec γ γ_fp γ_k first k first n (dom I2) I_f C_f I_n C_n) with "[-AU]").
    iPoseProof (own_valid with "HIf") as "%". assert (✓ I_f) as ?.
    { apply (auth_frag_valid (◯ I_f)). done. } iFrame "∗ # %".
    iPureIntro. split. unfold globalint in H5. destruct H5 as [? [? [? ?]]]. 
    specialize (H14 first). destruct H14 as [H14 _]. apply (inset_monotone I2 I_f Io' k first); try done.
    set_solver. apply H14. done. assert (n ∉ dom I_f). { apply (outset_distinct I_f n); try done.      
    exists k. done. } set_solver. iApply (aacc_aupd_abort with "AU"); first done. iIntros (C3) "Hst".
    iAaccIntro with "Hst"; first by eauto with iFrame. iIntros ( p' n' Ns Ip' In' Cp' Cn') "(Hst & H)".
    iDestruct "H" as "(% & % & #Hfpns & HIp' & HIn' & Hrepp' & Hrepn' & % & Hksp' & Hksn' & % & % & % & % & %)".    
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures. wp_bind (alloc _)%E.
    wp_apply (alloc_spec); first done. iIntros (m lm) "(Hreps & % & Hlm)". 
    wp_let. wp_bind(decisiveOp _ _ _ _)%E. destruct dop.
    - admit.
    - iApply fupd_wp. iMod "AU" as (C4)"[Hst [Hclose _]]". iDestruct "Hst" as (I4) "Hst".
      destruct (decide (m ∈ dom I4)). { iDestruct "Hst" as "(HKS & HI & % & Hstar & Hdom)".
      rewrite (big_sepS_elem_of_acc _ (dom I4) m); last by eauto.
      iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
      iEval (rewrite H18) in "Hlockm".
      iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%". assert (False) as Hf. { done. }
      exfalso. done. } iDestruct "Hst" as "(HKS & HI & % & H)".
      assert (first ∈ dom I4). { apply globalint_root_fp. done. } 
      assert (m ≠ first). { set_solver. }
      iMod ("Hclose" with "[HKS HI H]") as "AU". iExists I4. iFrame "∗ # %". iModIntro.   
      wp_apply ((decisiveOp_insert_spec first p' n' m k Ip' In' Cp' Cn') with "[Hrepp' Hrepn' Hreps]").
      iFrame "∗ # %". iIntros (Cp'' Cn'' Cm'' Ip'' In'' Im'' res) "(Hrepp' & Hrepn' & Hrepm' & % & H)".  
      iDestruct "H" as "(% & % & % & % & % & % & % & % & % & % & %)".
      assert ((Cp'' ∪ Cn'' ∪ Cm'' = Cp' ∪ Cn' ∧ k ∈ Cp' ∪ Cn' ∧ res = false) ∨ Cp'' ∪ Cn'' ∪ Cm'' = Cp' ∪ Cn' ∪ {[k]}).
      { apply (Ψ_insert_relation (Cp' ∪ Cn') (Cp'' ∪ Cn'' ∪ Cm'') k res). done. } destruct H34.
      destruct H34 as [H34 [Hkin Hres]].
      + iPoseProof ((own_op γ_k (◯ prod (keyset Ip' p', Cp')) (◯ prod (keyset In' n', Cn')) 
                          with "[Hksp' Hksn']")) as "H"; first by eauto with iFrame.
        assert (◯ prod (keyset Ip' p', Cp') ⋅ ◯ prod (keyset In' n', Cn') =
                                     ◯ (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn'))).
        { apply (auth_frag_op (prod (keyset Ip' p', Cp')) (prod (keyset In' n', Cn'))). }                         
        iEval (rewrite H35) in "H".
        iPoseProof (own_valid with "H") as "%". 
        assert (✓ (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn'))).
        { apply (auth_frag_valid (◯ (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn')))). done. }
        unfold op,prodOp in H37. repeat case_decide; 
                  [ simpl | try exfalso; eauto | try exfalso; eauto | try exfalso; eauto | try exfalso; eauto].
        assert (prod (keyset Ip' p', Cp') ⋅ prod (keyset In' n', Cn') = 
                          prod (keyset Ip'' p', Cp'') ⋅ prod (keyset In'' n', Cn'') ⋅ prod (keyset Im'' m, Cm'')).
        { admit. (* unfold op, prodOp. repeat case_decide; try done. rewrite H34. rewrite H35. reflexivity.
          exfalso. apply H54. set_solver by eauto. exfalso. apply H53. set_solver by eauto.
          exfalso. apply H51. set_solver by eauto. exfalso. apply H50. set_solver by eauto. *) }
        iEval (rewrite H42) in "H". iDestruct "H" as "((Hksp & Hksn) & Hksm)". 
        clear H27. clear H28. clear H29. clear H30. clear H31. clear H32. clear H33. clear H34.
        clear H36. clear H38. clear H39. clear H40. clear H41. clear H42. clear H37. clear H35.
        wp_let. wp_bind (unlockNode _)%E. awp_apply (unlockNode_spec p')%E.
        iApply (aacc_aupd_commit with "AU"); first done. iIntros (C5) "Hst".                              
        iDestruct "Hst" as (I5) "(HKS & HI & % & Hstar & Hdom)".
        destruct (decide (m ∈ dom I5)). { 
        rewrite (big_sepS_elem_of_acc _ (dom I5) m); last by eauto.
        iDestruct "Hstar" as "(Hm & Hstar)". iDestruct "Hm" as (b) "(Hlockm & Hb)".
        iEval (rewrite H18) in "Hlockm".
        iDestruct (mapsto_valid_2 with "Hlm Hlockm") as "%". assert (False) as Hf. { done. }
        exfalso. done. }
        iAssert (⌜p' ∈ dom I5⌝)%I with "[Hdom]" as "%".
        { iPoseProof ((auth_set_incl γ_fp Ns (dom I5)) with "[$]") as "%".
          iPureIntro. set_solver. }   
        rewrite (big_sepS_elem_of_acc _ (dom I5) p'); last by eauto.
        iDestruct "Hstar" as "[Hp' Hstar]". iDestruct "Hp'" as (b) "(Hlock & Hb)".
        destruct b; last first. { iDestruct "Hb" as (Ip1 Cp1) "(_ & Hpnode & _)".
        iAssert (⌜False⌝)%I with "[Hrepp' Hpnode]" as %Hf. { iApply (node_sep_star p' Ip'' Ip1). 
        iFrame. } exfalso. done. }
        iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitL "HKS HI Hdom Hstar Hlock".
        iExists I5. iFrame "∗ # %". iApply "Hstar". iExists true. iFrame. iIntros "AU".
        iModIntro. eauto with iFrame. } iIntros "Hlock".  
        iPoseProof (own_valid with "HI") as "%". 
        iAssert (own γ (◯ (Ip'⋅ In')))%I with "[HIp' HIn']" as "HIpn".
        { rewrite auth_frag_op. rewrite own_op. iFrame. }
        iMod (own_updateP (flowint_update_P I5 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')) γ
                          (● I5 ⋅ ◯ (Ip' ⋅ In')) with "[HI HIpn]") as (Io'') "H0".
        { apply (flowint_update I5 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im'')). done. }
        { rewrite own_op. iFrame. }
        iPoseProof ((flowint_update_result γ I5 (Ip' ⋅ In') (Ip'' ⋅ In'' ⋅ Im''))
                      with "H0") as (I') "(% & % & HIIpnm)".
        iEval (rewrite own_op) in "HIIpnm". iDestruct "HIIpnm" as "(HI' & HIpnm'')".
        iPoseProof ((own_valid γ (● I')) with "HI'") as "%". iDestruct "HIpnm''" as "((HIp & HIn) & HIm)".
        iMod (own_update γ_fp (● dom I5) (● (dom I5 ∪ {[m]}) ⋅ ◯ (dom I5 ∪ {[m]})) with "[Hdom]") as "H".
        { apply (auth_update_alloc (dom I5) (dom I5 ∪ {[m]}) (dom I5 ∪ {[m]})).
        apply gset_local_update. set_solver. } done. iDestruct "H" as "(Hdom & #Hfp5)".
        assert (dom I' = dom I5 ∪ {[m]}). { destruct H31 as [I_o H31]. destruct H31.
        apply flowint_comp_fp in H31. assert (dom (Ip' ⋅ In') = {[p']} ∪ {[n']}). 
        { assert (Ip' ⋅ In' = Ip' ⋅ In'). { reflexivity. } apply flowint_comp_fp in H34.
          rewrite H34. rewrite H13. rewrite H14. done. } apply flowint_comp_fp in H33.
          rewrite H31. assert (dom (Ip'' ⋅ In'' ⋅ Im'') = {[p']} ∪ {[n']} ∪ {[m]}).
          { admit. } rewrite H33. rewrite H35. rewrite H34. admit. (*set_solver.*) }
        assert (globalint first I'). { apply (contextualLeq_impl_globalint I5 I' first); try done. }
        iModIntro. iExists C5, res. iSplitR "Hrepn' Hksn HIn". iSplitL. iExists I'.
        iEval (rewrite <-H33) in "Hdom". iFrame "∗ # %". assert (m ∈ dom I'). { rewrite H33. set_solver. }
        rewrite (big_sepS_delete _ (dom I') m); last by eauto. iSplitL "Hksm Hlm HIm Hrepm'".
        iExists false. iEval (rewrite <-H18) in "Hlm". iFrame. iExists Im'', Cm''. iFrame "∗ % #".
        assert (dom I' ∖ {[m]} = dom I5). { rewrite H33. set_solver. } iEval (rewrite H36).
        iApply "Hstar". iExists false. iFrame. iExists Ip'', Cp''. iFrame "∗ # %". iPureIntro.
         
        iIntros "AU".














    iIntros (Ns). iIntros "#HInv H" (Φ) "AU". iLöb as "IH".
    iDestruct "H" as "#(Hfp & Hroot)". wp_lam. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec γ γ_fp γ_c root Ns). done. eauto with iFrame.
    iAssert (True)%I as "#Ht". { done. } iAaccIntro with "Ht". eauto with iFrame.
    iIntros (Ir) "(HIr & HrepR & #HNdsR)". iModIntro. wp_pures.
    wp_bind (findNext _ _)%E. awp_apply (findNext_spec root Ir k).
    iAaccIntro with "HrepR". eauto with iFrame.
    iIntros (b n) "(HrepR & Hb)". destruct b; last first.
    - iModIntro. wp_pures. iApply "IH". iFrame "Hfp Hroot". done.
    - iModIntro. wp_pures. wp_bind (lockNode _)%E. iDestruct "Hb" as "#Hb".
      iDestruct (ghost_update_root_inset γ γ_fp γ_c k Ir with "[HInv] [HIr HNdsR]") as ">HN".
      done. eauto with iFrame. iDestruct "HN" as "(HIr & #HinsetR)".
      iDestruct (ghost_update_step γ γ_fp γ_c root n k Ns Ir with "[HInv] [HIr HNdsR Hb HinsetR]") as ">HN".
      done. eauto with iFrame. iDestruct "HN" as (Ns') "(#Hfp' & #HinN & #HinR & HIr & _)".
      awp_apply (lockNode_spec γ γ_fp γ_c n Ns'). done. eauto with iFrame.
      iAaccIntro with "Ht". eauto with iFrame.
      iIntros (In) "(HIn & HrepN & #HNdsN)". iModIntro. wp_pures.
      wp_bind (traverse _ _ _)%E.
      iDestruct (ghost_update_step_2 γ γ_fp γ_c root n k Ns' Ir In with 
      "[HInv] [HIr HNdsR HIn HNdsN HinsetR Hb]") as ">HN".
      done. eauto with iFrame. iDestruct "HN" as "(HIr & HIn & #HinsetN)".
      awp_apply (traverse_spec γ γ_fp γ_c Ir In Ns' root n k with "[] [HIr HIn HrepR HrepN]") . done.
      iFrame "HrepN HIn HNdsN HinsetN Hfp' HinR HinN HIr HrepR HNdsR Hb".
      iAaccIntro with "Ht". eauto with iFrame.
      iIntros (p' n' Ip' In') "(HIp' & HIn' & HrepP' & HrepN' & #HNdsP' & 
      #HNdsN' & #HedgeP' & #HinsetN' & #HnotoutN')".
      iModIntro. wp_pures. wp_bind(alloc _)%E. awp_apply (alloc_spec γ γ_fp γ_c). done.
      iAaccIntro with "Ht". eauto with iFrame.
      iIntros (m Im) "(HIm & HempM & #HNdsM & #HM & #HempIntM)".
      iModIntro. wp_pures. wp_bind (decisiveOp _ _ _ _)%E. iDestruct "HempM" as "_".
      awp_apply (decisiveOp_3_spec dop Ip' In' Im p' n' m k).
      iAssert (empty_node m)%I as "HempM". { admit. }
      iAssert (hrep p' Ip' ∗ hrep n' In' ∗ empty_node m ∗ ⌜is_empty_flowint Im⌝ ∗ ⌜Nds Im = {[m]}⌝
               ∗ ⌜✓ Im⌝ ∗ ⌜in_edgeset k Ip' p' n'⌝ ∗ ⌜in_inset k In' n'⌝ ∗ ⌜not_in_outset k In' n'⌝)%I 
               with "[HrepP' HrepN' HempM]" as "Haac".
      { iFrame "HrepP' HrepN' HempM HempIntM HNdsM HM HedgeP' HinsetN' HnotoutN'". }
      iAaccIntro with "Haac". iIntros "(HrepP' & HrepN' & _)". iModIntro. iFrame "AU HIp' HIn' HrepP' HrepN' HIm".
      iIntros (b Ip'' In'' Im'' res) "Hb'". destruct b.
      + iDestruct "Hb'" as "(HrepP'' & HrepN'' & HrepM'' & #HΨ & #HNdsP'' & #HNdsN'' & #HNdsM'' & #Hcon)".
        iInv dictN as ">H". iDestruct "H" as (I N' C') "(HC & HCI & HI & Hglob & Hstar & HAfp & HINds)".
        iPoseProof (own_valid with "HI") as "%". 
        iAssert (own γ (◯ (Ip'⋅ In' ⋅ Im)))%I with "[HIp' HIn' HIm]" as "HIpnm'".
        { rewrite auth_frag_op. rewrite own_op. iFrame. rewrite auth_frag_op. rewrite own_op. iFrame. }
        iDestruct "Hcon" as %Hcon.
        iMod (own_updateP (flowint_update_P I (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im'')) γ
                          (● I ⋅ ◯ (Ip' ⋅ In' ⋅ Im)) with "[HI HIpnm']") as (Io) "H0".
        { apply (flowint_update I (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im'')). done. }
        { rewrite own_op. iFrame. }
        iPoseProof ((flowint_update_result γ I (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im''))
                      with "H0") as (I') "(% & % & HIIpnm)".
        iEval (rewrite own_op) in "HIIpnm". iDestruct "HIIpnm" as "(HI' & HIpnm'')".
        iPoseProof ((own_valid γ (● I')) with "HI'") as "%".
        iDestruct "HinsetN'" as %HinsetN'. iDestruct "HnotoutN'" as %HnotoutN'.
        iPoseProof ((Ψ_keyset_theorem dop k (Ip' ⋅ In' ⋅ Im) (Ip'' ⋅ In'' ⋅ Im'')
                                      I I' res) with "[-] [$HΨ]") as "#HΨI".
        { iFrame "# %". iFrame "Hglob". iPureIntro. repeat split.
          - apply flowint_keyset_mono. rewrite (comm op). apply flowint_keyset_mono.
            by apply (flowint_keyset k In' n').
          - apply auth_auth_valid. apply H.
          - apply auth_auth_valid. apply H2. }
        assert (Nds I = Nds I') as HFP. { apply contextualLeq_impl_fp. done. }
        iDestruct "HCI" as %HCI. iEval (rewrite <-HCI) in "HΨI". iDestruct "Hglob" as %Hglob.
        iMod "AU" as (C) "[hoho [_ Hcl]]".
        iDestruct (auth_agree with "HC hoho") as %Hauth.
        iMod (auth_update γ_c (cont I') with "HC hoho") as "[HC hoho]".
        iSpecialize ("Hcl" $! (cont I') res). iEval (rewrite <- Hauth) in "Hcl".
        iMod ("Hcl" with "[hoho HΨI]") as "HΦ". iFrame. iEval (rewrite <- Hauth). done.
        iDestruct "HIpnm''" as "((HIp'' & HIn'') & HIm'')". iModIntro. iSplitR "HrepP'' HrepN'' HIp'' HIn'' HΦ".
        * iNext. iExists I', N', (cont I'). unfold main_inv. iEval (rewrite HFP) in "Hstar".
          iEval (rewrite HFP) in "HINds". iFrame "HC HI' Hstar HAfp HINds". assert (globalint I') as HI'. 
          { by apply (contextualLeq_impl_globalint I I'). } iPureIntro. eauto.
        * iModIntro. wp_let. iDestruct "HΦ" as "_". awp_apply (unlockNode_spec γ γ_fp γ_c p' Ns').





