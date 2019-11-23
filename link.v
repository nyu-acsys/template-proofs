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
Variable lockLoc : Node → loc.
Variable getLockLoc : val.

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

Definition traverse : val :=
  rec: "tr" "n" "k" :=
    lockNode "n";;
    match: (findNext "n" "k") with
      NONE => "n"
    | SOME "n'" => unlockNode "n";; "tr" "n'" "k"
    end.

Definition searchStrOp (Ψ: dOp) (root: Node) : val :=
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
Class nodesetG Σ := NodesetG { nodeset_inG :> inG Σ (authR (gsetUR Node)) }.
Definition nodesetΣ : gFunctors := #[GFunctor (authR (gsetUR Node))].

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
  
  Parameter in_inset : key → flowintUR → Node → Prop.
  Parameter in_outset : key → flowintUR → Node → Prop.      
  Parameter linkset : flowintUR → Node → gset key.               (*inreach → linkset*)
  Parameter keyset : flowintUR → Node → gset key.                 (* define as a lemma keyset I_n n *)

  Parameter node : Node → flowintUR → gset key → iProp.
  Parameter node_timeless_proof : ∀ n I C, Timeless (node n I C).
  Instance node_timeless n I C: Timeless (node n I C).
  Proof. apply node_timeless_proof. Qed.

  Definition in_outsets k In := ∃ n, in_outset k In n.

  Definition globalint root I : Prop := ✓I ∧ (root ∈ dom I) ∧ (∀ k n, ¬ (in_outset k I n)) 
                                  ∧ ∀ n, ((n = root) → (∀ k, in_inset k I n ∧ k ∈ linkset I n))
                                      ∧ ((n ≠ root) → (∀ k, ¬ in_inset k I n ∧ k ∉ linkset I n)).

  Definition nodeinv I_n n: Prop := (∀ k, k ∈ linkset I_n n ∧ ¬ in_outsets k I_n → in_inset k I_n n).    

  (* ---------- Proved in GRASShopper for each implementation: ---------- *)

  Hypothesis keyset_def : ∀ k I_n n, in_inset k I_n n → ¬ in_outsets k I_n → k ∈ keyset I_n n.

  (* TODO: instead have node n I_n C -∗ n ↦ _ and use
     iDestruct (mapsto_valid_2 with "H1 H2") as %[]
     to say n ↦ _ ∗ n ↦ _ -∗ False *)
  Hypothesis node_sep_star: ∀ n I_n I_n' C C', node n I_n C ∗ node n I_n' C' -∗ False.

  Hypothesis node_implies_nodeinv : ∀ n I_n C, (⌜✓I_n⌝)%I ∗ node n I_n C -∗ node n I_n C ∗ (⌜nodeinv I_n n⌝)%I. 
                                                        (* check the name *)
   
  Hypothesis flowint_comp_fp : ∀ I1 I2 I, I = I1 ⋅ I2 → dom I = dom I1 ∪ dom I2.      (* move to the flows file *)

  Hypothesis inreach_monotone :                                           (* globalint_inreach → inreach_monotone *)
    ∀ I I1 I2 k n,  ✓ I → I = I1⋅I2 → n ∈ dom I1 → k ∈ linkset I n → k ∈ linkset I1 n.
      
  Hypothesis outset_distinct : ∀ I n, (∃ k, in_outset k I n) → n ∉ dom I. 
  
  Hypothesis flowint_inreach_step : 
    ∀ I I1 I2 k n1 n2, ✓ I → I = I1⋅I2 → in_outset k I1 n2 → k ∈ linkset I1 n1 → k ∈ linkset I2 n2.

  Hypothesis flowint_step :
    ∀ I I1 I2 k n root, I = I1 ⋅ I2 → ✓I → in_outset k I1 n → globalint root I → n ∈ dom I2.
  
  (* ---------- Coarse-grained specification ---------- *)

  Definition Ψ dop k (C: gset key) (C': gset key) (res: bool) : iProp :=
    match dop with
    | memberOp => (⌜C' = C ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    | insertOp => (⌜C' = union C {[k]} ∧ (if res then k ∉ C else k ∈ C)⌝)%I
    | deleteOp => (⌜C' = difference C {[k]} ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    end.

  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.


  (* ---------- Helper functions specs ---------- *)
  (* These are proved for each implementation in GRASShopper *)

  Parameter getLockLoc_spec : ∀ (n: Node),
      ({{{ True }}}
           getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  Parameter findNext_spec : ∀ (n: Node) (I_n : flowintUR) (C: gset key) (k: key),
      ({{{ node n I_n C ∗ ⌜k ∈ linkset I_n n ∨ in_inset k I_n n⌝ }}}
           findNext #n #k
       {{{ (b: bool) (n': Node), 
              RET (match b with true => (SOMEV #n') | false => NONEV end); 
               node n I_n C ∗ (match b with true => ⌜in_outset k I_n n'⌝ |
                                          false => ⌜¬in_outsets k I_n⌝ end) }}})%I.

  Parameter decisiveOp_spec : ∀ (dop: dOp) (n: Node) (k: key) (I_n: flowintUR) (C: gset key),
      ({{{ node n I_n C ∗ ⌜in_inset k I_n n⌝
                    ∗ ⌜¬in_outsets k I_n⌝ }}}
           decisiveOp dop #n #k
       {{{ (b: bool) (C': gset key) (res: bool),
                  RET (match b with false => NONEV | true => (SOMEV #res) end);
                  match b with false => node n I_n C |
                              true => node n I_n C' ∗ Ψ dop k C C' res ∗ ⌜ C' ⊆ keyset I_n n⌝ end }}})%I.

  (* ---------- The invariant ---------- *)
  
  (* should change the name so as to not confuse with the node-level predicate *)
  (* Sid: can we make these two one predicate called SchStr like in the paper? *)
  Definition searchStr γ γ_fp γ_k γ_inr γ_fi root I C : iProp :=                             
    (own γ (● I) ∗ own γ_k (● prod (KS, C)) ∗ own γ_fp (● dom I) ∗ ⌜globalint root I⌝
      ∗ ([∗ set] n ∈ (dom I), (∃ (b: bool) (I_n: flowintUR),
          (lockLoc n) ↦ #b
          ∗ (if b then True
            else (∃ C_n, node n I_n C_n ∗ own (γ_fi n) ((●{1/2} I_n)) ∗ own γ_k (◯ prod (keyset I_n n, C_n))))
          ∗ own γ (◯ I_n) ∗ ⌜dom I_n = {[n]}⌝ ∗ own (γ_fi n) ((●{1/2} I_n)) ∗ own (γ_inr n) (● (linkset I_n n))
        ))
    )%I.    

  Definition is_searchStr γ γ_fp γ_k γ_inr γ_fi root C := (∃ I, (searchStr γ γ_fp γ_k γ_inr γ_fi root I C))%I.

  (* ---------- Assorted useful lemmas ---------- *)

  Lemma globalint_root_fp: ∀ I root, globalint root I → root ∈ dom I.
  Proof. 
    intros I root Hglob. unfold globalint in Hglob.
    destruct Hglob as [H1 [H2 H3]]. done.
  Qed.    

  Lemma globalint_root_inr : ∀ I Ir root k, globalint root I ∧ Ir ≼ I 
                                           ∧ dom Ir = {[root]} → k ∈ linkset Ir root.
  Proof.
    intros I Ir root k Hglob. destruct Hglob as [Hglob [H1 H2]].
    unfold globalint in Hglob. destruct Hglob as [H3 [H4 [H5 H6]]].
    specialize (H6 root). assert (k ∈ linkset I root).
    { apply H6. done. } destruct H1 as [I2 H1].
     apply (inreach_monotone I Ir I2 k root); try done. set_solver.
  Qed. 

  Lemma auth_own_incl γ (x y: flowintUR) : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro.
    apply auth_both_valid.
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

  Lemma auth_own_incl_ks γ (x y: keysetUR) : own γ (● x) ∗ own γ (◯ y) -∗ ⌜y ≼ x⌝.
  Proof.
    rewrite -own_op. rewrite own_valid. iPureIntro. rewrite auth_valid_discrete.
    simpl. intros H. destruct H. destruct H0 as [a Ha]. destruct Ha as [Ha Hb].
    destruct Hb as [Hb Hc]. apply to_agree_inj in Ha.
    assert (ε ⋅ y = y) as Hy.
    { rewrite /(⋅) /=. destruct y; try done. }
    rewrite Hy in Hb. rewrite <- Ha in Hb. done.
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


  Lemma ghost_update_keyset γ_k dop k Cn Cn' res K1 C:
          Ψ dop k Cn Cn' res ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
                             ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝  ==∗
                 ∃ C', Ψ dop k C C' res ∗ own γ_k (● prod (KS, C')) ∗ own γ_k (◯ prod (K1, Cn')).
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

  (* ---------- Proofs of traverse and searchStrOp ---------- *)

  Lemma traverse_spec (γ γ_fp γ_k: gname) γ_inr γ_fi root (k: key) (n: Node) (Ns: gset Node) (I_n:flowintUR) :
       ⌜n ∈ Ns⌝ ∗ own γ_fp (◯ Ns) ∗ ⌜root ∈ Ns⌝ ∗ own (γ_inr n) (◯ (linkset I_n n)) ∗ ⌜k ∈ linkset I_n n⌝ -∗ 
          <<< ∀ C, is_searchStr γ γ_fp γ_k γ_inr γ_fi root C >>>
                traverse #n #k
                    @ ⊤
          <<< ∃ (n': Node) (Ns': gsetUR Node) (I_n': flowintUR) (Cn': gset key),
                           is_searchStr γ γ_fp γ_k γ_inr γ_fi root C ∗ ⌜n' ∈ Ns'⌝ ∗ own γ_fp (◯ Ns') ∗ node n' I_n' Cn' 
                         ∗ own (γ_fi n') ((●{1/2} I_n')) ∗ own γ_k (◯ prod (keyset I_n' n', Cn')) ∗ ⌜dom I_n' = {[n']}⌝
                         ∗ ⌜in_inset k I_n' n'⌝ ∗ ⌜¬in_outsets k I_n'⌝, RET #n' >>>.
  Proof.
    iLöb as "IH" forall (n Ns I_n). iIntros "(#Hinn & #Hfp & #Hroot & #Hinrfp & #Hkinr)".
    iDestruct "Hinn" as %Hinn. iDestruct "Hroot" as %Hroot.
    iIntros (Φ) "AU". wp_lam. wp_let. wp_bind(lockNode _)%E.
    awp_apply (lockNode_spec n). iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C0) "Hst". iDestruct "Hst" as (I) "(HI & HKS & HNDS & Hglob & Hstar)".
    iAssert (⌜n ∈ dom I⌝)%I with "[HNDS]" as "%".
    { iPoseProof ((auth_set_incl γ_fp Ns (dom I)) with "[$]") as "%".
      iPureIntro. set_solver. }
    rewrite (big_sepS_elem_of_acc _ (dom I) n); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b In) "(Hlock & Hb & HIn & #HNds & Hfis & Hks)".
    iAaccIntro with "Hlock". { iIntros "H". iModIntro. iSplitL. iFrame "∗ % #".
    iExists I. iFrame "∗ % #". iApply "Hstar". iExists b, In.
    iFrame "# % ∗". eauto with iFrame. } iIntros "(Hloc & ?)".
    destruct b. { iExFalso. done. } iModIntro. 
    iPoseProof (auth_set_incl with "[$Hks $Hinrfp]") as "%".
    iDestruct "Hkinr" as "%". assert (k ∈ linkset In n) as Hkinr. { set_solver. }
    iPoseProof (own_valid with "HIn") as "%". rename H2 into HInV.
    assert (✓ In) as HInv. { apply (auth_frag_valid (◯ In)). done. }
    iSplitR "Hb". iFrame "∗ % #". iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In.
    iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures.
    iDestruct "Hb" as (Cn) "(Hrep & Hfil & Hks)". iDestruct "HNds" as %HNds.
    wp_bind (findNext _ _)%E. wp_apply ((findNext_spec n In Cn k) with "[Hrep]").
    iFrame; iPureIntro; left; done. iIntros (b n') "(Hrep & Hb)". destruct b. 
    - wp_pures. awp_apply (unlockNode_spec n). 
      iApply (aacc_aupd_abort with "AU"); first done. iIntros (C1) "Hst".
      iDestruct "Hst" as (I1) "(HI & HKS & HNDS & Hglob & Hstar)".
      iAssert (⌜n ∈ dom I1⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (dom I1)) with "[$]") as "%".
        iPureIntro. set_solver. }
      rewrite (big_sepS_delete _ (dom I1) n); last by eauto. iDestruct "Hstar" as "(Hcln & Hstar)".
      iDestruct "Hcln" as (b In1) "(Hlock & Hbb & HIn & #HNds1 & Hfis & Hks1)".
      destruct b; first last. { iDestruct "Hbb" as (Cn') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In1). 
      iFrame. } exfalso. done. }
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H3. apply leibniz_equiv in H3. replace In1.            
      iDestruct "Hb" as %Hb. iDestruct "HNds1" as %HNds1. iDestruct "Hglob" as %Hglob.
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof (own_valid with "HI") as "%". iAssert (⌜n' ∈ dom I1⌝)%I as "%".
      { iPureIntro. assert (n' ∈ dom I2). { apply (flowint_step I1 In I2 k n' root). done. 
        apply auth_auth_valid. done. done. done. }
        apply flowint_comp_fp in H4. set_solver. }
      assert (n ≠ n') as Hneq. { assert (n' ∉ dom In). { apply (outset_distinct In n').
      exists k. done. } rewrite HNds1 in H7. set_solver. }
      rewrite (big_sepS_delete _ (dom I1 ∖ {[n]}) n'); last first.
      set_solver. iDestruct "Hstar" as "(Hcln' & Hstar)". 
      iDestruct "Hcln'" as (b In') "(Hlock' & Hbb' & HIn' & #HNds' & Hfis' & Hks1')".
      iPoseProof ((own_op γ (◯ In) (◯ In' )) with "[HIn HIn']") as "H"; first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H7.
      assert (✓ (In ⋅ In')). { apply (auth_frag_valid (◯ (In ⋅ In'))). done. }
      iDestruct "HNds'" as %HNds'. assert (k ∈ linkset In' n').
      { apply (flowint_inreach_step (In⋅In') In In' k n n'); try done. }
      assert (root ∈ dom I1). { apply globalint_root_fp. done. } iDestruct "H" as "(HIn & HIn')".
      iMod (own_update (γ_inr n') (● linkset In' n') (● linkset In' n' ⋅ ◯ linkset In' n') with "Hks1'") as "HNs".
      apply auth_update_core_id. apply gset_core_id. done. iDestruct "HNs" as "(Hks1' & #Hinr1')".
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hks Hrep". iFrame "∗ # %".
      iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (dom I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists true, In. iFrame "# % ∗". 
      rewrite (big_sepS_delete _ (dom I1 ∖ {[n]}) n'); last first. set_solver. iFrame. iExists b, In'.
      iFrame "# % ∗".  iIntros "AU". iModIntro. iFrame "# % ∗". } iIntros "Hlock".
      iMod (own_update γ_fp (● dom I1) (● dom I1 ⋅ ◯ dom I1) with "HNDS") as "HNs".
      apply auth_update_core_id. apply gset_core_id. done. iDestruct "HNs" as "(HAfp & #Hfp1)".
      iModIntro. iSplitL. iExists I1. iFrame "∗ % #". rewrite (big_sepS_delete _ (dom I1) n); last by eauto.
      iSplitR "Hstar Hbb' HIn' Hfis' Hks1' Hlock'". iExists false, In. iFrame "# % ∗". iExists Cn. iFrame. 
      rewrite (big_sepS_delete _ (dom I1 ∖ {[n]}) n'); last first. set_solver. iFrame. iExists b, In'.
      iFrame "# % ∗". iIntros "AU". iModIntro. wp_pures. iSpecialize ("IH" $! n' (dom I1) In').
      iApply "IH". iFrame "∗ # %". done.
    - iApply fupd_wp. iMod "AU" as (C) "[Hst [_ Hclose]]". iSpecialize ("Hclose" $! n Ns In Cn).
      iMod ("Hclose" with "[Hst Hfil Hks Hrep Hb]") as "HΦ". iDestruct "Hb" as %Hnotout.
      iAssert (node n In Cn ∗ ⌜nodeinv In n⌝)%I with "[Hrep]" as "(Hrep & Hninv)". 
      { iApply (node_implies_nodeinv _ _ _). iFrame "∗ # %". } iDestruct "Hninv" as %Hninv. 
      iFrame "∗ # %". iPureIntro. unfold nodeinv in Hninv. specialize (Hninv k).
      apply Hninv. try done. iModIntro. wp_pures. done.
  Qed.

  Theorem searchStrOp_spec (γ γ_fp γ_k: gname) γ_inr γ_fi root (k: key) (dop: dOp):
      ⌜k ∈ KS⌝ -∗ <<< ∀ C, is_searchStr γ γ_fp γ_k γ_inr γ_fi root C >>>
            searchStrOp dop root #k
                  @ ⊤
      <<< ∃ C' (res: bool), is_searchStr γ γ_fp γ_k γ_inr γ_fi root C' 
                                        ∗ Ψ dop k C C' res, RET #res >>>.
  Proof.
    iIntros "HKin" (Φ) "AU". iLöb as "IH". wp_lam.
    iApply fupd_wp. iMod "AU" as (C0) "[Hst [HAU _]]".
    iDestruct "Hst" as (I0) "(HI & HKS & HNDS & #Hglob & Hstar)".
    iDestruct "Hglob" as %Hglob. iDestruct "HKin" as %HKin. 
    assert (root ∈ dom I0)%I as Hroot. { apply globalint_root_fp. done. }
    iMod (own_update γ_fp (● dom I0) (● dom I0 ⋅ ◯ dom I0) with "HNDS") as "H".
    { apply auth_update_core_id. apply gset_core_id. done. } 
    iDestruct "H" as "(HNDS & #Hfp0)".
    rewrite (big_sepS_elem_of_acc _ (dom I0) root); last by eauto.
    iDestruct "Hstar" as "[Hn Hstar]".
    iDestruct "Hn" as (b Ir) "(H1 & H2 & H3 & H4 & H5 & Hksr)".
    iPoseProof (auth_own_incl with "[$HI $H3]") as "%". iDestruct "H4" as %HNdsr.
    (*assert (inreach Ir root = inreach I0 root) as Hinreach. { apply globalint_inreach; try done. }*)
    iMod (own_update (γ_inr root) (● linkset Ir root) (● linkset Ir root ⋅ ◯ linkset Ir root) with "Hksr") as "H".
    apply auth_update_core_id. apply gset_core_id. done. iDestruct "H" as "(Hksr & #Hinr)".
    iMod ("HAU" with "[HI HKS H1 H2 H3 H5 Hstar HNDS Hksr] ") as "AU". 
    { iExists I0. iFrame "∗ % #". iApply "Hstar". iExists b, Ir. iFrame "∗ # %". }
    iModIntro. wp_bind (traverse _ _)%E.
    awp_apply (traverse_spec γ γ_fp γ_k γ_inr γ_fi root k root (dom I0) Ir). iFrame "∗ # %".
    iPureIntro. apply (globalint_root_inr I0 Ir root k); try done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (C1) "Hst". iAaccIntro with "Hst"; first by eauto with iFrame.
    iIntros (n Ns In Cn) "(Hst & #Hinn & #Hfp & Hrepn & Hfil & Hks & #HNdsn & #Hinset & #Hnotout)".
    iDestruct "Hinn" as %Hinn. iDestruct "Hinset" as %Hinset. iDestruct "Hnotout" as %Hnotout.
    iModIntro. iFrame. iIntros "AU". iModIntro. wp_pures. wp_bind (decisiveOp _ _ _)%E.
    wp_apply ((decisiveOp_spec dop n k In Cn) with "[Hrepn]"). eauto with iFrame.
    iIntros (b' Cn' res). iIntros "Hb". destruct b'.
    - iDestruct "Hb" as "(Hrep & #HΨ & #Hsub)".
      wp_pures. wp_bind(unlockNode _)%E.
      awp_apply (unlockNode_spec n).
      iApply (aacc_aupd_commit with "AU"); first done. iIntros (C2) "Hst".
      iDestruct "Hst" as (I) "(HI & HKS & HNDS & #Hglob & Hstar)". 
      iDestruct "Hglob" as %Hglob'.
      iAssert (⌜n ∈ dom I⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (dom I)) with "[$]") as "%".
      iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (dom I) n); last by eauto.
      iDestruct "Hstar" as "[Hn Hstar]".
      iDestruct "Hn" as (b' In1) "(Hlock & Hb & HIn & #HNds & Hfis & Hinreach)".
      destruct b'; first last. { iDestruct "Hb" as (Cn'') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hrep Hrep']" as %Hf. { iApply (node_sep_star n In In1). 
      iFrame. } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hrep Hks".
      iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In1. 
      iFrame "∗ # %". eauto with iFrame. } iIntros "Hlock".
      iPoseProof (auth_own_incl with "[$HI $HIn]") as (I2)"%".
      iPoseProof ((own_valid γ (● I)) with "HI") as "%".
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H3. apply leibniz_equiv in H3. replace In1.
      iPoseProof ((own_valid γ (◯ In)) with "HIn") as "%". rename H4 into HInV.
      assert (✓ In) as HInv. { apply (auth_frag_valid (◯ In)). done. }
      iAssert (node n In Cn' ∗ ⌜nodeinv In n⌝)%I with "[Hrep]" as "(Hrep & Hninv)". 
      { iApply (node_implies_nodeinv _ _ _). iFrame "% ∗ #". } iDestruct "Hninv" as %Hninv.                   
      iMod ((ghost_update_keyset γ_k dop k Cn Cn' res (keyset In n) C2) with "[HKS Hks]") as "Hgks".
      iFrame "% ∗ #". iPureIntro. apply keyset_def; try done.
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
      iAssert (⌜n ∈ dom I⌝)%I with "[HNDS]" as "%".
      { iPoseProof ((auth_set_incl γ_fp Ns (dom I)) with "[$]") as "%".
      iPureIntro. set_solver. }
      rewrite (big_sepS_elem_of_acc _ (dom I) n); last by eauto.
      iDestruct "Hstar" as "[Hn Hstar]".
      iDestruct "Hn" as (b' In1) "(Hlock & Hb' & HIn & #HNds & Hfis & Hinreach)".
      destruct b'; first last. { iDestruct "Hb'" as (Cn'') "(Hrep' & _)".
      iAssert (⌜False⌝)%I with "[Hb Hrep']" as %Hf. { iApply (node_sep_star n In In1). 
      iFrame "∗ # %". } exfalso. done. }
      iAaccIntro with "Hlock". { iIntros "Hlock". iModIntro. iSplitR "Hfil Hb Hks".
      iExists I. iFrame "∗ % #". iApply "Hstar". iExists true, In1. 
      iFrame "∗ # %". eauto with iFrame. } iIntros "Hlock". iModIntro.
      iPoseProof ((own_valid_2 (γ_fi n) (●{1 / 2} In) (●{1 / 2} In1)) with "[Hfil] [Hfis]") as "%"; try done.
      apply (auth_auth_frac_op_inv _ _ _ _) in H1. apply leibniz_equiv in H1. replace In1.            
      iSplitR "". iExists I. iFrame "∗ % #". iApply "Hstar". iExists false, In. iFrame "∗ % #".
      iExists Cn. iFrame. iIntros "AU". iModIntro. wp_pures. iApply "IH"; try done.
  Qed.
 
End Link_Template.