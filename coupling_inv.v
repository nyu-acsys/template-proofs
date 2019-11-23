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

  Definition Ψ dop k (C: gsetO key) (C': gsetO key) (res: bool) : iProp :=
    match dop with
    | memberOp => (⌜C' = C ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    | insertOp => (⌜C' = union C {[k]} ∧ (if res then k ∉ C else k ∈ C)⌝)%I
    | deleteOp => (⌜C' = difference C {[k]} ∧ (if res then k ∈ C else k ∉ C)⌝)%I
    end.

  Instance Ψ_persistent dop k C C' res : Persistent (Ψ dop k C C' res).
  Proof. destruct dop; apply _. Qed.

  (** Helper functions specs *)

  (* Sid: we can also try to get rid of getLockLoc and just do CAS (lockLoc "l") #true #false in lock, etc. *)
  Parameter getLockLoc_spec : ∀ (n: Node),
      ({{{ True }}}
           getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.

  (* the following functions are proved for each implementation in GRASShopper (see b+-tree.spl and hashtbl-give-up.spl) *)

  Parameter findNext_spec : ∀ first (n: Node) (I_n : flowintUR) (C: gset key) (k: key),
      ({{{ node first n I_n C ∗ ⌜in_inset k I_n n⌝ }}}
           findNext #n #k
       {{{ (b: bool) (n': Node), 
              RET (match b with true => (SOMEV #n') | false => NONEV end); 
               node first n I_n C ∗ (match b with true => ⌜in_outset k I_n n'⌝ |
                                          false => ⌜¬in_outsets k I_n⌝ end) }}})%I.

  Parameter decisiveOp_insert_spec :
    ∀ first (p n m: Node) (k: key) (I_p I_n: flowintUR) (C_p C_n: gset key),
      ({{{ node p first I_p C_p ∗ node n first I_n C_n ∗ hrep_spatial m ∗ ⌜n ≠ first⌝
           ∗ ⌜m ≠ first⌝ ∗ ⌜in_inset k I_p p⌝ ∗ ⌜in_outset k I_p n ⌝
           ∗ ⌜¬in_outsets k I_n⌝ }}}
         decisiveOp insertOp #p #n #k
       {{{ (C_p' C_n' C_m': gset key) (I_p' I_n' I_m': flowintUR) (res: bool),
           RET  #res;
           node p first I_p' C_p' ∗ node n first I_n' C_n' ∗ node m first I_m' C_m'
           ∗ ⌜Ψ insertOp k (C_p ∪ C_n) (C_p' ∪ C_n' ∪ C_m') res⌝ 
           ∗ ⌜contextualLeq (I_p ⋅ I_n) (I_p' ⋅ I_n' ⋅ I_m')⌝
           ∗ ⌜dom I_p' = {[p]}⌝ ∗ ⌜dom I_n' = {[n]}⌝ ∗ ⌜dom I_m' = {[m]}⌝
           ∗ ⌜C_p' ⊆ keyset I_p' p⌝ ∗ ⌜C_n' ⊆ keyset I_n' n⌝ ∗ ⌜C_m' ⊆ keyset I_m' m⌝
           ∗ ⌜keyset I_p' p ## keyset I_n' n⌝ ∗ ⌜keyset I_p' p ## keyset I_m' m⌝
           ∗ ⌜keyset I_m' m ## keyset I_n' n⌝ 
           ∗ ⌜keyset I_p' p ∪ keyset I_n' n ∪ keyset I_m' m
              = keyset I_p p ∪ keyset I_n n⌝ }}})%I.

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
                                      own γ (◯ I_n) ∗ node root n I_n C_n 
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

  (* ---------- Lock module proofs ---------- *)

  Lemma lockNode_spec γ γ_fp γ_k γ_c first Ns (n: Node):
    css γ γ_fp γ_k γ_c first ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝ -∗
    <<< True >>>
        lockNode #n    @ ⊤
    <<< ∃ (I_n: flowintUR) (C_n: gset key),
        own γ (◯ I_n) ∗ node first n I_n C_n ∗ own γ_k (◯ prod (keyset I_n n, C_n)),
        RET #()
    >>>.
  Proof.
  Admitted.

  Lemma unlockNode_spec γ γ_fp γ_k γ_c first Ns (n: Node) I_n C_n:
    css γ γ_fp γ_k γ_c first ∗ own γ_fp (◯ Ns) ∗ ⌜n ∈ Ns⌝
    ∗ own γ (◯ I_n) ∗ node first n I_n C_n ∗ own γ_k (◯ prod (keyset I_n n, C_n)) -∗
    <<< True >>>
      unlockNode #n    @ ⊤
    <<< True, RET #() >>>.
  Proof.
  Admitted.

  (* ---------- Proof of the lock coupling template  ---------- *)

  Hypothesis outset_impl_inset: ∀ I1 I2 k n n',
    ✓ (I1⋅I2) → n' ∈ (dom I2) → in_inset k I1 n → in_outset k I1 n' → in_inset k I2 n'.

  Hypothesis flowint_step :
    ∀ I I1 I2 k n first, I = I1 ⋅ I2 → in_outset k I1 n → globalint first I → n ∈ dom I2.

  Hypothesis successor_not_first : ∀ I I1 I2 I3 first n k C,
    I = I1⋅I2⋅I3 → globalint first I → in_outset k I1 n → nodeinv first n I2 C → n ≠ first. 

  Lemma traverse_spec (γ γ_fp γ_k γ_c: gname) first (k: key) (p n: Node) (Ns: gset Node) I_p C_p I_n C_n:
    css γ γ_fp γ_k γ_c first
    ∗ own γ_fp (◯ Ns) ∗ ⌜p ∈ Ns⌝ ∗ ⌜n ∈ Ns⌝ ∗ ⌜first ∈ Ns⌝ ∗ ⌜n ≠ first⌝
    ∗ node first p I_p C_p ∗ own γ (◯ I_p) ∗ ⌜in_inset k I_p p⌝ ∗ ⌜in_outset k I_p n⌝
    ∗ own γ_k (◯ prod (keyset I_p p, C_p))
    ∗ node first n I_n C_n ∗ own γ (◯ I_n) ∗ ⌜dom I_n = {[n]}⌝
    ∗ own γ_k (◯ prod (keyset I_n n, C_n)) -∗
    <<< True >>>
      traverse #p #n #k @ ⊤
    <<< ∃ (p' n': Node) (Ns': gsetUR Node) (I_p' I_n': flowintUR) (C_p' C_n': gset key), 
        own γ_fp (◯ Ns') ∗ ⌜p' ∈ Ns'⌝ ∗ ⌜n' ∈ Ns'⌝ ∗ own γ (◯ I_p') ∗ own γ (◯ I_n') 
        ∗ node first p' I_p' C_p' ∗ node first n' I_n' C_n' ∗ ⌜n' ≠ first⌝
        ∗ own γ_k (◯ prod (keyset I_p' p', C_p'))
        ∗ own γ_k (◯ prod (keyset I_n' n', C_n')) 
        ∗ ⌜dom I_p' = {[p']}⌝ ∗ ⌜dom I_n' = {[n']}⌝
        ∗ ⌜in_inset k I_p' p'⌝ ∗ ⌜in_outset k I_p' n'⌝ ∗ ⌜¬in_outsets k I_n'⌝,
        RET (#p', #n')
    >>>.
  Proof.
    iLöb as "IH" forall (p n Ns I_p C_p I_n C_n).                                        
    iIntros "(#Hinv & #Hfp & % & % & % & % & Hp & HIp & % & % & HCp & Hn & HIn & % & HCn)".
    iIntros (Φ) "AU".
    wp_lam. wp_let. wp_let. wp_bind(findNext _ _)%E.
    (* Prove in_inset k In n *)
    iAssert (⌜in_inset k I_n n⌝)%I with "[HIp HIn]" as "%".
    {
      iPoseProof ((own_op γ (◯ I_p) (◯ I_n)) with "[HIp HIn]") as "H";
        first by eauto with iFrame.
      iPoseProof (own_valid with "H") as "%". rewrite -auth_frag_op in H6.
      iPureIntro.
      apply (outset_impl_inset I_p I_n k p n); try done. set_solver.
    }
    wp_apply ((findNext_spec first n I_n C_n k) with "[$Hn]"). iPureIntro. done.
    iIntros (b n') "(Hn & Hb)". destruct b.
    - (* findNext returns Some n' *)
      wp_pures. wp_bind(lockNode _)%E.
      iAssert (⌜n' ∈ Ns⌝)%I as "%".
      { 
        iPureIntro. assert (n' ∈ Ns).
        { apply (flowint_step I1 In I2 k n' root); try done.
          apply auth_auth_valid. done. }
        unfold globalinv in H0.
        apply flowint_comp_fp in H3. set_solver.
      }
      awp_apply ((lockNode_spec γ γ_fp γ_k γ_c first Ns n') with "[$Hinv $Hfp //]").
      iAaccIntro with "[]".
      { iPureIntro. done. }
      iIntros. iModIntro. iFrame "∗ % #".
      iIntros (I_n' C_n') "(HIn' & Hn' & HCn')".
      iModIntro. wp_seq. wp_bind(unlockNode _)%E.
      awp_apply ((unlockNode_spec γ γ_fp γ_k γ_c first Ns p)
                   with "[$Hinv $Hfp $Hp $HIp $HCp //]").
      iAaccIntro with "[]".
      { iPureIntro. done. }
      iIntros. iModIntro. iFrame "∗ % #".
      iIntros. iModIntro. wp_pures.
      iAssert (⌜n' ≠ first⌝)%I as "%".
      {
        admit.                  (* use successor_not_first *)
      }
      iAssert (⌜dom I_n' = {[n']}⌝)%I as "%".
      {
        admit.                  (* get rid of this *)
      }
      iSpecialize ("IH" $! n n' Ns I_n C_n I_n' C_n').
      iApply ("IH" with "[-AU]"). iFrame "∗ # %".
      done.
    - (* findNext returns None *)
      iApply fupd_wp. iMod "AU" as "[_ [_ HCl]]".
      iSpecialize ("HCl" $! p n Ns I_p I_n C_p C_n).
      iMod ("HCl" with "[-]"). iFrame "∗ # %".
      iModIntro. wp_pures. done.
  Admitted.

  Theorem searchStrOp_spec (γ γ_fp γ_k γ_c: gname) first (k: key) (dop: dOp):
    ⌜k ∈ KS⌝ ∗ css γ γ_fp γ_k γ_c first -∗
    <<< ∀ (C: gset key), css_cont γ_c C >>>
      searchStrOp dop first #k @ ⊤
    <<< ∃ C' (res: bool), css_cont γ_c C' ∗ ⌜Ψ dop k C C' res⌝, RET #res >>>.
  Proof.
    iIntros "(% & #HInv)". iIntros (Φ) "AU". wp_lam. wp_bind (lockNode _)%E.
    iApply fupd_wp. iInv "HInv" as ">H". iDestruct "H" as (I C) "H".
    iAssert (own γ_fp (◯ dom I))%I as "#Hfp". { admit. }
    assert (first ∈ dom I). { admit. }
    iModIntro. iSplitL "H". iNext. iExists I, C. iFrame "∗ # %".
    iModIntro. awp_apply (lockNode_spec γ γ_fp γ_k γ_c first (dom I) first).
    iFrame "∗ # %". iAssert (⌜True⌝)%I as "Ht". { done. }
    iAaccIntro with "Ht"; eauto with iFrame.
    iIntros (If Cf) "(HIf & Hrepf & Hksf)".
    iModIntro. wp_pures. wp_bind (findNext _ _)%E.
    wp_apply ((findNext_spec first first If Cf k) with "[Hrepf]").
    { iFrame. iPureIntro. admit. }
    iIntros (b n) "(Hrepf & Hb)". destruct b; last first. exfalso. admit.
    wp_let. wp_pures. wp_bind (lockNode _)%E.
    iApply fupd_wp. iInv "HInv" as ">H". iDestruct "H" as (I1 C1) "H".
    iAssert (own γ_fp (◯ dom I1))%I as "#Hfp1". { admit. }
    iModIntro. iSplitL "H". iNext. iExists I1, C1. iFrame "∗ # %".
    iModIntro. awp_apply (lockNode_spec γ γ_fp γ_k γ_c first (dom I) n).
    { iFrame "HInv Hfp". iPureIntro. admit. }
    iAaccIntro with "[]". iPureIntro. done. iIntros. iModIntro.
    eauto with iFrame. iIntros (In Cn) "(HIn & Hrepn & Hksn)".
    iModIntro. wp_pures. wp_bind (traverse _ _ _)%E.
    awp_apply ((traverse_spec γ γ_fp γ_k γ_c first k first n (dom I1) If Cf In Cn) with "[-AU]").
    iFrame "∗ # %". admit. iAaccIntro with "[]". iPureIntro. done.
    iIntros. iModIntro. eauto with iFrame. 
    iIntros (p' n' Ns' Ip' In' Cp' Cn') "(#Hfp' & % & % & HIp' & HIn' 
                & Hrepp' & Hrepn' & % & Hksp' & Hksn' & % & % & % & % & %)".
    iModIntro. wp_pures. wp_bind (alloc _)%E. wp_apply (alloc_spec); try done.
    iIntros (m l) "(hreps & % & Hlm)". wp_pures. wp_bind (decisiveOp _ _ _ _)%E.
    destruct dop. 
    - admit.
    - wp_apply (decisiveOp_insert_spec first k p' n' m Ip' In' Cp' Cn')%E.     
  Admitted.
