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

  (** The concurrent search structure invariant *)

  Definition ccs (γ γ_fp γ_k γ_c : gname) root (C: gset key) : iProp :=
    (∃ I,
        own γ_k (● prod (KS, C)) ∗ own γ (● I) ∗ ⌜globalint root I⌝
        ∗ own γ_fp (● dom I) ∗ own γ_c (● (Some ((Excl C))))
        ∗ ([∗ set] n ∈ (dom I), (∃ b: bool,
          (lockLoc n) ↦ #b ∗ if b then True
                             else (∃ (I_n: flowintUR) (C_n: gset key),
                                      own γ (◯ I_n) ∗ node root n I_n C_n 
                                      ∗ own γ_k (◯ prod (keyset I_n n, C_n)))))
    )%I.

  Definition ccs_cont (γ_c: gname) (C: gset key) : iProp :=
    (own γ_c (◯ (Some ((Excl C)))))%I.

  Instance main_inv_timeless γ γ_fp γ_c I N C :
    Timeless (main_inv γ γ_fp γ_c I N C).
  Proof.
    rewrite /main_inv. repeat apply bi.sep_timeless; try apply _.
    try apply big_sepS_timeless. intros. apply bi.exist_timeless. intros.
    apply bi.sep_timeless; try apply _.
    destruct x0; try apply _.
  Qed.
