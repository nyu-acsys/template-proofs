From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export lock multicopy multicopy_util.

Parameter inContents : val.
Parameter findNext : val.
Parameter addContents: val.
Parameter atCapacity: val.
Parameter chooseNext: val.
Parameter mergeContents: val.
Parameter allocNode: val.
Parameter insertNode: val.

(** Template algorithms *)

Definition search (r d: Node) : val := 
  λ: "k",
    lockNode #r;;
    match: (inContents #r "k") with
      SOME "t" => unlockNode #r;; "t"
    | NONE => unlockNode #r;;
              lockNode #d;;
              match: (inContents #d "k") with
                SOME "t" => unlockNode #d;; "t"
              | NONE => unlockNode #d;; #0 end end.
  
Definition readClock : val :=
  λ: "l", !"l".
  
Definition incrementClock : val :=
  λ: "l", let: "t" := !"l" in
          "l" <- "t" + #1.

Definition upsert (lc: loc) (r: Node) : val :=
  rec: "upsert_rec" "k" := 
    lockNode #r ;;
    let: "t" := readClock #lc in
    let: "res" := addContents #r "k" "t" in
    if: "res" then 
      incrementClock #lc;;
      unlockNode #r
    else
      unlockNode #r;;
      "upsert_rec" "k".

(** Proof setup *)

Definition frac_contR := frac_agreeR (gmapUR K natUR).
Definition timeR := authR (max_natUR).

Class multicopy_dfG Σ := MULTICOPY_DF {
                            multicopy_df_frac_contG :> inG Σ frac_contR;
                            multicopy_df_timeG :> inG Σ timeR;
                      }.

Definition multicopy_dfΣ : gFunctors :=
  #[GFunctor frac_contR; GFunctor timeR ].

Instance subG_multicopy_dfΣ {Σ} : subG multicopy_dfΣ Σ → multicopy_dfG Σ.
Proof. solve_inG. Qed.

Section multicopy_df.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_dfG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  (** Assumptions on the implementation made by the template algorithms. *)

  (* The node predicate is specific to each template implementation. 
     See GRASShopper files multicopy-lsm.spl for the concrete definition. *)
  Parameter node : Node → Node → (gmap K natUR) → iProp.

  Parameter nodeSpatial : Node → iProp.
  
(*   Parameter needsNewNode : Node → Node → esT → (gmap K nat) → iProp.  *)

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ r n C, Timeless (node r n C).
  Global Instance node_timeless r n C: Timeless (node r n C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis are proved as a GRASShopper lemma in
   * multicopy-lsm.spl *)
  Parameter node_sep_star: ∀ r n C C',
    node r n C ∗ node r n C' -∗ False.

  (** The LSM multicopy structure invariant *)

  Definition clock lc (t: nat) : iProp := lc ↦ #t.

  Definition nodePred γ_s γ_t γ_cn lc r n (Cn: gmap K nat) t : iProp :=
      node r n Cn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ own (γ_cn) (to_frac_agree (1/2) (Cn))
    ∗ (if (decide (n = r)) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t 
       else True)%I.

  Definition cir (H: gset KT) (Cr Cd: gmap K nat) :=
                   ∀ k t, ((Cr !! k = Some t → map_of_set H !! k = Some t)
                 ∧ (Cr !! k = None → map_of_set H !! k = Cd !! k)). 

      
  Definition Inv_DF γ_s γ_t γ_cr γ_cd (γ_d: gmap K gname) lc r d t H : iProp :=
    ∃ (Cr Cd: gmap K nat),
      own γ_t (●{1/2} MaxNat t)
    ∗ (∃ br, lockR br r (nodePred γ_s γ_t γ_cr lc r r Cr t))
    ∗ (∃ bd, lockR bd d (nodePred γ_s γ_t γ_cd lc r d Cd t))
    ∗ ⌜cir H Cr Cd⌝
    ∗ ([∗ set] k ∈ KS, own (γ_d !!! k) (● (MaxNat (Cd !!! k)))).

  Global Instance Inv_DF_timeless γ_s γ_t γ_cr γ_cd γ_d lc r d t H:
    Timeless (Inv_DF γ_s γ_t γ_cr γ_cd γ_d lc r d t H).
  Proof.
    rewrite /Inv_DF.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    repeat (intros; apply bi.exist_timeless; intros).
    apply bi.sep_timeless; try apply _.
    destruct x1; try apply _.    
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (r = r)); try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct x1; try apply _.
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (d = r)); try apply _.
  Qed.
  
  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper
   * (see multicopy-lsm.spl *)
    
  Parameter inContents_spec : ∀ r n Cn (k: K),
     ⊢ ({{{ node r n Cn }}}
           inContents #n #k
       {{{ (t: option nat), 
              RET (match t with Some t => SOMEV #t | None => NONEV end);
                  node r n Cn ∗ ⌜Cn !! k = t⌝ }}})%I.

  Lemma readClock_spec: ∀ γ_t lc q t, 
     ⊢ ({{{ own γ_t (●{q} MaxNat t) ∗ clock lc t }}}
           readClock #lc
       {{{ RET #t; own γ_t (●{q} MaxNat t) ∗ clock lc t }}})%I.
  Proof.
    intros γ_t lc q t.
    iIntros (Φ) "!# (Hqt & Hclock) HCont".
    wp_lam. wp_load. iApply "HCont". 
    iFrame; try done.
  Qed.  

  Parameter addContents_spec : ∀ r n Cn (k: K) (t:nat),
     ⊢ ({{{ node r n Cn ∗ ⌜n = r⌝ }}}
           addContents #r #k #t
       {{{ (succ: bool) (Cn': gmap K natUR),
              RET #succ;
                  node r n Cn' ∗ if succ then ⌜Cn' = <[k := t]> Cn⌝ 
                                else ⌜Cn' = Cn⌝ }}})%I.

End multicopy_df.           
