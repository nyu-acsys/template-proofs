From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export KT_flows inset_flows_multicopy auth_ext.

(** Algorithms **)

Variable inContents : val.
Variable findNext : val.
Variable lockLoc : Node → loc.
Variable getLockLoc: val.
Variable addContents: val.
Variable mergeContents: val.
Variable chooseNext: val.
Variable atCapacity: val.

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
  rec: "t_rec" "n" "k" :=
    lockNode "n" ;;
    let: "t" := inContents "n" "k" in
    match: "t" with
      SOME "t" => unlockNode "n";;
                  "t"
    | NONE => match: (findNext "n" "k") with
                SOME "n'" => unlockNode "n" ;; "t_rec" "n'" "k"
              | NONE => unlockNode "n" ;; #0 end end.
(*              
    if: ("t" ≠ #0) 
    then
      unlockNode "n";; "t"
    else
      match: (findNext "n" "k") with
        SOME "n'" => unlockNode "n" ;; "t_rec" "n'" "k"
      | NONE => unlockNode "n" ;; #0 end.
*)
              
Definition search (r: Node) : val := 
  λ: "k", traverse #r "k".
  
Definition readClock : val :=
  λ: "l", !"l".
  
Definition incrementClock : val :=
  λ: "l", let: "n" := !"l" in
          "l" <- "n" + #1.

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

Definition compact : val :=
  rec: "compact_rec" "n" :=
    lockNode "n" ;;
    if: atCapacity "n" then
      let: "m" := chooseNext "n" in
      lockNode "m" ;;
      mergeContents "n" "m" ;;
      unlockNode "n" ;;
      unlockNode "m" ;;
      "compact_rec" "m"
    else
      unlockNode "n".          


(** Proof setup **)

Definition K := Z.
Definition KT := @KT K.
Parameter KS : gset K.

Definition esT : Type := gmap Node (gset K).
Canonical Structure esRAC := leibnizO esT.

Definition prod5O A B C D E :=
  prodO (prodO (prodO (prodO A B) C) D) E.

Definition per_node_gl :=
    agreeR 
      (prod5O gnameO gnameO gnameO gnameO (gmapO K gnameO)).

Definition ghost_heapUR := gmapUR Node $ per_node_gl.  

Definition contR := frac_agreeR (gmapUR K natUR).
Definition flow_KTR := authR (KT_flowint_ur K).
Definition flow_KR := authR (inset_flowint_ur K).
Definition setR := authR (gsetUR Node).
Definition esR := frac_agreeR (esRAC).
Definition timeR := authR (max_natUR).
Definition histR := authR (gsetUR (KT)).
Definition hist_exclR := authR $ optionUR $ exclR (gsetO KT).
Definition time_exclR := authR $ optionUR $ exclR natUR.
Definition ghR := authR $ ghost_heapUR.

Class multicopyG Σ := MULTICOPY {
                        multicopy_contG :> inG Σ contR;
                        multicopy_flow_KTG :> inG Σ flow_KTR;
                        multicopy_flow_KG :> inG Σ flow_KR;
                        multicopy_setG :> inG Σ setR;
                        multicopy_esG :> inG Σ esR;
                        multicopy_timeG :> inG Σ timeR;
                        multicopy_histG :> inG Σ histR;
                        multicopy_hist_exclG :> inG Σ hist_exclR;
                        multicopy_time_exclG :> inG Σ time_exclR;
                        multicopy_ghG :> inG Σ ghR;
                       }.

Definition multicopyΣ : gFunctors :=
  #[GFunctor contR; GFunctor flow_KTR; GFunctor flow_KR; GFunctor setR; 
    GFunctor esR; GFunctor timeR; GFunctor histR; GFunctor hist_exclR; 
    GFunctor time_exclR; GFunctor ghR ].

Instance subG_multicopyΣ {Σ} : subG multicopyΣ Σ → multicopyG Σ.
Proof. solve_inG. Qed.

Section multicopy.
  Context {Σ} `{!heapG Σ, !multicopyG Σ}.
  Context (N : namespace).
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  (** Definitions **)

  Parameter node : Node → Node → esT → (gmap K natUR) → iProp.

  Parameter node_timeless_proof : ∀ r n es C, Timeless (node r n es C).
  Instance node_timeless r n es C: Timeless (node r n es C).
  Proof. apply node_timeless_proof. Qed.

  Hypothesis node_sep_star: ∀ r n es C es' C',
    node r n es C ∗ node r n es' C' -∗ False.

  Hypothesis node_edgeset_disjoint: ∀ r n es C,
    node r n es C -∗ ⌜∀ n1 n2, n1 ≠ n2 → es !!! n1 ∩ es !!! n2 = ∅⌝.  

  Hypothesis node_edgeset_self_empty: ∀ r n es C,
    node r n es C -∗ ⌜es !!! n = ∅⌝.

  Definition inFP γ_f (n: Node) : iProp := own γ_f (◯ {[n]}).

  Definition closed γ_f (es: esT) : iProp := ∀ n, ⌜es !!! n  ≠ ∅⌝ → inFP γ_f n.

  Definition inflow_zero (I: KT_flowint_ur K) := ∀ n, inset_KT I n = ∅. 

  Definition outflow_zero (I: KT_flowint_ur K) := out_map I = ∅. 

  Definition outflow_zero_R (I: inset_flowint_ur K) := out_map I = ∅. 

  Definition inflow_R (R: inset_flowint_ur K) r := 
    ∀ n k, if n =? r then in_inset K k R n else ¬ in_inset K k R n. 

  Definition outflow_le_1 (I: KT_flowint_ur K) :=
    ∀ n kt, out I n !1 kt ≤ 1.

  Definition outflow_constraint_I (In: KT_flowint_ur K) (es: esT) 
                          (Qn: gmap K natUR) := 
    ∀ n' k t, (k,t) ∈ outset_KT In n' ↔ 
                          k ∈ es !!! n' ∧ (Qn !! k = Some t).
                          
  Definition outflow_constraint_R (Rn: inset_flowint_ur K) (es: esT) n := 
    ∀ n' k, k ∈ outset K Rn n' ↔ k ∈ es !!! n' ∧ k ∈ inset K Rn n.

  Definition map_of_set (C: gset KT) : gmap K nat := 
              let f := λ (kt: KT) (M: gmap K nat), if (M !!! kt.1 <=? kt.2) 
                                 then (<[kt.1 := kt.2]> M : gmap K nat) else M in
              set_fold f (∅: gmap K nat) C.

  Definition set_of_map (C: gmap K nat) : gset KT := 
             let f := λ k t H, H ∪ {[(k,t)]} in
             map_fold f (∅: gset KT) C.

  (** ϕ_1 in the paper *)
  Definition φ0 (es: esT) (Qn: gmap K natUR) :=
              ∀ k, (∀ n', k ∉ es !!! n') → Qn !! k = None.

  (** This constraint is implicit in the paper. We track B_n explicitly as ghost state here. 
      That is the following captures the definition of B_n in terms of C_n/Q_n given in the paper. *)
  Definition φ1 (Bn Cn Qn: gmap K natUR) := 
              ∀ k t, (Cn !! k = Some t → Bn !! k = Some t)
                 ∧ (Cn !! k = None → Bn !! k = Qn !! k). 

  (** ϕ_2 in the paper *)
  Definition φ2 n (Bn: gmap K natUR) In := 
              ∀ k t, (k,t) ∈ inset_KT In n → Bn !!! k = t.

  (** ϕ_4 in the paper *)
  Definition φ3 n (Bn: gmap K natUR) Rn :=
              ∀ k, Bn !! k = None ∨ k ∈ inset K Rn n.

  (** ϕ_5 in the paper *)
  Definition φ4 n (Rn: inset_flowint_ur K) := 
              ∀ k, inf Rn n !1 k ≤ 1.

  (** ϕ_3 in the paper *)
  Definition φ5 (Bn Qn: gmap K natUR) :=
              ∀ k, Qn !!! k ≤ Bn !!! k.            

  Definition φ6 (Bn: gmap K natUR) (t: nat) := 
              ∀ k, Bn !!! k ≤ t.
  
  Definition φ7 n (es: esT) (Rn: inset_flowint_ur K) (Qn: gmap K natUR) :=
              ∀ k, (∃ n', k ∈ es !!! n') ∧ k ∈ inset K Rn n 
                          → k ∈ dom (gset K) Qn.              

  Definition maxTS (t: nat) (H: gset KT) := 
              (∀ (k: K) t', (k, t') ∈ H → t' < t) ∧ (t > 0).
  
  Definition f_merge (Cn: gmap K nat) (Es: gset K) (Cm: gmap K nat) := 
                    λ k o1 o2, 
                      if (decide (Cn !! k ≠ None)) then o1
                      else if (decide (k ∈ Es)) then o2 
                           else (None: option nat).
  
  Instance f_merge_diag_none Cn Es Cm k : DiagNone (f_merge Cn Es Cm k).
  Proof.
    unfold DiagNone. unfold f_merge.
    destruct (decide (Cn !! k ≠ None)); try by simpl.
    destruct (decide (k ∈ Es)); try by simpl.
  Qed.  
  
  Definition merge (Cn: gmap K nat) (Es: gset K) (Cm: gmap K nat) 
                          : (gmap K nat) :=
             gmap_imerge (f_merge Cn Es Cm) Cn Cm.            

  Definition MCS_auth (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (● Excl' t) ∗ own γ_he (● Excl' H).

  Definition MCS (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (◯ Excl' t) ∗ own γ_he (◯ Excl' H).

  Definition frac_ghost_state γ_en γ_cn γ_bn γ_qn es 
                                  (Cn Bn Qn: gmap K natUR): iProp :=
      own (γ_en) (to_frac_agree (1/2) (es))
    ∗ own (γ_cn) (to_frac_agree (1/2) (Cn))
    ∗ own (γ_bn) (to_frac_agree (1/2) (Bn))
    ∗ own (γ_qn) (to_frac_agree (1/2) (Qn)).

  Definition singleton_interfaces_ghost_state γ_I γ_R n 
                  (In: KT_flowint_ur K) (Rn: inset_flowint_ur K) : iProp :=
      own γ_I (◯ In)
    ∗ own γ_R (◯ Rn)
    ∗ ⌜domm In = {[n]}⌝
    ∗ ⌜domm Rn = {[n]}⌝.
    
  Definition outflow_constraints n In Rn es Qn : iProp :=
      ⌜outflow_constraint_I In es Qn⌝
    ∗ ⌜outflow_constraint_R Rn es n⌝
    ∗ ⌜outflow_le_1 In⌝.

  Definition clock lc (t: nat) : iProp := lc ↦ #t.
  
  Definition history_init (H: gset KT) := ∀ k, k ∈ KS → (k, 0) ∈ H.

  Definition ghost_loc γ_en γ_cn γ_bn γ_qn (γ_cirn: gmap K gnameO) : per_node_gl := 
        to_agree (γ_en, γ_cn, γ_bn, γ_qn, γ_cirn).

  (** Predicate N_L *)
  Definition nodePred γ_gh γ_t γ_s lc r n (Cn Bn Qn : gmap K natUR) : iProp :=
    ∃ γ_en γ_cn γ_bn γ_qn γ_cirn es t,
      node r n es Cn
    ∗ own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})  
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ (if (n =? r) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t else ⌜True⌝)%I.

  (** Predicate N_S *)
  Definition nodeShared (γ_I γ_R γ_f: gname) γ_gh r n 
          (Cn Bn Qn : gmap K natUR) H t: iProp :=
    ∃ γ_en γ_cn γ_bn γ_qn γ_cirn es In Rn,
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn  
    ∗ singleton_interfaces_ghost_state γ_I γ_R n In Rn 
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ outflow_constraints n In Rn es Qn
    ∗ (if (n =? r) then ⌜Bn = map_of_set H⌝ ∗ ⌜inflow_zero In⌝ else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cirn !!! (k)) (● (MaxNat (Bn !!! k))))
    ∗ ⌜φ0 es Qn⌝ ∗ ⌜φ1 Bn Cn Qn⌝ ∗ ⌜φ2 n Bn In⌝ ∗ ⌜φ3 n Bn Rn⌝ 
    ∗ ⌜φ4 n Rn⌝ ∗ ⌜φ5 Bn Qn⌝ ∗ ⌜φ6 Bn t⌝ ∗ ⌜φ7 n es Rn Qn⌝. 

  (** Predicate G *)
  Definition global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r t H 
          (hγ: gmap Node per_node_gl) (I: KT_flowint_ur K) 
          (R: inset_flowint_ur K) : iProp :=
      MCS_auth γ_te γ_he t H
    ∗ own γ_s (● H) ∗ ⌜history_init H⌝
    ∗ own γ_t (●{1/2} MaxNat t)
    ∗ own γ_I (● I) ∗ ⌜outflow_zero I⌝
    ∗ own γ_R (● R) ∗ ⌜outflow_zero_R R⌝ ∗ ⌜inflow_R R r⌝
    ∗ own γ_f (● domm I)
    ∗ own γ_gh (● hγ)
    ∗ inFP γ_f r
    ∗ ⌜maxTS t H⌝
    ∗ ⌜domm I = domm R⌝ ∗ ⌜domm I = dom (gset Node) hγ⌝.

  (** Invariant Inv *)
  Definition mcs γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r : iProp :=
    ∃ t (H: gset KT) hγ
      (I: KT_flowint_ur K) (R: inset_flowint_ur K),
      global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r t H hγ I R
    ∗ ([∗ set] n ∈ (domm I), ∃ (bn: bool) Cn Bn Qn, 
          lockLoc n ↦ #bn  
        ∗ (if bn then True else nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn)
        ∗ nodeShared γ_I γ_R γ_f γ_gh r n Cn Bn Qn H t)%I.  

  Instance mcs_timeless γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r :
    Timeless (mcs γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r).
  Proof.
    rewrite /mcs.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    apply big_sepS_timeless.
    repeat (intros; apply bi.exist_timeless; intros).
    apply bi.sep_timeless; try apply _.
    repeat apply bi.sep_timeless; try apply _.
    destruct x5; try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (x4 =? r); try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (x4 =? r); try apply _.
  Qed.

  Definition mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r := 
    inv N (mcs γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r).
  
  (** Helper functions Spec **)
    
  Parameter inContents_spec : ∀ r n es (Cn: gmap K natUR) (k: K),
     ⊢ ({{{ node r n es Cn }}}
           inContents #n #k
       {{{ (t: option nat), 
              RET (match t with Some t => SOMEV #t | None => NONEV end);
                  node r n es Cn ∗ ⌜Cn !! k = t⌝ }}})%I.

  Parameter findNext_spec : ∀ r n es (Cn: gmap K natUR) (k: K),
     ⊢ ({{{ node r n es Cn }}}
           findNext #n #k
       {{{ (succ: bool) (n': Node),
              RET (match succ with true => SOMEV #n' | false => NONEV end);
                  node r n es Cn ∗ if succ then ⌜k ∈ es !!! n'⌝
                                else ⌜∀ n', k ∉ es !!! n'⌝ }}})%I.

  Lemma readClock_spec: ∀ γ_t lc q t, 
     ⊢ ({{{ own γ_t (●{q} MaxNat t) ∗ clock lc t }}}
           readClock #lc
       {{{ RET #t; own γ_t (●{q} MaxNat t) ∗ clock lc t }}})%I.
  Proof.
    intros γ_t lc q t.
    iIntros (Φ) "!# (Hqt & Hclock) HCont".
    wp_lam. wp_load. iApply "HCont". iFrame.
  Qed.  

  Lemma incrementClock_spec: ∀ γ_t (lc: loc) t, 
     ⊢ (<<< own γ_t (● MaxNat t)  ∗ clock lc t >>>
           incrementClock #lc @ ⊤
       <<< own γ_t (● MaxNat (t+1)) ∗ clock lc (t+1), RET #() >>>)%I.
  Proof.
    intros γ_t lc t. iIntros (Φ) "AU".
    wp_lam. wp_bind (!#lc)%E.
    iMod "AU" as "[(Ht & Hc) [H' _]]".
    wp_load. iMod ("H'" with "[Ht Hc]") as "AU".
    iFrame. iModIntro. wp_pures.
    iMod "AU" as "[(Ht & Hc) [_ H']]".
    wp_store.
    iMod (own_update (γ_t) (● (MaxNat (t))) 
             (● (MaxNat (t+1))) with "Ht") as "Ht".
    { apply (auth_update_auth _ _ (MaxNat (t+1))).
      apply max_nat_local_update. simpl. lia. }
     iMod ("H'" with "[Ht Hc]").
    assert (#(t+1) = #(t+1)%nat) as H'.
    { apply f_equal. 
      apply f_equal. lia. }
    iEval (rewrite H') in "Hc".
    iFrame. by iModIntro.
  Qed.

  Parameter addContents_spec : ∀ r es (Cn: gmap K natUR) (k: K) (t:nat),
     ⊢ ({{{ node r r es Cn }}}
           addContents #r #k #t
       {{{ (succ: bool) (Cn': gmap K natUR),
              RET #succ;
                  node r r es Cn' ∗ if succ then ⌜Cn' = <[k := t]> Cn⌝ 
                                else ⌜Cn' = Cn⌝ }}})%I.

  Parameter atCapacity_spec : ∀ r n es (Cn: gmap K natUR),
     ⊢ ({{{ node r n es Cn }}}
           atCapacity #n
       {{{ (b: bool), RET #b;
           node r n es Cn ∗ ⌜b = true ∨ b = false⌝ }}})%I.
           
  Parameter chooseNext_spec : ∀ r n esn (Cn: gmap K natUR),
     ⊢ ({{{ node r n esn Cn }}}
           chooseNext #n
       {{{ (m: Node) (esn' esm: esT) Cm, RET #m;
           node r n esn' Cn ∗ ⌜esn' !!! m ≠ ∅⌝
           ∗ (  ⌜esn' = esn⌝ 
              ∨ ⌜esn' = <[m := (esn' !!! m)]> esn⌝ 
                ∗ node r m esm Cm 
                ∗ lockLoc m ↦ #false
                ∗ ⌜Cm = ∅⌝ 
                ∗ ⌜esm = ∅⌝) }}})%I.

  Parameter mergeContents_spec : ∀ r n m esn esm (Cn Cm: gmap K natUR),
     ⊢ ({{{ node r n esn Cn ∗ node r m esm Cm ∗ ⌜esn !!! m ≠ ∅⌝ }}}
           mergeContents #n #m
       {{{ Cn' Cm', RET #m;
           node r n esn Cn' ∗ node r m esm Cm' 
           ∗ ⌜set_of_map Cn' ⊆ set_of_map Cn⌝
           ∗ ⌜set_of_map Cm' ⊆ set_of_map Cn ∪ set_of_map Cm⌝
           ∗ ⌜set_of_map Cn ∩ set_of_map Cm' ## set_of_map Cn'⌝
           ∗ ⌜dom (gset K) Cm ⊆ dom (gset K) Cm'⌝
           ∗ ⌜merge Cn (esn !!! m) Cm = merge Cn' (esn !!! m) Cm'⌝ }}})%I.

  (** Useful lemmas and definitions **)

  Instance test r n γ_t lc T : Laterable (if n =? r then 
                          own γ_t (●{1 / 2} MaxNat T) ∗ clock lc T else ⌜True⌝)%I.
  Proof.
    destruct (n =? r); apply timeless_laterable; apply _.
  Qed.

  Lemma inFP_domm γ_f n D : inFP γ_f n -∗ own γ_f (● D) -∗ ⌜n ∈ D⌝.
  Proof.
    iIntros "FP HD".
    iPoseProof (own_valid_2 _ _ _ with "[$HD] [$FP]") as "H'".
    iDestruct "H'" as %H'.
    apply auth_both_valid_discrete in H'.
    destruct H' as [H' _].
    apply gset_included in H'.
    iPureIntro. set_solver.
  Qed.

  Lemma own_alloc_set (S: gset K): True ==∗ 
          ∃ (γ: gmap K gname), ([∗ set] k ∈ S, own (γ !!! k) (● (MaxNat 0))).
  Proof.
    iIntros "_".
    iInduction S as [| s S] "IH" using set_ind_L.
    - iModIntro. iExists _. try done.
    - iMod (own_alloc (● (MaxNat 0))) as (γs)"H'".
      { rewrite auth_auth_valid. try done. }
      iDestruct "IH" as ">IH".
      iDestruct "IH" as (γ)"IH". 
      iModIntro. iExists (<[s := γs]> γ).
      rewrite (big_sepS_delete _ ({[s]} ∪ S) s); last by set_solver.
      iSplitL "H'". by rewrite lookup_total_insert.
      assert (({[s]} ∪ S) ∖ {[s]} = S) as HS. set_solver.
      rewrite HS. 
      iApply (big_sepS_mono 
                  (λ y, own (γ !!! y) (● {| max_nat_car := 0 |}) )%I
                  (λ y, own (<[s:=γs]> γ !!! y) (● {| max_nat_car := 0 |}))%I
                  S); try done.
      intros k k_in_S. iFrame. iIntros "H'".
      rewrite lookup_total_insert_ne; last by set_solver. 
      done.
      (* No idea what is happening here *) 
      Unshelve. exact (∅: gmap K gname).
  Qed.

  Lemma ghost_heap_sync γ_gh n γ_en γ_cn γ_bn γ_qn γ_cirn 
                                      γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' : 
    own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]}) 
      -∗ own γ_gh (◯ {[n := ghost_loc γ_en' γ_cn' γ_bn' γ_qn' γ_cirn']}) 
          -∗ ⌜γ_en = γ_en'⌝ ∗ ⌜γ_cn = γ_cn'⌝ ∗ ⌜γ_bn = γ_bn'⌝ 
             ∗ ⌜γ_qn = γ_qn'⌝ ∗ ⌜γ_cirn = γ_cirn'⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1" "H2" as "H".
    iPoseProof (own_valid with "H") as "Valid".
    iDestruct "Valid" as %Valid.
    rewrite auth_frag_valid in Valid *; intros Valid.
    apply singleton_valid in Valid.
    apply to_agree_op_inv in Valid.
    apply leibniz_equiv in Valid.
    inversion Valid.
    by iPureIntro.
  Qed.

  Lemma ghost_heap_update γ_gh (hγ: gmap Node per_node_gl) n 
                                γ_en γ_cn γ_bn γ_qn γ_cirn :
    ⌜n ∉ dom (gset Node) hγ⌝ -∗ 
          own γ_gh (● hγ) ==∗ 
            own γ_gh (● <[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]> hγ)
          ∗ own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]}).
  Proof.
    iIntros "%". rename H into n_notin_hγ.
    iIntros "Hown". set (<[ n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn ]> hγ) as hγ'.
    iDestruct (own_update _ _ 
        (● hγ' ⋅ ◯ {[ n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn ]})
               with "Hown") as "Hown".
    { apply auth_update_alloc. 
      rewrite /hγ'.
      apply alloc_local_update; last done.
      by rewrite <-not_elem_of_dom. }
    iMod (own_op with "Hown") as "[Ht● Ht◯]".
    iModIntro. iFrame.
  Qed.    

  Lemma frac_eq γ_e γ_c γ_b γ_q es Cn Bn Qn es' Cn' Bn' Qn' : 
              frac_ghost_state γ_e γ_c γ_b γ_q es Cn Bn Qn -∗
                  frac_ghost_state γ_e γ_c γ_b γ_q es' Cn' Bn' Qn' -∗ 
                    ⌜es = es'⌝ ∗ ⌜Cn = Cn'⌝ ∗ ⌜Bn = Bn'⌝ ∗ ⌜Qn = Qn'⌝.
  Proof.
    iIntros "H1 H2". unfold frac_ghost_state.
    iDestruct "H1" as "(H1_es & H1_c & H1_b & H1_q)".
    iDestruct "H2" as "(H2_es & H2_c & H2_b & H2_q)".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_es] [$H2_es]") as "Hes".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_c] [$H2_c]") as "Hc".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_b] [$H2_b]") as "Hb".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_q] [$H2_q]") as "Hq".
    iDestruct "Hes" as %Hes. iDestruct "Hc" as %Hc.
    iDestruct "Hb" as %Hb. iDestruct "Hq" as %Hq.
    apply frac_agree_op_valid in Hes. destruct Hes as [_ Hes].
    apply frac_agree_op_valid in Hc. destruct Hc as [_ Hc].
    apply frac_agree_op_valid in Hb. destruct Hb as [_ Hb].
    apply frac_agree_op_valid in Hq. destruct Hq as [_ Hq].
    apply leibniz_equiv_iff in Hes.
    apply leibniz_equiv_iff in Hc. 
    apply leibniz_equiv_iff in Hb.
    apply leibniz_equiv_iff in Hq.
    iPureIntro. repeat split; try done.   
  Qed.

  Lemma frac_update γ_e γ_c γ_b γ_q es Cn Bn Qn es' Cn' Bn' Qn' : 
              frac_ghost_state γ_e γ_c γ_b γ_q es Cn Bn Qn ∗ 
                 frac_ghost_state γ_e γ_c γ_b γ_q es Cn Bn Qn ==∗ 
                      frac_ghost_state γ_e γ_c γ_b γ_q es' Cn' Bn' Qn' ∗ 
                        frac_ghost_state γ_e γ_c γ_b γ_q es' Cn' Bn' Qn'.
  Proof.
    iIntros "(H1 & H2)". 
    iDestruct "H1" as "(H1_es & H1_c & H1_b & H1_q)".
    iDestruct "H2" as "(H2_es & H2_c & H2_b & H2_q)".
    iCombine "H1_es H2_es" as "Hes". 
    iEval (rewrite <-frac_agree_op) in "Hes". 
    iEval (rewrite Qp_half_half) in "Hes". 
    iCombine "H1_c H2_c" as "Hc". 
    iEval (rewrite <-frac_agree_op) in "Hc". 
    iEval (rewrite Qp_half_half) in "Hc". 
    iCombine "H1_b H2_b" as "Hb". 
    iEval (rewrite <-frac_agree_op) in "Hb". 
    iEval (rewrite Qp_half_half) in "Hb".
    iCombine "H1_q H2_q" as "Hq". 
    iEval (rewrite <-frac_agree_op) in "Hq". 
    iEval (rewrite Qp_half_half) in "Hq".
    iMod ((own_update (γ_e) (to_frac_agree 1 es) 
                  (to_frac_agree 1 es')) with "[$Hes]") as "Hes".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hes".
    iEval (rewrite frac_agree_op) in "Hes".  
    iDestruct "Hes" as "(H1_es & H2_es)".            
    iMod ((own_update (γ_c) (to_frac_agree 1 Cn) 
                  (to_frac_agree 1 Cn')) with "[$Hc]") as "Hc".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hc".
    iEval (rewrite frac_agree_op) in "Hc".  
    iDestruct "Hc" as "(H1_c & H2_c)".
    iMod ((own_update (γ_b) (to_frac_agree 1 Bn) 
                  (to_frac_agree 1 Bn')) with "[$Hb]") as "Hb".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hb".
    iEval (rewrite frac_agree_op) in "Hb".  
    iDestruct "Hb" as "(H1_b & H2_b)".
    iMod ((own_update (γ_q) (to_frac_agree 1 Qn) 
                  (to_frac_agree 1 Qn')) with "[$Hq]") as "Hq".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hq".
    iEval (rewrite frac_agree_op) in "Hq".  
    iDestruct "Hq" as "(H1_q & H2_q)".
    iModIntro. iFrame.
  Qed.


  Lemma auth_agree γ xs ys :
    own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.

  Lemma auth_agree' (γ: gname) (xs ys: gset KT) :
    own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.


  Lemma set_of_map_member_ne (C: gmap K nat) k :
            C !! k = None →    
              ∀ t, (k, t) ∉ set_of_map C.
  Proof.
    set (P := λ (s: gset KT) (m: gmap K nat), 
                   m !! k = None → ∀ t, (k, t) ∉ s). 
    apply (map_fold_ind P); try done.
    intros kx tx m r Hm HP. unfold P.
    unfold P in HP. destruct (decide (kx = k)).
    - subst kx. rewrite lookup_insert. try done.
    - rewrite lookup_insert_ne; try done. 
      intros Hm'. pose proof HP Hm' as HP. 
      intros t. intros Hnot. 
      rewrite elem_of_union in Hnot*; intros Hnot.
      destruct Hnot as [Hnot | Hnot].
      + by apply HP in Hnot.
      + rewrite elem_of_singleton in Hnot*; intros Hnot.
        inversion Hnot. try done.
  Qed.

  Lemma set_of_map_member (C: gmap K nat) k t :
            C !! k = Some(t) →    
              (k, t) ∈ set_of_map C.
  Proof.
    intros Hc. unfold set_of_map.
    set (P := λ (s: gset KT) (m: gmap K nat), 
                  ∀ j x, m !! j = Some x → (j,x) ∈ s). 
    apply (map_fold_ind P); try done.
    intros i x m s Hmi Hp. unfold P.
    intros j x'. destruct (decide (i = j)).
    - replace j. rewrite lookup_insert. 
      intros H'; inversion H'. set_solver.
    - rewrite lookup_insert_ne; try done.
      pose proof Hp j x' as Hp'. set_solver.
  Qed.

  Lemma set_of_map_member_rev (C: gmap K nat) k t :
            (k, t) ∈ set_of_map C → 
                C !! k = Some(t).
  Proof.
    set (P := λ (s: gset KT) (m: gmap K nat), 
                  ∀ j x, (j,x) ∈ s → m !! j = Some x).
    apply (map_fold_ind P); try done.
    intros i x m r Hmi Hp. unfold P.
    intros j x'. destruct (decide (i = j)).
    - replace j. rewrite lookup_insert.
      rewrite elem_of_union. intros [Hr | Hr].
      unfold P in Hp. pose proof Hp i x' Hr as Hp.
      rewrite Hp in Hmi. inversion Hmi.
      assert (x = x') by set_solver. by replace x.              
    - intros H'. assert ((j,x') ∈ r) as Hj by set_solver.
      pose proof Hp j x' Hj as Hp.
      rewrite lookup_insert_ne; try done.
  Qed.

  Lemma set_of_map_insert_subseteq (C: gmap K nat) k t :
         set_of_map (<[k := t]> C) ⊆ set_of_map C ∪ {[(k, t)]}.
  Proof.
    intros [k' t'] Hkt. destruct (decide (k' = k)).
    - replace k'. rewrite e in Hkt. 
      apply set_of_map_member_rev in Hkt.
      rewrite lookup_insert in Hkt.
      inversion Hkt. set_solver.
    - apply set_of_map_member_rev in Hkt.
      rewrite lookup_insert_ne in Hkt; try done.
      apply set_of_map_member in Hkt.
      set_solver.  
  Qed.          
  
  Lemma map_of_set_lookup_cases H k:
        (∃ T, (k, T) ∈ H ∧ (∀ t, (k,t) ∈ H → t ≤ T) ∧ map_of_set H !! k = Some T)
      ∨ ((∀ t, (k,t) ∉ H) ∧ map_of_set H !! k = None).
  Proof.
    set (P := λ (m: gmap K nat) (X: gset KT),
                (∃ T, (k, T) ∈ X ∧ (∀ t, (k,t) ∈ X → t ≤ T) 
                          ∧ m !! k = Some T)
              ∨ ((∀ t, (k,t) ∉ X) ∧ m !! k = None)).
    apply (set_fold_ind_L P); try done.
    - unfold P. right. split; try done.
    - intros [k' t'] X m Hnotin Hp.
      destruct (decide (k' = k)).
      + replace k'. unfold P. left. unfold P in Hp.
        destruct Hp as [Hp | Hp].
        * destruct Hp as [T Hp].
          destruct (decide (T < t')).
          ** exists t'. repeat split; first set_solver.
             intros t. rewrite elem_of_union.
             intros [Hv | Hv]. assert (t = t') by set_solver. 
             lia. destruct Hp as [_ [Hp _]].
             pose proof Hp t Hv. lia. simpl.
             assert (m !!! k <=? t' = true) as Hm.
             { unfold lookup_total, finmap_lookup_total.
               destruct Hp as [_ [_ Hp]]. rewrite Hp.
               simpl. rewrite leb_le. lia. }
             rewrite Hm. by rewrite lookup_insert.      
          ** assert (t' = T ∨ t' < T) as Ht by lia. clear n. 
             exists T. destruct Hp as [Hp1 [Hp2 Hp3]].
             repeat split; first set_solver.
             intros t. rewrite elem_of_union.
             intros [Hv | Hv]. assert (t = t') by set_solver. 
             lia. pose proof Hp2 t Hv. lia. simpl.
             destruct Ht as [Ht | Ht].
             assert (m !!! k <=? t' = true) as Hm.
             { unfold lookup_total, finmap_lookup_total.
               rewrite Hp3. simpl. rewrite leb_le. lia. }
             rewrite Hm. rewrite lookup_insert. by rewrite Ht.
             assert (m !!! k <=? t' = false) as Hm.
             { unfold lookup_total, finmap_lookup_total.
               rewrite Hp3. simpl. by apply leb_correct_conv. }
             by rewrite Hm.
        * exists t'. simpl. repeat split; first set_solver.
          intros t. rewrite elem_of_union. intros [Hv | Hv].
          assert (t = t') by set_solver. lia.
          destruct Hp as [Hp _]. 
          pose proof Hp t as Hp. set_solver.
          assert (m !!! k <=? t' = true) as Hm.
          { unfold lookup_total, finmap_lookup_total.
            destruct Hp as [_ Hp]. rewrite Hp. by simpl. }
          rewrite Hm. by rewrite lookup_insert.
      + unfold P. unfold P in Hp.
        destruct Hp as [Hp | Hp].
        * destruct Hp as [T [Hp1 [Hp2 Hp3]]].
          left. exists T. repeat split; first set_solver.
          intros t Hkt. assert ((k,t) ∈ X) as Hx by set_solver.
          by pose proof Hp2 t Hx.
          simpl. 
          destruct (m !!! k' <=? t'). 
          rewrite lookup_insert_ne; try done. done.
        * destruct Hp as [Hp1 Hp2]. right.
          repeat split; first set_solver. simpl.   
          destruct (m !!! k' <=? t'). 
          rewrite lookup_insert_ne; try done. done.
  Qed.
  
  Lemma map_of_set_lookup H k T : 
        (k, T) ∈ H → (∀ t, (k, t) ∈ H → t ≤ T) →
           map_of_set H !! k = Some T.
  Proof.
    intros Hkt Hmax.
    pose proof (map_of_set_lookup_cases H k) as Hp.
    destruct Hp as [Hp | Hp].
    - destruct Hp as [T' [Hp1 [Hp2 Hp3]]].
      pose proof Hmax T' Hp1 as Ht1.
      pose proof Hp2 T Hkt as Ht2.
      assert (T = T') as Ht by lia.
      by rewrite Ht.
    - destruct Hp as [Hp _].
      pose proof Hp T. set_solver.
  Qed.

  Lemma map_of_set_union_ne H k t k' : 
          k' ≠ k → map_of_set (H ∪ {[(k, t)]}) !! k' = map_of_set H !! k'.
  Proof.
    intros Hk.
    pose proof (map_of_set_lookup_cases H k') as Hp.
    pose proof (map_of_set_lookup_cases (H ∪ {[(k,t)]}) k') as Hu.
    destruct Hp as [Hp | Hp].
    - destruct Hu as [Hu | Hu].
      + destruct Hp as [T [Hp1 [Hp2 Hp3]]].
        destruct Hu as [T' [Hu1 [Hu2 Hu3]]].
        assert (T ≤ T') as Ht1.
        { assert ((k', T) ∈ H ∪ {[k, t]}) as Ht by set_solver.
          by pose proof Hu2 T Ht. }
        assert (T' ≤ T) as Ht2.
        { assert ((k', T') ∈ H) as Ht by set_solver.
          by pose proof Hp2 T' Ht. }  
        rewrite Hp3 Hu3. assert (T = T') as Ht by lia.
        by rewrite Ht.
      + destruct Hp as [T [Hp1 [Hp2 Hp3]]].
        destruct Hu as [Hu1 Hu2].
        pose proof Hu1 T as Hu1. set_solver.
    - destruct Hu as [Hu | Hu].
      + destruct Hp as [Hp1 Hp2].         
        destruct Hu as [T' [Hu1 [Hu2 Hu3]]].
        pose proof Hp1 T' as Hp1. set_solver.      
      + destruct Hp as [Hp1 Hp2].
        destruct Hu as [Hu1 Hu2].
        by rewrite Hp2 Hu2.    
  Qed.

  Lemma map_of_set_insert_eq (C: gmap K nat) k T H :
        (∀ t, (k, t) ∈ H → t < T) → 
                  C = map_of_set H →
                 <[k := T]> C = map_of_set (H ∪ {[(k, T)]}).
  Proof.
    intros Hmax Hc. apply map_eq. intros k'.
    destruct (decide (k' = k)). 
    - replace k'. rewrite lookup_insert.
      rewrite (map_of_set_lookup _ _ T); try done.
      set_solver. intros t'. rewrite elem_of_union.
      intros [Hk | Hk]. pose proof Hmax t' Hk. lia.
      assert (t' = T) by set_solver. by replace t'.
    - rewrite map_of_set_union_ne; try done.
      rewrite lookup_insert_ne; try done.
      by rewrite Hc.
  Qed. 

  Lemma flowint_update_result γ I I_n I_n' x :
    ⌜flowint_update_P (KT_multiset K) I I_n I_n' x⌝ ∗ own γ x -∗
    ∃ I', ⌜contextualLeq (KT_multiset K) I I'⌝
          ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
          ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (view_auth_proj x); last first.
    - intros Hx. iIntros "(% & ?)". iExFalso. done.
    - intros [q a] Hx.
      iIntros "[HI' Hown]". iDestruct "HI'" as %HI'.
      destruct HI' as [I' HI'].
      destruct HI' as [Hagree [Hq [HIn [Hcontxl HIo]]]].
      iExists I'.
      iSplit. by iPureIntro.
      iSplit. by iPureIntro. destruct x.
      simpl in Hx. simpl in HIn.
      rewrite Hx. rewrite <-HIn.
      rewrite Hq Hagree.
      assert (● I' ⋅ ◯ I_n' = View (Some (1%Qp, to_agree I')) I_n') as H'.
      { rewrite /(● I' ⋅ ◯ I_n'). unfold cmra_op.
        simpl. unfold view_op. simpl.
        assert (ε ⋅ I_n' = I_n') as H'. by rewrite left_id.
        rewrite H'. unfold op, cmra_op. by simpl. }   
      by iEval (rewrite H').
  Qed.

  Lemma flowint_update_result' γ I I_n I_n' x :
    ⌜flowint_update_P (K_multiset) I I_n I_n' x⌝ ∗ own γ x -∗
    ∃ I', ⌜contextualLeq (K_multiset) I I'⌝
          ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
          ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (view_auth_proj x); last first.
    - intros Hx. iIntros "(% & ?)". iExFalso. done.
    - intros [q a] Hx.
      iIntros "[HI' Hown]". iDestruct "HI'" as %HI'.
      destruct HI' as [I' HI'].
      destruct HI' as [Hagree [Hq [HIn [Hcontxl HIo]]]].
      iExists I'.
      iSplit. by iPureIntro.
      iSplit. by iPureIntro. destruct x.
      simpl in Hx. simpl in HIn.
      rewrite Hx. rewrite <-HIn.
      rewrite Hq Hagree.
      assert (● I' ⋅ ◯ I_n' = View (Some (1%Qp, to_agree I')) I_n') as H'.
      { rewrite /(● I' ⋅ ◯ I_n'). unfold cmra_op.
        simpl. unfold view_op. simpl.
        assert (ε ⋅ I_n' = I_n') as H'. by rewrite left_id.
        rewrite H'. unfold op, cmra_op. by simpl. }   
      by iEval (rewrite H').
  Qed.    

  Lemma dom_lookup (C: gmap K nat) k :
        C !! k ≠ None → k ∈ dom (gset K) C.
  Proof.
    intros Hcn. destruct (C !! k) eqn: Hcnk.
    rewrite elem_of_dom. rewrite Hcnk.
    by exists n. done.
  Qed.
  
  Lemma contents_in_reach_bigS_update (S : gset K) (γ: gmap K gname) 
                                          (Bm Bm': gmap K nat) :
        ⌜∀ k, k ∈ S → Bm !!! k ≤ Bm' !!! k⌝ -∗ 
          [∗ set] k ∈ S, own (γ !!! k) (● (MaxNat (Bm !!! k))) -∗
            |==>  [∗ set] k ∈ S, own (γ !!! k) (● (MaxNat (Bm' !!! k))).
  Proof.
  Admitted.
  
  Definition map_subset (S: gset K) (C: gmap K nat) :=
              let f := λ a s', s' ∪ {[(a, C !!! a)]} in
                        set_fold f (∅: gset KT) S.          

  Definition map_restriction (S: gset K) (C: gmap K nat) := 
              let f := λ a m, <[a := C !!! a ]> m in
                        set_fold f (∅: gmap K nat) S.
                        
  
  Lemma lookup_map_restriction S (C: gmap K nat) (k: K):
              k ∈ S → map_restriction S C !! k = Some (C !!! k).
  Proof.
    set (P := λ (m: gmap K nat) (X: gset K),
                    ∀ x, x ∈ X → m !! x = Some (C !!! x)).
    apply (set_fold_ind_L P); try done.
    intros x X r Hx HP.
    unfold P in HP. unfold P.
    intros x' Hx'.
    destruct (decide (x' = x)).
    - subst x'. by rewrite lookup_insert.
    - assert (x' ∈ X) as x'_in_X. set_solver.
      rewrite lookup_insert_ne. apply HP.
      done. done.
  Qed.

  Lemma map_subset_member S C k t:
              (k, t) ∈ map_subset S C ↔ k ∈ S ∧ t = C !!! k.
  Proof.
    set (P := λ (m: gset KT) (X: gset K),
                    ∀ kx tx, (kx, tx) ∈ m ↔ kx ∈ X ∧ tx = C !!! kx).
    apply (set_fold_ind_L P); try done.
    - unfold P. intros kx tx. set_solver.
    - intros x X r Hx HP. unfold P.
      unfold P in HP. intros kx' tx'.
      split.
      + intros Hktx. rewrite elem_of_union in Hktx*; intros Hktx.
        destruct Hktx as [H' | H'].
        * apply HP in H'. destruct H' as [H' H''].
          split; try done. set_solver.
        * rewrite elem_of_singleton in H'*; intros H'.
          inversion H'. split; try done; set_solver.
      + intros [H' H'']. rewrite elem_of_union in H'*; intros H'.
        destruct H' as [H' | H'].
        rewrite elem_of_singleton in H'*; intros H'.
        rewrite H'. rewrite H''. set_solver.
        assert ((kx', tx') ∈ r) as Hkt.
        apply HP. split; try done.
        set_solver.       
  Qed.              

  Lemma map_restriction_dom S C :
              dom (gset K) (map_restriction S C) = S.
  Proof.
    set (P := λ (m: gmap K nat) (X: gset K), dom (gset K) m = X).
    apply (set_fold_ind_L P); try done.
    - unfold P; set_solver. 
    - intros x X r Hx HP. unfold P. unfold P in HP. 
      apply leibniz_equiv. rewrite dom_insert.
      rewrite HP. done.
  Qed.            

  Lemma map_of_set_lookup_some_aux (H: gset KT) k :
          (∀ t, (k,t) ∉ H) ∨ (∃ T, (k, T) ∈ H ∧ (∀ t', (k,t') ∈ H → t' ≤ T)).
  Proof.
    set (P := λ (X: gset KT), (∀ t, (k,t) ∉ X) ∨ 
                  (∃ T, (k, T) ∈ X ∧ (∀ t', (k,t') ∈ X → t' ≤ T))).
    apply (set_ind_L P); try done.
    - unfold P. left. intros t. set_solver.
    - intros [k' t'] X Hkt HP. subst P.
      simpl in HP. simpl. destruct (decide (k' = k)).
      + subst k'. destruct HP as [H' | H'].
        * right. exists t'. split.
          set_solver. intros t. destruct (decide (t' = t)).
          subst t'. intros; done.
          intros H''. assert ((k,t) ∈ X).
          set_solver. pose proof H' t as H'.
          done.
        * right. destruct H' as [T H']. 
          destruct (decide (t' < T)).
          ** exists T. split.
             destruct H' as [H' _].
             set_solver. intros t Hkt'.
             rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia. 
             destruct H' as [_ H'']. apply H''; try done.
          ** exists t'. split. set_solver.
             intros t Hkt'. rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia.
             destruct H' as [_ H'']. 
             apply (Nat.le_trans _ T _); try lia.
             apply H''. try done.
      + destruct HP as [H' | H'].
        * left. intros t. set_solver.
        * right. destruct H' as [T H'].
          exists T. destruct H' as [H' H''].
          split. set_solver. intros t.
          intros Hkt'. rewrite elem_of_union in Hkt'*; intros Hkt'.
          destruct Hkt' as [Hkt' | Hkt'].
          rewrite elem_of_singleton in Hkt'*; intros Hkt'.
          inversion Hkt'. done. apply H''; try done.
  Qed.

  Lemma map_of_set_lookup_some (H: gset KT) k t :
              (k, t) ∈ H → is_Some(map_of_set H !! k).
  Proof.
    intros Hkt.
    pose proof map_of_set_lookup_some_aux H k as Hkt'.
    destruct Hkt' as [Hkt' | Hkt'].
    { pose proof Hkt' t as H'. set_solver. }
    pose proof (map_of_set_lookup_cases H k) as H'.
    destruct H' as [H' | H'].
    - destruct H' as [T' H'].
      destruct H' as [_ [_ H']].
      rewrite H'. by exists T'.
    - destruct Hkt' as [T Hkt'].
      destruct Hkt' as [Hkt' _].
      destruct H' as [H' _].
      pose proof H' T as H'.
      set_solver.   
  Qed.            

  (** Lock module **)
  
  Parameter getLockLoc_spec : ∀ (n: Node),
    ⊢ ({{{ True }}}
        getLockLoc #n
       {{{ (l:loc), RET #l; ⌜lockLoc n = l⌝ }}})%I.
  
  Lemma lockNode_spec (n: Node):
    ⊢ <<< ∀ (b: bool), (lockLoc n) ↦ #b >>>
      lockNode #n    @ ⊤
    <<< (lockLoc n) ↦ #true ∗ ⌜b = false⌝ , RET #() >>>.
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

  Lemma lockNode_spec_high γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r n:
    ⊢ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
        inFP γ_f n -∗
              <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑N
              <<< ∃ Cn Bn Qn, nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn, RET #() >>>.
  Proof.
    iIntros "#mcsInv #FP_n".
    iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iInv "mcsInv" as ">mcs". iDestruct "mcs" as (T H hγ I R) "(Hglob & Hstar)".
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
    iPoseProof (inFP_domm with "[$FP_n] [$]") as "%". rename H0 into n_in_I.
    iEval (rewrite (big_sepS_elem_of_acc (_) (domm I) n); 
           last by eauto) in "Hstar".
    iDestruct "Hstar" as "(Hn & Hstar')".
    iDestruct "Hn" as (b Cn Bn Qn) "(Hlock & Hnp & Hns)".
    iAaccIntro with "Hlock".
    { iIntros "Hlockn". iModIntro.
      iSplitR "AU".
      { iExists T, H, hγ, I, R. iFrame.
        iPoseProof ("Hstar'" with "[-]") as "Hstar".
        iExists b, Cn, Bn, Qn. iFrame.
        iNext. iFrame.
      }
      iFrame.
    }
    iIntros "(Hlockn & %)". subst b.
    iMod "AU" as "[_ [_ Hclose]]".
    iMod ("Hclose" with "[Hnp]") as "HΦ"; try done.
    iModIntro. iSplitR "HΦ".
    iNext. iExists T, H, hγ, I, R.
    iPoseProof ("Hstar'" with "[Hlockn Hns]") as "Hstar".
    iExists true, Cn, Bn, Qn. iFrame.
    iSplitR "Hstar". iFrame. iFrame. done.
  Qed.

  Lemma unlockNode_spec (n: Node) :
    ⊢ <<< lockLoc n ↦ #true >>>
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
  
  Lemma int_domm γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r t H hγ I R n In :
    own γ_I (◯ In) -∗ ⌜domm In = {[n]}⌝
    -∗ global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r t H hγ I R
    -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "Hi Dom_In Hglob".
    iDestruct "Dom_In" as %Dom_In.
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
    iPoseProof ((auth_own_incl γ_I (I) (In)) with "[$]") as "%".
    rename H0 into I_incl. destruct I_incl as [Io I_incl].
    iPoseProof (own_valid with "HI") as "%". rename H0 into Valid_I.
    iPureIntro. rewrite I_incl. rewrite flowint_comp_fp.
    rewrite Dom_In. set_solver. rewrite <- I_incl.
    by apply auth_auth_valid.
  Qed.

  Lemma unlockNode_spec_high γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r n Cn Bn Qn:
    ⊢ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
        inFP γ_f n -∗ nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn -∗
              <<< True >>>
                unlockNode #n    @ ⊤ ∖ ↑N
              <<< True, RET #() >>>.
  Proof.
    iIntros "#mcsInv #FP_n Hnp". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iInv "mcsInv" as ">mcs". iDestruct "mcs" as (T H hγ I R) "(Hglob & Hstar)".
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
    iPoseProof (inFP_domm with "[$FP_n] [$]") as "%". rename H0 into n_in_I.
    iEval (rewrite (big_sepS_elem_of_acc (_) (domm I) n); 
           last by eauto) in "Hstar".
    iDestruct "Hstar" as "(Hn & Hstar')".
    iDestruct "Hn" as (b Cn' Bn' Qn') "(Hlock & Hnp' & Hns)".
    iAssert (lockLoc n ↦ #true ∗ nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn)%I
      with "[Hlock Hnp Hnp']" as "(Hlock & Hnp)".
    {
      destruct b.
    - (* Case n locked *)
      iFrame "∗".
    - (* Case n unlocked: impossible *)
      iDestruct "Hnp" as (? ? ? ? ? ? ?) "(n & _)".
      iDestruct "Hnp'" as (? ? ? ? ? ? ?) "(n' & _)".
      iExFalso. iApply (node_sep_star r n). iFrame.
    }
    iAaccIntro with "Hlock".
    { iIntros "Hlock". iModIntro.
      iSplitR "Hnp AU".
      iExists T, H, hγ, I, R. iNext. iFrame.
      iPoseProof ("Hstar'" with "[Hlock Hns]") as "Hstar".
      iExists true, Cn', Bn', Qn'. iFrame.
      iFrame. iFrame. 
    }
    iIntros "Hlock".
    iMod "AU" as "[_ [_ Hclose]]".
    iMod ("Hclose" with "[]") as "HΦ"; try done.
    iModIntro. iSplitR "HΦ".
    iNext. iExists T, H, hγ, I, R.
    iPoseProof ("Hstar'" with "[Hlock Hns Hnp]") as "Hstar".
    iExists false, Cn, Bn, Qn.
    iAssert (nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn
                      ∗ nodeShared γ_I γ_R γ_f γ_gh r n Cn Bn Qn H T)%I
      with "[Hns Hnp]" as "(Hns & Hnp)".
    {
      iDestruct "Hnp" as (γ_en γ_cn γ_bn γ_qn γ_cirn esn T')
                             "(node_n & HnP_gh & HnP_frac & HnP_C & HnP_t)".
      iDestruct "Hns" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In0 Rn0) 
                           "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                            & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
      iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
        as "(% & % & % & % & %)".
      subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
      iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
      destruct H0 as [Hes [Hc [Hb Hq]]]. 
      subst es'. subst Cn'. subst Bn'. subst Qn'.
      iSplitL "node_n HnP_gh HnP_frac HnP_C HnP_t".
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn, T'.
      iFrame.
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn, In0, Rn0.
      iFrame.
    }
    iFrame. iFrame. iFrame.
  Qed.
  
  (** Proofs **)  

  Lemma compact_spec γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r (n: Node) :
    ⊢ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
        inFP γ_f n -∗ <<< ∀ t H, MCS γ_te γ_he t H >>> 
                            compact #n @ ⊤ ∖ ↑N
                      <<< MCS γ_te γ_he t H, RET #() >>>.
  Proof.
    iIntros "#HInv". iLöb as "IH" forall (n).
    iIntros "#FP_n". iIntros (Φ) "AU". wp_lam.
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame.
    iIntros (Cn Bn Qn)"HnP_n". iModIntro.
    wp_pures. iDestruct "HnP_n" as (γ_en γ_cn γ_bn γ_qn γ_cirn esn T)"(node_n   
                            & HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iPoseProof ((node_edgeset_disjoint r n) with "[$node_n]") as "%".
    rename H into Disj_esn.                        
    wp_apply (atCapacity_spec with "node_n").
    iIntros (b) "(node_n & _)". destruct b; last first; wp_pures.
    - awp_apply (unlockNode_spec_high with "[] [] [-AU]"); try done.
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn, T. iFrame.
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iMod "AU" as (t H)"[MCS [_ Hclose]]".
      iMod ("Hclose" with "MCS") as "HΦ".
      by iModIntro.
    - wp_apply (chooseNext_spec with "node_n").
      iIntros (m esn' esm0 Cm0)"(node_n & es_ne & Hor)".
      iDestruct "es_ne" as %es_ne.
      iDestruct "Hor" as "[ Hesn' | 
                      (Hesn' & node_m & Hl_m & Hcm & Hesm) ]"; last first.
      + iDestruct "Hesn'" as %Hesn'.
        iDestruct "Hcm" as %Hcm.
        iDestruct "Hesm" as %Hesm.
        wp_pures.
        iApply fupd_wp. iInv "HInv" as ">H".
        iDestruct "H" as (T0' H0 hγ0 I0 R0) "(Hglob & Hstar)".
        iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".

        iAssert (⌜m ∉ domm I0⌝)%I as "%".
        { destruct (decide (m ∈ domm I0)); try done.
          rewrite (big_sepS_delete _ (domm I0) m); last by eauto.
          iDestruct "Hstar" as "(Hm & _)".
          iDestruct "Hm" as (bm Cm Bm Qm)"(Hl_m' & _)".
          iDestruct (mapsto_valid_2 with "Hl_m Hl_m'") as "%".
          exfalso. done. }

        iAssert (⌜n ∈ domm I0⌝)%I as "%". 
        { by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rename H into m_notin_I0. rename H1 into n_in_I0.  
        rewrite (big_sepS_delete _ (domm I0) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In0 Rn0) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn'. subst Bn'. subst Qn'.
          
        set (Qm0 := ∅ : gmap K nat).  
        set (Bm0 := ∅ : gmap K nat).  
        set (Im0 := int {| infR := {[m := ∅]} ; outR := ∅|} : KT_flowint_ur K).
        set (Rm0 := int {| infR := {[m := ∅]} ; outR := ∅|} : inset_flowint_ur K).

        iAssert (⌜r ∈ domm I0⌝)%I as "%". 
        { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
        rename H into r_in_I0.
        assert (m ≠ r) as m_neq_r. 
        { clear -m_notin_I0 r_in_I0. set_solver. }
        assert (m ≠ n) as m_neq_n. 
        { clear -m_notin_I0 n_in_I0. set_solver. }
        assert (domm Im0 = {[m]}) as Domm_Im0.
        { subst Im0. unfold domm, dom, flowint_dom.
          unfold inf_map. simpl. apply leibniz_equiv. 
          by rewrite dom_singleton. }
        assert (domm Rm0 = {[m]}) as Domm_Rm0.
        { subst Im0. unfold domm, dom, flowint_dom.
          unfold inf_map. simpl. apply leibniz_equiv. 
          by rewrite dom_singleton. }  

        iAssert (⌜esn !!! m = ∅⌝)%I as %Esn_empty.
        { destruct (decide (esn !!! m = ∅)); try done.
          iAssert (⌜esn !!! m ≠ ∅⌝)%I as "H'".
          by iPureIntro. 
          iPoseProof ("HnS_cl" with "H'") as "Hfp_m".
          iAssert (⌜m ∈ domm I0⌝)%I as "%". 
          { by iPoseProof (inFP_domm _ _ _ with "[$Hfp_m] [$Hf]") as "H''". }
          iPureIntro. clear -H m_notin_I0. set_solver. }
        
        iPoseProof (own_valid with "HI") as "%".
        rename H into Valid_I0.
        rewrite auth_auth_valid in Valid_I0 *; intros Valid_I0. 

        iDestruct "HnS_si" as "(HnI & HnR & Domm_In0 & Domm_Rn0)".
        iPoseProof (own_valid with "HnI") as "%".
        rename H into Valid_In0. 
        rewrite auth_frag_valid in Valid_In0 *; intros Valid_In0.
        iPoseProof (own_valid with "HnR") as "%".
        rename H into Valid_Rn0. 
        rewrite auth_frag_valid in Valid_Rn0 *; intros Valid_Rn0.
        iDestruct "Domm_In0" as %Domm_In0.
        iDestruct "Domm_Rn0" as %Domm_Rn0.
        
        assert (✓ Im0) as Valid_Im0.
        { unfold valid, cmra_valid, flowint_valid.
          subst Im0. simpl. split.
          solve_map_disjoint. 
          intros _; try done. }
        assert (✓ Rm0) as Valid_Rm0.
        { unfold valid, cmra_valid, flowint_valid.
          subst Rm0. simpl. split.
          solve_map_disjoint. 
          intros _; try done. }

        iPoseProof ((auth_own_incl γ_I I0 In0) with "[$HI $HnI]") as "%".
        rename H into Incl_In0. destruct Incl_In0 as [Iz Incl_In0].
        iDestruct "Out_I" as %Out_I.
        assert (out In0 m = 0%CCM ∧ out Iz m = 0%CCM) as [Out_In_m Out_Iz_m].
        { unfold outflow_zero in Out_I.
          rewrite Incl_In0 in Valid_I0*; intro H'.
          rewrite Incl_In0 in m_notin_I0*; intro H''.
          pose proof (intComp_unfold_out In0 Iz H' m H'') as Hout.
          unfold out in Hout. unfold out.
          rewrite <-Incl_In0 in Hout. rewrite Out_I in Hout. 
          rewrite nzmap_lookup_empty in Hout. 
          unfold ccmunit, ccm_unit in Hout. simpl in Hout.
          unfold lift_unit in Hout. unfold ccmop, ccm_op in Hout.
          simpl in Hout. unfold lift_op in Hout.
          unfold ccmop, ccm_op in Hout. simpl in Hout.
          rewrite nzmap_eq in Hout*; intros Hout.
          unfold ccmunit, lift_unit. split; apply nzmap_eq;
          intros k; rewrite nzmap_lookup_empty;
          unfold ccmunit, ccm_unit; simpl;
          unfold nat_unit; pose proof Hout k as Hout;
          rewrite nzmap_lookup_empty in Hout;
          unfold ccmunit, ccm_unit in Hout;
          simpl in Hout; unfold nat_unit, nat_op in Hout;
          rewrite nzmap_lookup_merge in Hout; clear-Hout; lia. }

        assert (✓ (In0 ⋅ Im0)) as Valid_Inm0.
        { apply intValid_composable. unfold intComposable.
          repeat split; try done.
          * simpl. solve_map_disjoint.
          * rewrite Domm_In0 Domm_Im0.
            clear -m_notin_I0 n_in_I0.
            set_solver.
          * unfold map_Forall. intros n' x Hinf.
            subst Im0. unfold out. simpl.
            rewrite nzmap_lookup_empty.
            rewrite ccm_left_id. rewrite ccm_pinv_unit.
            unfold inf. by rewrite Hinf.
          * unfold map_Forall. intros n' x Hinf.
            destruct (decide (n' = m)).
            ** subst n'. rewrite Out_In_m.
               rewrite ccm_left_id. rewrite ccm_pinv_unit.
               unfold inf. by rewrite Hinf.
            ** subst Im0. simpl in Hinf.
               rewrite lookup_singleton_ne in Hinf; try done. }

        assert (domm (In0 ⋅ Im0) = {[n; m]}) as Domm_Inm0.
        { rewrite flowint_comp_fp; try done.
          by rewrite Domm_In0 Domm_Im0. }
        assert (domm I0 = domm In0 ∪ domm Iz) as Domm_Inz.
        { rewrite Incl_In0. rewrite flowint_comp_fp. done.
          by rewrite <-Incl_In0. }   
        assert (n ∉ domm Iz) as n_notin_Iz.
        { rewrite Incl_In0 in Valid_I0 *; intros Valid_In0'.
          apply intComposable_valid in Valid_In0'.
          unfold intComposable in Valid_In0'.
          destruct Valid_In0' as [_ [_ [H' _]]].
          rewrite Domm_In0 in H'. clear -H'; set_solver. }

        assert (m ∉ domm Iz) as m_notin_Iz.
        { clear -Domm_Inz m_notin_I0. set_solver. }
          
                
        iMod (own_updateP (flowint_update_P (KT_multiset K) I0 In0 (In0 ⋅ Im0)) γ_I
                   (● I0 ⋅ ◯ (In0)) with "[HI HnI]") as (Io) "H'".
        { rewrite Incl_In0. apply flowint_update. 
          split; last split.
          - unfold contextualLeq.
            repeat split; try done.
            + rewrite flowint_comp_fp; try done.
              clear; set_solver.
            + intros n' H'.
              assert (n' = n) as Hn.
              { rewrite Domm_In0 in H'.
                clear -H'; set_solver. }
              subst n'.
              pose proof (intComp_inf_1 In0 Im0 Valid_Inm0 n H') as H''.
              rewrite H''. subst Im0; unfold out; simpl.
              rewrite nzmap_lookup_empty.
              by rewrite ccm_pinv_unit. 
            + intros n' H'.
              pose proof (intComp_unfold_out In0 Im0 Valid_Inm0 n' H') as H''.
              rewrite H''. unfold out at 3, out_map. subst Im0.
              simpl. rewrite nzmap_lookup_empty.
              by rewrite ccm_right_id.
          - rewrite Domm_Inm0. clear -n_notin_Iz m_notin_Iz.
            set_solver.
          - intros n' Hn'. rewrite Domm_Inm0 Domm_In0 in Hn'.
            assert (n' = m) as H'. clear -Hn'. set_solver.
            subst n'. by unfold out in Out_Iz_m. }              

        { rewrite own_op. iFrame. }                        
        iPoseProof ((flowint_update_result γ_I I0 In0 (In0 ⋅ Im0))
                        with "H'") as (I0') "(% & % & (HI & HIn))".
        rename H into ContLeq_I0. clear Io. 
        destruct H1 as [Io [HI0 HI0']].
        iEval (rewrite auth_frag_op) in "HIn".
        iDestruct "HIn" as "(HIn & HIm)".
        iPoseProof (own_valid with "HI") as "%".
        rename H into Valid_I0'.
        rewrite auth_auth_valid in Valid_I0' *; intros Valid_I0'. 

        assert (domm I0' = domm I0 ∪ {[m]}) as Domm_I0'.
        { rewrite Incl_In0 in HI0*; intros H'.
          apply intComp_cancelable in H'. 
          rewrite HI0'. repeat rewrite flowint_comp_fp.
          rewrite Domm_Im0 H'. clear; set_solver.
          rewrite Incl_In0 in Valid_I0 *; intros H''.
          done. done. apply leibniz_equiv_iff in HI0'. 
          by rewrite <-HI0'. by rewrite <-Incl_In0. }

        assert (domm I0' ∖ {[m]} = domm I0) as Domm_I0_m.
        { clear -Domm_I0' m_notin_I0. set_solver. }  

        
        iAssert (⌜r ∈ domm R0⌝)%I as "%". 
        { iDestruct "domm_IR" as %H'. iPureIntro. by rewrite <-H'. }
        rename H into r_in_R0.
        iAssert (⌜m ∉ domm R0⌝)%I as "%".
        { iDestruct "domm_IR" as %H'. iPureIntro. by rewrite <-H'. }
        rename H into m_notin_R0.
        iAssert (⌜n ∈ domm R0⌝)%I as "%".
        { iDestruct "domm_IR" as %H'. iPureIntro. by rewrite <-H'. }
        rename H into n_in_R0.        
        
        iPoseProof (own_valid with "HR") as "%".
        rename H into Valid_R0.
        rewrite auth_auth_valid in Valid_R0 *; intros Valid_R0. 
        
        iPoseProof ((auth_own_incl γ_R R0 Rn0) with "[$HR $HnR]") as "%".
        rename H into Incl_Rn0. destruct Incl_Rn0 as [Rz Incl_Rn0].
        iDestruct "Out_R" as %Out_R.
        assert (out Rn0 m = 0%CCM ∧ out Rz m = 0%CCM) as [Out_Rn_m Out_Rz_m].
        { unfold outflow_zero in Out_R.
          rewrite Incl_Rn0 in Valid_R0*; intro H'.
          rewrite Incl_Rn0 in m_notin_R0*; intro H''.
          pose proof (intComp_unfold_out Rn0 Rz H' m H'') as Hout.
          unfold out in Hout. unfold out.
          rewrite <-Incl_Rn0 in Hout. rewrite Out_R in Hout. 
          rewrite nzmap_lookup_empty in Hout. 
          unfold ccmunit, ccm_unit in Hout. simpl in Hout.
          unfold lift_unit in Hout. unfold ccmop, ccm_op in Hout.
          simpl in Hout. unfold lift_op in Hout.
          unfold ccmop, ccm_op in Hout. simpl in Hout.
          rewrite nzmap_eq in Hout*; intros Hout.
          unfold ccmunit, lift_unit. split; apply nzmap_eq;
          intros k; rewrite nzmap_lookup_empty;
          unfold ccmunit, ccm_unit; simpl;
          unfold nat_unit; pose proof Hout k as Hout;
          rewrite nzmap_lookup_empty in Hout;
          unfold ccmunit, ccm_unit in Hout;
          simpl in Hout; unfold nat_unit, nat_op in Hout;
          rewrite nzmap_lookup_merge in Hout; clear-Hout; lia. }

        assert (✓ (Rn0 ⋅ Rm0)) as Valid_Rnm0.
        { apply intValid_composable. unfold intComposable.
          repeat split; try done.
          * simpl. solve_map_disjoint.
          * rewrite Domm_Rn0 Domm_Rm0.
            clear -m_notin_R0 n_in_R0.
            set_solver.
          * unfold map_Forall. intros n' x Hinf.
            subst Rm0. unfold out. simpl.
            rewrite nzmap_lookup_empty.
            rewrite ccm_left_id. rewrite ccm_pinv_unit.
            unfold inf. by rewrite Hinf.
          * unfold map_Forall. intros n' x Hinf.
            destruct (decide (n' = m)).
            ** subst n'. rewrite Out_Rn_m.
               rewrite ccm_left_id. rewrite ccm_pinv_unit.
               unfold inf. by rewrite Hinf.
            ** subst Rm0. simpl in Hinf.
               rewrite lookup_singleton_ne in Hinf; try done. }

        assert (domm (Rn0 ⋅ Rm0) = {[n; m]}) as Domm_Rnm0.
        { rewrite flowint_comp_fp; try done.
          by rewrite Domm_Rn0 Domm_Rm0. }
        assert (domm R0 = domm Rn0 ∪ domm Rz) as Domm_Rnz.
        { rewrite Incl_Rn0. rewrite flowint_comp_fp. done.
          by rewrite <-Incl_Rn0. }   
        assert (n ∉ domm Rz) as n_notin_Rz.
        { rewrite Incl_Rn0 in Valid_R0 *; intros Valid_Rn0'.
          apply intComposable_valid in Valid_Rn0'.
          unfold intComposable in Valid_Rn0'.
          destruct Valid_Rn0' as [_ [_ [H' _]]].
          rewrite Domm_Rn0 in H'. clear -H'; set_solver. }
        assert (m ∉ domm Rz) as m_notin_Rz.
        { clear -Domm_Rnz m_notin_R0. set_solver. }               

        iMod (own_updateP (flowint_update_P (_) R0 Rn0 (Rn0 ⋅ Rm0)) γ_R
                   (● R0 ⋅ ◯ (Rn0)) with "[HR HnR]") as (Ro) "H'".
        { rewrite Incl_Rn0. apply flowint_update. 
          split; last split.
          - unfold contextualLeq.
            repeat split; try done.
            + rewrite flowint_comp_fp; try done.
              clear; set_solver.
            + intros n' H'.
              assert (n' = n) as Hn.
              { rewrite Domm_Rn0 in H'.
                clear -H'; set_solver. }
              subst n'.
              pose proof (intComp_inf_1 Rn0 Rm0 Valid_Rnm0 n H') as H''.
              rewrite H''. subst Rm0; unfold out; simpl.
              rewrite nzmap_lookup_empty.
              by rewrite ccm_pinv_unit. 
            + intros n' H'.
              pose proof (intComp_unfold_out Rn0 Rm0 Valid_Rnm0 n' H') as H''.
              rewrite H''. unfold out at 3, out_map. subst Rm0.
              simpl. rewrite nzmap_lookup_empty.
              by rewrite ccm_right_id.
          - rewrite Domm_Rnm0. clear -n_notin_Rz m_notin_Rz.
            set_solver.
          - intros n' Hn'. rewrite Domm_Rnm0 Domm_Rn0 in Hn'.
            assert (n' = m) as H'. clear -Hn'. set_solver.
            subst n'. by unfold out in Out_Rz_m. }              
        { rewrite own_op. iFrame. }                        
        iPoseProof ((flowint_update_result' γ_R R0 Rn0 (Rn0 ⋅ Rm0))
                        with "H'") as (R0') "(% & % & (HR & HRn))".
        rename H into ContLeq_R0. clear Ro. 
        destruct H1 as [Ro [HR0 HR0']].
        iEval (rewrite auth_frag_op) in "HRn".
        iDestruct "HRn" as "(HRn & HRm)".
        iPoseProof (own_valid with "HR") as "%".
        rename H into Valid_R0'.
        rewrite auth_auth_valid in Valid_R0' *; intros Valid_R0'. 

        assert (domm R0' = domm R0 ∪ {[m]}) as Domm_R0'.
        { rewrite Incl_Rn0 in HR0*; intros H'.
          apply intComp_cancelable in H'. 
          rewrite HR0'. repeat rewrite flowint_comp_fp.
          rewrite Domm_Rm0 H'. clear; set_solver.
          rewrite Incl_Rn0 in Valid_R0 *; intros H''.
          done. done. apply leibniz_equiv_iff in HR0'. 
          by rewrite <-HR0'. by rewrite <-Incl_Rn0. }
        assert (domm R0' ∖ {[m]} = domm R0) as Domm_R0_m.
        { clear -Domm_R0' m_notin_R0. set_solver. }
        iDestruct "Inf_R" as %Inf_R.  
        iAssert (⌜inflow_R R0' r⌝)%I as "Inf_R'".
        { iPureIntro. unfold inflow_R. intros n' k.
          destruct (n' =? r) eqn: Hn'.
          + pose proof Inf_R n' k as Inf_R.
            rewrite Hn' in Inf_R.
            rewrite Nat.eqb_eq in Hn'*; intros Hn'.
            subst n'. unfold contextualLeq in ContLeq_R0.
            destruct ContLeq_R0 as [_ [_ [_ [H' _]]]].
            pose proof H' r r_in_R0 as H'.
            unfold in_inset. unfold in_inset in Inf_R.
            by rewrite <-H'. 
          + pose proof Inf_R n' k as Inf_R.
            rewrite Hn' in Inf_R.
            rewrite Nat.eqb_neq in Hn'*; intros Hn'.
            unfold contextualLeq in ContLeq_R0.
            destruct ContLeq_R0 as [_ [_ [_ [H' H'']]]].
            destruct (decide (n' ∈ domm R0)).
            * pose proof H' n' e as H'.
              unfold in_inset. unfold in_inset in Inf_R.
              by rewrite <-H'.
            * destruct (decide (n' = m)).
              ** subst n'.
                 pose proof (intComp_inf_2 R0 Rm0) as Hinf.
                 rewrite cmra_comm in HR0' *; intros HR0'.
                 rewrite cmra_assoc in HR0' *; intros HR0'.
                 rewrite cmra_comm in HR0 *; intros HR0.
                 rewrite <-HR0 in HR0'.
                 rewrite HR0' in Valid_R0'.
                 assert (m ∈ domm Rm0) as m_in_Rm0.
                 { rewrite Domm_Rm0. clear; set_solver. }
                 pose proof Hinf Valid_R0' m m_in_Rm0 as Hinf.
                 apply leibniz_equiv_iff in HR0'. 
                 rewrite <-HR0' in Hinf.
                 unfold in_inset. rewrite Hinf.
                 unfold outflow_zero_R in Out_R.
                 unfold out. rewrite Out_R.
                 rewrite nzmap_lookup_empty.
                 subst Rm0. unfold inf. simpl.
                 rewrite lookup_singleton.
                 simpl. rewrite ccm_pinv_unit.
                 clear. unfold dom_ms, dom, nzmap_dom.
                 set_solver.
              ** assert (n' ∉ domm R0') as Hdom.
                 { rewrite Domm_R0'.
                   clear -n0 n1. set_solver. }
                 unfold domm, dom, flowint_dom in Hdom.
                 destruct R0' as [ [Rinf Rout] | ]; last by contradiction.
                 simpl in Hdom. rewrite not_elem_of_dom in Hdom *; intros Hdom.
                 unfold in_inset. unfold inf, inf_map.
                 simpl. rewrite Hdom. simpl.
                 unfold ccmunit, ccm_unit, lift_unit.
                 unfold dom_ms, dom, flowint_dom, nzmap_dom.
                 unfold nzmap_unit. simpl. clear; set_solver. }

        iMod (own_update γ_f (● domm I0) (● (domm I0 ∪ {[m]}) ⋅ ◯ ({[m]}))
                         with "[Hf]") as "(Hf & H')"; try done.
        { apply (auth_update_alloc (domm I0) (domm I0 ∪ {[m]}) ({[m]})).
          apply local_update_discrete.
          intros mz _ Hmz. split; try done.
          rewrite gset_opM in Hmz. rewrite gset_opM.
          rewrite Hmz. clear. set_solver. }
        iEval (rewrite <-Domm_I0') in "Hf".
        iAssert (inFP γ_f m) with "H'" as "#FP_m".
        iDestruct "H'" as "HnS_FPm".
        
        iMod (own_alloc (to_frac_agree (1) (esm0))) 
              as (γ_em)"Hesm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hesm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hesm_f". 
        iDestruct "Hesm_f" as "(HnS_esm & HnP_esm)".        

        iMod (own_alloc (to_frac_agree (1) (Cm0))) 
              as (γ_cm)"Hcm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hcm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hcm_f". 
        iDestruct "Hcm_f" as "(HnS_cm & HnP_cm)".        

        iMod (own_alloc (to_frac_agree (1) (Bm0))) 
              as (γ_bm)"Hbm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hbm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hbm_f". 
        iDestruct "Hbm_f" as "(HnS_bm & HnP_bm)".        

        iMod (own_alloc (to_frac_agree (1) (Qm0))) 
              as (γ_qm)"Hqm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hqm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hqm_f". 
        iDestruct "Hqm_f" as "(HnS_qm & HnP_qm)".
        
        iAssert (frac_ghost_state γ_em γ_cm γ_bm γ_qm esm0 Cm0 Bm0 Qm0
                ∗ frac_ghost_state γ_em γ_cm γ_bm γ_qm esm0 Cm0 Bm0 Qm0)%I
                with "[HnS_esm HnP_esm HnS_cm HnP_cm HnS_bm HnP_bm HnS_qm HnP_qm]"
                as "(HnS_fracm & HnP_fracm)".
        { iFrame. }               

        iMod (own_alloc_set KS with "[]") as "HnS_starm"; first done.
        iDestruct "HnS_starm" as (γ_cirm)"HnS_starm".
        
        iDestruct "domm_IR" as "#domm_IR".
        iDestruct "domm_Iγ" as "#domm_Iγ".
        iMod ((ghost_heap_update γ_gh hγ0 m γ_em γ_cm γ_bm γ_qm γ_cirm) 
                    with "[] [$Hγ]") as "(Hγ & #HnS_ghm)".
        { iDestruct "domm_Iγ" as %H'. iPureIntro.
          rewrite <-H'. apply m_notin_I0. }            

        assert (set_of_map Cm0 = ∅) as Set_of_Cm0.
        { unfold set_of_map. subst Cm0.
          by rewrite map_fold_empty. }
        iMod (own_update γ_s (● H0) (● H0 ⋅ ◯ (set_of_map Cm0))
                 with "[$HH]") as "HH".
        { apply (auth_update_alloc _ (H0) (set_of_map Cm0)).
          rewrite Set_of_Cm0.
          apply local_update_discrete. intros mz Valid_H1 H1_eq.
          split; try done. }
        iDestruct "HH" as "(HH & HnP_Cm)".

        iAssert (⌜history_init H0⌝)%I as "%".
        { by iDestruct "Hist" as "%". }
        rename H into Hist.
        
        iAssert (closed γ_f esm0) as "HnS_clm".
        { iIntros (n')"%". rename H into H'.
          exfalso. rewrite Hesm in H'.
          rewrite /(∅ !!! n') in H'.
          unfold finmap_lookup_total in H'.
          rewrite lookup_empty in H'.
          simpl in H'. clear -H'; done. }

        set (Sr := KS ∩ (esn' !!! m ∩ inset K Rn0 n)).
        set (Sr_map := map_restriction Sr ∅).
        set (Sr_mset := map_subset Sr ∅).
        set (Sb := KS ∩ (Sr ∖ dom (gset K) Cn)).
        set (Sb_map := map_restriction Sb ∅). 
        set (Qn0' := gmap_insert_map Qn Sr_map).
        set (Bn0' := gmap_insert_map Bn Sb_map).
        set (In0' := outflow_insert_set_KT In0 m Sr_mset).
        set (Im0' := inflow_insert_set_KT Im0 m Sr_mset). 
        set (Rn0' := outflow_insert_set_K Rn0 m Sr).
        set (Rm0' := inflow_insert_set_K Rm0 m Sr).


        iMod ((frac_update γ_en γ_cn γ_bn γ_qn esn Cn Bn Qn esn' Cn Bn0' Qn0') 
             with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".

        iPoseProof ((node_edgeset_disjoint r n) with "[$node_n]") as "%".
        rename H into Disj_esn'.                        

        iAssert (closed γ_f esn')%I with "[HnS_cl]" as "HnS_cl".
        { unfold closed. iIntros (n')"%". rename H into Hn'.
          destruct (decide (n' = m)).
          + subst n'; try done.
          + rewrite Hesn' in Hn'.
            rewrite lookup_total_insert_ne in Hn'; try done.
            iApply "HnS_cl". by iPureIntro. }


        assert (∀ k, k ∈ Sr → (∀ n', k ∉ esn !!! n')) as Esn_not.
        { intros k Hk. subst Sr. 
          rewrite !elem_of_intersection in Hk*; intros Hk.
          destruct Hk as [_ [Hk _]].
          intros n'. destruct (decide (k ∈ esn !!! n')); try done.
          destruct (decide (n' = m)).
          - subst n'. clear -e Esn_empty. set_solver.
          - assert (k ∈ esn' !!! n') as H'. 
            rewrite Hesn'. rewrite lookup_total_insert_ne; try done.
            pose proof Disj_esn' n' m n0 as H''.
            clear -H'' H' Hk. set_solver.  } 

        iAssert (⌜φ0 esn Qn⌝)%I as "%".
        { by iDestruct "Hφ" as "(%&_)". }
        rename H into Hφ0.

        iAssert (⌜∀ k, k ∈ Sb → Bn !!! k = 0⌝)%I as %HSb.
        { iDestruct "Hφ" as "(_&%&_)". rename H into Hφ1.
          iPureIntro. intros k Hk. subst Sb. 
          rewrite elem_of_intersection in Hk *; intros Hk.
          destruct Hk as [_ Hk].
          rewrite elem_of_difference in Hk *; intros Hk.
          destruct Hk as [Hk1 Hk2].
          rewrite not_elem_of_dom in Hk2*; intros Hk2.
          pose proof (Esn_not k Hk1) as Hk'.
          subst Sr.  rewrite elem_of_intersection in Hk1*; intros Hk1.
          destruct Hk1 as [H' H'']. apply Hφ1 in Hk2.
          apply Hφ0 in Hk'. rewrite lookup_total_alt.
          rewrite Hk2 Hk'; by simpl. try done. }

        assert (dom (gset K) Sb_map = Sb) as Domm_Sbmap.
        { subst Sb_map. by rewrite map_restriction_dom. }

        iAssert (⌜∀ k, Bn !!! k ≤ Bn0' !!! k⌝)%I as "%".
        { iPureIntro. intros k.
          destruct (decide (k ∈ Sb)).
          - rewrite HSb; try done. lia. 
          - subst Bn0'. rewrite !lookup_total_alt. 
            rewrite gmap_lookup_insert_map_ne. done.
            by rewrite Domm_Sbmap.  }
        rename H into Bn_le_Bn0'.

        iAssert (|==> [∗ set] k ∈ KS, own (γ_cirn !!! k)
                                (● {| max_nat_car := Bn0' !!! k |}))%I
                      with "[HnS_star]" as ">HnS_star".
        { admit. }
(*
        { iInduction KS as [| s S' H'] "IHs" using set_ind_L.
          - iModIntro; try done.
          - rewrite (big_sepS_delete _ ({[s]} ∪ S') s); last first.
            clear; set_solver.
            iDestruct "HnS_star" as "(Hs & HnS_star')".
            iMod (own_update (γ_cirn !!! s) (● (MaxNat (Bn !!! s))) 
                    (● (MaxNat (Bn0' !!! s))) with "Hs") as "Hs".
            { apply (auth_update_auth _ _ (MaxNat (Bn0' !!! s))).
              apply max_nat_local_update. simpl. 
              destruct (decide (s ∈ Sb)).
              - rewrite HSb; try done. lia. 
              - subst Bn0'. rewrite !lookup_total_alt. 
                rewrite gmap_lookup_insert_map_ne. done.
                by rewrite Domm_Sbmap.  }
            assert (({[s]} ∪ S') ∖ {[s]} = S') as HS.
            { clear -H; set_solver. } rewrite HS. 
            rewrite (big_sepS_delete _ ({[s]} ∪ S') s); last first.
            clear; set_solver. iSplitL "Hs". iModIntro; iFrame "Hs".
            rewrite HS. iMod ("IHs" with "HnS_star'") as "H'". 
             iModIntro; iFrame. }
*)


        iAssert (own γ_R (◯ Rn0') ∗ own γ_R (◯ Rm0'))%I 
                with "[HRn HRm]" as "(HRn & HRm)".
        { iCombine "HRn HRm" as "HRnm".
          assert (Rn0' = outflow_insert_set_K Rn0 m Sr) 
                  as HRn0'. done.
          assert (Rm0' = inflow_insert_set_K Rm0 m Sr)
                  as HRm0'. done.         
          pose proof (flowint_insert_set_eq_K Rn0 Rn0' Rm0 Rm0' 
                  m Sr HRn0' HRm0') as HRnm0'.
          iEval (rewrite HRnm0') in "HRnm".
          iEval (rewrite auth_frag_op) in "HRnm".
          iDestruct "HRnm" as "(?&?)". iFrame. }

        iAssert (own γ_I (◯ In0') ∗ own γ_I (◯ Im0'))%I 
                with "[HIn HIm]" as "(HIn & HIm)".
        { iCombine "HIn HIm" as "HInm".
          assert (In0' = outflow_insert_set_K In0 m Sr_mset) 
                  as HIn0'. done.
          assert (Im0' = inflow_insert_set_K Im0 m Sr_mset)
                  as HIm0'. done.         
          pose proof (flowint_insert_set_eq_KT In0 In0' Im0 Im0' 
                  m Sr_mset HIn0' HIm0') as HInm0'.
          iEval (rewrite HInm0') in "HInm".
          iEval (rewrite auth_frag_op) in "HInm".
          iDestruct "HInm" as "(?&?)". iFrame. }

        assert (domm Rm0' = {[m]}) as Domm_Rm0'.
        { pose proof (flowint_inflow_insert_set_dom_K Rm0 m Sr Rm0') as H'.
          subst Rm0'. rewrite H'. clear -Domm_Rm0; set_solver.
          done. }         

        assert (domm Im0' = {[m]}) as Domm_Im0'.
        { pose proof (flowint_inflow_insert_set_dom_KT Im0 m Sr_mset Im0') as H'.
          subst Im0'. rewrite H'. clear -Domm_Im0; set_solver.
          done. }         




        
        assert (dom (gset K) Sr_map = Sr) as Domm_Srmap.
        { subst Sr_map. by rewrite map_restriction_dom. }


        assert (∀ k, k ∈ Sr → Qn0' !! k = Some 0) as Lookup_Qn0'.
        { intros k Hk. subst Qn0'. rewrite gmap_lookup_insert_map.
          subst Sr_map. rewrite lookup_map_restriction; try done.
          by rewrite Domm_Srmap. }

        assert (∀ k, k ∉ Sr → Qn0' !! k = Qn !! k) as Lookup_Qn0'_ne.
        { intros k Hk. subst Qn0'. 
          rewrite gmap_lookup_insert_map_ne; try done.
          by rewrite Domm_Srmap. }

        assert (∀ k, k ∈ Sb → Bn0' !! k = Some 0) as Lookup_Bn0'.
        { intros k Hk. subst Bn0'. rewrite gmap_lookup_insert_map.
          subst Sb_map. rewrite lookup_map_restriction; try done.
          by rewrite Domm_Sbmap. }

        assert (∀ k, k ∉ Sb → Bn0' !! k = Bn !! k) as Lookup_Bn0'_ne.
        { intros k Hk. subst Bn0'. 
          rewrite gmap_lookup_insert_map_ne; try done.
          by rewrite Domm_Sbmap. }
        
        assert (∀ k t, (k, t) ∈ Sr_mset ↔ k ∈ Sr ∧ t = 0) as HSr_mset.
        { intros k t. subst Sr_mset. apply map_subset_member. } 





        iDestruct "HnS_oc" as "(%&%&%)".
        rename H into OC1. rename H1 into OC2. rename H2 into OC3.

        iAssert (outflow_constraints n In0' Rn0' esn' Qn0')%I as "HnS_oc".
        { iPureIntro. split; last split; try done.
          - intros n' k t. destruct (decide (n' = m)).
            + subst n'. assert (outset_KT In0' m = Sr_mset) as Hout.
              { assert (outset_KT In0 m = ∅).
                { unfold outset_KT. rewrite Out_In_m. 
                  unfold ccmunit, ccm_unit. unfold lift_unit.
                  unfold nzmap_unit. unfold KT_flows.dom_ms, dom, nzmap_dom.
                  simpl. apply leibniz_equiv. by rewrite dom_empty. }
                assert (In0' = outflow_insert_set_KT In0 m Sr_mset) as H' by done.  
                pose proof (outflow_insert_set_outset_KT In0 m Sr_mset In0' H').
                rewrite H in H1. clear -H1; set_solver. }
              rewrite Hout. split.
              * intros H'. apply HSr_mset in H'. 
                destruct H' as [H1' H2'].
                split. subst Sr. clear -H1'. set_solver.
                rewrite (Lookup_Qn0' k H1').
                by rewrite H2'.
              * intros [Hkt1 Hkt2].
                destruct (decide (k ∈ Sr)).
                ** rewrite (Lookup_Qn0' k e) in Hkt2.
                   inversion Hkt2. rewrite HSr_mset.
                   split; try done. 
                ** assert (∀ n', k ∉ esn !!! n') as Hnot.
                   { intros n'. destruct (decide (n' = m)).
                     subst n'. rewrite Esn_empty. clear; set_solver.
                     destruct (decide (k ∈ esn !!! n')); try done.
                     assert (k ∈ esn' !!! n') as H'. rewrite Hesn'. 
                     rewrite lookup_total_insert_ne; try done.
                     pose proof Disj_esn' n' m n1 as Disj_esn'.
                     clear -Disj_esn' Hkt1 H'. set_solver. }
                   rewrite (Lookup_Qn0'_ne k n0) in Hkt2.   
                   pose proof Hφ0 k Hnot as H'. rewrite H' in Hkt2.
                   done.
            + rewrite Hesn'. rewrite lookup_total_insert_ne; try done.
              assert (outset_KT In0' n' = outset_KT In0 n') as Hout.
              { assert (In0' = outflow_insert_set_KT In0 m Sr_mset) as H' by done.  
                by pose proof (outflow_insert_set_outset_ne_KT In0 m 
                                                Sr_mset In0' n' n0 H'). }
                rewrite Hout. split.
              * destruct (decide (k ∈ Sr)).
                ** intros H'. apply OC1 in H'.
                   destruct H' as [H' _].
                   pose proof Esn_not k e n' as H''.
                   clear -H' H''. set_solver.
                ** rewrite (Lookup_Qn0'_ne k n1). apply OC1.   
              * intros [Hkt1 Hkt2]. destruct (decide (k ∈ Sr)).
                ** pose proof Esn_not k e n' as H''.
                   clear -Hkt1 H''. set_solver.
                ** rewrite (Lookup_Qn0'_ne k n1) in Hkt2.
                   apply OC1; try done.   
          - intros n' k. assert (inset K Rn0' n = inset K Rn0 n) as Hin.
            { try done. } rewrite Hin. destruct (decide (n' = m)).
            + subst n'. assert (outset K Rn0' m = Sr) as Hout.
              { assert (outset K Rn0 m = ∅).
                { unfold outset. rewrite Out_Rn_m. 
                  unfold ccmunit, ccm_unit. unfold lift_unit.
                  unfold nzmap_unit. unfold dom_ms, dom, nzmap_dom.
                  simpl. apply leibniz_equiv. by rewrite dom_empty. }  
                assert (Rn0' = outflow_insert_set_K Rn0 m Sr) as H' by done.  
                pose proof (outflow_insert_set_outset_K Rn0 m Sr Rn0' H').
                rewrite H in H1. clear -H1; set_solver. } rewrite Hout. 
              subst Sr.  rewrite !elem_of_intersection.
              split; try done. admit. admit.
            + assert (outset K Rn0' n' = outset K Rn0 n') as Hout.
              { assert (Rn0' = outflow_insert_set_K Rn0 m Sr) as H' by done.  
                by pose proof (outflow_insert_set_outset_ne_K Rn0 m Sr 
                          Rn0' n' n0 H'). } rewrite Hout. rewrite Hesn'. 
              rewrite lookup_total_insert_ne; try done.
          - intros n' kt. destruct (decide (n' = m)).
            + subst n'. subst In0'.
              destruct (decide (kt ∈ Sr_mset)).
              * unfold out, out_map. unfold outflow_insert_set_KT.
                simpl. rewrite nzmap_lookup_total_insert.
                rewrite nzmap_lookup_total_increment_set.
                rewrite Out_In_m. unfold ccmunit, ccm_unit.
                simpl. unfold lift_unit. rewrite nzmap_lookup_empty.
                unfold ccmunit, ccm_unit. simpl. lia. done.
              * unfold out, out_map. unfold outflow_insert_set_KT.
                simpl. rewrite nzmap_lookup_total_insert.
                rewrite nzmap_lookup_total_increment_set_ne.
                rewrite Out_In_m. unfold ccmunit, ccm_unit.
                simpl. unfold lift_unit. rewrite nzmap_lookup_empty.
                unfold ccmunit, ccm_unit. simpl. unfold nat_unit. lia. done.
            + subst In0'. unfold outflow_insert_set_KT.
              unfold out at 1, out_map at 1; simpl.
              rewrite nzmap_lookup_total_insert_ne; try done.
              pose proof OC3 n' kt as H'. by unfold out in H'.  }
       
        iAssert (outflow_constraints m Im0' Rm0' esm0 Qm0)%I as "HnS_ocm".
        { iPureIntro. split; last split.
          - split.
            + unfold outset_KT, KT_flows.dom_ms. 
              rewrite nzmap_elem_of_dom_total. unfold out, out_map. 
              subst Im0. simpl. rewrite nzmap_lookup_empty. 
              unfold ccmunit, ccm_unit. simpl.
              unfold lift_unit.
              rewrite nzmap_lookup_empty.
              unfold ccmunit, ccm_unit. simpl. done.
            + subst esm0. rewrite /(∅ !!! n'). 
              unfold finmap_lookup_total. rewrite lookup_empty.
              simpl. clear; set_solver.
          - unfold outflow_constraint_R. 
            intros n' k. unfold outset.
            assert (out Rm0' n' = out Rm0 n') as Hout.
            { assert (Rm0' = inflow_insert_set_K Rm0 m Sr) as H' by done.  
              by pose proof (inflow_insert_set_out_eq_K Rm0 m Sr Rm0' n' H'). }
            rewrite Hout. split.
            + unfold in_outset, dom_ms. 
              rewrite nzmap_elem_of_dom_total. unfold out, out_map. 
              subst Rm0. simpl. rewrite nzmap_lookup_empty. 
              unfold ccmunit, ccm_unit. simpl.
              unfold lift_unit.
              rewrite nzmap_lookup_empty.
              unfold ccmunit, ccm_unit. simpl. done.
            + subst esm0. rewrite /(∅ !!! n'). 
              unfold finmap_lookup_total. rewrite lookup_empty.
              simpl. clear; set_solver.
          - intros n' kt. unfold out, out_map; subst Im0; simpl.
            rewrite nzmap_lookup_empty. unfold ccmunit, ccm_unit.
            simpl. unfold lift_unit. rewrite nzmap_lookup_empty.
            unfold ccmunit, ccm_unit; simpl. unfold nat_unit. lia. }

        iAssert (⌜φ0 esn' Qn0'⌝ ∗ ⌜φ1 Bn0' Cn Qn0'⌝ ∗ ⌜φ2 n Bn0' In0'⌝ 
           ∗ ⌜φ3 n Bn0' Rn0'⌝ ∗ ⌜φ4 n Rn0'⌝ ∗ ⌜φ5 Bn0' Qn0'⌝ 
           ∗ ⌜φ6 Bn0' T0'⌝ ∗ ⌜φ7 n esn' Rn0' Qn0'⌝)%I 
                with "[Hφ]" as "Hφ".
        { iDestruct "Hφ" as "(%&%&%&%&%&%&%&%)".         
          clear H. rename H1 into Hφ1. 
          rename H2 into Hφ2. rename H3 into Hφ3.
          rename H4 into Hφ4. rename H5 into Hφ5.
          rename H6 into Hφ6. rename H7 into Hφ7.
          iPureIntro. split; last split; last split; 
          last split; last split; last split; last split.
          - intros k Hnot. destruct (decide (k ∈ Sr)). 
            + subst Sr. rewrite !elem_of_intersection in e*; intros e. 
              destruct e as [_ [e _]]. pose proof Hnot m as Hnot. 
              clear -Hnot e. set_solver.  
            + rewrite (Lookup_Qn0'_ne k n0). apply Hφ0. 
              intros n'. destruct (decide (n' = m)).
              * subst n'. rewrite Esn_empty.
                clear; set_solver.
              * pose proof Hnot n' as Hnot.
                rewrite Hesn' in Hnot.
                rewrite lookup_total_insert_ne in Hnot; try done.
          - intros k t. destruct (decide (k ∈ Sr)).
            + split.
              * intros HCn.
                assert (is_Some(Cn !! k)). by exists t; try done.
                rewrite <-elem_of_dom in H.
                assert (k ∉ Sb) as Hk.
                { destruct (decide (k ∈ Sb)); try done.
                  subst Sb. rewrite elem_of_intersection in e0*; intros e0.
                  destruct e0 as [_ e0].
                  clear -e0 H. set_solver. }
                rewrite (Lookup_Bn0'_ne k Hk).
                by apply Hφ1.
              * assert (k ∈ Sb) as Hk.
                { admit. }
                rewrite (Lookup_Bn0' k Hk).
                rewrite (Lookup_Qn0' k e).
                done.
            + assert (k ∉ Sb) as Hk.
              { destruct (decide (k ∈ Sb)); try done.
                subst Sb. rewrite elem_of_intersection in e*; intros e.
                destruct e as [_ e]. clear -e n0. set_solver. }
              rewrite (Lookup_Bn0'_ne k Hk).
              rewrite (Lookup_Qn0'_ne k n0).
              apply Hφ1.
          - intros k t. assert (inset_KT In0' n = inset_KT In0 n) as Hin. 
            { assert (In0' = outflow_insert_set_KT In0 m Sr_mset) by done.
              by pose proof (outflow_insert_set_inset_KT In0 m Sr_mset In0' n H). }
            rewrite Hin. destruct (decide (k ∈ Sb)). 
            + intros H'. apply Hφ2 in H'. rewrite lookup_total_alt.
              rewrite (Lookup_Bn0' k e). simpl.
              by rewrite (HSb k e) in H'.
            + rewrite lookup_total_alt. rewrite (Lookup_Bn0'_ne k n0).
              rewrite <-lookup_total_alt. apply Hφ2.
          - intros k. assert (inset K Rn0' n = inset K Rn0 n) as Hin.
            { assert (Rn0' = outflow_insert_set_K Rn0 m Sr) by done.
              by pose proof (outflow_insert_set_inset_K Rn0 m Sr Rn0' n H). }
            rewrite Hin.
            destruct (decide (k ∈ Sb)).
            + right. subst Sb. subst Sr. clear -e. set_solver.
            + by rewrite (Lookup_Bn0'_ne k n0).
          - try done.
          - intros k. destruct (decide (k ∈ Sb)).
            + destruct (decide (k ∈ Sr)).
              * rewrite !lookup_total_alt. 
                rewrite (Lookup_Bn0' k e).
                rewrite (Lookup_Qn0' k e0).
                by simpl.
              * subst Sb Sr; clear -e n0; set_solver.
            + destruct (decide (k ∈ Sr)).
              * rewrite lookup_total_alt.
                rewrite (Lookup_Qn0' k e).
                simpl. lia.
              * rewrite !lookup_total_alt. 
                rewrite (Lookup_Bn0'_ne k n0).
                rewrite (Lookup_Qn0'_ne k n1).
                rewrite <-!lookup_total_alt.
                by apply Hφ5.
          - intros k. rewrite lookup_total_alt. 
            destruct (decide (k ∈ Sb)).
            * rewrite (Lookup_Bn0' k e). simpl. lia.
            * rewrite (Lookup_Bn0'_ne k n0).
              by rewrite <-lookup_total_alt.
          - intros k. intros [H' H''].
            destruct H' as [n' H'].
            destruct (decide (n' = m)).
            + subst n'. rewrite elem_of_dom. 
              assert (k ∈ Sr).
              { subst Sr. admit. }
              rewrite (Lookup_Qn0' k H).
              by exists 0.
            + assert (inset K Rn0' n = inset K Rn0 n) as Hin.
              { admit. } rewrite Hesn' in H'.
              rewrite lookup_total_insert_ne in H'; try done.
              destruct (decide (k ∈ Sr)).
              * pose proof Lookup_Qn0' k e as H'''.
                rewrite elem_of_dom. rewrite H'''.
                by exists 0.
              * rewrite elem_of_dom. rewrite (Lookup_Qn0'_ne k n1).
                rewrite <-elem_of_dom. apply Hφ7.
                split; try done. by exists n'. }
      
        iAssert (⌜φ0 esm0 Qm0⌝ ∗ ⌜φ1 Bm0 Cm0 Qm0⌝ ∗ ⌜φ2 m Bm0 Im0'⌝ 
              ∗ ⌜φ3 m Bm0 Rm0'⌝ ∗ ⌜φ4 m Rm0'⌝ ∗ ⌜φ5 Bm0 Qm0⌝  
              ∗ ⌜φ6 Bm0 T0'⌝ ∗ ⌜φ7 m esm0 Rm0' Qm0⌝)%I
                 as "Hφm".
        { iPureIntro. subst esm0 Cm0 Bm0 Qm0.
          repeat split; try done.
          - unfold φ2.
            assert (inset_KT Im0' m = Sr_mset) as Hin.
            { admit. } rewrite Hin. intros k t Hkt.
            apply HSr_mset in Hkt.
            destruct Hkt as [_ H'].
            rewrite lookup_total_alt; rewrite lookup_empty; by simpl.
          - unfold φ3. intros k; left.
            rewrite /(∅ !!! k). unfold finmap_lookup_total.
            rewrite lookup_empty. by simpl.
          - unfold φ4. intros k.
            subst Rm0; unfold inf, inf_map; simpl.
            rewrite lookup_insert. simpl.
            unfold inf, inf_map; simpl.
            rewrite lookup_insert. simpl.
            destruct (decide (k ∈ Sr)). 
            + admit.
            + admit.
          - intros k. rewrite /(∅ !!! k).
            unfold finmap_lookup_total.
            rewrite lookup_empty. by simpl.  
          - unfold φ6. intros k. rewrite /(∅ !!! k). 
            unfold finmap_lookup_total. rewrite lookup_empty.
            simpl. lia.
          - intros k [Hkt1 Hkt2].
            destruct Hkt1 as [n' H'].
            clear -H'. set_solver.   }

        iAssert (⌜outflow_zero I0'⌝)%I as "Out_I'".
        { iPureIntro. unfold outflow_zero.
          apply nzmap_eq. intros n'.
          destruct (decide (n' ∈ domm I0')).
          + pose proof intValid_in_dom_not_out I0' n' Valid_I0' e as H'.
            unfold out in H'. rewrite H'.
            by rewrite nzmap_lookup_empty.
          + destruct ContLeq_I0 as [_ [_ [_ [H' H'']]]].
            pose proof H'' n' n0 as H''.
            unfold out in H''. rewrite <-H''.
            apply leibniz_equiv in Out_I.
            rewrite nzmap_eq in Out_I *; intros Out_I.
            pose proof Out_I n' as Out_I.
            by rewrite Out_I. }  

        iAssert (⌜outflow_zero_R R0'⌝)%I as "Out_R'".
        { iPureIntro. unfold outflow_zero.
          apply nzmap_eq. intros n'.
          destruct (decide (n' ∈ domm R0')).
          + pose proof intValid_in_dom_not_out R0' n' Valid_R0' e as H'.
            unfold out in H'. rewrite H'.
            by rewrite nzmap_lookup_empty.
          + destruct ContLeq_R0 as [_ [_ [_ [H' H'']]]].
            pose proof H'' n' n0 as H''.
            unfold out in H''. rewrite <-H''.
            apply leibniz_equiv in Out_R.
            rewrite nzmap_eq in Out_R *; intros Out_R.
            pose proof Out_R n' as Out_R.
            by rewrite Out_R. }  

        iAssert (⌜bn = true⌝)%I as "%".
        { destruct bn; try done.
          iDestruct "Hlif_n" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r n) with "[$]") as "%".
          contradiction. } subst bn.


        iModIntro. iSplitR "AU node_n HnP_gh HnP_frac HnP_C HnP_t".
        { iNext. iExists T0', H0,
               (<[m:=ghost_loc γ_em γ_cm γ_bm γ_qm γ_cirm]> hγ0), I0', R0'.
          iSplitL "MCS_auth Hist Ht FP_r Max_ts HI HR Hf Hγ HH Out_I' Out_R'".
          { iFrame. iFrame "Inf_R' Out_I' Out_R'". 
            iDestruct "domm_IR" as %H'.
            iDestruct "domm_Iγ" as %H''.
            iPureIntro. split.
            rewrite Domm_I0' Domm_R0'. by rewrite H'.
            apply leibniz_equiv. rewrite dom_insert.
            rewrite Domm_I0' H''. clear; set_solver. }
          rewrite (big_sepS_delete _ (domm I0') m); 
              last first. { rewrite Domm_I0'. clear; set_solver. }
          iSplitR "Hl_n Hlif_n HnS_gh HnS_frac
                      HnS_FP HnS_cl HnS_oc HnS_H HnS_star Hφ Hstar' HIn HRn".
          { iExists false, Cm0, Bm0, Qm0. iFrame "Hl_m".
            iSplitL "node_m HnP_fracm HnP_Cm". 
            iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm0, T.
            iFrame "∗#".
            rewrite <-(PeanoNat.Nat.eqb_neq m r) in m_neq_r.
            by rewrite m_neq_r.
            iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm0, Im0', Rm0'.
            iFrame "∗#". repeat iSplitR; try by iPureIntro.
            rewrite <-(PeanoNat.Nat.eqb_neq m r) in m_neq_r.
            by rewrite m_neq_r.
            iApply (big_sepS_mono 
                    (λ y, own (γ_cirm !!! y) (● {| max_nat_car := 0 |}) )%I
                    (λ y, own (γ_cirm !!! y) (● {| max_nat_car := Bm0 !!! y |}))%I
                    KS); try done. }
            rewrite Domm_I0_m.
            rewrite (big_sepS_delete _ (domm I0) n); 
              last apply n_in_I0.
            iFrame "Hstar'". iExists true, Cn, Bn0', Qn0'.
            iFrame. iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn', In0', Rn0'.
            iFrame "∗#". destruct (n =? r). 
            - iDestruct "HnS_H" as "(%&%)".
              rename H into Bn_eq_H0. rename H1 into Infz_In0. 
              iPureIntro. repeat split; try done.
              apply map_eq. intros k.
              destruct (decide (k ∈ Sb)).
              + rewrite (Lookup_Bn0' k e).
                rewrite map_eq_iff in Bn_eq_H0*; intros Bn_eq_H0.
                pose proof Bn_eq_H0 k as H'. 
                pose proof (HSb k e) as H''.
                subst Sb. rewrite elem_of_intersection in e*; intros e.
                destruct e as [e _].
                pose proof Hist k e as Hist.
                pose proof (map_of_set_lookup_some H0 k 0 Hist) as Hm.
                destruct Hm as [u Hm]. rewrite Hm.
                rewrite lookup_total_alt in H''.
                rewrite H' in H''. rewrite Hm in H''. 
                simpl in H''. by rewrite H''.
              + subst Bn0'. rewrite gmap_lookup_insert_map_ne.
                rewrite map_eq_iff in Bn_eq_H0*; intros Bn_eq_H0.
                by pose proof Bn_eq_H0 k as H'.
                by rewrite Domm_Sbmap.
            - by iPureIntro. }

        iModIntro.
        iClear "Inf_R' domm_IR domm_Iγ HnS_clm HnS_ocm Hφm Out_I' Out_R' HnS_oc".
        clear In0' Im0' Domm_Im0' OC1 OC2 OC3 Hcm Hesm m_notin_I0 
        n_in_I0 In0 Qm0 Bm0 Im0 r_in_I0 Domm_Im0 Domm_Rm0 Valid_I0 Valid_In0
        Valid_Rn0 Domm_In0 Domm_Rn0 Valid_Im0 Valid_Rm0 Iz Incl_In0
        Out_I Out_In_m Out_Iz_m Valid_Inm0 Domm_Inm0 Domm_Inz
        n_notin_Iz m_notin_Iz I0' ContLeq_I0 Io HI0 HI0' Valid_I0'
        Domm_I0' Domm_I0_m r_in_R0 m_notin_R0 n_in_R0 Valid_R0
        Rz Incl_Rn0 Out_R Out_Rn_m Out_Rz_m Valid_Rnm0 Domm_Rnm0
        Domm_Rnz n_notin_Rz  R0' ContLeq_R0 R0 HR0 m_notin_Rz
        HR0' Valid_R0' Domm_R0' Domm_R0_m Inf_R Set_of_Cm0 Hφ0.
        clear Disj_esn esm0 Cm0 T0' hγ0 I0 Ro
        Rn0' Rm0' Domm_Rm0' Domm_Rm0' Esn_empty.
        
        awp_apply lockNode_spec_high without "HnP_t"; try done.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros (Cm Bm Qm)"HnP_m". iModIntro.
        iIntros "HnP_t". wp_pures.
        iDestruct "HnP_m" as (γ_em' γ_cm' γ_bm' γ_qm' γ_cirm' esm Tm)"(node_m   
                            & HnP_ghm & HnP_fracm & HnP_Cm & HnP_tm)".
        iPoseProof (ghost_heap_sync with "[$HnP_ghm] [$HnS_ghm]") 
                                  as "(% & % & % & % & %)".
        subst γ_em'. subst γ_cm'. subst γ_bm'. subst γ_qm'. subst γ_cirm'.
        wp_apply (mergeContents_spec with "[$node_n $node_m]"); try done.
        iIntros (Cn' Cm') "(node_n & node_m & Subset_Cn & Subset_Cm 
                                     & Subset_disj & Cm_sub_Cm' & MergeEq)".  
        iDestruct "Subset_Cn" as %Subset_Cn.
        iDestruct "Subset_Cm" as %Subset_Cm.
        iDestruct "Subset_disj" as %Subset_disj.
        iDestruct "Cm_sub_Cm'" as %Cm_sub_Cm'.
        iDestruct "MergeEq" as %MergeEq. wp_pures.
        iApply fupd_wp. iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rename H1 into n_in_I.  
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn'' Bn'' Qn'')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn''. subst Bn''. subst Qn''.
        iAssert (⌜m ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_m] [$Hf]") as "H'". }
        rename H1 into m_in_I.
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) m); last by set_solver.
        iDestruct "Hstar'" as "(H_m & Hstar')".
        iDestruct "H_m" as (bm Cm'' Bm'' Qm'')"(Hl_m & Hlif_m & HnS_m)".
        iClear "HnS_ghm".
        iDestruct "HnS_m" as (γ_em' γ_cm' γ_bm' γ_qm' γ_cirm' es' Im Rm) 
                      "(HnS_ghm & HnS_fracm & HnS_sim & HnS_FPm 
                                & HnS_clm & HnS_ocm & HnS_Hm & HnS_starm & Hφm)".
        iPoseProof (ghost_heap_sync with "[$HnP_ghm] [$HnS_ghm]") 
                                  as "(% & % & % & % & %)".
        subst γ_em'. subst γ_cm'. subst γ_bm'. subst γ_qm'. subst γ_cirm'.
        iPoseProof (frac_eq with "[$HnP_fracm] [$HnS_fracm]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cm''. subst Bm''. subst Qm''.

        iAssert (⌜bn = true⌝)%I as "%".
        { destruct bn; try done.
          iDestruct "Hlif_n" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r n) with "[$]") as "%".
          contradiction. } subst bn.
                
        iAssert (⌜bm = true⌝)%I as "%".
        { destruct bm; try done.
          iDestruct "Hlif_m" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r m) with "[$]") as "%".
          contradiction. } subst bm.
        
        set (S := dom (gset K) Cn ∖ dom (gset K) Cn').
        set (S_map := map_restriction S Cn).
        set (Qn_old := map_subset S Qn0').
        set (Qn_new := map_subset S Cn).
        set (Qn' := gmap_insert_map Qn0' S_map).
        set (Bm' := gmap_insert_map Bm S_map).
        set (In_temp := outflow_delete_set_KT In m Qn_old).
        set (In' := outflow_insert_set_KT In_temp m Qn_new).
        set (Im_temp := inflow_delete_set_KT Im m Qn_old).
        set (Im' := inflow_insert_set_KT Im_temp m Qn_new).

        iMod ((frac_update γ_en γ_cn γ_bn γ_qn esn' Cn Bn0' Qn0' esn' Cn' Bn0' Qn') 
             with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".

        iMod ((frac_update γ_em γ_cm γ_bm γ_qm esm Cm Bm Qm esm Cm' Bm' Qm) 
             with "[$HnP_fracm $HnS_fracm]") as "(HnP_fracm & HnS_fracm)".

        assert (S ⊆ esn' !!! m) as Sub_S.
        { intros k Hk. destruct (decide (k ∈ esn' !!! m)); try done.
          rewrite map_eq_iff in MergeEq *; intros MergeEq.
          pose proof MergeEq k as MergeEq.
          unfold merge in MergeEq.
          rewrite !gmap_imerge_prf in MergeEq.
          unfold f_merge in MergeEq.
          destruct (decide (Cn !! k ≠ None)) eqn: Hd; 
                        rewrite Hd in MergeEq.
          - destruct (decide (Cn' !! k ≠ None)) eqn: Hd'; 
                          rewrite Hd' in MergeEq.
            + pose proof dom_lookup Cn k n1 as H'.
              pose proof dom_lookup Cn' k n2 as H''.
              clear -H' H'' S Hk. set_solver.
            + destruct (decide (k ∈ esn' !!! m)); try done.
          - destruct (decide (k ∈ esn' !!! m)); try done.
            clear Hd. apply dec_stable in n1. 
            apply not_elem_of_dom in n1. 
            clear -n1 S Hk. set_solver. }


        assert (∀ k t, (k,t) ∈ Qn_new ↔ k ∈ S ∧ t = Cn !!! k) as HQn_new.
        { intros k t. subst Qn_new. apply map_subset_member. } 
        assert (∀ k t, (k,t) ∈ Qn_old ↔ k ∈ S ∧ t = Qn0' !!! k) as HQn_old.
        { intros k t. subst Qn_old. apply map_subset_member. } 
        assert (dom (gset K) S_map = S) as Dom_Smap.
        { subst S_map. apply map_restriction_dom. }

        assert (∀ k, k ∈ S → S_map !! k = Some(Cn !!! k)) as Lookup_Smap.
        { intros k Hk. subst S_map. by rewrite lookup_map_restriction. }
        assert (∀ k, k ∈ S → Qn' !! k = Cn !! k) as Lookup_Qn'.
        { intros k Hk. subst Qn'. rewrite gmap_lookup_insert_map.
          rewrite (Lookup_Smap k Hk).
          assert (k ∈ dom (gset K) Cn) as H'.
          { subst S. clear -Hk; set_solver. }
          rewrite elem_of_dom in H'*; intros H'. destruct H' as [t H'].
          rewrite lookup_total_alt. rewrite H'; by simpl.
          by rewrite Dom_Smap. }
        assert (∀ k, k ∉ S → Qn' !! k = Qn0' !! k) as Lookup_Qn'_ne.
        { intros k Hk. subst Qn'. rewrite gmap_lookup_insert_map_ne.
          done. by rewrite Dom_Smap. }
        assert (∀ k t, k ∉ S → (k,t) ∉ Qn_old) as HQn_old_ne.
        { intros k t Hk. destruct (decide ((k,t) ∈ Qn_old)); try done. 
          rewrite HQn_old in e*; intros e. destruct e as [e _].
          clear -e Hk; set_solver. }
        assert (∀ k t, k ∉ S → (k,t) ∉ Qn_new) as HQn_new_ne.
        { intros k t Hk. destruct (decide ((k,t) ∈ Qn_new)); try done. 
          rewrite HQn_new in e*; intros e. destruct e as [e _].
          clear -e Hk; set_solver. }
        
        assert (∀ k, k ∈ S → Cn !! k = Cm' !! k) as Lookup_merge.
        { intros k Hk. assert (Hes := Hk).
          apply Sub_S in Hes. subst S.
          rewrite elem_of_difference in Hk*; intros Hk.
          destruct Hk as [H' H''].
          rewrite elem_of_dom in H'*; intros H'.
          rewrite not_elem_of_dom in H''*; intros H''.
          destruct H' as [t H'].
          rewrite map_eq_iff in MergeEq*; intros MergeEq.
          pose proof MergeEq k as Hm.
          unfold merge in Hm. rewrite !gmap_imerge_prf in Hm.
          unfold f_merge in Hm. rewrite decide_True in Hm.
          rewrite decide_False in Hm. rewrite decide_True in Hm.
          done. done. rewrite H''. intros ?; contradiction.
          rewrite H'; try done. }
        
        iAssert (⌜∀ k, k ∈ S → k ∈ inset K Rn n⌝)%I as %S_sub_insetn.
        { iDestruct "Hφ" as "(_&%&_&%&_)".
          rename H1 into Hφ1. rename H2 into Hφ3. iPureIntro.
          intros k Hk. subst S. 
          rewrite elem_of_difference in Hk*; intros Hk.
          destruct Hk as [Hk _].
          pose proof Hφ3 k as Hφ3.
          destruct Hφ3 as [H' | H']; try done.
          rewrite elem_of_dom in Hk*; intros Hk.
          destruct Hk as [t Hk]. apply Hφ1 in Hk.
          rewrite H' in Hk. done. }

        iAssert (⌜∀ k, k ∈ S → k ∈ outset K Rn m⌝)%I as %Out_Rn_m.
        { iDestruct "HnS_oc" as "(_&%&_)". rename H1 into OC2.
          iPureIntro; intros k Hk. apply OC2.
          split; try done. by apply Sub_S.
          by apply S_sub_insetn. }
        
        iAssert (⌜∀ k, k ∈ S → k ∈ inset K Rm m⌝)%I as %S_sub_insetm.
        { iDestruct "HnS_si" as "(_&HRn&_&Domm_Rn)".
          iDestruct "HnS_sim" as "(_&HRm&_&Domm_Rm)".
          iCombine "HRn HRm" as "HRnm".
          iPoseProof (own_valid with "[$HRnm]") as "%".
          rename H1 into Valid_Rnm. 
          rewrite auth_frag_valid in Valid_Rnm*; intros Valid_Rnm.
          iDestruct "Domm_Rn" as %Domm_Rn.
          iDestruct "Domm_Rm" as %Domm_Rm. 
          assert (m ∈ domm Rm) as m_in_Rm. 
          clear -Domm_Rm; set_solver. 
          pose proof intComp_unfold_inf_2 Rn Rm Valid_Rnm m m_in_Rm as H'. 
          unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op in H'.
          iPureIntro. rewrite nzmap_eq in H' *; intros H'.
          intros k Hk. pose proof H' k as H'.
          unfold inset. rewrite nzmap_elem_of_dom_total.
          unfold ccmunit, ccm_unit. simpl.
          unfold nat_unit.
          rewrite nzmap_lookup_merge in H'.
          unfold ccmop, ccm_op in H'. simpl in H'.
          unfold nat_op in H'.
          assert (1 ≤ out Rn m !1 k) as Hout.
          { pose proof Out_Rn_m k Hk as H''.
            unfold outset in H''.
            rewrite nzmap_elem_of_dom_total in H'' *; 
            intros H''.
            unfold ccmunit, ccm_unit in H''.
            simpl in H''. unfold nat_unit in H''.
            clear - H''. lia. }
          assert (1 ≤ inf Rm m !1 k) as Hin.
          { clear -H' Hout. 
            assert (∀ (x y z: nat), 1 ≤ y → x = z + y → 1 ≤ x) as H''.
            lia. by pose proof H'' _ _ _ Hout H'. }
          clear -Hin. lia. }

        iAssert (⌜∀ k, k ∈ S → (k, Qn0' !!! k) ∈ outset_KT In m⌝)%I 
                                                as %Out_In_m.
        { iDestruct "HnS_oc" as "(%&_)". 
          iDestruct "Hφ" as "(_&_&_&_&_&_&_&%)". 
          rename H1 into OC1. rename H2 into Hφ7.
          iPureIntro; intros k Hk. apply OC1.
          split; try done. by apply Sub_S.
          pose proof Hφ7 k as H'.
          assert (k ∈ dom (gset K) Qn0') as H''.
          apply H'. split. exists m; by apply Sub_S in Hk.
          by apply S_sub_insetn. 
          rewrite elem_of_dom in H''*; intros H''.
          destruct H'' as [t H''].
          rewrite lookup_total_alt; rewrite H''; by simpl. }


        iAssert (⌜∀ k, k ∈ S → (k, Qn0' !!! k) ∈ inset_KT Im m⌝)%I as %Ins_Im.
        { iDestruct "HnS_si" as "(HIn&_&Domm_In&_)".
          iDestruct "HnS_sim" as "(HIm&_&Domm_Im&_)".
          iCombine "HIn HIm" as "HInm".
          iPoseProof (own_valid with "[$HInm]") as "%".
          rename H1 into Valid_Inm. 
          rewrite auth_frag_valid in Valid_Inm*; intros Valid_Inm.
          iDestruct "Domm_In" as %Domm_In.
          iDestruct "Domm_Im" as %Domm_Im. 
          assert (m ∈ domm Im) as m_in_Im. 
          clear -Domm_Im; set_solver. 
          pose proof intComp_unfold_inf_2 In Im Valid_Inm m m_in_Im as H'. 
          unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op in H'.
          iPureIntro. rewrite nzmap_eq in H' *; intros H'.
          intros k Hk. pose proof H' (k, Qn0' !!! k) as H'.
          unfold inset. rewrite nzmap_elem_of_dom_total.
          unfold ccmunit, ccm_unit. simpl.
          unfold nat_unit.
          rewrite nzmap_lookup_merge in H'.
          unfold ccmop, ccm_op in H'. simpl in H'.
          unfold nat_op in H'.
          assert (1 ≤ out In m !1 (k, Qn0' !!! k)) as Hout.
          { pose proof Out_In_m k Hk as H''.
            unfold outset in H''.
            rewrite nzmap_elem_of_dom_total in H'' *; 
            intros H''.
            unfold ccmunit, ccm_unit in H''.
            simpl in H''. unfold nat_unit in H''.
            clear - H''. lia. }
          assert (1 ≤ inf Im m !1 (k, Qn0' !!! k)) as Hin.
              { clear -H' Hout. 
                assert (∀ (x y z: nat), 1 ≤ y → x = z + y → 1 ≤ x) as H''.
                lia. by pose proof H'' _ _ _ Hout H'. }
              clear -Hin. lia. }

        iAssert (⌜∀ k, k ∈ S → Bm !!! k = Qn0' !!! k⌝)%I as %Bm_eq_Qn.
        { iDestruct "Hφm" as "(_&_&%&_)".
          rename H1 into Hφ2.
          iPureIntro. intros k Hk.
          pose proof Ins_Im k Hk as H'.
          by pose proof Hφ2 k (Qn0' !!! k) H' as H''. }

        iAssert (⌜∀ k, Bm !!! k ≤ Bm' !!! k⌝)%I as "%".
        { iDestruct "Hφ" as "(_&%&_&_&_&%&_)".
          rename H1 into Hφ1. rename H2 into Hφ5.
          iPureIntro. intros k. subst Bm'.
          destruct (decide (k ∈ S)).
          - pose proof Bm_eq_Qn k e as H'.
            rewrite H'. rewrite /(gmap_insert_map Bm S_map !!! k).
            unfold finmap_lookup_total.
            rewrite gmap_lookup_insert_map.
            rewrite (Lookup_Smap k e). simpl.
            subst S. rewrite elem_of_difference in e*; intros e.
            destruct e as [Hc _].
            rewrite elem_of_dom in Hc*; intros Hc.
            destruct Hc as [t Hc].
            pose proof Hφ1 k t as [Hc' _].
            pose proof Hc' Hc.
            rewrite lookup_total_alt.
            rewrite Hc. rewrite <-H1.
            rewrite <-lookup_total_alt.
            apply Hφ5. by rewrite Dom_Smap. 
          - rewrite !lookup_total_alt.
            rewrite gmap_lookup_insert_map_ne.
            done. by rewrite Dom_Smap. }
        rename H1 into Bm_le_Bm'.

        iAssert (|==> [∗ set] k ∈ KS, own (γ_cirm !!! k)
                                (● {| max_nat_car := Bm' !!! k |}))%I
                      with "[HnS_starm]" as ">HnS_starm".
        { admit. }
(*
        { iInduction KS as [| s S' Hs] "IHs" using set_ind_L.
          - iModIntro; try done.
          - rewrite (big_sepS_delete _ ({[s]} ∪ S') s); last first.
            clear; set_solver.
            iDestruct "HnS_starm" as "(Hs & HnS_starm')".
            iMod (own_update (γ_cirm !!! s) (● (MaxNat (Bm !!! s))) 
                    (● (MaxNat (Bm' !!! s))) with "Hs") as "Hs".
            { apply (auth_update_auth _ _ (MaxNat (Bm' !!! s))).
              apply max_nat_local_update. simpl. 
              apply Bm_le_Bm'. }
            assert (({[s]} ∪ S') ∖ {[s]} = S') as HS.
            { clear -H1; set_solver. } rewrite HS. 
            rewrite (big_sepS_delete _ ({[s]} ∪ S') s); last first.
            clear; set_solver. iSplitL "Hs". iModIntro; iFrame "Hs".
            iMod ("IHs" with "HnS_starm'") as "H'". 
            rewrite HS. iModIntro; iFrame. }
*)

        iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".

        iAssert (⌜set_of_map Cn ⊆ H⌝)%I as %Cn_sub_H.
        { iPoseProof ((auth_own_incl γ_s H _) with "[$HH $HnP_C]") as "%".
          rename H1 into H'. by apply gset_included in H'. }

        iAssert (⌜set_of_map Cm ⊆ H⌝)%I as %Cm_sub_H.
        { iPoseProof ((auth_own_incl γ_s H _) with "[$HH $HnP_Cm]") as "%".
          rename H1 into H'. by apply gset_included in H'. }

        iAssert (⌜set_of_map Cn' ⊆ H⌝)%I as %Cn'_sub_H.
        { iPureIntro. clear -Subset_Cn Cn_sub_H.  set_solver. }

        iAssert (⌜set_of_map Cm' ⊆ H⌝)%I as %Cm'_sub_H.
        { iPureIntro. clear -Subset_Cm Cm_sub_H Cn_sub_H.  set_solver. }

        iAssert (⌜∀ k, Cn !!! k ≤ T'⌝)%I as %Cn_le_T'.
        { iDestruct "Max_ts" as %H'. iPureIntro. 
          intros k. destruct (Cn !! k) as [t |] eqn: Hcn.
          - rewrite lookup_total_alt.
            rewrite Hcn; simpl. 
            apply set_of_map_member in Hcn.
            apply Cn_sub_H in Hcn.
            destruct H' as [H' _].
            apply H' in Hcn. clear -Hcn.
            lia.
          - rewrite lookup_total_alt.
            rewrite Hcn; simpl. lia. }
        
        iMod (own_update γ_s (● H) 
             (● H ⋅ ◯ (set_of_map Cn' ⋅ set_of_map Cm')) with "[$HH]") as "HH".
        { apply (auth_update_alloc _ (H) (set_of_map Cn' ⋅ set_of_map Cm')).
          apply local_update_discrete. intros mc Valid_H1 H1_eq.
          split; try done. rewrite /(ε ⋅? mc) in H1_eq.
          destruct mc. rewrite gset_op_union in H1_eq. 
          rewrite left_id in H1_eq *; intros H1_eq.
          rewrite <-H1_eq. 
          rewrite /(set_of_map Cn' ⋅ set_of_map Cm' ⋅? Some H).
          rewrite !gset_op_union.
          clear - Cn'_sub_H Cm'_sub_H. set_solver.
          rewrite /(set_of_map Cn' ⋅ set_of_map Cm' ⋅? None).
          rewrite gset_op_union.
          clear - Cn'_sub_H Cm'_sub_H H1_eq. set_solver. }
         
        iClear "HnP_C HnP_Cm".
        iDestruct "HH" as "(HH & (HnP_C & HnP_Cm))".
        
        iAssert (global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r T' H hγ I R)
          with "[MCS_auth HH Hist Ht HI Out_I HR Out_R 
            Inf_R Hf Hγ FP_r Max_ts domm_IR domm_Iγ]" as "Hglob".
        { iFrame. }     
        
        
        iDestruct "HnS_oc" as "(%&%&%)".
        rename H1 into OC1. rename H2 into OC2. rename H3 into OC3.
        iAssert (outflow_constraints n In' Rn esn' Qn')%I as "HnS_oc".
        { iPureIntro. split; last split; try done.
          - intros n' k t. destruct (decide (n' = m)).
            + subst n'. 
              assert (outset_KT In' m = 
                          outset_KT In m ∖ Qn_old ∪ Qn_new) as Outset'.
              { assert (In_temp = outflow_delete_set_KT In m Qn_old) by done.
                assert (In' = outflow_insert_set_KT In_temp m Qn_new) by done.
                admit. }
              split.
              * intros Hout. rewrite Outset' in Hout.
                rewrite elem_of_union in Hout*; intros Hout.
                destruct Hout as [Hout | Hout].
                ** rewrite elem_of_difference in Hout *; intros Hout.
                   destruct Hout as [Hout1 Hout2].
                   apply (OC1 m k t) in Hout1.
                   destruct Hout1 as [H' H''].
                   assert (Ht := H'').
                   apply lookup_total_correct in H''.
                   rewrite <-H'' in Hout2.
                   assert (k ∉ S) as Hk.
                   { destruct (decide (k ∈ S)); try done.
                     assert ((k, Qn0' !!! k) ∈ Qn_old) as HkQn.
                     apply (HQn_old k (Qn0' !!! k)). 
                     split; try done. clear -Hout2 HkQn. done. }
                   split; try done. subst Qn'.
                   rewrite gmap_lookup_insert_map_ne.
                   done. by rewrite Dom_Smap.
                ** apply HQn_new in Hout.
                   destruct Hout as [Hout1 Hout2].
                   split. clear -Hout1 Sub_S. set_solver.
                   subst Qn'. 
                   rewrite gmap_lookup_insert_map.
                   rewrite (Lookup_Smap k Hout1).
                   by rewrite Hout2. by rewrite Dom_Smap.
              * destruct (decide (k ∈ S)).
                ** subst Qn'.
                   rewrite gmap_lookup_insert_map; try done.
                   rewrite (Lookup_Smap k e). simpl.
                   intros [H1' H2'].
                   assert (k ∈ S ∧ t = Cn !!! k) as H''.
                   split; try done. by inversion H2'.
                   apply (HQn_new k t) in H''.
                   clear -H'' Outset'. set_solver.
                   by rewrite Dom_Smap.
                ** rewrite (Lookup_Qn'_ne k n0).
                   intros H'. apply OC1 in H'.
                   apply (HQn_old_ne k t) in n0.
                   clear -H' Outset' n0. set_solver.
            + assert (outset_KT In' n' = outset_KT In n') as Outset'.
              { assert (In' = outflow_insert_set_KT In_temp m Qn_new) by done.
                assert (In_temp = outflow_delete_set_KT In m Qn_old) by done.
                pose proof (outflow_insert_set_outset_ne_KT In_temp m 
                                                Qn_new In' n' n0 H1).
                admit. }
(*                 pose proof (outflow_delete_set_outset_ne_KT In m  *)
(*                                                 Qn_old In_temp n' n0 H2). *)

              rewrite Outset'.
              split.
              * intros Hout. apply OC1 in Hout.
                destruct Hout as [Hout1 Hout2].
                assert (k ∉ S) as Hk.
                { destruct (decide (k ∈ S)); try done.
                  apply Sub_S in e.
                  pose proof Disj_esn' n' m n0.
                  clear -H1 e Hout1. set_solver. }
                rewrite (Lookup_Qn'_ne k Hk).
                split; try done.
              * intros Hkt.
                assert (k ∉ S) as Hk.
                { destruct Hkt as [Hkt1 Hkt2].
                  destruct (decide (k ∈ S)); try done.
                  apply Sub_S in e.
                  pose proof Disj_esn' n' m n0.
                  clear -H1 e Hkt1. set_solver. }
                rewrite (Lookup_Qn'_ne k Hk) in Hkt.
                by apply OC1 in Hkt. 
          - unfold outflow_le_1. intros n' kt. 
            destruct (decide (n' = m)).
            * subst n'. subst In'. unfold out, out_map. 
              unfold outflow_insert_set_KT. simpl.
              rewrite nzmap_lookup_total_insert.
              unfold out, out_map.
              unfold In_temp, outflow_delete_set_KT.
              simpl. rewrite nzmap_lookup_total_insert.
              pose proof OC3 m kt as OC3.
              destruct (decide (kt ∈ Qn_new)).
              ** rewrite nzmap_lookup_total_increment_set; try done.
                 destruct (decide (kt ∈ Qn_old)).
                 *** rewrite KT_flows.nzmap_lookup_total_decrement_set; try done.
                     clear -OC3. lia.
                 *** rewrite KT_flows.nzmap_lookup_total_decrement_set_ne; try done.
                     assert (∀ (x: nat), x ≤ 1 → x = 0 ∨ x = 1) as Hx.
                     { lia. } apply Hx in OC3.
                     destruct OC3 as [OC3 | OC3].
                     rewrite OC3. lia.
                     assert (kt ∈ outset_KT In m) as Hkt.
                     { unfold outset_KT, KT_flows.dom_ms.
                       rewrite nzmap_elem_of_dom_total.
                       rewrite OC3. unfold ccmunit, ccm_unit; simpl.
                       by unfold nat_unit. }
                     destruct kt as [k t].
                     apply OC1 in Hkt.
                     destruct Hkt as [_ H'].
                     apply lookup_total_correct in H'.
                     rewrite <-H' in n0.
                     assert ((k, Qn0' !!! k) ∈ Qn_old) as H''.
                     { apply HQn_old. apply HQn_new in e.
                       destruct e as [e _]. split; try done. }
                     clear -H'' n0. done.
              ** rewrite nzmap_lookup_total_increment_set_ne; try done.
                 destruct (decide (kt ∈ Qn_old)).
                 *** rewrite KT_flows.nzmap_lookup_total_decrement_set; try done.
                     clear -OC3. lia.
                 *** rewrite KT_flows.nzmap_lookup_total_decrement_set_ne; try done.
            * subst In'. unfold out, out_map. 
              unfold outflow_insert_set_KT. simpl.
              rewrite nzmap_lookup_total_insert_ne; try done.
              rewrite nzmap_lookup_total_insert_ne; try done.
              pose proof OC3 n' kt as OC3.
              by unfold out in OC3. }

        iDestruct "HnS_ocm" as "(%&%&%)".
        rename H1 into OC1m. rename H2 into OC2m. rename H3 into OC3m.

        iAssert (outflow_constraints m Im' Rm esm Qm)%I as "HnS_ocm".
        { iPureIntro. split; last split; try done. }

        assert (domm In' = {[n]}) as Domm_In'.
        { assert (In' = outflow_insert_set_KT In_temp m Qn_new).
          admit.  }

        assert (domm Im' = {[m]}) as Domm_Im'.
        { admit. }
        
        iAssert (singleton_interfaces_ghost_state γ_I γ_R n In' Rn
            ∗ singleton_interfaces_ghost_state γ_I γ_R m Im' Rm)%I 
                    with "[HnS_si HnS_sim]" as "(HnS_si & HnS_sim)".
        { iDestruct "HnS_si" as "(HIn & HRn & Domm_In & Domm_Rn)".
          iDestruct "HnS_sim" as "(HIm & HRm & Domm_Im & Domm_Rm)".
          iCombine "HIn HIm" as "HInm".
          assert (Im_temp = inflow_delete_set_KT Im m Qn_old) 
              as HIm_temp. done.
          assert (In_temp = outflow_delete_set_KT In m Qn_old)
              as HIn_temp. done.
          assert (In' = outflow_insert_set_KT In_temp m Qn_new)
              as HIn'. done.
          assert (Im' = inflow_insert_set_KT Im_temp m Qn_new)
              as HIm'. done.
          pose proof (flowint_delete_set_eq_KT In In_temp Im Im_temp 
                  m Qn_old HIn_temp HIm_temp) as HInm_temp.
          pose proof (flowint_insert_set_eq_KT In_temp In' Im_temp Im' 
                  m Qn_new HIn' HIm') as HInm'.
          rewrite HInm' in HInm_temp.
          iEval (rewrite HInm_temp) in "HInm".
          iEval (rewrite auth_frag_op) in "HInm".
          iDestruct "HInm" as "(HIn & HIm)".
          iFrame. iPureIntro. apply Domm_Im'. }
        
        iAssert (⌜φ0 esn' Qn'⌝ ∗ ⌜φ1 Bn0' Cn' Qn'⌝ ∗ ⌜φ2 n Bn0' In'⌝ 
                  ∗ ⌜φ3 n Bn0' Rn⌝ ∗ ⌜φ4 n Rn⌝ ∗ ⌜φ5 Bn0' Qn'⌝ 
                  ∗ ⌜φ6 Bn0' T'⌝ ∗ ⌜φ7 n esn' Rn Qn'⌝)%I
                with "[Hφ]" as "Hφ".
        { iDestruct "Hφ" as "(%&%&%&%&%&%&%&%)". 
          rename H1 into Hφ0. rename H2 into Hφ1.
          rename H3 into Hφ2. rename H4 into Hφ3.
          rename H5 into Hφ4. rename H6 into Hφ5. 
          rename H7 into Hφ6. rename H8 into Hφ7.
          iPureIntro. split; last split; last split; 
          last split; last split; last split; last split.
          - unfold φ0. intros k Hnot.
            assert (k ∉ S) as Hk.
            { destruct (decide (k ∈ S)); try done.
              apply Sub_S in e. pose proof Hnot m as Hnot.
              clear -e Hnot. set_solver. }
            rewrite (Lookup_Qn'_ne k Hk).
            apply Hφ0; try done.  
          - unfold φ1. intros k t'.
            rewrite map_eq_iff in MergeEq*; intros MergeEq.
            pose proof MergeEq k as MergeEq.
            rewrite !gmap_imerge_prf in MergeEq.
            unfold f_merge in MergeEq. split.
            + intros HCn'k. destruct (Cn !! k) as [t |] eqn: HCnk.
              * repeat rewrite decide_True in MergeEq.
                pose proof Hφ1 k t as [H' _].
                pose proof H' HCnk as H'.
                rewrite <-HCn'k, H'. by rewrite <-HCnk.
                rewrite HCn'k; try done. rewrite HCnk; try done.
              * pose proof set_of_map_member_ne Cn k HCnk t' as H'.
                pose proof set_of_map_member Cn' k t' HCn'k as H''.
                apply Subset_Cn in H''. clear -H' H''.
                set_solver.
            + intros HCn'. destruct (Cn !! k) as [t |] eqn: HCnk.
              * assert (k ∈ S) as Hk.
                { assert (k ∈ dom (gset K) Cn) as H1'.
                  rewrite elem_of_dom. rewrite HCnk; by exists t.
                  assert (k ∉ dom (gset K) Cn') as H2'.
                  rewrite not_elem_of_dom. done. 
                  subst S. clear -H1' H2'. set_solver. }
                rewrite (Lookup_Qn' k Hk).
                pose proof Hφ1 k t as H'.
                destruct H' as [H' _].
                pose proof H' HCnk as H'. 
                by rewrite H'.
              * assert (k ∉ S) as Hk.
                { assert (k ∉ dom (gset K) Cn) as H1'.
                  rewrite not_elem_of_dom. done. 
                  subst S. clear -H1'. set_solver. }
                rewrite (Lookup_Qn'_ne k Hk).
                pose proof Hφ1 k 0 as H'.
                destruct H' as [_ H'].
                by pose proof H' HCnk as H'. 
          - unfold φ2. try done.
          - unfold φ3. try done.
          - try done.
          - intros k. destruct (decide (k ∈ S)).
            + rewrite /(Qn' !!! k).
              unfold finmap_lookup_total. 
              rewrite (Lookup_Qn' k e).
              destruct (Cn !! k) as [t |] eqn: HCnk.
              * pose proof Hφ1 k t as H'.
                destruct H' as [H' _].
                pose proof H' HCnk as H'.
                rewrite lookup_total_alt.
                by rewrite H'.
              * by simpl; lia.
            + rewrite /(Qn' !!! k).
              rewrite /(Bn0' !!! k). 
              unfold finmap_lookup_total. 
              rewrite (Lookup_Qn'_ne k n0).
              pose proof Hφ5 k as H'.    
              rewrite /(Qn0' !!! k) in H'.
              by rewrite /(Bn0' !!! k) in H'. 
          - try done.
          - intros k. intros H'. rewrite elem_of_dom.
            apply Hφ7 in H'. rewrite elem_of_dom in H'*; intros H'.
            destruct (decide (k ∈ S)).
            * rewrite (Lookup_Qn' k e).
              assert (k ∈ dom (gset K) Cn) as H''.
              { subst S. clear -e; set_solver. }
              by rewrite elem_of_dom in H''*; intros H''.
            * by rewrite (Lookup_Qn'_ne k n0).   }
                              
        iAssert (⌜φ0 esm Qm⌝ ∗ ⌜φ1 Bm' Cm' Qm⌝ ∗ ⌜φ2 m Bm' Im'⌝ 
                  ∗ ⌜φ3 m Bm' Rm⌝ ∗ ⌜φ4 m Rm⌝ ∗ ⌜φ5 Bm' Qm⌝ 
                  ∗ ⌜φ6 Bm' T'⌝ ∗ ⌜φ7 m esm Rm Qm⌝)%I
                with "[Hφm]" as "Hφm".
        { iDestruct "Hφm" as "(%&%&%&%&%&%&%&%)". 
          rename H1 into Hφ0. rename H2 into Hφ1.
          rename H3 into Hφ2. rename H4 into Hφ3.
          rename H5 into Hφ4. rename H6 into Hφ5. 
          rename H7 into Hφ6. rename H8 into Hφ7. 
          iPureIntro. split; last split; last split; 
          last split; last split; last split; last split.
          - unfold φ0. try done.
          - unfold φ1. intros k t.
            rewrite map_eq_iff in MergeEq*; intros MergeEq.
            pose proof MergeEq k as MergeEq.
            rewrite !gmap_imerge_prf in MergeEq.
            unfold f_merge in MergeEq. split.
            + intros HCm'k. assert (H' := HCm'k). 
              apply set_of_map_member in H'.
              apply Subset_Cm in H'.
              rewrite elem_of_union in H'*; intros H'.
              destruct H' as [H' | H'].
              * apply set_of_map_member_rev in H'.
                subst Bm'. destruct (Cn' !! k) as [t' | ] eqn: HCn'k.
                ** repeat rewrite decide_True in MergeEq.
                   assert (t' = t) as Ht.
                   { rewrite HCn'k H' in MergeEq.
                     by inversion MergeEq. }
                   subst t'. 
                   apply set_of_map_member in H'.
                   apply set_of_map_member in HCm'k.
                   apply set_of_map_member in HCn'k.
                   clear -H' HCm'k  HCn'k Subset_disj. set_solver.
                   rewrite HCn'k; try done. rewrite H'; try done.
                ** rewrite decide_True in MergeEq.
                   rewrite decide_False in MergeEq.
                   destruct (decide (k ∈ esn' !!! m)).
                   *** assert (k ∈ S) as Hk.
                       { subst S. rewrite elem_of_difference.
                         split. rewrite elem_of_dom.
                         rewrite H'. by exists t.
                         by rewrite not_elem_of_dom. }
                       rewrite gmap_lookup_insert_map.
                       rewrite (Lookup_Smap k Hk).
                       rewrite /(Cn !!! k). 
                       unfold finmap_lookup_total.
                       rewrite H'; by simpl.
                       rewrite Dom_Smap. done.
                   *** rewrite H' in MergeEq.
                       inversion MergeEq.
                   *** intros H''. done.
                   *** rewrite H'. done.
                * apply set_of_map_member_rev in H'.
                  pose proof Hφ1 k t as H''.
                  destruct H'' as [H'' _].
                  pose proof H'' H' as HBm.
                  destruct (decide (k ∈ S)).
                  ** subst Bm'.
                     rewrite gmap_lookup_insert_map.
                     rewrite (Lookup_Smap k e).
                     destruct (Cn !! k) as [t' | ] eqn: HCnk.
                     *** rewrite decide_True in MergeEq.
                         destruct (Cn' !! k) as [t'' | ] eqn: HCn'k.
                         **** assert (k ∉ S) as Hk.
                              { assert (k ∈ dom (gset K) Cn). 
                                rewrite elem_of_dom. rewrite HCnk.
                                by exists t'.
                                assert (k ∈ dom (gset K) Cn'). 
                                rewrite elem_of_dom. rewrite HCn'k.
                                by exists t''. subst S.
                                clear -H1 H2. set_solver. }
                              clear -Hk e.
                              set_solver.
                         **** rewrite decide_False in MergeEq.
                              rewrite decide_True in MergeEq.
                              rewrite HCm'k in MergeEq.
                              apply lookup_total_correct in MergeEq.
                              by rewrite MergeEq. by apply Sub_S in e.
                              rewrite HCn'k. intros Hnone. done.
                         **** rewrite HCnk; try done.
                     *** assert (k ∉ S) as Hk.
                         { assert (k ∉ dom (gset K) Cn). 
                           rewrite not_elem_of_dom. rewrite HCnk.
                           done. subst S. clear -H1; set_solver. }
                         clear -Hk e. set_solver.
                     *** by rewrite Dom_Smap.
                  ** rewrite gmap_lookup_insert_map_ne.
                     done. by rewrite Dom_Smap.
            + intros HCm'. assert (Cm !! k = None) as HCm.
              { destruct (Cm !! k) eqn: HCmk; try done.
                assert (k ∈ dom (gset K) Cm).
                { rewrite elem_of_dom. rewrite HCmk.
                  by exists u. }
                assert (k ∉ dom (gset K) Cm').
                { by rewrite not_elem_of_dom. }
                clear -H1 H2 Cm_sub_Cm'.
                set_solver. }
              pose proof Hφ1 k 0 as H'.
              destruct H' as [_ H'].
              pose proof H' HCm as H'.
              assert (k ∉ S) as Hk.
              { destruct (decide (k ∈ S)); try done.
                subst S. assert (k ∈ dom (gset K) Cn) as H1'.
                { clear -e. set_solver. }
                assert (k ∉ dom (gset K) Cn') as H2'.
                { clear -e. set_solver. }
                rewrite elem_of_dom in H1'*; intros H1'.
                rewrite not_elem_of_dom in H2'*; intros H2'.
                destruct H1' as [t' H1'].
                rewrite decide_True in MergeEq.
                rewrite decide_False in MergeEq.
                rewrite decide_True in MergeEq.
                rewrite HCm' in MergeEq.
                rewrite MergeEq in H1'. inversion H1'.
                by apply Sub_S in e.
                rewrite H2'. intros ?; try done.
                rewrite H1'; try done. }
              subst Bm'. rewrite gmap_lookup_insert_map_ne.
              done. by rewrite Dom_Smap.
          - unfold φ2. intros k t Hkt.
            assert (inset_KT Im' m = 
                          inset_KT Im m ∖ Qn_old ∪ Qn_new) as Hinset.
            { admit. }
            rewrite Hinset in Hkt.
            rewrite elem_of_union in Hkt*; intros Hkt.
            destruct Hkt as [Hkt | Hkt].
            * rewrite elem_of_difference in Hkt*; intros Hkt.
              destruct Hkt as [Hkt1 Hkt2].
              apply Hφ2 in Hkt1.
              destruct (decide (k ∈ S)).
              ** pose proof Bm_eq_Qn k e as H'.
                 assert ((k,t) ∈ Qn_old) as H''.
                 { apply HQn_old. split; try done.
                   by rewrite H' in Hkt1. }
                 clear -H'' Hkt2. set_solver.
              ** rewrite lookup_total_alt. subst Bm'.
                 rewrite gmap_lookup_insert_map_ne.
                 by rewrite lookup_total_alt in Hkt1.
                 by rewrite Dom_Smap.
            * apply HQn_new in Hkt.
              destruct Hkt as [Hkt1 Hkt2].
              rewrite lookup_total_alt.
              subst Bm'. rewrite gmap_lookup_insert_map.
              rewrite (Lookup_Smap k Hkt1).
              by simpl. by rewrite Dom_Smap.
          - unfold φ3. intros k.
            destruct (decide (k ∈ S)).
            + apply S_sub_insetm in e.
              right. unfold in_inset.
              by unfold inset in e.
            + subst Bm'.
              rewrite gmap_lookup_insert_map_ne.
              apply Hφ3. by rewrite Dom_Smap.
          - try done.
          - intros k. 
            apply (Nat.le_trans _ (Bm !!! k) _).
            apply Hφ5. apply Bm_le_Bm'.
          - intros k. destruct (decide (k ∈ S)).
            + rewrite /(Bm' !!! k).
              unfold finmap_lookup_total.
              subst Bm'.
              rewrite gmap_lookup_insert_map.
              rewrite (Lookup_Smap k e). simpl.    
              apply Cn_le_T'. by rewrite Dom_Smap.
            + rewrite /(Bm' !!! k).
              unfold finmap_lookup_total.
              subst Bm'.
              rewrite gmap_lookup_insert_map_ne.
              apply Hφ6. by rewrite Dom_Smap.
          - try done. }

        
        iModIntro.
        iSplitR "AU HnP_gh HnP_ghm HnP_tm HnP_t node_n node_m 
                            HnP_C HnP_Cm HnP_frac HnP_fracm".
        { iNext. iExists T', H, hγ, I, R. iFrame "Hglob".
          rewrite (big_sepS_delete _ (domm I) n); last by eauto.
          iSplitL "Hl_n HnS_gh HnS_FP HnS_cl HnS_H HnS_star 
                       HnS_frac HnS_oc HnS_si Hφ".
          { iExists true, Cn', Bn0', Qn'. iFrame "Hl_n".
            iSplitR; try done.
            iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn', In', Rn.
            iFrame. iFrame "HnS_oc". }
          rewrite (big_sepS_delete _ (domm I ∖ {[n]}) m); last first.
          clear -m_neq_n m_in_I. set_solver.
          iFrame "Hstar'". iExists true, Cm', Bm', Qm.
          iFrame "Hl_m Hlif_m".
          iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm, Im', Rm.
          iFrame. rewrite <-PeanoNat.Nat.eqb_neq in m_neq_r.
          by rewrite m_neq_r. }                            
        iModIntro.
        awp_apply (unlockNode_spec_high with "[] [] 
            [HnP_gh HnP_frac HnP_C HnP_t node_n]"); try done.
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn', T.
        iFrame. iAaccIntro with ""; try eauto with iFrame.
        iIntros "_"; iModIntro. wp_pures.
        awp_apply (unlockNode_spec_high with "[] [] 
            [HnP_ghm HnP_fracm HnP_Cm HnP_tm node_m]"); try done.
        iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm, Tm.
        iFrame. iAaccIntro with ""; try eauto with iFrame.
        iIntros "_"; iModIntro. wp_pures.
        iApply "IH"; try done.
    + admit.             
  Admitted.           

(*
  Lemma traverse_spec γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r 
                          γ_en γ_cn γ_bn γ_qn γ_cirn n (k: K) t0 t1 :
    ⊢ ⌜k ∈ KS⌝ -∗ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
        inFP γ_f n -∗ 
          own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]}) -∗ 
            own (γ_cirn !!! k) (◯ MaxNat t1) -∗ ⌜t0 ≤ t1⌝ -∗
              <<< ∀ t H, MCS γ_te γ_he t H >>> 
                  traverse #n #k @ ⊤ ∖ ↑N
              <<< ∃ (t': nat), MCS γ_te γ_he t H ∗ ⌜(k, t') ∈ H⌝ 
                                             ∗ ⌜t0 ≤ t'⌝ , RET #t' >>>.
  Proof.
    iIntros "k_in_KS #HInv". 
    iLöb as "IH" forall (n t1 γ_en γ_cn γ_bn γ_qn γ_cirn).
    iIntros "#FP_n #Hgh #Hlb H". iDestruct "H" as %t0_le_t1.
    iDestruct "k_in_KS" as %k_in_KS.
    iIntros (Φ) "AU". wp_lam. wp_pures.
    (** Lock node n **)
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cn Bn Qn)"HnP_n". iModIntro. wp_pures. 
    iDestruct "HnP_n" as (γ_en' γ_bn' γ_cn' γ_qn' γ_cirn' es T)
                    "(node_n & HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iPoseProof (ghost_heap_sync with "[$HnP_gh] [$Hgh]") 
                                  as "(% & % & % & % & %)".
    subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
    (** Check contents of n **)
    wp_apply (inContents_spec with "node_n").
    iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val.
    wp_pures.
    (** Case analysis on whether k in contents of n **)
    destruct t as [t |]; last first.
    - (** Case : k not in contents of n **)
      wp_pures.
      (** Find next node to visit **)
      wp_apply (findNext_spec with "node_n").
      iIntros (b n1) "(node_n & Hif)". 
      (** Case analysis on whether there exists a next node **)
      destruct b.
      + (** Case : exists next node n' **)
        wp_pures. iDestruct "Hif" as %k_in_es.
        iApply fupd_wp.
        (** Open invariant to establish resources
            required to apply induction hypothesis IH
            on node n' **)
        iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn'. subst Bn'. subst Qn'.
        iAssert (inFP γ_f n1)%I as "#FP_n1".
        { iApply "HnS_cl". iPureIntro. 
          clear -k_in_es. set_solver. }
             
        iAssert (⌜n1 ∈ domm I⌝)%I as %n_in_I.
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n1] [$Hf]") as "H'". }
        iAssert (⌜n ≠ n1⌝)%I as %n_neq_n1.
        { destruct (decide (n = n1)); try done.
          iPoseProof (node_edgeset_self_empty with "node_n") as "%".
          rename H1 into Es_n. rewrite <-e in k_in_es.
          clear -k_in_es Es_n. set_solver. } 
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n1); last by set_solver.
        iDestruct "Hstar'" as "(H_n1 & Hstar'')".
        iDestruct "H_n1" as (bn1 Cn1 Bn1 Qn1)"(Hl_n1 & Hlif_n1 & HnS_n1)".
        iDestruct "HnS_n1" as (γ_en1 γ_cn1 γ_bn1 γ_qn1 γ_cirn1 es1 In1 Rn1) 
                  "(HnS_gh1 & HnS_frac1 & HnS_si1 & HnS_FP1 
                       & HnS_cl1 & HnS_oc1 & HnS_H1 & HnS_star1 & Hφ1)".

        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); 
                              last by eauto) in "HnS_star".
        iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k);
                                     last by eauto) in "HnS_star1".
        iDestruct "HnS_star1" as "(Hcirk_n1 & HnS_star1')".
        iMod (own_update (γ_cirn1 !!! k) (● MaxNat (Bn1 !!! k)) 
              ((● MaxNat (Bn1 !!! k)) ⋅ (◯ MaxNat (Bn1 !!! k))) 
                  with "[Hcirk_n1]") as "(Hcirk_n1 & #Hlb_1)".
        { apply (auth_update_alloc _ (MaxNat (Bn1 !!! k)) 
                              (MaxNat (Bn1 !!! k))).
          apply max_nat_local_update. 
          simpl. lia. } { iFrame. }

        iAssert (⌜t0 ≤ Bn1 !!! k⌝)%I as "%".
        { iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
          { iPoseProof (own_valid_2 with "[$Hcirk_n] [$Hlb]") as "%".
            rename H1 into Valid_Bnt.
            apply auth_both_valid_discrete in Valid_Bnt.
            destruct Valid_Bnt as [H' _].
            apply max_nat_included in H'.
            simpl in H'. by iPureIntro. }
          destruct (Qn !! k) as [tq | ] eqn: Hqn.
          - iAssert (⌜(k, Qn !!! k) ∈ outset_KT In n1⌝)%I as %outflow_n_n1.
            { iDestruct "HnS_oc" as "(H' & _)".
              iDestruct "H'" as %H'. iPureIntro.    
              apply (H' n1 k (Qn !!! k)).
              unfold outflow_constraint_I in H'.
              repeat split; try done. 
              rewrite lookup_total_alt. 
              rewrite Hqn. by simpl. }
            iAssert (⌜(k, Qn !!! k) ∈ inset_KT In1 n1⌝)%I as %inflow_n1.
            { iDestruct "HnS_si" as "(H'&_)".
              iDestruct "HnS_si1" as "(H1'&_&%&_)".
              rename H1 into Domm_In1.
              assert (n1 ∈ domm In1) as H''. 
              { clear -Domm_In1. set_solver. }
              iCombine "H'" "H1'" as "H'".
              iPoseProof (own_valid with "[$H']") as "%".
              rename H1 into Valid_InIn1.
              rewrite auth_frag_valid in Valid_InIn1 *; intros Valid_InIn1.
              pose proof intComp_unfold_inf_2 In In1 Valid_InIn1 n1 H''.
              rename H1 into H'. unfold ccmop, ccm_op in H'.
              simpl in H'. unfold lift_op in H'.
              iPureIntro. rewrite nzmap_eq in H' *; intros H'.
              pose proof H' (k, Qn !!! k) as H'.
              rewrite nzmap_lookup_merge in H'.
              unfold ccmop, ccm_op in H'. simpl in H'.
              unfold nat_op in H'.
              assert (1 ≤ out In n1 !1 (k, Qn !!! k)) as Hout.
              { unfold outset_KT, KT_flows.dom_ms in outflow_n_n1.
                rewrite nzmap_elem_of_dom_total in outflow_n_n1 *; 
                intros outflow_n_n1.
                unfold ccmunit, ccm_unit in outflow_n_n1.
                simpl in outflow_n_n1. unfold nat_unit in outflow_n_n1.
                clear - outflow_n_n1. lia. }
              assert (1 ≤ inf In1 n1 !1 (k, Qn !!! k)) as Hin.
              { clear -H' Hout. 
                assert (∀ (x y z: nat), 1 ≤ y → x = z + y → 1 ≤ x) as H''.
                lia. by pose proof H'' _ _ _ Hout H'. }
              unfold inset_KT. rewrite nzmap_elem_of_dom_total.
              unfold ccmunit, ccm_unit. simpl. unfold nat_unit.
              clear -Hin. lia. }
            iAssert (⌜Bn1 !!! k = Qn !!! k⌝)%I as %Bn1_eq_Bn.
            { iDestruct "Hφ1" as "(_ & _& % & _)". 
              rename H1 into Hφ2. pose proof Hφ2 k (Qn !!! k) inflow_n1 as H'.
              iPureIntro. done. } 
            iAssert (⌜Bn !!! k = Qn !!! k⌝)%I as %Bn_eq_Qn.
            { iDestruct "Hφ" as "(_ & % & _)". rename H1 into Hφ1.
              pose proof Hφ1 k as [_ H'].
              iPureIntro. pose proof H' Cn_val as H'. 
              rewrite /(Bn !!! k). unfold finmap_lookup_total.
              by rewrite H'.  } 
            iPureIntro. rewrite Bn1_eq_Bn.
            rewrite <-Bn_eq_Qn. clear -lb_t1 t0_le_t1.
            apply (Nat.le_trans _ t1 _); try done.
          - iDestruct "Hφ" as "(_ & % & _)".
            rename H1 into Hφ1. apply Hφ1 in Cn_val.
            rewrite <-Cn_val in Hqn.
            rewrite lookup_total_alt in lb_t1.
            rewrite Hqn in lb_t1.
            simpl in lb_t1. iPureIntro.
            clear -lb_t1 t0_le_t1. lia.
            try done. }
 
        iAssert (own γ_gh (◯ {[n1 := 
                      ghost_loc γ_en1 γ_cn1 γ_bn1 γ_qn1 γ_cirn1]}))%I
                            with "HnS_gh1" as "#Hgh1".  
        (** Closing the invariant **)
        iModIntro. iSplitR "node_n HnP_gh HnP_frac HnP_C HnP_t AU". iNext.
        iExists T', H, hγ, I, R. iFrame "Hglob".
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n1); last set_solver.
        iFrame "Hstar''". iSplitL "Hl_n Hlif_n HnS_gh HnS_frac 
                    HnS_si HnS_FP HnS_cl HnS_oc HnS_H Hcirk_n HnS_star' Hφ".
        iExists bn, Cn, Bn, Qn. iFrame "Hl_n Hlif_n".
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, In, Rn.
        iFrame. by iApply "HnS_star'".                  
        iExists bn1, Cn1, Bn1, Qn1. iFrame "Hl_n1 Hlif_n1".
        iExists γ_en1, γ_cn1, γ_bn1, γ_qn1, γ_cirn1, es1, In1, Rn1.
        iFrame. by iApply "HnS_star1'".
        iModIntro.
        (** Unlock node n **)       
        awp_apply (unlockNode_spec_high with "[] [] 
            [HnP_gh HnP_frac HnP_C HnP_t node_n]"); try done.
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, T.
        iFrame.                
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_". iModIntro. wp_pures.
        (** Apply IH on node n' **)
        iApply "IH"; try done. 
      + (** Case : no next node from n **)
        wp_pures. iDestruct "Hif" as %Not_in_es.
        iApply fupd_wp. 
        (** Linearization Point: key k has not been found in the 
            data structure. Open invariant to obtain resources 
            required to establish post-condition **)
        iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn'. subst Bn'. subst Qn'.
        iAssert (⌜Bn !!! k = 0⌝)%I as %Bn_eq_0.
        { iDestruct "Hφ" as "(Hφ0 & Hφ1 & _)".
          iDestruct "Hφ0" as %Hφ0.
          iDestruct "Hφ1" as %Hφ1.
          pose proof Hφ0 k Not_in_es as Hφ0.
          pose proof Hφ1 k as [_ H'].
          pose proof H' Cn_val as H'. 
          iPureIntro.
          rewrite lookup_total_alt.
          rewrite H' Hφ0. by simpl. }          
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                       in "HnS_star".
        iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
        iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
        { iPoseProof (own_valid_2 with "[$Hcirk_n] [$Hlb]") as "%".
          rename H1 into Valid_Bnt.
          apply auth_both_valid_discrete in Valid_Bnt.
          destruct Valid_Bnt as [H' _].
          apply max_nat_included in H'.
          simpl in H'. by iPureIntro. }
        iAssert (⌜t0 = 0⌝)%I as %t0_zero. 
        { iPureIntro. rewrite Bn_eq_0 in lb_t1. 
          clear -lb_t1 t0_le_t1. lia. } subst t0.
        (** Linearization **)  
        iMod "AU" as (t' H') "[MCS [_ Hclose]]". 
        iAssert (⌜H' = H⌝)%I as %H1. 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
          unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
          by iDestruct "MCS" as "(_ & H')".
          by iPureIntro. } subst H'.
        iAssert (⌜(k,0) ∈ H⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          iDestruct "Hist" as %Hist. iPureIntro. 
          by pose proof Hist k k_in_KS as Hist. }
        rename H1 into k0_in_H.  
        iSpecialize ("Hclose" $! 0).
        iMod ("Hclose" with "[MCS]") as "HΦ". iFrame. 
        iPureIntro. split; try done.
        (** Closing the invariant **)
        iModIntro. iSplitR "node_n HnP_gh HnP_frac HnP_C HnP_t HΦ". iNext.
        iExists T', H, hγ, I, R. iFrame "Hglob".
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iFrame "Hstar'". iExists bn, Cn, Bn, Qn.
        iFrame "Hl_n Hlif_n". 
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, In, Rn.
        iFrame "∗%". by iApply "HnS_star'". iModIntro.
        (** Unlock node n **)
        awp_apply (unlockNode_spec_high with "[] [] 
               [HnP_gh HnP_frac HnP_C HnP_t node_n]") without "HΦ"; try done. 
        iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, T. iFrame.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_". iModIntro. iIntros "HΦ". by wp_pures.
    - (** Case : k in contents of n **)
      wp_pures.                                         
      iApply fupd_wp. 
      (** Linearization Point: key k has been found. Open 
          invariant to obtain resources required to 
          establish post-condition **)
      iInv "HInv" as ">H".
      iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
      iAssert (⌜n ∈ domm I⌝)%I as "%". 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iDestruct "Hstar" as "(H_n & Hstar')".
      iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
      iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                    "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                              & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
      iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                as "(% & % & % & % & %)".
      subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
      iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
      destruct H1 as [Hes [Hc [Hb Hq]]]. 
      subst es'. subst Cn'. subst Bn'. subst Qn'.
      iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                      in "HnS_star".
      iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
      iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
      { iPoseProof (own_valid_2 with "[$Hcirk_n] [$Hlb]") as "%".
        rename H1 into Valid_Bnt.
        apply auth_both_valid_discrete in Valid_Bnt.
        destruct Valid_Bnt as [H' _].
        apply max_nat_included in H'.
        simpl in H'. by iPureIntro. }
      iAssert (⌜Bn !!! k = Cn !!! k⌝)%I as %Bn_eq_Cn.
      { iDestruct "Hφ" as "(_ & Hφ1 & _)".
        iDestruct "Hφ1" as %Hφ1.
        pose proof Hφ1 k t as [H' _].
        iPureIntro.
        rewrite !lookup_total_alt.
        pose proof H' Cn_val as H'.
        by rewrite Cn_val H'. }          
      iAssert (⌜set_of_map Cn ⊆ H⌝)%I as %Cn_Sub_H.
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        iPoseProof ((auth_own_incl γ_s H _) with "[$HH $HnP_C]") as "%".
        rename H1 into H'. by apply gset_included in H'. }  
      iAssert (⌜(k,t) ∈ set_of_map Cn⌝)%I as %kt_in_Cn.
      { iPureIntro. apply set_of_map_member.
        rewrite /(Cn !!! k) in Cn_val.
        unfold finmap_lookup_total, inhabitant in Cn_val.
        simpl in Cn_val. 
        destruct (Cn !! k) as [cnk | ] eqn: Hcnk.
        - rewrite Hcnk. apply f_equal.
          by inversion Cn_val. 
        - try done.  }
      (** Linearization **)      
      iMod "AU" as (t' H') "[MCS [_ Hclose]]". 
      iSpecialize ("Hclose" $! t).
      iAssert (⌜H' = H⌝)%I as %H1. 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
        unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
        by iDestruct "MCS" as "(_ & H')".
        by iPureIntro. } replace H'.
      iMod ("Hclose" with "[MCS]") as "HΦ". iFrame. 
      iPureIntro. split. set_solver. rewrite Bn_eq_Cn in lb_t1.
      rewrite lookup_total_alt in lb_t1.
      rewrite Cn_val in lb_t1. simpl in lb_t1. lia.
      (** Closing the invariant **)
      iModIntro. iSplitR "node_n HnP_gh HnP_frac HnP_C HnP_t HΦ".
      iNext. iExists T', H, hγ, I, R. iFrame "Hglob".
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iFrame "Hstar'". iExists bn, Cn, Bn, Qn.
      iFrame "Hl_n Hlif_n". 
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, In, Rn.
      iFrame "∗%". by iApply "HnS_star'". iModIntro.
      (** Unlock node n **)
      awp_apply (unlockNode_spec_high with "[] [] 
                [HnP_gh HnP_frac HnP_C HnP_t node_n]") without "HΦ"; 
                      try done.
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, es, T. iFrame.
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. iIntros "HΦ". by wp_pures.
      Unshelve. try done. try done.
  Qed.

  Lemma upsert_spec γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r (k: K) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
          mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
                <<< ∀ t H, MCS γ_te γ_he t H >>> 
                    upsert lc r #k @ ⊤ ∖ ↑N
                <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k, t)]}), RET #() >>>.
  Proof.
    iIntros "H". iDestruct "H" as %k_in_KS.
    iIntros "#HInv". iLöb as "IH".
    iIntros (Φ) "AU". wp_lam.
    iApply fupd_wp. 
    (** Open invariant to establish root node in footprint **)
    iInv "HInv" as ">H".
    iDestruct "H" as (T0 H0 hγ0 I0 R0) "(Hglob & Hstar)".
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & #FP_r & Max_ts & domm_IR & domm_Iγ)".
    iModIntro. iSplitR "AU". iNext. 
    iExists T0, H0, hγ0, I0, R0. iFrame "∗ #". iModIntro.
    (** Lock the node r **)
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cr Br Qr)"HnP_n". iModIntro. wp_pures.
    iDestruct "HnP_n" as (γ_er γ_cr γ_br γ_qr γ_cirr es T)
                      "(node_r & HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iEval (rewrite <-beq_nat_refl) in "HnP_t".
    wp_apply (readClock_spec with "[HnP_t]"); try done.
    iIntros "HnP_t". wp_pures.
    wp_apply (addContents_spec with "node_r").
    iIntros (b Cr')"(node_r & Hif)".
    (** Case analysis on whether addContents is successful **)
    destruct b; last first.
    - (** Case : addContents fails. Unlock root node and apply 
                 inductive hypothesis IH **) 
      iDestruct "Hif" as %HCr. replace Cr'. wp_pures.
      awp_apply (unlockNode_spec_high with "[] [] [-AU]"); try done.
      { iExists γ_er, γ_cr, γ_br, γ_qr, γ_cirr, es, T.
        iFrame. iEval (rewrite <-beq_nat_refl); try done. }
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. wp_pures.
      by iApply "IH".
    - (** Case : addContent successful **)
      (** Linearization Point: open invariant and update the resources **)
      awp_apply (incrementClock_spec γ_t lc T). iInv "HInv" as ">H". 
      iDestruct "H" as (T1 H1 hγ1 I1 R1) "(Hglob & Hstar)".
      iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & _ & Max_ts & domm_IR & domm_Iγ)".
      iDestruct "Hif" as %HCr. wp_pures.
      iAssert (⌜T = T1⌝)%I as %HT. 
      { iDestruct "HnP_t" as "(HnP_t & Hc)".
        iPoseProof ((own_valid_2 _ _ _) with "[$HnP_t] [$Ht]") as "H'".
        iDestruct "H'" as %H'. 
        pose proof (auth_auth_frac_op_inv _ _ _ _ H') as H''.
        inversion H''. by iPureIntro. } replace T1.
      (** Updating the clock value **)            
      iAssert (own γ_t (● (MaxNat T)) ∗ clock lc T)%I 
                                        with "[Ht HnP_t]" as "H".
      { iDestruct "HnP_t" as "(Ht' & Hc)".
        iCombine "Ht Ht'" as "H'". iFrame. }
      iAaccIntro with "H".
      { iIntros "H". iDestruct "H" as "(Ht & Hc)".
        iDestruct "Ht" as "(Ht & HnP_t)".
        iCombine "HnP_t Hc" as "HnP_t". 
        iModIntro. iSplitR "AU HnP_gh HnP_frac HnP_C node_r HnP_t".
        iNext. iExists T, H1, hγ1, I1, R1. iFrame "∗ #". iFrame.
        by iPureIntro. }
      iIntros "(Ht & Hc)".  
      iDestruct "Ht" as "(Ht & HnP_t)".
      iCombine "HnP_t Hc" as "HnP_t".
      iPoseProof ((auth_own_incl γ_s H1 _) with "[$HH $HnP_C]") as "%".
      rename H into Cr_sub_H1. apply gset_included in Cr_sub_H1.
      iDestruct "Max_ts" as %Max_tsH1.
      (** Re-establish maxTS for updated T and H **)
      assert (maxTS (T+1) (H1 ∪ {[(k, T)]})) as Max_ts.
      { split. intros k' t' H.
        assert (((k',t') ∈ H1) ∨ (k' = k ∧ t' = T)) as Hor by set_solver.
        destruct Hor as [Hor | Hor]. 
        destruct Max_tsH1 as [Max_tsH1 _].
        pose proof Max_tsH1 k' t' Hor as Hres. lia.
        destruct Hor as [_ Hor]. replace t'. lia.
        destruct Max_tsH1 as [_ Max_tsH1]. lia. }       
      iAssert (⌜set_of_map Cr' ⊆ H1 ∪ {[(k,T)]}⌝)%I as %Cr_sub_H1'.
      { iPureIntro. replace Cr'.
        pose proof (set_of_map_insert_subseteq Cr k T) as H'.
        assert (set_of_map Cr = set_of_map Cr) as H'' by done. 
        set_solver. }
      (** Update the (● H) resource **)  
      iMod (own_update γ_s (● H1) (● (H1 ∪ {[(k,T)]})) with "[$HH]") as "HH".
      { apply (auth_update_auth _ _ (H1 ∪ {[(k,T)]})).
        apply gset_local_update. set_solver. }
      iMod (own_update γ_s (● (H1 ∪ {[(k, T)]})) 
             (● (H1 ∪ {[(k, T)]}) ⋅ ◯ (set_of_map Cr')) with "[$HH]") as "HH".
      { apply (auth_update_alloc _ (H1 ∪ {[(k,T)]}) (set_of_map Cr')).
        apply local_update_discrete. intros m Valid_H1 H1_eq.
        split; try done. rewrite /(ε ⋅? m) in H1_eq.
        destruct m. rewrite gset_op_union in H1_eq. 
        rewrite left_id in H1_eq *; intros H1_eq.
        rewrite <-H1_eq. 
        rewrite /(set_of_map Cr' ⋅? Some (H1 ∪ {[k, T]})).
        rewrite gset_op_union.
        rewrite /(ε) in H1_eq. unfold ucmra_unit in H1_eq.
        simpl in H1_eq.
        assert ((k,T) ∈ set_of_map Cr') as H'.
        { replace Cr'. apply set_of_map_member.
          apply lookup_insert. } 
        clear - H' Cr_sub_H1 Cr_sub_H1'. set_solver.
        exfalso. clear -H1_eq. set_solver. }
      (** Re-establish history_init **)   
      iAssert (⌜history_init (H1 ∪ {[(k, T)]})⌝)%I with "[Hist]" as "Hist".
      { iDestruct "Hist" as %Hist.
        unfold history_init. iPureIntro.
        clear -Hist k_in_KS. intros k' Hk'.
        pose proof Hist k' Hk' as H'. set_solver. }  
      iDestruct "HnP_C" as "_".  
      iDestruct "HH" as "(HH & HnP_C)".   
      iAssert (⌜r ∈ domm I1⌝)%I as %r_in_I.
      { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
      iDestruct "Hstar" as "(H_r & Hstar')".
      iDestruct "H_r" as (br Cr'' Br'' Qr'')"(Hl_r & Hlif_r & HnS_r)".
      iAssert (⌜br = true⌝)%I as %Hbr.
      { destruct br; try done.
        iDestruct "Hlif_r" as 
            (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T')"(node' & _)".
        iPoseProof ((node_sep_star r r) with "[$]") as "%".
        contradiction. } replace br.
      iDestruct "HnS_r" as (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' Ir Rr) 
                    "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                              & HnS_cl & HnS_oc & HnS_if & HnS_star & Hφ)".
      iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                as "(% & % & % & % & %)".
      subst γ_er'. subst γ_cr'. subst γ_br'. subst γ_qr'. subst γ_cirr'.
      iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
      destruct H as [Hes [Hc [Hb Hq]]]. 
      subst es'. subst Cr''. subst Br''. subst Qr''.
      (** Update contents-in-reach of r **)
      set (Br' := <[k := T]>Br).
      assert (Br' = <[k := T]>Br) as HBr'. try done.
      iEval (rewrite <-beq_nat_refl) in "HnS_if".
      iDestruct "HnS_if" as "(% & %)". 
      rename H into Br_eq_H1. rename H2 into Infz_Ir.
      iAssert (⌜Br' = map_of_set (H1 ∪ {[(k, T)]})⌝)%I as %Br'_eq_H1.
      { iPureIntro.
        apply map_of_set_insert_eq; try done.
        intros t. 
        destruct Max_tsH1 as [Max_tsH1 _].
        by pose proof Max_tsH1 k t. }
      iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto) in "HnS_star".
      iDestruct "HnS_star" as "(Hk & HnS_star')".
      iAssert (⌜Br !!! k ≤ T⌝)%I as %Br_le_T. 
      { iDestruct "Hφ" as "(_&_&_&_&_&_&%&_)".
        iPureIntro. rename H into H'.
        by pose proof H' k. }
      iMod (own_update (γ_cirr !!! k) (● (MaxNat (Br !!! k))) 
                (● (MaxNat (Br' !!! k))) with "Hk") as "Hk".
      { apply (auth_update_auth _ _ (MaxNat (Br' !!! k))).
        apply max_nat_local_update.
        simpl. rewrite HBr'.
        by rewrite lookup_total_insert. }        
      iAssert ([∗ set] k0 ∈ KS, own (γ_cirr !!! k0) 
                  (● {| max_nat_car := Br' !!! k0 |}))%I 
          with "[HnS_star' Hk]" as "HnS_star".
      { iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto).
        iFrame "Hk".        
        iApply (big_opS_proper 
             (λ y, own (γ_cirr !!! y) (● {| max_nat_car := Br' !!! y |}))
             (λ y, own (γ_cirr !!! y) (● {| max_nat_car := Br !!! y |})) 
             (KS ∖ {[k]})).
        intros x Hx. assert (x ≠ k) as H' by set_solver.
        iFrame. iSplit. 
        iIntros "H". iEval (rewrite HBr') in "H".
        assert (<[k:=T]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'') in "H".       
        iIntros "H". iEval (rewrite HBr').
        assert (<[k:=T]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'').
        done. }
      iMod ((frac_update γ_er γ_cr γ_br γ_qr es Cr Br Qr es Cr' Br' Qr) 
                  with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".
      iDestruct "Inf_R" as %Inf_R.
      iPoseProof ((auth_own_incl γ_R R1 Rr) with "[HR HnS_si]")
                                    as (Ro) "%". 
      { unfold singleton_interfaces_ghost_state.
        iDestruct "HnS_si" as "(_ & H' & _)". 
        iFrame. } rename H into Incl_R1.
      iPoseProof (own_valid with "HR") as "%".
      rename H into Valid_R1.
      iAssert (⌜domm Rr = {[r]}⌝)%I as "%".
      { by iDestruct "HnS_si" as "(_&_&_&H')". }
      rename H into Domm_Rr.
      iAssert (⌜φ0 es Qr⌝ ∗ ⌜φ1 Br' Cr' Qr⌝ ∗ ⌜φ2 r Br' Ir⌝ 
        ∗ ⌜φ3 r Br' Rr⌝ ∗ ⌜φ4 r Rr⌝ ∗ ⌜φ5 Br' Qr⌝ 
        ∗ ⌜φ6 Br' (T+1)⌝ ∗ ⌜φ7 r es Rr Qr⌝)%I 
            with "[Hφ]" as "Hφ".
      { iDestruct "Hφ" as %Hφ. 
        destruct Hφ as [Hφ0 [Hφ1 [Hφ2 [Hφ3 [Hφ4 [Hφ5 [Hφ6 Hφ7]]]]]]].
        iPureIntro. repeat split; try done.
        - destruct (decide (k0 = k)).
          + subst k0. subst Cr' Br'.
            rewrite !lookup_insert. try done.
          + subst Cr' Br'. 
            rewrite !lookup_insert_ne; try done.
            by pose proof Hφ1 k0 as [H' _].
        - destruct (decide (k0 = k)).
          + subst k0. subst Cr' Br'.
            rewrite !lookup_insert.
            destruct Max_tsH1 as [_ H'].
            intros H''; inversion H''.
          + (* This is the cause of later admit *)
            subst Cr' Br'. 
            rewrite !lookup_insert_ne; try done.
            pose proof Hφ1 k0 as [_ H']. done.
        - intros k' t' Hins.
          pose proof Infz_Ir r as Infz_Ir.
          rewrite Infz_Ir in Hins.
          exfalso. clear -Hins. set_solver.
        - intros k'. right.
          apply (inset_monotone R1 Rr Ro); try done.
          by rewrite <-auth_auth_valid.
          pose proof Inf_R r k' as Inf_R.
          by rewrite <-beq_nat_refl in Inf_R.
          rewrite Domm_Rr. clear. set_solver.
        - intros k'. subst Br'. destruct (decide (k' = k)).
          + subst k'. rewrite lookup_total_insert.
            apply (Nat.le_trans _ (Br !!! k) _); try done.
          + rewrite lookup_total_insert_ne; try done.    
        - intros k'. destruct (decide (k' = k)).
          + subst k' Br'. rewrite lookup_total_insert; lia.
          + subst Br'. rewrite lookup_total_insert_ne; try done.
            pose proof Hφ6 k'. clear -H. 
            apply (Nat.le_trans _ T _); try done. lia. } 
      (** Linearization **)    
      iMod "AU" as (t' H')"[MCS [_ Hclose]]".
      iAssert (⌜t' = T⌝)%I as %Ht'. 
      { iPoseProof ((auth_agree γ_te) with "[MCS_auth] [MCS]") as "%".
        unfold MCS_auth. by iDestruct "MCS_auth" as "(H' & _)".
        by iDestruct "MCS" as "(H' & _)".
        by iPureIntro. } replace t'.
      iAssert (⌜H' = H1⌝)%I as %H1'.
      { iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
        unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
        by iDestruct "MCS" as "(_ & H')".
        by iPureIntro. } replace H'.
      iDestruct "MCS" as "(MCS◯t & MCS◯h)".
      iDestruct "MCS_auth" as "(MCS●t & MCS●h)".
      iMod ((auth_excl_update γ_te (T+1) T T) with "MCS●t MCS◯t") 
                                          as "(MCS●t & MCS◯t)".
      iMod ((auth_excl_update γ_he (H1 ∪ {[(k, T)]}) H1 H1) with "MCS●h MCS◯h") 
                                          as "(MCS●h & MCS◯h)".
      iCombine "MCS◯t MCS◯h" as "MCS".
      iCombine "MCS●t MCS●h" as "MCS_auth".
      iMod ("Hclose" with "MCS") as "HΦ".
      
      iModIntro.
      iSplitR "HΦ node_r HnP_gh HnP_t HnP_C HnP_frac".
      { iNext. iExists (T+1), (H1 ∪ {[(k, T)]}), hγ1, I1, R1.
        iFrame "∗ %".   
        rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
        iSplitR "Hstar'".
        { iExists true, Cr', Br', Qr. iFrame.
          iExists γ_er, γ_cr, γ_br, γ_qr, γ_cirr, es, Ir, Rr.
          iFrame "∗#". iEval (rewrite <-beq_nat_refl). 
          iFrame "%∗". }        
        iApply (big_sepS_mono 
                  (λ y, ∃ (bn : bool) (Cn Bn Qn : gmap K natUR),
                          lockLoc y ↦ #bn
                        ∗ (if bn then True
                           else nodePred γ_gh γ_t γ_s lc r y Cn Bn Qn)
                        ∗ nodeShared γ_I γ_R γ_f γ_gh r y Cn Bn Qn H1 T )%I
                  (λ y, ∃ (bn : bool) (Cn Bn Qn : gmap K natUR),
                          lockLoc y ↦ #bn
                        ∗ (if bn then True
                           else nodePred γ_gh γ_t γ_s lc r y Cn Bn Qn)
                        ∗ nodeShared γ_I γ_R γ_f γ_gh r y Cn Bn Qn 
                                                (H1 ∪ {[(k, T)]}) (T + 1))%I
                  (domm I1 ∖ {[r]})); try done.
        intros y y_dom. assert (y ≠ r) as Hy by set_solver. iFrame.
        iIntros "Hstar". iDestruct "Hstar" as (b C B Q)"(Hl & Hlif & HnS)".
        iExists b, C, B, Q. iFrame. 
        iDestruct "HnS" as (γ_e γ_c γ_b γ_q γ_cir esy Iy Ry)
                    "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
                              & HnS_cl & HnS_oc & HnS_if & HnS_star 
                              & Hφ0 & Hφ1 & Hφ2 & Hφ3 & Hφ4 & Hφ6 & Hφ7)".
        iExists γ_e, γ_c, γ_b, γ_q, γ_cir, esy, Iy, Ry. iFrame.
        iDestruct "Hφ6" as %Hφ6. 
        assert (y =? r = false) as Hyr by (rewrite beq_nat_false_iff; done).
        iEval (rewrite Hyr). iPureIntro. split; try done.
        intros k'. pose proof Hφ6 k'. 
        apply (Nat.le_trans _ T _); try done. lia. } 
      wp_pures. 
      (** Unlock node r **) 
      awp_apply (unlockNode_spec_high with "[] [] 
        [HnP_gh HnP_t HnP_C HnP_frac node_r]") without "HΦ"; try done. 
      iExists γ_er, γ_cr, γ_br, γ_qr, γ_cirr, es, (T + 1).
      iFrame. by iEval (rewrite <-beq_nat_refl).
      iAaccIntro with ""; try done.
      iIntros "_". iModIntro; iIntros "HΦ"; try done.
      Unshelve. try done.
  Qed.      
*)

    
