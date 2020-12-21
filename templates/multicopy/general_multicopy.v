From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multiset_flows auth_ext one_shot_proph typed_proph.

(** Declarations of implementation-specific helper functions **)

Variable inContents : val.
Variable findNext : val.
Variable lockLoc : Node → loc.
Variable getLockLoc: val.
Variable addContents: val.
Variable mergeContents: val.
Variable chooseNext: val.
Variable atCapacity: val.

(** Template algorithms *)

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
  
Definition search' (r: Node) : val :=
  λ: "k",
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "v" := search r "k" in
    resolve_proph: "p" to: "v";;
    "v".  
  
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

(* Keys and timestamps *)

Definition K := Z.
Definition KT : Type := K * nat.
Parameter KS : gset K.

Definition esT : Type := gmap Node (gset K).
Canonical Structure esRAC := leibnizO esT.

(* RAs used in proof *)

Definition prod5O A B C D E :=
  prodO (prodO (prodO (prodO A B) C) D) E.

Definition per_node_gl :=
    agreeR 
      (prod5O gnameO gnameO gnameO gnameO (gmapO K gnameO)).

Definition ghost_heapUR := gmapUR Node $ per_node_gl.  

Definition flow_KTR := authR (multiset_flowint_ur KT).
Definition flow_KR := authR (multiset_flowint_ur K).
Definition set_nodeR := authR (gsetUR Node).
Definition set_tidR := authR (gsetUR proph_id).
Definition frac_contR := frac_agreeR (gmapUR K natUR).
Definition frac_esR := frac_agreeR (esRAC).
Definition frac_histR := frac_agreeR (gsetUR KT).
Definition timeR := authR (max_natUR).
Definition histR := authR (gsetUR (KT)).
Definition hist_exclR := authR $ optionUR $ exclR (gsetO KT).
Definition time_exclR := authR $ optionUR $ exclR natUR.
Definition ghR := authR $ ghost_heapUR.
Definition tokenUR    := exclR unitO.


Class multicopyG Σ := MULTICOPY {
                        multicopy_flow_KTG :> inG Σ flow_KTR;
                        multicopy_flow_KG :> inG Σ flow_KR;
                        multicopy_set_nodeG :> inG Σ set_nodeR;
                        multicopy_set_tidG :> inG Σ set_tidR;
                        multicopy_frac_contG :> inG Σ frac_contR;
                        multicopy_frac_esG :> inG Σ frac_esR;
                        multicopy_frac_histG :> inG Σ frac_histR;
                        multicopy_timeG :> inG Σ timeR;
                        multicopy_histG :> inG Σ histR;
                        multicopy_hist_exclG :> inG Σ hist_exclR;
                        multicopy_time_exclG :> inG Σ time_exclR;
                        multicopy_ghG :> inG Σ ghR;
                        multicopy_tokenG :> inG Σ tokenUR;
                       }.

Definition multicopyΣ : gFunctors :=
  #[GFunctor flow_KTR; GFunctor flow_KR; GFunctor set_nodeR;
    GFunctor set_tidR; GFunctor frac_contR; GFunctor frac_esR; 
    GFunctor frac_histR; GFunctor timeR; GFunctor histR; 
    GFunctor hist_exclR; GFunctor time_exclR; GFunctor ghR; 
    GFunctor tokenUR ].

Instance subG_multicopyΣ {Σ} : subG multicopyΣ Σ → multicopyG Σ.
Proof. solve_inG. Qed.

Section multicopy.
  Context {Σ} `{!heapG Σ, !multicopyG Σ}.
(*  Context (N : namespace).*)
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  (** Assumptions on the implementation made by the template algorithms. *)

  (* The node predicate is specific to each template implementation. See GRASShopper files
     <TODO>.spl for the concrete definition. *)
  Parameter node : Node → Node → esT → (gmap K natUR) → iProp.

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ r n es C, Timeless (node r n es C).
  Global Instance node_timeless r n es C: Timeless (node r n es C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis are proved as a GRASShopper lemma in
   * <TODO>.spl *)
  Parameter node_sep_star: ∀ r n es C es' C',
    node r n es C ∗ node r n es' C' -∗ False.

  Parameter node_es_disjoint: ∀ r n es C,
    node r n es C -∗ ⌜∀ n1 n2, n1 ≠ n2 → es !!! n1 ∩ es !!! n2 = ∅⌝.  

  Parameter node_es_empty: ∀ r n es C,
    node r n es C -∗ ⌜es !!! r = ∅ ∧ es !!! n = ∅⌝.

  (** The multicopy structure invariant *)
  
  Definition inFP γ_f (n: Node) : iProp := own γ_f (◯ {[n]}).

  Definition closed γ_f (es: esT) : iProp := ∀ n, ⌜es !!! n  ≠ ∅⌝ → inFP γ_f n.

  Definition inflow_zero (I: multiset_flowint_ur KT) := ∀ n, inset KT I n = ∅. 

  Definition outflow_zero (I: multiset_flowint_ur KT) := out_map I = ∅. 

  Definition outflow_zero_R (I: multiset_flowint_ur K) := out_map I = ∅. 

  Definition inflow_R (R: multiset_flowint_ur K) r := 
    ∀ n k, k ∈ KS → if decide (n = r) then in_inset K k R n else ¬ in_inset K k R n. 

  Definition outflow_le_1 (I: multiset_flowint_ur KT) :=
    ∀ n kt, out I n !1 kt ≤ 1.

  Definition outflow_constraint_I (In: multiset_flowint_ur KT) (es: esT) 
                          (Qn: gmap K natUR) := 
    ∀ n' k t, k ∈ KS → ((k,t) ∈ outset KT In n' ↔ 
                          k ∈ es !!! n' ∧ (Qn !! k = Some t)).
                          
  Definition outflow_constraint_R (Rn: multiset_flowint_ur K) (es: esT) n := 
    ∀ n' k, k ∈ KS → (k ∈ outset K Rn n' ↔ k ∈ es !!! n' ∧ k ∈ inset K Rn n).

  Definition map_of_set (C: gset KT) : gmap K nat := 
              let f := λ (kt: KT) (M: gmap K nat), 
                         if (decide (M !!! kt.1 <= kt.2)) 
                         then (<[kt.1 := kt.2]> M : gmap K nat) else M in
              set_fold f (∅: gmap K nat) C.

  Definition set_of_map (C: gmap K nat) : gset KT := 
             let f := λ k t H, H ∪ {[(k,t)]} in
             map_fold f (∅: gset KT) C.

  (** ϕ_1 in the paper *)
  Definition φ0 (es: esT) (Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → ((∀ n', k ∉ es !!! n') → Qn !! k = None).

  (* This constraint is implicit in the paper. We track B_n 
     explicitly as ghost state here. That is the following 
     captures the definition of B_n in terms of C_n/Q_n given 
     in the paper. *)
  Definition φ1 (Bn Cn Qn: gmap K natUR) := 
              ∀ k t, k ∈ KS → ((Cn !! k = Some t → Bn !! k = Some t)
                 ∧ (Cn !! k = None → Bn !! k = Qn !! k)). 

  (** ϕ_2 in the paper *)
  Definition φ2 n (Bn: gmap K natUR) In := 
              ∀ k t, k ∈ KS → ((k,t) ∈ inset KT In n → Bn !!! k = t).

  (** ϕ_4 in the paper *)
  Definition φ3 n (Bn: gmap K natUR) Rn :=
              ∀ k, k ∈ KS → (Bn !! k = None ∨ k ∈ inset K Rn n).

  (** ϕ_5 in the paper *)
  Definition φ4 n (Rn: multiset_flowint_ur K) := 
              ∀ k, inf Rn n !1 k ≤ 1.

  (** ϕ_3 in the paper *)
  Definition φ5 (Bn Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → (Qn !!! k ≤ Bn !!! k).            

  Definition φ6 (Bn: gmap K natUR) (t: nat) := 
              ∀ k, k ∈ KS → (Bn !!! k ≤ t).
  
  Definition φ7 n (es: esT) (Rn: multiset_flowint_ur K) (Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → ((∃ n', k ∈ es !!! n') ∧ k ∈ inset K Rn n 
                          → k ∈ dom (gset K) Qn).              

  Definition φ8 (n: Node) (In: multiset_flowint_ur KT) := 
              ∀ kt, inf In n !1 kt ≤ 1.


  Definition maxTS (t: nat) (H: gset KT) := 
              (∀ (k: K) t', (k, t') ∈ H → t' < t) ∧ (t > 0).
  
  Definition f_merge (Cn: gmap K nat) (Es: gset K) (Cm: gmap K nat) := 
                    λ k o1 o2, 
                      if (decide (Cn !! k ≠ None)) then o1
                      else if (decide (k ∈ Es)) then o2 
                           else (None: option nat).
  
  Global Instance f_merge_diag_none Cn Es Cm k : DiagNone (f_merge Cn Es Cm k).
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

  Definition frac_ghost_state γ_en γ_cn γ_bn γ_qn (es: esT)
                                  (Cn Bn Qn: gmap K natUR): iProp :=
      own (γ_en) (to_frac_agree (1/2) (es))
    ∗ own (γ_cn) (to_frac_agree (1/2) (Cn))
    ∗ own (γ_bn) (to_frac_agree (1/2) (Bn))
    ∗ own (γ_qn) (to_frac_agree (1/2) (Qn)).

  Definition singleton_interfaces_ghost_state (γ_I γ_R: gname) (n: Node) 
                  (In: multiset_flowint_ur KT) (Rn: multiset_flowint_ur K) : iProp :=
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

  (** Predicate N_L in the paper *)
  Definition nodePred γ_gh γ_t γ_s lc r n (Cn Bn Qn : gmap K natUR) : iProp :=
    ∃ γ_en γ_cn γ_bn γ_qn γ_cirn es t,
      node r n es Cn
    ∗ own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})  
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ (if decide (n = r) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t else ⌜True⌝)%I.

  (** Predicate N_S in the paper *)
  Definition nodeShared (γ_I γ_R γ_f: gname) γ_gh r n 
          (Cn Bn Qn : gmap K natUR) H t: iProp :=
    ∃ γ_en γ_cn γ_bn γ_qn γ_cirn es In Rn,
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn  
    ∗ singleton_interfaces_ghost_state γ_I γ_R n In Rn 
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ outflow_constraints n In Rn es Qn
    ∗ (if decide (n = r) then ⌜Bn = map_of_set H⌝ ∗ ⌜inflow_zero In⌝ else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cirn !!! (k)) (● (MaxNat (Bn !!! k))))
    ∗ ⌜φ0 es Qn⌝ ∗ ⌜φ1 Bn Cn Qn⌝ ∗ ⌜φ2 n Bn In⌝ ∗ ⌜φ3 n Bn Rn⌝ 
    ∗ ⌜φ4 n Rn⌝ ∗ ⌜φ5 Bn Qn⌝ ∗ ⌜φ6 Bn t⌝ ∗ ⌜φ7 n es Rn Qn⌝ ∗ ⌜φ8 n In⌝. 

  (** Predicate G in the paper *)
  Definition global_state (γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr: gname) 
          (r: Node) (t: nat) (H: gset KT) 
          (hγ: gmap Node per_node_gl) (I: multiset_flowint_ur KT) 
          (R: multiset_flowint_ur K) : iProp :=
      MCS_auth γ_te γ_he t H
    ∗ own γ_s (● H) ∗ ⌜history_init H⌝
    ∗ own γ_fr (to_frac_agree (1/2) H)
    ∗ own γ_t (●{1/2} MaxNat t)
    ∗ own γ_I (● I) ∗ ⌜outflow_zero I⌝
    ∗ own γ_R (● R) ∗ ⌜outflow_zero_R R⌝ ∗ ⌜inflow_R R r⌝
    ∗ own γ_f (● domm I)
    ∗ own γ_gh (● hγ)
    ∗ inFP γ_f r
    ∗ ⌜maxTS t H⌝
    ∗ ⌜domm I = domm R⌝ ∗ ⌜domm I = dom (gset Node) hγ⌝.

  (** Invariant Inv in the paper *)
  Definition mcs γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r : iProp :=
    ∃ t (H: gset KT) hγ
      (I: multiset_flowint_ur KT) (R: multiset_flowint_ur K),
      global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr r t H hγ I R
    ∗ ([∗ set] n ∈ (domm I), ∃ (bn: bool) Cn Bn Qn, 
          lockLoc n ↦ #bn  
        ∗ (if bn then True else nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn)
        ∗ nodeShared γ_I γ_R γ_f γ_gh r n Cn Bn Qn H t)%I.  

  Global Instance mcs_timeless γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r :
    Timeless (mcs γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r).
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
    destruct (decide (x4 = r)); try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (x4 = r)); try apply _.
  Qed.

  Definition mcs_inv N1 γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r := 
    inv N1 (mcs γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r).

  (** Helping Inv **)

  Definition MCS_high (γ_te γ_he: gname) (t: nat) (M: gmap K nat) : iProp :=
    ∃ H, MCS γ_te γ_he t H ∗ ⌜map_of_set H = M⌝.  

  Definition pau N1 N2 thN γ_ce γ_he P (Q : val → iProp) k := 
    (▷ P -∗ ◇ AU << ∀ t M, MCS_high γ_ce γ_he t M >> @ ⊤ ∖ (↑N1 ∪ ↑N2 ∪ ↑thN), ∅
                 << ∃ (t': nat), MCS_high γ_ce γ_he t M ∗ ⌜M !!! k = t'⌝, 
                                                          COMM Q #t' >>)%I.


  Definition state_lin_pending (P: iProp) (H: gset KT) (k: K) (vp: nat) : iProp := 
    P ∗ ⌜(k, vp) ∉ H⌝.

  Definition state_lin_done (γ_tk: gname) (Q: val → iProp) 
                              (H: gset KT) (k: K) (vp : nat) : iProp := 
    (Q #vp ∨ own γ_tk (Excl ())) ∗ ⌜(k, vp) ∈ H⌝. 

  Definition get_op_state (γ_sy: proph_id → gname) (t_id: proph_id) 
                          γ_tk P Q H (k: K) (vp: nat) : iProp :=
                        own (γ_sy t_id) (to_frac_agree (1/2) H) 
                     ∗ (state_lin_pending P H k vp 
                        ∨ state_lin_done γ_tk Q H k vp).

  Definition registered (N1 N2 thN: namespace) (γ_sy: proph_id → gname) 
                            (γ_ce γ_he: gname) 
                            (H: gset KT) (t_id: proph_id) : iProp :=
    ∃ (P: iProp) (Q: val → iProp) (k: K) (vp: nat) (vt: val) (γ_tk: gname), 
        proph1 t_id vt
      ∗ own (γ_sy t_id) (to_frac_agree (1/2) H)
      ∗ □ pau N1 N2 thN γ_ce γ_he P Q k
      ∗ inv thN (∃ H, get_op_state γ_sy t_id γ_tk P Q H (k: K) (vp: nat)).

  Definition helping (N1 N2 thN: namespace) (γ_sy: proph_id → gname) 
                            (γ_ce γ_he γ_fr γ_td: gname) : iProp :=
    ∃ (H: gset KT) (TD: gset proph_id),
        own γ_fr (to_frac_agree (1/2) H)
      ∗ own γ_td (● TD)  
      ∗ ([∗ set] t_id ∈ TD, registered N1 N2 thN γ_sy γ_ce γ_he H t_id).
  
  Definition helping_inv (N1 N2 thN: namespace) (γ_sy: proph_id → gname) 
                            (γ_ce γ_he γ_fr γ_td: gname) : iProp :=
    inv N2 (helping N1 N2 thN γ_sy γ_ce γ_he γ_fr γ_td).   
  
  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper
   * (see <TODO>.spl *)
    
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
    iModIntro; done.
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

  Global Instance HnP_t_laterable (r n: Node) γ_t lc T : 
              Laterable (if decide (n = r) 
                         then own γ_t (●{1 / 2} MaxNat T) ∗ clock lc T 
                         else ⌜True⌝)%I.
  Proof.
    destruct (decide (n = r)); apply timeless_laterable; apply _.
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
             assert (m !!! k <= t') as Hm.
             { unfold lookup_total, finmap_lookup_total.
               destruct Hp as [_ [_ Hp]]. rewrite Hp.
               simpl. lia. }
             destruct (decide (m !!! k ≤ t')); try done.  
             by rewrite lookup_insert.      
          ** assert (t' = T ∨ t' < T) as Ht by lia. clear n. 
             exists T. destruct Hp as [Hp1 [Hp2 Hp3]].
             repeat split; first set_solver.
             intros t. rewrite elem_of_union.
             intros [Hv | Hv]. assert (t = t') by set_solver. 
             lia. pose proof Hp2 t Hv. lia. simpl.
             destruct Ht as [Ht | Ht].
             assert (m !!! k <= t') as Hm.
             { unfold lookup_total, finmap_lookup_total.
               rewrite Hp3. simpl. lia. }
             destruct (decide (m !!! k ≤ t')); try done.
             rewrite lookup_insert. by rewrite Ht.
             assert (m !!! k > t') as Hm.
             { unfold lookup_total, finmap_lookup_total.
               rewrite Hp3. simpl. lia. }
             destruct (decide (m !!! k ≤ t')); try done.  
             exfalso. lia.
        * exists t'. simpl. repeat split; first set_solver.
          intros t. rewrite elem_of_union. intros [Hv | Hv].
          assert (t = t') by set_solver. lia.
          destruct Hp as [Hp _]. 
          pose proof Hp t as Hp. set_solver.
          assert (m !!! k ≤ t') as Hm.
          { unfold lookup_total, finmap_lookup_total.
            destruct Hp as [_ Hp]. rewrite Hp. simpl; lia. }
          destruct (decide (m !!! k ≤ t')); try done.  
          by rewrite lookup_insert.
      + unfold P. unfold P in Hp.
        destruct Hp as [Hp | Hp].
        * destruct Hp as [T [Hp1 [Hp2 Hp3]]].
          left. exists T. repeat split; first set_solver.
          intros t Hkt. assert ((k,t) ∈ X) as Hx by set_solver.
          by pose proof Hp2 t Hx.
          simpl. 
          destruct (decide (m !!! k' <= t')). 
          rewrite lookup_insert_ne; try done. done.
        * destruct Hp as [Hp1 Hp2]. right.
          repeat split; first set_solver. simpl.   
          destruct (decide (m !!! k' <= t')). 
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
  

  Lemma flowint_update_result (γ: gname) (I I_n I_n': multiset_flowint_ur K) x :
    ⌜flowint_update_P (_) I I_n I_n' x⌝ ∗ own γ x -∗
    ∃ I', ⌜contextualLeq (_) I I'⌝
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

  Lemma flowint_update_result' (γ: gname) (I I_n I_n': multiset_flowint_ur KT) x :
    ⌜flowint_update_P (_) I I_n I_n' x⌝ ∗ own γ x -∗
    ∃ I', ⌜contextualLeq (_) I I'⌝
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

  Lemma lockNode_spec_high N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r n:
    ⊢ mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r -∗
        inFP γ_f n -∗
              <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑N
              <<< ∃ Cn Bn Qn, nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn, RET #() >>>.
  Proof.
    iIntros "#mcsInv #FP_n".
    iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iInv "mcsInv" as ">mcs". iDestruct "mcs" as (T H hγ I R) "(Hglob & Hstar)".
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & Ht & HI & Out_I & HR 
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
(*  
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
*)
  Lemma unlockNode_spec_high N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r n Cn Bn Qn:
    ⊢ mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh γ_fr lc r -∗
        inFP γ_f n -∗ nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn -∗
              <<< True >>>
                unlockNode #n    @ ⊤ ∖ ↑N
              <<< True, RET #() >>>.
  Proof.
    iIntros "#mcsInv #FP_n Hnp". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iInv "mcsInv" as ">mcs". iDestruct "mcs" as (T H hγ I R) "(Hglob & Hstar)".
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & HfrH & Ht & HI & Out_I & HR 
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
  

End multicopy.
