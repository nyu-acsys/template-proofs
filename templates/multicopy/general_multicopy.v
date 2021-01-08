From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy multicopy_util.

(** Declarations of implementation-specific helper functions **)

Parameter inContents : val.
Parameter findNext : val.
Parameter lockLoc : Node → loc.
Parameter getLockLoc: val.
Parameter addContents: val.
Parameter mergeContents: val.
Parameter chooseNext: val.
Parameter atCapacity: val.

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

(*  
Definition search' (r: Node) : val :=
  λ: "k",
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "v" := search r "k" in
    resolve_proph: "p" to: "v";;
    "v".  
*)
  
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
Definition frac_contR := frac_agreeR (gmapUR K natUR).
Definition frac_esR := frac_agreeR (esRAC).
Definition timeR := authR (max_natUR).
Definition ghR := authR $ ghost_heapUR.

Class gen_multicopyG Σ := GEN_MULTICOPY {
                            gen_multicopy_flow_KTG :> inG Σ flow_KTR;
                            gen_multicopy_flow_KG :> inG Σ flow_KR;
                            gen_multicopy_set_nodeG :> inG Σ set_nodeR;
                            gen_multicopy_frac_contG :> inG Σ frac_contR;
                            gen_multicopy_frac_esG :> inG Σ frac_esR;
                            gen_multicopy_timeG :> inG Σ timeR;
                            gen_multicopy_ghG :> inG Σ ghR;
                      }.

Definition gen_multicopyΣ : gFunctors :=
  #[GFunctor flow_KTR; GFunctor flow_KR; GFunctor set_nodeR;
    GFunctor frac_contR; GFunctor frac_esR; 
    GFunctor timeR; GFunctor ghR ].

Instance subG_gen_multicopyΣ {Σ} : subG gen_multicopyΣ Σ → gen_multicopyG Σ.
Proof. solve_inG. Qed.

Section gen_multicopy.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !gen_multicopyG Σ}.
(*   Context (N : namespace). *)
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
  
(*  Definition mcs_sr γ_s (kt: KT) : iProp := own γ_s (◯ {[kt]}).  *)

  Definition closed γ_f (es: esT) : iProp := ∀ n, ⌜es !!! n  ≠ ∅⌝ → inFP γ_f n.

  Definition inflow_zero (I: multiset_flowint_ur KT) := ∀ n, inset KT I n = ∅. 

  Definition outflow_zero (I: multiset_flowint_ur KT) := out_map I = ∅. 

  Definition outflow_zero_J (I: multiset_flowint_ur K) := out_map I = ∅. 

  Definition inflow_J (R: multiset_flowint_ur K) r := 
    ∀ n k, k ∈ KS → if decide (n = r) then in_inset K k R n else ¬ in_inset K k R n. 

  Definition outflow_le_1 (I: multiset_flowint_ur KT) :=
    ∀ n kt, out I n !1 kt ≤ 1.

  Definition outflow_constraint_I (In: multiset_flowint_ur KT) (es: esT) 
                          (Qn: gmap K natUR) := 
    ∀ n' k t, k ∈ KS → ((k,t) ∈ outset KT In n' ↔ 
                          k ∈ es !!! n' ∧ (Qn !! k = Some t)).
                          
  Definition outflow_constraint_J (Rn: multiset_flowint_ur K) (es: esT) n := 
    ∀ n' k, k ∈ KS → (k ∈ outset K Rn n' ↔ k ∈ es !!! n' ∧ k ∈ inset K Rn n).

(*
  Definition map_of_set (C: gset KT) : gmap K nat := 
              let f := λ (kt: KT) (M: gmap K nat), 
                         if (decide (M !!! kt.1 <= kt.2)) 
                         then (<[kt.1 := kt.2]> M : gmap K nat) else M in
              set_fold f (∅: gmap K nat) C.

  Definition set_of_map (C: gmap K nat) : gset KT := 
             let f := λ k t H, H ∪ {[(k,t)]} in
             map_fold f (∅: gset KT) C.
*)

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
  Definition φ3 n (Bn: gmap K natUR) Jn :=
              ∀ k, k ∈ KS → (Bn !! k = None ∨ k ∈ inset K Jn n).

  (** ϕ_5 in the paper *)
  Definition φ4 n (Jn: multiset_flowint_ur K) := 
              ∀ k, inf Jn n !1 k ≤ 1.

  (** ϕ_3 in the paper *)
  Definition φ5 (Bn Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → (Qn !!! k ≤ Bn !!! k).            

  (** extraneous *)
  Definition φ6 (Bn: gmap K natUR) (t: nat) := 
              ∀ k, k ∈ KS → (Bn !!! k ≤ t).
  
  (** simplify to dom Qn = out(es) ∩ inset Jn n 
      to combine φ0 and φ7, where
      out(es) = { k | ∃ n', k in es(n') }
      φ0 := dom Qn ⊆ out(es)
      φ7 := out(es) ∩ inset Jn n ⊆ dom Qn *)
  Definition φ7 n (es: esT) (Jn: multiset_flowint_ur K) (Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → ((∃ n', k ∈ es !!! n') ∧ k ∈ inset K Jn n 
                          → k ∈ dom (gset K) Qn).              

  Definition φ8 (n: Node) (In: multiset_flowint_ur KT) := 
              ∀ kt, inf In n !1 kt ≤ 1.

(*
  Definition maxTS (t: nat) (H: gset KT) := 
              (∀ (k: K) t', (k, t') ∈ H → t' < t) ∧ (t > 0).
*)
  
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

(*
  Definition MCS_auth (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (● Excl' t) ∗ own γ_he (● Excl' H).

  Definition MCS (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (◯ Excl' t) ∗ own γ_he (◯ Excl' H).
*)

  Definition frac_ghost_state γ_en γ_cn γ_bn γ_qn (es: esT)
                                  (Cn Bn Qn: gmap K natUR): iProp :=
      own (γ_en) (to_frac_agree (1/2) (es))
    ∗ own (γ_cn) (to_frac_agree (1/2) (Cn))
    ∗ own (γ_bn) (to_frac_agree (1/2) (Bn))
    ∗ own (γ_qn) (to_frac_agree (1/2) (Qn)).

  Definition singleton_interfaces_ghost_state (γ_I γ_J: gname) (n: Node) 
                  (In: multiset_flowint_ur KT) (Jn: multiset_flowint_ur K) : iProp :=
      own γ_I (◯ In)
    ∗ own γ_J (◯ Jn)
    ∗ ⌜domm In = {[n]}⌝
    ∗ ⌜domm Jn = {[n]}⌝.
    
  Definition outflow_constraints n In Jn es Qn : iProp :=
      ⌜outflow_constraint_I In es Qn⌝
    ∗ ⌜outflow_constraint_J Jn es n⌝
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
    ∗ (if decide (n = r) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t else True)%I.

  (** Predicate N_S in the paper *)
  Definition nodeShared (γ_I γ_J γ_f: gname) γ_gh r n 
          (Cn Bn Qn : gmap K natUR) H t: iProp :=
    ∃ γ_en γ_cn γ_bn γ_qn γ_cirn es In Jn,
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn  
    ∗ singleton_interfaces_ghost_state γ_I γ_J n In Jn 
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ outflow_constraints n In Jn es Qn
    ∗ (if decide (n = r) then ⌜Bn = map_of_set H⌝ ∗ ⌜inflow_zero In⌝ else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cirn !!! (k)) (● (MaxNat (Bn !!! k))))
    ∗ ⌜φ0 es Qn⌝ ∗ ⌜φ1 Bn Cn Qn⌝ ∗ ⌜φ2 n Bn In⌝ ∗ ⌜φ3 n Bn Jn⌝ 
    ∗ ⌜φ4 n Jn⌝ ∗ ⌜φ5 Bn Qn⌝ ∗ ⌜φ6 Bn t⌝ ∗ ⌜φ7 n es Jn Qn⌝ ∗ ⌜φ8 n In⌝. 

(*
  Definition mcs_inv_high γ_te γ_he γ_s γ_fr t H : iProp :=
      MCS_auth γ_te γ_he t H
    ∗ own γ_s (● H) ∗ ⌜history_init H⌝
    ∗ own γ_fr (to_frac_agree (1/2) H)
    ∗ ⌜maxTS t H⌝.
*)
  
  (* Remove H as parameter *)  
  (** Predicate G in the paper *)
  Definition global_state (γ_t γ_I γ_J γ_f γ_gh: gname) 
          (r: Node) (t: nat) (H: gset KT) 
          (hγ: gmap Node per_node_gl) (I: multiset_flowint_ur KT) 
          (R: multiset_flowint_ur K) : iProp :=
      own γ_t (●{1/2} MaxNat t)
    ∗ own γ_I (● I) ∗ ⌜outflow_zero I⌝
    ∗ own γ_J (● R) ∗ ⌜outflow_zero_J R⌝ ∗ ⌜inflow_J R r⌝
    ∗ own γ_f (● domm I)
    ∗ own γ_gh (● hγ)
    ∗ inFP γ_f r
    ∗ ⌜domm I = domm R⌝ 
    ∗ ⌜domm I = dom (gset Node) hγ⌝.

  Definition mcs_conc γ_s γ_t γ_I γ_J γ_f γ_gh lc r t H : iProp :=
    ∃ hγ
      (I: multiset_flowint_ur KT) (R: multiset_flowint_ur K),
      global_state γ_t γ_I γ_J γ_f γ_gh r t H hγ I R
    ∗ ([∗ set] n ∈ (domm I), ∃ (bn: bool) Cn Bn Qn, 
          lockLoc n ↦ #bn  
        ∗ (if bn then True else nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn)
        ∗ nodeShared γ_I γ_J γ_f γ_gh r n Cn Bn Qn H t)%I.  

  Global Instance mcs_conc_timeless γ_s γ_t γ_I γ_J γ_f γ_gh lc r t H:
    Timeless (mcs_conc γ_s γ_t γ_I γ_J γ_f γ_gh lc r t H).
  Proof.
    rewrite /mcs_conc.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    apply big_sepS_timeless.
    repeat (intros; apply bi.exist_timeless; intros).
    apply bi.sep_timeless; try apply _.
    destruct x3; try apply _.    
    repeat apply bi.sep_timeless; try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (x2 = r)); try apply _.
    repeat apply bi.sep_timeless; try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (x2 = r)); try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (x2 = r)); try apply _.
  Qed.

(*
  Definition mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr lc r := 
    inv (mcsN N) (mcs γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr lc r).

  (** Helping Inv **)

  Definition helping (N: namespace) (γ_fr: gname) 
                      (protocol_abs : gset KT → iProp) : iProp :=
      ∃ (H: gset KT),  
        own γ_fr (to_frac_agree (1/2) H)
      ∗ protocol_abs H.
  
  Definition helping_inv N γ_fr protocol_abs : iProp :=
    inv (helpN N) (helping N γ_fr protocol_abs).
  
  Definition pau N γ_te γ_he P (Q : val → iProp) k := 
    (▷ P -∗ ◇ AU << ∀ t H, MCS γ_te γ_he t H >> 
                  @ ⊤ ∖ (↑(mcsN N) ∪ ↑(helpN N) ∪ ↑(threadN N)), ∅
                 << ∃ (t': nat), MCS γ_te γ_he t H ∗ ⌜map_of_set H !!! k = t'⌝, 
                                                          COMM Q #t' >>)%I.


  Definition state_lin_pending (P: iProp) (H: gset KT) (k: K) (vp: nat) : iProp := 
    P ∗ ⌜(k, vp) ∉ H⌝.

  Definition state_lin_done (γ_tk: gname) (Q: val → iProp) 
                              (H: gset KT) (k: K) (vp : nat) : iProp := 
    (Q #vp ∨ own γ_tk (Excl ())) ∗ ⌜(k, vp) ∈ H⌝. 

  Definition get_op_state γ_sy (t_id: proph_id) 
                          γ_tk P Q H (k: K) (vp: nat) : iProp :=
                        own γ_sy (to_frac_agree (1/2) H) 
                     ∗ (state_lin_pending P H k vp 
                        ∨ state_lin_done γ_tk Q H k vp).

  Definition registered (N: namespace) (γ_te γ_he γ_ght: gname) 
                            (H: gset KT) (t_id: proph_id) : iProp :=
    ∃ (P: iProp) (Q: val → iProp) (k: K) (vp: nat) (vt: val) (γ_tk γ_sy: gname), 
        proph1 t_id vt
      ∗ own γ_ght (◯ {[t_id := to_agree γ_sy]})  
      ∗ own (γ_sy) (to_frac_agree (1/2) H)
      ∗ □ pau N γ_te γ_he P Q k
      ∗ inv (threadN N) (∃ H, get_op_state γ_sy t_id γ_tk P Q H (k: K) (vp: nat)).

  Definition protocol_conc (N: namespace) (γ_te γ_he γ_fr γ_td γ_ght: gname) 
                                        (H: gset KT) : iProp :=
    ∃ (TD: gset proph_id) (hγt: gmap proph_id (agreeR gnameO)),
        own γ_td (● TD)
      ∗ own γ_ght (● hγt) ∗ ⌜dom (gset proph_id) hγt = TD⌝  
      ∗ ([∗ set] t_id ∈ TD, registered N γ_te γ_he γ_ght H t_id).

  Definition MCS_high N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr 
                      lc r γ_td γ_ght t M : iProp :=
  ∃ H, MCS γ_te γ_he t H ∗ ⌜map_of_set H = M⌝
     ∗ mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh γ_fr lc r
     ∗ helping_inv N γ_fr (protocol_conc N γ_te γ_he γ_fr γ_td γ_ght).      

  Definition ghost_update_protocol N γ_te γ_he protocol_abs k : iProp :=
        (∀ H T, ⌜map_of_set (H ∪ {[k, T]}) !!! k = T⌝ -∗  
                MCS_auth γ_te γ_he (T+1) (H ∪ {[(k, T)]}) -∗ 
                  protocol_abs H ={⊤ ∖ ↑mcsN N ∖ ↑helpN N}=∗
                    protocol_abs (H ∪ {[(k, T)]}) 
                      ∗ MCS_auth γ_te γ_he (T+1) (H ∪ {[(k, T)]})).
*)  
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

End gen_multicopy.
