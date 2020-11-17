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
    if: ("t" ≠ #0) 
    then
      unlockNode "n";; "t"
    else
      match: (findNext "n" "k") with
        SOME "n'" => unlockNode "n" ;; "t_rec" "n'" "k"
      | NONE => unlockNode "n" ;; #0 end.
              
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
Definition hist_exclR := authR $ optionUR $ exclR (gsetUR KT).
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

  Definition inflow_R (R: inset_flowint_ur K) r := 
    ∀ n k, if n =? r then in_inset K k R n else ¬ in_inset K k R n. 

  Definition outflow_le_1 (I: KT_flowint_ur K) :=
    ∀ n kt, out I n !1 kt ≤ 1.

  Definition outflow_constraint_I (In: KT_flowint_ur K) (es: esT) 
                          (Qn: gmap K natUR) := 
    ∀ n' k t, (k,t) ∈ outset_KT In n' ↔ 
                          k ∈ es !!! n' ∧ (Qn !!! k = t).
                          
  Definition outflow_constraint_R (Rn: inset_flowint_ur K) (es: esT) n := 
    ∀ n' k, in_outset K k Rn n' ↔ k ∈ es !!! n' ∧ in_inset K k Rn n.

  Definition map_of_set (C: gset KT) : gmap K nat := 
              let f := λ (kt: KT) (M: gmap K nat), if (M !!! kt.1 <=? kt.2) 
                                 then (<[kt.1 := kt.2]> M : gmap K nat) else M in
              set_fold f (∅: gmap K nat) C.

  Definition set_of_map (C: gmap K nat) : gset KT := 
             let f := λ k t H, H ∪ {[(k,t)]} in
             map_fold f (∅: gset KT) C.

(*
  Definition φ0 (Bn: gmap K natUR) (T: nat) := 
              ∀ k, Bn !!! k ≤ T.  
*)

  Definition φ0 (es: esT) (Qn: gmap K natUR) :=
              ∀ k, (∀ n', k ∉ es !!! n') → Qn !!! k = 0.

  Definition φ1 (Bn Cn Qn: gmap K natUR) := 
              ∀ k, (Cn !!! k > 0 → Bn !!! k = Cn !!! k)
                 ∧ (Cn !!! k = 0 → Bn !!! k = Qn !!! k). 

  Definition φ2 r n (Bn: gmap K natUR) In := 
              ∀ k t, n ≠ r → (k,t) ∈ inset_KT In n → Bn !!! k = t.

  Definition φ3 n (Bn: gmap K natUR) Rn :=
              ∀ k, Bn !!! k = 0 ∨ in_inset K k Rn n.

  Definition φ4 n (Rn: inset_flowint_ur K) := 
              ∀ k, inf Rn n !1 k ≤ 1.
  
  Definition φ5 (es: esT) r :=
                es !!! r = ∅.            

  Definition φ6 (Bn: gmap K natUR) (t: nat) := 
              ∀ k, Bn !!! k ≤ t.  

  Definition maxTS (t: nat) (H: gset KT) := 
              (∀ (k: K) t', (k, t') ∈ H → t' < t) ∧ (t > 0).
  
  Definition merge (Cn: gmap K nat) (Es: gset K) (Cm: gmap K nat) 
                          : (gmap K nat) :=
             let f := λ k o1 o2, if (decide (Cn !!! k ≠ 0)) then Cn !! k
                                 else if (decide (k ∈ Es)) then Cm !! k 
                                      else None in
             gmap_imerge f Cn Cm.            

  Definition MCS_auth (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (● Excl' t) ∗ own γ_he (● Excl' H).

  Definition MCS (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (◯ Excl' t) ∗ own γ_he (◯ Excl' H).

  Definition frac_ghost_state γ_en γ_cn γ_bn γ_qn (n: Node) es 
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
  
  Definition history_init (H: gset KT) : iProp := ⌜∀ k, k ∈ KS → (k, 0) ∈ H⌝.

  Definition ghost_loc γ_en γ_cn γ_bn γ_qn (γ_cirn: gmap K gnameO) : per_node_gl := 
        to_agree (γ_en, γ_cn, γ_bn, γ_qn, γ_cirn).

  Definition nodePred γ_gh γ_t γ_s lc r n (Cn Bn Qn : gmap K natUR) : iProp :=
    ∃ γ_en γ_cn γ_bn γ_qn γ_cirn es t,
      node r n es Cn
    ∗ own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})  
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn n es Cn Bn Qn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ (if (n =? r) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t else ⌜True⌝)%I.

  Definition nodeShared (γ_I γ_R γ_f: gname) γ_gh r n 
          (Cn Bn Qn : gmap K natUR) H t: iProp :=
    ∃ γ_en γ_cn γ_bn γ_qn γ_cirn es In Rn,
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})
    ∗ ⌜dom (gset K) γ_cirn = KS⌝                          
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn n es Cn Bn Qn  
    ∗ singleton_interfaces_ghost_state γ_I γ_R n In Rn 
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ outflow_constraints n In Rn es Qn
    ∗ (if (n =? r) then ⌜Bn = map_of_set H⌝ else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cirn !!! (k)) (● (MaxNat (Bn !!! k))))
    ∗ ⌜φ0 es Qn⌝ ∗ ⌜φ1 Bn Cn Qn⌝ ∗ ⌜φ2 r n Bn In⌝ 
    ∗ ⌜φ3 n Bn Rn⌝ ∗ ⌜φ4 n Rn⌝ ∗ ⌜φ5 es r⌝ ∗ ⌜φ6 Bn t⌝. 

  Definition global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r t H 
          (hγ: gmap Node per_node_gl) (I: KT_flowint_ur K) 
          (R: inset_flowint_ur K) : iProp :=
      MCS_auth γ_te γ_he t H
    ∗ own γ_s (● H) ∗ (history_init H)
    ∗ own γ_t (●{1/2} MaxNat t)
    ∗ own γ_I (● I)
    ∗ own γ_R (● R) ∗ ⌜inflow_R R r⌝
    ∗ own γ_f (● domm I)
    ∗ own γ_gh (● hγ)
    ∗ inFP γ_f r
    ∗ ⌜maxTS t H⌝
    ∗ ⌜domm I = domm R⌝ ∗ ⌜domm I = dom (gset Node) hγ⌝.

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
  Proof. Admitted.

  Definition mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r := 
    inv N (mcs γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r).
  
  (** Helper functions Spec **)
    
  Lemma lockNode_spec_high γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r n:
    ⊢ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
        inFP γ_f n -∗
              <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑N
              <<< ∃ Cn Bn Qn, nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn, RET #() >>>.
  Proof.
  Admitted.

  Lemma unlockNode_spec_high γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r n Cn Bn Qn:
    ⊢ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
        inFP γ_f n -∗ nodePred γ_gh γ_t γ_s lc r n Cn Bn Qn -∗
              <<< True >>>
                unlockNode #n    @ ⊤ ∖ ↑N
              <<< True, RET #() >>>.
  Proof.
  Admitted.
  
  Parameter inContents_spec : ∀ r n es (Cn: gmap K natUR) (k: K),
     ⊢ ({{{ node r n es Cn }}}
           inContents #n #k
       {{{ (t: nat), RET #t; node r n es Cn ∗ ⌜Cn !!! k = t⌝ }}})%I.

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
           ∗ ⌜merge Cn (esn !!! m) Cm = merge Cn' (esn !!! m) Cm'⌝ }}})%I.

  (** Useful lemmas and definitions **)

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

  Lemma frac_eq γ_e γ_c γ_b γ_q n es Cn Bn Qn es' Cn' Bn' Qn' : 
              frac_ghost_state γ_e γ_c γ_b γ_q n es Cn Bn Qn -∗
                  frac_ghost_state γ_e γ_c γ_b γ_q n es' Cn' Bn' Qn' -∗ 
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

  Lemma frac_update γ_e γ_c γ_b γ_q n es Cn Bn Qn es' Cn' Bn' Qn' : 
              frac_ghost_state γ_e γ_c γ_b γ_q n es Cn Bn Qn ∗ 
                 frac_ghost_state γ_e γ_c γ_b γ_q n es Cn Bn Qn ==∗ 
                      frac_ghost_state γ_e γ_c γ_b γ_q n es' Cn' Bn' Qn' ∗ 
                        frac_ghost_state γ_e γ_c γ_b γ_q n es' Cn' Bn' Qn'.
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


  Lemma auth_update γ ys xs1 xs2 :
    own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.
  
  Lemma auth_update' (γ: gname) (ys xs1 xs2: gset KT) :
    own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { admit. }  
    (* { apply view_update, option_local_update, exclusive_local_update. } *)
    done.
  Admitted.

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

  (** Proofs **)  
  
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
    case_eq (bool_decide ((#t = #0))).
    - (** Case : k not in contents of n **)
      intros t_eq_0. wp_pures.
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
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR 
                & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
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
        iAssert (⌜(k, Qn !!! k) ∈ outset_KT In n1⌝)%I as %outflow_n_n1.
        { iDestruct "HnS_oc" as "(H' & _)".
          iDestruct "H'" as %H'. iPureIntro. 
          apply (H' n1 k (Qn !!! k)).
          repeat split; try done. }
        iAssert (⌜n1 ∈ domm I⌝)%I as %n_in_I.
        { iDestruct "Hglob" as "(_ & _ & _ & _ & _ & _ &_ & Hf & _)". 
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
                  "(HnS_gh1 & domm_γcir1 & HnS_frac1 & HnS_si1 & HnS_FP1 
                       & HnS_cl1 & HnS_oc1 & HnS_H1 & HnS_star1 & Hφ1)".
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
        iAssert (⌜n1 ≠ r⌝)%I as %n1_neq_r.
        { iDestruct "Hφ" as "(_ & _ & _ & _ & _ & %)".
          rename H1 into Hφ5. iPureIntro.
          destruct (decide (n1 = r)); try done.
          unfold φ5 in Hφ5. rewrite <-e in Hφ5.
          clear -Hφ5 k_in_es. set_solver. }      
        iAssert (⌜Bn1 !!! k = Qn !!! k⌝)%I as %Bn1_eq_Bn.
        { iDestruct "Hφ1" as "(_ & _ & % & _)". 
          rename H1 into Hφ2.
          by pose proof Hφ2 k (Qn !!! k) n1_neq_r inflow_n1. } 
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); 
                              last by eauto) in "HnS_star".
        iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
        iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
        { iPoseProof (own_valid_2 with "[$Hcirk_n] [$Hlb]") as "%".
          rename H1 into Valid_Bnt.
          apply auth_both_valid_discrete in Valid_Bnt.
          destruct Valid_Bnt as [H' _].
          apply max_nat_included in H'.
          simpl in H'. by iPureIntro. }
        iAssert (⌜Bn !!! k = Qn !!! k⌝)%I as %Bn_eq_Qn.
        { iDestruct "Hφ" as "(_ & % & _)". rename H1 into Hφ1.
          apply bool_decide_eq_true in t_eq_0.
          inversion t_eq_0 as [H''].
          pose proof Hφ1 k as [_ H'].
          iPureIntro. apply H'. rewrite Cn_val.
          clear -H''. lia. }  
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
        iAssert (own γ_gh (◯ {[n1 := 
                      ghost_loc γ_en1 γ_cn1 γ_bn1 γ_qn1 γ_cirn1]}))%I
                            with "HnS_gh1" as "#Hgh1".  
        (** Closing the invariant **)
        iModIntro. iSplitR "node_n HnP_gh HnP_frac HnP_C HnP_t AU". iNext.
        iExists T', H, hγ, I, R. iFrame "Hglob".
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n1); last set_solver.
        iFrame "Hstar''". iSplitL "Hl_n Hlif_n HnS_gh domm_γcir HnS_frac 
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
        iApply "IH"; try done. iPureIntro.
        rewrite Bn1_eq_Bn. rewrite <-Bn_eq_Qn.
        clear -lb_t1 t0_le_t1.
        apply (Nat.le_trans t0 t1 _); try done.
      + (** Case : no next node from n **)
        wp_pures. iDestruct "Hif" as %Not_in_es.
        iApply fupd_wp. 
        (** Linearization Point: key k has not been found in the 
            data structure. Open invariant to obtain resources 
            required to establish post-condition **)
        iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR 
                & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
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
          rewrite Hφ0 in H'. 
          iPureIntro. apply H'.
          apply bool_decide_eq_true in t_eq_0.
          inversion t_eq_0 as [H''].
          rewrite Cn_val.
          clear -H''. lia. }          
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
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR & Hf 
                & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
          unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
          by iDestruct "MCS" as "(_ & H')".
          by iPureIntro. } subst H'.
        iAssert (⌜(k,0) ∈ H⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR 
                & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
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
      intros t_eq_0. wp_pures.                                         
      iApply fupd_wp. 
      (** Linearization Point: key k has been found. Open 
          invariant to obtain resources required to 
          establish post-condition **)
      iInv "HInv" as ">H".
      iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
      iAssert (⌜n ∈ domm I⌝)%I as "%". 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR 
              & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iDestruct "Hstar" as "(H_n & Hstar')".
      iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
      iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                    "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
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
        pose proof Hφ1 k as [H' _].
        iPureIntro. apply H'.
        apply bool_decide_eq_false in t_eq_0.
        rewrite Cn_val.
        clear -t_eq_0. apply neq_0_lt. 
        unfold not. intros H'. 
        apply t_eq_0. apply f_equal. 
        rewrite <-H'. done. }          
      iAssert (⌜set_of_map Cn ⊆ H⌝)%I as %Cn_Sub_H.
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR 
              & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        iPoseProof ((auth_own_incl γ_s H _) with "[$HH $HnP_C]") as "%".
        rename H1 into H'. by apply gset_included in H'. }  
      iAssert (⌜(k,t) ∈ set_of_map Cn⌝)%I as %kt_in_Cn.
      { iPureIntro. apply set_of_map_member.
        rewrite /(Cn !!! k) in Cn_val.
        unfold finmap_lookup_total, inhabitant in Cn_val.
        simpl in Cn_val. 
        destruct (Cn !! k) as [cnk | ] eqn: Hcnk.
        - rewrite Hcnk. apply f_equal. 
          by simpl in Cn_val.
        - simpl in Cn_val.
          apply bool_decide_eq_false_1 in t_eq_0.
          exfalso. apply t_eq_0. replace t. try done. }
      (** Linearization **)      
      iMod "AU" as (t' H') "[MCS [_ Hclose]]". 
      iSpecialize ("Hclose" $! t).
      iAssert (⌜H' = H⌝)%I as %H1. 
      { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR 
              & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
        iPoseProof ((auth_agree' γ_he) with "[MCS_auth] [MCS]") as "%".
        unfold MCS_auth. by iDestruct "MCS_auth" as "(_ & H'')".
        by iDestruct "MCS" as "(_ & H')".
        by iPureIntro. } replace H'.
      iMod ("Hclose" with "[MCS]") as "HΦ". iFrame. 
      iPureIntro. split. set_solver. rewrite Bn_eq_Cn in lb_t1.
      rewrite Cn_val in lb_t1. lia.
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
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR & 
              Inf_R & Hf & Hγ & #FP_r & Max_ts & domm_IR & domm_Iγ)".
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
      iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & HR 
                & Inf_R & Hf & Hγ & _ & Max_ts & domm_IR & domm_Iγ)".
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
      iAssert (history_init (H1 ∪ {[(k, T)]})) with "[Hist]" as "Hist".
      { iDestruct "Hist" as %Hist.
        unfold history_init. iPureIntro.
        clear -Hist. set_solver. }  
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
                    "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
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
      iDestruct "HnS_if" as %Br_eq_H1.
      iAssert (⌜Br' = map_of_set (H1 ∪ {[(k, T)]})⌝)%I as %Br'_eq_H1.
      { iPureIntro.
        apply map_of_set_insert_eq; try done.
        intros t. 
        destruct Max_tsH1 as [Max_tsH1 _].
        by pose proof Max_tsH1 k t. }
      iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto) in "HnS_star".
      iDestruct "HnS_star" as "(Hk & HnS_star')".
      iAssert (⌜Br !!! k ≤ T⌝)%I as %Br_le_T. 
      { iDestruct "Hφ" as "(_&_&_&_&_&_&%)".
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
      iMod ((frac_update γ_er γ_cr γ_br γ_qr r es Cr Br Qr es Cr' Br' Qr) 
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
      iAssert (⌜φ0 es Qr⌝ ∗ ⌜φ1 Br' Cr' Qr⌝ ∗ ⌜φ2 r r Br' Ir⌝ 
        ∗ ⌜φ3 r Br' Rr⌝ ∗ ⌜φ4 r Rr⌝ ∗ ⌜φ5 es r⌝ ∗ ⌜φ6 Br' (T+1)⌝)%I 
            with "[Hφ]" as "Hφ".
      { iDestruct "Hφ" as %Hφ. 
        destruct Hφ as [Hφ0 [Hφ1 [Hφ2 [Hφ3 [Hφ4 [Hφ5 Hφ6]]]]]].
        iPureIntro. repeat split; try done.
        - destruct (decide (k0 = k)).
          + subst k0. subst Cr' Br'.
            rewrite !lookup_total_insert. try done.
          + subst Cr' Br'. 
            rewrite !lookup_total_insert_ne; try done.
            by pose proof Hφ1 k0 as [H' _].
        - destruct (decide (k0 = k)).
          + subst k0. subst Cr' Br'.
            rewrite !lookup_total_insert.
            destruct Max_tsH1 as [_ H'].
            intros H''; clear -H' H''; lia.
          + subst Cr' Br'. 
            rewrite !lookup_total_insert_ne; try done.
            by pose proof Hφ1 k0 as [_ H'].
        - intros k' t' Hr. clear -Hr. done.
        - intros k'. right.
          apply (inset_monotone R1 Rr Ro); try done.
          by rewrite <-auth_auth_valid.
          pose proof Inf_R r k' as Inf_R.
          by rewrite <-beq_nat_refl in Inf_R.
          rewrite Domm_Rr. clear. set_solver.
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
      iMod ((auth_update γ_te (T+1) T T) with "MCS●t MCS◯t") 
                                          as "(MCS●t & MCS◯t)".
      iMod ((auth_update' γ_he (H1 ∪ {[(k, T)]}) H1 H1) with "MCS●h MCS◯h") 
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
                              & Hφ0 & Hφ1 & Hφ2 & Hφ3 & Hφ4 & Hφ5 & Hφ6)".
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
      iAaccIntro with ""; try eauto with iFrame.
  Qed.      

    
