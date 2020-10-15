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
(*Variable readClock: val.
Variable incrementClock: val.*)
Variable addContents: val.
Variable set_next: val.
Variable merge_contents: val.
Variable allocNode: val.

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
    if: ("t" ≠ #0%nat)%nat 
    then
      unlockNode "n";; "t"
    else
      match: (findNext "n" "k") with
        SOME "n'" => unlockNode "n" ;; "t_rec" "n'" "k"
      | NONE => unlockNode "n" ;; #0 end.
              
Definition search (r: Node) : val := 
  λ: "k", traverse #r "k".
  
Definition readClock : val :=
  λ: "", "".
  
Definition incrementClock : val :=
  λ: "", "".  

Definition upsert (r: Node) : val :=
  rec: "upsert_rec" "k" := 
    lockNode #r ;;
    let: "t" := readClock #() in
    let: "res" := addContents #r "k" "t" in
    if: "res" then 
      incrementClock #();;
      unlockNode #r
    else
      unlockNode #r;;
      "upsert_rec" "k".


(** Proof setup **)

Definition K := Z.
Definition KT := @KT K.
Parameter KS : gset K.

Definition esT : Type := gmap Node (gset K).
Canonical Structure esRAC := leibnizO esT.

Definition contR := frac_agreeR (gmapUR K natUR).
Definition flow_KTR := authR (KT_flowint_ur K).
Definition flow_KR := authR (inset_flowint_ur K).
Definition setR := authR (gsetUR Node).
Definition esR := frac_agreeR (esRAC).
Definition timeR := authR (max_natUR).
Definition histR := authR (gsetUR (KT)).
Definition hist_exclR := authR $ optionUR $ exclR (gsetUR KT).
Definition time_exclR := authR $ optionUR $ exclR natUR.

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
                       }.

Definition multicopyΣ : gFunctors :=
  #[GFunctor contR; GFunctor flow_KTR; GFunctor flow_KR; GFunctor setR; 
    GFunctor esR; GFunctor timeR; GFunctor histR; GFunctor hist_exclR; 
    GFunctor time_exclR ].

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


  Definition out_edgeset_list (k: K) (esl : list (Node * gset K)) :=             
    list_find (λ ns, k ∈ ns.2) esl.

  Definition out_edgeset (k: K) (es: esT) : bool := 
    match (out_edgeset_list k (map_to_list es)) with
    | None => false
    | _ => true end.

  Lemma out_edgeset_true k : ∀ es, out_edgeset k es = true → ∃ n, k ∈ es !!! n.
  Proof.
    intros es Hes.
    unfold out_edgeset in Hes.
    destruct (out_edgeset_list k (map_to_list es)) 
      as [ (i, (n,s)) | ] eqn: E; try inversion Hes.
    unfold out_edgeset_list in E.
    rewrite list_find_Some in E *; intros E.
    destruct E as [E1 [E2 _]].
    simpl in E2. apply elem_of_list_lookup_2 in E1.
    apply elem_of_map_to_list in E1.
    exists n. rewrite /(es !!! n). 
    unfold finmap_lookup_total. rewrite E1. by simpl.
  Qed.
      
  Lemma out_edgeset_false k : ∀ es, out_edgeset k es = false → ∀ n, k ∉ es !!! n.
  Proof.
    intros es Hes n.
    unfold out_edgeset in Hes.
    destruct (out_edgeset_list k (map_to_list es)) 
      as [ p | ] eqn: E; try inversion Hes.
    unfold out_edgeset_list in E.
    rewrite list_find_None in E *; intros E.
    rewrite Forall_forall in E *; intros E.
    rewrite /(es !!! n). 
    unfold finmap_lookup_total.
    destruct (es !! n) eqn:F.
    - rewrite F. simpl.
      rewrite <-(elem_of_map_to_list es n g) in F.
      pose proof E (n, g) F as E. by simpl in E.
    - rewrite F. simpl. set_solver.
  Qed.    

  Definition inFP γ_f (n: Node) : iProp := own γ_f (◯ {[n]}).

  Definition closed γ_f (es: esT) : iProp := ∀ n, ⌜es !!! n  ≠ ∅⌝ → inFP γ_f n.

  Definition inflow_zero (I: KT_flowint_ur K) : iProp := ⌜∀ n, inset_KT I n = ∅⌝. 

  Definition inflow_R (R: inset_flowint_ur K) r : iProp := 
    ⌜∀ n k, if n =? r then in_inset K k R n else ¬ in_inset K k R n⌝. 

  Definition outflow_constraint_I (In: KT_flowint_ur K) (es: esT) 
                          (Cn Bn: gmap K natUR) : iProp := 
    ⌜∀ n' k t, (k,t) ∈ outset_KT In n' ↔ 
                          k ∈ es !!! n' ∧ (Cn !!! k = 0) ∧ (Bn !!! k = t)⌝.

  Definition outflow_constraint_J (Jn: KT_flowint_ur K) (es: esT) 
                          (Cn Bn: gmap K natUR) : iProp := 
    ⌜∀ n' k t, (k,t) ∈ outset_KT Jn n' ↔ 
                          k ∈ es !!! n' ∧ (Cn !!! k = t)⌝.

  Definition outflow_constraint_R (Rn: inset_flowint_ur K) (es: esT) n : iProp := 
    ⌜∀ n' k, in_outset K k Rn n' ↔ k ∈ es !!! n' ∧ in_inset K k Rn n⌝.

  Definition map_of_set : gset KT → gmap K nat.
  Proof. Admitted.

  Definition set_of_map : gmap K nat → gset KT.
  Proof. Admitted.

  Definition φ1 (Bn Cn: gmap K natUR) (In: KT_flowint_ur K) : iProp := 
              ⌜∀ k, out_KT In k ∨ (Bn !!! k = Cn !!! k)⌝.

  Definition φ2 n (Bn: gmap K natUR) In : iProp := 
              ⌜∀ k t, (k,t) ∈ inset_KT In n → Bn !!! k = t⌝.

  Definition φ3 n (Bn: gmap K natUR) Jn : iProp :=
              ⌜∀ k t, (k,t) ∈ inset_KT Jn n → Bn !!! k ≤ t⌝.

  Definition φ4 n (Bn: gmap K natUR) Rn : iProp :=
              ⌜∀ k, Bn !! k = None ∨ in_inset K k Rn n⌝.

  Definition φ5 n (Rn: inset_flowint_ur K) : iProp := ⌜∀ k, inf Rn n !1 k ≤ 1⌝.

  Definition maxTS (t: nat) (H: gset KT) : iProp := 
              ⌜∀ (k: K) t', (k, t') ∈ H → t' < t⌝.

  Definition MCS_auth (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (● Excl' t) ∗ own γ_he (● Excl' H).

  Definition MCS (γ_te γ_he: gname) (t: nat) (H: gset KT) : iProp := 
      own γ_te (◯ Excl' t) ∗ own γ_he (◯ Excl' H).

  Definition frac_ghost_state γ_e γ_c γ_b (n: Node) es 
                                  (Cn Bn: gmap K natUR): iProp :=
      own (γ_e(n)) (to_frac_agree (1/2) (es))
    ∗ own (γ_c(n)) (to_frac_agree (1/2) (Cn))
    ∗ own (γ_b(n)) (to_frac_agree (1/2) (Bn)).

  Definition singleton_interfaces_ghost_state γ_I γ_J γ_R n 
                  (In Jn: KT_flowint_ur K) (Rn: inset_flowint_ur K) : iProp :=
      own γ_I (◯ In)
    ∗ own γ_J (◯ Jn)
    ∗ own γ_R (◯ Rn)
    ∗ ⌜domm In = {[n]}⌝
    ∗ ⌜domm Jn = {[n]}⌝
    ∗ ⌜domm Rn = {[n]}⌝.
    
  Definition outflow_constraints n In Jn Rn es Cn Bn : iProp :=
      outflow_constraint_I In es Cn Bn
    ∗ outflow_constraint_J Jn es Cn Bn
    ∗ outflow_constraint_R Rn es n.
      
  Definition nodePred γ_e γ_c γ_b γ_t γ_s r n (Cn Bn : gmap K natUR) : iProp :=
    ∃ es t,
      node r n es Cn
    ∗ frac_ghost_state γ_e γ_c γ_b n es Cn Bn 
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ (if (n =? r) then own γ_t (●{1/2} MaxNat t) else ⌜True⌝)%I.

  Definition nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir
                              r n (Cn Bn : gmap K natUR) H : iProp :=
    ∃ es In Jn Rn,                          
      frac_ghost_state γ_e γ_c γ_b n es Cn Bn    
    ∗ singleton_interfaces_ghost_state γ_I γ_J γ_R n In Jn Rn
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ outflow_constraints n In Jn Rn es Cn Bn
    ∗ (if (n =? r) then ⌜Bn = map_of_set H⌝ ∗ inflow_zero In ∗ inflow_zero Jn 
                   else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cir n k) (● (MaxNat (Bn !!! k))))
    ∗ φ1 Bn Cn In ∗ φ2 n Bn In 
    ∗ φ3 n Bn Jn ∗ φ4 n Bn Rn ∗ φ5 n Rn. 
    
  Definition global_state γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f r t H I J R : iProp :=
      MCS_auth γ_te γ_he t H
    ∗ own γ_s (● H)
    ∗ own γ_t (●{1/2} MaxNat t)
    ∗ own γ_I (● I)
    ∗ own γ_J (● J)
    ∗ own γ_R (● R)
    ∗ own γ_f (● domm I)
    ∗ inflow_zero I ∗ inflow_zero J ∗ inflow_R R r
    ∗ inFP γ_f r
    ∗ maxTS t H
    ∗ ⌜domm I = domm J⌝ ∗ ⌜domm I = domm R⌝.
       
  Definition mcs γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r : iProp :=
    ∃ t (H: gset KT) (I J: KT_flowint_ur K) (R: inset_flowint_ur K),
      global_state γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f r t H I J R
    ∗ ([∗ set] n ∈ (domm I), ∃ (bn: bool) Cn Bn, 
          lockLoc n ↦ #bn
        ∗ (if bn then True else nodePred γ_e γ_c γ_b γ_t γ_s r n Cn Bn)
        ∗ nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir r n Cn Bn H)%I.  

  Instance mcs_timeless γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r :
    Timeless (mcs γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r).
  Proof. Admitted.

  Definition mcs_inv γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r := 
    inv N (mcs γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r).

  (** Helper functions Spec **)

  Lemma lockNode_spec (n: Node):
    ⊢ <<< ∀ (b: bool), (lockLoc n) ↦ #b >>>
      lockNode #n    @ ⊤
    <<< (lockLoc n) ↦ #true ∗ ⌜b = false⌝ , RET #() >>>.
  Proof.
  Admitted.

  Lemma unlockNode_spec (n: Node) :
    ⊢ <<< lockLoc n ↦ #true >>>
      unlockNode #n    @ ⊤
    <<< lockLoc n ↦ #false, RET #() >>>.
  Proof.
  Admitted.

  Lemma lockNode_spec_high γ_te γ_he γ_s γ_t γ_I γ_J γ_R 
                                      γ_f γ_e γ_c γ_b γ_cir r n:
    ⊢ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r -∗
        inFP γ_f n -∗
              <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑N
              <<< ∃ Cn Bn, nodePred γ_e γ_c γ_b γ_t γ_s r n Cn Bn, RET #() >>>.
  Proof.
  Admitted.

  Lemma unlockNode_spec_high γ_te γ_he γ_s γ_t γ_I γ_J γ_R 
                                        γ_f γ_e γ_c γ_b γ_cir r n Cn Bn:
    ⊢ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r -∗
        inFP γ_f n -∗ nodePred γ_e γ_c γ_b γ_t γ_s r n Cn Bn -∗
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

  Parameter readClock_spec: ∀ γ_t q t, 
     ⊢ ({{{ own γ_t (●{q} MaxNat t) }}}
           readClock #()
       {{{ RET #t; own γ_t (●{q} MaxNat t) }}})%I.

  Parameter incrementClock_spec: ∀ γ_t t, 
     ⊢ (<<< own γ_t (● MaxNat t) >>>
           incrementClock #() @ ⊤
       <<< own γ_t (● MaxNat (t+1)), RET #() >>>)%I.

  Parameter addContents_spec : ∀ r es (Cn: gmap K natUR) (k: K) (t:nat),
     ⊢ ({{{ node r r es Cn }}}
           addContents #r #k #t
       {{{ (succ: bool) (Cn': gmap K natUR),
              RET #succ;
                  node r r es Cn' ∗ if succ then ⌜Cn' = <[k := t]> Cn⌝ 
                                else ⌜Cn' = Cn⌝ }}})%I.

  (** Useful lemmas and definitions **)

  Instance test r n γ_t T : Laterable (if n =? r then 
                                            own γ_t (●{1 / 2} T) else ⌜True⌝)%I.
  Proof. Admitted.

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
  
  Lemma frac_eq γ_e γ_c γ_b n es Cn Bn es' Cn' Bn' : 
              frac_ghost_state γ_e γ_c γ_b n es Cn Bn -∗
                  frac_ghost_state γ_e γ_c γ_b n es' Cn' Bn'-∗ 
                    ⌜es = es'⌝ ∗ ⌜Cn = Cn'⌝ ∗ ⌜Bn = Bn'⌝.
  Proof.
    iIntros "H1 H2". unfold frac_ghost_state.
    iDestruct "H1" as "(H1_es & H1_c & H1_b)".
    iDestruct "H2" as "(H2_es & H2_c & H2_b)".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_es] [$H2_es]") as "Hes".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_c] [$H2_c]") as "Hc".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_b] [$H2_b]") as "Hb".
    iDestruct "Hes" as %Hes. iDestruct "Hc" as %Hc. iDestruct "Hb" as %Hb.
    apply frac_agree_op_valid in Hes. destruct Hes as [_ Hes].
    apply frac_agree_op_valid in Hc. destruct Hc as [_ Hc].
    apply frac_agree_op_valid in Hb. destruct Hb as [_ Hb].
    apply leibniz_equiv_iff in Hes.
    apply leibniz_equiv_iff in Hc. 
    apply leibniz_equiv_iff in Hb.
    iPureIntro. repeat split; try done.   
  Qed.

  Lemma frac_update γ_e γ_c γ_b r es Cr Br es' Cr' Br' : 
              frac_ghost_state γ_e γ_c γ_b r es Cr Br ∗ 
                 frac_ghost_state γ_e γ_c γ_b r es Cr Br ==∗ 
                      frac_ghost_state γ_e γ_c γ_b r es' Cr' Br' ∗ 
                        frac_ghost_state γ_e γ_c γ_b r es' Cr' Br'.
  Proof.
    iIntros "(H1 & H2)". 
    iDestruct "H1" as "(H1_es & H1_c & H1_b)".
    iDestruct "H2" as "(H2_es & H2_c & H2_b)".
    iCombine "H1_es H2_es" as "Hes". 
    iEval (rewrite <-frac_agree_op) in "Hes". 
    iEval (rewrite Qp_half_half) in "Hes". 
    iCombine "H1_c H2_c" as "Hc". 
    iEval (rewrite <-frac_agree_op) in "Hc". 
    iEval (rewrite Qp_half_half) in "Hc". 
    iCombine "H1_b H2_b" as "Hb". 
    iEval (rewrite <-frac_agree_op) in "Hb". 
    iEval (rewrite Qp_half_half) in "Hb".
    iMod ((own_update (γ_e r) (to_frac_agree 1 es) 
                  (to_frac_agree 1 es')) with "[$Hes]") as "Hes".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hes".
    iEval (rewrite frac_agree_op) in "Hes".  
    iDestruct "Hes" as "(H1_es & H2_es)".            
    iMod ((own_update (γ_c r) (to_frac_agree 1 Cr) 
                  (to_frac_agree 1 Cr')) with "[$Hc]") as "Hc".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hc".
    iEval (rewrite frac_agree_op) in "Hc".  
    iDestruct "Hc" as "(H1_c & H2_c)".
    iMod ((own_update (γ_b r) (to_frac_agree 1 Br) 
                  (to_frac_agree 1 Br')) with "[$Hb]") as "Hb".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hb".
    iEval (rewrite frac_agree_op) in "Hb".  
    iDestruct "Hb" as "(H1_b & H2_b)".
  iModIntro. iFrame.
  Qed.

  Definition outflow_insert_KT (I : KT_flowint_ur K) (n: Node) 
                              (k: K) (t: nat) :KT_flowint_ur K := 
             let I_out_n := ((nzmap_imerge 
                         (λ k' a1 _, if (decide (k' = (k, t))) then 1 else a1)
                         (out I n) (∅)): (KT_multiset)) in
             let I'_out := ((nzmap_imerge 
                          (λ k' a1 _, if (decide (k = n)) then I_out_n else a1)
                          (out_map I) (∅)) : (nzmap Node KT_multiset)) in
             (int {| infR := inf_map I ; outR := I'_out |}).              

  Definition outflow_delete_KT (I : KT_flowint_ur K) (n: Node) 
                              (k: K) (t: nat) :KT_flowint_ur K := 
             let I_out_n := ((nzmap_imerge 
                         (λ k' a1 _, if (decide (k' = (k, t))) then 0 else a1)
                         (out I n) (∅)): (KT_multiset)) in
             let I'_out := ((nzmap_imerge 
                          (λ k' a1 _, if (decide (k = n)) then I_out_n else a1)
                          (out_map I) (∅)) : (nzmap Node KT_multiset)) in
             (int {| infR := inf_map I ; outR := I'_out |}).

  Lemma outflow_insert_outset_KT I n k t I' :
        I' = outflow_insert_KT I n k t → 
           ∀ n', (n' = n → outset_KT I' n' = (outset_KT I n') ∪ {[(k,t)]})
               ∧ (n' ≠ n → outset_KT I' n' = outset_KT I n').
  Proof.
  Admitted.

  Lemma outflow_delete_outset_KT I n k t I' :
        I' = outflow_delete_KT I n k t → 
           ∀ n', (n' = n → outset_KT I' n' = (outset_KT I n') ∖ {[(k,t)]})
               ∧ (n' ≠ n → outset_KT I' n' = outset_KT I n').
  Proof.
  Admitted.

  Definition inflow_insert_KT (I : KT_flowint_ur K) (n: Node) 
                              (k: K) (t: nat) :KT_flowint_ur K := 
             let I_inf_n := ((nzmap_imerge 
                         (λ k' a1 _, if (decide (k' = (k, t))) then 1 else a1)
                         (inf I n) (∅)): (KT_multiset)) in
             let I'_inf := (<[ n := I_inf_n ]>(inf_map I):(gmap Node KT_multiset)) in
             (int {| infR := I'_inf ; outR := out_map I |}).              

  Definition inflow_delete_KT (I : KT_flowint_ur K) (n: Node) 
                              (k: K) (t: nat) :KT_flowint_ur K := 
             let I_inf_n := ((nzmap_imerge 
                         (λ k' a1 _, if (decide (k' = (k, t))) then 0 else a1)
                         (inf I n) (∅)): (KT_multiset)) in
             let I'_inf := (<[ n := I_inf_n ]>(inf_map I):(gmap Node KT_multiset)) in
             (int {| infR := I'_inf ; outR := out_map I |}).           

  Lemma inflow_insert_outset_KT I n k t I' :
        I' = inflow_insert_KT I n k t → 
           ∀ n', (n' = n → inset_KT I' n' = (inset_KT I n') ∪ {[(k,t)]})
               ∧ (n' ≠ n → inset_KT I' n' = inset_KT I n').
  Proof.
  Admitted.

  Lemma inflow_delete_outset_KT I n k t I' :
        I' = inflow_delete_KT I n k t → 
           ∀ n', (n' = n → inset_KT I' n' = (inset_KT I n') ∖ {[(k,t)]})
               ∧ (n' ≠ n → inset_KT I' n' = inset_KT I n').
  Proof.
  Admitted.


  Lemma inflow_insert_domm I n k t I' : 
        I' = inflow_insert_KT I n k t → domm I' = domm I.
  Proof.
  Admitted.

  Lemma inflow_delete_domm I n k t I' : 
        I' = inflow_delete_KT I n k t → domm I' = domm I.
  Proof.
  Admitted.

  Lemma flow_delete_eq_KT I1 I1' I2 I2' n k t :
        I1' = outflow_delete_KT I1 n k t →
          I2' = inflow_delete_KT I2 n k t →
            I1 ⋅ I2 = I1' ⋅ I2'.
  Proof.
  Admitted.    

  Lemma flow_insert_eq_KT I1 I1' I2 I2' n k t :
        I1' = outflow_insert_KT I1 n k t →
          I2' = inflow_insert_KT I2 n k t →
            I1 ⋅ I2 = I1' ⋅ I2'.
  Proof.
  Admitted.    

  Lemma outflow_insert_inf_eq_KT I n k t I' :
        I' = outflow_insert_KT I n k t → 
          ∀ n', inset_KT I' n' = inset_KT I n'.
  Proof.
  Admitted.

  Lemma outflow_delete_inf_eq_KT I n k t I' :
        I' = outflow_delete_KT I n k t → 
          ∀ n', inset_KT I' n' = inset_KT I n'.
  Proof.
  Admitted.
  
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
    (* { apply auth_update. option_local_update, exclusive_local_update. } *)
    done.
  Admitted.


  (** Proofs **)  


(*
  Lemma traverse_spec γ_te γ_he γ_s γ_t γ_I γ_J γ_R 
                                  γ_f γ_e γ_c γ_b γ_cir r n k t0 t1:
    ⊢ ⌜k ∈ KS⌝ -∗ mcs_inv γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r -∗
        inFP γ_f n -∗ own (γ_cir n k) (◯ MaxNat t1) -∗ ⌜t0 ≤ t1⌝ -∗
          <<< ∀ t H, MCS γ_te γ_he t H >>> 
              traverse #n #k @ ⊤ ∖ ↑N
          <<< ∃ (t': nat), MCS γ_te γ_he t H ∗ ⌜(k, t') ∈ H⌝ 
                                             ∗ ⌜t0 ≤ t'⌝ , RET #t' >>>.
  Proof.
    iIntros "k_in_KS #HInv". iLöb as "IH" forall (n t1).
    iIntros "#FP_n #Hlb H". iDestruct "H" as %t0_le_t1.
    iDestruct "k_in_KS" as %k_in_KS.
    iIntros (Φ) "AU". wp_lam. wp_pures.
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cn Bn)"HnP_n". iModIntro.
    wp_pures. iDestruct "HnP_n" as (es T)"(node_n & HnP_frac & HnP_C & HnP_t)".
    wp_apply (inContents_spec with "node_n").
    iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val.
    wp_pures. case_eq (bool_decide ((#t = #0%nat)%nat)).
    - intros Ht. wp_pures.
      wp_apply (findNext_spec with "node_n").
      iIntros (b n1) "(node_n & Hif)". destruct b.
      + wp_pures. iDestruct "Hif" as %k_in_es.
        iApply fupd_wp. iInv "HInv" as ">H".
        iDestruct "H" as (T' H I J R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Ht & HI & HJ & HR & Hf 
                & Inf_I & Inf_J & Inf_R & _ & Max_ts & domm_IJ & domm_IR)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        (* { by iPoseProof (inFP_domm with "[$Hfp] [$Hdomm]") as "?". } *) 
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (es' In Jn Rn) "(HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc Hb]]. subst es'. subst Cn'. subst Bn'.
        iAssert (inFP γ_f n1)%I as "#HFP_n1".
        { iApply "HnS_cl". iPureIntro. 
          clear -k_in_es. set_solver. }
        iAssert (⌜(k, Bn !!! k) ∈ outset_KT In n1⌝)%I as %outflow_n_n1.
        { iDestruct "HnS_oc" as "(H' & _)".
          iDestruct "H'" as %H'. iPureIntro. 
          apply (H' n1 k (Bn !!! k)).
          repeat split; try done. apply bool_decide_eq_true in Ht.
          inversion Ht as [H'']. rewrite Cn_val. admit. }
        iAssert (⌜n1 ∈ domm I⌝)%I as %n_in_I.
        { admit. }
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n1); last admit.
        iDestruct "Hstar'" as "(H_n1 & Hstar'')".
        iDestruct "H_n1" as (bn1 Cn1 Bn1)"(Hl_n1 & Hlif_n1 & HnS_n1)".
        iDestruct "HnS_n1" as (es1 In1 Jn1 Rn1) 
         "(HnS_frac1 & HnS_si1 & HnS_FP1 & HnS_cl1 & 
                          HnS_oc1 & HnS_H1 & HnS_star1 & Hφ1)".
        iAssert (⌜(k, Bn !!! k) ∈ inset_KT In1 n1⌝)%I as %inflow_n1.
        { admit. }
        iAssert (⌜Bn1 !!! k = Bn !!! k⌝)%I as %Bn1_eq_Bn.
        { admit. }
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                                in "HnS_star".
        iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
        iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
        { admit. }
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                                in "HnS_star1".
        iDestruct "HnS_star1" as "(Hcirk_n1 & HnS_star1')".
        iAssert (own (γ_cir n1 k) (● MaxNat (Bn1 !!! k)) ∗ 
                  own (γ_cir n1 k) (◯ MaxNat (Bn1 !!! k)))%I 
                      with "[Hcirk_n1]" as "(Hcirk_n1 & #Hlb_1)".
        { admit. }
        iModIntro. iSplitR "node_n HnP_n' AU". iNext.
        iExists T', H, I, J, R. iFrame "Hglob".
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) n1); last admit.
        iFrame "Hstar''". iSplitL "Hl_n Hlif_n HnS_frac HnS_si HnS_FP
                         HnS_cl HnS_oc HnS_H Hcirk_n HnS_star' Hφ".
        iExists bn, Cn, Bn. iFrame "Hl_n Hlif_n".
        iExists es, In, Jn, Rn. iFrame. by iApply "HnS_star'".                  
        iExists bn1, Cn1, Bn1. iFrame "Hl_n1 Hlif_n1".
        iExists es1, In1, Jn1, Rn1. iFrame. by iApply "HnS_star1'".
        iModIntro.        
        awp_apply (unlockNode_spec_high with "[] [] [HnP_n' node_n]"); 
                        try done. iExists es, T. iFrame.                
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_". iModIntro. wp_pures.
        iApply "IH"; try done. iPureIntro.
        apply leibniz_equiv_iff in Bn1_eq_Bn.
        rewrite <-Bn1_eq_Bn in lb_t1. clear -lb_t1 t0_le_t1.
        apply (Nat.le_trans t0 t1 _); try done.
      + wp_pures. iDestruct "Hif" as %Not_in_es.
        iApply fupd_wp. iInv "HInv" as ">H".
        iDestruct "H" as (T' H I J R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". { admit. }
        (* { by iPoseProof (inFP_domm with "[$Hfp] [$Hdomm]") as "?". } *) 
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn')"(Hl_n & Hlif_n & HnS_n)".
        iAssert (⌜Cn' = Cn⌝)%I as "%".  
        { admit. } subst Cn'.
        iAssert (⌜Bn' = Bn⌝)%I as "%".  
        { admit. } subst Bn'.
        iDestruct "HnS_n" as (es' In Jn Rn) 
            "(HnS_frac & HnS_si & HnS_FP & HnS_cl & HnS_oc & 
                                        HnS_H & HnS_star & Hφ1 & Hφ)".
        iAssert (⌜es' = es⌝)%I as "%".  
        { admit. } subst es'.          
        iDestruct "Hφ1" as %Hφ. pose proof Hφ k as Hφ1. 
        destruct Hφ1 as [Hφ1 | Hφ1].
        { unfold out_KT in Hφ1. destruct Hφ1 as [tw [n' Hφ1]].
          iDestruct "HnS_oc" as "(HnS_ocI & HnS_os')". 
          iDestruct "HnS_ocI" as %HnS_ocI. 
          pose proof HnS_ocI n' k tw as Hoc.
          destruct Hoc as [Hoc _].
          pose proof Hoc Hφ1 as Hoc.
          destruct Hoc as [Hoc [_ _]].
          pose proof Not_in_es n'. contradiction. }
        iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                       in "HnS_star".
        iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
        iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
        { admit. }
        iAssert (⌜t0 = 0⌝)%I as %t0_zero. { admit. } subst t0.
        iMod "AU" as (t' H') "[MCS [_ Hclose]]". iSpecialize ("Hclose" $! 0).
        iMod ("Hclose" with "[MCS]") as "HΦ". iFrame. 
        iPureIntro. split; try done. admit.
        iModIntro. iSplitR "node_n HnP_n' HΦ". iNext.
        iExists T', H, I, J, R. iFrame "Hglob".
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iFrame "Hstar'". iExists bn, Cn, Bn.
        iFrame "Hl_n Hlif_n". iExists es, In, Jn, Rn.
        iFrame "∗%". by iApply "HnS_star'". iModIntro.
        awp_apply (unlockNode_spec_high with "[] [] [HnP_n' node_n]") without "HΦ";
                        try done. iExists es, T. iFrame.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_". iModIntro. iIntros "HΦ". by wp_pures.
    - intros Ht. wp_pures.                                         
      iApply fupd_wp. iInv "HInv" as ">H".
      iDestruct "H" as (T' H I J R) "(Hglob & Hstar)".
      iAssert (⌜n ∈ domm I⌝)%I as "%". { admit. }
      (* { by iPoseProof (inFP_domm with "[$Hfp] [$Hdomm]") as "?". } *) 
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iDestruct "Hstar" as "(H_n & Hstar')".
      iDestruct "H_n" as (bn Cn' Bn')"(Hl_n & Hlif_n & HnS_n)".
      iAssert (⌜Cn' = Cn⌝)%I as "%".  
      { admit. } subst Cn'.
      iAssert (⌜Bn' = Bn⌝)%I as "%".  
      { admit. } subst Bn'.
      iDestruct "HnS_n" as (es' In Jn Rn) 
            "(HnS_frac & HnS_si & HnS_FP & HnS_cl & HnS_oc & 
                                        HnS_H & HnS_star & Hφ1 & Hφ)".
      iAssert (⌜es' = es⌝)%I as "%".  
      { admit. } subst es'.      
      iEval (rewrite (big_sepS_elem_of_acc (_) (KS) k); last by eauto) 
                                                      in "HnS_star".
      iDestruct "HnS_star" as "(Hcirk_n & HnS_star')".
      iAssert (⌜t1 ≤ Bn !!! k⌝)%I as %lb_t1.
      { admit. }
      iDestruct "Hφ1" as %Hφ. pose proof Hφ k as Hφ1. 
      destruct Hφ1 as [Hφ1 | Hφ1].
      { unfold out_KT in Hφ1. destruct Hφ1 as [tw [n' Hφ1]].
        iDestruct "HnS_oc" as "(HnS_ocI & HnS_os')". 
        iDestruct "HnS_ocI" as %HnS_ocI. 
        pose proof HnS_ocI n' k tw as Hoc.
        destruct Hoc as [Hoc _].
        pose proof Hoc Hφ1 as Hoc.
        destruct Hoc as [_ [Hoc _]].
        rewrite Cn_val in Hoc. unfold bool_decide in Ht.
        rewrite Hoc in Ht. simpl in Ht. inversion Ht. }
      iAssert (⌜set_of_map Cn ⊆ H⌝)%I as %Cn_Sub_H.
      { admit. }
      iAssert (⌜(k,t) ∈ set_of_map Cn⌝)%I as %kt_in_Cn.
      { admit. }  
      iMod "AU" as (t' H') "[MCS [_ Hclose]]". iSpecialize ("Hclose" $! t).
      iAssert (⌜H' = H⌝)%I as %H1. 
      { admit. } subst H'.
      iMod ("Hclose" with "[MCS]") as "HΦ". iFrame. 
      iPureIntro. split. set_solver. rewrite Hφ1 in lb_t1.
      rewrite Cn_val in lb_t1. lia.
      iModIntro. iSplitR "node_n HnP_n' HΦ". iNext.
      iExists T', H, I, J, R. iFrame "Hglob".
      rewrite (big_sepS_delete _ (domm I) n); last by eauto.
      iFrame "Hstar'". iExists bn, Cn, Bn.
      iFrame "Hl_n Hlif_n". iExists es, In, Jn, Rn.
      iFrame "∗%". by iApply "HnS_star'". iModIntro.
      awp_apply (unlockNode_spec_high with "[] [] [HnP_n' node_n]") without "HΦ"; 
                      try done. iExists es, T. iFrame.
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. iIntros "HΦ". by wp_pures.
  Admitted.        
*)     


  Lemma upsert_spec γ_te γ_he γ_s γ_t γ_I γ_J γ_R 
                                  γ_f γ_e γ_c γ_b γ_cir r (k: K) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
          mcs_inv γ_te γ_he γ_s γ_t γ_I γ_J γ_R γ_f γ_e γ_c γ_b γ_cir r -∗
                <<< ∀ t H, MCS γ_te γ_he t H >>> 
                    upsert r #k @ ⊤ ∖ ↑N
                <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k, t)]}), RET #() >>>.
  Proof.
    iIntros "H". iDestruct "H" as %k_in_KS.
    iIntros "#HInv". iLöb as "IH".
    iIntros (Φ) "AU". wp_lam.
    iApply fupd_wp. iInv "HInv" as ">H".
    iDestruct "H" as (T0 H0 I0 J0 R0) "(Hglob & Hstar)".
    iDestruct "Hglob" as "(MCS & Hs & Ht & HI & HJ & HR & Hf 
                & Inf_I & Inf_J & Inf_R & #FP_r & Max_ts & domm_IJ & domm_IR)".
    iModIntro. iSplitR "AU". iNext. 
    iExists T0, H0, I0, J0, R0. iFrame "∗ #". iModIntro.
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cr Br)"HnP_n". iModIntro. wp_pures.
    iDestruct "HnP_n" as (es T)"(node_n & HnP_frac & HnP_C & HnP_t)".
    iEval (rewrite <-beq_nat_refl) in "HnP_t".
    wp_apply (readClock_spec with "[HnP_t]"); try done.
    iIntros "HnP_t". wp_pures.
    wp_apply (addContents_spec with "node_n").
    iIntros (b Cr')"(node_n & Hif)".
    destruct b; last first.
    - iDestruct "Hif" as %HCr. replace Cr'. wp_pures.
      awp_apply (unlockNode_spec_high with "[] [] [-AU]"); try done.
      { iExists es, T. iFrame. iEval (rewrite <-beq_nat_refl); try done. }
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro. wp_pures.
      by iApply "IH".
    - iDestruct "Hif" as %HCr. wp_pures.
      awp_apply incrementClock_spec. iInv "HInv" as ">H". 
      iDestruct "H" as (T1 H1 I1 J1 R1) "(Hglob & Hstar)".
      iDestruct "Hglob" as "(MCS_auth & HH & Ht & HI & HJ & HR & Hf 
                & Inf_I & Inf_J & Inf_R & _ & Max_ts & domm_IJ & domm_IR)".
      iAssert (⌜T = T1⌝)%I as %HT. 
      { iPoseProof ((own_valid_2 _ _ _) with "[$HnP_t] [$Ht]") as "H'".
        iDestruct "H'" as %H'. 
        pose proof (auth_auth_frac_op_inv _ _ _ _ H') as H''.
        inversion H''. by iPureIntro. } replace T1.          
      iAssert (own γ_t (● (MaxNat T)))%I with "[Ht HnP_t]" as "H".
      { iCombine "Ht HnP_t" as "H'". done. }          
      iAaccIntro with "H".
      { iIntros "H". iDestruct "H" as "(Ht & HnP_t)".
        iModIntro. iSplitR "AU HnP_frac HnP_C node_n HnP_t".
        iNext. iExists T, H1, I1, J1, R1. iFrame "∗ #". iFrame. }
      iIntros "H". iDestruct "H" as "(Ht & HnP_t)".
      iMod (own_update γ_s (● H1) (● (H1 ∪ {[(k,T)]})) with "[$HH]") as "HH".
      { apply (auth_update_auth _ _ (H1 ∪ {[(k,T)]})).
        apply gset_local_update. set_solver. } 
      iAssert (maxTS (T+1) (H1 ∪ {[(k, T)]}))%I with "[Max_ts]" as "Max_ts".
      { iDestruct "Max_ts" as %Max_ts. iPureIntro. intros k' t' H.
        assert (((k',t') ∈ H1) ∨ (k' = k ∧ t' = T)) as Hor by set_solver.
        destruct Hor as [Hor | Hor]. 
          pose proof Max_ts k' t' Hor as Hres. lia.
          destruct Hor as [_ Hor]. replace t'. lia. }       
      iAssert (⌜set_of_map Cr ⊆ set_of_map Cr'⌝)%I as %Cr_sub_Cr'.
      { admit. }
      iAssert (own γ_s (◯ set_of_map Cr'))%I with "[HnP_C]" as "HnP_C".
      { admit. }
      iAssert (⌜r ∈ domm I1⌝)%I as %r_in_I.
      { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
      iDestruct "Hstar" as "(H_r & Hstar')".
      iDestruct "H_r" as (br Cr'' Br'')"(Hl_r & Hlif_r & HnS_r)".
      iAssert (⌜br = true⌝)%I as %Hbr.
      { destruct br; try done.
        iDestruct "Hlif_r" as (es' T')"(node' & _)".
        iPoseProof ((node_sep_star r r) with "[$]") as "%".
        contradiction. } replace br.
      iDestruct "HnS_r" as (es' Ir Jr Rr) 
            "(HnS_frac & HnS_si & HnS_FP & HnS_cl & HnS_oc & 
                                        HnS_if & HnS_star & Hφ)".
      iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
      destruct H as [Hes [Hc Hb]]. subst es'. subst Cr''. subst Br''.
      destruct (decide (Cr !!! k = 0)) as [ Cr_k | Cr_k ]; last first.
      + set (Br' := <[k := T]>Br).
        assert (Br' = <[k := T]>Br) as HBr'. try done.
        iAssert (⌜Br' = map_of_set (H1 ∪ {[(k, T)]})⌝)%I as %Br'_eq_H1.
        { admit. }
        assert (∀ k', k' ≠ k → Br' !!! k' = Br !!! k') as HBr_neq.
        { intros k' Hk'. rewrite /(Br !!! k').
          rewrite /(Br' !!! k'). 
          unfold finmap_lookup_total.
          unfold inhabitant. simpl.
          assert (Br' !! k' = Br !! k') as HBr.
          { by apply lookup_insert_ne. } 
          by rewrite HBr. }
        assert (Br' !!! k = T) as HBr'_k.
        { apply lookup_total_insert. }          
        iAssert ([∗ set] k0 ∈ KS, own (γ_cir r k0) 
                    (● {| max_nat_car := Br' !!! k0 |}))%I 
            with "[HnS_star]" as "HnS_star".
        { admit. }
        iMod ((frac_update γ_e γ_c γ_b r es Cr Br es Cr' Br') 
                    with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".
        assert ((∃ n, k ∈ es !!! n ∧ n ≠ r) ∨ (∀ n, k ∉ es !!! n)) as Hes.
        { admit. } destruct Hes as [Hes | Hes].
        * destruct Hes as [n [k_in_es n_neq_r]].
          set (Jr'_temp := outflow_delete_KT Jr n k (Cr !!! k)).
          set (Jr' := outflow_insert_KT Jr'_temp n k T).
          iAssert (outflow_constraints r Ir Jr' Rr es Cr' Br')%I 
                    with "[HnS_oc]" as "HnS_oc".
          { iDestruct "HnS_oc" as "(% & % & %)".
            rename H into OC_1. rename H2 into OC_2.
            rename H3 into OC_3. 
            iPureIntro. split; last split; try done.
            - intros n' k' t'. split.
              + intros Hout.
                apply OC_1 in Hout.
                destruct Hout as [Hout1 [Hout2 Hout3]].
                destruct (decide (k' = k)).
                * replace k' in Hout2.
                  contradiction.
                * repeat split; try done.
                  rewrite /(Cr' !!! k'). 
                  unfold finmap_lookup_total.
                  replace Cr'. rewrite lookup_insert_ne; try done.
                  rewrite /(Br' !!! k'). 
                  unfold finmap_lookup_total.
                  rewrite HBr'. rewrite lookup_insert_ne; try done.
              + intros [Hout1 [Hout2 Hout3]].
                apply OC_1. split; try done.
                destruct (decide (k' = k)).
                * replace k'.
                  rewrite e in Hout2. replace Cr' in Hout2.
                  rewrite lookup_total_insert in Hout2.
                  admit. (* Contradiction: T = 0 *)
                * rewrite /(Cr' !!! k') in Hout2.
                  unfold finmap_lookup_total in Hout2.
                  replace Cr' in Hout2. 
                  rewrite lookup_insert_ne in Hout2; try done.
                  rewrite /(Br' !!! k') in Hout3.
                  unfold finmap_lookup_total in Hout3; try done.
                  rewrite HBr' in Hout3. 
                  rewrite lookup_insert_ne in Hout3; try done.
            - intros n' k' t'.
              destruct (decide (n' = n)).
              + assert (outset_KT Jr' n = 
                      (outset_KT Jr n ∖ {[k, Cr !!! k]}) ∪ {[k, T]}) as Outset.
                { pose proof outflow_insert_outset_KT Jr'_temp n k T Jr' as Houts.
                  assert (Jr' = outflow_insert_KT Jr'_temp n k T) as HJr' by done.
                  pose proof Houts HJr' n' as [Hp _].
                  pose proof Hp e as Hp.
                  pose proof outflow_delete_outset_KT Jr n k (Cr !!! k) Jr'_temp 
                    as Houts'. 
                  assert (Jr'_temp = outflow_delete_KT Jr n k (Cr !!! k)) 
                    as HJr_t by done.  
                  pose proof Houts' HJr_t n' as [Hp' _].
                  pose proof Hp' e as Hp'.
                  rewrite e in Hp.
                  rewrite e in Hp'.
                  by rewrite Hp' in Hp. }
                replace n'.  
                assert ((k',t') ∈ outset_KT Jr' n → 
                       ((k',t') ∈ outset_KT Jr n) ∨ (k',t') = (k, T)) as Hkt'.
                { intros Hout. rewrite Outset in Hout.
                  set_solver. }
                split.
                * intros Hout. pose proof Hkt' Hout as Hkt'.
                  destruct Hkt' as [Hkt' | Hkt'].
                  ** apply OC_2 in Hkt'.
                     destruct Hkt' as [Hkt'_1 Hkt'_2]. 
                     split; try done.
                     destruct (decide (k' = k)).
                     rewrite e0 in Hkt'_2.
                     rewrite e0 in Hout.
                     rewrite <-Hkt'_2 in Hout.
                     assert ((k, Cr !!! k) ∉ outset_KT Jr' n).
                     { clear -Outset.
                       assert (Cr !!! k ≠ T). admit.
                       set_solver. }
                     contradiction.
                     replace Cr'. 
                     rewrite lookup_total_insert_ne; try done.
                  ** inversion Hkt'.
                     repeat split; try done.
                     replace Cr'.
                     rewrite lookup_total_insert; try done.
                * intros [Hk1 Hk2].
                  destruct (decide (k' = k)).
                  ** replace k'.
                     rewrite e0 in Hk1.
                     rewrite e0 in Hk2.
                     replace Cr' in Hk2. 
                     rewrite lookup_total_insert in Hk2.
                     replace t'. rewrite Outset.
                     set_solver.
                  ** replace Cr' in Hk2.
                     rewrite lookup_total_insert_ne in Hk2; try done.
                     assert (k' ∈ es !!! n ∧ Cr !!! k' = t') as Hkt; try done.
                     apply OC_2 in Hkt.
                     rewrite Outset.
                     clear -Hkt n0. set_solver.
              + assert (outset_KT Jr' n' = outset_KT Jr n') as Outset.
                { pose proof outflow_insert_outset_KT Jr'_temp n k T Jr' as Houts.
                  assert (Jr' = outflow_insert_KT Jr'_temp n k T) as HJr' by done.
                  pose proof Houts HJr' n' as [_ Hp].
                  pose proof Hp n0 as Hp.
                  pose proof outflow_delete_outset_KT Jr n k (Cr !!! k) Jr'_temp 
                    as Houts'. 
                  assert (Jr'_temp = outflow_delete_KT Jr n k (Cr !!! k)) 
                    as HJr_t by done.  
                  pose proof Houts' HJr_t n' as [_ Hp'].
                  pose proof Hp' n0 as Hp'.
                  by rewrite Hp' in Hp. }
                rewrite Outset.
                split.
                * intros Hout.
                  apply OC_2 in Hout.
                  destruct Hout as [Hout1 Hout2].
                  split; try done.
                  destruct (decide (k' = k)).
                  ** rewrite e in Hout1.
                     admit.
                  ** replace Cr'.
                     rewrite lookup_total_insert_ne; try done.
                * intros [Hout1 Hout2].
                  destruct (decide (k' = k)).
                  ** rewrite e in Hout1.
                     admit.
                  ** replace Cr' in Hout2.
                     rewrite lookup_total_insert_ne in Hout2; try done.
                     apply OC_2.
                     split; try done. }
          iAssert (inFP γ_f n)%I as "#FP_n".
          { iApply "HnS_cl". iPureIntro.
            clear -k_in_es. set_solver. }
          iAssert (⌜n ∈ domm I1⌝)%I as %n_in_I.
          { by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
          rewrite (big_sepS_delete _ (domm I1 ∖ {[r]}) n); last by set_solver.
          iDestruct "Hstar'" as "(H_n & Hstar')".
          iDestruct "H_n" as (bn Cn Bn)"(Hl_n & Hlif_n & HnS_n)".
          iDestruct "HnS_n" as (es_n In Jn Rn) 
            "(HnS_fracn & HnS_sin & HnS_FPn & HnS_cln & HnS_ocn & 
                                        HnS_ifn & HnS_starn & Hφn)".
          set (Jn'_temp := inflow_delete_KT Jn n k (Cr !!! k)).
          set (Jn' := inflow_insert_KT Jn'_temp n k T).
          iAssert (outflow_constraints n In Jn' Rn es_n Cn Bn)%I
            with "[HnS_ocn]" as "HnS_ocn".
          { iDestruct "HnS_ocn" as "(% & % & %)".
            rename H into OC_1. rename H2 into OC_2.
            rename H3 into OC_3. 
            iPureIntro. split; last split; try done. }
          iAssert (singleton_interfaces_ghost_state γ_I γ_J γ_R r Ir Jr' Rr
            ∗ singleton_interfaces_ghost_state γ_I γ_J γ_R n In Jn' Rn)%I 
                    with "[HnS_si HnS_sin]" as "(HnS_si & HnS_sin)".
          { unfold singleton_interfaces_ghost_state. 
            iDestruct "HnS_si" as "(HrI & HrJ & HrR & Domm_rI & Domm_rJ & Domm_rR)".
            iDestruct "HnS_sin" as "(HnI & HnJ & HnR & Domm_nI & Domm_nJ & Domm_nR)".
            assert (domm Jn' = domm Jn).
            { assert (Jn'_temp = inflow_delete_KT Jn n k (Cr !!! k)) 
                          as HJn't by done.
              assert (Jn' = inflow_insert_KT Jn'_temp n k T) as HJn' by done.
              assert (domm Jn' = domm Jn'_temp) as H'.
              apply (inflow_insert_domm _ n k T); try done.
              assert (domm Jn'_temp = domm Jn) as H''.
              apply (inflow_delete_domm _ n k (Cr !!! k)); try done.
              by rewrite H'. } 
            rewrite H. iFrame.
            iCombine "HrJ HnJ" as "HrnJ".
            assert (Jr ⋅ Jn = Jr' ⋅ Jn') as H'.
            { assert (Jr ⋅ Jn = Jr'_temp ⋅ Jn'_temp) as H'.
              { apply (flow_delete_eq_KT Jr Jr'_temp _ _ n k (Cr !!! k));
                         try done. }
              assert (Jr'_temp ⋅ Jn'_temp = Jr' ⋅ Jn') as H''.
              { apply (flow_insert_eq_KT Jr'_temp Jr' _ _ n k T);
                         try done. }
              by rewrite H'. }            
            iEval (rewrite H') in "HrnJ".
            iEval (rewrite auth_frag_op) in "HrnJ".
            iDestruct "HrnJ" as "(HrJ & HnJ)". iFrame. }
          iEval (rewrite <-beq_nat_refl) in "HnS_if".
          iDestruct "HnS_if" as "(H' & H'' & H''')".
          iDestruct "H'" as %Br_eq_H1. 
          iDestruct "H''" as %Infz_rI.
          iDestruct "H'''" as %Infz_rJ.
          iDestruct "Inf_R" as %Inf_R.
          iPoseProof ((auth_own_incl γ_R R1 Rr) with "[HR HnS_si]")
              as (Ro) "%". 
          { unfold singleton_interfaces_ghost_state.
            iDestruct "HnS_si" as "(_ & _ & H' & _)". 
            iFrame. } rename H into Incl_R1.
          iPoseProof (own_valid with "HR") as "%".
          rename H into Valid_R1.
          iAssert (⌜domm Rr = {[r]}⌝)%I as "%".
          { by iDestruct "HnS_si" as "(_&_&_&_&_&H')". }
          rename H into Domm_Rr.
          iAssert (φ1 Br' Cr' Ir ∗ φ2 r Br' Ir ∗ φ3 r Br' Jr' ∗ φ4 r Br' Rr 
                  ∗ φ5 r Rr)%I with "[Hφ]" as "Hφ".
          { iDestruct "Hφ" as %Hφ. 
            destruct Hφ as [Hφ1 [Hφ2 [Hφ3 [Hφ4 Hφ5]]]].
            iPureIntro. repeat split; try done.
            - intros k'. pose proof Hφ1 k' as Hφ1.
              destruct Hφ1 as [Hφ1 | Hφ1].
              by left.
              destruct (decide (k' = k)).
              replace k'. right.
              replace Cr'. rewrite HBr'.
              rewrite lookup_total_insert.
              by rewrite lookup_total_insert.
              right.    
              replace Cr'. rewrite HBr'.
              rewrite lookup_total_insert_ne; try done.
              rewrite lookup_total_insert_ne; try done.
            - intros k' t' Hins.
              pose proof Infz_rI r as Infz_rI.
              rewrite Infz_rI in Hins.
              exfalso. clear -Hins. set_solver.
            - intros k' t' Hins.
              pose proof Infz_rJ r as Infz_rJ.
              assert (inset_KT Jr' r = inset_KT Jr r) as H'.
              { assert (inset_KT Jr'_temp r = inset_KT Jr r) as H'.
                apply (outflow_delete_inf_eq_KT _ n k (Cr !!! k)); try done.
                assert (inset_KT Jr' r = inset_KT Jr'_temp r) as H''.
                apply (outflow_insert_inf_eq_KT _ n k T); try done.
                by rewrite <-H'. }
              rewrite H' in Hins. rewrite Infz_rJ in Hins.
              exfalso. clear -Hins. set_solver.
            - intros k'. right.
              apply (inset_monotone R1 Rr Ro); try done.
              by rewrite <-auth_auth_valid.
              pose proof Inf_R r k' as Inf_R.
              by rewrite <-beq_nat_refl in Inf_R.
              rewrite Domm_Rr. clear. set_solver. } 
          iAssert (φ1 Bn Cn In ∗ φ2 n Bn In ∗ φ3 n Bn Jn' ∗ φ4 n Bn Rn 
                  ∗ φ5 n Rn)%I with "[Hφn]" as "Hφn".
          { iDestruct "Hφn" as %Hφ. 
            destruct Hφ as [Hφ1 [Hφ2 [Hφ3 [Hφ4 Hφ5]]]].
            iPureIntro. repeat split; try done.
            intros k' t'. 
            assert (inset_KT Jn' n = 
                      (inset_KT Jn n ∖ {[k, Cr !!! k]}) ∪ {[k, T]}) as Inset.
            { pose proof inflow_insert_outset_KT Jn'_temp n k T Jn' as Hin.
              assert (Jn' = inflow_insert_KT Jn'_temp n k T) as HJn' by done.
              pose proof Hin HJn' n as [Hp _].
              assert (n = n) as H' by done.
              pose proof Hp H' as Hp.
              pose proof inflow_delete_outset_KT Jn n k (Cr !!! k) Jn'_temp as Hin'. 
              assert (Jn'_temp = inflow_delete_KT Jn n k (Cr !!! k)) 
                    as HJn_t by done.  
              pose proof Hin' HJn_t n as [Hp' _].
              pose proof Hp' H' as Hp'.
              by rewrite Hp' in Hp. }
              assert ((k',t') ∈ inset_KT Jn' n → 
                       ((k',t') ∈ inset_KT Jn n) ∨ (k',t') = (k, T)) as Hkt'.
              { intros Hin. rewrite Inset in Hin. set_solver. }
              intros Hin. apply Hkt' in Hin.
              destruct Hin as [Hin | Hin].
              by pose proof Hφ3 k' t' Hin as Hφ3.
              inversion Hin.
              admit.
          }  
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
          iSplitR "HΦ node_n HnP_t HnP_C HnP_frac".
          { iNext. iExists (T+1), (H1 ∪ {[(k, T)]}), I1, J1, R1.
            iFrame "∗ %".   
            rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
            iSplitL "Hl_r Hlif_r HnS_cl HnS_star Hφ HnS_frac HnS_oc HnS_si".
            { iExists true, Cr', Br'. iFrame.
              unfold nodeShared. iExists es, Ir, Jr', Rr.
              iFrame "∗#". iEval (rewrite <-beq_nat_refl). 
              iFrame "%∗". }        
            rewrite (big_sepS_delete _ (domm I1 ∖ {[r]}) n); last by set_solver.
            iSplitL "Hl_n Hlif_n HnS_cln HnS_starn Hφn HnS_fracn HnS_ocn 
                        HnS_sin HnS_ifn".
            { iExists bn, Cn, Bn. iFrame. iExists es_n, In, Jn', Rn.
              iFrame "∗#". assert (n =? r = false) as Hnr. 
              { by rewrite beq_nat_false_iff. } 
              by rewrite Hnr. }
            iApply (big_opS_proper (λ y, ∃ (bn0 : bool) (Cn0 Bn0 : gmap K natUR),
                                      lockLoc y ↦ #bn0
                                    ∗ (if bn0 then True else
                                       nodePred γ_e γ_c γ_b γ_t γ_s r y Cn0 Bn0)
                                    ∗ nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir
                                              r y Cn0 Bn0 H1 )%I
                                   (λ y, ∃ (bn0 : bool) (Cn0 Bn0 : gmap K natUR),
                                      lockLoc y ↦ #bn0
                                    ∗ (if bn0 then True else
                                       nodePred γ_e γ_c γ_b γ_t γ_s r y Cn0 Bn0)
                                    ∗ nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir
                                              r y Cn0 Bn0 (H1 ∪ {[(k, T)]}) )%I
                                   (domm I1 ∖ {[r]} ∖ {[n]})); try done.
            intros y y_dom. assert (y ≠ r) as Hy by set_solver. iFrame. iSplit;
            iIntros "Hstar"; iDestruct "Hstar" as (b C B)"(Hl & Hlif & HnS)";
            iExists b, C, B; iFrame; 
            iDestruct "HnS" as (esy Iy Jy Ry)"(HnS_frac & HnS_si & HnS_FP 
                          & HnS_cl & HnS_oc & HnS_if & HnS_star & Hφ)";
            iExists esy, Iy, Jy, Ry; iFrame; 
            assert (y =? r = false) as Hyr by (rewrite beq_nat_false_iff; done);
            iEval (rewrite Hyr); done. } 
          wp_pures.  
          awp_apply (unlockNode_spec_high with "[] [] [HnP_t HnP_C HnP_frac node_n]")
                without "HΦ"; try done. iExists es, (T + 1). iFrame.
                by iEval (rewrite <-beq_nat_refl).
          iAaccIntro with ""; try eauto with iFrame.
          
          
          
        * iAssert (outflow_constraints r Ir Jr Rr es Cr' Br')%I 
                    with "[HnS_oc]" as "HnS_oc".
          { admit. }
          iAssert (φ1 Br' Cr' Ir ∗ φ2 r Br' Ir ∗ φ3 r Br' Jr ∗ φ4 r Br' Rr 
                  ∗ φ5 r Rr)%I with "[Hφ]" as "Hφ".
          { admit. }  
          iMod "AU" as (t' H')"[MCS [_ Hclose]]".
          iAssert (⌜t' = T⌝)%I as %Ht'. { admit. } replace t'.
          iAssert (⌜H' = H1⌝)%I as %H1'. { admit. } replace H'.
          iAssert (MCS γ_te γ_he (T+1) (H1 ∪ {[(k, T)]}) ∗
                   MCS_auth γ_te γ_he (T+1) (H1 ∪ {[(k, T)]}))%I
            with "[MCS MCS_auth]" as "(MCS & MCS_auth)".
          { admit. }
          iMod ("Hclose" with "MCS") as "HΦ".            
                    
          
          
          iModIntro.
          iSplitR "HΦ node_n HnP_t HnP_C HnP_frac".
          { iNext. iExists (T+1), (H1 ∪ {[(k, T)]}), I1, J1, R1.
            iFrame.   
            rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
            iSplitL "Hl_r Hlif_r HnS_cl HnS_star Hφ HnS_frac HnS_oc HnS_si HnS_if".
            { iExists true, Cr', Br'. iFrame.
              unfold nodeShared. iExists es, Ir, Jr, Rr.
              iFrame "∗#". iEval (rewrite <-beq_nat_refl) in "HnS_if".
              iDestruct "HnS_if" as "(_ & HnS_if)".
              iEval (rewrite <-beq_nat_refl). iFrame "%∗". }        
            iApply (big_opS_proper (λ y, ∃ (bn0 : bool) (Cn0 Bn0 : gmap K natUR),
                                      lockLoc y ↦ #bn0
                                    ∗ (if bn0 then True else
                                       nodePred γ_e γ_c γ_b γ_t γ_s r y Cn0 Bn0)
                                    ∗ nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir
                                              r y Cn0 Bn0 H1 )%I
                                   (λ y, ∃ (bn0 : bool) (Cn0 Bn0 : gmap K natUR),
                                      lockLoc y ↦ #bn0
                                    ∗ (if bn0 then True else
                                       nodePred γ_e γ_c γ_b γ_t γ_s r y Cn0 Bn0)
                                    ∗ nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir
                                              r y Cn0 Bn0 (H1 ∪ {[(k, T)]}) )%I
                                   (domm I1 ∖ {[r]})); try done.
            intros y y_dom. assert (y ≠ r) as Hy by set_solver. iFrame. iSplit;
            iIntros "Hstar"; iDestruct "Hstar" as (b C B)"(Hl & Hlif & HnS)";
            iExists b, C, B; iFrame; 
            iDestruct "HnS" as (esy Iy Jy Ry)"(HnS_frac & HnS_si & HnS_FP 
                          & HnS_cl & HnS_oc & HnS_if & HnS_star & Hφ)";
            iExists esy, Iy, Jy, Ry; iFrame; 
            assert (y =? r = false) as Hyr by (rewrite beq_nat_false_iff; done);
            iEval (rewrite Hyr); done. } 
          wp_pures.  
          awp_apply (unlockNode_spec_high with "[] [] [HnP_t HnP_C HnP_frac node_n]")
                without "HΦ"; try done. iExists es, (T + 1). iFrame.
                by iEval (rewrite <-beq_nat_refl).
          iAaccIntro with ""; try eauto with iFrame.
      + intros Cr_k.
        set (Br' := <[k := T]>Br).
        iAssert (⌜Br' = map_of_set (H1 ∪ {[(k, T)]})⌝)%I as %Br_eq_H1.
        { admit. }
        iAssert ([∗ set] k0 ∈ KS, own (γ_cir r k0) 
                    (● {| max_nat_car := Br' !!! k0 |}))%I 
            with "[HnS_star]" as "HnS_star".
        { admit. }     
        iAssert (frac_ghost_state γ_e γ_c γ_b r es Cr' Br' ∗ 
                    frac_ghost_state γ_e γ_c γ_b r es Cr' Br')%I 
              with "[HnP_frac HnS_frac]" as "(HnP_frac & HnS_frac)".
        { admit. }
        assert ((∃ n, k ∈ es !!! n ∧ n ≠ r) ∨ (∀ n, k ∉ es !!! n)) as Hes.
        { admit. } destruct Hes as [Hes | Hes].
        * destruct Hes as [n [k_in_es n_neq_r]].
          set (Jr'_out_r := (nzmap_imerge 
             (λ k' a1 _, if (decide (k' = (k, T))) then 1 else a1)
                         (out Jr n) (∅)): (KT_multiset)).
          set (Jr'_out := (nzmap_imerge 
                      (λ k' a1 _, if (decide (k = r)) then Jr'_out_r else a1)
                      (out_map Jr) (∅)) : (nzmap Node KT_multiset)).
          set (Jr1' := ({| infR := inf_map Jr ; outR := Jr'_out |})).
          set (Jr' := ∅: (KT_flowint_ur K)).
          set (Ir' := ∅: (KT_flowint_ur K)).
          iAssert (outflow_constraints r Ir' Jr' Rr es Cr' Br')%I 
                    with "[HnS_oc]" as "HnS_oc".
          { admit. }
          iAssert (inFP γ_f n)%I as "#FP_n". 
          { iApply "HnS_cl". iPureIntro.
            clear -k_in_es. set_solver. }
          iAssert (⌜n ∈ domm I1⌝)%I as %n_in_I.
          { admit. }
          rewrite (big_sepS_delete _ (domm I1 ∖ {[r]}) n); last by set_solver.
          iDestruct "Hstar'" as "(H_n & Hstar')".
          iDestruct "H_n" as (bn Cn Bn)"(Hl_n & Hlif_n & HnS_n)".
          iDestruct "HnS_n" as (es_n In Jn Rn) 
            "(HnS_fracn & HnS_sin & HnS_FPn & HnS_cln & HnS_ocn & 
                                        HnS_ifn & HnS_starn & Hφn)".
          set (Jn' := ∅: (KT_flowint_ur K)).
          set (In' := ∅: (KT_flowint_ur K)).
          iAssert (singleton_interfaces_ghost_state γ_I γ_J γ_R r Ir' Jr' Rr
            ∗ singleton_interfaces_ghost_state γ_I γ_J γ_R n In' Jn' Rn)%I 
                    with "[HnS_si HnS_sin]" as "(HnS_si & HnS_sin)".
          { admit. }          
          iAssert (outflow_constraints n In' Jn' Rn es_n Cn Bn)%I
            with "[HnS_ocn]" as "HnS_ocn".
          { admit. }
          iAssert (φ1 Br' Cr' Ir' ∗ φ2 r Br' Ir' ∗ φ3 r Br' Jr' ∗ φ4 r Br' Rr 
                  ∗ φ5 r Rr)%I with "[Hφ]" as "Hφ".
          { admit. }  
          iAssert (φ1 Bn Cn In' ∗ φ2 n Bn In' ∗ φ3 n Bn Jn' ∗ φ4 n Bn Rn 
                  ∗ φ5 n Rn)%I with "[Hφn]" as "Hφn".
          { admit. }  
          iMod "AU" as (t' H')"[MCS [_ Hclose]]".
          iAssert (⌜t' = T⌝)%I as %Ht'. { admit. } replace t'.
          iAssert (⌜H' = H1⌝)%I as %H1'. { admit. } replace H'.
          iAssert (MCS γ_te γ_he (T+1) (H1 ∪ {[(k, T)]}) ∗
                   MCS_auth γ_te γ_he (T+1) (H1 ∪ {[(k, T)]}))%I
            with "[MCS MCS_auth]" as "(MCS & MCS_auth)".
          { admit. }
          iMod ("Hclose" with "MCS") as "HΦ".            
                    
          
          
          iModIntro.
          iSplitR "HΦ node_n HnP_t HnP_C HnP_frac".
          { iNext. iExists (T+1), (H1 ∪ {[(k, T)]}), I1, J1, R1.
            iFrame.   
            rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
            iSplitL "Hl_r Hlif_r HnS_cl HnS_star Hφ HnS_frac HnS_oc HnS_si HnS_if".
            { iExists true, Cr', Br'. iFrame.
              unfold nodeShared. iExists es, Ir', Jr', Rr.
              iFrame "∗#". iEval (rewrite <-beq_nat_refl) in "HnS_if".
              iDestruct "HnS_if" as "(_ & HnS_if)".
              iEval (rewrite <-beq_nat_refl). iFrame "%∗".
              unfold inflow_zero. admit. }        
            rewrite (big_sepS_delete _ (domm I1 ∖ {[r]}) n); last by set_solver.
            iSplitL "Hl_n Hlif_n HnS_cln HnS_starn Hφn HnS_fracn HnS_ocn 
                        HnS_sin HnS_ifn".
            { iExists bn, Cn, Bn. iFrame. iExists es_n, In', Jn', Rn.
              iFrame "∗#". assert (n =? r = false) as Hnr. 
              { by rewrite beq_nat_false_iff. } 
              by rewrite Hnr. }
            iApply (big_opS_proper (λ y, ∃ (bn0 : bool) (Cn0 Bn0 : gmap K natUR),
                                      lockLoc y ↦ #bn0
                                    ∗ (if bn0 then True else
                                       nodePred γ_e γ_c γ_b γ_t γ_s r y Cn0 Bn0)
                                    ∗ nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir
                                              r y Cn0 Bn0 H1 )%I
                                   (λ y, ∃ (bn0 : bool) (Cn0 Bn0 : gmap K natUR),
                                      lockLoc y ↦ #bn0
                                    ∗ (if bn0 then True else
                                       nodePred γ_e γ_c γ_b γ_t γ_s r y Cn0 Bn0)
                                    ∗ nodeShared γ_I γ_J γ_R γ_e γ_c γ_b γ_f γ_cir
                                              r y Cn0 Bn0 (H1 ∪ {[(k, T)]}) )%I
                                   (domm I1 ∖ {[r]} ∖ {[n]})); try done.
            intros y y_dom. assert (y ≠ r) as Hy by set_solver. iFrame. iSplit;
            iIntros "Hstar"; iDestruct "Hstar" as (b C B)"(Hl & Hlif & HnS)";
            iExists b, C, B; iFrame; 
            iDestruct "HnS" as (esy Iy Jy Ry)"(HnS_frac & HnS_si & HnS_FP 
                          & HnS_cl & HnS_oc & HnS_if & HnS_star & Hφ)";
            iExists esy, Iy, Jy, Ry; iFrame; 
            assert (y =? r = false) as Hyr by (rewrite beq_nat_false_iff; done);
            iEval (rewrite Hyr); done. } 
          wp_pures.  
          awp_apply (unlockNode_spec_high with "[] [] [HnP_t HnP_C HnP_frac node_n]")
                without "HΦ"; try done. iExists es, (T + 1). iFrame.
                by iEval (rewrite <-beq_nat_refl).
          iAaccIntro with ""; try eauto with iFrame.
                    
  Admitted.

End multicopy.             
                    
                       

      
      
      

                    
       
       
    
                                        
        
    
    
                                                  
    
  
  
  
  
  
  

