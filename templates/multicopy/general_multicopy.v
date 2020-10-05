From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export KT_flows inset_flows_multicopy.

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
    if: "t" ≠ #0 
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

  Definition inFP γ_f (n: Node) : iProp := own γ_f (◯ {[n]}).

  Definition closed γ_f (es: esT) : iProp := ∀ n, ⌜es !!! n  ≠ ∅⌝ → inFP γ_f n.

  Definition inflow_zero (I: KT_flowint_ur K) : iProp := ⌜∀ n, inf I n = ∅⌝. 

  Definition inflow_R (R: inset_flowint_ur K) r : iProp := 
    ⌜∀ n k, if n =? r then in_inset K k R n else ¬ in_inset K k R n⌝. 

  Definition outflow_constraint_I (In: KT_flowint_ur K) (es: esT) 
                          (Cn Bn: gmap K natUR) : iProp := 
    ⌜∀ n' k t, (k,t) ∈ outset_KT In n' ↔ 
                          k ∈ es !!! n' ∧ (Cn !!! k = 0) ∧ (Bn !! k = Some(t))⌝.

  Definition outflow_constraint_J (Jn: KT_flowint_ur K) (es: esT) 
                          (Cn Bn: gmap K natUR) : iProp := 
    ⌜∀ n' k t, (k,t) ∈ outset_KT Jn n' ↔ 
                          k ∈ es !!! n' ∧ (Cn !! k = Some(t))⌝.

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
              ⌜∀ k t, (k,t) ∈ inset_KT Jn n → t ≤ Bn !!! k⌝.

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
    ∗ (if (n =? r) then ⌜Bn = map_of_set H⌝ ∗ inflow_zero In else True)%I
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


  (** Proofs **)  

  Instance test r n γ_t T : Laterable (if n =? r then 
                                            own γ_t (●{1 / 2} T) else ⌜True⌝)%I.
  Proof. Admitted.

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
    iIntros "#HFP_n #Hlb H". iDestruct "H" as %t0_le_t1.
    iDestruct "k_in_KS" as %k_in_KS.
    iIntros (Φ) "AU". wp_lam. wp_pures.
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cn Bn)"HnP_n". iModIntro.
    wp_pures. iDestruct "HnP_n" as (es T)"(node_n & HnP_n')".
    wp_apply (inContents_spec with "node_n").
    iIntros (t) "(node_n & H)". iDestruct "H" as %Cn_val.
    wp_pures. case_eq (bool_decide (#t = #0)).
    - intros Ht. wp_pures.
      wp_apply (findNext_spec with "node_n").
      iIntros (b n1) "(node_n & Hif)". destruct b.
      + wp_pures. iDestruct "Hif" as %k_in_es.
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
           "(HnS_frac & HnS_si & HnS_FP & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iAssert (⌜es' = es⌝)%I as "%".  
        { admit. } subst es'.          
        iAssert (inFP γ_f n1)%I as "#HFP_n1".
        { iApply "HnS_cl". iPureIntro. 
          clear -k_in_es. set_solver. }
        iAssert (⌜(k, Bn !!! k) ∈ outset_KT In n⌝)%I as %outflow_n_n1.
        { admit. }
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
    iDestruct "HnP_n" as (es T)"(node_n & HnP_frac & HnP_Cn & HnP_t)".
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
      iDestruct "Hglob" as "(MCS & Hs & Ht & HI & HJ & HR & Hf 
                & Inf_I & Inf_J & Inf_R & _ & Max_ts & domm_IJ & domm_IR)".
      iAssert (⌜T = T1⌝)%I as %HT. { admit. } replace T1.          
      iAssert (own γ_t (● (MaxNat T)))%I with "[Ht HnP_t]" as "H".
      { admit. }          
      iAaccIntro with "H".
      { iIntros "H". iDestruct "H" as "(Ht & HnP_t)".
        iModIntro. iSplitR "AU HnP_frac HnP_Cn node_n HnP_t".
        iNext. iExists T, H1, I1, J1, R1. iFrame "∗ #". iFrame. }
      iIntros "H". iDestruct "H" as "(Ht & HnP_t)".
      iAssert (own γ_s (● (H1 ∪ {[(k,T)]})))%I with "[Hs]" as "Hs".
      { admit. }
      iAssert (maxTS (T+1) (H1 ∪ {[(k, T)]}))%I with "[Max_ts]" as "Max_ts".
      { iDestruct "Max_ts" as %Max_ts. iPureIntro. intros k' t' H.
        assert (((k',t') ∈ H1) ∨ (k' = k ∧ t' = T)) as Hor by set_solver.
        destruct Hor as [Hor | Hor]. 
          pose proof Max_ts k' t' Hor as Hres. lia.
          destruct Hor as [_ Hor]. replace t'. lia. }       
      iAssert (⌜set_of_map Cr ⊆ set_of_map Cr'⌝)%I as %Cr_sub_Cr'.
      { admit. }
      iAssert (own γ_s (◯ set_of_map Cr'))%I with "[HnP_Cn]" as "HnP_Cn".
      { admit. }
      iAssert (⌜r ∈ domm I1⌝)%I as %r_in_I.
      { admit. }
      rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
      iDestruct "Hstar" as "(H_r & Hstar')".
      iDestruct "H_r" as (br Cr'' Br'')"(Hl_r & Hlif_r & HnS_r)".
      iAssert (⌜br = true⌝)%I as %Hbr. { admit. } replace br.
      iDestruct "HnS_r" as (es' Ir Jr Rr) 
            "(HnS_frac & HnS_si & HnS_FP & HnS_cl & HnS_oc & 
                                        HnS_H & HnS_star & Hφ)".
      iAssert (⌜es' = es⌝)%I as "%".  
      { admit. } subst es'.      
      iAssert (⌜Cr'' = Cr⌝)%I as "%".  
      { admit. } subst Cr''.      
      iAssert (⌜Br'' = Br⌝)%I as "%".  
      { admit. } subst Br''.
      case_eq (Cr !! k).
      + intros t Cr_k.
        set (Br' := <[k := T]>Br).
        iAssert (frac_ghost_state γ_e γ_c γ_b r es Cr' Br' ∗ 
                    frac_ghost_state γ_e γ_c γ_b r es Cr' Br')%I 
              with "[HnP_frac HnS_frac]" as "(HnP_frac & HnS_frac)".
        { admit. }
        assert ((∃ n, k ∈ es !!! n ∧ n ≠ r) ∨ (∀ n, k ∉ es !!! n)) as Hes.
        { admit. } destruct Hes as [Hes | Hes].
        * destruct Hes as [n [k_in_es n_neq_r]].
          set (Jr'_out_r := (nzmap_imerge 
             (λ k' a1 _, if (decide (k' = (k, t))) then 0 else 
                         if (decide (k' = (k, T))) then 1 else a1) (out Jr n) (∅)): (KT_multiset)).
          set (Jr'_out := (nzmap_imerge 
                      (λ k' a1 _, if (decide (k = r)) then Jr'_out_r else a1)
                      (out_map Jr) (∅)) : (nzmap Node KT_multiset)).
          set (Jr' := ({| infR := 
          (inf_map Jr: gmap Node KT_multiset) ; 
           outR := (Jr'_out: nzmap Node KT_multiset) |})).
(*
          set (Jr1 : (KT_flowint_ur K) := Jr' : (KT_flowint_ur)).  
          iAssert (outflow_constraints r Ir Jr' Rr es Cr' Br')%I 
                    with "[HnS_oc]" as "HnS_oc".
          { admit. }
*)
  Admitted.

End multicopy.             
                    
                       

      
      
      

                    
       
       
    
                                        
        
    
    
                                                  
    
  
  
  
  
  
  

