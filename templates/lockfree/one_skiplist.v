(* Herlihy Skiplist with a single level *)

From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Export one_shot_proph typed_proph.
Require Export multiset_flows search_str keyset_ra.

(** Assumed functions to retrieve next pointer from a node *)
Parameter nextLoc : Node → loc.
Parameter getNextLoc : val.

Parameter inContents : val.
Parameter findNext : val.
Parameter try_constraint : val.

(** Template algorithms *)

Definition traverse_rec (r: Node) : val :=
  rec: "tr" "p" "c" "k" :=
    let: "fn_ck" := findNext "c" "k" in
    if: Fst "fn_ck" then
      match: Snd "fn_ck" with
        NONE => ""
      | SOME "s" =>
          match: try_constraint "p" "c" "s" with
            NONE =>
              let: "fn_hk" := findNext "h" "k" in
              match: Snd "fn_hk" with
                NONE => ""
              | SOME "n" => 
                  "tr" #r "n" "k" end
          | SOME "" => "tr" "p" "s" "k" end end  
    else
      match: Snd "fn_ck" with
        NONE => ("p", "c")
      | SOME "s" => "tr" "c" "s" "k" end.

Definition traverse (r: Node) : val := 
  λ: "k", 
    let: "fn_hk" := findNext #r "k" in
    match: Snd "fn_hk" with
      NONE => ""
    | SOME "n" => 
        traverse_rec r #r "n" "k" end.

Definition search (r: Node) : val :=
  λ: "k",
    let: "pc" := traverse r "k" in
    let: "c" := Snd "pc" in
    inContents "c" "k".
    
(** Proof Setup **)

Definition K := Z.
(* Parameter KS : gset K.*)

(*
The state stores:
0) set of nodes
1) ghost location for interface
2) global interface
3) ghost location for keyset
4) global contents
5) map from nodes to node-local info

Node local info:
1) singleton interface
2) keyset
3) physical contents
4) Marking
*)

Definition State := gset K.
Definition AbState := gset K.

(* RAs used in proof *)

Definition stateUR := gsetUR K.
Definition flow_KR := authR (multiset_flowint_ur K).
Definition auth_natUR := authUR $ max_natUR.
Definition frac_natR := dfrac_agreeR $ stateUR.
Definition map_gsetKR := authR $ gmapUR nat $ agreeR (stateUR).
Definition tokenUR := exclR unitO.
Definition frac_mapR := dfrac_agreeR $ gmapUR nat stateUR.
Definition set_tidR := authR (gsetUR proph_id). 
Definition thread_viewR := authUR $ gmapUR proph_id $ agreeR $ 
                                                        prodO natO gnameO.
Definition auth_keysetUR := authUR $ (keysetUR K).

Class skG Σ := SK {
                  sk_auth_natG :> inG Σ auth_natUR;
                  sk_frac_natG :> inG Σ frac_natR;
                  sk_map_natG :> inG Σ map_gsetKR;
                  sk_tokenG :> inG Σ tokenUR;
                  sk_frac_mapG :> inG Σ frac_mapR;
                  sk_set_tidG :> inG Σ set_tidR;
                  sk_thread_viewG :> inG Σ thread_viewR;
                  sk_flow_viewG :> inG Σ flow_KR;
                  sk_auth_keysetG :> inG Σ auth_keysetUR;
                 }.
                 
Definition skΣ : gFunctors :=
  #[ GFunctor auth_natUR; GFunctor frac_natR; GFunctor map_gsetKR;
     GFunctor tokenUR; GFunctor frac_mapR; GFunctor set_tidR;
     GFunctor thread_viewR; GFunctor flow_KR; GFunctor auth_keysetUR ].
  
Instance subG_skΣ {Σ} : subG skΣ Σ → skG Σ.
Proof. solve_inG. Qed.

Section sk.
  Context {Σ} `{!heapGS Σ, !skG Σ}.
  Notation iProp := (iProp Σ).
  
  Global Definition sstrN N := N .@ "sstr".
  Global Definition threadN N := N .@ "thread".

  Definition SearchStr2 γ_s (s: AbState) : iProp := 
    own γ_s (to_frac_agree (1/2) s).
  
  Definition SearchStr γ_s (s: AbState) : iProp := 
    own γ_s (to_frac_agree (1/2) s).

  Definition keyset (I : multiset_flowint_ur K) n := 
    dom_ms (inf I n) ∖ dom_ms (out I n).
  
  (** History Inv *)
  
  Definition map_max (M: gmap nat State) : nat := 
    max_list (elements (dom (gset nat) M)).   

  Definition history_inv γ_t γ_m T M M' s : iProp := 
      own γ_t (● MaxNat T) ∗ own γ_m (● M')
    ∗ ⌜map_Forall (λ k a, a = to_agree (M !!! k)) M'⌝  
    ∗ ⌜T = map_max M⌝ ∗ ⌜M !!! T = s⌝
    ∗ ⌜∀ t, t < T → M !!! t ≠ M !!! (t+1)%nat⌝.

  (** Structural Inv *)
  
  Parameter node : Node → bool → (multiset_flowint_ur K) → (gset K) → iProp.
  Parameter node_timeless_proof : ∀ r n es V, Timeless (node r n es V).
  Global Instance node_timeless r n es V: Timeless (node r n es V).
  Proof. apply node_timeless_proof. Qed.  

  Parameter PC : State → Node → gset K.
  Parameter mark : State → Node → bool.
  Parameter gintf : State → (multiset_flowint_ur K).
  Parameter intf : State → Node → (multiset_flowint_ur K).
  Parameter γ_I : State → gname.
  Parameter γ_ks : State → gname.
  Parameter gcont : State → gset K.
  Parameter FP : State → gset Node.

  Parameter out : multiset_flowint_ur K → gset K.
  Parameter out_map : multiset_flowint_ur K → (nzmap K nat).

  
  Definition C (s: State) (n: Node) : gset K :=
    if decide (mark s n) then ∅ else PC s n.
      
  Definition node_local_pure s n : iProp :=
      ⌜¬ (mark s n) → out (intf s n) ⊆ inset K (intf s n) n⌝
    ∗ ⌜C s n ⊆ keyset (intf s n) n⌝
    ∗ ⌜mark s n → out (intf s n) ≠ ∅⌝.

  Definition node_local_inv s n : iProp :=
      own (γ_I s) (◯ intf s n) 
    ∗ own (γ_ks s) (◯ prod (keyset (intf s n) n, C s n))
    ∗ node_local_pure s n.

  Definition per_tick_inv r s : iProp := 
      own (γ_I s) (● (gintf s)) ∗ own (γ_ks s) (● prod (KS, gcont s))
    ∗ ⌜inset K (intf s r) r = KS⌝ ∗ ⌜out (intf s r) = KS⌝
    ∗ ⌜¬ mark s r⌝
    ∗ [∗ set] n ∈ (FP s), node_local_inv s n.
    
  Definition transition_inv s s' : Prop :=
      (∀ n, n ∈ FP s → mark s n → out_map (intf s n) = out_map (intf s' n))
    ∧ (∀ n, n ∈ FP s → mark s n → mark s' n)
    ∧ (∀ n, n ∈ FP s → (¬ mark s n ∧ mark s' n ∧ out (intf s n) ≠ out (intf s' n)) ∨
                       (mark s n ∧ mark s' n ∧ out (intf s n) = out (intf s' n)))
    ∧ (∀ n, n ∈ FP s → PC s n = PC s' n)
    ∧ (FP s ⊆ FP s').
  
  Definition nodeFull s n : iProp :=
    ∃ m In pc,
      node n m In pc
    ∗ ⌜m = mark s n⌝ ∗ ⌜In = intf s n⌝ ∗ ⌜pc = PC s n⌝  
    ∗ own (γ_I s) (◯ In)
    ∗ own (γ_ks s) (◯ prod (keyset In n, if m then ∅ else pc)).   
  
  Definition resources s : iProp :=
      [∗ set] n ∈ FP s, nodeFull s n. 
    
  Definition structural_inv r (M: gmap nat State) T s : iProp :=
      ([∗ set] t ∈ dom (gset nat) M, per_tick_inv r (M !!! t))
    ∗ ⌜∀ t, t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝
    ∗ resources s.
(*
  Global Instance Timeless_str_inv r M T : Timeless (structural_inv r M T).
  Proof.
    rewrite /structural_inv.
    repeat apply bi.sep_timeless; try apply _.
  Qed.
*)      
  (** Helping Inv **)
 
  Definition search_seq_spec (k: K) C res : Prop := Ψ searchOp k C C res. 
  
  Definition pau N γ_s P (Q : val → iProp) k := 
    (▷ P -∗ ◇ AU << ∀ C, SearchStr γ_s C >> 
                  @ ⊤ ∖ (↑(sstrN N) ∪ ↑(threadN N)), ∅
                 << ∃ res, SearchStr γ_s C 
                           ∗ ⌜search_seq_spec k C res⌝, COMM Q #res >>)%I.

  Definition pending (P: iProp) k (M: gmap nat State) (t0: nat) (vp: bool) : iProp := 
    P ∗ ⌜∀ t, t0 ≤ t ≤ map_max M → ¬search_seq_spec k (gcont (M !!! t)) vp⌝.

  Definition done (γ_tk: gname) (Q: val → iProp) k  
                  (M: gmap nat State) (t0: nat) (vp: bool) : iProp := 
      (Q #vp ∨ own γ_tk (Excl ())) 
    ∗ ⌜∃ t, t0 ≤ t ≤ map_max M ∧ search_seq_spec k (gcont (M !!! t)) vp⌝.

  Definition helping_state γ_sy γ_tk k P Q t0 vp M : iProp :=
      own γ_sy (to_frac_agree (1/2) M)
    ∗ (pending P k M t0 vp ∨ done γ_tk Q k M t0 vp).

  Definition thread_vars γ_t γ_ght t_id t0 γ_sy : iProp := 
    own γ_ght (◯ {[t_id := to_agree (t0, γ_sy)]}) ∗ own γ_t (◯ MaxNat t0).

  Definition reg (N: namespace) (γ_t γ_s γ_ght: gname)
                   (t_id: proph_id) M : iProp :=
    ∃ (P: iProp) (Q: val → iProp) k (γ_tk γ_sy: gname) 
    t0 vp (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght t_id t0 γ_sy  
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ □ pau N γ_s P Q k
      ∗ inv (threadN N) (∃ M, helping_state γ_sy γ_tk k P Q t0 vp M).

  Definition helping_inv (N: namespace) γ_t γ_s γ_td γ_ght M : iProp :=
    ∃ (R: gset proph_id) (hγt: gmap proph_id (agreeR _)),
        own γ_td (● R)
      ∗ own γ_ght (● hγt) ∗ ⌜dom (gset proph_id) hγt = R⌝  
      ∗ ([∗ set] t_id ∈ R, reg N γ_t γ_s γ_ght t_id M).

  (** Final Invariant *)

  Definition searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r: iProp := 
    inv (sstrN N) 
    (∃ (T: nat) (s: State) M (M': gmap nat (agreeR (gsetUR K))),
      SearchStr2 γ_s (gcont s)
    ∗ history_inv γ_t γ_m T M M' s
    ∗ structural_inv r M T s
    ∗ helping_inv N γ_t γ_s γ_td γ_ght M).
        
    
  (** Helper functions specs *)
    
  Parameter inContents_spec : ∀ (N: namespace) (k: K) (n: Node),
     ⊢ (<<< ∀ m In pc, node n m In pc >>>
           inContents #n #k @ ⊤ ∖ ↑(sstrN N)
       <<< ∃ (v: bool),
              node n m In pc ∗ ⌜v ↔ k ∈ pc⌝,
              RET #v >>>)%I.

  Parameter findNext_spec : ∀ (N: namespace) (k: K) (n: Node),
     ⊢ (<<< ∀ m In pc, node n m In pc >>>
           findNext #n #k @ ⊤ ∖ ↑(sstrN N)
       <<< ∃ (succ: bool) (n': Node),
              node n m In pc
            ∗ (match succ with true => ⌜k ∈ outset K In n'⌝ 
                             | false => ⌜k ∉ out In⌝ end),
              RET (match succ with true => (#m, SOMEV #n') 
                                 | false => (#m, NONEV) end)  >>>)%I.

  (** Some lemmas *)

  Parameter ghost_update_keyset : ∀ γ_k dop (k: K) Cn Cn' res K1 C,
    ⊢ ⌜Ψ dop k Cn Cn' res⌝ ∗ own γ_k (● prod (KS, C)) ∗ own γ_k (◯ prod (K1, Cn))
    ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝
    ==∗ ∃ C', ⌜Ψ dop k C C' res⌝ ∗ own γ_k (● prod (KS, C'))
      ∗ own γ_k (◯ prod (K1, Cn')).

  (** Proof *)
  
  Definition thread_id γ_t γ_ght t_id : iProp := 
    ∃ t0 γ_sy, thread_vars γ_t γ_ght t_id t0 γ_sy.
  
  Definition past_state γ_t γ_ght γ_m t_id (s: State) : iProp :=
    ∃ t0 γ_sy t, 
      thread_vars γ_t γ_ght t_id t0 γ_sy 
    ∗ own γ_m (◯ {[t := to_agree s]}) ∗ ⌜t0 ≤ t⌝.
    
  Definition traverse_rec_inv γ_t γ_ght γ_m t_id k s p c : iProp :=
      past_state γ_t γ_ght γ_m t_id s
    ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
    ∗ ⌜¬ mark s p⌝
    ∗ ⌜k ∈ inset K (intf s p) p⌝
    ∗ ⌜k ∈ outset K (intf s p) c⌝
    ∗ ⌜k ∈ inset K (intf s c) c⌝. 


  Lemma traverse_rec_spec N γ_s γ_t γ_m γ_td γ_ght r t_id (k: K) s p c:
    ⌜k ∈ KS⌝ -∗
      searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r -∗
       thread_id γ_t γ_ght t_id -∗  
        traverse_rec_inv γ_t γ_ght γ_m t_id k s p c -∗
          <<< True >>>
            traverse_rec r #p #c #k @ (↑(sstrN N))
          <<< ∃ (p c: Node) (s: State), 
                past_state γ_t γ_ght γ_m t_id s
              ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
              ∗ ⌜¬ mark s p⌝
              ∗ ⌜k ∈ inset K (intf s p) p⌝
              ∗ ⌜k ∈ outset K (intf s p) c⌝
              ∗ ⌜¬ mark s c⌝
              ∗ ⌜k ∈ keyset (intf s c) c⌝, 
                RET (#p, #c) >>>.
  Proof.
    iIntros "%k_in_KS #HInv #Htid". iLöb as "IH". 
    iIntros "#Tr_inv" (Φ) "AU".
    wp_lam. wp_pures. awp_apply (findNext_spec).
    iInv "HInv" as (T0 s0 M0 M0') "(>Half & >Hist & >Str & Help)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c.
    { admit. }
    iDestruct "Str" as "(Per_tick & Trans_inv & Resources)".
    iEval (unfold resources) in "Resources". 
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Resources" as "(NodeFull_r & Resources_rest)".
    iDestruct "NodeFull_r" as (mc Ic pcc) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "AU". iNext; iExists T0, s0, M0, M0'.
      iFrame. unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Resources_rest".
      iExists mc, Ic, pcc. iFrame. }
    iIntros (succ n) "(Node & Hif)".
    destruct succ; last first.
    - iDestruct "Hif" as %k_notin_Outc.
      iAssert (
      iModIntro. iSplitR "AU".
      { admit. }
      wp_pures. destruct mc.
      + wp_pures. 
        
  Admitted.


  Lemma traverse_spec N γ_s γ_t γ_m γ_td γ_ght r t_id (k: K) :
    ⌜k ∈ KS⌝ -∗
      searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r -∗
       thread_id γ_t γ_ght t_id -∗ 
        <<< True >>>
           traverse r #k @ (↑(sstrN N))
        <<< ∃ (p c: Node) (s: State), 
              past_state γ_t γ_ght γ_m t_id s
            ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
            ∗ ⌜¬ mark s p⌝
            ∗ ⌜k ∈ inset K (intf s p) p⌝
            ∗ ⌜k ∈ outset K (intf s p) c⌝
            ∗ ⌜¬ mark s c⌝
            ∗ ⌜k ∈ keyset (intf s c) c⌝, 
              RET (#p, #c) >>>.
  Proof.
    iIntros "%k_in_KS #HInv #Htid" (Φ) "AU".
    wp_lam. awp_apply (findNext_spec).
    iInv "HInv" as (T0 s0 M0 M0') "(>Half & >Hist & >Str & Help)".
    iAssert (⌜r ∈ FP s0⌝)%I as %FP_r0.
    { admit. }
    iDestruct "Str" as "(Per_tick & Trans_inv & Resources)".
    iEval (unfold resources) in "Resources". 
    rewrite (big_sepS_delete _ (FP s0) r); last by eauto.
    iDestruct "Resources" as "(NodeFull_r & Resources_rest)".
    iDestruct "NodeFull_r" as (mr Ir pcr) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "AU". iNext; iExists T0, s0, M0, M0'.
      iFrame. unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) r); last by eauto. 
      iFrame "Resources_rest".
      iExists mr, Ir, pcr. iFrame. }
    iIntros (succ n) "(Node & Hif)".
    destruct succ; last first.
    - iAssert (⌜k ∉ KS⌝)%I as %k_notin_KS.
      { iAssert (⌜T0 ∈ dom (gset nat) M0⌝)%I as %t_in_M0.
        { admit. }
        rewrite (big_sepS_delete _ (dom (gset nat) M0) T0); last by eauto.
        iDestruct "Per_tick" as "(Tick_T & Per_tick_rest)".
        iAssert (⌜M0 !!! T0 = s0⌝)%I as %M_t_s.
        { by iDestruct "Hist" as "(_&_&_&_&%&_)". } 
        iEval (rewrite M_t_s) in "Tick_T". 
        iDestruct "Tick_T" as "(HI & HKS & Ins_r & Out_r 
          & Mark_r & Hbig_star)".
        iDestruct "Hif" as %Hif.
        iDestruct "Out_r" as %Out_r.
        iDestruct "Node_rest" as "(_&%H'&_)".
        iPureIntro. rewrite <-H' in Out_r.
        by rewrite Out_r in Hif. }
      iClear "∗#". clear -k_in_KS k_notin_KS. exfalso; try done.
    - iModIntro.
      iDestruct "Htid" as (t0 γ_sy)"Htid".
      iAssert (own γ_m (◯ {[T0 := to_agree s0]}))%I as "#HT0".
      { admit. }
      iAssert (⌜t0 ≤ T0⌝)%I as %t0_le_T0.
      { admit. }
      iAssert (past_state γ_t γ_ght γ_m t_id s0)%I as "#Hpast".
      { iExists t0, γ_sy, T0. iFrame "#%". }
      iAssert (⌜r ∈ FP s0⌝)%I as %FP_r.
      { admit. }
      iAssert (⌜n ∈ FP s0⌝)%I as %FP_n.
      { admit. }
      iAssert (⌜T0 ∈ dom (gset nat) M0⌝)%I as %T0_in_M0.
      { admit. }
      rewrite (big_sepS_delete _ (dom (gset nat) M0) T0); last by eauto.
      iDestruct "Per_tick" as "(Tick_T & Per_tick_rest)".
      iAssert (⌜M0 !!! T0 = s0⌝)%I as %M_t_s.
      { by iDestruct "Hist" as "(_&_&_&_&%&_)". } 
      iEval (rewrite M_t_s) in "Tick_T". 
      iDestruct "Tick_T" as "(HI & HKS & %Ins_r & %Out_r 
          & %Mark_r & Hbig_star)".    
      iAssert (⌜k ∈ inset K (intf s0 r) r⌝)%I as %k_in_Insr.
      { iPureIntro. by rewrite Ins_r. }
      iDestruct "Hif" as %k_in_Outr.
      iAssert (⌜n ≠ r⌝)%I as "%n_neq_r".
      { admit. }
      iAssert (⌜n ∈ FP s0 ∖ {[r]}⌝)%I as "%".
      { clear -FP_n n_neq_r. iPureIntro; set_solver. } 
      rewrite (big_sepS_delete _ (FP s0 ∖ {[r]}) n); last by eauto.
      iDestruct "Resources_rest" as "(NodeFull_n & Resources_rest)".
      iDestruct "NodeFull_n" as (mn In pcn) "(Node_n & Node_n_rest)".
      iAssert (⌜Ir = intf s0 r⌝)%I as %HIr.
      { by iDestruct "Node_rest" as "(_&%&_)". }
      rewrite HIr in k_in_Outr.
      iAssert (⌜k ∈ inset K (intf s0 n) n⌝)%I as %k_in_Insn.
      { admit. }
      iAssert (traverse_rec_inv γ_t γ_ght γ_m t_id k s0 r n)%I as "#Tr_inv".
      { iFrame "#%". }
      iSplitR "AU". 
      { iNext. iExists T0, s0, M0, M0'.
        iFrame "Half Hist Help". iFrame "Trans_inv".
        iSplitL "HI HKS Hbig_star Per_tick_rest".
        rewrite (big_sepS_delete _ (dom (gset nat) M0) T0); last by eauto.
        iFrame "Per_tick_rest". rewrite M_t_s.
        iFrame. iPureIntro; repeat split; try done.
        unfold resources. 
        rewrite (big_sepS_delete _ (FP s0) r); last by eauto.
        rewrite (big_sepS_delete _ (FP s0 ∖ {[r]}) n); last by eauto.
        iFrame "Resources_rest". iSplitL "Node Node_rest". 
        iExists mr, Ir, pcr. iFrame.
        iExists mn, In, pcn. iFrame. }   
      wp_pures. awp_apply traverse_rec_spec; try done.
      { by iExists t0, γ_sy. }
      iAaccIntro with ""; try done.
      { iIntros "_". iModIntro. iFrame. }
      iIntros (p c s) "Hpost".
      iMod "AU" as "[_ [_ Hcomm]]".
      iSpecialize ("Hcomm" $! p c s).
      iMod ("Hcomm" with "Hpost") as "HΦ".
      by iModIntro.  
  Admitted.

  
  Lemma search_spec N γ_s γ_t γ_m γ_td γ_ght r t_id (k: K) :
    ⌜k ∈ KS⌝ -∗
      searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r -∗
        thread_id γ_t γ_ght t_id -∗ 
          <<< True >>>
            search r #k @ ⊤ ∖ (↑(sstrN N))
          <<< ∃ (res: bool) (s: State), 
                past_state γ_t γ_ght γ_m t_id s 
              ∗ ⌜search_seq_spec k (gcont s) res⌝, 
                RET #res >>>.
  Proof.
    iIntros "% #HInv #Htid" (Φ) "AU".
    rename H into k_in_KS.
    wp_lam. wp_pures.
    awp_apply traverse_spec; try done.
    iAaccIntro with ""; try done.
    { eauto with iFrame. }
    iIntros (p c s) "(#Hpast & %)".
    destruct H as [FP_p [FP_c [Unmarkedp [k_in_pins 
      [k_in_pouts [Unmarkedc k_in_cks]]]]]].
    iModIntro. wp_pures.
    awp_apply (inContents_spec).
    iInv "HInv" as (T0 s0 M0 M0') "(>Half & >Hist & >Str & Help)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    iDestruct "Str" as "(Per_tick & Trans_inv & Resources)".
    iEval (unfold resources) in "Resources". 
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Resources" as "(NodeFull_c & Resources_rest)".
    iDestruct "NodeFull_c" as (mc Ic pcc) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "AU". iNext; iExists T0, s0, M0, M0'.
      iFrame. unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Resources_rest".
      iExists mc, Ic, pcc. iFrame. }
    iIntros (res) "(Node & Hres)". iDestruct "Hres" as %Hres.
    iAssert (past_state γ_t γ_ght γ_m t_id s)%I as "#Hpast2". { done. }
    iDestruct "Hpast2" as (t0 γ_sy t)"(Hth_vars & t_s & %)".
    iAssert (⌜t ∈ dom (gset nat) M0⌝)%I as %t_in_M0.
    { admit. }
    rewrite (big_sepS_delete _ (dom (gset nat) M0) t); last by eauto.
    iDestruct "Per_tick" as "(Tick_t & Per_tick_rest)".
    iAssert (⌜M0 !!! t = s⌝)%I as %M0_t_s.
    { admit. } iEval (rewrite M0_t_s) in "Tick_t". 
    iDestruct "Tick_t" as "(HI & HKS & Ins_r & Out_r & Hbig_star)".
    rewrite (big_sepS_delete _ (FP s) c); last by eauto.
    iDestruct "Hbig_star" as "(Node_local & Hbig_star_rest)".
    iDestruct "Node_local" as "(HIc & Hksc & Hpurec)".
    iAssert (⌜pcc = PC s c⌝)%I as %->.
    { (* interpolation *) admit. }
    iAssert (⌜Ψ searchOp k (C s c) (C s c) res⌝)%I as %HΨ_c.
    { iPureIntro. unfold Ψ. split; try done. destruct res; 
      unfold C; destruct (decide (mark s c)); try done.
      - by apply Hres.
      - intros ?. by apply Hres. }
    iAssert (⌜C s c ⊆ keyset (intf s c) c⌝)%I as %cc_sub_ksc.
    { by iDestruct "Hpurec" as "(_ & %)". }
    iMod (ghost_update_keyset (γ_ks s) searchOp k (C s c) (C s c) res 
      (keyset (intf s c) c) (gcont s)
      with "[$HKS $Hksc]") as (C') "(% & HKS & Hksc)".
    { iPureIntro; repeat (split; try done). }
    rename H0 into HΨ.
    iAssert (⌜C' = gcont s⌝)%I as %->.
    { by destruct HΨ as [? _]. }
    iAssert (⌜search_seq_spec k (gcont s) res⌝)%I as %HPost.
    { by iPureIntro. }
    iMod "AU" as "[_ [_ Hcomm]]". admit.
    iSpecialize ("Hcomm" $! res s).
    iMod ("Hcomm" with "[$Hpast]") as "HΦ".
    { by iPureIntro. }
    
    iModIntro. iFrame "HΦ". 
    { iNext. iExists T0, s0, M0, M0'.
      iFrame "Half Hist Help". iFrame "Trans_inv".
      iSplitR "Node Node_rest Resources_rest".
      rewrite (big_sepS_delete _ (dom (gset nat) M0) t); last by eauto.
      iFrame "Per_tick_rest". iEval (rewrite M0_t_s). iFrame "HI HKS".
      rewrite (big_sepS_delete _ (FP s) c); last by eauto.
      iFrame"Hbig_star_rest". iFrame.
      unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Resources_rest". iExists mc, Ic, (PC s c). iFrame. }
  Admitted.      
          
            
      
         
      
      
          
        
    
  
  
  
  
  
  