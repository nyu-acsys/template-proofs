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
Parameter maintenance : val.

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
          | SOME "_" => "tr" "p" "s" "k" end end  
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
    
Definition delete (r: Node) : val :=
  λ: "k",
    let: "pc" := traverse r "k" in
    let: "c" := Snd "pc" in
    if: ~ (inContents "c" "k") then
      #false
    else
      match: try_constraint "c" with
        NONE => #false
      | SOME "_" => maintenance "k";; #true end.        
    
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

Section skiplist_v0.
  Context {Σ} `{!heapGS Σ, !skG Σ}.
  Notation iProp := (iProp Σ).
  
  Global Definition sstrN N := N .@ "sstr".
  Global Definition threadN N := N .@ "thread".

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

  Definition C (s: State) (n: Node) : gset K :=
    if decide (mark s n) then ∅ else PC s n.

  Parameter out_set : multiset_flowint_ur K → gset K.
  Parameter out_map : multiset_flowint_ur K → gmap Node (gset K).

  Definition keyset (I : multiset_flowint_ur K) n := 
    dom_ms (inf I n) ∖ dom_ms (out I n).
    
  Definition SearchStr2 γ_s (s: State) : iProp := 
    own γ_s (to_frac_agree (1/2) (gcont s)).
  
  Definition SearchStr γ_s (s: State) : iProp := 
    own γ_s (to_frac_agree (1/2) (gcont s)).

  (** data structure specific inv *)  

  Definition node_local_pure s n : iProp :=
      ⌜¬ (mark s n) → out_set (intf s n) ⊆ inset K (intf s n) n⌝
    ∗ ⌜C s n ⊆ keyset (intf s n) n⌝
    ∗ ⌜mark s n → out_set (intf s n) ≠ ∅⌝.

  Definition node_local_inv s n : iProp :=
      own (γ_I s) (◯ intf s n) 
    ∗ own (γ_ks s) (◯ prod (keyset (intf s n) n, C s n))
    ∗ node_local_pure s n.

  Definition per_tick_inv r s : iProp := 
      own (γ_I s) (● (gintf s)) ∗ own (γ_ks s) (● prod (KS, gcont s))
    ∗ ⌜inset K (intf s r) r = KS⌝ ∗ ⌜out_set (intf s r) = KS⌝
    ∗ ⌜¬ mark s r⌝
    ∗ [∗ set] n ∈ (FP s), node_local_inv s n.
    
  Definition transition_inv s s' : Prop :=
      (∀ n, n ∈ FP s → mark s n → out_map (intf s n) = out_map (intf s' n))
    ∧ (∀ n, n ∈ FP s → mark s n → mark s' n)
    ∧ (∀ n, n ∈ FP s → 
        (¬ mark s n ∧ mark s' n ∧ out_set (intf s n) ≠ out_set (intf s' n)) ∨
        (mark s n ∧ mark s' n ∧ out_set (intf s n) = out_set (intf s' n)))
    ∧ (∀ n, n ∈ FP s → PC s n = PC s' n)
    ∧ (FP s ⊆ FP s').
  
  (** History Inv *)

  Definition history_inv γ_t γ_m r (M: gmap nat (gset K)) T s : iProp :=
    ∃ (Ag_M: gmap nat (agreeR (gsetO K))),
      own γ_t (● MaxNat T) ∗ own γ_m (● Ag_M)
    ∗ ⌜∀ t, t ≤ T ↔ t ∈ dom (gset nat) M⌝ ∗ ⌜M !!! T = s⌝
    ∗ ⌜map_Forall (λ k a, a = to_agree (M !!! k)) Ag_M⌝  
    ∗ ⌜∀ t, t < T → M !!! t ≠ M !!! (t+1)%nat⌝
    ∗ ([∗ set] t ∈ dom (gset nat) M ∖ {[ T ]}, per_tick_inv r (M !!! t))
    ∗ ⌜∀ t, t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝.

  (** resources inv *)

  Definition nodeFull s n : iProp :=
    ∃ m In pc,
      node n m In pc
    ∗ ⌜m = mark s n⌝ ∗ ⌜In = intf s n⌝ ∗ ⌜pc = PC s n⌝  
    ∗ own (γ_I s) (◯ In)
    ∗ own (γ_ks s) (◯ prod (keyset In n, C s n)).   
  
  Definition resources s : iProp :=
      [∗ set] n ∈ FP s, nodeFull s n. 
    
  Definition res_inv r s : iProp :=
      per_tick_inv r s
    ∗ resources s.
    
  (** Helping Inv **)
  
  Definition map_max (M: gmap nat State) : nat := 
    max_list (elements (dom (gset nat) M)).
 
  Definition seq_spec (k: K) C res : Prop := Ψ searchOp k C C res. 
  
  Definition pau N γ_s P (Q : val → iProp) k := 
    (▷ P -∗ ◇ AU << ∀ C, SearchStr γ_s C >> 
                  @ ⊤ ∖ (↑(sstrN N) ∪ ↑(threadN N)), ∅
                 << ∃ res, SearchStr γ_s C 
                           ∗ ⌜seq_spec k C res⌝, COMM Q #res >>)%I.

  Definition pending (P: iProp) k t0 vp  (M: gmap nat State) : iProp := 
    P ∗ ⌜∀ t, t0 ≤ t ≤ map_max M → ¬ seq_spec k (gcont (M !!! t)) vp⌝.

  Definition done (γ_tk: gname) (Q: val → iProp) k (t0: nat) (vp: bool)   
                  (M: gmap nat State) : iProp := 
      (Q #vp ∨ own γ_tk (Excl ())) 
    ∗ ⌜∃ t, t0 ≤ t ≤ map_max M ∧ seq_spec k (gcont (M !!! t)) vp⌝.

  Definition helping_state γ_sy γ_tk P Q k t0 vp M : iProp :=
      own γ_sy (to_frac_agree (1/2) M)
    ∗ (pending P k t0 vp M ∨ done γ_tk Q k t0 vp M).

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
      ∗ inv (threadN N) (∃ M, helping_state γ_sy γ_tk P Q k t0 vp M).

  Definition helping_inv (N: namespace) γ_t γ_s γ_td γ_ght M : iProp :=
    ∃ (R: gset proph_id) (hγt: gmap proph_id (agreeR _)),
        own γ_td (● R)
      ∗ own γ_ght (● hγt) ∗ ⌜dom (gset proph_id) hγt = R⌝  
      ∗ ([∗ set] t_id ∈ R, reg N γ_t γ_s γ_ght t_id M).
      
      
  Definition thread_id γ_t γ_ght t_id : iProp := 
    ∃ t0 γ_sy, thread_vars γ_t γ_ght t_id t0 γ_sy.
  
  Definition past_state γ_t γ_ght γ_m t_id (s: State) : iProp :=
    ∃ t0 γ_sy t, 
      thread_vars γ_t γ_ght t_id t0 γ_sy 
    ∗ own γ_m (◯ {[t := to_agree s]}) ∗ ⌜t0 ≤ t⌝.      

  (** Final Invariant *)

  Definition searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r: iProp := 
    inv (sstrN N) 
    (∃ s M T,
      SearchStr2 γ_s s
    ∗ res_inv r s
    ∗ history_inv γ_t γ_m r M T s
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
                             | false => ⌜k ∉ out_set In⌝ end),
              RET (match succ with true => (#m, SOMEV #n') 
                                 | false => (#m, NONEV) end)  >>>)%I.

  Parameter try_constraint_trav_spec : ∀ (N: namespace) (k: K) (p c s: Node),
     ⊢ (<<< ∀ mp Ip pcp, node p mp Ip pcp >>>
           try_constraint #p #c #s @ ⊤ ∖ ↑(sstrN N)
       <<< ∃ (succ: bool) Ip',
              node p mp Ip' pcp
            ∗ (match succ with true => ⌜mp = false ∧ k ∈ (out_map Ip) !!! c⌝
                                     ∗ ⌜k ∈ (out_map Ip') !!! s⌝ 
                             | false => ⌜mp = true ∨ k ∉ (out_map Ip) !!! c⌝
                                      ∗ ⌜Ip' = Ip⌝ end),
              RET (match succ with true => SOMEV #() 
                                 | false => NONEV end)  >>>)%I.

  (** Some lemmas *)

  Parameter ghost_update_keyset : ∀ γ_k dop (k: K) Cn Cn' res K1 C,
    ⊢   ⌜Ψ dop k Cn Cn' res⌝ 
      ∗ own γ_k (● prod (KS, C)) 
      ∗ own γ_k (◯ prod (K1, Cn))
      ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝ ==∗ 
        ∃ C', 
          ⌜Ψ dop k C C' res⌝ 
        ∗ own γ_k (● prod (KS, C'))
        ∗ own γ_k (◯ prod (K1, Cn')).
          
End skiplist_v0.
    

          
            
      
         
      
      
          
        
    
  
  
  
  
  
  