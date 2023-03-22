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
Require Export multiset_flows search_structures keyset_ra.

(** Assumed functions to retrieve next pointer from a node *)
Parameter nextLoc : Node → loc.
Parameter getNextLoc : val.

Parameter inContents : val.
Parameter findNext : val.
Parameter try_constraint : val.
Parameter maintenance : val.
Parameter createNode: val.

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
              let: "fn_hk" := findNext #r "k" in
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
      
Definition insert (r: Node) : val :=
  rec: "ins" "k" :=
    let: "pc" := traverse r "k" in
    let: "p" := Fst "pc" in
    let: "c" := Snd "pc" in
    if: inContents "c" "k" then
      #false
    else
      let: "e" := createNode "k" "c" in
      match: try_constraint "p" "c" "e" with
        NONE => "ins" "k"
      | SOME "_" => #true end.
    
(*
The snapshot stores:
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

Definition K := Z.

Definition flowUR := authR (multiset_flowint_ur K).
Definition auth_keysetUR := authUR $ (keysetUR K).

Class skG Σ := SK {
                  sk_flowG :> inG Σ flowUR;
                  sk_auth_keysetG :> inG Σ auth_keysetUR;
                 }.
                 
Definition skΣ : gFunctors :=
  #[ GFunctor flowUR;  GFunctor auth_keysetUR ].
  
Instance subG_skΣ {Σ} : subG skΣ Σ → skG Σ.
Proof. solve_inG. Qed.

Section skiplist_v0.
  Context {Σ} `{!heapGS Σ, !skG Σ}.
  Notation iProp := (iProp Σ).
  
  Parameter node : Node → bool → (multiset_flowint_ur K) → (gset K) → iProp.
  Parameter node_timeless_proof : ∀ r n es V, Timeless (node r n es V).
  Global Instance node_timeless r n es V: Timeless (node r n es V).
  Proof. apply node_timeless_proof. Qed.  

  Parameter PC : snapshot → Node → gset K.
  Parameter mark : snapshot → Node → bool.
  Parameter gintf : snapshot → (multiset_flowint_ur K).
  Parameter intf : snapshot → Node → (multiset_flowint_ur K).
  Parameter γ_I : snapshot → gname.
  Parameter γ_ks : snapshot → gname.
  Parameter FP : snapshot → gset Node.

  Definition Cont (s: snapshot) (n: Node) : gset K :=
    if decide (mark s n) then ∅ else PC s n.

  Parameter out_set : multiset_flowint_ur K → gset K.
  Parameter out_map : multiset_flowint_ur K → gmap Node (gset K).
  Parameter keyset : multiset_flowint_ur K → gset K.
    
  (** data structure specific inv *)  

  Definition node_local_pure s n : iProp :=
      ⌜¬ (mark s n) → out_set (intf s n) ⊆ inset K (intf s n) n⌝
    ∗ ⌜Cont s n ⊆ keyset (intf s n)⌝
    ∗ ⌜mark s n → out_set (intf s n) ≠ ∅⌝.

  Definition node_local_inv s n : iProp :=
      own (γ_I s) (◯ intf s n) 
    ∗ own (γ_ks s) (◯ prod (keyset (intf s n), Cont s n))
    ∗ node_local_pure s n.

  Definition per_tick_inv r s : iProp := 
      own (γ_I s) (● (gintf s)) ∗ own (γ_ks s) (● prod (KS, abs s))
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
  
  (** resources inv *)

  Definition nodeFull s n : iProp :=
    ∃ m In pc,
      node n m In pc
    ∗ ⌜m = mark s n⌝ ∗ ⌜In = intf s n⌝ ∗ ⌜pc = PC s n⌝  
    ∗ own (γ_I s) (◯ In)
    ∗ own (γ_ks s) (◯ prod (keyset In, Cont s n)).   
  
  Definition resources s : iProp :=
      [∗ set] n ∈ FP s, nodeFull s n. 
        
  Definition skiplist_inv r (M: gmap nat snapshot) 
    (T: nat) (s: snapshot): iProp :=
      ([∗ set] t ∈ dom M, per_tick_inv r (M !!! t))
    ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝
    ∗ ⌜transition_inv (M !!! T) s⌝
    ∗ ([∗ set] n ∈ FP s, nodeFull s n).
    
  Instance skiplist_inv_timeless r M T s : Timeless (skiplist_inv r M T s).
  Proof.
  Admitted.     
    
  (** Helper functions specs *)
    
  Parameter inContents_spec : ∀ (k: K) (n: Node),
     ⊢ (<<< ∀∀ m In pc, node n m In pc >>>
           inContents #n #k @ ⊤
       <<< ∃∃ (v: bool),
              node n m In pc ∗ ⌜v ↔ k ∈ pc⌝,
              RET #v >>>)%I.

  Parameter findNext_spec : ∀ (k: K) (n: Node),
     ⊢ (<<< ∀∀ m In pc, node n m In pc >>>
           findNext #n #k @ ⊤
       <<< ∃∃ (succ: bool) (n': Node),
              node n m In pc
            ∗ (match succ with true => ⌜k ∈ outset K In n'⌝ 
                             | false => ⌜k ∉ out_set In⌝ end),
              RET (match succ with true => (#m, SOMEV #n') 
                                 | false => (#m, NONEV) end)  >>>)%I.

  Parameter try_constraint_trav_spec : ∀ (k: K) (p c s: Node),
     ⊢ (<<< ∀∀ mp Ip pcp, node p mp Ip pcp >>>
           try_constraint #p #c #s @ ⊤
       <<< ∃∃ (succ: bool) Ip',
              node p mp Ip' pcp
            ∗ (match succ with true => ⌜mp = false⌝ ∗ ⌜k ∈ (out_map Ip) !!! c⌝
                                     ∗ ⌜k ∈ (out_map Ip') !!! s⌝ 
                             | false => ⌜mp = true ∨ k ∉ (out_map Ip) !!! c⌝
                                      ∗ ⌜Ip' = Ip⌝ end),
              RET (match succ with true => SOMEV #() 
                                 | false => NONEV end)  >>>)%I.

  Parameter createNode_spec : ∀ (k: K) (c: Node),
     ⊢ ({{{ True }}}
           createNode #k #c
       {{{ (e: Node) em Ie pce, RET #e;
              node e em Ie pce
            ∗ ⌜k ∈ pce⌝
            ∗ ⌜k ∈ outset K Ie c⌝ }}})%I.

  Parameter try_constraint_insert_spec : ∀ (k: K) (p c e: Node),
     ⊢ (<<< ∀∀ mp Ip pcp, node p mp Ip pcp >>>
           try_constraint #p #c #e @ ⊤
       <<< ∃∃ (succ: bool) Ip',
              node p mp Ip' pcp
            ∗ (match succ with true => ⌜mp = false⌝ ∗ ⌜k ∈ (out_map Ip) !!! c⌝
                                     ∗ ⌜k ∈ (out_map Ip') !!! e⌝ 
                             | false => ⌜mp = true ∨ k ∉ (out_map Ip) !!! c⌝
                                      ∗ ⌜Ip' = Ip⌝ end),
              RET (match succ with true => SOMEV #() 
                                 | false => NONEV end)  >>>)%I.



End skiplist_v0.
    

          
            
      
         
      
      
          
        
    
  
  
  
  
  
  