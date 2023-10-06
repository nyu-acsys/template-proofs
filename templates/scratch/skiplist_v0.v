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
Require Export hindsight.

Module SKIPLIST0 <: DATA_STRUCTURE.

  Parameter inContents : val.
  Parameter findNext : val.
  Parameter try_constraint : val.
  Parameter maintenance : val.
  Parameter createNode: val.

  (** Template algorithms *)

  Definition traverse_rec : val :=
    λ: "r",
    rec: "tr" "p" "c" "k" :=
      let: "fn_ck" := findNext "c" "k" in
      if: Fst "fn_ck" then
        match: Snd "fn_ck" with
          NONE => ""
        | SOME "s" =>
            match: try_constraint "p" "c" "s" with
              NONE =>
                let: "fn_hk" := findNext "r" "k" in
                match: Snd "fn_hk" with
                  NONE => ""
                | SOME "n" => 
                    "tr" "r" "n" "k" end
            | SOME "_" => "tr" "p" "s" "k" end end  
      else
        match: Snd "fn_ck" with
          NONE => ("p", "c")
        | SOME "s" => "tr" "c" "s" "k" end.

  Definition traverse : val := 
    λ: "r" "k", 
      let: "fn_hk" := findNext "r" "k" in
      match: Snd "fn_hk" with
        NONE => ""
      | SOME "n" => 
          traverse_rec "r" "r" "n" "k" end.

  Definition search : val :=
    λ: "r" "k",
      let: "pc" := traverse "r" "k" in
      let: "c" := Snd "pc" in
      inContents "c" "k".
      
  Definition delete : val :=
    λ: "r" "k",
      let: "pc" := traverse "r" "k" in
      let: "c" := Snd "pc" in
      if: ~ (inContents "c" "k") then
        #false
      else
        match: try_constraint "c" with
          NONE => #false
        | SOME "_" => maintenance "k";; #true end.
        
  Definition insert : val :=
    λ: "r",
    rec: "ins" "k" :=
      let: "pc" := traverse "r" "k" in
      let: "p" := Fst "pc" in
      let: "c" := Snd "pc" in
      if: inContents "c" "k" then
        #false
      else
        let: "e" := createNode "k" "c" in
        match: try_constraint "p" "c" "e" with
          NONE => "ins" "k"
        | SOME "_" => #true end.

  Definition dsOp : val :=
    λ: "OP" "r",
      let: "op" := Fst "OP" in
      let: "k" := Snd "OP" in     
      if: "op" = #0 
      then search "r" "k"
      else if: "op" = #1 
      then insert "r" "k"
      else delete "r" "k".

  (* Definition K := Z. *)
  Inductive Opp := searchOp : nat → Opp | insertOp : nat → Opp | deleteOp : nat → Opp.
  Definition Op := Opp.

  Definition Op_to_val (op: Op) : val :=
    match op with
    | searchOp k => (#0, #k)
    | insertOp k => (#1, #k)
    | deleteOp k => (#2, #k) 
    end.
    
  Definition absTUR := gsetUR nat.
  Definition absT := ucmra_car absTUR.

  Definition resT := bool.
  Definition resT_to_base_lit (b: resT) : base_lit := LitBool b.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Definition resT_from_val (v : val) : option bool :=
    match v with
    | LitV(LitBool b) => Some b
    | _               => None
    end.
  Definition resT_to_val (b : bool) : val := LitV(LitBool b).
  
  Lemma resT_inj_prop : ∀ (b : bool), bool_from_val (bool_to_val b) = Some b.
  Proof. done. Qed.

  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.

  Lemma resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  Proof. try done. Qed.

  Definition seq_spec (op: Op) (C: absT) (C': absT) (res: bool) : Prop :=
    match op with
    | searchOp k => C' = C ∧ (if res then k ∈ C else k ∉ C)
    | insertOp k => C' = C ∪ {[k]} ∧ (if res then k ∉ C else k ∈ C)
    | deleteOp k => C' = C ∖ {[k]} ∧ (if res then k ∈ C else k ∉ C)
    end.

  Global Instance seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Proof.
    intros op c c' res. unfold seq_spec. 
    destruct op; try apply and_dec; try destruct res; try apply _.
  Qed.

  Definition updater_thread (op: Op) (res: resT) : bool := 
    match op, res with
    | searchOp _, _ => false
    | _, false => false
    | _, _ => true
    end.

  Global Instance updater_thread_dec: ∀ op res b, 
    Decision (updater_thread op res = b).
  Proof.
    intros op res b. unfold updater_thread.
    destruct op; destruct res; try apply _.
  Qed.  

  Global Instance Op_inhabited : Inhabited Op := populate (searchOp 0).
  Global Instance absTUR_discrete : CmraDiscrete absTUR.
  Proof. try apply _. Qed.
  Global Instance resT_inhabited : Inhabited resT.
  Proof. try apply _. Qed.

  
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

  Definition flowUR := multiset_flowint_ur nat.
  Definition auth_flowUR := authR flowUR.
  Definition auth_keysetUR := authUR $ (keysetUR nat).
  Definition auth_setnodeUR := authUR $ (gsetUR Node).

  Definition prod3R A B C :=
    prodR (prodR A B) C.

  Definition prod7UR A B C D E F G:=
    prodUR (prodUR (prodUR (prodUR (prodUR (prodUR A B) C) D) E) F) G.
  
  Definition esT : Type := gmap Node (gset nat).
  Definition esTUR := gmapUR Node $ gsetUR nat.
  
  Definition MarkUR := gmapUR Node $ natUR.
  Definition ESUR := gmapUR Node $ esTUR.
  Definition PCUR := gmapUR Node $ gsetUR nat.
  Definition FIUR := gmapUR Node $ multiset_flowint_ur nat.

  Definition snapshotUR :=
    prod7UR
      (gsetUR Node)
      (flowUR)
      (gsetUR nat)
      (MarkUR)
      (ESUR)
      (PCUR)
      (FIUR).
      
  Definition snapshot := ucmra_car snapshotUR.
  
  Definition abs (s: snapshot) : absT :=
    match s with
    | (_,_, C, _,_,_,_) => C end.

  Global Instance snapshotUR_discrete : CmraDiscrete snapshotUR.
  Proof. try apply _. Qed.

  Global Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Proof. try apply _. Qed.
  
  Global Instance snapshot_inhabited : Inhabited snapshot.
  Proof. try apply _. Qed.
  
  (*
  Global Instance NodeLocalUR_inhabited : Inhabited (nat * esT * gset nat) := 
    populate (0, ∅, ∅).  
  *)
  Class dsGG Σ := ds {
                    ds_flowG :> inG Σ auth_flowUR;
                    ds_auth_keysetG :> inG Σ auth_keysetUR;
                    ds_auth_setnodeG :> inG Σ auth_setnodeUR;
                   }.
  
  Definition dsG := dsGG.
                
                     
  Definition dsΣ : gFunctors :=
    #[ GFunctor auth_flowUR;  GFunctor auth_keysetUR;
       GFunctor auth_setnodeUR ].
  
  Global Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsGG Σ.
  Proof. solve_inG. Qed.

    Context `{!heapGS Σ, !dsGG Σ}. 
    Context (γ_I γ_fp γ_ks: gname) (r: Node).
    Notation iProp := (iProp Σ).
  
    Parameter node : Node → bool → esT → (gset nat) → iProp.
    Parameter node_timeless_proof : ∀ r n es V, Timeless (node r n es V).
    Global Instance node_timeless r n es V: Timeless (node r n es V).
    Proof. apply node_timeless_proof. Qed.  

    (*
    Parameter Mark : snapshot → Node → bool.
    Parameter ES : snapshot → Node → esT.
    Parameter PC : snapshot → Node → gset nat.
    Parameter GFI : snapshot → (multiset_flowint_ur nat).
    Parameter FI : snapshot → Node → (multiset_flowint_ur nat).
    Parameter FP : snapshot → gset Node.

    Definition node_local (s: snapshot) (n: Node) 
      : (nat * esT * gset nat * multiset_flowint_ur nat) :=
      match s with
      | (_,_,_,m) => default (0, ∅, ∅, ∅) (m !! n) end.
    *)
    
    Definition Mark (s: snapshot) (n: Node) : bool :=
      match s with
      | (_,_,_,m,_,_,_) => 
        match (m !! n) with
        | Some (S _) => true
        | _ => false end end.

    Definition ES (s: snapshot) (n: Node) : esT :=
      match s with
      | (_,_,_,_,m,_,_) => default ∅ (m !! n) end.

    Definition PC (s: snapshot) (n: Node) : gset nat :=
      match s with
      | (_,_,_,_,_,m,_) => default ∅ (m !! n) end.
    
    Definition FI (s: snapshot) (n: Node) : multiset_flowint_ur nat :=
      match s with
      | (_,_,_,_,_,_,m) => default ∅ (m !! n) end.
    
    Definition GFI (s: snapshot) : multiset_flowint_ur nat :=
      match s with
      | (_,x,_,_,_,_,_) => x end.
      
    Definition FP (s: snapshot) : gset Node :=
      match s with
      | (x,_,_,_,_,_,_) => x end.
          
    Definition Cont (s: snapshot) (n: Node) : gset nat :=
      if decide (Mark s n) then ∅ else PC s n.
    
    Parameter out_set : multiset_flowint_ur nat → gset nat.
    (* out_es es := ⋃_n es !!! n *)
    Parameter out_es : esT → gset nat.
    (*
    Parameter keyset : multiset_flowint_ur nat → gset nat. 
    *)
    
    (** data structure specific inv *)

  Definition globalRes γ_fp γ_I γ_ks s : iProp :=
      own γ_I (● (GFI s))
    ∗ own γ_fp (● (FP s)) 
    ∗ own γ_ks (● prod (KS, abs s)).
      
  Definition outflow_constraint (In: multiset_flowint_ur nat) (esn: esT) : Prop := 
    True.

  Definition node_inv_pure s n : Prop :=
      (¬ (Mark s n) → out_set (FI s n) ⊆ inset nat (FI s n) n)
    ∧ (Cont s n ⊆ keyset (FI s n))
    ∧ (Mark s n → out_set (FI s n) ≠ ∅)
    ∧ (outflow_constraint (FI s n) (ES s n)).

  Definition node_inv γ_I γ_ks s n : iProp :=
      node n (Mark s n) (ES s n) (PC s n)
    ∗ own γ_I (◯ (FI s n))
    ∗ own γ_ks (◯ prod (keyset (FI s n), Cont s n))
    ∗ ⌜node_inv_pure s n⌝.   
(*
  Definition node_local_inv s n : iProp :=
      own (γ_I s) (◯ intf s n) 
    ∗ own (γ_ks s) (◯ prod (keyset (intf s n), Cont s n))
    ∗ node_local_pure s n.
*)
  Definition per_tick_inv r s : Prop := 
      inset nat (FI s r) r = KS 
    ∧ out_es (ES s r) = KS
    ∧ ¬ Mark s r
    ∧ (∀ n, n ∈ (FP s) → node_inv_pure s n).
    
  Definition transition_inv s s' : Prop :=
      (∀ n, n ∈ FP s → Mark s n → ES s' n = ES s n)
    ∧ (∀ n, n ∈ FP s → Mark s n → Mark s' n)
    ∧ (∀ n, n ∈ FP s → ¬ Mark s n → Mark s' n → ES s n ≠ ES s' n)
    ∧ (∀ n, n ∈ FP s → PC s n = PC s' n)
    ∧ (FP s ⊆ FP s').

  Definition ds_inv (M: gmap nat snapshot) 
    (T: nat) (s: snapshot) : iProp :=
      globalRes γ_I γ_fp γ_ks s
    ∗ ([∗ set] n ∈ FP s, node_inv γ_I γ_ks s n)
    ∗ ⌜∀ t, t ∈ dom M → per_tick_inv r (M !!! t)⌝
    ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝.
    
  Global Instance ds_inv_timeless M T s : 
    Timeless (ds_inv M T s).
  Proof.
    try apply _.
  Qed.

    (** Helper functions specs *)
    
  Parameter inContents_spec : ∀ (k: nat) (n: Node),
     ⊢ (<<< ∀∀ m es pc, node n m es pc >>>
           inContents #n #k @ ⊤
       <<< ∃∃ (v: bool),
              node n m es pc ∗ ⌜v ↔ k ∈ pc⌝,
              RET #v >>>)%I.

  Parameter findNext_spec : ∀ (k: nat) (n: Node),
     ⊢ (<<< ∀∀ m es pc, node n m es pc >>>
           findNext #n #k @ ⊤
       <<< ∃∃ (success: bool) (n': Node),
              node n m es pc
            ∗ (match success with true => ⌜k ∈ es !!! n'⌝ 
                                | false => ⌜k ∉ out_es es⌝ end),
              RET (match success with true => (#m, SOMEV #n') 
                                    | false => (#m, NONEV) end)  >>>)%I.
                                 
  Definition edgset_update es k curr succ : esT :=
   <[ succ := (es !!! succ) ∪ {[k]} ]>
    (<[ curr := (es !!! curr) ∖ {[k]} ]> es).

  Parameter try_constraint_trav_spec : ∀ (k: nat) (pred curr succ: Node),
     ⊢ (<<< ∀∀ m es pc, node pred m es pc >>>
           try_constraint #pred #curr #succ @ ⊤
       <<< ∃∃ (success: bool) es',
              node pred m es' pc
            ∗ (match success with true => ⌜m = false⌝ ∗ ⌜k ∈ es !!! curr⌝
                                          ∗ ⌜es' = edgset_update es k curr succ⌝ 
                                | false => ⌜m = true ∨ k ∉ es !!! curr⌝
                                           ∗ ⌜es' = es⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.

  Parameter createNode_spec : ∀ (k: nat) (n: Node),
     ⊢ ({{{ True }}}
           createNode #k #n
       {{{ e esn, RET #e;
              node e false {[n := esn]} {[k]}
            ∗ ⌜k ∈ esn⌝ }}})%I.

  Parameter try_constraint_insert_spec : ∀ (k: nat) (pred curr entry: Node),
     ⊢ (<<< ∀∀ m es pc, node pred m es pc >>>
           try_constraint #pred #curr #entry @ ⊤
       <<< ∃∃ (success: bool) es',
              node pred m es' pc
            ∗ (match success with true => ⌜m = false⌝ ∗ ⌜k ∈ es !!! curr⌝
                                          ∗ ⌜es' = edgset_update es k curr entry⌝ 
                                | false => ⌜m = true ∨ k ∉ es !!! curr⌝
                                           ∗ ⌜es' = es⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.

  Parameter try_constraint_delete_spec : ∀ (k: nat) (curr: Node),
     ⊢ (<<< ∀∀ m es pc, node curr m es pc >>>
           try_constraint #curr @ ⊤
       <<< ∃∃ (success: bool) m',
              node curr m' es pc
            ∗ (match success with true => ⌜m = false⌝ ∗ ⌜m' = true⌝ 
                                | false => ⌜m' = m⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.


  Definition dsG0 : dsG Σ.
    try done.
    Admitted.
    
End SKIPLIST0.