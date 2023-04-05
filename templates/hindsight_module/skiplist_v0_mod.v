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
(* From diaframe.heap_lang Require Import proof_automation atomic_specs wp_auto_lob. *)
Require Export search_structures_mod.

Module SKIPLIST0 <: DATA_STRUCTURE SEARCH_STRUCTURE.
  Import SEARCH_STRUCTURE.
  
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

  
  Definition snapshotUR := natUR.
  Definition snapshot := ucmra_car snapshotUR.
  
  Definition abs (s: snapshot) : absT := ∅.

  Global Instance snapshotUR_discrete : CmraDiscrete snapshotUR.
  Proof. try apply _. Qed.

  Global Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Proof. try apply _. Qed.
  
  Global Instance snapshot_inhabited : Inhabited snapshot := populate 0.
  
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
  
  Definition esT : Type := gmap Node (gset nat).

  Definition flowUR := authR (multiset_flowint_ur nat).
  Definition auth_keysetUR := authUR $ (keysetUR nat).
  Definition auth_setnodeUR := authUR $ (gsetUR Node).

  Class dsGG Σ := ds {
                    ds_flowG :> inG Σ flowUR;
                    ds_auth_keysetG :> inG Σ auth_keysetUR;
                    ds_auth_setnodeG :> inG Σ auth_setnodeUR;
                   }.
  
  Definition dsG := dsGG.
                
                     
  Definition dsΣ : gFunctors :=
    #[ GFunctor flowUR;  GFunctor auth_keysetUR;
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

    Parameter Mark : snapshot → Node → bool.
    Parameter ES : snapshot → Node → esT.
    Parameter PC : snapshot → Node → gset nat.
    Parameter GFI : snapshot → (multiset_flowint_ur nat).
    Parameter FI : snapshot → Node → (multiset_flowint_ur nat).
    Parameter FP : snapshot → gset Node.
  
    Definition Cont (s: snapshot) (n: Node) : gset nat :=
      if decide (Mark s n) then ∅ else PC s n.

    Parameter out_set : multiset_flowint_ur nat → gset nat.
    (* out_es es := ⋃_n es !!! n *)
    Parameter out_es : esT → gset nat.
    Parameter keyset : multiset_flowint_ur nat → gset nat. 
    
    (** data structure specific inv *)

    Definition globalRes γ_I γ_fp γ_ks s : iProp :=
        own γ_I (● (GFI s)) 
      ∗ own γ_fp (● FP s) 
      ∗ own γ_ks (● prod (KS, abs s)).
    
    Definition outflow_constraint (In: multiset_flowint_ur nat) (esn: esT) : Prop := True.
  
    Definition node_inv_pure s n : iProp :=
        ⌜¬ (Mark s n) → out_set (FI s n) ⊆ inset nat (FI s n) n⌝
      ∗ ⌜Cont s n ⊆ keyset (FI s n)⌝
      ∗ ⌜Mark s n → out_set (FI s n) ≠ ∅⌝
      ∗ ⌜outflow_constraint (FI s n) (ES s n)⌝ .

    Definition node_inv γ_I γ_ks s n : iProp :=
        node n (Mark s n) (ES s n) (PC s n)
      ∗ own γ_I (◯ (FI s n))
      ∗ own γ_ks (◯ prod (keyset (FI s n), Cont s n))
      ∗ node_inv_pure s n.   

    Definition per_tick_inv r s : iProp := 
        ⌜inset nat (FI s r) r = KS⌝ ∗ ⌜out_set (FI s r) = KS⌝
      ∗ ⌜¬ Mark s r⌝
      ∗ [∗ set] n ∈ (FP s), node_inv_pure s n.
    
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
      ∗ ([∗ set] t ∈ dom M, per_tick_inv r (M !!! t))
      ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝
      ∗ ⌜transition_inv (M !!! T) s⌝.
    
    Global Instance ds_inv_timeless M T s : 
      Timeless (ds_inv M T s).
    Proof.
    Admitted.  

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
         {{{ e m es pc, RET #e;
                node e m es pc
              ∗ ⌜k ∈ pc⌝
              ∗ ⌜k ∈ es !!! n⌝ }}})%I.
  
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
    
    Definition dsG0 : dsG Σ.
    try done.
    Admitted.
    
End SKIPLIST0.
