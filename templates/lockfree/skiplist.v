(* Herlihy Skiplist *)

From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
From flows Require Export multiset_flows keyset_ra2 bool_ra.
From flows Require Export hindsight traverse_module.

Module Type SKIPLIST <: DATA_STRUCTURE.
  Declare Module TR : TRAVERSE.
  Export TR.NODE TR.
  
  (* Parameter L : nat. (* Maxlevels *) *)
  
  Parameter permute_levels : heap_lang.val.

  Definition init : heap_lang.val :=
    λ: <>,
      let: "t" := createTail #() in
      let: "h" := createHead "t" in
      let: "r" := ref ("h", "t") in
      "r".

  (* Template Algorithms *)
  Definition search : heap_lang.val :=
    λ: "h" "t" "k",
      let: "preds_succs_res" := traverse "h" "t" "k" in
      let: "res" := Snd "preds_succs_res" in
      "res".
  
  Definition maintenanceOp_delete_rec : heap_lang.val :=
    rec: "mOp" "i" "h" "perm" "curr" :=
      if: "i" < ("h" - #1) then
        let: "idx" := ! ("perm" +ₗ "i") in
        markNode "curr" "idx";;
        "mOp" ("i" + #1) "h" "perm" "curr"
      else
        #().
  
  Definition maintenanceOp_delete : heap_lang.val :=
    λ: "curr",
      let: "h" := getHeight "curr" in
      let: "perm" := permute_levels "h" in
      maintenanceOp_delete_rec #0%nat "h" "perm" "curr".
  
  Definition delete : heap_lang.val :=
    λ: "p" "h" "t" "k",
      let: "preds_succs_res" := traverse "h" "t" "k" in
      let: "preds" := Fst (Fst "preds_succs_res") in
      let: "succs" := Snd (Fst "preds_succs_res") in
      let: "res" := Snd "preds_succs_res" in
      if: ~ "res" then
        #false
      else 
        let: "curr" := ! ("succs" +ₗ #0%nat) in 
        maintenanceOp_delete "curr";;
        match: markNode' "curr" "p"  with
          NONE => #false
        | SOME "_" => traverse_rec "k" "preds" "succs" #(L-2)%nat;; #true end.

  Definition maintenanceOp_insert_rec : heap_lang.val :=
    rec: "mOp" "i" "k" "h" "perm" "preds" "succs" "new_node" :=
      if: "i" < ("h" - #1) then
        let: "idx" := ! ("perm" +ₗ "i") in
        let: "pred" := ! ("preds" +ₗ "idx") in
        let: "succ" := ! ("succs" +ₗ "idx") in
        match: changeNext "pred" "succ" "new_node" "idx" with
          NONE =>
          traverse_rec "k" "preds" "succs" #(L-2)%nat;;
          "mOp" "i" "k" "h" "perm" "preds" "succs" "new_node"
        | SOME "_" => 
          "mOp" ("i" + #1) "k" "h" "perm" "preds" "succs" "new_node" end
      else
        #().

  Definition maintenanceOp_insert : heap_lang.val :=
    λ: "k" "preds" "succs" "new_node",
      let: "h" := getHeight "new_node" in
      let: "perm" := permute_levels "h" in
      maintenanceOp_insert_rec #0%nat "k" "h" "perm" "preds" "succs" "new_node".
  
  Definition insert : heap_lang.val :=
    rec: "ins" "p" "h" "t" "k" :=
      let: "preds_succs_res" := traverse "h" "t" "k" in
      let: "preds" := Fst (Fst "preds_succs_res") in
      let: "succs" := Snd (Fst "preds_succs_res") in
      let: "res" := Snd "preds_succs_res" in
      if: "res" then
        #false
      else
        let: "new_node" := createNode "k" "succs" in
        let: "pred" := ! ("preds" +ₗ #0%nat) in
        let: "curr" := ! ("succs" +ₗ #0%nat) in
        match: changeNext' "pred" "curr" "new_node" "p" with
          NONE => "ins" "p" "h" "t" "k"
        | SOME "_" => 
          maintenanceOp_insert "k" "preds" "succs" "new_node";;
          #true end.         

  Definition dsOp : heap_lang.val :=
    λ: "OP" "p" "r",
      let: "ht" := ! "r" in
      let: "h" := Fst "ht" in
      let: "t" := Snd "ht" in
      let: "op" := Fst "OP" in
      let: "k" := Snd "OP" in     
      if: "op" = #0 
      then search "h" "t" "k"
      else if: "op" = #1 
      then insert "p" "h" "t" "k"
      else delete "p" "h" "t" "k".
      
  Inductive Opp := 
    searchOp : nat → Opp | insertOp : nat → Opp | deleteOp : nat → Opp.
  Definition Op := Opp.

  Definition Op_to_val (op: Op) : heap_lang.val :=
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
  Definition resT_from_val (v : heap_lang.val) : option resT :=
    match v with
    | LitV(LitBool b) => Some b
    | _               => None
    end.
  Definition resT_to_val (b : resT) : heap_lang.val := LitV(LitBool b).
  
  Lemma resT_inj_prop : ∀ (b : resT), resT_from_val (resT_to_val b) = Some b.
  Proof. done. Qed.
  
  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.

  Lemma resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  Proof. try done. Qed.

  Definition seq_spec (op: Op) (C: absT) (C': absT) (res: resT) : Prop :=
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
  
  Global Instance Op_inhabited : Inhabited Op := populate (searchOp 0).
  Global Instance absTUR_discrete : CmraDiscrete absTUR.
  Proof. try apply _. Qed.
  Global Instance resT_inhabited : Inhabited resT := bool_inhabated.
      
  (*
    The snapshot stores:
    0) set of nodes
    1) global interface
    2) global contents
    3) map from nodes to node-local info

    Node local info:
    1) key
    2) Marking
    3) Next pointers
    4) singleton interface
  *)

  Definition ms_flowUR := multiset_flowint_ur nat.
  Definition auth_flowUR := authR ms_flowUR.
  Definition auth_keysetUR := authUR $ (keysetUR nat).
  Definition auth_setnodeUR := authUR $ (gsetUR Node).
  Definition contentsUR := gsetUR natUR.
  Definition set_NodesUR := gsetUR Node.
  

  Definition MarkUR := gmapUR Node $ gmapUR nat $ boolUR.
  Definition NextUR := gmapUR Node $ gmapUR nat $ locUR. 
  Definition KeyUR := gmapUR Node $ natUR.
  Definition HeightUR := gmapUR Node $ natUR.
  Definition FlowUR := gmapUR Node $ ms_flowUR.
  
  Definition prod7UR A B C D E F G :=
    prodUR (prodUR (prodUR (prodUR (prodUR (prodUR A B) C) D) E) F) G.

  Definition snapshotUR := 
    prod7UR set_NodesUR contentsUR HeightUR MarkUR NextUR KeyUR FlowUR.
  Definition snapshot := ucmra_car snapshotUR.
  
  Definition abs (s: snapshot) : absT :=
    match s with (_, c, _, _, _, _, _) => c end.

  Global Instance snapshotUR_discrete : CmraDiscrete snapshotUR.
  Proof. try apply _. Qed.

  Global Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Proof. try apply _. Qed.

  Global Instance absT_leibnizequiv : LeibnizEquiv (absT).
  Proof. try apply _. Qed.
  
  Global Instance snapshot_inhabited : Inhabited snapshot.
  Proof. try apply _. Qed. 

  Class dsGG Σ := ds {
                    ds_auth_keysetG :: inG Σ auth_keysetUR;
                  }.
  
  Definition dsG := dsGG.
                
  (*
  Definition dsΣ : gFunctors :=
    #[ GFunctor auth_keysetUR ].
  
  Global Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsGG Σ.
  Proof. solve_inG. Qed.
  *)

  (* Context `{!heapGS Σ, !dsGG Σ}. *)
  (* Notation iProp := (iProp Σ). *)
  (* Parameter γ_ks: gname.  *)
  
  Definition FP (s: snapshot) : gset Node :=
    match s with (N, _, _, _, _, _, _) => N end.
  
  Definition Mark (s: snapshot) (n: Node) : MarkT :=
    match s with (_, _, _, m, _, _, _) =>
      match (m !! n) with 
      | Some mn => mn
      | None => ∅ end end.
      
  Definition Marki (s: snapshot) (n: Node) (i: nat) : bool := 
    Mark s n !!! i.

  Definition Next (s: snapshot) (n: Node) : NextT :=
    match s with (_, _, _, _, m, _, _) =>
      match (m !! n) with 
      | Some mn => mn
      | None => ∅ end end.

  Definition Nexti (s: snapshot) (n: Node) (i: nat) : option Node := 
    Next s n !! i.

  Definition Key (s: snapshot) (n: Node) : nat :=
    match s with (_, _, _, _, _, m, _) =>
      match (m !! n) with 
      | Some k => k
      | None => 0 end end.
  
  Definition Height (s: snapshot) (n: Node) : nat :=
    match s with (_, _, m, _, _, _, _) =>
      match (m !! n) with 
      | Some h => h
      | None => 0 end end.

  Definition Content (s: snapshot) (n: Node) : gset nat :=
    if Marki s n 0 then ∅ else {[ Key s n ]}.

  Definition FI (s: snapshot) (n: Node) : multiset_flowint_ur nat :=
    match s with (_, _, _, _, _, _, m) => 
      match (m !! n) with 
      | Some In => In
      | None => ∅ end end.
      
  Definition GFI (s: snapshot) : multiset_flowint_ur nat :=
    ([^op set] x ∈ FP s, FI s x). 

  Definition snapshot_constraints (s: snapshot) : Prop :=
    ∃ (N: gset Node) (C: gset nat) (H: gmap Node nat)
      (Mk: gmap Node (gmap nat bool)) (Nx: gmap Node (gmap nat Node)) 
      (Ky: gmap Node nat) (I: gmap Node (multiset_flowint_ur nat)),
      s = (N, C, H, Mk, Nx, Ky, I) ∧ dom H = N ∧ dom Mk = N ∧ dom Nx = N 
      ∧ dom Ky = N ∧ dom I = N.
  
  Definition KS := gset_seq 0 W.
        
  Definition flow_constraints_I n In (m: bool) (on: option Node) (k: nat) : Prop := 
      (dom In = {[n]})
    ∧ (insets In ≠ ∅ → 
        dom (out_map In) = match on with Some n' => {[n']} | None => ∅ end)
    ∧ (outsets In ⊆ insets In)
    ∧ (if m then keyset In = ∅ 
        else gset_seq k W ⊆ insets In ∧ gset_seq (k+1) W = outsets In)
    ∧ (insets In ≠ ∅ → W ∈ insets In)
    ∧ (∀ k, k ∈ insets In → k ≤ W)
    ∧ (∀ k, inf In n !!! k ≤ 1)
    ∧ (∀ n' k, out In n' !!! k ≤ 1).

  Definition node_inv_pure hd tl n h (mark: gmap nat bool) (next: gmap nat Node) 
    k In : Prop :=
      ((∃ i, mark !!! i = false) → mark !!! 0 = false)
    ∧ (n ≠ tl → dom next = gset_seq 0 (h-1)) 
    ∧ (dom mark = gset_seq 0 (h-1))
    ∧ (n ≠ hd → n ≠ tl → 0 < h < L)
    ∧ (0 ≤ k ≤ W)
    ∧ (flow_constraints_I n In (mark !!! 0) (next !! 0) k).
    
  Definition hd_tl_inv hd tl (fp: gset Node) ht_hd ht_tl (mhd mtl: gmap nat bool)
    (nhd ntl: gmap nat Node) k_hd k_tl : Prop :=
      {[hd; tl]} ⊆ fp
    ∧ (k_hd = 0)
    ∧ (k_tl = W)
    ∧ (∀ i, i < L → mhd !!! i = false)
    ∧ (∀ i, i < L → mtl !!! i = false)
    ∧ (nhd !! (L-1) = Some tl)
    ∧ ntl = ∅
    ∧ ht_hd = L
    ∧ ht_tl = L.

  Definition per_tick_inv hd tl s : Prop := 
      hd_tl_inv hd tl (FP s) (Height s hd) (Height s tl) (Mark s hd) (Mark s tl)
        (Next s hd) (Next s tl) (Key s hd) (Key s tl)
    ∧ (✓ (GFI s) ∧ (∀ n, n ≠ hd → inf (GFI s) n = 0%CCM))
    ∧ (∀ n k, n ∈ FP s → k ∈ keyset (FI s n) → (k ∈ abs s ↔ k ∈ Content s n))
    ∧ (∀ n, n ∈ (FP s) → 
        node_inv_pure hd tl n (Height s n) (Mark s n) (Next s n) (Key s n) (FI s n))
    ∧ (∀ n1 n2, Nexti s n1 0 = Some n2 → Key s n1 < Key s n2)
    ∧ (∀ n1 n2 i, Nexti s n1 i = Some n2 → n2 ∈ FP s)
    ∧ (∀ n1 n2 i, Nexti s n1 i = Some n2 → i < Height s n2).
  
  Definition transition_inv s s' : Prop :=
      (∀ n i, n ∈ FP s → Marki s' n i = true → Nexti s' n i = Nexti s n i)
    ∧ (∀ n, Marki s n 0 = false → Marki s' n 0 = true → Key s n ∉ abs s')
    ∧ (∀ n i, n ∈ FP s → Marki s n i = true → Marki s' n i = true)
    ∧ (∀ n, n ∈ FP s → Height s' n = Height s n)
    ∧ (∀ n, n ∈ FP s → Key s' n = Key s n)
    ∧ (FP s ⊆ FP s').
  
  Definition resources (Σ: gFunctors) (Hg1: heapGS Σ) (Hg2: dsGG Σ) γ_ks s : iProp Σ :=
      own γ_ks (● prodKS (KS, abs s))
    ∗ ([∗ set] n ∈ FP s, node Σ Hg1 n (Height s n) (Mark s n) (Next s n) (Key s n))
    ∗ ([∗ set] n ∈ FP s, own γ_ks (◯ prodKS (keyset (FI s n), Content s n))).

  Definition ds_inv Σ (Hg1 : heapGS Σ) (Hg2 : dsGG Σ) r (M: gmap nat snapshot) 
    (T: nat) (s: snapshot) : iProp Σ := 
    ∃ (hd tl: Node) (γ_ks : gname), 
      r ↦□ (#hd, #tl)
    ∗ ⌜snapshot_constraints s⌝ 
    ∗ resources Σ _ _ γ_ks s
    ∗ ⌜∀ t, 0 ≤ t ≤ T → per_tick_inv hd tl (M !!! t)⌝
    ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝.

  Global Instance ds_inv_timeless Σ (Hg1 : heapGS Σ) (Hg2 : dsGG Σ) r M T s : 
    Timeless (ds_inv Σ _ _ r M T s).
  Proof.
    try apply _.
  Qed.
  
  Definition local_pre (op : Op) :=
    match op with
    | searchOp k => 1 < L ∧ 0 < k < W 
    | insertOp k => 1 < L ∧ 0 < k < W  
    | deleteOp k => 1 < L ∧ 0 < k < W end.
  
  Parameter permute_levels_spec : ∀ Σ (Hg1: heapGS Σ) (L: nat),
      {{{ True }}}
          permute_levels #L
      {{{ (perm: loc) (vs: list heap_lang.val) (xs: list nat), RET #perm;
            perm ↦∗ vs
          ∗ ⌜vs = (fun n => # (LitInt (Z.of_nat n))) <$> xs⌝
          ∗ ⌜xs ≡ₚ seq 1 (L-1)⌝ }}}.
    
End SKIPLIST.