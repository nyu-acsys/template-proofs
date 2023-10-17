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
From flows Require Export multiset_flows keyset_ra2 hindsight bool_ra.

Module SKIPLIST1 <: DATA_STRUCTURE.

  Parameter inContents : val.
  Parameter findNext : val.
  Parameter changeNext : val.
  Parameter markNode : val.
  Parameter compareKey : val.
  Parameter createNode : val.
  Parameter getHeight : val.
  Parameter permute_levels : val.
  
  Parameter L : nat. (* Maxlevels *)
  Parameter W : nat. (* Keyspace *)

  (* Template Algorithms *)

  Definition traverse_i : val :=
    rec: "tri" "i" "pred" "curr" "k" :=
      let: "fn_curr" := findNext "curr" "i" in
      if: Fst "fn_curr" then
        match: Snd "fn_curr" with
          NONE => ""
        | SOME "succ" =>
            match: changeNext "pred" "curr" "succ" "i" with
              NONE => NONE
            | SOME "_" => 
              "tri" "i" "pred" "succ" "k" end end  
      else
        match: Snd "fn_curr" with
          NONE => SOME ("pred", "curr", #false)
        | SOME "succ" => 
          let: "res" := compareKey "curr" "k" in
          if: "res" = #0 then 
            "tri" "i" "curr" "succ" "k"
          else if: "res" = #1 then
            SOME ("pred", "curr", #true)
          else
            SOME ("pred", "curr", #false) end.

  Definition traverse_pop : val :=
    λ: "trec" "k" "preds" "succs" "i",
      let: "pred" := ! ("preds" +ₗ ("i" + #1)) in
      let: "fn_pred" := findNext "pred" "i" in
      match: Snd "fn_pred" with
        NONE => ""
      | SOME "curr" =>
        let: "ores" := traverse_i "i" "pred" "curr" "k" in
        match: "ores" with
          NONE => NONE
        | SOME "pred_succ_res" =>
          let: "pred" := Fst (Fst "pred_succ_res") in
          let: "succ" := Snd (Fst "pred_succ_res") in
          let: "res" := Snd "pred_succ_res" in
          "preds" +ₗ "i" <- "pred";;
          "succs" +ₗ "i" <- "succ";;
          SOME ("preds", "succs", "res") end end.

  Definition traverse_rec : val :=
    rec: "trec" "k" "preds" "succs" "i" :=
      let: "ores" := traverse_pop "trec" "k" "preds" "succs" "i" in
      match: "ores" with 
        NONE => "trec" "k" "preds" "succs" #(L-2)%nat
      | SOME "res" => 
        if: "i" = #0 then
          "res"
        else
          "trec" "k" "preds" "succs" ("i" - #1) end.
  
  Definition traverse : val :=
    λ: "h" "t" "k",
      let: "preds" := AllocN #L "h" in
      let: "succs" := AllocN #L "t" in
      traverse_rec "k" "preds" "succs" #(L-2)%nat.     

  Definition search : val :=
    λ: "h" "t" "k",
      let: "preds_succs_res" := traverse "h" "t" "k" in
      let: "res" := Snd "preds_succs_res" in
      "res".
  
  Definition maintenanceOp_delete_rec : val :=
    rec: "mOp" "i" "h" "perm" "curr" :=
      if: "i" < ("h" - #1) then
        let: "idx" := ! ("perm" +ₗ "i") in
        markNode "curr" "idx";;
        "mOp" ("i" + #1) "h" "perm" "curr"
      else
        #().
  
  Definition maintenanceOp_delete : val :=
    λ: "curr",
      let: "h" := getHeight "curr" in
      let: "perm" := permute_levels "h" in
      maintenanceOp_delete_rec #0%nat "h" "perm" "curr".
  
  Definition delete : val :=
    λ: "h" "t" "k",
      let: "preds_succs_res" := traverse "h" "t" "k" in
      let: "preds" := Fst (Fst "preds_succs_res") in
      let: "succs" := Snd (Fst "preds_succs_res") in
      let: "res" := Snd "preds_succs_res" in
      if: ~ "res" then
        #false
      else 
        let: "curr" := ! ("succs" +ₗ #0%nat) in 
        maintenanceOp_delete "curr";;
        match: markNode "curr" #0%nat  with
          NONE => #false
        | SOME "_" => traverse_rec "k" "preds" "succs" #(L-2)%nat;; #true end.

  Definition maintenanceOp_insert_rec : val :=
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

  Definition maintenanceOp_insert : val :=
    λ: "k" "preds" "succs" "new_node",
      let: "h" := getHeight "new_node" in
      let: "perm" := permute_levels "h" in
      maintenanceOp_insert_rec #0%nat "k" "h" "perm" "preds" "succs" "new_node".
  
  Definition insert : val :=
    rec: "ins" "h" "t" "k" :=
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
        match: changeNext "pred" "curr" "new_node" #0%nat with
          NONE => "ins" "h" "t" "k"
        | SOME "_" => 
          maintenanceOp_insert "k" "preds" "succs" "new_node";;
          #true end.
         

  Definition dsOp : val :=
    λ: "OP" "r",
      let: "op" := Fst "OP" in
      let: "k" := Snd "OP" in     
      if: "op" = #0 
      then search "r" "k"
      else if: "op" = #1 
      then insert "r" "k"
      else delete "r" "k".

      
  Inductive Opp := 
    searchOp : nat → Opp | insertOp : nat → Opp | deleteOp : nat → Opp.
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
  Definition resT_from_val (v : val) : option resT :=
    match v with
    | LitV(LitBool b) => Some b
    | _               => None
    end.
  Definition resT_to_val (b : resT) : val := LitV(LitBool b).
  
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
  
  Definition MarkT := gmap nat bool.
  Definition NextT := gmap nat Node.

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
                    ds_auth_keysetG :> inG Σ auth_keysetUR;
                  }.
  
  Definition dsG := dsGG.
                
                     
  Definition dsΣ : gFunctors :=
    #[ GFunctor auth_keysetUR ].
  
  Global Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsGG Σ.
  Proof. solve_inG. Qed.
  
  Context `{!heapGS Σ, !dsGG Σ}.
  Parameter γ_ks: gname. 
  Parameter (hd tl: Node).
  Notation iProp := (iProp Σ).

  Parameter node : Node → nat → MarkT → NextT → nat → iProp.
  Parameter node_timeless_proof : ∀ n h mark next k, 
    Timeless (node n h mark next k).
  Global Instance node_timeless n h mark next k: Timeless (node n h mark next k).
  Proof. apply node_timeless_proof. Qed.
  Parameter node_sep_star: ∀ n h mark next k h' mark' next' k',
    node n h mark next k -∗ node n h' mark' next' k' -∗ False.
  
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
  
  Definition gset_seq i j : gset nat :=
    list_to_set (seq i (j + 1 - i)).

  Lemma elem_of_gset_seq i j k :
    k ∈ gset_seq i j ↔ i ≤ k ≤ j.
  Proof.
    intros; rewrite elem_of_list_to_set elem_of_seq; lia.
  Qed.

  Definition snapshot_constraints (s: snapshot) : Prop :=
    ∃ (N: gset Node) (C: gset nat) (H: gmap Node nat)
      (Mk: gmap Node (gmap nat bool)) (Nx: gmap Node (gmap nat Node)) 
      (Ky: gmap Node nat) (I: gmap Node (multiset_flowint_ur nat)),
      s = (N, C, H, Mk, Nx, Ky, I) ∧ dom H = N ∧ dom Mk = N ∧ dom Nx = N 
      ∧ dom Ky = N ∧ dom I = N.
        
  Definition flow_constraints_I n In (m: bool) (on: option Node) (k: nat) : Prop := 
      (dom In = {[n]})
    ∧ (insets In ≠ ∅ → 
        dom (out_map In) = match on with Some n' => {[n']} | None => ∅ end)
    ∧ (outsets In ⊆ insets In)
    ∧ (if m then keyset In = ∅ 
        else gset_seq k W ⊆ insets In ∧ gset_seq (k+1) W = outsets In)
    ∧ (∀ k, k ∈ insets In → k ≤ W)
    ∧ (∀ k, inf In n !!! k ≤ 1)
    ∧ (∀ n' k, out In n' !!! k ≤ 1).

  Definition node_inv_pure n h (mark: gmap nat bool) (next: gmap nat Node) 
    k In : Prop :=
      ((∃ i, mark !!! i = false) → mark !!! 0 = false)
    ∧ (∀ i, next !! i = None ↔ n = tl)
    ∧ (dom next = gset_seq 0 (h-1)) 
    ∧ (dom mark = gset_seq 0 (h-1))
    ∧ (0 < h ≤ L)
    ∧ (0 ≤ k ≤ W)
    ∧ (flow_constraints_I n In (mark !!! 0) (next !! 0) k).
    
  Definition hd_tl_inv (fp: gset Node) k_hd k_tl (mhd mtl: gmap nat bool)
    (nhd: gmap nat Node) ht_hd ht_tl : Prop :=
      {[hd; tl]} ⊆ fp
    ∧ (k_hd = 0)
    ∧ (k_tl = W)
    ∧ (∀ i, mhd !!! i = false)
    ∧ (∀ i, mtl !!! i = false)
    ∧ (nhd !! (L-1) = Some tl)
    ∧ ht_hd = L
    ∧ ht_tl = L.

  Definition per_tick_inv s : Prop := 
      hd_tl_inv (FP s) (Key s hd) (Key s tl) (Mark s hd) (Mark s tl)
        (Next s hd) (Height s hd) (Height s tl)
    ∧ ✓ GFI s
    ∧ (∀ n, n ∈ (FP s) → 
        node_inv_pure n (Height s n) (Mark s n) (Next s n) (Key s n) (FI s n))
    ∧ (∀ n1 n2 i, Nexti s n1 i = Some n2 → Key s n1 < Key s n2)
    ∧ (∀ n1 n2 i, Nexti s n1 i = Some n2 → n2 ∈ FP s)
    ∧ (∀ n1 n2 i, Nexti s n1 i = Some n2 → i < Height s n2).
  
  Definition transition_inv s s' : Prop :=
      (∀ n i, n ∈ FP s → Marki s' n i = true → Nexti s' n i = Nexti s n i)
    ∧ (∀ n, Marki s n 0 = false → Marki s' n 0 = true → Key s n ∉ abs s')
    ∧ (∀ n i, n ∈ FP s → Marki s n i = true → Marki s' n i = true)
    ∧ (∀ n, n ∈ FP s → Height s' n = Height s n)
    ∧ (∀ n, n ∈ FP s → Key s' n = Key s n)
    ∧ (FP s ⊆ FP s').

  Definition resources γ_ks s : iProp :=
      own γ_ks (● prodKS (KS, abs s))
    ∗ ([∗ set] n ∈ FP s, node n (Height s n) (Mark s n) (Next s n) (Key s n))
    ∗ ([∗ set] n ∈ FP s, own γ_ks (◯ prodKS (keyset (FI s n), Content s n))).

  Definition ds_inv (M: gmap nat snapshot) 
    (T: nat) (s: snapshot) : iProp :=
      ⌜snapshot_constraints s⌝
    ∗ resources γ_ks s
    ∗ ⌜∀ t, t ∈ dom M → per_tick_inv (M !!! t)⌝
    ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝.
    
  Global Instance ds_inv_timeless M T s : 
    Timeless (ds_inv M T s).
  Proof.
    try apply _.
  Qed.

    (** Helper functions specs *)
        
  Definition is_array (array : loc) (xs : list Node) : iProp :=
    let vs := (fun n => # (LitLoc n)) <$> xs
    in array ↦∗ vs.
  (*
  Lemma array_store E (i : nat) (v : Node) arr (xs : list Node) :
    {{{ ⌜i < length xs⌝ ∗ ▷ is_array arr xs }}}
      #(arr +ₗ i) <- #v @ E 
    {{{ RET #(); is_array arr (<[i:=v]>xs) }}}.
  Proof.
    iIntros (ϕ) "[% isArr] Post".
    unfold is_array.
    iApply (wp_store_offset with "isArr").
    { apply lookup_lt_is_Some_2. by rewrite fmap_length. }
    rewrite (list_fmap_insert ((λ b : nat, #b) : nat → val) xs i v).
    iAssumption.
  Qed.

  Lemma array_repeat (b : nat) (n : nat) :
    {{{ ⌜0 < n⌝ }}} AllocN #n #b 
    {{{ arr, RET #arr; is_array arr (replicate n b) }}}.
  Proof.
    iIntros (ϕ ?%inj_lt) "Post".
    iApply wp_allocN; try done.
    iNext. iIntros (l) "[lPts _]".
    iApply "Post".
    unfold is_array.
    rewrite Nat2Z.id.
    rewrite -> fmap_replicate.
    iAssumption.
  Qed.

  Parameter findNext_spec : ∀ (n: Node) (i: nat),
     ⊢ (<<< ∀∀ mark next k, node n mark next k >>>
           findNext #n #i @ ⊤
       <<< ∃∃ (m: bool) (opt_n': option Node),
              node n mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !! i = opt_n'⌝,
              RET (match opt_n' with None => (#m, NONEV) 
                                    | Some n' => (#m, SOMEV #n') end) >>>)%I.

  Parameter try_constraint_traverse_spec : ∀ (i: nat) (p c s: Node),
     ⊢ (<<< ∀∀ mark next k, node p mark next k >>>
           try_constraint #i #p #c #s @ ⊤
       <<< ∃∃ (success: bool) (next': NextT),
              node p mark next' k
            ∗ (match success with true => ⌜mark !!! i = false 
                                            ∧ next !!! i = c 
                                            ∧ next' = <[i := s]> next⌝
                                | false => ⌜mark !!! i = true 
                                            ∧ next' = next⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.

  Parameter compareKey_spec : ∀ (n: Node) (k': nat),
     ⊢ (<<< ∀∀ mark next k, node n mark next k >>>
           compareKey #n #k' @ ⊤
       <<< ∃∃ (res: nat),
              node n mark next k ∗ 
              ⌜if decide (res = 0) then k < k'
               else if decide (res = 1) then k = k'
               else k > k'⌝,
              RET #res >>>)%I.

  Parameter try_constraint_delete_spec : ∀ (curr: Node) (i: nat),
     ⊢ (<<< ∀∀ mark next k, node curr mark next k >>>
           try_constraint #curr #i @ ⊤
       <<< ∃∃ (success: bool) mark',
              node curr mark' next k
            ∗ (match success with true => ⌜mark !!! i = false
                                            ∧ mark' = <[i := true]> mark⌝
                                | false => ⌜mark !!! i = true
                                            ∧ mark' = mark⌝ end),
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  >>>)%I.
  *)

  Definition dsG0 : dsG Σ.
    unfold dsG.
    try apply _.
  Qed.
    
    
End SKIPLIST1.
  
