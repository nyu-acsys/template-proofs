(* Multicopy LSM DAG Template *)

From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export notation locations lang.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
From flows Require Export multiset_flows keyset_ra misc_ra.
From flows Require Export hindsight lsm_node_module.

(* Instantiating multicopy template as DATA_STRUCTURE for the Hindsight Framework *)
Module Type LSM_TREE <: DATA_STRUCTURE.
  Declare Module NODE : LSM_NODE_IMPL.
  Export NODE.

  (** Template algorithms *)

  Parameter init : heap_lang.val.

  Definition traverse : heap_lang.val :=
    rec: "t_rec" "n" "k" :=
      lockNode "n" ;;
      match: (inContents "n" "k") with
        SOME "v" => unlockNode "n";; "v"
      | NONE => match: (findNext "n" "k") with
                  SOME "n'" => unlockNode "n" ;; "t_rec" "n'" "k"
                | NONE => unlockNode "n" ;; #bot end end.
                
  Definition search : heap_lang.val := 
    λ: "r" "k", traverse "r" "k".

  Definition upsert : heap_lang.val :=
    rec: "upsert_rec" "p" "r" "k" "v" := 
      lockNode "r" ;;
      let: "res" := addContents "r" "k" "v" in
      if: "res" then
        Resolve (Fst ((#(), #true)%V, #())%V) "p" #();;       
        unlockNode "r";; #0
      else
        unlockNode "r";;
        "upsert_rec" "p" "r" "k" "v".

  Definition dsOp : heap_lang.val :=
    λ: "OP" "p" "r",
      let: "op" := Fst "OP" in
      let: "k" := Fst (Snd "OP") in
      let: "v" := Snd (Snd "OP") in
      if: "op" = #0 
      then search "r" "k"
      else upsert "p" "r" "k" "v".

  Inductive Opp := 
    searchOp : K → Opp | upsertOp : K → V → Opp.
  Definition Op := Opp.

  Definition Op_to_val (op: Op) : heap_lang.val :=
    match op with
    | searchOp k => (#0, (#k, #0))
    | upsertOp k v => (#1, (#k, #v))
    end.
    
  Definition absTUR := gmapUR K V.
  Definition absT := ucmra_car absTUR.

  Definition resT := V.
  Definition resT_to_base_lit (z: resT) : base_lit := LitInt z.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Definition resT_from_val (v : heap_lang.val) : option resT :=
    match v with
    | LitV(LitInt z) => Some z
    | _               => None
    end.
  Definition resT_to_val (z : resT) : heap_lang.val := LitV(LitInt z).
  
  Lemma resT_inj_prop : ∀ (z : resT), resT_from_val (resT_to_val z) = Some z.
  Proof. done. Qed.
  
  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.

  Lemma resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  Proof. try done. Qed.
    
  Definition seq_spec (op: Op) (C: absT) (C': absT) (res: resT) : Prop :=
    match op with
    | searchOp k => C' = C ∧ res = ((C : gmap K V) !!! k)
    | upsertOp k v => C' = <[k := v]> C ∧ res = 0%Z
    end.

  Global Instance seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Proof.
    intros op c c' res. unfold seq_spec. 
    destruct op; try apply and_dec; try destruct res; try apply _.
  Qed.
  
  Global Instance Op_inhabited : Inhabited Op := populate (searchOp 0).
  Global Instance absTUR_discrete : CmraDiscrete absTUR.
  Proof. try apply _. Qed.

  Global Instance resT_inhabited : Inhabited resT := Z.inhabited.

  (*
    The snapshot stores:
    0) set of nodes
    1) global interface
    3) map from nodes to node-local info

    Node local info:
    1) Edgesets
    2) VN, TN, QN, BN
    3) singleton interface
  *)
  Definition T := nat.
  Definition set_NodesUR := gsetUR Node.
  Definition ms_flowUR_KVT := multiset_flowint_ur (K * V * T).
  Definition ms_flowUR_K := multiset_flowint_ur K.
  Definition esTUR := gmapUR Node (gset K).
  Definition V_contentsUR := gmapUR K V.
  Definition T_contentsUR := gmapUR K T.
  Definition VT_contentsUR := gmapUR K (V * T : Type).

  Definition ESUR := gmapUR Node esTUR.
  Definition VNUR := gmapUR Node V_contentsUR.
  Definition TNUR := gmapUR Node T_contentsUR.
  Definition QNUR := gmapUR Node VT_contentsUR.
  Definition BNUR := gmapUR Node VT_contentsUR.
  Definition FlowUR_KVT := gmapUR Node $ ms_flowUR_KVT.
  Definition FlowUR_K := gmapUR Node $ ms_flowUR_K.

  Definition prod9UR A B C D E F G H I :=
    prodUR (prodUR (prodUR (prodUR (prodUR (prodUR (prodUR 
      (prodUR A B) C) D) E) F) G) H) I.

  Definition snapshotUR := 
    prod9UR set_NodesUR V_contentsUR ESUR VNUR TNUR QNUR BNUR FlowUR_KVT FlowUR_K.
  Definition snapshot := ucmra_car snapshotUR.

  Definition abs (s: snapshot) : absT :=
    match s with (_, c, _, _, _, _, _, _, _) => c end.

  Global Instance snapshotUR_discrete : CmraDiscrete snapshotUR.
  Proof. try apply _. Qed.

  Global Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Proof. try apply _. Qed.

  Global Instance absT_leibnizequiv : LeibnizEquiv (absT).
  Proof. try apply _. Qed.
  
  Global Instance snapshot_inhabited : Inhabited snapshot.
  Proof. try apply _. Qed. 

  Class dsGG Σ := ds { 
                    ds_fracG :: inG Σ (dfrac_agreeR $ prodUR esTUR V_contentsUR);
                    ds_heapG :: inG Σ (authR $ gmapUR Node $ agreeR gnameO)
                  }.
  
  Definition dsG := dsGG.

  (*
  Definition dsΣ : gFunctor := #[ ].
  
  Global Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsGG Σ.
  Proof. solve_inG. Qed.
  *)

  Definition FP (s: snapshot) : gset Node :=
    match s with (N, _, _, _, _, _, _, _, _) => N end.
  
  Definition ES (s: snapshot) (n: Node) : esT :=
      match s with (_, _, m, _, _, _, _, _, _) =>
        match (m !! n) with 
        | Some mn => mn
        | None => ∅ end end.
  
  Definition VN (s: snapshot) (n: Node) : gmap K V :=
      match s with (_, _, _, m, _, _, _, _, _) =>
        match (m !! n) with 
        | Some mn => mn
        | None => ∅ end end.
  
  Definition TN (s: snapshot) (n: Node) : gmap K T :=
    match s with (_, _, _, _, m, _, _, _, _) =>
      match (m !! n) with 
      | Some mn => mn
      | None => ∅ end end.

  Definition QN (s: snapshot) (n: Node) : gmap K (V * T) :=
    match s with (_, _, _, _, _, m, _, _, _) =>
      match (m !! n) with 
      | Some mn => mn
      | None => ∅ end end.
  
  Definition BN (s: snapshot) (n: Node) : gmap K (V * T) :=
    match s with (_, _, _, _, _, _, m, _, _) =>
      match (m !! n) with 
      | Some mn => mn
      | None => ∅ end end.
  
  Definition FI (s: snapshot) (n: Node) : multiset_flowint_ur (K * V * T) :=
    match s with (_, _, _, _, _, _, m, _) => 
      match (m !! n) with 
      | Some In => In
      | None => ∅ end end.

  Definition FJ (s: snapshot) (n: Node) : multiset_flowint_ur K :=
    match s with (_, _, _, _, _, _, _, m) => 
      match (m !! n) with 
      | Some In => In
      | None => ∅ end end.
      
  Definition GFI (s: snapshot) : multiset_flowint_ur (K * V * T) :=
    ([^op set] x ∈ FP s, FI s x).
  Definition GFJ (s: snapshot) : multiset_flowint_ur K :=
    ([^op set] x ∈ FP s, FJ s x).
  
  Definition snapshot_constraints (s: snapshot) : Prop :=
    ∃ (N: gset Node) (C: gmap K V) (ES: gmap Node esT)
      (VN: gmap Node (gmap K V)) (TN: gmap Node (gmap K T)) 
      (QN: gmap Node (gmap K (V * T))) (BN: gmap Node (gmap K (V * T))) 
      (I: gmap Node (multiset_flowint_ur (K * V * T)))
      (J: gmap Node (multiset_flowint_ur K)),
      s = (N, C, ES, VN, TN, QN, BN, I, J) ∧ dom ES = N ∧ dom VN = N ∧ dom TN = N 
      ∧ dom QN = N ∧ dom BN = N ∧ dom I = N ∧ dom J = N.
  
  Definition flow_constraints (n: Node) (es: esT) (Qn Bn : gmap K (V * T)) 
    (In : multiset_flowint_ur (K * V * T)) (Jn : multiset_flowint_ur K) : Prop :=
    (dom In = {[n]})
  ∧ (dom Jn = {[n]})
  ∧ (∀ k v t, k ∈ KS → (k, v, t) ∈ inset _ In n → Bn !!! k = (v, t))
  ∧ (∀ k, k ∈ KS → (Bn !! k = None ∨ k ∈ inset K Jn n))
  ∧ (∀ n' k v t, k ∈ KS → ((k, v, t) ∈ outset _ In n' ↔ 
                            k ∈ es !!! n' ∧ (Qn !! k = Some (v, t))))
  ∧ (∀ n' k, k ∈ KS → (k ∈ outset K Jn n' ↔ k ∈ es !!! n' ∧ k ∈ inset K Jn n))
  ∧ (∀ k, k ∈ KS → (∃ n', k ∈ es !!! n') → k ∈ inset K Jn n → k ∈ dom Qn)
  ∧ (∀ kvt, inf In n !!! kvt ≤ 1)
  ∧ (∀ n' kvt, out In n' !!! kvt ≤ 1)
  ∧ (∀ k, inf Jn n !!! k ≤ 1).

  Definition node_inv_pure (n: Node) (es: esT) (Vn : gmap K V) (Tn : gmap K T) 
    (Qn Bn : gmap K (V * T)) (In : multiset_flowint_ur (K * V * T)) 
    (Jn : multiset_flowint_ur K) : Prop :=
    (∀ k, k ∈ KS → ((k ∈ dom Vn → Bn !! k = Some (Vn !!! k, Tn !!! k)) 
                  ∧ (k ∉ dom Vn → Bn !! k = Qn !! k)))
  ∧ (∀ k, k ∈ KS → ((∀ n', k ∉ es !!! n') → Qn !! k = None))
  ∧ (∀ k, k ∈ KS → ((Qn !!! k).2 ≤ (Bn !!! k).2))
  ∧ (dom Tn = dom Vn)
  ∧ flow_constraints n es Qn Bn In Jn.

  Definition global_flow_constraints (r: Node) (I : multiset_flowint_ur (K * V * T))
    (J : multiset_flowint_ur K) : Prop :=
    (✓ I) ∧ (✓ J) ∧ (∀ n, inset _ I n = ∅) 
  ∧ (∀ n k, k ∈ KS → if decide (n = r) then k ∉ inset K J n
      else k ∈ inset K J n)
  ∧ (out_map I = ∅)
  ∧ (out_map J = ∅). 
  
  Definition per_tick_inv r s : Prop :=
    (r ∈ FP s ∧ inset _ (FI s r) r = ∅ ∧ inset _ (FJ s r) r = KS)
  ∧ global_flow_constraints r (GFI s) (GFJ s)
  ∧ (∀ k, (abs s : gmap K V) !!! k = (BN s r !!! k).1)
  ∧ (∀ n, n ∈ FP s → 
    node_inv_pure n (ES s n) (VN s n) (TN s n) (QN s n) (BN s n) (FI s n) (FJ s n))
  ∧ (∀ n n', n ∈ FP s → (ES s n) !!! n'  ≠ ∅ → n' ∈ FP s).

  Definition transition_inv r (M : gmap nat snapshot) (T : nat) : Prop :=
    (∀ n k v t t', t' ∈ dom M → BN (M !!! t') n !! k = Some (v, t) 
                    → BN (M !!! t) r !! k = Some (v, t))
  ∧ (∀ n k v t t', t' ∈ dom M → BN (M !!! t') n !!! k = (v, t) → t ≤ t')
  ∧ (∀ t, 0 ≤ t < T → 
      let s := M !!! t in let s' := (M !!! (t+1)%nat) in 
      (FP s ⊆ FP s')
    ∧ (∀ n k, BN s n !!! k = BN s' n !!! k ∨ (BN s n !!! k).2 < (BN s' n !!! k).2)
    ∧ (∀ n, inset _ (FJ s n) n ⊆ inset _ (FJ s' n) n)).
  
  Definition lock_frac (Σ: gFunctors) (Hg1: heapGS Σ) (Hg2 : dsGG Σ) γ es Vn :=
      own γ (to_frac_agree (1/2) (es, Vn)).

  Parameter γ_gh: gname. 

  Definition resources (Σ: gFunctors) (Hg1: heapGS Σ) (Hg2 : dsGG Σ) r s : iProp Σ :=
      ([∗ set] n ∈ FP s, ∃ b γ,
          own γ_gh (◯ {[n := to_agree γ]})
        ∗ lock_frac _ _ _ γ (ES s n) (VN s n)
        ∗ lockR _ _ b n (node Σ Hg1 r n (ES s n) (VN s n) 
                        ∗ lock_frac _ _ _ γ (ES s n) (VN s n))).

  Definition ds_inv Σ (Hg1 : heapGS Σ) (Hg2 : dsGG Σ) r (M: gmap nat snapshot) 
    (T: nat) (s: snapshot) : iProp Σ := 
      ⌜snapshot_constraints s⌝
    ∗ resources Σ _ _ r s
    ∗ ⌜∀ t, 0 ≤ t ≤ T → per_tick_inv r (M !!! t)⌝
    ∗ ⌜transition_inv r M T⌝.

  Global Instance ds_inv_timeless Σ (Hg1 : heapGS Σ) (Hg2 : dsGG Σ) r M T s : 
    Timeless (ds_inv Σ _ _ r M T s).
  Proof.
    rewrite /ds_inv. repeat apply bi.sep_timeless; try apply _.
    rewrite /resources. apply big_sepS_timeless. intros. 
    apply bi.exist_timeless. intros. apply bi.exist_timeless. intros. 
    apply bi.sep_timeless; try apply _. rewrite /lock_frac. 
    apply bi.sep_timeless; try apply _. destruct x0; try apply _.
  Qed.
  
  Definition local_pre (op : Op) :=
    match op with
    | searchOp k => k ∈ KS
    | upsertOp k v => k ∈ KS end.

End LSM_TREE.
