From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multiset_flows one_shot_proph typed_proph.

(** Proof setup **)

(* Keys, values and timestamps *)

Definition K := Z.
Definition V := Z.
Definition T := nat.
Definition KVT : Type := K * (V * T).
Parameter KS : gset K.
Parameter bot : V.

Notation "kvt .key" := (kvt.1) (at level 5).
Notation "kvt .value" := (kvt.2.1) (at level 5).
Notation "kvt .ts" := (kvt.2.2) (at level 5).

(* RAs used in proof *)

Definition ghost_heap'UR := gmapUR proph_id $ agreeR (gnameO).  
Definition set_tidR := authR (gsetUR proph_id).
Definition frac_histR := frac_agreeR (gsetUR KVT).
Definition histR := authR (gsetUR (KVT)).
Definition hist_exclR := authR $ optionUR $ exclR (gsetO KVT).
Definition time_exclR := authR $ optionUR $ exclR natUR.
Definition gh'R := authR $ ghost_heap'UR.
Definition tokenUR := exclR unitO.


Class multicopyG Σ := MULTICOPY {
                        multicopy_set_tidG :> inG Σ set_tidR;
                        multicopy_frac_histG :> inG Σ frac_histR;
                        multicopy_histG :> inG Σ histR;
                        multicopy_hist_exclG :> inG Σ hist_exclR;
                        multicopy_time_exclG :> inG Σ time_exclR;
                        multicopy_gh'G :> inG Σ gh'R;
                        multicopy_tokenG :> inG Σ tokenUR;
                      }.

Definition multicopyΣ : gFunctors :=
  #[GFunctor set_tidR; GFunctor frac_histR; GFunctor histR; 
    GFunctor hist_exclR; GFunctor time_exclR; GFunctor gh'R; 
    GFunctor tokenUR ].

Instance subG_multicopyΣ {Σ} : subG multicopyΣ Σ → multicopyG Σ.
Proof. solve_inG. Qed.

Section multicopy.
  Context {Σ} `{!heapG Σ, !multicopyG Σ}.
  Notation iProp := (iProp Σ).

  Global Definition mcsN N := N .@ "mcs".
  Global Definition threadN N := N .@ "thread".

  (** The multicopy template invariant *)
    
  Definition SR γ_s (kvt: KVT) : iProp := own γ_s (◯ {[kvt]}).  

  Definition map_of_set (C: gset KVT) : gmap K (V*T) := 
              let f := λ (kvt: KVT) (M: gmap K (V*T)), 
                         if (decide ((M !!! kvt.key).2 <= kvt.ts)) 
                         then <[kvt.key := (kvt.value, kvt.ts)]> M 
                         else M in
              set_fold f (∅: gmap K (V*T)) C.

  Definition set_of_map (M: gmap K (V*T)) : gset KVT := 
             let f := λ k vt H, H ∪ {[(k, (vt.1, vt.2))]} in
             map_fold f (∅: gset KVT) M.

  Definition chop_ts (M: gmap K (V*T)) : (gmap K V) := 
             let f := λ k vt m, <[k := vt.1]> m in
             map_fold f (∅: gmap K V) M.

  Definition HClock (t: T) (H: gset KVT) := 
              (∀ k v t', (k, (v, t')) ∈ H → t' < t).

  Definition HUnique (H: gset KVT) := 
              ∀ k t' v v', (k, (v, t')) ∈ H → (k, (v', t')) ∈ H → v = v'.

  Definition MCS_auth (γ_te γ_he: gname) (t: nat) (H: gset KVT) : iProp := 
      own γ_te (● Excl' t) ∗ own γ_he (● Excl' H).

  Definition MCS (γ_te γ_he: gname) (t: nat) (H: gset KVT) : iProp := 
      own γ_te (◯ Excl' t) ∗ own γ_he (◯ Excl' H) ∗ ⌜HClock t H⌝ ∗ ⌜HUnique H⌝.
  
  Definition HInit (H: gset KVT) := ∀ k, k ∈ KS → (k, (bot, 0)) ∈ H.

  Definition mcs_inv_high (γ_te γ_he γ_s: gname) (Prot: gset KVT → iProp) 
                          (T: T) (H: gset KVT) : iProp :=
      MCS_auth γ_te γ_he T H
    ∗ own γ_s (● H) 
    ∗ ⌜HInit H⌝
    ∗ ⌜HClock T H⌝
    ∗ ⌜HUnique H⌝
    ∗ Prot H.
    
  (** Invariant Inv in the paper *)
  Definition mcs (γ_te γ_he γ_s: gname) (Prot: gset KVT → iProp) 
                    (Inv_tpl: gset KVT → iProp) : iProp :=
    ∃ (t: T) (H: gset KVT),
      mcs_inv_high γ_te γ_he γ_s Prot t H
    ∗ Inv_tpl H.  

  Definition mcs_inv (N: namespace) (γ_te γ_he γ_s: gname)
                      (Prot: gset KVT → iProp) 
                      (Inv_tpl: gset KVT → iProp) := 
    inv (mcsN N) (mcs γ_te γ_he γ_s Prot Inv_tpl).

  (** Helping Inv **)

  Definition pau N γ_te γ_he P (Q : val → iProp) k := 
    (▷ P -∗ ◇ AU << ∀ t H, MCS γ_te γ_he t H >> 
                  @ ⊤ ∖ (↑(mcsN N) ∪ ↑(threadN N)), ∅
                 << ∃ (v': V) (t': T), MCS γ_te γ_he t H 
                         ∗ ⌜map_of_set H !!! k = (v', t')⌝, 
                         COMM Q #v' >>)%I.

  Definition Pending (P: iProp) (H: gset KVT) (k: K) (vp: V) (t0: T) : iProp := 
    P ∗ ⌜∀ t', (k, (vp, t')) ∈ H → t' < t0⌝.

  Definition Done (γ_tk: gname) (Q: val → iProp) 
                              (H: gset KVT) (k: K) (vp: V) (t0: T) : iProp := 
    (Q #vp ∨ own γ_tk (Excl ())) ∗ ⌜∃ t', (k, (vp, t')) ∈ H ∧ t0 ≤ t'⌝. 

  Definition State γ_sy (t_id: proph_id) 
                          γ_tk P Q H (k: K) (vp: V) (t0: T) : iProp :=
                        own γ_sy (to_frac_agree (1/2) H)
                     ∗ (Pending P H k vp t0 
                        ∨ Done γ_tk Q H k vp t0).

  Definition Reg (N: namespace) (γ_te γ_he γ_ght: gname) 
                            (H: gset KVT) (t_id: proph_id) : iProp :=
    ∃ (P: iProp) (Q: val → iProp) (k: K) (vp: V) (t0: T) (vtid: val) (γ_tk γ_sy: gname), 
        proph1 t_id vtid
      ∗ own γ_ght (◯ {[t_id := to_agree γ_sy]})  
      ∗ own (γ_sy) (to_frac_agree (1/2) H)
      ∗ □ pau N γ_te γ_he P Q k
      ∗ inv (threadN N) (∃ H, State γ_sy t_id γ_tk P Q H (k: K) (vp: V) (t0: T)).

  Definition Prot_help (N: namespace) (γ_te γ_he γ_td γ_ght: gname) 
                                        (H: gset KVT) : iProp :=
    ∃ (R: gset proph_id) (hγt: gmap proph_id (agreeR gnameO)),
        own γ_td (● R)
      ∗ own γ_ght (● hγt) ∗ ⌜dom (gset proph_id) hγt = R⌝  
      ∗ ([∗ set] t_id ∈ R, Reg N γ_te γ_he γ_ght H t_id).

  (** \overline{MCS} in the paper *)
  Definition MCS_high N γ_te γ_he γ_s Inv_tpl γ_td γ_ght M : iProp :=
    ∃ t H, MCS γ_te γ_he t H ∗ ⌜chop_ts (map_of_set H) = M⌝
      ∗ mcs_inv N γ_te γ_he γ_s (Prot_help N γ_te γ_he γ_td γ_ght) Inv_tpl.

  Definition ghost_update_protocol N γ_te γ_he Prot_help k : iProp :=
        ∀ v T H, ⌜map_of_set (H ∪ {[k, (v, T)]}) !!! k = (v, T)⌝ -∗  
                MCS_auth γ_te γ_he (T+1) (H ∪ {[(k, (v, T))]}) -∗ 
                  Prot_help H ={⊤ ∖ ↑mcsN N}=∗
                    Prot_help (H ∪ {[(k, (v, T))]}) 
                      ∗ MCS_auth γ_te γ_he (T+1) (H ∪ {[(k, (v, T))]}).

End multicopy.

