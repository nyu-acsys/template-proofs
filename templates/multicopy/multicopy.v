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

(* Keys and timestamps *)

Definition K := Z.
Definition KT : Type := K * nat.
Parameter KS : gset K.

(* RAs used in proof *)

Definition ghost_heap'UR := gmapUR proph_id $ agreeR (gnameO).  

Definition set_tidR := authR (gsetUR proph_id).
Definition frac_histR := frac_agreeR (gsetUR KT).
Definition histR := authR (gsetUR (KT)).
Definition hist_exclR := authR $ optionUR $ exclR (gsetO KT).
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
  Global Definition helpN N := N .@ "help".
  Global Definition threadN N := N .@ "thread".

  (** The multicopy template invariant *)
    
  Definition mcs_sr γ_s (kt: KT) : iProp := own γ_s (◯ {[kt]}).  

  Definition map_of_set (C: gset KT) : gmap K nat := 
              let f := λ (kt: KT) (M: gmap K nat), 
                         if (decide (M !!! kt.1 <= kt.2)) 
                         then (<[kt.1 := kt.2]> M : gmap K nat) else M in
              set_fold f (∅: gmap K nat) C.

  Definition set_of_map (C: gmap K nat) : gset KT := 
             let f := λ k t H, H ∪ {[(k,t)]} in
             map_fold f (∅: gset KT) C.

  Definition maxTS (T: nat) (H: gset KT) := 
              (∀ (k: K) t', (k, t') ∈ H → t' < T) ∧ (T > 0).

  Definition MCS_auth (γ_te γ_he: gname) (T: nat) (H: gset KT) : iProp := 
      own γ_te (● Excl' T) ∗ own γ_he (● Excl' H).

  Definition MCS (γ_te γ_he: gname) (T: nat) (H: gset KT) : iProp := 
      own γ_te (◯ Excl' T) ∗ own γ_he (◯ Excl' H) ∗ ⌜maxTS T H⌝.
  
  Definition history_init (H: gset KT) := ∀ k, k ∈ KS → (k, 0) ∈ H.

  Definition mcs_inv_high (γ_te γ_he γ_s: gname) (protocol_abs: gset KT → iProp) 
                          (T: nat) (H: gset KT) : iProp :=
      MCS_auth γ_te γ_he T H
    ∗ own γ_s (● H) 
    ∗ ⌜history_init H⌝
    ∗ ⌜maxTS T H⌝
    ∗ protocol_abs H.
    
  (** Invariant Inv in the paper *)
  Definition mcs (γ_te γ_he γ_s: gname) (protocol_abs: gset KT → iProp) 
                    (mcs_abs: nat → gset KT → iProp) : iProp :=
    ∃ (T: nat) (H: gset KT),
      mcs_inv_high γ_te γ_he γ_s protocol_abs T H
    ∗ mcs_abs T H.  

  Definition mcs_inv (N: namespace) (γ_te γ_he γ_s: gname)
                      (protocol_abs: gset KT → iProp) 
                      (mcs_abs: nat → gset KT → iProp) := 
    inv (mcsN N) (mcs γ_te γ_he γ_s protocol_abs mcs_abs).

  (** Helping Inv **)
(*
  Definition helping (N: namespace) (γ_fr: gname) 
                      (protocol_abs : gset KT → iProp) : iProp :=
      ∃ (H: gset KT),  
        own γ_fr (to_frac_agree (1/2) H)
      ∗ protocol_abs H.
  
  Definition helping_inv N γ_fr protocol_abs : iProp :=
    inv (helpN N) (helping N γ_fr protocol_abs).
*)  
  Definition pau N γ_te γ_he P (Q : val → iProp) k := 
    (▷ P -∗ ◇ AU << ∀ t H, MCS γ_te γ_he t H >> 
                  @ ⊤ ∖ (↑(mcsN N) ∪ ↑(threadN N)), ∅
                 << ∃ (t': nat), MCS γ_te γ_he t H ∗ ⌜map_of_set H !!! k = t'⌝, 
                                                          COMM Q #t' >>)%I.


  Definition state_lin_pending (P: iProp) (H: gset KT) (k: K) (vp: nat) : iProp := 
    P ∗ ⌜(k, vp) ∉ H⌝.

  Definition state_lin_done (γ_tk: gname) (Q: val → iProp) 
                              (H: gset KT) (k: K) (vp : nat) : iProp := 
    (Q #vp ∨ own γ_tk (Excl ())) ∗ ⌜(k, vp) ∈ H⌝. 

  Definition get_op_state γ_sy (t_id: proph_id) 
                          γ_tk P Q H (k: K) (vp: nat) : iProp :=
                        own γ_sy (to_frac_agree (1/2) H) 
                     ∗ (state_lin_pending P H k vp 
                        ∨ state_lin_done γ_tk Q H k vp).

  Definition registered (N: namespace) (γ_te γ_he γ_ght: gname) 
                            (H: gset KT) (t_id: proph_id) : iProp :=
    ∃ (P: iProp) (Q: val → iProp) (k: K) (vp: nat) (vt: val) (γ_tk γ_sy: gname), 
        proph1 t_id vt
      ∗ own γ_ght (◯ {[t_id := to_agree γ_sy]})  
      ∗ own (γ_sy) (to_frac_agree (1/2) H)
      ∗ □ pau N γ_te γ_he P Q k
      ∗ inv (threadN N) (∃ H, get_op_state γ_sy t_id γ_tk P Q H (k: K) (vp: nat)).

  Definition protocol_conc (N: namespace) (γ_te γ_he γ_td γ_ght: gname) 
                                        (H: gset KT) : iProp :=
    ∃ (TD: gset proph_id) (hγt: gmap proph_id (agreeR gnameO)),
        own γ_td (● TD)
      ∗ own γ_ght (● hγt) ∗ ⌜dom (gset proph_id) hγt = TD⌝  
      ∗ ([∗ set] t_id ∈ TD, registered N γ_te γ_he γ_ght H t_id).

  Definition MCS_high N γ_te γ_he γ_s mcs_abs γ_td γ_ght t M : iProp :=
  ∃ H, MCS γ_te γ_he t H ∗ ⌜map_of_set H = M⌝
     ∗ mcs_inv N γ_te γ_he γ_s (protocol_conc N γ_te γ_he γ_td γ_ght) mcs_abs.      

  Definition ghost_update_protocol N γ_te γ_he protocol_abs k : iProp :=
        (∀ T H, ⌜map_of_set (H ∪ {[k, T]}) !!! k = T⌝ -∗  
                MCS_auth γ_te γ_he (T+1) (H ∪ {[(k, T)]}) -∗ 
                  protocol_abs H ={⊤ ∖ ↑mcsN N}=∗
                    protocol_abs (H ∪ {[(k, T)]}) 
                      ∗ MCS_auth γ_te γ_he (T+1) (H ∪ {[(k, T)]})).

End multicopy.

