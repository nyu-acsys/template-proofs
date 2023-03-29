From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants fancy_updates.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
From diaframe.heap_lang Require Import proof_automation atomic_specs wp_auto_lob.
Require Export one_shot_proph typed_proph data_structure.

Module Type HINDSIGHT_DEFS.
  Declare Module DS : DATA_STRUCTURE.
  Import DS.
  
  Global Instance snapshotUR_discrete' : CmraDiscrete snapshotUR.
  Proof.
    apply snapshotUR_discrete.
  Qed.
  
  Global Instance absTUR_discrete' : CmraDiscrete absTUR.
  Proof.
    apply absTUR_discrete.
  Qed.

  Global Instance snapshot_leibnizequiv' : LeibnizEquiv (snapshot).
  Proof.
    apply snapshot_leibnizequiv.
  Qed.  

  Global Instance snapshot_inhabited' : Inhabited snapshot.
  Proof.
    apply snapshot_inhabited.
  Qed.

  Global Instance resT_inhabited' : Inhabited resT.
  Proof.
    apply resT_inhabited.
  Qed.

  Global Instance Op_inhabited' : Inhabited Op.
  Proof.
    apply Op_inhabited.
  Qed.

  
  (* RAs used in proof *)

  Definition auth_natUR := authUR $ max_natUR.
  Definition agree_snapshotR := agreeR $ snapshotUR.
  Definition frac_absTR := dfrac_agreeR $ absTUR.
  Definition historyR := gmapUR nat $ snapshotUR.
  Definition auth_historyR := authR $ gmapUR nat $ agree_snapshotR.
  Definition frac_historyR := dfrac_agreeR $ historyR.
  Definition tokenUR := exclR unitO.
  Definition set_tidR := authR (gsetUR proph_id). 
  Definition thread_viewR := authUR $ 
                              gmapUR proph_id $ 
                                agreeR $ prodO natO gnameO.

  Class dsG Σ := DS {
                  dsG_auth_natG :> inG Σ auth_natUR;
                  dsG_agree_snapshotG :> inG Σ agree_snapshotR;
                  dsG_frac_absTG :> inG Σ frac_absTR;
                  dsG_historyG :> inG Σ historyR;
                  dsG_auth_historyG :> inG Σ auth_historyR;
                  dsG_tokenG :> inG Σ tokenUR;
                  dsG_frac_historyG :> inG Σ frac_historyR;
                  dsG_set_tidG :> inG Σ set_tidR;
                  dsG_thread_viewG :> inG Σ thread_viewR
                 }.
                 
  Definition dsΣ : gFunctors :=
    #[ GFunctor auth_natUR; GFunctor agree_snapshotR;
       GFunctor frac_absTR; GFunctor historyR;
       GFunctor auth_historyR; GFunctor tokenUR; 
       GFunctor frac_historyR; GFunctor set_tidR;
       GFunctor thread_viewR ].
  
  Global Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsG Σ.
  Proof. solve_inG. Qed.

  Context {Σ} `{!heapGS Σ, !dsG Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types M : gmap nat snapshot.
  Implicit Types T : nat.
  
  Global Definition cntrN N := N .@ "cntr".
  Global Definition threadN N := N .@ "thread".
  

  Definition map_max (M: gmap nat snapshot) : nat := 
    max_list (elements (dom M)).

  Definition hist γ_t γ_m M T : iProp :=
    ∃ (M': gmap nat (agreeR (_))),
      own γ_t (● MaxNat T) ∗ own γ_m (● M')
    ∗ ⌜T = map_max M⌝
    ∗ ⌜map_Forall (λ k a, a = to_agree (M !!! k)) M'⌝
    ∗ ⌜∀ t, t < T → M !!! t ≠ M !!! (t+1)%nat⌝.

  Definition dsRep γ_s (a: absTUR) : iProp := 
    own γ_s (to_frac_agree (1/2) a).

  Definition dsRepI γ_s (a: absTUR) : iProp := 
    own γ_s (to_frac_agree (1/2) a).
    
  (** Helping Inv **)
  
  Definition au N γ_r op (Q : val → iProp) := 
    (AU << ∃∃ a, dsRep γ_r a >> 
          @ ⊤ ∖ ↑(cntrN N), ∅
        << ∀∀ a' res, dsRep γ_r a' ∗ ⌜seq_spec op a a' res⌝, COMM Q #res >>)%I.
        
  Definition past_lin M T op res t0 : iProp :=
    ⌜match updater_thread op res with
    | true =>
      ∃ t, t0 ≤ t < T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! (t+1)%nat)) res
    | false =>  
      ∃ t, t0 ≤ t ≤ T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! t)) res end⌝.

  Definition past_state γ_m (t0: nat) (s: snapshot) : iProp :=
    ∃ t, ⌜t0 ≤ t⌝ ∗ own γ_m (◯ {[t := to_agree s]}).
  
  Definition past_two_states γ_m (t0: nat) (s s': snapshot) : iProp :=
    ∃ t, ⌜t0 ≤ t⌝ 
    ∗ own γ_m (◯ {[t := to_agree s]}) 
    ∗ own γ_m (◯ {[t+1 := to_agree s']}).

  Definition past_lin_witness γ_m op res t0 : iProp :=
    match updater_thread op res with
    | true =>
      ∃ s s', past_two_states γ_m t0 s s' ∗ ⌜seq_spec op (abs s) (abs s') res⌝
    | false =>  
      ∃ s, past_state γ_m t0 s ∗ ⌜seq_spec op (abs s) (abs s) res⌝ end.

  Definition Pending (P: iProp) M T op vp t0 : iProp := 
    P ∗ £1 ∗ ¬ past_lin M T op vp t0.

  Definition Done γ_tk (Q: val → iProp) M T op (vp: resT) t0 : iProp := 
      (Q #vp ∨ own γ_tk (Excl ())) ∗ past_lin M T op vp t0.

  Definition State γ_sy γ_tk P Q M T op vp t0 : iProp :=
      own γ_sy (to_frac_agree (1/2) M)
    ∗ ⌜T = map_max M⌝ 
    ∗ (Pending P M T op vp t0 ∨ Done γ_tk Q M T op vp t0).

  Definition thread_vars γ_t γ_ght γ_sy t_id t0 : iProp := 
    own γ_ght (◯ {[t_id := to_agree (t0, γ_sy)]}) ∗ own γ_t (◯ MaxNat t0).

  Definition Reg N γ_t γ_s γ_ght t_id M : iProp :=
    ∃ γ_tk γ_sy Q op vp t0 (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght γ_sy t_id t0
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ inv (threadN N) (∃ M T, State γ_sy γ_tk (au N γ_s op Q) Q M T op vp t0).

  Definition helping_inv (N: namespace) γ_t γ_s γ_td γ_ght M : iProp :=
    ∃ (R: gset proph_id) (hγt: gmap proph_id (agreeR _)),
        own γ_td (● R)
      ∗ own γ_ght (● hγt) ∗ ⌜dom hγt = R⌝  
      ∗ ([∗ set] t_id ∈ R, Reg N γ_t γ_s γ_ght t_id M).
  
  Definition ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv : iProp :=
    inv (cntrN N)
    (∃ M T (s: snapshot),
      dsRepI γ_s (abs s) ∗ ⌜abs (M !!! T) = abs s⌝
    ∗ hist γ_t γ_m M T
    ∗ helping_inv N γ_t γ_s γ_td γ_ght M
    ∗ template_inv M T s).
(*    
  Instance dsRep_timeless : ∀ γ_s C, Timeless (dsRep γ_s C).
  Proof.
    intros γ_s C. rewrite /dsRep. Search Timeless. 
    apply own_timeless; apply _.
  Qed.   
*)    
  Definition update_helping_protocol N γ_t γ_s γ_td γ_ght : iProp :=
        ∀ M T n s, 
          ⌜map_max M = T⌝ -∗   
            dsRep γ_s n -∗ own γ_t (● MaxNat T) -∗ 
              helping_inv N γ_t γ_s γ_td γ_ght M ={⊤ ∖ ↑cntrN N}=∗
                helping_inv N γ_t γ_s γ_td γ_ght (<[T := s]> M) 
                ∗ dsRep γ_s n ∗ own γ_t (● MaxNat T).
    
End HINDSIGHT_DEFS.