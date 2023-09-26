From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants fancy_updates.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
From flows Require Export one_shot_proph typed_proph.


Module Type DATA_STRUCTURE.
  
  Parameter dsOp : val.
  Parameter Op : Type.
  Parameter Op_to_val : Op -> val.

  Parameter absTUR : ucmra.
  Definition absT := ucmra_car absTUR.

  Parameter resT : Type.
  Parameter resT_to_base_lit : resT -> base_lit.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Parameter resT_from_val : val -> option resT.
  Parameter resT_to_val : resT -> val.
  Parameter resT_inj_prop : 
    ∀ (r : resT), resT_from_val (resT_to_val r) = Some r.
  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.
  Parameter resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  
  Parameter seq_spec : Op -> absT -> absT -> resT -> Prop.
  Parameter seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Parameter updater_thread: Op -> resT -> bool.
  Parameter updater_thread_dec: 
    ∀ op res b, Decision (updater_thread op res = b).


  Parameter snapshotUR : ucmra.
  Definition snapshot := ucmra_car snapshotUR.
  
  Parameter abs : snapshot -> absT.
  
  #[global] Declare Instance Op_inhabited : Inhabited Op.
  #[global] Declare Instance absTUR_discrete : CmraDiscrete absTUR.
  #[global] Declare Instance absT_leibnizequiv : LeibnizEquiv (absT).
  #[global] Declare Instance resT_inhabited : Inhabited resT.
  #[global] Declare Instance snapshotUR_discrete : CmraDiscrete snapshotUR.  
  #[global] Declare Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  #[global] Declare Instance snapshot_inhabited : Inhabited snapshot.
  
(*   Parameter dsG : gFunctors -> Set. *)
  (* Parameter dsΣ : gFunctors. *)
  
  (* Parameter subG_dsΣ : ∀ Σ, subG dsΣ Σ → dsG Σ. *)
  
  Context `{!heapGS Σ, !dsG Σ}.
  
  Parameter ds_inv : gmap nat snapshot -> nat -> snapshot -> iProp Σ.

End DATA_STRUCTURE.  


Module HINDSIGHT_DEFS (DS : DATA_STRUCTURE).
  Import DS.
    
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
  Definition upd_fracR := fracR. 

  Class hsG Σ := HS {
                  hsG_auth_natG :> inG Σ auth_natUR;
                  hsG_agree_snapshotG :> inG Σ agree_snapshotR;
                  hsG_frac_absTG :> inG Σ frac_absTR;
                  hsG_historyG :> inG Σ historyR;
                  hsG_auth_historyG :> inG Σ auth_historyR;
                  hsG_tokenG :> inG Σ tokenUR;
                  hsG_frac_historyG :> inG Σ frac_historyR;
                  hsG_set_tidG :> inG Σ set_tidR;
                  hsG_thread_viewG :> inG Σ thread_viewR;
                  hsG_upd_fracG :> inG Σ upd_fracR
                 }.
                 
  Definition hsΣ : gFunctors :=
    #[ GFunctor auth_natUR; GFunctor agree_snapshotR;
       GFunctor frac_absTR; GFunctor historyR;
       GFunctor auth_historyR; GFunctor tokenUR; 
       GFunctor frac_historyR; GFunctor set_tidR;
       GFunctor thread_viewR; GFunctor upd_fracR].
  
  Global Instance subG_hsΣ {Σ} : subG hsΣ Σ → hsG Σ.
  Proof. solve_inG. Qed.
  
  Context `{!heapGS Σ, !hsG Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types M : gmap nat snapshot.
  Implicit Types T : nat.
  
  Global Definition cntrN N := N .@ "cntr".
  Global Definition threadN N := N .@ "thread".
  

  Definition map_max (M: gmap nat snapshot) : nat := 
    max_list (elements (dom M)).
    
  Lemma map_max_dom (M: gmap nat snapshot) t :
    t ∈ dom M → t ≤ map_max M.
  Proof.
    intros Ht. unfold map_max.
    apply max_list_elem_of_le.
    set_solver.
  Qed.
  
  Definition hist γ_t γ_m M T : iProp :=
    ∃ (M': gmap nat (agreeR (_))),
      own γ_t (● MaxNat T) ∗ own γ_m (● M')
    ∗ ⌜T = map_max M⌝ ∗ ⌜T ∈ dom M⌝
    ∗ ⌜∀ t s, M' !! t ≡ Some (to_agree s) ↔ M !! t = Some s⌝
    ∗ ⌜∀ t, t < T → abs (M !!! t) ≠ abs (M !!! (t+1)%nat)⌝.

  Definition dsRep γ_r (a: absTUR) : iProp := 
    own γ_r (to_frac_agree (1/2) a).

  Definition dsRepI γ_r (a: absTUR) : iProp := 
    own γ_r (to_frac_agree (1/2) a).
    
  (** Helping Inv **)
  
  Definition au N γ_r op (Q : val → iProp) := 
    (AU << ∃∃ a, dsRep γ_r a >> 
          @ ⊤ ∖ ↑(cntrN N), ∅
        << ∀∀ a' res, dsRep γ_r a' ∗ ⌜seq_spec op a a' res⌝, COMM Q #res >>)%I.
  (*
  Definition au_nupd N γ_r op (Q : val → iProp) := 
    (AU << ∃∃ a, dsRep γ_r a >> 
          @ ⊤ ∖ ↑(cntrN N), ∅
        << ∀∀ res, dsRep γ_r a ∗ ⌜seq_spec op a a res⌝, COMM Q #res >>)%I.
  *)
  Definition past_lin M T op res t0 : iProp :=
    ⌜∃ t, t0 ≤ t ≤ T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! t)) res⌝.

  Definition past_state γ_m (t0: nat) (s: snapshot) : iProp :=
    ∃ t, ⌜t0 ≤ t⌝ ∗ own γ_m (◯ {[t := to_agree s]}).
  
  (*
  Definition past_two_states γ_m (t0: nat) (s s': snapshot) : iProp :=
    ∃ t, ⌜t0 ≤ t⌝ 
    ∗ own γ_m (◯ {[t := to_agree s]}) 
    ∗ own γ_m (◯ {[t+1 := to_agree s']}).
  *)
  
  Definition past_lin_witness γ_m op res t0 : iProp :=
    ∃ s, past_state γ_m t0 s ∗ ⌜seq_spec op (abs s) (abs s) res⌝.

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

  Definition Reg_nupd N γ_t γ_r γ_ght t_id M : iProp :=
    ∃ γ_tk γ_sy Q op vp t0 (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght γ_sy t_id t0
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ ⌜updater_thread op vp = false⌝ 
      ∗ inv (threadN N) (∃ M T, State γ_sy γ_tk (au N γ_r op Q) Q M T op vp t0).

  Definition Reg_upd N γ_t γ_r γ_ght t_id : iProp :=
    ∃ γ_fr Q op vp t0 (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght γ_fr t_id t0
      ∗ ⌜updater_thread op vp = true⌝ 
      ∗ ((au N γ_r op Q) ∗ own (γ_fr) (1/2)%Qp ∨ own (γ_fr) (1%Qp)).

  Definition helping_inv (N: namespace) γ_t γ_r γ_td1 γ_td2 γ_ght M : iProp :=
    ∃ (R1 R2: gset proph_id) (hγt: gmap proph_id (agreeR _)),
        own γ_td1 (● R1) ∗ own γ_td2 (● R2)
      ∗ own γ_ght (● hγt) ∗ ⌜dom hγt = R1 ∪ R2⌝
      ∗ ([∗ set] t_id ∈ R1, Reg_upd N γ_t γ_r γ_ght t_id)
      ∗ ([∗ set] t_id ∈ R2, Reg_nupd N γ_t γ_r γ_ght t_id M).
  
  Definition main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght : iProp :=
    inv (cntrN N)
    (∃ M T (s: snapshot),
      dsRepI γ_r (abs s) ∗ ⌜M !!! T ≡ s⌝
    ∗ hist γ_t γ_m M T
    ∗ helping_inv N γ_t γ_r γ_td1 γ_td2 γ_ght M
    ∗ ds_inv M T s).

  Definition update_helping_protocol N γ_t γ_s γ_td1 γ_td2 γ_ght : iProp :=
        ∀ M T n s, 
          ⌜map_max M = T⌝ -∗   
            dsRep γ_s n -∗ own γ_t (● MaxNat T) -∗ 
              helping_inv N γ_t γ_s γ_td1 γ_td2 γ_ght M ={⊤ ∖ ↑cntrN N}=∗
                helping_inv N γ_t γ_s γ_td1 γ_td2 γ_ght (<[T := s]> M) 
                ∗ dsRep γ_s n ∗ own γ_t (● MaxNat T).
    
End HINDSIGHT_DEFS.


