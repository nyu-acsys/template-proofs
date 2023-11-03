From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants fancy_updates.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
From flows Require Export one_shot_proph typed_proph gset_seq.

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
  #[global] Declare Instance seq_spec_dec : 
    ∀ op c c' res, Decision (seq_spec op c c' res).
  (*
  Parameter updater_thread: Op -> resT -> bool.
  Parameter updater_thread_dec: 
    ∀ op res b, Decision (updater_thread op res = b).
  *)

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
  Definition sync_mapR := authUR $ gmapUR proph_id $ agreeR $ gnameO.
  Definition ts_mapR := authUR $ gmapUR proph_id $ agreeR $ natO.
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
                  hsG_sync_mapG :> inG Σ sync_mapR;
                  hsG_ts_mapG :> inG Σ ts_mapR;
                  hsG_upd_fracG :> inG Σ upd_fracR
                 }.
                 
  Definition hsΣ : gFunctors :=
    #[ GFunctor auth_natUR; GFunctor agree_snapshotR;
       GFunctor frac_absTR; GFunctor historyR;
       GFunctor auth_historyR; GFunctor tokenUR; 
       GFunctor frac_historyR; GFunctor set_tidR;
       GFunctor sync_mapR; GFunctor ts_mapR; GFunctor upd_fracR].
  
  Global Instance subG_hsΣ {Σ} : subG hsΣ Σ → hsG Σ.
  Proof. solve_inG. Qed.
  
  Context `{!heapGS Σ, !hsG Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types M : gmap nat snapshot.
  Implicit Types T : nat.
  
  Global Definition cntrN N := N .@ "cntr".
  Global Definition threadN N := N .@ "thread".
  
  Definition hist γ_t γ_m M T : iProp :=
    ∃ (M': gmap nat (agreeR (_))),
      own γ_t (● MaxNat T) ∗ own γ_m (● M')
    ∗ ⌜dom M = gset_seq 0 T⌝
    ∗ ⌜∀ t s, M' !! t ≡ Some (to_agree s) ↔ M !! t = Some s⌝
    ∗ ⌜∀ t, t < T → (M !!! t) ≠ (M !!! (t+1)%nat)⌝.

  Definition dsRep γ_r (a: absTUR) : iProp := 
    own γ_r (to_frac_agree (1/2) a).

  Definition dsRepI γ_r (a: absTUR) : iProp := 
    own γ_r (to_frac_agree (1/2) a).
    
  (** Helping Inv **)
  
  Definition au N γ_r op (Q : val → iProp) := 
    (AU << ∃∃ a, dsRep γ_r a >> 
          @ ⊤ ∖ (↑N), ∅
        << ∀∀ a' res, dsRep γ_r a' 
          ∗ ⌜seq_spec op a a' res⌝, COMM Q #res >>)%I.

  Definition past_lin M T op res t0 : iProp :=
    ⌜∃ t, t0 ≤ t ≤ T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! t)) res⌝.

  Definition past_state γ_m (t0: nat) (s: snapshot) : iProp :=
    ∃ t, ⌜t0 ≤ t⌝ ∗ own γ_m (◯ {[t := to_agree s]}).
  
  Definition past_lin_witness γ_m op res t0 : iProp :=
    ∃ s, past_state γ_m t0 s ∗ ⌜seq_spec op (abs s) (abs s) res⌝.

  Definition Token γ := own γ (Excl ()).
  
  Definition Pending P M T op vp t0 : iProp := 
      P ∗ £1 ∗ ¬ past_lin M T op vp t0.

  Definition Done γ_tk (Q: val → iProp) M T op (vp: resT) t0 : iProp := 
    (Q #vp ∨ Token γ_tk) ∗ past_lin M T op vp t0.
  
  Definition State γ_sy γ_tk P Q M T op vp t0: iProp :=
        own γ_sy (to_frac_agree (1/2) M)
      ∗ ⌜dom M = gset_seq 0 T⌝ ∗ ⌜t0 ≤ T⌝
      ∗ (Pending P M T op vp t0 ∨ Done γ_tk Q M T op vp t0).

  Definition thread_start γ_t γ_mt t_id t0 : iProp := 
    own γ_mt (◯ {[t_id := to_agree t0]}) ∗ own γ_t (◯ MaxNat t0).

  Definition thread_sync γ_msy t_id γ_sy : iProp := 
      own γ_msy (◯ {[t_id := to_agree γ_sy]}).
  
  Definition Reg N γ_t γ_r γ_mt γ_msy t_id M : iProp :=
    ∃ γ_tk γ_sy Q op vp t0, 
        thread_start γ_t γ_mt t_id t0
      ∗ own γ_msy (◯ {[t_id := to_agree γ_sy]})
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ inv (threadN N) 
        (∃ M T, State γ_sy γ_tk (au N γ_r op Q) Q M T op vp t0).
    
  Definition helping_inv (N: namespace) γ_t γ_r γ_mt γ_msy M : iProp :=
    ∃ (Mt: gmap proph_id (agreeR nat)) (Msy: gmap proph_id (agreeR gname)),
        own γ_mt (● Mt) 
      ∗ own γ_msy (● Msy) 
      ∗ ⌜dom Msy ⊆ dom Mt⌝ 
      ∗ ([∗ set] t_id ∈ dom Mt, ∃ vtid, proph1 t_id vtid)
      ∗ ([∗ set] t_id ∈ dom Msy, Reg N γ_t γ_r γ_mt γ_msy t_id M).

  Definition main_inv N γ_t γ_r γ_m γ_mt γ_msy : iProp :=
    inv (cntrN N)
    (∃ M T (s: snapshot),
      dsRepI γ_r (abs s) ∗ ⌜M !!! T ≡ s⌝
    ∗ hist γ_t γ_m M T
    ∗ helping_inv N γ_t γ_r γ_mt γ_msy M
    ∗ ds_inv M T s).

  Definition update_helping_protocol N γ_t γ_r γ_mt γ_msy : iProp :=
    ∀ M T s, 
    ⌜dom M = gset_seq 0 T⌝ -∗   
    dsRep γ_r (abs s) -∗
    helping_inv N γ_t γ_r γ_mt γ_msy M ={⊤ ∖ ↑cntrN N}=∗
        helping_inv N γ_t γ_r γ_mt γ_msy (<[T+1 := s]> M) ∗ dsRep γ_r (abs s).

  Definition update_helping_protocol2 N γ_t γ_r γ_mt γ_msy : iProp :=
    ∀ M T s', 
    ⌜dom M = gset_seq 0 T⌝ -∗
    ⌜abs s' = abs (M !!! T)⌝ -∗
    helping_inv N γ_t γ_r γ_mt γ_msy M ={⊤ ∖ ↑cntrN N}=∗
        helping_inv N γ_t γ_r γ_mt γ_msy (<[T+1 := s']> M).

  Definition is_snd (b: bool) (x : val * val) := ∃ v, x.1 = (v, #b)%V.  

  Global Instance is_snd_dec : ∀ b (x : val * val), Decision (is_snd b x).
  Proof.
    intros b [x1 x2]. rewrite /is_snd /=. destruct x1.
    - right; intros [v1 H']; try done.
    - right; intros [v1 H']; try done.
    - destruct (decide (x1_2 = #b)) as [-> | Hx1]. 
      + left. by exists x1_1.
      + right. intros [v1 H']. inversion H'. done.
    - right; intros [v1 H']; try done.
    - right; intros [v1 H']; try done.
  Qed.

  Definition process_proph (tid: proph_id) (pvs : list (val * val)) 
    : option (nat * option nat) :=
    match list_find (λ x, x.2 = #tid) pvs with
      None => None
    | Some (i, _) => 
      let ls := take i pvs in
      match list_find (is_snd true) ls with
        None => Some (i, None)
      | Some (j, _) => Some (i, Some j) end end.
  
  Lemma process_proph_case1 tid pvs :
    process_proph tid pvs = None → Forall (λ x, x.2 ≠ #tid) pvs.
  Proof.
    rewrite /process_proph. destruct (list_find _ pvs) eqn: H'.
    { destruct p. destruct (list_find (is_snd true)); try destruct p0; try done. }
    intros _. by apply list_find_None in H'.
  Qed.

  Lemma process_proph_case2 tid pvs i :
    process_proph tid pvs = Some (i, None) → 
      (∃ x, pvs !! i = Some (x, #tid))
      ∧ (∀ j, j < i → (pvs !!! j).2 ≠ #tid)
      ∧ (∀ j, j < i → ¬ (is_snd true (pvs !!! j))).
  Proof.
    rewrite /process_proph. destruct (list_find _ pvs) eqn: H'; try done.
    destruct p as [i' x]. destruct (list_find (is_snd true) _) eqn: H''. 
    { destruct p. try done. }
    intros [=]. subst i'. apply list_find_None in H''. apply list_find_Some in H'.
    destruct x as [x1 x2]. rewrite /= in H'. destruct H' as [Hi [Hx2 Hj]].
    subst x2. split; last split.
    - by exists x1.
    - intros j Hji. assert (is_Some (pvs !! j)) as [[xj1 xj2] Hpvsj]. 
      { rewrite lookup_lt_is_Some. apply mk_is_Some in Hi. 
        rewrite lookup_lt_is_Some in Hi. lia. }
      pose proof Hj j (xj1, xj2) as H'. assert (H1' := Hpvsj).
      apply list_lookup_total_correct in H1'. rewrite H1'. by apply H'.
    - intros j Hji. assert (is_Some (pvs !! j)) as [[xj1 xj2] Hpvsj]. 
      { rewrite lookup_lt_is_Some. apply mk_is_Some in Hi. 
        rewrite lookup_lt_is_Some in Hi. lia. }
      rewrite Forall_lookup in H''. pose proof H'' j (xj1, xj2) as H''.
      rewrite lookup_take in H''; try done. assert (H' := Hpvsj).
      apply list_lookup_total_correct in H'. rewrite H'. by apply H''.
  Qed.

  Lemma process_proph_case3 tid pvs i j :
    process_proph tid pvs = Some (i, Some j) → 
      (∃ x, pvs !! i = Some (x, #tid))
      ∧ (∀ j', j' < i → (pvs !!! j').2 ≠ #tid)
      ∧ (j < i) ∧ (is_snd true (pvs !!! j)).
  Proof.
    rewrite /process_proph. destruct (list_find _ pvs) eqn: H'; try done.
    destruct p as [i' x]. destruct (list_find (is_snd true) _) eqn: H''; last done.
    destruct p as [j' y]. intros [=]. subst i' j'. 
    apply list_find_Some in H''. apply list_find_Some in H'.
    destruct x as [x1 x2]. rewrite /= in H'. destruct H' as [Hi [Hx2 Hj]].
    destruct H'' as [Hy [Hy' Hj']]. subst x2. 
    assert (j < i) as j_lt_i. { apply mk_is_Some, lookup_lt_is_Some in Hy.
      apply mk_is_Some, lookup_lt_is_Some in Hi. rewrite take_length in Hy. lia. }
    assert (is_Some (pvs !! j)) as [[xj1 xj2] Hpvsj]. 
    { rewrite lookup_lt_is_Some. apply mk_is_Some, lookup_lt_is_Some in Hi. lia. }
    split; last split; last split; try done.
    - by exists x1.
    - intros j' Hji. assert (is_Some (pvs !! j')) as [[xj1' xj2'] Hpvsj']. 
      { rewrite lookup_lt_is_Some. apply mk_is_Some in Hi. 
        rewrite lookup_lt_is_Some in Hi. lia. }
      pose proof Hj j' (xj1', xj2') Hpvsj' Hji as H'.
      apply list_lookup_total_correct in Hpvsj'. by rewrite Hpvsj'.
    - rewrite lookup_take in Hy; try done. apply list_lookup_total_correct in Hy.
      by rewrite Hy.
  Qed.

End HINDSIGHT_DEFS.


