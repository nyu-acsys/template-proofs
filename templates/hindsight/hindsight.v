From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants fancy_updates.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
From flows Require Export flows one_shot_proph typed_proph gset_seq.

Module Type DATA_STRUCTURE.
  
  Parameter init : val.
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
  
  Parameter dsG : gFunctors → Set.
  (* Parameter test : heapGS dsΣ. *)
  (* Print heapGS_gen. *)
  (* Parameter subG_dsΣ : ∀ Σ, subG dsΣ Σ → dsG Σ. *)


  (* Context `{!heapGS Σ, !dsG Σ}. *)
   
  Parameter ds_inv : ∀ Σ, heapGS Σ → dsG Σ → Node → gmap nat snapshot -> 
    nat -> snapshot -> iProp Σ.

  Parameter local_pre : Op -> Prop.

End DATA_STRUCTURE.


Module Type HINDSIGHT_DEFS.
  Declare Module DS : DATA_STRUCTURE.
  Import DS.
    
  (* RAs used in proof *)

  Definition auth_natUR := authUR $ max_natUR.
  Definition frac_absTR := dfrac_agreeR $ absTUR.
  Definition agree_snapshotR := agreeR $ snapshotUR.
  Definition historyR := gmapUR nat $ snapshotUR.
  Definition auth_historyR := authR $ gmapUR nat $ agree_snapshotR.
  Definition frac_historyR := dfrac_agreeR $ historyR.
  Definition tokenUR := exclR unitO.
  Definition set_tidR := authR (gsetUR proph_id). 
  Definition sync_mapR := authUR $ gmapUR proph_id $ agreeR $ gnameO.
  Definition ts_mapR := authUR $ gmapUR proph_id $ agreeR $ natO.
  Definition upd_fracR := fracR. 

  Class hsG Σ := HS {
                  hsG_auth_natG :: inG Σ auth_natUR;
                  hsG_agree_snapshotG :: inG Σ agree_snapshotR;
                  hsG_frac_absTG :: inG Σ frac_absTR;
                  hsG_historyG :: inG Σ historyR;
                  hsG_auth_historyG :: inG Σ auth_historyR;
                  hsG_tokenG :: inG Σ tokenUR;
                  hsG_frac_historyG :: inG Σ frac_historyR;
                  hsG_set_tidG :: inG Σ set_tidR;
                  hsG_sync_mapG :: inG Σ sync_mapR;
                  hsG_ts_mapG :: inG Σ ts_mapR;
                  hsG_upd_fracG :: inG Σ upd_fracR
                 }.
               
  Definition hsΣ : gFunctors :=
    #[ GFunctor auth_natUR; GFunctor agree_snapshotR;
       GFunctor frac_absTR; GFunctor historyR;
       GFunctor auth_historyR; GFunctor tokenUR; 
       GFunctor frac_historyR; GFunctor set_tidR;
       GFunctor sync_mapR; GFunctor ts_mapR; GFunctor upd_fracR].
  
  Global Instance subG_hsΣ {Σ} : subG hsΣ Σ → hsG Σ.
  Proof. solve_inG. Qed.

  Implicit Types M : gmap nat snapshot.
  Implicit Types T : nat.
  
  Global Definition cntrN N := N .@ "cntr".
  Global Definition threadN N := N .@ "thread".
  
  Definition hist (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ) 
    γ_t γ_m M T : iProp Σ :=
    ∃ (M': gmap nat (agreeR (_))),
      own γ_t (● MaxNat T) ∗ own γ_m (● M')
    ∗ ⌜dom M = gset_seq 0 T⌝
    ∗ ⌜∀ t s, M' !! t ≡ Some (to_agree s) ↔ M !! t = Some s⌝
    ∗ ⌜∀ t, t < T → (M !!! t) ≠ (M !!! (t+1)%nat)⌝.

  Definition dsRep (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    γ_r (a: absTUR) : iProp Σ := 
    own γ_r (to_frac_agree (1/2) a).

  Definition dsRepI (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
  γ_r (a: absTUR) : iProp Σ := 
    own γ_r (to_frac_agree (1/2) a).
    
  (** Helping Inv **)
  
  Definition au (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    N γ_r op (Q : val → iProp Σ) := 
    (AU <{ ∃∃ a, dsRep Σ H' H'' H''' γ_r a }> 
          @ ⊤ ∖ (↑N), ∅
        <{ ∀∀ a' res, dsRep Σ H' H'' H''' γ_r a' 
          ∗ ⌜seq_spec op a a' res⌝, COMM Q #res }>)%I.

  Definition past_lin (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    M T op res t0 : iProp Σ :=
    ⌜∃ t, t0 ≤ t ≤ T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! t)) res⌝.

  Definition past_state (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    γ_m (t0: nat) (s: snapshot) : iProp Σ :=
    ∃ t, ⌜t0 ≤ t⌝ ∗ own γ_m (◯ {[t := to_agree s]}).
  
  Definition past_lin_witness (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    γ_m op res t0 : iProp Σ :=
    ∃ s, past_state Σ H' H'' H''' γ_m t0 s ∗ ⌜seq_spec op (abs s) (abs s) res⌝.

  Definition Token (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ) 
    γ : iProp Σ := own γ (Excl ()).
  
  Definition Pending (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    (P: iProp Σ) M T op vp t0 : iProp Σ := 
      P ∗ £1 ∗ ¬ past_lin Σ H' H'' H''' M T op vp t0.

  Definition Done (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    γ_tk (Q: val → iProp Σ) M T op (vp: resT) t0 : iProp Σ := 
    (Q #vp ∨ Token Σ H' H'' H''' γ_tk) ∗ past_lin Σ H' H'' H''' M T op vp t0.
  
  Definition State (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    γ_sy γ_tk P Q M T op vp t0 : iProp Σ :=
        own γ_sy (to_frac_agree (1/2) M)
      ∗ ⌜dom M = gset_seq 0 T⌝ ∗ ⌜t0 ≤ T⌝
      ∗ (Pending Σ H' H'' H''' P M T op vp t0 ∨ Done Σ H' H'' H''' γ_tk Q M T op vp t0).

  Definition thread_start (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    γ_t γ_mt t_id t0 : iProp Σ := 
    own γ_mt (◯ {[t_id := to_agree t0]}) ∗ own γ_t (◯ MaxNat t0).

  Definition thread_sync (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    γ_msy t_id γ_sy : iProp Σ := 
      own γ_msy (◯ {[t_id := to_agree γ_sy]}).
  
  Definition Reg (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ) 
    N γ_t γ_r γ_mt γ_msy t_id M : iProp Σ :=
    ∃ γ_tk γ_sy Q op vp t0, 
        thread_start Σ H' H'' H''' γ_t γ_mt t_id t0
      ∗ own γ_msy (◯ {[t_id := to_agree γ_sy]})
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ inv (threadN N) 
        (∃ M T, State Σ H' H'' H''' γ_sy γ_tk (au Σ H' H'' H''' N γ_r op Q) Q M T op vp t0).
    
  Definition helping_inv (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    (N: namespace) γ_t γ_r γ_mt γ_msy M : iProp Σ :=
    ∃ (Mt: gmap proph_id (agreeR nat)) (Msy: gmap proph_id (agreeR gname)),
        own γ_mt (● Mt) 
      ∗ own γ_msy (● Msy) 
      ∗ ⌜dom Msy ⊆ dom Mt⌝ 
      ∗ ([∗ set] t_id ∈ dom Mt, ∃ vtid, proph1 t_id vtid)
      ∗ ([∗ set] t_id ∈ dom Msy, Reg Σ H' H'' H''' N γ_t γ_r γ_mt γ_msy t_id M).

  Definition main_inv (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    N γ_t γ_r γ_m γ_mt γ_msy (r: loc) : iProp Σ :=
    inv (cntrN N)
    (∃ M T (s: snapshot),
      dsRepI Σ H' H'' H''' γ_r (abs s) ∗ ⌜M !!! T ≡ s⌝
    ∗ hist Σ H' H'' H''' γ_t γ_m M T
    ∗ helping_inv Σ H' H'' H''' N γ_t γ_r γ_mt γ_msy M
    ∗ ds_inv Σ H' H'' r M T s).

  Definition update_helping_protocol (Σ : gFunctors) (H' : heapGS Σ) (H'' : dsG Σ) (H''' : hsG Σ)
    N γ_t γ_r γ_mt γ_msy: iProp Σ :=
    ∀ M T s, 
    ⌜dom M = gset_seq 0 T⌝ -∗   
    dsRep Σ H' H'' H''' γ_r (abs s) -∗
    helping_inv Σ H' H'' H''' N γ_t γ_r γ_mt γ_msy M ={⊤ ∖ ↑cntrN N}=∗
        helping_inv Σ H' H'' H''' N γ_t γ_r γ_mt γ_msy (<[T+1 := s]> M) 
        ∗ dsRep Σ H' H'' H''' γ_r (abs s).

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

  Inductive proph_case := contra | upd | no_upd.

  Definition process_proph (tid: proph_id) (pvs : list (val * val)) : proph_case :=
    match list_find (λ x, x.2 = #tid) pvs with
      None => contra
    | Some (i, _) => 
      let ls := take i pvs in
      match list_find (is_snd true) ls with
        None => no_upd
      | Some (j, _) => upd end end.

  (* Useful Lemmas *)

  Lemma process_proph_contra tid pvs :
    process_proph tid pvs = contra → Forall (λ x, x.2 ≠ #tid) pvs.
  Proof. 
    rewrite /process_proph. destruct (list_find _ pvs) eqn: H'.
    { destruct p. destruct (list_find (is_snd true)); try destruct p0; try done. }
    intros _. by apply list_find_None in H'.  
  Qed.

  Lemma process_proph_no_upd tid pvs :
    process_proph tid pvs = no_upd → 
      ∃ i x, pvs !! i = Some (x, #tid)
            ∧ Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) (take i pvs).
  Proof. 
    rewrite /process_proph. destruct (list_find _ pvs) eqn: H'; try done.
    destruct p as [i x]. destruct (list_find (is_snd true) _) eqn: H''. 
    { destruct p. try done. }
    intros [=]. apply list_find_None in H''. apply list_find_Some in H'.
    destruct x as [x1 x2]. rewrite /= in H'. destruct H' as [Hi [Hx2 Hj]].
    subst x2. exists i, x1. split; try done. apply List.Forall_and; try done.
    rewrite Forall_lookup. apply mk_is_Some, lookup_lt_is_Some in Hi.
    intros i' x' Hx'. assert (i' < i). apply mk_is_Some, lookup_lt_is_Some in Hx'.
    rewrite take_length in Hx'. lia.
    apply (Hj i' x'); try done. rewrite lookup_take in Hx'; try done.
  Qed.

  Lemma process_proph_upd tid pvs :
    process_proph tid pvs = upd →
      ∃ i x j,
        (j < i) ∧ pvs !! i = Some (x, #tid) ∧ (is_snd true (pvs !!! j))
      ∧ Forall (λ x, x.2 ≠ #tid) (take i pvs)
      ∧ Forall (λ x, ¬ is_snd true x) (take j pvs).
  Proof. 
    rewrite /process_proph. destruct (list_find _ pvs) eqn: H'; try done.
    destruct p as [i x]. destruct (list_find (is_snd true) _) eqn: H''; last done.
    destruct p as [j y]. intros _.
    apply list_find_Some in H''. apply list_find_Some in H'.
    destruct x as [x1 x2]. rewrite /= in H'. destruct H' as [Hi [Hx2 Hj]].
    destruct H'' as [Hy [Hy' Hj']]. subst x2. 
    assert (j < i) as j_lt_i. { apply mk_is_Some, lookup_lt_is_Some in Hy.
      apply mk_is_Some, lookup_lt_is_Some in Hi. rewrite take_length in Hy. lia. }
    assert (is_Some (pvs !! j)) as [[xj1 xj2] Hpvsj]. 
    { rewrite lookup_lt_is_Some. apply mk_is_Some, lookup_lt_is_Some in Hi. lia. }
    exists i, x1, j. split; last split; last split; last split; try done.
    - rewrite lookup_take in Hy; try done. apply list_lookup_total_correct in Hy.
      by rewrite Hy.
    - rewrite Forall_lookup. intros i' x' Hx'. 
      assert (i' < i). apply mk_is_Some, lookup_lt_is_Some in Hx'.
      rewrite take_length in Hx'. lia.
      apply (Hj i' x'). rewrite lookup_take in Hx'. all: done.
    - rewrite Forall_lookup. intros i' x' Hx'. 
      assert (i' < i). apply mk_is_Some, lookup_lt_is_Some in Hx'.
      rewrite take_length in Hx'. lia.
      assert (i' < j). apply mk_is_Some, lookup_lt_is_Some in Hx'.
      rewrite take_length in Hx'. lia.
      assert (take i pvs !! i' = take j pvs !! i') as H'. 
      rewrite !lookup_take; try done. rewrite -H' in Hx'.
      pose proof (Hj' i' x' Hx' H0) as H''. done.
  Qed.

  Lemma process_proph_contra_rec tid prf pvs :
    process_proph tid (prf ++ pvs) = contra →
    Forall (λ x, x.2 ≠ #tid) prf →
        process_proph tid pvs = contra.
  Proof.
    intros Hp Hprf. apply process_proph_contra in Hp. 
    rewrite /process_proph. destruct (list_find _ pvs) eqn: H'; try done.
    destruct p as [i x]. apply list_find_Some in H'.
    apply Forall_app in Hp. destruct Hp as [_ Hp].
    destruct H' as [H' [H'' _]]. rewrite Forall_lookup in Hp.
    pose proof Hp i x H' as H1'. by exfalso.
  Qed.

  Lemma process_proph_no_upd_rec tid prf pvs :
    process_proph tid (prf ++ pvs) = no_upd →
    Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf →
        process_proph tid pvs = no_upd.
  Proof. 
    intros Hp Hprf. apply process_proph_no_upd in Hp.
    destruct Hp as [i [x [Hxtid Htake]]]. apply Forall_and in Htake.
    destruct Htake as [Htake1 Htake2]. rewrite /process_proph.
    assert (prf !! i = None) as Prf_i.
    { destruct (prf !! i) eqn: H'; try done. exfalso.
      rewrite (lookup_app_l_Some prf pvs _ _ H') in Hxtid. inversion Hxtid.
      subst p. rewrite Forall_lookup in Hprf.
      pose proof Hprf _ _ H' as H''. destruct H'' as [_ H'']. done. }
    assert (pvs !! (i - length prf) = Some (x, #tid)) as Pvs_i'.
    { by rewrite lookup_app Prf_i in Hxtid. }
    destruct (list_find _ pvs) eqn: H'; try done; last first.
    { exfalso. apply list_find_None in H'. rewrite Forall_lookup in H'.
      pose proof H' _ _ Pvs_i' as H''. done. }
    destruct p as [i' x']. apply list_find_Some in H'.
    destruct H' as (Def_x' & Hx' & Hjtid).
    assert (i' = i - length prf) as ->.
    { assert (not (i - length prf < i')).
      { intros H'. pose proof Hjtid _ _ Pvs_i' H' as H''. done. }
      assert (not (i' < i - length prf)).
      { intros H'. assert (i' + length prf < i) as H'' by lia.
        assert (take i (prf ++ pvs) !! (i' + length prf) = Some x') as H1''.
        rewrite lookup_take; try done. rewrite lookup_app_r; last by lia.
        by assert (i' + length prf - length prf = i') as -> by lia.
        rewrite Forall_lookup in Htake2. pose proof Htake2 _ _ H1'' as H2'. done. }
      lia. }
    destruct (list_find _ _) eqn: H'; try done. destruct p as [i' y']. 
    exfalso. apply list_find_Some in H'. destruct H' as [Hi' [Hy' _]].
    apply lookup_take_Some in Hi'. destruct Hi' as [Hi' H'].
    assert (i' + length prf < i) as H'' by lia.
    assert (take i (prf ++ pvs) !! (i' + length prf) = Some y') as H1''.
    rewrite lookup_take; try done. rewrite lookup_app_r; last by lia.
    by assert (i' + length prf - length prf = i') as -> by lia.
    rewrite Forall_lookup in Htake1. pose proof Htake1 _ _ H1'' as H2'. done. 
  Qed.

  Lemma process_proph_upd_rec tid prf pvs :
    process_proph tid (prf ++ pvs) = upd →
    Forall (λ x, ¬ is_snd true x ∧ x.2 ≠ #tid) prf →
        process_proph tid pvs = upd.
  Proof. 
    intros Hp Hprf. apply process_proph_upd in Hp.
    destruct Hp as [i [x [j [Hji [Hxtid [Hj [Htakei Htakej]]]]]]].
    rewrite Forall_and in Hprf. destruct Hprf as [Hprf1 Hprf2].
    rewrite /process_proph.
    assert (prf !! i = None) as Prf_i.
    { destruct (prf !! i) eqn: H'; try done. exfalso.
      rewrite (lookup_app_l_Some prf pvs _ _ H') in Hxtid. inversion Hxtid.
      subst p. rewrite Forall_lookup in Hprf2.
      pose proof Hprf2 _ _ H' as H''. done. }
    assert (pvs !! (i - length prf) = Some (x, #tid)) as Pvs_i'.
    { by rewrite lookup_app Prf_i in Hxtid. }
    assert (prf !! j = None) as Prf_j.
    { destruct (prf !! j) eqn: H'; try done. exfalso.
      pose proof (lookup_app_l_Some prf pvs _ _ H') as H''.
      rewrite Forall_lookup in Hprf1. pose proof Hprf1 _ _ H' as Hprf.
      rewrite list_lookup_total_alt H'' /= in Hj. done. }
    assert (is_Some((prf ++ pvs) !! j)) as [y Hy].
    { rewrite lookup_lt_is_Some. apply mk_is_Some in Hxtid.
      rewrite lookup_lt_is_Some in Hxtid. lia. }
    assert ((prf ++ pvs) !! j = pvs !! (j - length prf)) as Pvs_j.
    { by rewrite lookup_app Prf_j. }
    destruct (list_find _ pvs) eqn: H'; try done; last first.
    { exfalso. apply list_find_None in H'. rewrite Forall_lookup in H'.
      pose proof H' _ _ Pvs_i' as H''. done. }
    destruct p as [i' x']. apply list_find_Some in H'.
    destruct H' as (Def_x' & Hx' & Hjtid).
    assert (i' = i - length prf) as ->.
    { assert (not (i - length prf < i')).
      { intros H'. pose proof Hjtid _ _ Pvs_i' H' as H''. done. }
      assert (not (i' < i - length prf)).
      { intros H'. assert (i' + length prf < i) as H'' by lia.
        assert (take i (prf ++ pvs) !! (i' + length prf) = Some x') as H1''.
        rewrite lookup_take; try done. rewrite lookup_app_r; last by lia.
        by assert (i' + length prf - length prf = i') as -> by lia.
        rewrite Forall_lookup in Htakei. pose proof Htakei _ _ H1'' as H2'. done. }
      lia. }
    destruct (list_find _ _) eqn: H'; first by (destruct p).
    exfalso. apply list_find_None in H'. rewrite Forall_lookup in H'.
    assert (take (i - length prf) pvs !! (j - length prf) = Some y) as H''.
    { rewrite lookup_take. by rewrite lookup_app Prf_j in Hy. 
      apply lookup_ge_None in Prf_j. lia. }
    rewrite list_lookup_total_alt Hy /= in Hj.
    pose proof H' _ _ H'' as H1'. done.
  Qed.

  Lemma history_sync (Σ : gFunctors) (Hg1 : heapGS Σ) (Hg2 : dsG Σ) (Hg3 : hsG Σ) 
    γ_m (M: gmap nat (agreeR (ucmra_ofeO snapshotUR))) (s: snapshot) t: 
    own γ_m (● M) -∗ own γ_m (◯ {[t := to_agree s]}) -∗
      ⌜M !! t ≡ Some (to_agree s)⌝.
  Proof.
    iIntros "HM Hs". iCombine "HM" "Hs" as "H'".
    iPoseProof (own_valid with "H'") as "Hv".
    iDestruct "Hv" as %Hv.
    rewrite auth_both_valid_discrete in Hv.
    destruct Hv as [H' Hv].
    rewrite lookup_included in H'.
    pose proof H' t as H'.
    rewrite lookup_insert in H'.
    unfold included in H'.
    iPureIntro.
    destruct H' as [z H'].
    destruct z as [z | ].
    - rewrite /op /cmra_op /= in H'. 
      pose proof lookup_valid_Some M t (to_agree s ⋅ z) Hv H' as H''.
      apply agree_op_inv in H''.
      rewrite <-H'' in H'.
      by rewrite agree_idemp in H'.
    - by rewrite /op /cmra_op /= in H'. 
  Qed.

  Lemma temporal_interpolation_refl_trans `{R: relation A}
    (M : gmap nat snapshot) (t0 T: nat) (F: snapshot → A) :
      Reflexive R → Transitive R → 
      (∀ t, t0 ≤ t < T → R (F (M !!! t)) (F (M !!! (t+1)%nat))) →
        (∀ t1 t2, t0 ≤ t1 ≤ t2 ≤ T → R (F (M !!! t1)) (F (M !!! t2))).
  Proof.
    intros R_refl R_trans Hcons. induction t1.
    - induction t2.
      + intros; try done.
      + intros Ht2.
        assert (R (F (M !!! 0)) (F (M !!! t2))) as H'.
        { apply IHt2. lia. }
        assert (R (F (M !!! t2)) (F (M !!! S t2))) as H''.
        { assert (t2 + 1 = S t2) as <- by lia.
          apply Hcons. lia. }
        apply (R_trans _ _ _ H' H''); try done.
    - induction t2.
      + intros H'. exfalso; lia.
      + intros Ht1.
        destruct (decide (S t1 <= t2)).
        * assert (R (F (M !!! S t1)) (F (M !!! t2))) as H'.
          { apply IHt2; try lia. }
          assert (R (F (M !!! t2)) (F (M !!! S t2))) as H''.
          { assert (t2 + 1 = S t2) as <- by lia. 
            apply Hcons. split; try lia. }
          apply (R_trans _ _ _ H' H''); try done.
        * assert (t1 = t2) as -> by lia.
          apply R_refl.
  Qed.

  Lemma history_dom Σ Hg1 Hg2 Hg3 t γ_t γ_m M T :
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
      ⌜t ∈ dom M ↔ 0 ≤ t ≤ T⌝.
  Proof.
    iIntros "Hist".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    by rewrite Dom_M elem_of_gset_seq.
  Qed. 

  Lemma snapshot_create Σ Hg1 Hg2 Hg3 t t0 γ_t γ_m M T:
    ⌜t0 ≤ t ≤ T⌝ -∗ 
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
      |==> past_state Σ Hg1 Hg2 Hg3 γ_m t0 (M !!! t) ∗ hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T.
  Proof.
    iIntros "%Ht Hist".
    iPoseProof (history_dom Σ Hg1 Hg2 Hg3 t with "Hist") as "%Hdom".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    assert (0 ≤ t ≤ T) as Dom_t by lia. apply Hdom in Dom_t.
    apply elem_of_dom in Dom_t. destruct Dom_t as [s Dom_t].
    apply M_eq in Dom_t. 
    iPoseProof (own_update _ (● M') (● M' ⋅ ◯ {[t := to_agree s]}) with "HM'") 
      as ">(HM' & #Ht)". 
    { apply auth_update_alloc, local_update_unital_discrete. 
      intros z Hm Hz. split; try done. rewrite left_id in Hz. rewrite -Hz.
      apply map_equiv_iff. intros x. destruct (decide (x = t)) as [-> | Hxz].
      - rewrite lookup_op Dom_t lookup_insert. rewrite /op /cmra_op /=.
        by rewrite agree_idemp.
      - rewrite lookup_op lookup_insert_ne; try done. rewrite lookup_empty.
        rewrite /op /cmra_op /=. destruct (M' !! x) eqn:H'; rewrite H'; try done. }
    iModIntro. iFrame. iSplitR. iExists t. apply M_eq, lookup_total_correct in Dom_t.
    rewrite Dom_t. iFrame "%#". iPureIntro; lia. iExists M'. iFrame "∗%".
  Qed.

  Lemma snapshot_current Σ Hg1 Hg2 Hg3 γ_t γ_m γ_mt M T s tid t0:
    ⌜M !!! T ≡ s⌝ -∗ 
    thread_start Σ Hg1 Hg2 Hg3 γ_t γ_mt tid t0 -∗
    hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗ 
      |==> past_state Σ Hg1 Hg2 Hg3 γ_m t0 s ∗ hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T.
  Proof.
    iIntros "%Habs #(_&Ht0) Hist".
    iAssert (⌜t0 ≤ T⌝)%I as "%H'".
    { iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
      iPoseProof (own_valid_2 with "HT Ht0") as "%Hv".
      rewrite auth_both_valid_discrete max_nat_included /= in Hv.
      iPureIntro. apply Hv. }
    apply leibniz_equiv in Habs. rewrite -Habs.
    iPoseProof (snapshot_create with "[%] [$Hist]") as "H'"; try done.
  Qed.

  Lemma hist_upd Σ Hg1 Hg2 Hg3 γ_t γ_m M T s s':
  ⌜M !!! T ≡ s⌝ -∗
  ⌜s ≠ s'⌝ -∗ 
  hist Σ Hg1 Hg2 Hg3 γ_t γ_m M T -∗
    |==> hist Σ Hg1 Hg2 Hg3 γ_t γ_m (<[T+1:=s']> M) (T+1).
  Proof.
    iIntros "%Habs %Hs Hist".
    iDestruct "Hist" as (M')"(HT&HM'&%Dom_M&%M_eq&%M_neq)".
    iPoseProof (own_update _ (● MaxNat T) (● MaxNat (T+1)) with "HT") 
      as ">HT".
    { apply (auth_update_auth _ _ (MaxNat (T+1))), max_nat_local_update.
      simpl. lia. } 
    iPoseProof (own_update _ (● M') (● (<[T+1:= to_agree s']> M')) with "HM'") 
      as ">HM'". 
    { apply (auth_update_auth _ _ {[T+1 := to_agree s']}). 
      apply local_update_unital_discrete. intros z Hm Hz. rewrite left_id in Hz. 
      rewrite -Hz. split. 
      - apply insert_valid; try done.
      - assert (M' !! (T+1) = None) as Hmt. 
        { assert (T+1 ∉ dom M) as H'. rewrite Dom_M elem_of_gset_seq. lia.
          assert (T+1 ∉ dom M') as H''. intros H''. rewrite elem_of_dom in H''.
          destruct H'' as [x H'']. assert (M' !! (T+1) ≡ Some x) as H1'.
          rewrite H''. done. pose proof lookup_valid_Some _ _ _ Hm H1' as H1''.
          apply to_agree_uninj in H1''. destruct H1'' as [s'' H1''].
          rewrite -H1'' in H1'. apply M_eq in H1'. apply elem_of_dom_2 in H1'.
          set_solver. by rewrite not_elem_of_dom in H''. }
        apply map_equiv_iff. intros x. destruct (decide (x = T+1)) as [-> | Hxz].
        + rewrite lookup_op Hmt !lookup_insert /=. try done.
        + rewrite lookup_op !lookup_insert_ne; try done. rewrite lookup_empty.
          rewrite /op /cmra_op /=. destruct (M' !! x) eqn:H'; rewrite H'; try done. }
    iModIntro. iExists (<[T+1:= to_agree s']> M'). iFrame. iPureIntro. split; last split.
    - rewrite dom_insert_L Dom_M. rewrite gset_seq_union. clear; set_solver.
    - intros t s0. destruct (decide (t = T+1)) as [-> | Ht].
      + rewrite !lookup_insert. split. intros H'. inversion H'.
        apply to_agree_inj in H1. apply leibniz_equiv in H1. by rewrite H1.
        intros [=]. by subst s0.
      + rewrite !lookup_insert_ne; try done.
    - intros t. destruct (decide (t = T)) as [-> | Ht].
      + rewrite lookup_total_insert_ne. rewrite lookup_total_insert.
        apply leibniz_equiv in Habs. rewrite Habs. done. lia.
      + intros ?; rewrite !lookup_total_insert_ne; try lia. apply M_neq. lia.
  Qed.

End HINDSIGHT_DEFS.