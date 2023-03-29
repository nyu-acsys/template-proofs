(* Hindsight reasoning for search structures *)

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
Require Export one_shot_proph typed_proph.

Parameter dsOp : val.

Definition dsOp' : val :=
  λ: "OP" "r",     
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "v" := dsOp "OP" "r" in
    resolve_proph: "p" to: "v";;
    "v".

  
Section Hindsight.

  (* Data structure specific definitions *)

  Parameter Op : Type.
  Parameter Op_to_val : Op -> val.

  Parameter snapshotUR : ucmra.
  Definition snapshot := ucmra_car snapshotUR.

  Parameter absTUR : ucmra.
  Definition absT := ucmra_car absTUR.

  Parameter resT : Type.
  Parameter resT_to_base_lit : resT -> base_lit.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Parameter resT_from_val : val -> option resT.
  Parameter resT_to_val : resT -> val.
  Parameter resT_inj_prop : ∀ (r : resT), resT_from_val (resT_to_val r) = Some r.
  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.
  Parameter resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  
  Parameter seq_spec : Op -> absT -> absT -> resT -> Prop.
  Parameter abs : snapshot -> absT.
  Parameter updater_thread: Op -> resT -> bool.

  Parameter neg_seq_spec_dec : ∀ op c c' res, Decision (¬ seq_spec op c c' res).
  Parameter seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Parameter updater_thread_dec: ∀ op res b, Decision (updater_thread op res = b).  
  
  Parameter snapshotUR_discrete : CmraDiscrete snapshotUR.
  Parameter absTUR_discrete : CmraDiscrete absTUR.
  Parameter snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Parameter snapshot_inhabited : Inhabited snapshot.
  Parameter resT_inhabited : Inhabited resT.
  Parameter Op_inhabited : Inhabited Op.

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
  
  Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsG Σ.
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

  (** Proofs *)

  Parameter dsOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght template_inv op r γ_sy t_id t0,
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     dsOp (Op_to_val op) #r
                {{{ res, RET #res; past_lin_witness γ_m op res t0  }}}.


  Lemma dsOp'_spec N γ_s γ_t γ_m γ_td γ_ght template_inv op r :
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
              <<< ∀∀ a, dsRep γ_s a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N)
              <<< ∃∃ a' res, dsRep γ_s a' ∗ ⌜seq_spec op a a' res⌝, RET #res >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 resTTypedProph); first done.
    iIntros (vp p)"Hproph". wp_pures.
    iApply fupd_wp.
    iInv "HInv" as (M0 T0 s0) "(>HCntr & >%Habs0 & >Hist & Help & Templ)". 
    iDestruct "Help" as (R hγt)"(>HR & >Hγt 
                                & >Domm_hγt & Hstar_reg)".
    iAssert (▷ (⌜tid ∉ R⌝ 
            ∗ ([∗ set] t_id ∈ R, Reg N γ_t γ_s γ_ght t_id M0) 
            ∗ proph1 tid vtid))%I with "[Hstar_reg Htid]" 
            as "(>% & Hstar_reg & Htid)".
    { destruct (decide (tid ∈ R)); try done.
      - iEval (rewrite (big_sepS_elem_of_acc _ (R) tid); 
                            last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg & Hstar_reg')".
        iDestruct "Hreg" as (? ? ? ? ? ? ?)"(H' & _)".
        iAssert (▷ False)%I with "[H' Htid]" as "HF".
        iApply (proph1_exclusive tid with "[Htid]"); try done.
        iNext. iExFalso; try done.
      - iNext. iFrame. by iPureIntro. }
    rename H into tid_notin_R.
    
    iMod (own_update γ_td (● R) (● (R ∪ {[tid]})) with "[$HR]") as "HR".
    { apply (auth_update_auth _ _ (R ∪ {[tid]})).
      apply gset_local_update. set_solver. }
    iMod (own_update γ_td (● (R ∪ {[tid]})) (● (R ∪ {[tid]}) ⋅ ◯ {[tid]}) 
              with "[$HR]") as "(HR & #FP_t)".
    { apply (auth_update_dfrac_alloc _ (R ∪ {[tid]}) ({[tid]})).
      apply gset_included. clear; set_solver. }
    
    iMod (own_alloc (to_frac_agree (1) (M0))) 
            as (γ_sy)"Hfr_t". { try done. }        
    iEval (rewrite <-Qp.half_half) in "Hfr_t".      
    iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
    iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  
    
    iDestruct "Domm_hγt" as %Domm_hγt.
    set (<[ tid := to_agree (T0, γ_sy) ]> hγt) as hγt'.
    iDestruct (own_update _ _ 
      (● hγt' ⋅ ◯ {[ tid := to_agree (T0, γ_sy) ]})
             with "Hγt") as ">Hγt".
    { apply auth_update_alloc. 
      rewrite /hγt'.
      apply alloc_local_update; last done.
      rewrite <-Domm_hγt in tid_notin_R.
      by rewrite not_elem_of_dom in tid_notin_R. }
    iDestruct "Hγt" as "(Hγt & #Hreg_gh)".
  
    iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.
  
    assert (map_max M0 = T0) as M_max. { admit. }
    iAssert (own γ_t (◯ (MaxNat T0))) as "HfragT0".
    { admit. }
    
    assert (∀ op c res, Decision (updater_thread op res = true 
              ∨ (updater_thread op res = false 
                  ∧ ¬ seq_spec op c c res))) as Hdec.
    { intros. apply or_dec; try apply updater_thread_dec.
      apply and_dec; try apply updater_thread_dec.
      apply neg_seq_spec_dec. }
      
    destruct (decide (updater_thread op vp = true 
      ∨ (updater_thread op vp = false 
          ∧ ¬ seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))) 
      as [Hcase1 | Hcase2]; clear Hdec.
    - iMod (inv_alloc (threadN N) _
              (∃ M T, State γ_sy γ_tk (au N γ_s op Φ) Φ M T op vp T0) 
                                    with "[AU Hc Hreg_sy1]") as "#HthInv".
      { iNext. iExists M0, T0. iFrame "Hreg_sy1".
        iSplitR. { by iPureIntro. }
        iLeft. unfold Pending. iFrame.
        unfold past_lin.
        destruct Hcase1 as [H' | H'].
        - rewrite H'. iIntros "%Hpast". 
          destruct Hpast as [t [H'' _]]. lia.
        - destruct H' as [H1' H2'].
          rewrite H1'. iIntros "%Hpast". 
          destruct Hpast as [t [H' Hss]].
          assert (t = T0) as -> by lia. contradiction. }

      iModIntro. iSplitR "Hproph Token". iNext.
      iExists M0, T0, s0. iFrame "∗%".
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". }
      
      wp_apply dsOp_spec; try done.
      iIntros (res)"HpastW".
      wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }  
      wp_pures. iModIntro. iIntros "%vp_eq_res". subst vp.
       
      iApply fupd_wp.
      
      iInv "HthInv" as (M1_th T1_th)"(>Hth_sy & >% & Hth_or)".
      iInv "HInv" as (M1 T1 s1) "(>HCntr & >%Habs1 & >Hist & Help & Templ)".
      iDestruct "Help" as (R1 hγt1)"(>HR & >Hγt 
                                  & >Domm_hγt & Hstar_reg)".
      
      iAssert (⌜tid ∈ R1⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HR] [$FP_t]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro. set_solver. }
      rename H into tid_in_R1.
      
      iAssert (▷ (⌜M1_th = M1⌝ ∗ ⌜T1_th = T1⌝ 
               ∗ ([∗ set] t_id ∈ R1, Reg N γ_t γ_s γ_ght t_id M1)
               ∗ own (γ_sy) (to_frac_agree (1 / 2) M1_th) ))%I
                with "[Hstar_reg Hth_sy]" as "(>% & >% & Hstar_reg & >Hth_sy)". 
      { 
        iEval (rewrite (big_sepS_elem_of_acc _ (R1) tid); 
                                last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg_t & Hstar_reg')".
        iDestruct "Hreg_t" as (γ_tk' γ_sy' Q' op' vp' t0' vtid')
                          "(Hreg_proph & >Hreg_gh' & >Hreg_sy & Ht_reg')".

        iDestruct "Hreg_gh'" as "(Hreg_gh' & #?)".
        iCombine "Hreg_gh" "Hreg_gh'" as "H".
        iPoseProof (own_valid with "H") as "Valid".
        iDestruct "Valid" as %Valid.
        rewrite auth_frag_valid in Valid.
        apply singleton_valid in Valid.
        apply to_agree_op_inv in Valid.
        apply leibniz_equiv in Valid.
        injection Valid; intros <- <-.
                  
        iAssert (⌜M1_th = M1 ∧ T1_th = T1⌝)%I as "(% & %)".
        { iPoseProof (own_valid_2 _ _ _ with "[$Hth_sy] [$Hreg_sy]") 
              as "V_M".
          iDestruct "V_M" as %V_M.
          apply frac_agree_op_valid in V_M. destruct V_M as [_ V_M].
          iPureIntro. split; first by apply leibniz_equiv. admit. } 
        subst M1_th T1_th.
          
        iSplitR. { by iPureIntro. } 
        iSplitR. iNext; by iPureIntro.
        iSplitR "Hth_sy". iApply "Hstar_reg'".
        iNext. iExists γ_tk', γ_sy, Q', op', vp', T0, vtid'.
        iFrame "∗#". by iNext. 
      } subst M1_th T1_th.
      
      iEval (unfold past_lin_witness) in "HpastW".
      (* iEval (rewrite Upd_thr) in "HpastW".*)

      iDestruct "Hth_or" as "[Hth_or | Hth_or]".
      { iDestruct "Hth_or" as "(AU & Hc & >%HPending)".
        destruct (decide (updater_thread op res = true))
          as [Hdec | Hdec]. 
        - rewrite Hdec. rewrite Hdec in HPending.
          iExFalso. admit. 
        - destruct (decide (updater_thread op res = false)) as [Hdec' | Hdec'].
          + rewrite Hdec'. rewrite Hdec' in HPending. 
            iExFalso. admit.
          + admit. }  
      
      iDestruct "Hth_or" as "(Hth_or & Hpast)".  
      iDestruct "Hth_or" as "[Hth_or | >Hth_or]"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Hth_or]") as "%".
        exfalso; try done. }
        
      iModIntro. iSplitR "Hth_or Hth_sy Token Hpast".
      iExists M1, T1, s1; iFrame "∗%".
      iNext. iExists R1, hγt1; iFrame.     

      iModIntro. iSplitL "Token Hth_sy Hpast".
      iNext. iExists M1, T1. iFrame "Hth_sy". 
      iSplitR. by iPureIntro. iRight. iFrame "∗%".
      by subst T1.
      
      iModIntro. by wp_pures.
    - assert (updater_thread op vp = false 
        ∧ seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp) as [Upd_thr Hss]. 
      { clear -Hcase2. destruct (updater_thread op vp); split.
        - exfalso; apply Hcase2. left; try done.
        - exfalso; apply Hcase2. left; try done. 
        - done. 
        - assert (Decision (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp)) as H'.
          { apply seq_spec_dec. }
          destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp));
            try done. 
          exfalso. apply Hcase2. right.
          split; try done. } 
      iMod "AU" as (c) "[Cntr [_ Hcomm]]".
      iAssert (⌜c = abs s0⌝)%I as "%". { admit. } subst c. 
      iSpecialize ("Hcomm" $! (abs s0) vp). 
      iMod ("Hcomm" with "[Cntr]") as "HΦ".
      { iFrame. rewrite Habs0 in Hss. by iPureIntro. }
   
      iAssert (past_lin M0 T0 op vp T0)%I as "Hpast".
      { iPureIntro. rewrite Upd_thr. exists T0.
        split; try done. }
        
      iMod (inv_alloc (threadN N) _
            (∃ M T, State γ_sy γ_tk (au N γ_s op Φ) Φ M T op vp T0) 
                                  with "[Hreg_sy1 Token]") as "#HthInv".
      { iNext. iExists M0, T0. iFrame "Hreg_sy1".
        iSplitR. by iPureIntro.
        iRight. unfold Done. iFrame "Hpast".
        by iRight. }
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". }
  
      
      iModIntro. iSplitR "Hproph HΦ". iNext.
      iExists M0, T0, s0.  iFrame "∗%".
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                by (clear -tid_notin_R; set_solver).
      by rewrite H'.  
        
      iModIntro.
      wp_apply dsOp_spec; try done.
      iIntros (res)"HpastW". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }    
      wp_pures. iModIntro. iIntros "->".
      wp_pures. iModIntro. done. 
  Admitted.
End Hindsight.
