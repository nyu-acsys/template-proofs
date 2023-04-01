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
Require Export multiset_flows keyset_ra.


Module Type ABSTRACT_DATA_TYPE.
  
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
  Parameter resT_inj_prop : ∀ (r : resT), resT_from_val (resT_to_val r) = Some r.
  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.
  Parameter resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  
  Parameter seq_spec : Op -> absT -> absT -> resT -> Prop.
  Parameter seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Parameter updater_thread: Op -> resT -> bool.
  Parameter updater_thread_dec: ∀ op res b, Decision (updater_thread op res = b).

  Parameter Op_inhabited : Inhabited Op.
  Parameter absTUR_discrete : CmraDiscrete absTUR.
  Parameter resT_inhabited : Inhabited resT.

End ABSTRACT_DATA_TYPE.

Module Type DATA_STRUCTURE (ADT: ABSTRACT_DATA_TYPE).
  Import ADT.

  Parameter snapshotUR : ucmra.
  Definition snapshot := ucmra_car snapshotUR.
  
  Parameter abs : snapshot -> absT.
  
  Parameter snapshotUR_discrete : CmraDiscrete snapshotUR.
  
  Parameter snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Parameter snapshot_inhabited : Inhabited snapshot.

End DATA_STRUCTURE.  


Module HINDSIGHT_DEFS (ADT: ABSTRACT_DATA_TYPE) (DS : DATA_STRUCTURE ADT).
  Import ADT DS.
  
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

Module Type HINDSIGHT_SPEC (ADT: ABSTRACT_DATA_TYPE) (DS : DATA_STRUCTURE ADT).
  Module DEFS := HINDSIGHT_DEFS ADT DS.
  Import ADT DS DEFS.

  Parameter dsOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght op (r: Node) template_inv γ_sy t_id t0,
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     dsOp (Op_to_val op) #r
                {{{ res, RET #res; past_lin_witness γ_m op res t0  }}}.

End HINDSIGHT_SPEC.

Module CLIENT_SPEC (ADT: ABSTRACT_DATA_TYPE) (DS : DATA_STRUCTURE ADT) 
  (HS: HINDSIGHT_SPEC ADT DS).
  (* Module DEFS := HINDSIGHT_DEFS ADT DS. *)
  Import ADT DS HS DEFS.

  Definition dsOp' : val :=
    λ: "OP" "r",     
      let: "t_id" := NewProph in
      let: "p" := NewProph in
      let: "v" := dsOp "OP" "r" in
      resolve_proph: "p" to: "v";;
      "v".
        
  (** Proofs *)

  Lemma dsOp'_spec N γ_s γ_t γ_m γ_td γ_ght template_inv op r :
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
              <<< ∀∀ a, dsRep γ_s a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N)
              <<< ∃∃ a' res, dsRep γ_s a' ∗ ⌜seq_spec op a a' res⌝, RET #res >>>.
  Proof.
(*  
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
    
    assert (∀ op c c' res, Decision (¬ seq_spec op c c' res)) as neg_seq_spec_dec.
    { intros; apply not_dec. apply seq_spec_dec. }
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
*)
  Admitted.
  
End CLIENT_SPEC.

Module SEARCH_STRUCTURE : ABSTRACT_DATA_TYPE with Definition absTUR := gsetUR nat.

  Parameter search : val.
  Parameter insert : val.
  Parameter delete : val.

  Definition dsOp : val :=
  λ: "OP" "r" "k",     
    if: "OP" = #0 
    then search "r" "k"
    else if: "OP" = #1 
    then insert "r" "k"
    else delete "r" "k".

  (* Definition K := Z. *)
  Inductive Opp := searchOp : nat → Opp | insertOp : nat → Opp | deleteOp : nat → Opp.
  Definition Op := Opp.

  Definition Op_to_val (op: Op) : val :=
    match op with
    | searchOp _ => #0
    | insertOp _ => #1
    | deleteOp _ => #2 
    end.
    
  Definition absTUR := gsetUR nat.
  Definition absT := ucmra_car absTUR.

  Definition resT := bool.
  Definition resT_to_base_lit (b: resT) : base_lit := LitBool b.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Definition resT_from_val (v : val) : option bool :=
    match v with
    | LitV(LitBool b) => Some b
    | _               => None
    end.
  Definition resT_to_val (b : bool) : val := LitV(LitBool b).
  
  Lemma resT_inj_prop : ∀ (b : bool), bool_from_val (bool_to_val b) = Some b.
  Proof. done. Qed.

  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.

  Lemma resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  Proof. try done. Qed.

  Definition seq_spec (op: Op) (C: absT) (C': absT) (res: bool) : Prop :=
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
  Global Instance resT_inhabited : Inhabited resT.
  Proof. try apply _. Qed.

End SEARCH_STRUCTURE.

Module SKIPLIST0 <: DATA_STRUCTURE SEARCH_STRUCTURE.
  Import SEARCH_STRUCTURE.
  
  (*
    The snapshot stores:
    0) set of nodes
    1) ghost location for interface
    2) global interface
    3) ghost location for keyset
    4) global contents
    5) map from nodes to node-local info

    Node local info:
    1) singleton interface
    2) keyset
    3) physical contents
    4) Marking
  *)

  
  Definition snapshotUR := natUR.
  Definition snapshot := ucmra_car snapshotUR.
  
  Definition abs (s: snapshot) : absT := ∅.

  Global Instance snapshotUR_discrete : CmraDiscrete snapshotUR.
  Proof. try apply _. Qed.

  Global Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Proof. try apply _. Qed.
  
  Global Instance snapshot_inhabited : Inhabited snapshot := populate 0.
  
  Parameter inContents : val.
  Parameter findNext : val.
  Parameter try_constraint : val.
  Parameter maintenance : val.
  Parameter createNode: val.

  (** Template algorithms *)

  Definition traverse_rec (r: Node) : val :=
    rec: "tr" "p" "c" "k" :=
      let: "fn_ck" := findNext "c" "k" in
      if: Fst "fn_ck" then
        match: Snd "fn_ck" with
          NONE => ""
        | SOME "s" =>
            match: try_constraint "p" "c" "s" with
              NONE =>
                let: "fn_hk" := findNext #r "k" in
                match: Snd "fn_hk" with
                  NONE => ""
                | SOME "n" => 
                    "tr" #r "n" "k" end
            | SOME "_" => "tr" "p" "s" "k" end end  
      else
        match: Snd "fn_ck" with
          NONE => ("p", "c")
        | SOME "s" => "tr" "c" "s" "k" end.

  Definition traverse (r: Node) : val := 
    λ: "k", 
      let: "fn_hk" := findNext #r "k" in
      match: Snd "fn_hk" with
        NONE => ""
      | SOME "n" => 
          traverse_rec r #r "n" "k" end.

  Definition search (r: Node) : val :=
    λ: "k",
      let: "pc" := traverse r "k" in
      let: "c" := Snd "pc" in
      inContents "c" "k".
      
  Definition delete (r: Node) : val :=
    λ: "k",
      let: "pc" := traverse r "k" in
      let: "c" := Snd "pc" in
      if: ~ (inContents "c" "k") then
        #false
      else
        match: try_constraint "c" with
          NONE => #false
        | SOME "_" => maintenance "k";; #true end.
        
  Definition insert (r: Node) : val :=
    rec: "ins" "k" :=
      let: "pc" := traverse r "k" in
      let: "p" := Fst "pc" in
      let: "c" := Snd "pc" in
      if: inContents "c" "k" then
        #false
      else
        let: "e" := createNode "k" "c" in
        match: try_constraint "p" "c" "e" with
          NONE => "ins" "k"
        | SOME "_" => #true end.
  
  Definition esT : Type := gmap Node (gset nat).

  Definition flowUR := authR (multiset_flowint_ur nat).
  Definition auth_keysetUR := authUR $ (keysetUR nat).
  Definition auth_setnodeUR := authUR $ (gsetUR Node).

  Class skG Σ := SK {
                    sk_flowG :> inG Σ flowUR;
                    sk_auth_keysetG :> inG Σ auth_keysetUR;
                    sk_auth_setnodeG :> inG Σ auth_setnodeUR;
                   }.
                 
  Definition skΣ : gFunctors :=
    #[ GFunctor flowUR;  GFunctor auth_keysetUR;
       GFunctor auth_setnodeUR ].
  
  Instance subG_skΣ {Σ} : subG skΣ Σ → skG Σ.
  Proof. solve_inG. Qed.

  Section skiplist_v0.
    Context {Σ} `{!heapGS Σ, !skG Σ}.
    Notation iProp := (iProp Σ).
  
    Parameter node : Node → bool → esT → (gset nat) → iProp.
    Parameter node_timeless_proof : ∀ r n es V, Timeless (node r n es V).
    Global Instance node_timeless r n es V: Timeless (node r n es V).
    Proof. apply node_timeless_proof. Qed.  

    Parameter Mark : snapshot → Node → bool.
    Parameter ES : snapshot → Node → esT.
    Parameter PC : snapshot → Node → gset nat.
    Parameter GFI : snapshot → (multiset_flowint_ur nat).
    Parameter FI : snapshot → Node → (multiset_flowint_ur nat).
    Parameter FP : snapshot → gset Node.
  
    Definition Cont (s: snapshot) (n: Node) : gset nat :=
      if decide (Mark s n) then ∅ else PC s n.

    Parameter out_set : multiset_flowint_ur nat → gset nat.
    (* out_es es := ⋃_n es !!! n *)
    Parameter out_es : esT → gset nat.
    Parameter keyset : multiset_flowint_ur nat → gset nat. 
    
    (** data structure specific inv *)

    Definition globalRes γ_I γ_fp γ_ks s : iProp :=
        own γ_I (● (GFI s)) 
      ∗ own γ_fp (● FP s) 
      ∗ own γ_ks (● prod (KS, abs s)).
    
    Definition outflow_constraint (In: multiset_flowint_ur nat) (esn: esT) : Prop := True.
  
    Definition node_inv_pure s n : iProp :=
        ⌜¬ (Mark s n) → out_set (FI s n) ⊆ inset nat (FI s n) n⌝
      ∗ ⌜Cont s n ⊆ keyset (FI s n)⌝
      ∗ ⌜Mark s n → out_set (FI s n) ≠ ∅⌝
      ∗ ⌜outflow_constraint (FI s n) (ES s n)⌝ .

    Definition node_inv γ_I γ_ks s n : iProp :=
        node n (Mark s n) (ES s n) (PC s n)
      ∗ own γ_I (◯ (FI s n))
      ∗ own γ_ks (◯ prod (keyset (FI s n), Cont s n))
      ∗ node_inv_pure s n.   

    Definition per_tick_inv r s : iProp := 
        ⌜inset nat (FI s r) r = KS⌝ ∗ ⌜out_set (FI s r) = KS⌝
      ∗ ⌜¬ Mark s r⌝
      ∗ [∗ set] n ∈ (FP s), node_inv_pure s n.
    
    Definition transition_inv s s' : Prop :=
        (∀ n, n ∈ FP s → Mark s n → ES s' n = ES s n)
      ∧ (∀ n, n ∈ FP s → Mark s n → Mark s' n)
      ∧ (∀ n, n ∈ FP s → ¬ Mark s n → Mark s' n → ES s n ≠ ES s' n)
      ∧ (∀ n, n ∈ FP s → PC s n = PC s' n)
      ∧ (FP s ⊆ FP s').

    Definition skiplist_inv γ_I γ_fp γ_ks r (M: gmap nat snapshot) 
      (T: nat) (s: snapshot) : iProp :=
        globalRes γ_I γ_fp γ_ks s
      ∗ ([∗ set] n ∈ FP s, node_inv γ_I γ_ks s n)
      ∗ ([∗ set] t ∈ dom M, per_tick_inv r (M !!! t))
      ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝
      ∗ ⌜transition_inv (M !!! T) s⌝.
    
    Instance skiplist_inv_timeless γ_I γ_fp γ_ks r M T s : 
      Timeless (skiplist_inv γ_I γ_fp γ_ks r M T s).
    Proof.
    Admitted.  

    (** Helper functions specs *)
    
    Parameter inContents_spec : ∀ (k: nat) (n: Node),
       ⊢ (<<< ∀∀ m es pc, node n m es pc >>>
             inContents #n #k @ ⊤
         <<< ∃∃ (v: bool),
                node n m es pc ∗ ⌜v ↔ k ∈ pc⌝,
                RET #v >>>)%I.

    Parameter findNext_spec : ∀ (k: nat) (n: Node),
       ⊢ (<<< ∀∀ m es pc, node n m es pc >>>
             findNext #n #k @ ⊤
         <<< ∃∃ (success: bool) (n': Node),
                node n m es pc
              ∗ (match success with true => ⌜k ∈ es !!! n'⌝ 
                                  | false => ⌜k ∉ out_es es⌝ end),
             RET (match success with true => (#m, SOMEV #n') 
                                   | false => (#m, NONEV) end)  >>>)%I.
                                 
    Definition edgset_update es k curr succ : esT :=
      <[ succ := (es !!! succ) ∪ {[k]} ]>
        (<[ curr := (es !!! curr) ∖ {[k]} ]> es).

    Parameter try_constraint_trav_spec : ∀ (k: nat) (pred curr succ: Node),
       ⊢ (<<< ∀∀ m es pc, node pred m es pc >>>
             try_constraint #pred #curr #succ @ ⊤
         <<< ∃∃ (success: bool) es',
                node pred m es' pc
              ∗ (match success with true => ⌜m = false⌝ ∗ ⌜k ∈ es !!! curr⌝
                                            ∗ ⌜es' = edgset_update es k curr succ⌝ 
                                  | false => ⌜m = true ∨ k ∉ es !!! curr⌝
                                             ∗ ⌜es' = es⌝ end),
                RET (match success with true => SOMEV #() 
                                      | false => NONEV end)  >>>)%I.
  
    Parameter createNode_spec : ∀ (k: nat) (n: Node),
       ⊢ ({{{ True }}}
             createNode #k #n
         {{{ e m es pc, RET #e;
                node e m es pc
              ∗ ⌜k ∈ pc⌝
              ∗ ⌜k ∈ es !!! n⌝ }}})%I.
  
    Parameter try_constraint_insert_spec : ∀ (k: nat) (pred curr entry: Node),
       ⊢ (<<< ∀∀ m es pc, node pred m es pc >>>
             try_constraint #pred #curr #entry @ ⊤
         <<< ∃∃ (success: bool) es',
                node pred m es' pc
              ∗ (match success with true => ⌜m = false⌝ ∗ ⌜k ∈ es !!! curr⌝
                                            ∗ ⌜es' = edgset_update es k curr entry⌝ 
                                  | false => ⌜m = true ∨ k ∉ es !!! curr⌝
                                             ∗ ⌜es' = es⌝ end),
                RET (match success with true => SOMEV #() 
                                      | false => NONEV end)  >>>)%I.
End skiplist_v0.   
    
End SKIPLIST0.

Module SKIPLIST_SPEC : HINDSIGHT_SPEC SEARCH_STRUCTURE SKIPLIST0.
  Module DEFS := HINDSIGHT_DEFS SEARCH_STRUCTURE SKIPLIST0.
  Import SEARCH_STRUCTURE SKIPLIST0 DEFS.
  
  Context {Σ} `{!heapGS Σ, !skG DEFS.Σ}.
  Notation iProp := (iProp Σ).
  Context {γ_I γ_fp γ_ks: gname}.

  Lemma dsOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght op r (template_inv := skiplist_inv γ_I γ_fp γ_ks r) γ_sy t_id t0,
          ds_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv γ_I γ_fp γ_ks r) -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     dsOp (Op_to_val op) #r
                {{{ res, RET #res; past_lin_witness γ_m op res t0  }}}.
  Proof.
  Admitted.              
                
                

End SKIPLIST_SPEC.
