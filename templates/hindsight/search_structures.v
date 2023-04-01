(*
Differences compared to hindsight.v:

1) History needs to be updated anytime a snapshot is 
  updated (and not just when the abstract state is udpated).
2) M !!! T = s -> M !!! T ≡ s
*)

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
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Export multiset_flows one_shot_proph typed_proph.

Parameter search : val.
Parameter insert : val.
Parameter delete : val.

(*
Definition cssOp : val :=
  λ: "OP" "r",     
    if: "OP" = #0 then search "r"
    else if: "OP" = #1 then insert "r"
    else delete "r".
*)
Parameter cssOp : val.

Definition cssOp' : val :=
  λ: "OP" "r" "k",     
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "v" := cssOp "OP" "r" "k" in
    resolve_proph: "p" to: "v";;
    "v".


Definition K := Z.

(** Proof Setup **)
Section Proof.
  
  (* Data structure specific definitions *)

  Inductive Op := searchOp | insertOp | deleteOp.
  Definition snapshot := nat.
  Definition snapshotUR := natUR.
  Definition Op_to_val (op: Op) : val :=
    match op with
    | searchOp => #0
    | insertOp => #1
    | deleteOp => #2 
    end.
  Definition absT := gset K.
  Definition absTUR := gsetUR K.
  Definition resT := bool.
  Definition seq_spec (op: Op) (C: absT) (C': absT) (res: bool) (k: K) : Prop :=
    match op with
    | searchOp => C' = C ∧ (if res then k ∈ C else k ∉ C)
    | insertOp => C' = C ∪ {[k]} ∧ (if res then k ∉ C else k ∈ C)
    | deleteOp => C' = C ∖ {[k]} ∧ (if res then k ∈ C else k ∉ C)
    end.

  Definition abs (s: snapshot) : absT := ∅.
  Definition updater_thread (op: Op) (res: resT) : bool := 
    match op, res with
    | searchOp, _ => false
    | _, false => false
    | _, _ => true
    end.

  Parameter seq_spec_dec : ∀ op s s' res k, Decision (seq_spec op s s' res k).
  (* Parameter snapshot_eq: EqDecision snapshot.*)
  
  (* RAs used in proof *)

  Definition auth_natUR := authUR $ max_natUR.
  Definition agree_snapshotR := agreeR $ snapshotUR.
  Definition frac_absTR := dfrac_agreeR $ absTUR.
  Definition historyR := gmapUR nat $ snapshotUR.  
  Definition history_agreeR := gmapUR nat $ agree_snapshotR.
  Definition auth_historyR := authR $ history_agreeR.
  Definition tokenUR := exclR unitO.
  Definition frac_historyR := dfrac_agreeR $ historyR.
  Definition set_tidR := authR (gsetUR proph_id). 
  Definition thread_viewR := authUR $ 
                              gmapUR proph_id $ 
                                agreeR $ prodO natO gnameO.

  Class dsG Σ := DS {
                  dsG_auth_natG :> inG Σ auth_natUR;
                  dsG_agree_snapshotG :> inG Σ agree_snapshotR;
                  dsG_frac_absTG :> inG Σ frac_absTR;
                  dsG_historyG :> inG Σ historyR;
                  dsG_history_agreeG :> inG Σ history_agreeR;
                  dsG_auth_historyG :> inG Σ auth_historyR;
                  dsG_tokenG :> inG Σ tokenUR;
                  dsG_frac_historyG :> inG Σ frac_historyR;
                  dsG_set_tidG :> inG Σ set_tidR;
                  dsG_thread_viewG :> inG Σ thread_viewR
                 }.
                 
  Definition dsΣ : gFunctors :=
    #[ GFunctor auth_natUR; GFunctor agree_snapshotR;
       GFunctor frac_absTR; GFunctor historyR; GFunctor history_agreeR;
       GFunctor auth_historyR; GFunctor tokenUR; 
       GFunctor frac_historyR; GFunctor set_tidR;
       GFunctor thread_viewR ].
  
  Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsG Σ.
  Proof. solve_inG. Qed.
End Proof.

Section counter.
  Context {Σ} `{!heapGS Σ, !dsG Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types M : gmap nat snapshot.
  Implicit Types T : nat.

  Global Definition cssN N := N .@ "css".
  Global Definition threadN N := N .@ "thread".

  Instance snapshot_lookuptotal : LookupTotal nat snapshotUR (gmap nat snapshot).
  Proof.
  Admitted.

  Definition map_max (M: gmap nat snapshot) : nat := 
    max_list (elements (dom M)).

  Definition hist γ_t γ_m M T : iProp :=
    ∃ (M': gmap nat (agreeR (_))),
      own γ_t (● MaxNat T) ∗ own γ_m (● M')
    ∗ ⌜T = map_max M⌝
    ∗ ⌜map_Forall (λ k a, a = to_agree (M !!! k)) M'⌝
    ∗ ⌜∀ t, t < T → M !!! t ≠ M !!! (t+1)%nat⌝.
  
  Definition CSS γ_r (a: absTUR) : iProp := 
    own γ_r (to_frac_agree (1/2) a).

  Definition CSSI γ_r (a: absTUR) : iProp := 
    own γ_r (to_frac_agree (1/2) a).
    
  (** Helping Inv **)
  
  Definition au N γ_r op k (Q : val → iProp) := 
    (AU << ∃∃ C, CSS γ_r C >> 
          @ ⊤ ∖ ↑(cssN N), ∅
        << ∀∀ C' res, CSS γ_r C' ∗ ⌜seq_spec op C C' res k⌝, COMM Q #res >>)%I.
        
  Definition past_lin M T op k res t0 : iProp :=
    ⌜match updater_thread op res with
    | true =>
      ∃ t, t0 ≤ t < T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! (t+1)%nat)) res k
    | false =>  
      ∃ t, t0 ≤ t ≤ T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! t)) res k end⌝.

  Definition past_state γ_m (t0: nat) (s: snapshot) : iProp :=
    ∃ t, ⌜t0 ≤ t⌝ ∗ own γ_m (◯ {[t := to_agree s]}).
  
  Definition past_two_states γ_m (t0: nat) (s s': snapshot) : iProp :=
    ∃ t, ⌜t0 ≤ t⌝ 
    ∗ own γ_m (◯ {[t := to_agree s]}) 
    ∗ own γ_m (◯ {[t+1 := to_agree s']}).

  Definition past_lin_witness γ_m op k res t0 : iProp :=
    match updater_thread op res with
    | true =>
      ∃ s s', past_two_states γ_m t0 s s' ∗ ⌜seq_spec op (abs s) (abs s') res k⌝
    | false =>  
      ∃ s, past_state γ_m t0 s ∗ ⌜seq_spec op (abs s) (abs s) res k⌝ end.

  Definition Pending (P: iProp) M T op k vp t0 : iProp := 
    P ∗ £1 ∗ ¬ past_lin M T op k vp t0.

  Definition Done γ_tk (Q: val → iProp) M T op (k: K) (vp: bool) t0 : iProp := 
      (Q #vp ∨ own γ_tk (Excl ())) ∗ past_lin M T op k vp t0.

  Definition State γ_sy γ_tk P Q M T op k vp t0: iProp :=
      own γ_sy (to_frac_agree (1/2) M)
    ∗ ⌜T = map_max M⌝ 
    ∗ (Pending P M T op k vp t0 ∨ Done γ_tk Q M T op k vp t0).

  Definition thread_vars γ_t γ_ght γ_sy t_id t0 : iProp := 
    own γ_ght (◯ {[t_id := to_agree (t0, γ_sy)]}) ∗ own γ_t (◯ MaxNat t0).

  Definition Reg N γ_t γ_s γ_ght t_id M : iProp :=
    ∃ γ_tk γ_sy Q op k (vp: bool) (t0: nat) (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght γ_sy t_id t0
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ inv (threadN N) (∃ M T, State γ_sy γ_tk (au N γ_s op k Q) Q M T op k vp t0).

  Definition helping_inv (N: namespace) γ_t γ_s γ_td γ_ght M : iProp :=
    ∃ (R: gset proph_id) (hγt: gmap proph_id (agreeR _)),
        own γ_td (● R)
      ∗ own γ_ght (● hγt) ∗ ⌜dom hγt = R⌝  
      ∗ ([∗ set] t_id ∈ R, Reg N γ_t γ_s γ_ght t_id M).
  
  Definition css_inv N γ_t γ_s γ_m γ_td γ_ght template_inv : iProp :=
    inv (cssN N)
    (∃ M T s,
      CSS γ_s (abs s) ∗ ⌜M !!! T ≡ s⌝
    ∗ hist γ_t γ_m M T
    ∗ helping_inv N γ_t γ_s γ_td γ_ght M
    ∗ template_inv M T s).
    
  Definition update_helping_protocol N γ_t γ_s γ_td γ_ght : iProp :=
        ∀ M T C s, 
          ⌜map_max M = T⌝ -∗   
            CSS γ_s C -∗ own γ_t (● MaxNat T) -∗ 
              helping_inv N γ_t γ_s γ_td γ_ght M ={⊤ ∖ ↑cssN N}=∗
                helping_inv N γ_t γ_s γ_td γ_ght (<[T := s]> M) 
                ∗ CSS γ_s C ∗ own γ_t (● MaxNat T).

  (** Proofs *)    

  Parameter searchOp_spec: ∀ N γ_s γ_t γ_m γ_td γ_ght template_inv r (k: K) γ_sy t_id t0,
          css_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     search #r #k
                {{{ res, RET #res; past_lin_witness γ_m searchOp k res t0  }}}.


  Lemma counterOp_spec N γ_s γ_t γ_m γ_td γ_ght template_inv op r (k: K) γ_sy t_id t0 :
          css_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     cssOp (Op_to_val op) #r #k
                {{{ res, RET #res; past_lin_witness γ_m op k res t0  }}}.
  Proof.
  Admitted.

  Lemma cssOp'_spec N γ_s γ_t γ_m γ_td γ_ght template_inv op r (k: K) :
          css_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
              <<< ∀∀ C, CSS γ_s C >>> 
                     cssOp' (Op_to_val op) #r #k @ ↑(cssN N)
              <<< ∃∃ C' res, CSS γ_s C' ∗ ⌜seq_spec op C C' res k⌝, RET #res >>>.
  Proof.
  (*
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 NatTypedProph); first done.
    iIntros (vp p)"Hproph". wp_pures.
    iApply fupd_wp.
    iInv "HInv" as (M0 T0 n0) "(>HCntr & >%Habs0 & >Hist & Help & Templ)". 
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
        (* Issue with op *)
        (* iDestruct "Hreg" as (? ? ? ? ? ? ?)"(H' & _)". *)
        iAssert (∃ vtid', proph1 tid vtid')%I as (?)"H'".
        { admit. }
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
      
    destruct (decide (updater_thread op vp = true 
      ∨ (updater_thread op vp = false 
          ∧ ¬ seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))) 
      as [Hcase1 | Hcase2].
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
      iExists M0, T0, n0. iFrame "∗%".
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
      
      iModIntro. wp_bind (counterOp _ _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". }
      
      wp_apply counterOp_spec; try done.
      (*
      iAaccIntro with ""; try done.
      { iIntros "_"; iModIntro; eauto with iFrame. }
      iIntros (res)"HpastW". iModIntro.
      *)
      iIntros (res)"HpastW".
      wp_pures.
      wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph");
         try done.
      wp_pures. iModIntro. iIntros "%vp_eqZ_res".
      assert (vp = res) as vp_eq_res by (clear -vp_eqZ_res; lia).
      clear vp_eqZ_res. subst vp.
       
      iApply fupd_wp.
      
      iInv "HthInv" as (M1_th T1_th)"(>Hth_sy & >% & Hth_or)".
      iInv "HInv" as (M1 T1 n1) "(>HCntr & >%Habs1 & >Hist & Help & Templ)".
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
      { admit.
        (*
        iEval (rewrite (big_sepS_elem_of_acc _ (R1) tid); 
                                last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg_t & Hstar_reg')".
        iDestruct "Hreg_t" as (P Q γ_tk' γ_sy' t0 vp' vtid')
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
                  
        iAssert (⌜M1_th = M1⌝)%I as "%".
        { iPoseProof (own_valid_2 _ _ _ with "[$Hth_sy] [$Hreg_sy]") 
              as "V_M".
          iDestruct "V_M" as %V_M.
          apply frac_agree_op_valid in V_M. destruct V_M as [_ V_M].
          apply leibniz_equiv_iff in V_M.
          by iPureIntro. } subst M1_th.
        iSplitR. iNext; by iPureIntro.
        iSplitR "Hth_sy". iApply "Hstar_reg'".
        iNext. iExists P, Q, γ_tk', γ_sy, T0, vp', vtid'.
        iFrame "∗#". by iNext. 
        *)
      } subst M1_th T1_th.
      
      iEval (unfold past_lin_witness) in "HpastW".
      (* iEval (rewrite Upd_thr) in "HpastW".*)

      iDestruct "Hth_or" as "[Hth_or | Hth_or]".
      { iDestruct "Hth_or" as "(AU & Hc & >%)".
        rename H into HPending.
        exfalso. apply HPending.
        admit. }  
      
      iDestruct "Hth_or" as "(Hth_or & Hpast)".  
      iDestruct "Hth_or" as "[Hth_or | >Hth_or]"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Hth_or]") as "%".
        exfalso; try done. }
        
      iModIntro. iSplitR "Hth_or Hth_sy Token Hpast".
      iExists M1, T1, n1; iFrame "∗%".
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
        - destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp));
            try done. 
          exfalso. apply Hcase2. right.
          split; try done. } 
      iMod "AU" as (n) "[Cntr [_ Hcomm]]".
        iAssert (⌜n = n0⌝)%I as "%". { admit. } subst n. 
        iSpecialize ("Hcomm" $! n0 vp). 
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
        iExists M0, T0, n0.  iFrame "∗%".
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
        (*
        awp_apply counterOp_spec without "HΦ"; try done.
        iAaccIntro with ""; try done.
        { iIntros "_". iModIntro; try eauto with iFrame. } 
        iIntros (res) "HpastW". 
        iModIntro. iIntros "HΦ". wp_pures.
        *)
        wp_apply counterOp_spec; try done.
        iIntros (res)"HpastW". wp_pures.
        wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); 
          try done.
        wp_pures. iModIntro. iIntros "%". rename H into vp_eq_res. 
        assert (vp = res). { clear -vp_eq_res. lia. } 
        clear vp_eq_res. wp_pures. iModIntro. by subst vp.
  *)
  Admitted.
End counter.  