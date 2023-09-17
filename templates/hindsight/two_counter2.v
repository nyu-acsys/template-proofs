(* Two-location counter *)

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
Require Export one_shot_proph typed_proph.

Section two_counter.

  Definition read : val := 
    λ: "l1" "l2", 
      let: "v1" := !"l1" in
      (* { <->(l1 ↦ a1 ∗ l2 ↦ a2) } *)
      let: "v2" := !"l2" in
      (* { <->(l1 ↦ a1 ∗ l2 ↦ a2) 
          ∗ <->(l1 ↦ b1 ∗ l2 ↦ b2)
          ∗ a1 ≤ b1 ∗ a2 ≤ b2 } *)
      (* { <->(l1 ↦ a1 ∗ l2 ↦ a2) 
          ∗ <->(l1 ↦ b1 ∗ l2 ↦ b2)
          ∗ a1 + a2 ≤ b1 + b2 } *)
      (* { <->(l1 ↦ a1 ∗ l2 ↦ a2) 
          ∗ <->(l1 ↦ b1 ∗ l2 ↦ b2)
          ∗ a1 + a2 ≤ a1 + b2 ≤ b1 + b2 } *)
      "v1" + "v2".

  Definition sing_incr: val :=
    rec: "sing_incr" "l" :=
       let: "oldv" := !"l" in
       if: CAS "l" "oldv" ("oldv" + #1)
         then #()
         else "sing_incr" "l".

  Definition incr: val :=
    λ: "l1" "l2", 
      let: "random" := nondet_bool #() in
       if: "random"
        then sing_incr "l1"
        else sing_incr "l2".
        
  Definition dsOp : val :=
    λ: "OP" "l1" "l2",
      if: "OP" = #0 
      then read "l1" "l2"
      else incr "l1" "l2".

  Inductive Op := readOp | incrOp.

  Definition Op_to_val (op: Op) : val :=
    match op with
    | readOp => #0
    | incrOp => #1
    end.
    
  Definition absT := nat.
  Definition resT := nat.
  
  Definition resT_to_base_lit (n: resT) : base_lit := LitInt n.
  Coercion resT_to_base_lit : resT >-> base_lit.
  Definition resT_from_val (v : val) : option resT :=
    match v with
    | LitV(LitInt n) => Some (Z.to_nat n)
    | _               => None
    end.
  Definition resT_to_val (n : resT) : val := LitV(LitInt n).
  
  Lemma resT_inj_prop : ∀ (n : resT), resT_from_val (resT_to_val n) = Some n.
  Proof. intros n; simpl. apply f_equal. lia. Qed.

  Definition resTProph : TypedProphSpec :=
    mkTypedProphSpec resT resT_from_val resT_to_val resT_inj_prop.
  Definition resTTypedProph `{!heapGS Σ} := make_TypedProph resTProph.

  Lemma resT_proph_resolve : ∀ (res: resT), resT_from_val #res = Some res.
  Proof. intros res; simpl. apply f_equal; lia. Qed.

  Definition seq_spec (op: Op) (C: absT) (C': absT) (res: resT) : Prop :=
    match op with
    | readOp => (C' = C) ∧ (res = C)
    | incrOp => (C' = C + 1) ∧ (res = C)
    end.

  Global Instance seq_spec_dec : ∀ op c c' res, Decision (seq_spec op c c' res).
  Proof.
    intros op c c' res. unfold seq_spec. 
    destruct op; try apply and_dec; try destruct res; try apply _.
  Qed.

  Definition updater_thread (op: Op) (res: resT) : bool := 
    match op with
    | readOp => false
    | _ => true
    end.

  Global Instance updater_thread_dec: ∀ op res b, 
    Decision (updater_thread op res = b).
  Proof.
    intros op res b. unfold updater_thread.
    destruct op; destruct res; try apply _.
  Qed.  

  (*
  Global Instance Op_inhabited : Inhabited Op := populate (readOp).
  Global Instance absTUR_discrete : CmraDiscrete absTUR.
  Proof. try apply _. Qed.
  Global Instance absT_leibnizequiv : LeibnizEquiv absTUR.
  Proof. try apply _. Qed.
  Global Instance resT_inhabited : Inhabited resT.
  Proof. try apply _. Qed.
  *)

  (* RAs used in proof *)

  Definition auth_natUR := authUR $ max_natUR.

  Definition snapshot : Type := nat * nat.
  
  Definition abs (s: snapshot) : absT :=
    match s with
    | (n1, n2) => n1+n2 end.

(*
  Global Instance snapshotUR_discrete : CmraDiscrete snapshotUR.
  Proof. try apply _. Qed.

  Global Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Proof. try apply _. Qed.
  
  Global Instance snapshot_inhabited : Inhabited snapshot := 
    populate (0, 0).
*)
  
  (*
  Class dsG Σ := ds {
                    ds_auth_natG :> inG Σ auth_natUR;
                   }.
                 
  Definition dsΣ : gFunctors :=
    #[ GFunctor auth_natUR ].
  
  Global Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsG Σ.
  Proof. solve_inG. Qed.

  Notation iProp := (iProp Σ).
  *)
  Context (l1 l2: loc).
        

  (* Hindsight defs *)

  (* RAs used in hindsight proof *)

  Definition snapshotUR := prodUR natUR natUR.
  Definition absTUR := natUR.
  Definition resTUR := natUR.
  Definition agree_snapshotR := agreeR $ snapshotUR.
  Definition frac_absTR := dfrac_agreeR $ absTUR.
  Definition historyR := gmapUR nat $ snapshotUR.
  Definition auth_historyR := authR $ gmapUR nat $ agree_snapshotR.
  Definition frac_historyR := dfrac_agreeR $ historyR.
  Definition tokenUR := exclR unitO.
  Definition set_tidR := authR (gsetUR proph_id). 
  Definition thread_viewR := authUR $ gmapUR proph_id $ 
                              agreeR $ prodO natO gnameO.
  Definition thread_contraR := authUR $ gmapUR proph_id $ agreeR $ natUR.
                               
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
                  hsG_thread_contraG :> inG Σ thread_contraR;
                  hsG_upd_fracG :> inG Σ upd_fracR
                 }.
                 
  Definition hsΣ : gFunctors :=
    #[ GFunctor auth_natUR; GFunctor agree_snapshotR;
       GFunctor frac_absTR; GFunctor historyR;
       GFunctor auth_historyR; GFunctor tokenUR; 
       GFunctor frac_historyR; GFunctor set_tidR;
       GFunctor thread_viewR; GFunctor thread_contraR;
       GFunctor upd_fracR].
  
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
          @ ⊤ ∖ (↑(cntrN N) ∪ ↑(threadN N)), ∅
        << ∀∀ a' res (res': resT), dsRep γ_r a' ∗ ⌜seq_spec op a a' res⌝, COMM Q #res' >>)%I.

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
  
  Definition Token γ := own γ (Excl ()).
  
  Definition past_lin_witness γ_m op res t0 : iProp :=
    ∃ s, past_state γ_m t0 s ∗ ⌜seq_spec op (abs s) (abs s) res⌝.

  Definition Pending M T op vp t0 : iProp := 
    ¬ past_lin M T op vp t0.

  Definition Done N γ_tk (P: iProp) (Q: val → iProp) M T op (vp: resT) t0 : iProp := 
      past_lin M T op vp t0
    ∗ ((P -∗ |={⊤ ∖ ↑threadN N ∖ ↑cntrN N}=> Q #vp) ∨ Token γ_tk).

  (*
  Definition Accept_contra P : iProp :=
    P.
  
  Definition Submit_contra γ_cm op (t_id: proph_id) : iProp :=
    ∃ res, ⌜updater_thread op res = true⌝ 
          ∗ own γ_cm (◯ {[t_id := to_agree res]}).
  *)
  
  Definition State_nupd N γ_sy γ_tk P Q M T op vp t0: iProp :=
        own γ_sy (to_frac_agree (1/2) M)
      ∗ ⌜T = map_max M⌝ 
      ∗ (Pending M T op vp t0 ∨ Done N γ_tk P Q M T op vp t0).

  Definition thread_vars γ_t γ_ght γ_sy t_id t0 : iProp := 
    own γ_ght (◯ {[t_id := to_agree (t0, γ_sy)]}) ∗ own γ_t (◯ MaxNat t0).

  Definition Reg_nupd N γ_t γ_r γ_ght t_id M : iProp :=
    ∃ γ_tk γ_sy Q op vp t0 (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght γ_sy t_id t0
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ ⌜updater_thread op vp = false⌝ 
      ∗ inv (threadN N) 
        (∃ M T, State_nupd N γ_sy γ_tk (au N γ_r op Q) Q M T op vp t0).
  
  (*
  Definition State_upd γ_tk1 γ_tk2 γ_tk3 P Q vp : iProp :=
    Token γ_tk1 ∗ P ∨ Token γ_tk2 ∗ (Q #vp ∨ Token γ_tk3).

  Definition Reg_upd N γ_t γ_r γ_ght t_id : iProp :=
    ∃ γ_tk1 γ_tk2 γ_tk3 Q op vp t0 (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght γ_tk1 t_id t0
      ∗ ⌜updater_thread op vp = true⌝ 
      ∗ inv (threadN N)
        (State_upd γ_tk1 γ_tk2 γ_tk3 (au N γ_r op Q) Q vp).
  *)

  (*
  Lemma test N γ_r op Q M T vp t0 γ_tk :
    Pending (au N γ_r op Q) M T op vp t0 -∗
      Done γ_tk Q M T op vp t0 ∧ (au N γ_r op Q).
  Proof.  
    iIntros "(AU & Hcred & #Hpast)".
    iSplit; try done.
  Admitted.
  *)
  
  Definition helping_inv (N: namespace) γ_t γ_r γ_n γ_ght M : iProp :=
    ∃ (R: gset proph_id) (hγt: gmap proph_id (agreeR (prodO _ _))),
        own γ_n (● R)
      ∗ own γ_ght (● hγt) ∗ ⌜R ⊆ dom hγt⌝
      ∗ ([∗ set] t_id ∈ R, Reg_nupd N γ_t γ_r γ_ght t_id M).

  Definition transition_inv (s s': snapshot) : Prop :=
    (s'.1 = (s.1 + 1)%nat ∧ s'.2 = s.2) 
      ∨ (s'.1 = s.1 ∧ s'.2 = (s.2 + 1)%nat).

  Definition resources (s: snapshot) : iProp :=
    l1 ↦ #(s.1) ∗ l2 ↦ #(s.2).
  
  Definition ds_inv (M: gmap nat snapshot) 
    (T: nat) (s: snapshot) : iProp :=
      resources s
    ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝.
  
  Definition main_inv N γ_t γ_r γ_m γ_n γ_ght : iProp :=
    inv (cntrN N)
    (∃ M T (s: snapshot),
      dsRepI γ_r (abs s) ∗ ⌜M !!! T ≡ s⌝
    ∗ hist γ_t γ_m M T
    ∗ helping_inv N γ_t γ_r γ_n γ_ght M
    ∗ ds_inv M T s).

  Definition update_helping_protocol N γ_t γ_r γ_n γ_ght : iProp :=
        ∀ M T s, 
          ⌜map_max M < T⌝ -∗   
            dsRep γ_r (abs s) -∗
              helping_inv N γ_t γ_r γ_n γ_ght M ={⊤ ∖ ↑cntrN N}=∗
                helping_inv N γ_t γ_r γ_n γ_ght (<[T := s]> M) 
                ∗ dsRep γ_r (abs s).

  Lemma dsOp_spec N γ_t γ_r γ_m γ_n γ_ght op (r: loc) 
    γ_sy t_id t0 Q:
          main_inv N γ_t γ_r γ_m γ_n γ_ght -∗
          □ update_helping_protocol N γ_t γ_r γ_n γ_ght -∗
          thread_vars γ_t γ_ght γ_sy t_id t0 -∗
            {{{ au N γ_r op Q }}} 
                  dsOp (Op_to_val op) #r
            {{{ (res: resT), RET #res; 
                  ⌜updater_thread op res = true⌝ ∗ Q #res
                ∨ ⌜updater_thread op res = false⌝ 
                  ∗ past_lin_witness γ_m op res t0 
                  ∗ au N γ_r op Q }}}.
  Proof.
  Admitted.
  
  Definition dsOp' : val :=
    λ: "OP" "r",     
      let: "t_id" := NewProph in
      let: "p" := NewProph in
      let: "v" := dsOp "OP" "r" in
      resolve_proph: "p" to: "v";;
      "v".

  Lemma dsOp'_spec N γ_t γ_r γ_m γ_n γ_ght op (r: loc) :
          main_inv N γ_t γ_r γ_m γ_n γ_ght -∗
              <<< ∀∀ a, dsRep γ_r a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N) ∪ ↑(threadN N)
              <<< ∃∃ a' res, dsRep γ_r a' ∗ ⌜seq_spec op a a' res⌝, 
                  RET #res >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 resTTypedProph); first done.
    iIntros (vp p)"Hproph". wp_pures.
    
    destruct (decide (updater_thread op vp = true)) as [Upd_thr | Upd_thr].
    - 
    iApply fupd_wp. 
    iInv "HInv" as (M0 T0 s0) "(>HCntr & >%Habs0 & >Hist & Help & Templ)".
    iApply (lc_fupd_add_later with "Hc"). iNext. 
    iDestruct "Help" as (R0 hγt)"(HR & Hγt & Domm_hγt & Hstar)".
    
    iAssert (¬ ⌜tid ∈ R0⌝)%I as %H'.
    { admit. }
    assert (tid ∉ R0) as tid_notin_R0 by done.
    clear H'.
    (*
    iAssert (▷ (⌜tid ∉ R⌝ 
            ∗ ([∗ set] t_id ∈ R, Reg N γ_t γ_s γ_ght t_id M0) 
            ∗ proph1 tid vtid))%I with "[Hstar_reg Htid]" 
            as "(>%tid_notin_R & Hstar_reg & Htid)".
    { destruct (decide (tid ∈ R)); try done.
      - iEval (rewrite (big_sepS_elem_of_acc _ (R) tid); 
                            last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg & Hstar_reg')".
        iDestruct "Hreg" as (? ? ? ? ? ? ?)"(H' & _)".
        iAssert (▷ False)%I with "[H' Htid]" as "HF".
        iApply (proph1_exclusive tid with "[Htid]"); try done.
        iNext. iExFalso; try done.
      - iNext. iFrame. by iPureIntro. }
    *)
    
    
    
    (*
    iMod (own_update γ_u (● Ru1) (● (Ru1 ∪ {[tid]})) with "[$HR1]") as "HR1".
    { apply (auth_update_auth _ _ (Ru1 ∪ {[tid]})).
      apply gset_local_update. set_solver. }
    iMod (own_update γ_u (● (Ru1 ∪ {[tid]})) (● (Ru1 ∪ {[tid]}) ⋅ ◯ {[tid]}) 
              with "[$HR1]") as "(HR1 & #FP_t)".
    { apply (auth_update_dfrac_alloc _ (Ru1 ∪ {[tid]}) ({[tid]})).
      apply gset_included. clear; set_solver. }
      
    iMod (own_alloc (1)%Qp) as (γ_fr)"Hfr". { try done. }
    iEval (rewrite <-Qp.half_half) in "Hfr".      
    iEval (rewrite -(frac_op (1/2) (1/2))) in "Hfr". 
    iDestruct "Hfr" as "(Hfr1 & Hfr2)". 

    iMod (own_alloc (to_frac_agree (1) (M0))) 
            as (γ_sy)"Hfr_t". { try done. }        
    iEval (rewrite <-Qp.half_half) in "Hfr_t".      
    iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
    iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  
    *)
    iMod (own_alloc (Excl ())) as (γ_tk1) "Token1"; first try done.
    iMod (own_alloc (Excl ())) as (γ_tk2) "Token2"; first try done.
    iMod (own_alloc (Excl ())) as (γ_tk3) "Token3"; first try done.
    
    iDestruct "Domm_hγt" as %Domm_hγt.
    set (<[ tid := to_agree (T0, γ_tk1) ]> hγt) as hγt'.
    iDestruct (own_update _ _ 
      (● hγt' ⋅ ◯ {[ tid := to_agree (T0, γ_tk1) ]})
             with "Hγt") as ">Hγt".
    { apply auth_update_alloc. 
      rewrite /hγt'.
      apply alloc_local_update; last done.
      (*
      rewrite <-Domm_hγt in tid_notin_R1.
      by rewrite not_elem_of_dom in tid_notin_R1. *) }
    iDestruct "Hγt" as "(Hγt & #Hreg_gh)".

    iAssert (⌜map_max M0 = T0⌝)%I as %M_max. 
    { by iDestruct "Hist" as (M0') "(_&_&%&_)". }
    iDestruct "Hist" as (M0')"(H'&H'')". Check own_update.
    iDestruct (own_update _ _ (● (MaxNat T0) ⋅ ◯ (MaxNat T0)) with "H'") 
      as ">H1'".
    { apply auth_update_alloc. apply max_nat_local_update. 
      try done. }
    iDestruct "H1'" as "(H' & #HfragT0)".
    iAssert (hist γ_t γ_m M0 T0) with "[H' H'']" as "Hist".
    { iExists M0'; iFrame. }
    
    (*
    iMod (inv_alloc (threadN N) _
              (State_upd γ_tk1 γ_tk2 γ_tk3 (au N γ_r op Φ) Φ vp) 
                                    with "[AU Token1]") as "#HthInv".
    { iNext. iLeft. iFrame "∗". }
    *)
    
    iModIntro. iSplitR "AU Htid Hproph Token2 Token3". iNext.
    iExists M0, T0, s0. iFrame "∗%".
      iExists R0, hγt'. iFrame. admit.
      (*
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (Ru1 ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar1". unfold Reg_upd.
      iExists γ_tk1, γ_tk2, γ_tk3, Φ, op, vp, T0, vtid.
      rewrite Upd_thr; iFrame "∗#". by iPureIntro.
      assert ((Ru1 ∪ {[tid]}) ∖ {[tid]} = Ru1) as H' 
                  by (clear -tid_notin_R1; set_solver).
      by rewrite H'.*)
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_r γ_n γ_ght)%I 
        as "Upd_help". 
      { iIntros (M T s)"%Map_max DSRep".
        iIntros "Prot". clear hγt' Domm_hγt hγt.
        iDestruct "Prot" as (R hγt)"(HR & Hγt & Domm_hγt & Hstar)".
        iAssert (dsRep γ_r (abs s) -∗
                  ([∗ set] t_id ∈ R, Reg_nupd N γ_t γ_r γ_ght t_id M) ={⊤ ∖ ↑cntrN N}=∗
                  (([∗ set] t_id ∈ R, Reg_nupd N γ_t γ_r γ_ght t_id (<[T:=s]> M))
                  ∗ dsRep γ_r (abs s)))%I as "H'".
        { iIntros "DSRep". 
          iInduction R as [|tid' R' tid_notin_R IH] "HInd" using set_ind_L; 
            auto using big_sepS_empty'.
          rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
          rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
          assert (({[tid']} ∪ R') ∖ {[tid']} = R') as HR'. set_solver.
          rewrite HR'.
          iIntros "(Htid & Hbigstar)". 
          iMod ("HInd" with "[$DSRep] Hbigstar") as "(H' & DSRep)".
          iFrame "H'". 
          iDestruct "Htid" as (γ_tk' γ_sy' Q' op' vp' t0' vtid')
            "(Hproph & #Hthd & Hsy & %Hupd & #HthInv)".
          iInv "HthInv" as (M'' T'')"Hstate".
          iDestruct "Hstate" as "(>Hsy' & >%Map_max'' & Hstate)".
          assert (M'' = M) as ->. admit.
          iAssert (own γ_sy' (to_frac_agree (1 / 2) (<[T:=s]> M))
            ∗ own γ_sy' (to_frac_agree (1 / 2) (<[T:=s]> M)))%I
            with "[Hsy Hsy']" as "(Hsy & Hsy')".
          { admit. }
          iDestruct "Hstate" as "[>%HPending | HDone]".
          - destruct (decide (seq_spec op' (abs s) (abs s) vp'))
              as [Hss | Hss].
            + iAssert (□ (au N γ_r op' Q' -∗ 
                  |={⊤ ∖ ↑cntrN N ∖ ↑threadN N}=> Q' #vp'))%I 
                  with "[DSRep]" as "H'".
              { iModIntro. }
              iModIntro. iSplitL "Hsy". iNext. iExists (<[T:=s]> M), T.
              iFrame. iSplitR. admit. iRight. unfold Done. iSplitR. 
              iPureIntro. exists T. split; try done. admit.
              by rewrite lookup_total_insert. iLeft.
              iIntros "AU".
              iMod "AU" as (c) "[Cntr [_ Hcomm]]".
              iAssert (⌜c = abs s⌝)%I as "%". 
              { unfold dsRep, dsRepI. Search own valid.
                iDestruct (own_valid_2 with "[$DSRep] [$Cntr]") as %H'.
                rewrite frac_agree_op_valid_L in H'.
                destruct H' as [_ H']; by iPureIntro. } subst c. 
              iSpecialize ("Hcomm" $! (abs s) vp'). 
              iMod ("Hcomm" with "[Cntr]") as "HΦ".
              { iFrame. by iPureIntro. }
              iModIntro. iFrame. by rewrite lookup_total_insert.
              iModIntro. iFrame.
              iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
              iFrame "∗#%".
            + iModIntro. iSplitL "Hsy". iNext. iExists (<[T:=s]> M), T.
              iFrame. iSplitR. admit. iLeft. iPureIntro. 
              intros [t Ht]. admit.
              iModIntro. iFrame.
              iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
              iFrame "∗#%".
          - iModIntro. iSplitL "HDone Hsy". iNext. 
            iDestruct "HDone" as "(%H' & HDone)".
            iExists (<[T:=s]> M), T.
            iFrame. iSplitR. admit. iRight. iSplitR.
            iPureIntro. admit.
            iDestruct "HDone" as "[HAU | Token]".
            + iLeft. iIntros "(AU & DSRep)".
              iEval (rewrite lookup_total_insert) in "DSRep".
              iMod "AU" as (c) "[Cntr [_ Hcomm]]".
              iAssert (⌜c = abs s⌝)%I as "%". 
              { unfold dsRep, dsRepI. Search own valid.
                iDestruct (own_valid_2 with "[$DSRep] [$Cntr]") as %H''.
                rewrite frac_agree_op_valid_L in H''.
                destruct H'' as [_ H'']; by iPureIntro. } subst c. 
              iSpecialize ("Hcomm" $! (abs s) vp'). 
              iMod ("Hcomm" with "[Cntr]") as "HΦ".
              { iFrame. by iPureIntro. }
           }
        iDestruct ("H'" with "[$DSRep] [$Hstar]") as ">(Hstar & DSRep)".
        iModIntro. iFrame "DSRep".
        iExists R, hγt. iFrame.  *) admit. }
      iAssert (thread_vars γ_t γ_ght γ_tk1 tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_spec with "[] [] [] [AU]"); try done. unfold au.
      (* { iFrame "#∗". } *)
      
      iIntros (res)"HpastW". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. admit. }  
      wp_pures. iModIntro. iIntros "<-".
      rewrite Upd_thr. wp_pures. 
      iDestruct "HpastW" as "[HpastW | HpastW]".
      iModIntro; iDestruct "HpastW" as "(_&H')". iFrame.
      iDestruct "HpastW" as "(%&_)". exfalso; try done.
      
      (*
      wp_pure credit: "Hc"; wp_pure credit: "Hc'"; try done.
      
      iDestruct "HpastW" as "[HpastW | HpastW]"; last first.
      { iDestruct "HpastW" as "(% & _)"; exfalso; try done. }
      
      iDestruct "HpastW" as "(_ & Token1)". 
      iInv "HInv" as (M1 T1 s1) "(>HCntr & >%Habs1 & >Hist & Help & Templ)".
      iApply (lc_fupd_add_later with "Hc"). iNext. 
      clear tid_notin_R1 Domm_hγt Ru1 Rn1 hγt hγt'.
      iDestruct "Help" as (Ru2 Rn2 hγt)"(HR1 & HR2 & Hγt & 
        Domm_hγt & Hstar1 & Hstar2)".
      
      assert (tid ∈ Ru2) as tid_in_Ru2. { admit. }
      
      rewrite (big_opS_delete _ Ru2 tid).
      iDestruct "Hstar1" as "(Htid & Hstar1')".
      iInv "HthInv" as "H'".
      iApply (lc_fupd_add_later with "Hc'"). iNext.
      
      assert (γ_tk1' = γ_tk1) as ->. { admit. }
      
      iDestruct "H'" as "[Acc | Sub]".
      { iDestruct "Acc" as "(Acc & _)". 
        iPoseProof (own_valid_2 _ _ _ with "[$Token1] [$Acc]") as "%".
        exfalso; try done. }
      iDestruct "Sub" as "(Token2 & H')".
      iDestruct "H'" as "[HΦ | H']"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token3] [$H']") as "%".
        exfalso; try done. }
      iModIntro. iSplitL "Token2 Token3". iNext.
      iRight. iFrame.
      iModIntro. iSplitR "HΦ". iNext.
      iExists M1, T1, s1. iFrame "∗%#".
      iExists Ru2, Rn2, hγt. iFrame "∗%#".
      rewrite (big_opS_delete _ Ru2 tid); try done. 
      iFrame "Hstar1' Htid".
      iModIntro; iFrame. done.
      *)
    -   
      rewrite not_true_iff_false in Upd_thr.
      iApply fupd_wp. 
      iInv "HInv" as (M0 T0 s0) "(>HCntr & >%Habs0 & >Hist & Help & Templ)".
      iApply (lc_fupd_add_later with "Hc"). iNext. 

    iDestruct "Help" as (R0 hγt)"(HR & Hγt & Domm_hγt & Hstar)".
    
    iAssert (¬ ⌜tid ∈ R0⌝)%I as %H'.
    { admit. }
    assert (tid ∉ R0) as tid_notin_R0 by done.
    clear H'.
    (*
    iAssert (▷ (⌜tid ∉ R⌝ 
            ∗ ([∗ set] t_id ∈ R, Reg N γ_t γ_s γ_ght t_id M0) 
            ∗ proph1 tid vtid))%I with "[Hstar_reg Htid]" 
            as "(>%tid_notin_R & Hstar_reg & Htid)".
    { destruct (decide (tid ∈ R)); try done.
      - iEval (rewrite (big_sepS_elem_of_acc _ (R) tid); 
                            last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg & Hstar_reg')".
        iDestruct "Hreg" as (? ? ? ? ? ? ?)"(H' & _)".
        iAssert (▷ False)%I with "[H' Htid]" as "HF".
        iApply (proph1_exclusive tid with "[Htid]"); try done.
        iNext. iExFalso; try done.
      - iNext. iFrame. by iPureIntro. }
    *)
    
    iMod (own_update γ_n (● R0) (● (R0 ∪ {[tid]})) with "[$HR]") as "HR".
    { apply (auth_update_auth _ _ (R0 ∪ {[tid]})).
      apply gset_local_update. set_solver. }
    iMod (own_update γ_n (● (R0 ∪ {[tid]})) (● (R0 ∪ {[tid]}) ⋅ ◯ {[tid]}) 
              with "[$HR]") as "(HR & #FP_t)".
    { apply (auth_update_dfrac_alloc _ (R0 ∪ {[tid]}) ({[tid]})).
      apply gset_included. clear; set_solver. }
      
    iMod (own_alloc (to_frac_agree (1) (M0))) 
            as (γ_sy)"Hfr_t". { try done. }        
    iEval (rewrite <-Qp.half_half) in "Hfr_t".      
    iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
    iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  

    iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.
    iMod (own_alloc (Excl ())) as (γ_tk1) "Token1"; first try done.
    iMod (own_alloc (Excl ())) as (γ_tk2) "Token2"; first try done.

    iDestruct "Domm_hγt" as %Domm_hγt.
    set (<[ tid := to_agree (T0, γ_sy) ]> hγt) as hγt'.
    iDestruct (own_update _ _ 
      (● hγt' ⋅ ◯ {[ tid := to_agree (T0, γ_sy) ]})
             with "Hγt") as ">Hγt".
    { apply auth_update_alloc. 
      rewrite /hγt'.
      apply alloc_local_update; last done.
      admit.
      (*
      rewrite <-Domm_hγt in tid_notin_R1.
      by rewrite not_elem_of_dom in tid_notin_R12.*) }
    iDestruct "Hγt" as "(Hγt & #Hreg_gh)".

    iAssert (⌜map_max M0 = T0⌝)%I as %M_max. 
    { by iDestruct "Hist" as (M0') "(_&_&%&_)". }
    iDestruct "Hist" as (M0')"(H'&H'')". Check own_update.
    iDestruct (own_update _ _ (● (MaxNat T0) ⋅ ◯ (MaxNat T0)) with "H'") 
      as ">H1'".
    { apply auth_update_alloc. apply max_nat_local_update. 
      try done. }
    iDestruct "H1'" as "(H' & #HfragT0)".
    iAssert (hist γ_t γ_m M0 T0) with "[H' H'']" as "Hist".
    { iExists M0'; iFrame. }
    
(*      assert (∀ op c c' res, Decision (seq_spec op c c' res)) 
        as seq_spec_dec. { apply seq_spec_dec. } 
      destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))
        as [Hss | Hss].
*)
      
      (*
      iMod "AU" as (c) "[Cntr [_ Hcomm]]".
      iAssert (⌜c = abs s0⌝)%I as "%". 
      { unfold dsRep, dsRepI. Search own valid.
        iDestruct (own_valid_2 with "[$Cntr] [$HCntr]") as %H'.
        rewrite frac_agree_op_valid_L in H'.
        destruct H' as [_ H']; by iPureIntro. } subst c. 
      iSpecialize ("Hcomm" $! (abs s0) vp). 
      iMod ("Hcomm" with "[Cntr]") as "HΦ".
      { iFrame. apply leibniz_equiv in Habs0. 
        rewrite Habs0 in Hss. by iPureIntro. }
      
      iAssert (past_lin M0 T0 op vp T0)%I as "Hpast".
      { iPureIntro. exists T0. split; try done. }
      *)
      iAssert (∀ c, dsRep γ_r c -∗ ⌜c = abs s0⌝)%I as "H'".
        
      iMod (inv_alloc (threadN N) _ 
        (∃ M T, State_nupd N γ_sy γ_tk (au N γ_r op Φ) Φ M T op vp T0) 
        with "[]") as "#HthInv".
      { iNext. iExists M0, T0. iFrame. iSplitR. by iPureIntro.
        destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))
          as [Hss | Hss]; last first.
        - iLeft. iIntros "%Hpast". 
          destruct Hpast as [t [H' Hss']].
          assert (t = T0) as -> by lia. contradiction.
        - iRight. iSplitR. 
          iPureIntro. exists T0. split; try done.
          iLeft. iIntros "(AU & HCntr)".
          iMod "AU" as (c) "[Cntr [_ Hcomm]]".
          iAssert (⌜c = abs (M0 !!! T0)⌝)%I as "%". 
          { unfold dsRep, dsRepI. Search own valid.
            iDestruct (own_valid_2 with "[$HCntr] [$Cntr]") as %H'.
            rewrite frac_agree_op_valid_L in H'.
            destruct H' as [_ H']; by iPureIntro. } subst c. 
          iSpecialize ("Hcomm" $! (abs (M0 !!! T0)) vp). 
          iMod ("Hcomm" with "[Cntr]") as "HΦ".
          { iFrame. by iPureIntro. }
          iApply fupd_mask_intro. set_solver. iIntros "_". iFrame. }
      
      iModIntro. iSplitR "Hproph AU Token". iNext.
      iExists M0, T0, s0.  iFrame "∗%".
      iExists (R0 ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'. rewrite dom_insert.
      clear -Domm_hγt; set_solver.
      rewrite (big_sepS_delete _ (R0 ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar". unfold Reg_nupd.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. rewrite Upd_thr. iFrame "∗#".
      by iPureIntro.
      assert ((R0 ∪ {[tid]}) ∖ {[tid]} = R0) as H' 
                by (clear -tid_notin_R0; set_solver).
      by rewrite H'.  
        
      iModIntro.

      iAssert (update_helping_protocol N γ_t γ_r γ_n γ_ght)%I 
        as "Upd_help". { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_spec with "[] [] [] [AU]"); try done.
      
      iIntros (res)"HpastW". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. admit. }  
      wp_pures. iModIntro. iIntros "<-".
      rewrite Upd_thr. wp_pure credit: "Hc". wp_pures. 
      iDestruct "HpastW" as "[HpastW | HpastW]".
      iDestruct "HpastW" as "(%&_)". exfalso; try done.
      iDestruct "HpastW" as "(_&HpastW)".

(*       iDestruct "HpastW" as "(%Upd_thr' & HpastW)". *)
      iDestruct "HpastW" as "(HpastW & AU)".
      iInv "HthInv" as (M1_th T1_th)"(>Hth_sy & >% & Hth_or)".
      iInv "HInv" as (M1 T1 s1) "(>HCntr & >%Habs1 & >Hist & Help & Templ)".
      iApply (lc_fupd_add_later with "Hc"). iNext. 
      iDestruct "Help" as (R1 hγt1)"(HR & Hγt & Domm_hγt & Hstar_reg)".
      
      iAssert (⌜tid ∈ R1⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HR] [$FP_t]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro. set_solver. }
      rename H into tid_in_R1.
      
      iAssert (⌜map_max M1 = T1⌝)%I as %M_max1. 
      { by iDestruct "Hist" as (M1') "(_&_&%&_)". }
      
      assert (M1_th = M1) as ->. admit.
      assert (T1_th = T1) as ->. admit.
      
      (*
      iAssert (▷ (⌜M1_th = M1⌝ ∗ ⌜T1_th = T1⌝ 
               ∗ ([∗ set] t_id ∈ R1, Reg N γ_t γ_s γ_ght t_id M1)
               ∗ own (γ_sy) (to_frac_agree (1 / 2) M1_th) ))%I
                with "[Hstar_reg Hth_sy]" as "(>% & >% & Hstar_reg & >Hth_sy)". 
      { 
        iEval (rewrite (big_sepS_elem_of_acc _ (R1) tid); 
                                last by eauto) in "Hstar_reg".
        iDestruct "Hstar_reg" as "(Hreg_t & Hstar_reg')".
        iDestruct "Hreg_t" as (γ_tk' γ_sy' Q' op' vp' t0' vtid')
                          "(Hreg_proph & >Hreg_gh' & >Hreg_sy & H')".
        iDestruct "Hreg_gh'" as "(Hreg_gh' & #?)".
        iCombine "Hreg_gh" "Hreg_gh'" as "H''".
        iPoseProof (own_valid with "H''") as "Valid".
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
          iPureIntro. split; first by apply leibniz_equiv.
          rewrite tid_in_R1. apply leibniz_equiv in V_M. by rewrite V_M. } 
        subst M1_th T1_th.
          
        iSplitR. { by iPureIntro. } 
        iSplitR. iNext; by iPureIntro.
        iSplitR "Hth_sy". iApply "Hstar_reg'".
        iNext. iExists γ_tk', γ_sy, Q', op', vp', T0, vtid'.
        iFrame "∗#". by iNext. 
      } subst M1_th T1_th.
      *)
      
      iEval (unfold past_lin_witness) in "HpastW".
      (* iEval (rewrite Upd_thr) in "HpastW".*)

      iDestruct "Hth_or" as "[HPending | HDone]".
      { iDestruct "HPending" as "%HPending".
        
        iDestruct "HpastW" as (s) "(HpastW & %Hseq)".
          iDestruct "HpastW" as (t)"(%T0_le_t & Ht)".
          iDestruct "Hist" as (M1') "(H'&H''&H''')".
          admit.
          (*
          iDestruct (history_sync with "[$H''] [$Ht]") as "%M1'_t".
          iDestruct "H'''" as %(H1' & _ & H1'' & H1''').
          apply (H1'' t s) in M1'_t.
          exfalso. apply HPending. exists t.
          split.
          + split; try done. apply elem_of_dom_2 in M1'_t.
            by apply map_max_dom in M1'_t.
          + rewrite !lookup_total_alt. rewrite M1'_t. by simpl.
          *) }
      
      iDestruct "HDone" as "(#Hpast'& HDone)".
      iDestruct "HDone" as "[HDone | Token']"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Token']") as "%".
        exfalso; try done. }
      
      iMod ("HDone" with "[AU HCntr]") as "(HΦ & HCntr)".
      apply leibniz_equiv in Habs1. rewrite Habs1. iFrame.

      apply leibniz_equiv in Habs1. rewrite Habs1.
      iModIntro. iSplitR "HΦ Hth_sy Token".
      iExists M1, T1, s1; iFrame "∗%".
      iNext. iSplitR. iPureIntro. by apply leibniz_equiv_iff.
      iExists R1, hγt1; iFrame.     

      iModIntro. iSplitL "Token Hth_sy".
      iNext. iExists M1, T1. iFrame "Hth_sy". 
      iSplitR. by iPureIntro. iRight. iFrame "∗#%".
      
      by iModIntro.
  Admitted. 
      
      
      
        
      
      
      
     
    
  
  


End two_counter.