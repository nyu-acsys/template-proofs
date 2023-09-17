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

Module Type DATA_STRUCTURE.
  
  Parameter dsOp : val.
  Parameter Op : Type.
  Parameter Op_to_val : Op -> val.

  Parameter absTUR : ucmra.
  Definition absT := ucmra_car absTUR.

  Parameter resTUR : ucmra.
  Definition resT := ucmra_car resTUR.
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
  
  Declare Instance Op_inhabited : Inhabited Op.
  Declare Instance absTUR_discrete : CmraDiscrete absTUR.
  Declare Instance resTUR_discrete : CmraDiscrete resTUR.
  Declare Instance absT_leibnizequiv : LeibnizEquiv (absT).
  Declare Instance resT_inhabited : Inhabited resT.
  Declare Instance snapshotUR_discrete : CmraDiscrete snapshotUR.  
  Declare Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Declare Instance snapshot_inhabited : Inhabited snapshot.
  
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
  Definition thread_viewR := authUR $ gmapUR proph_id $ 
                              agreeR $ prodO natO gnameO.
  Definition thread_contraR := authUR $ gmapUR proph_id $ agreeR $ resTUR.
                               
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
  
  Context `{!heapGS DS.Σ, !hsG DS.Σ}.
  Notation iProp := (iProp DS.Σ).
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

  Definition Pending (P: iProp) M T op vp t0 : iProp := 
    P ∗ £1 ∗ ¬ past_lin M T op vp t0.

  Definition Done γ_tk (Q: val → iProp) M T op (vp: resT) t0 : iProp := 
      (Q #vp ∨ Token γ_tk) ∗ past_lin M T op vp t0.

  Definition Accept_contr P : iProp :=
    P.
  
  Definition Submit_contr γ_cm op (res: nat) (t_id: proph_id) : iProp :=
    ⌜updater_thread op res = true⌝ ∗ own γ_cm (◯ {[t_id := to_agree res]}).

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

  Lemma test N γ_r op Q M T vp t0 γ_tk :
    Pending (au N γ_r op Q) M T op vp t0 -∗
      Done γ_tk Q M T op vp t0 ∧ (au N γ_r op Q).
  Proof.  
    iIntros "(AU & Hcred & #Hpast)".
    iSplit; try done.
  Admitted.
  
  Definition helping_inv (N: namespace) γ_t γ_r γ_td1 γ_td2 γ_ght M : iProp :=
    ∃ (R1 R2: gset proph_id) (hγt: gmap proph_id (agreeR (prodR _))),
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

Module DISTRIBUTED_COUNTER <: DATA_STRUCTURE.

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
        

  Inductive Opp := readOp | incrOp.
  Definition Op := Opp.

  Definition Op_to_val (op: Op) : val :=
    match op with
    | readOp => #0
    | incrOp => #1
    end.
    
  Definition absTUR := natUR.
  Definition absT := ucmra_car absTUR.

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

  Global Instance Op_inhabited : Inhabited Op := populate (readOp).
  Global Instance absTUR_discrete : CmraDiscrete absTUR.
  Proof. try apply _. Qed.
  Global Instance absT_leibnizequiv : LeibnizEquiv absTUR.
  Proof. try apply _. Qed.
  Global Instance resT_inhabited : Inhabited resT.
  Proof. try apply _. Qed.


  (* RAs used in proof *)

  Definition auth_natUR := authUR $ max_natUR.

  Definition snapshotUR :=
    prodUR natUR natUR.

  Definition snapshot := ucmra_car snapshotUR.
  
  Definition abs (s: snapshot) : absT :=
    match s with
    | (n1, n2) => n1+n2 end.

  Global Instance snapshotUR_discrete : CmraDiscrete snapshotUR.
  Proof. try apply _. Qed.

  Global Instance snapshot_leibnizequiv : LeibnizEquiv (snapshot).
  Proof. try apply _. Qed.
  
  Global Instance snapshot_inhabited : Inhabited snapshot := 
    populate (0, 0).

  Class dsGG Σ := ds {
                    ds_auth_natG :> inG Σ auth_natUR;
                   }.
                 
  Definition dsΣ : gFunctors :=
    #[ GFunctor auth_natUR ].
  
  Global Instance subG_dsΣ {Σ} : subG dsΣ Σ → dsGG Σ.
  Proof. solve_inG. Qed.

  Context `{!heapGS Σ, !dsGG Σ}. 
  Context (l1 l2: loc).
  Notation iProp := (iProp Σ).
        
  Definition transition_inv (s s': snapshot) : Prop :=
    (s'.1 = (s.1 + 1)%nat ∧ s'.2 = s.2) 
      ∨ (s'.1 = s.1 ∧ s'.2 = (s.2 + 1)%nat).

  Definition resources (s: snapshot) : iProp :=
    l1 ↦ #(s.1) ∗ l2 ↦ #(s.2).
  
  Definition ds_inv (M: gmap nat snapshot) 
    (T: nat) (s: snapshot) : iProp :=
      resources s
    ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝.

  Definition dsG := dsGG.

  Definition dsG0 : dsG Σ.
  Admitted.

End DISTRIBUTED_COUNTER.

Module HINDSIGHT_SPEC.
  Module DEFS := HINDSIGHT_DEFS DISTRIBUTED_COUNTER.
  Import DISTRIBUTED_COUNTER DEFS.

  Lemma dsOp_spec N γ_r γ_t γ_m γ_td1 γ_td2 γ_ght op (r: loc) γ_sy t_id t0:
          main_inv N γ_t γ_r γ_m γ_td1 γ_td2 γ_ght -∗
          □ update_helping_protocol N γ_t γ_r γ_td1 γ_td2 γ_ght -∗
          thread_vars γ_t γ_ght γ_sy t_id t0 -∗
            {{{ True }}} 
                  dsOp (Op_to_val op) #r
            {{{ (res: resT), RET #res; 
                  past_lin_witness γ_m op res t0 }}}.
  Proof.
  Admitted.

End HINDSIGHT_SPEC.

Module CLIENT_SPEC.
  Import DISTRIBUTED_COUNTER HINDSIGHT_SPEC.DEFS HINDSIGHT_SPEC.

  Definition dsOp' : val :=
    λ: "OP" "r",     
      let: "t_id" := NewProph in
      let: "p" := NewProph in
      let: "v" := dsOp "OP" "r" in
      resolve_proph: "p" to: "v";;
      "v".
        
  (** Proofs *)
  
  Lemma dsOp'_spec N γ_s γ_t γ_m γ_td1 γ_td2 γ_ght op (r: loc) :
          main_inv N γ_t γ_s γ_m γ_td1 γ_td2 γ_ght -∗
              <<< ∀∀ a, dsRep γ_s a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N)
              <<< ∃∃ a' res, dsRep γ_s a' ∗ ⌜seq_spec op a a' res⌝, 
                  RET #res >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pure credit:"Hc1". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 resTTypedProph); first done.
    iIntros (vp p)"Hproph". wp_pures.
    
    destruct (decide (updater_thread op vp = true)) as [Upd_thr | Upd_thr].
    - 
    iApply fupd_wp. 
    iInv "HInv" as (M0 T0 s0) "(>HCntr & >%Habs0 & >Hist & Help & Templ)".
    iApply (lc_fupd_add_later with "Hc1"). iNext. 
    iDestruct "Help" as (R1 R2 hγt)"(HR1 & HR2 & Hγt & 
      Domm_hγt & Hstar1 & Hstar2)".
    
    iAssert (¬ ⌜tid ∈ R1 ∪ R2⌝)%I as %H'.
    { admit. }
    assert (tid ∉ R1 ∪ R2) as tid_notin_R12 by done.
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
    
    iMod (own_update γ_td1 (● R1) (● (R1 ∪ {[tid]})) with "[$HR1]") as "HR1".
    { apply (auth_update_auth _ _ (R1 ∪ {[tid]})).
      apply gset_local_update. set_solver. }
    iMod (own_update γ_td1 (● (R1 ∪ {[tid]})) (● (R1 ∪ {[tid]}) ⋅ ◯ {[tid]}) 
              with "[$HR1]") as "(HR1 & #FP_t)".
    { apply (auth_update_dfrac_alloc _ (R1 ∪ {[tid]}) ({[tid]})).
      apply gset_included. clear; set_solver. }
      
    iMod (own_alloc (1)%Qp) as (γ_fr)"Hfr". { try done. }
    iEval (rewrite <-Qp.half_half) in "Hfr".      
    iEval (rewrite -(frac_op (1/2) (1/2))) in "Hfr". 
    iDestruct "Hfr" as "(Hfr1 & Hfr2)". 

    (*
    iMod (own_alloc (to_frac_agree (1) (M0))) 
            as (γ_sy)"Hfr_t". { try done. }        
    iEval (rewrite <-Qp.half_half) in "Hfr_t".      
    iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
    iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  
    *)
    
    iDestruct "Domm_hγt" as %Domm_hγt.
    set (<[ tid := to_agree (T0, γ_fr) ]> hγt) as hγt'.
    iDestruct (own_update _ _ 
      (● hγt' ⋅ ◯ {[ tid := to_agree (T0, γ_fr) ]})
             with "Hγt") as ">Hγt".
    { apply auth_update_alloc. 
      rewrite /hγt'.
      apply alloc_local_update; last done.
      rewrite <-Domm_hγt in tid_notin_R12.
      by rewrite not_elem_of_dom in tid_notin_R12. }
    iDestruct "Hγt" as "(Hγt & #Hreg_gh)".
    (*  
    iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.
    *)
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
    
    iModIntro. iSplitR "Hproph Hfr1". iNext.
    iExists M0, T0, s0. iFrame "∗%".
      iExists (R1 ∪ {[tid]}), R2, hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R1 ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar1". unfold Reg_upd.
      iExists γ_fr, Φ, op, vp, T0, vtid.
      rewrite Upd_thr; iFrame "∗#". iSplitR. { by iPureIntro. }
      iLeft. iFrame.
      assert ((R1 ∪ {[tid]}) ∖ {[tid]} = R1) as H' 
                  by (clear -tid_notin_R12; set_solver).
      by rewrite H'.
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td1 γ_td2 γ_ght)%I 
        as "Upd_help". { admit. }
      iAssert (thread_vars γ_t γ_ght γ_fr tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_spec with "[] [] [] []"); try done.
      
      iIntros (res)"HpastW". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }  
      wp_pures. iModIntro. iIntros "%vp_eq_res". subst vp.
      rewrite Upd_thr. wp_pures; try done.
    
    destruct (decide (updater_thread op vp = true)) as [Upd_thr | Upd_thr].
    - iModIntro. iSplitR "AU Hproph". iNext.
      iExists M0, T0, s0. iFrame "∗%".
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid.
      rewrite Upd_thr; iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_upd_spec with "[] [] [] [AU]"); try done.
      
      iIntros (res)"HpastW". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }  
      wp_pures. iModIntro. iIntros "%vp_eq_res". subst vp.
      rewrite Upd_thr. wp_pures; try done.
    - rewrite not_true_iff_false in Upd_thr.
      assert (∀ op c c' res, Decision (seq_spec op c c' res)) 
        as seq_spec_dec. { apply seq_spec_dec. }
      destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))
        as [Hss | Hss].
      + 
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
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. rewrite Upd_thr. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                by (clear -tid_notin_R; set_solver).
      by rewrite H'.  
        
      iModIntro.
      wp_apply (dsOp_nupd_spec); try done.
      iIntros (res)"Hres". wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }
      wp_pures. iModIntro. iIntros "->".
      wp_pures. iModIntro. done.
      + 
      iMod (inv_alloc (threadN N) _
              (∃ M T, State γ_sy γ_tk (au N γ_s op Φ) Φ M T op vp T0) 
                                    with "[AU Hc Hreg_sy1]") as "#HthInv".
      { iNext. iExists M0, T0. iFrame "Hreg_sy1".
        iSplitR. { by iPureIntro. }
        iLeft. unfold Pending. iFrame "AU Hc". 
        unfold past_lin. iIntros "%Hpast". 
        destruct Hpast as [t [H' Hss']].
        assert (t = T0) as -> by lia. contradiction. }

      iModIntro. iSplitR "Hproph Token". iNext.
      iExists M0, T0, s0. iFrame "∗%".
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. rewrite Upd_thr. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.
      
      iModIntro. wp_bind (dsOp _ _)%E.
      
      iAssert (update_helping_protocol N γ_t γ_s γ_td γ_ght)%I as "Upd_help".
      { admit. }
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thr_vars".
      { iFrame "#". } 
      wp_apply (dsOp_nupd_spec); try done.
      iIntros (res)"HpastW".
      
      wp_pures.
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                  _ _ _ _ _ _ _ (res))
        with "Hproph"); try done.
      { unfold typed_proph_from_val; simpl. by rewrite resT_proph_resolve. }  
      wp_pures. iModIntro. iIntros "%vp_eq_res". subst vp.
       
      iApply fupd_wp.
      iDestruct "HpastW" as "(%Upd_thr' & HpastW)".
      
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
      
      iAssert (⌜map_max M1 = T1⌝)%I as %M_max1. 
      { by iDestruct "Hist" as (M1') "(_&_&%&_)". }

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
      
      iEval (unfold past_lin_witness) in "HpastW".
      (* iEval (rewrite Upd_thr) in "HpastW".*)

      iDestruct "Hth_or" as "[HPending | HDone]".
      { iDestruct "HPending" as "(AU & Hc & >%HPending)".
        iDestruct "HpastW" as (s) "(HpastW & %Hseq)".
          iDestruct "HpastW" as (t)"(%T0_le_t & Ht)".
          iDestruct "Hist" as (M1') "(H'&H''&H''')".
          iDestruct (history_sync with "[$H''] [$Ht]") as "%M1'_t".
          iDestruct "H'''" as %(H1' & _ & H1'' & H1''').
          apply (H1'' t s) in M1'_t.
          exfalso. apply HPending. exists t.
          split.
          + split; try done. apply elem_of_dom_2 in M1'_t.
            by apply map_max_dom in M1'_t.
          + rewrite !lookup_total_alt. rewrite M1'_t. by simpl. }
      
      iDestruct "HDone" as "(HDone & Hpast)".  
      iDestruct "HDone" as "[HDone | >Hth_or]"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Hth_or]") as "%".
        exfalso; try done. }
        
      iModIntro. iSplitR "HDone Hth_sy Token Hpast".
      iExists M1, T1, s1; iFrame "∗%".
      iNext. iExists R1, hγt1; iFrame.     

      iModIntro. iSplitL "Token Hth_sy Hpast".
      iNext. iExists M1, T1. iFrame "Hth_sy". 
      iSplitR. by iPureIntro. iRight. iFrame "∗%".
      by subst T1.
      
      iModIntro. by wp_pures.
  Admitted.


(*
  Lemma sing_incr_low_spec l N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2:
      ⌜l = l1 ∨ l = l2⌝ -∗
      (ghost_update_protocol N γ_t γ_s γ_td γ_ght) -∗ 
          counter_inv N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2 -∗
              <<< ∀∀ n, Cntr γ_s n >>> 
                     sing_incr #l @ ↑(cntrN N)
              <<< Cntr γ_s (n+1), RET #() >>>.
  Proof.
    iIntros "% Ghost_upd #HInv" (Φ) "AU".
    rename H into l_or.
    wp_lam. wp_bind (!_)%E.
    iInv "HInv" as (T0 n0 M0 M0') "(>Hstate & >HT & >HM' & >M_eq_M' 
              & >HTmax & >HMTstate & >HTdiff & >per_tick 
              & >trans_inv & >resources & Prot)".
    iDestruct "resources" as (a1 a2) "(Hl1 & Hl2 & % & Hauth1 & Hauth2)".
    destruct l_or. 
    - subst l. wp_load. iModIntro. iSplitR "Ghost_upd AU".
      iNext. iExists T0, n0, M0, M0'. iFrame.
      iExists a1, a2; iFrame. by iPureIntro.
      wp_pures. wp_bind (CmpXchg _ _ _)%E.
      iInv "HInv" as (T1 n1 M1 M1') "(>Hstate & >HT & >HM' & >M_eq_M' 
              & >HTmax & >HMTstate & >HTdiff & >per_tick 
              & >trans_inv & >resources & Prot)".
      iDestruct "resources" as (b1 b2) "(Hl1 & Hl2 & % & Hauth1 & Hauth2)".
      destruct (decide (a1 = b1)).
      + subst b1. wp_cmpxchg_suc.
        iMod "AU" as (n') "[HCntr [_ Hcom]]".
        iAssert (⌜n' = n1⌝)%I as "%". { admit. } subst n'.
        iAssert (Cntr γ_s (n1 + 1) ∗ cntr γ_s (n1 + 1))%I
          with "[HCntr Hstate]" as "(HCntr & Hstate)".
        { admit. }
        iMod ("Hcom" with "HCntr") as "HΦ".
        iAssert (own γ_t (● MaxNat (T1+1)))%I
          with "[HT]" as "HT".
        { admit. }
        iAssert (own γ_m (● <[T1+1 := to_agree (n1+1)]> M1'))%I
          with "[HM']" as "HM'".
        { admit. }
        iDestruct "M_eq_M'" as %M_eq_M'.
        iDestruct "HTmax" as %HTmax.
        iDestruct "HTdiff" as %HTdiff.
        iDestruct "HMTstate" as %HMTstate.
        iAssert (⌜map_Forall 
                  (λ k a, a = to_agree (<[(T1+1)%nat := (n1+1)%nat]> M1 !!! k)) 
                  (<[(T1+1)%nat := to_agree (n1+1)%nat]> M1')⌝)%I
          as "M_eq_M'".
        { Search map_Forall. iPureIntro. apply map_Forall_insert. admit.
          rewrite lookup_total_insert. split; first done.
          rewrite map_Forall_lookup in M_eq_M'. apply map_Forall_lookup.
          admit. }
        iAssert (⌜(T1+1)%nat = map_max (<[(T1+1)%nat := (n1+1)%nat]> M1)⌝)%I 
          as "HTmax".
        { admit. }
        iAssert (⌜∀ t, t < (T1+1)%nat → 
          <[(T1+1)%nat := (n1+1)%nat]> M1 !!! t ≠ 
            <[(T1+1)%nat := (n1+1)%nat]> M1 !!! (t + 1)%nat⌝)%I 
          as "HTdiff".
        { admit. }
        iAssert (⌜<[(T1+1)%nat := (n1+1)%nat]> M1 !!! (T1+1)%nat = 
                                                    (n1+1)%nat⌝)%I 
          as "HMTstate".
        { iPureIntro. by rewrite lookup_total_insert. }
        iAssert ([∗ set] t ∈ (dom (<[(T1+1)%nat := (n1+1)%nat]> M1)),
                            per_tick_inv t)%I with "[per_tick]" as "per_tick".
        { admit. }
        iAssert (transition_inv (<[(T1+1)%nat := (n1+1)%nat]> M1) (T1+1))%I
          with "[trans_inv]" as "trans_inv".
        { iDestruct "trans_inv" as %trans_inv. 
          iPureIntro. intros t1 t2 v t1_le_t2 Hpre.
          destruct (decide (v = n1+1)).
          - subst v. exists (T1+1). 
            split; last by rewrite lookup_total_insert.
             admit. }
        iAssert (own γ_l1 (● MaxNat (a1+1)))%I with "[Hauth1]" as "Hauth1".
        { admit. }
          
        
        iSpecialize ("Ghost_upd" $! M1 (T1+1) (n1+1)).
        iAssert (⌜map_max M1 < T1 + 1⌝)%I as
          "Pre_ghost_upd".
        { admit. }
        iMod ("Ghost_upd"  with "[$Pre_ghost_upd] [$Hstate] [$HT] [$Prot]") 
          as "(Prot & Hstate & HT)".
        
        iModIntro. iSplitR "HΦ".
        iNext. iExists (T1+1), (n1+1), (<[(T1+1)%nat := (n1+1)%nat]> M1), 
          (<[(T1+1)%nat := to_agree (n1+1)%nat]> M1').
        iFrame "∗#". iExists (a1+1), b2. iFrame. iSplitL.
        assert (#(a1+1) = #(a1+1)%nat) as ->. { admit. }
        done. iPureIntro. clear -H0. lia.
        wp_pures. by iModIntro.
  Admitted.



  Lemma incr_low_spec N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2:
      (ghost_update_protocol N γ_t γ_s γ_td γ_ght) -∗ 
          counter_inv N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2 -∗
              <<< ∀∀ n, Cntr γ_s n >>> 
                     incr #l1 #l2 @ ↑(cntrN N)
              <<< Cntr γ_s (n+1), RET #() >>>.
  Proof.
    iIntros "Ghost_upd #HInv" (Φ) "AU".
    wp_lam. wp_pures. wp_apply nondet_bool_spec; try done.
    iIntros (b) "_". wp_pures. destruct b.
    - wp_pures. awp_apply ((sing_incr_low_spec l1) with "[] Ghost_upd"); 
      try done. iPureIntro; left; try done.
      iApply (aacc_aupd_commit with "AU"). set_solver.
      iIntros (n) "HCntr".
      iAaccIntro with "HCntr".
      { iIntros "HCntr". iFrame. iModIntro. 
        iIntros "AU"; iFrame. try done. }
      iIntros "HCntr". iModIntro.
      iFrame "HCntr". iIntros "HΦ".
      iModIntro. iFrame.
    - wp_pures. awp_apply ((sing_incr_low_spec l2) with "[] Ghost_upd"); 
      try done. iPureIntro; right; try done.
      iApply (aacc_aupd_commit with "AU"). set_solver.
      iIntros (n) "HCntr".
      iAaccIntro with "HCntr".
      { iIntros "HCntr". iFrame. iModIntro. 
        iIntros "AU"; iFrame. try done. }
      iIntros "HCntr". iModIntro.
      iFrame "HCntr". iIntros "HΦ".
      iModIntro. iFrame.
  Qed.            
*)              
              

(*
  Lemma read_low_spec N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2 t_id t0 :
    counter_inv N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2 -∗
       thread_start γ_t γ_ght t_id t0 -∗ 
        <<< True >>>
           read_low #l1 #l2 @ (↑(cntrN N))
        <<< ∃∃ (s v t: nat), 
              past_state γ_m s 
            ∗ ⌜t0 ≤ t ∧ read_seq_spec s v⌝, 
              RET #v >>>.
  Proof.
    iIntros "#HInv #Hthd_st" (Φ) "AU". wp_lam. wp_pures.
    wp_bind (! _)%E.
    iInv "HInv" as (T0 n0 M0 M0') "(>Hstate & >HT & >HM' & >M_eq_M' 
              & >HTmax & >HMTstate & >HTdiff & >per_tick 
              & >trans_inv & >resources & Prot)".
    iDestruct "resources" as (a1 a2) "(Hl1 & Hl2 & % & Hauth1 & Hauth2)".
    rename H into a1_a2_n0.
    iAssert (own γ_l1 (◯ a1) ∗ own γ_l2 (◯ a2))%I as "(Hfrag1 & Hfrag2)".
    { admit. }
    iAssert (own γ_t (◯ MaxNat T0))%I as "#HfragT".
    { admit. }

    wp_load.
    iAssert (⌜t0 ≤ T0⌝)%I as "%". { admit. }
    rename H into t0_le_T0. 
    iAssert (⌜M0 !!! T0 = n0⌝)%I as "%". 
    { by iDestruct "HMTstate" as "%". }
    rename H into M0_T0_eq_n0.
    iAssert (own γ_m (◯ {[T0 := to_agree n0]})) as "#T0_n0".
    { admit. }
    
    iModIntro. iSplitR "AU". iNext. iExists T0, n0, M0, M0'.  
    iFrame. iExists a1, a2; iFrame. by iPureIntro.
    wp_pures.
    wp_bind (! _)%E.
    iInv "HInv" as (T1 n1 M1 M1') "(>Hstate & >HT & >HM' & >M_eq_M' 
              & >HTmax & >HMTstate & >HTdiff & >per_tick 
              & >trans_inv & >resources & Prot)".
    iDestruct "resources" as (b1 b2) "(Hl1 & Hl2 & % & Hauth1 & Hauth2)".
    rename H into b1_b2_n1.
    wp_load.
    iAssert (⌜M1 !!! T1 = n1⌝)%I as "%". 
    { by iDestruct "HMTstate" as "%". }
    rename H into M1_T1_eq_n1.
    assert (a1 ≤ b1) as a1_le_b1. { admit. }
    assert (a2 ≤ b2) as a2_le_b2. { admit. }
    assert (n0 ≤ a1 + b2 ≤ n1) as n0_ab_n1.
    { rewrite <-a1_a2_n0. rewrite <-b1_b2_n1.
      split; lia. }
    assert (T0 ≤ T1) as T0_le_T1. { admit. }
    assert (M1 !!! T0 = n0) as M1_T0_eq_n0. { admit. }  
    iAssert (transition_inv M1 T1)%I as "%". { done. }
    rename H into Trans_inv.
    pose proof Trans_inv T0 T1 (a1 + b2) as Trans_inv.
    rewrite <-M1_T0_eq_n0 in n0_ab_n1.  
    rewrite <-M1_T1_eq_n1 in n0_ab_n1.
    pose proof Trans_inv T0_le_T1 n0_ab_n1 as Trans_inv.
    destruct Trans_inv as [t [T0_t_T1 M1_t_ab]].  

    iAssert (own γ_m (◯ {[t := to_agree (a1+b2)]})) as "#T1_ab".
    { admit. }
        
    iModIntro. iSplitR "AU". iNext. iExists T1, n1, M1, M1'.  
    iFrame. iExists b1, b2; iFrame. by iPureIntro. wp_pures. 

    iMod "AU" as "[_ [_ Hcomm]]".
    iSpecialize ("Hcomm" $! (a1+b2) (a1+b2) t). 
    iMod ("Hcomm" with "[T1_ab]") as "HΦ".
    { iSplitL "T1_ab". by iExists t. iPureIntro.
      split; try done. lia. }
    iModIntro. 
    assert (#(a1 + b2)%nat = #(a1 + b2)).
    { admit. }
    by rewrite H.   
  Admitted.                 
*)