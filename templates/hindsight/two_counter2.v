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
    rec: "sing_incr" "l" "p" :=
       let: "oldv" := !"l" in
       let: "v" := (Resolve (CmpXchg "l" "oldv" ("oldv" + #1)) "p" #()) in
       if: Snd "v"
         then #0%nat
         else "sing_incr" "l".

  Definition incr: val :=
    λ: "l1" "l2" "p", 
      let: "random" := nondet_bool #() in
       if: "random"
        then sing_incr "l1" "p"
        else sing_incr "l2" "p".
        
  Definition dsOp : val :=
    λ: "OP" "l1" "l2" "p",
      if: "OP" = #0 
      then read "l1" "l2"
      else incr "l1" "l2" "p".

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
    | incrOp => (C' = C + 1) ∧ (res = 0)
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
        << ∀∀ a' res, dsRep γ_r a' 
          ∗ ⌜seq_spec op a a' res⌝, COMM Q #res >>)%I.

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

  Definition Pending P M T op vp t0 : iProp := 
      P ∗ £1 ∗ ¬ past_lin M T op vp t0.

  Definition Done γ_tk (Q: val → iProp) M T op (vp: resT) t0 : iProp := 
      past_lin M T op vp t0 ∗ (Q #vp ∨ Token γ_tk).
  
  Definition State γ_sy γ_tk P Q M T op vp t0: iProp :=
        own γ_sy (to_frac_agree (1/2) M)
      ∗ ⌜T = map_max M⌝ 
      ∗ (Pending P M T op vp t0 ∨ Done γ_tk Q M T op vp t0).

  Definition thread_vars γ_t γ_ght γ_sy t_id t0 : iProp := 
    own γ_ght (◯ {[t_id := to_agree (t0, γ_sy)]}) ∗ own γ_t (◯ MaxNat t0).

  Definition Reg N γ_t γ_r γ_ght t_id M : iProp :=
    ∃ γ_tk γ_sy Q op vp t0 (vtid: val), 
        proph1 t_id vtid
      ∗ thread_vars γ_t γ_ght γ_sy t_id t0
      ∗ own (γ_sy) (to_frac_agree (1/2) M)
      ∗ inv (threadN N) 
        (∃ M T, State γ_sy γ_tk (au N γ_r op Q) Q M T op vp t0).
    
  Definition helping_inv (N: namespace) γ_t γ_r γ_ght M : iProp :=
    ∃ (R: gset proph_id) (hγt: gmap proph_id (agreeR (prodO _ _))),
        own γ_ght (● hγt) ∗ ⌜R = dom hγt⌝
      ∗ ([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_ght t_id M).

  Definition transition_inv (s s': snapshot) : Prop :=
    (s'.1 = (s.1 + 1)%nat ∧ s'.2 = s.2) 
      ∨ (s'.1 = s.1 ∧ s'.2 = (s.2 + 1)%nat).

  Definition resources (s: snapshot) : iProp :=
    l1 ↦ #(s.1) ∗ l2 ↦ #(s.2).
  
  Definition ds_inv (M: gmap nat snapshot) 
    (T: nat) (s: snapshot) : iProp :=
      resources s
    ∗ ⌜∀ t, 0 ≤ t < T → transition_inv (M !!! t) (M !!! (t+1)%nat)⌝.
  
  Definition main_inv N γ_t γ_r γ_m γ_ght : iProp :=
    inv (cntrN N)
    (∃ M T (s: snapshot),
      dsRepI γ_r (abs s) ∗ ⌜M !!! T ≡ s⌝
    ∗ hist γ_t γ_m M T
    ∗ helping_inv N γ_t γ_r γ_ght M
    ∗ ds_inv M T s).

  Definition update_helping_protocol N γ_t γ_r γ_ght : iProp :=
        ∀ M T s, 
          ⌜map_max M < T⌝ -∗   
            dsRep γ_r (abs s) -∗
              helping_inv N γ_t γ_r γ_ght M ={⊤ ∖ ↑cntrN N}=∗
                helping_inv N γ_t γ_r γ_ght (<[T := s]> M) 
                ∗ dsRep γ_r (abs s).

  Definition is_updating (pvs : list (val * val)) : Prop :=
    Exists (λ x, ∃ v1, x.1 = (v1, #true)%V) pvs.
  
  Global Instance is_updating_dec : ∀ pvs, Decision (is_updating pvs).
  Proof.
    intros pvs. rewrite /is_updating. apply Exists_dec. intros [x1 x2].
    rewrite /=. destruct x1.
    - right; intros [v1 H']; try done.
    - right; intros [v1 H']; try done.
    - destruct (decide (x1_2 = #true)) as [-> | Hx1]. 
      + left. by exists x1_1.
      + right. intros [v1 H']. inversion H'. done.
    - right; intros [v1 H']; try done.
    - right; intros [v1 H']; try done.
  Qed.

  Lemma dsOp_spec N γ_t γ_r γ_m γ_ght op r (p: proph_id) pvs 
    γ_sy t_id t0 Q:
          main_inv N γ_t γ_r γ_m γ_ght -∗
          □ update_helping_protocol N γ_t γ_r γ_ght -∗
            {{{ proph p pvs ∗ 
                (⌜is_updating pvs⌝ ∗ au N γ_r op Q ∨
                  ⌜¬ is_updating pvs⌝ ∗ thread_vars γ_t γ_ght γ_sy t_id t0) }}} 
                  dsOp (Op_to_val op) #r #p
            {{{ (res: resT), RET #res; 
                  ⌜is_updating pvs⌝ ∗ Q #res
                ∨ ⌜¬ is_updating pvs⌝ ∗ past_lin_witness γ_m op res t0 }}}.
  Proof.
  Admitted.

  Lemma dsOp_spec' N γ_t γ_r γ_m γ_ght op (p: proph_id) pvs 
    γ_sy t_id t0 Q:
          main_inv N γ_t γ_r γ_m γ_ght -∗
          □ update_helping_protocol N γ_t γ_r γ_ght -∗
            {{{ proph p pvs ∗ 
                (⌜is_updating pvs⌝ ∗ au N γ_r op Q ∨
                  ⌜¬ is_updating pvs⌝ ∗ thread_vars γ_t γ_ght γ_sy t_id t0) }}} 
                  dsOp (Op_to_val op) #l1 #l2 #p
            {{{ (res: resT), RET #res; 
                  ⌜is_updating pvs⌝ ∗ Q #res
                ∨ ⌜¬ is_updating pvs⌝ ∗ past_lin_witness γ_m op res t0 }}}.
  Proof.
    iIntros "#HInv #HUpd" (Φ) "!# (Proph&Hor) Hpost".
    wp_lam. wp_pures. destruct op; wp_pures.
    - admit.
    - wp_lam; wp_pures. wp_apply nondet_bool_spec; try done.
      iIntros (b) "_". wp_pures. destruct b; wp_pures.
      + wp_lam; wp_pures. wp_bind (! _)%E.
        iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
        iDestruct "Templ" as "(Res & %Htrans0)".
        iDestruct "Res" as "(Hl1 & Hl2)".
        destruct s0 as [a0 b0]. iSimpl in "Hl1 Hl2".
        wp_load. iModIntro. iSplitR "Hor Proph Hpost".
        { iNext. iExists M0, T0, (a0, b0). iFrame "#∗%". }
        wp_pures. wp_bind (Resolve _ _ _)%E.
        iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
        iDestruct "Templ" as "(Res & %Htrans1)".
        iDestruct "Res" as "(Hl1 & Hl2)".
        destruct s1 as [a1 b1]. iSimpl in "Hl1 Hl2".
        destruct (decide (a1 = a0)) as [-> | Ha01].
        * wp_apply (wp_resolve_cmpxchg_suc with "[$Hl1 $Proph]").
          { by left. }
          iIntros "H'". iDestruct "H'" as  (pvs')"(%Def_pvs & Proph & Hl1)".
          iDestruct "Hor" as "[Hor | Hor]"; last first.
          { iDestruct "Hor" as "(%H'&_)". rewrite /is_updating in H'.
            apply Forall_Exists_neg in H'. rewrite Def_pvs in H'. 
            apply Forall_inv in H'. exfalso; apply H'. simpl. by exists #a0. }
          iDestruct "Hor" as "(%Hupd&AU)".
          iMod "AU" as (s)"[DsR [_ Hcomm]]". 
          assert (s = abs (a0, b1)) as ->. admit.
          iAssert (dsRep γ_r (abs (a0+1, b1)) ∗ dsRepI γ_r (abs (a0+1, b1)))%I
            with "[DsR Ds]" as "(DsR & Ds)".
          { admit. }
          iSpecialize ("Hcomm" $! (abs (a0+1, b1)) 0).
          iMod ("Hcomm" with "[$DsR]") as "HQ".
          { iPureIntro. rewrite /seq_spec /abs. lia. }
          set s: snapshot := (a0+1, b1).
          set M1' := <[T1+1 := s]> M1.
          assert (transition_inv (a0, b1) s) as Htr.
          { rewrite /s /transition_inv /=. by left. }
          iAssert (hist γ_t γ_m M1' (T1+1))%I with "[Hist]" as "Hist".
          { admit. }
          unfold update_helping_protocol. 
          iSpecialize ("HUpd" $! M1 (T1+1) s).
          iAssert (⌜map_max M1 < T1+1⌝)%I as "H'". admit.
          iPoseProof ("HUpd" with "[$H'] [$Ds] [$Help]") as ">(Help&Ds)".
          iModIntro. iSplitR "HQ Proph Hpost". iNext. iExists M1', (T1+1), s.
          iFrame. iSplitR. iPureIntro. by rewrite /M1' lookup_total_insert.
          rewrite /s /=. assert (#(a0+1)%nat = #(a0+1)) as ->.
          { repeat apply f_equal. lia. } iFrame "Hl1". 
          iPureIntro. admit.
          wp_pures. iApply "Hpost". iModIntro. iLeft. iFrame "∗%".
        * wp_apply (wp_resolve_cmpxchg_fail with "[$Hl1 $Proph]").
          { intros H'; inversion H'. apply Ha01. done. }
          
          
          
          
          
  Admitted.
  
  Definition dsOp' : val :=
    λ: "OP" "r",     
      let: "t_id" := NewProph in
      let: "p_upd" := NewProph in
      let: "p" := NewProph in
      let: "v" := dsOp "OP" "r" "p_upd" in
      resolve_proph: "p" to: "v";;
      "v".


  Lemma dsOp'_spec N γ_t γ_r γ_m γ_ght op (r: loc) :
          main_inv N γ_t γ_r γ_m γ_ght -∗
              <<< ∀∀ a, dsRep γ_r a >>> 
                     dsOp' (Op_to_val op) #r @ ↑(cntrN N) ∪ ↑(threadN N)
              <<< ∃∃ a' res, dsRep γ_r a' ∗ ⌜seq_spec op a a' res⌝, 
                  RET #res >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. 
    wp_pure credit:"Hc". wp_pure credit:"Hc'". wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (pvs p1)"Hproph1". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 resTTypedProph); first done.
    iIntros (vp p2) "Hproph2". wp_pures.
    
    iAssert (update_helping_protocol N γ_t γ_r γ_ght)%I 
        as "Upd_help". 
    { iIntros (M T s)"%Map_max Ds Prot".
      iDestruct "Prot" as (R G)"(HG & Domm_G & Hstar)".
      iAssert (dsRep γ_r (abs s) -∗
        ([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_ght t_id M) ={⊤ ∖ ↑cntrN N}=∗
        (([∗ set] t_id ∈ R, Reg N γ_t γ_r γ_ght t_id (<[T:=s]> M))
        ∗ dsRep γ_r (abs s)))%I as "H'".
      { iIntros "Ds". 
        iInduction R as [|tid' R' tid_notin_R IH] "HInd" using set_ind_L; 
          auto using big_sepS_empty'.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        rewrite (big_sepS_delete _ ({[tid']} ∪ R') tid'); last by set_solver.
        assert (({[tid']} ∪ R') ∖ {[tid']} = R') as HR'. set_solver. rewrite HR'.
        iIntros "(Htid & Hbigstar)". 
        iMod ("HInd" with "[$Ds] Hbigstar") as "(H' & Ds)". iFrame "H'". 
        iDestruct "Htid" as (γ_tk' γ_sy' Q' op' vp' t0' vtid')
          "(Hproph & #Hthd & Hsy & #HthInv)".
        iInv "HthInv" as (M'' T'')"Hstate".
        iDestruct "Hstate" as "(>Hsy' & >%Map_max'' & Hstate)".
        assert (M'' = M) as ->. admit.
        iAssert (own γ_sy' (to_frac_agree (1 / 2) (<[T:=s]> M))
          ∗ own γ_sy' (to_frac_agree (1 / 2) (<[T:=s]> M)))%I
          with "[Hsy Hsy']" as "(Hsy & Hsy')".
        { admit. }
        iDestruct "Hstate" as "[HPending | HDone]".
        - iDestruct "HPending" as "(AU & >Hc & >%Past_W)".
          destruct (decide (seq_spec op' (abs s) (abs s) vp'))
            as [Hss | Hss].
          + iApply (lc_fupd_add_later with "Hc"). iNext.
            iMod "AU" as (c) "[DsR [_ Hcomm]]".
            iAssert (⌜c = abs s⌝)%I as "%". 
            { unfold dsRep, dsRepI. Search own valid.
              iDestruct (own_valid_2 with "[$Ds] [$DsR]") as %H'.
              rewrite frac_agree_op_valid_L in H'.
              destruct H' as [_ H']; by iPureIntro. } subst c. 
            iSpecialize ("Hcomm" $! (abs s) vp'). 
            iMod ("Hcomm" with "[DsR]") as "HΦ".
            { iFrame. by iPureIntro. }
            iModIntro. iSplitL "Hsy HΦ". iNext. iExists (<[T:=s]> M), T.
            iFrame. iSplitR. admit. iRight. iSplitR. 
            iPureIntro. exists T. split. split; try done. admit.
            by rewrite lookup_total_insert. by iLeft.
            iModIntro. iFrame.
            iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
            iFrame "∗#%".
          + iModIntro. iSplitL "AU Hc Hsy". iNext. iExists (<[T:=s]> M), T.
            iFrame. iSplitR. admit. iLeft. iFrame. iPureIntro. 
            intros [t Ht]. admit.
            iModIntro. iFrame.
            iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
            iFrame "∗#%".
        - iDestruct "HDone" as "(>%PastW & HDone)".
          iModIntro. iSplitL "HDone Hsy". iNext. 
          iExists (<[T:=s]> M), T.
          iFrame. iSplitR. admit. iRight. iSplitR.
          iPureIntro. admit. iFrame.
          iModIntro. iFrame. iExists γ_tk', γ_sy', Q', op', vp', t0', vtid'.
          iFrame "∗#%". }
      iPoseProof ("H'" with "[$Ds] [$Hstar]") as ">(Hstar & Ds)".
      iModIntro. iFrame. iExists R, G. iFrame. }
    
    destruct (decide (is_updating pvs)) as [Hpvs | Hpvs].
    - wp_apply (dsOp_spec with "[] [] [AU Hproph1]"); try done.
      { iFrame "Hproph1". iLeft. iFrame "AU %". }
      iIntros (res)"Hor". iDestruct "Hor" as "[Hor | Hor]"; last first.
      { iDestruct "Hor" as "(% & _)". exfalso; try done. }
      iDestruct "Hor" as "(_&HΦ)". wp_pures. 
      wp_apply (typed_proph_wp_resolve1 resTTypedProph with "Hproph2"); try done.
      wp_pures. iModIntro. iIntros "_". wp_pures. done.
    - iApply fupd_wp. 
      iInv "HInv" as (M0 T0 s0) "(>Ds & >%Habs0 & >Hist & Help & >Templ)".
      iApply (lc_fupd_add_later with "Hc"). iNext. 
      iDestruct "Help" as (R0 G0)"(HG & %Domm_G0 & Hstar)".
      
      iAssert (¬ ⌜tid ∈ R0⌝)%I as %tid_notin_R0.
      { admit. }
            
      iMod (own_alloc (to_frac_agree (1) (M0))) 
              as (γ_sy)"Hfr_t". { try done. }        
      iEval (rewrite <-Qp.half_half) in "Hfr_t".      
      iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hfr_t". 
      iDestruct "Hfr_t" as "(Hreg_sy1 & Hreg_sy2)".  

      iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.

      set (<[ tid := to_agree (T0, γ_sy) ]> G0) as G0'.
      iDestruct (own_update _ _ 
        (● G0' ⋅ ◯ {[ tid := to_agree (T0, γ_sy) ]})
               with "HG") as ">HG".
      { apply auth_update_alloc. rewrite /G0'.
        apply alloc_local_update; last done. apply not_elem_of_dom.
        by rewrite Domm_G0 in tid_notin_R0. }
      iDestruct "HG" as "(HG & #Hreg_gh)".

      iAssert (⌜map_max M0 = T0⌝)%I as %M_max. 
      { by iDestruct "Hist" as (M0') "(_&_&%&_)". }
      iDestruct "Hist" as (M0')"(H'&H'')".
      iDestruct (own_update _ _ (● (MaxNat T0) ⋅ ◯ (MaxNat T0)) with "H'") 
        as ">H1'".
      { apply auth_update_alloc. apply max_nat_local_update. try done. }
      iDestruct "H1'" as "(H' & #HfragT0)".
      iAssert (hist γ_t γ_m M0 T0) with "[H' H'']" as "Hist".
      { iExists M0'; iFrame. }
      
      iAssert (|={⊤ ∖ ↑cntrN N}=> dsRepI γ_r (abs s0) ∗ 
        (inv (threadN N) (∃ M T, State γ_sy γ_tk (au N γ_r op Φ) Φ M T op vp T0)))%I
        with "[Ds AU Hc' Hreg_sy1]" as "H'".
      { destruct (decide (seq_spec op (abs (M0 !!! T0)) (abs (M0 !!! T0)) vp))
          as [Hss | Hss].
        - iMod "AU" as (c) "[DsR [_ Hcomm]]".
          iAssert (⌜c = abs s0⌝)%I as "%". 
          { unfold dsRep, dsRepI.
            iDestruct (own_valid_2 with "[$Ds] [$DsR]") as %H'.
            rewrite frac_agree_op_valid_L in H'.
            destruct H' as [_ H']; by iPureIntro. } subst c. 
          iSpecialize ("Hcomm" $! (abs s0) vp). 
          iMod ("Hcomm" with "[DsR]") as "HΦ".
          { iFrame. apply leibniz_equiv in Habs0. 
            rewrite Habs0 in Hss. by iPureIntro. }
        
          iAssert (past_lin M0 T0 op vp T0)%I as "Hpast".
          { iPureIntro. exists T0. split; try done. }
          
          iMod (inv_alloc (threadN N) _ 
            (∃ M T, State γ_sy γ_tk (au N γ_r op Φ) Φ M T op vp T0) 
            with "[HΦ Hreg_sy1]") as "#HthInv".
          { iNext. iExists M0, T0. iFrame. iSplitR. by iPureIntro.
            iRight. iSplitR. iFrame "#". by iLeft. }
          iModIntro; iFrame "∗#".
        - iMod (inv_alloc (threadN N) _ 
           (∃ M T, State γ_sy γ_tk (au N γ_r op Φ) Φ M T op vp T0) 
            with "[AU Hc' Hreg_sy1]") as "#HthInv".
          { iNext. iExists M0, T0. iFrame. iSplitR. by iPureIntro.
            iLeft. iFrame "AU Hc'". iPureIntro. intros [t [Ht Hss']].
            assert (t = T0) as -> by lia. done. }
          iModIntro; iFrame "∗#". }
      iDestruct "H'" as ">(Ds & #HthInv)".

      iModIntro. iSplitR "Hproph1 Hproph2 Token". iNext.
      iExists M0, T0, s0. iFrame "∗%".
      iExists (R0 ∪ {[tid]}), G0'. iFrame.
      iSplitR. iPureIntro. subst G0'. rewrite dom_insert_L.
      clear -Domm_G0; set_solver.
      rewrite (big_sepS_delete _ (R0 ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar". 
      iExists γ_tk, γ_sy, Φ, op, vp, T0, vtid. iFrame "∗#".
      assert ((R0 ∪ {[tid]}) ∖ {[tid]} = R0) as H' 
                by (clear -tid_notin_R0; set_solver).
      by rewrite H'.
      
      iAssert (thread_vars γ_t γ_ght γ_sy tid T0)%I as "#Thd".
      { iFrame "#". }
    
      iModIntro. wp_apply (dsOp_spec with "[] [] [Hproph1]"); try done.
      { iFrame "Hproph1". iRight. iFrame "#%". }
      
      iIntros (res)"Hor". iDestruct "Hor" as "[Hor | Hor]".
      { iDestruct "Hor" as "(%&_)"; exfalso; try done. }
      
      iDestruct "Hor" as "(_&PastW)".
      wp_pures. 
      wp_apply ((typed_proph_wp_resolve1 resTTypedProph 
                _ _ _ _ _ _ _ (res))
        with "Hproph2"); try done.
      { unfold typed_proph_from_val; simpl. apply f_equal. lia. }
    
      wp_pures. iModIntro. iIntros "<-". wp_pure credit: "Hc1". 
      wp_pure credit: "Hc2". 
      iInv "HInv" as (M1 T1 s1) "(>Ds & >%Habs1 & >Hist & Help & >Templ)".
      iApply (lc_fupd_add_later with "Hc1"). iNext. 
      iDestruct "Help" as (R1 G1)"(HG & %Domm_G1 & Hstar)".
      
      iAssert (⌜tid ∈ R1⌝)%I as "%tid_in_R1".
      { iPoseProof (own_valid_2 _ _ _ with "[$HG] [$Hreg_gh]") as "%H'".
        apply auth_both_valid_discrete in H'. destruct H' as [H' _].
        apply dom_included in H'. rewrite dom_singleton_L -Domm_G1 in H'.
        iPureIntro. clear -H'; set_solver. }
    
      iAssert (⌜map_max M1 = T1⌝)%I as %M_max1. 
      { by iDestruct "Hist" as (M1') "(_&_&%&_)". }
      
      iInv "HthInv" as (M1_th T1_th)"(>Hth_sy & >% & Hth_or)".
      iApply (lc_fupd_add_later with "Hc2"). iNext. 
      assert (M1_th = M1) as ->. admit.
      assert (T1_th = T1) as ->. admit.
      iDestruct "Hth_or" as "[HPending | HDone]".
      { iDestruct "HPending" as "(_&_&%HPending)".
        iDestruct "PastW" as (s) "(#PastW & %Hseq)".
        iDestruct "PastW" as (t)"(%T0_le_t & Ht)".
        iDestruct "Hist" as (M1') "(H'&H''&H''')". admit. }
    
      iDestruct "HDone" as "(#PastW' & HDone)".
      iDestruct "HDone" as "[HΦ | Token']"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Token']") as "%".
        exfalso; try done. }
      
      iModIntro. iSplitL "Hth_sy Token".
      iNext. iExists M1, T1. iFrame "Hth_sy %". iRight. iFrame "#". by iRight.
      iModIntro. iSplitR "HΦ".  
      iNext. iExists M1, T1, s1; iFrame "∗%".
      iExists R1, G1; iFrame "∗%".
      done. Unshelve. done. done. done. done.
  Admitted.



End two_counter.