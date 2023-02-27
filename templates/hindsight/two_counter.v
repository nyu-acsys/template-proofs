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
       then "oldv"
       else "sing_incr" "l".

Definition incr: val :=
  λ: "l1" "l2", 
    let: "random" := nondet_bool #() in
     if: "random"
      then sing_incr "l1"
      else sing_incr "l2".

Definition counterOp : val :=
  λ: "n" "l1" "l2",     
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "v" := 
      if: "n" = "0" 
        then read "l1" "l2"
        else if: "n" = "1" then incr "l1" "l2"
        else #() in
    resolve_proph: "p" to: "v";;
    "v".


(** Proof Setup **)

(* RAs used in proof *)

Definition auth_natUR := authUR $ max_natUR.
Definition frac_natR := dfrac_agreeR $ natUR.
Definition map_natR := authR $ gmapUR nat $ agreeR $ prodR natR natR.
Definition tokenUR := exclR unitO.
Definition frac_mapR := dfrac_agreeR $ gmapUR nat (prodR natUR natUR).
Definition set_tidR := authR (gsetUR proph_id). 
Definition thread_viewR := authUR $ gmapUR proph_id $ agreeR $ 
                                                        prodO natO gnameO.

Class cntrG Σ := CNTR {
                  cntr_auth_natG :> inG Σ auth_natUR;
                  cntr_frac_natG :> inG Σ frac_natR;
                  cntr_map_natG :> inG Σ map_natR;
                  cntr_tokenG :> inG Σ tokenUR;
                  cntr_frac_mapG :> inG Σ frac_mapR;
                  cntr_set_tidG :> inG Σ set_tidR;
                  cnrt_thread_viewG :> inG Σ thread_viewR;
                 }.
                 
Definition cntrΣ : gFunctors :=
  #[ GFunctor auth_natUR; GFunctor frac_natR; GFunctor map_natR;
     GFunctor tokenUR; GFunctor frac_mapR; GFunctor set_tidR;
     GFunctor thread_viewR ].
  
Instance subG_cntrΣ {Σ} : subG cntrΣ Σ → cntrG Σ.
Proof. solve_inG. Qed.

(* Data structure specific definitions *)
Inductive Op := readOp | incrOp.
Definition snapshot : Type := nat * nat.
Definition absT : Type := nat.
Definition resT : Type := nat.
Definition seq_spec (op : Op) (s s': absT) (res: resT) : Prop :=
  match op with
  | readOp => s' = s ∧ res = s
  | incrOp => s' = s + 1 ∧ res = s end.
Parameter abs : snapshot -> absT.  
  
Instance seq_spec_dec : ∀ op s s' res, Decision (seq_spec op s s' res).
Proof.
Admitted.  

Section counter.
  Context {Σ} `{!heapGS Σ, !cntrG Σ}.
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
    ∗ ⌜map_Forall (λ k a, a = to_agree (M !!! k)) M'⌝  
    ∗ ⌜T = map_max M⌝   
    ∗ ⌜∀ t, t < T → M !!! t ≠ M !!! (t+1)%nat⌝.
  
  Definition cntr γ_s (n: nat) : iProp := 
    own γ_s (to_frac_agree (1/2) n).
  
  Definition Cntr γ_s (n: nat) : iProp := 
    own γ_s (to_frac_agree (1/2) n).

(*  
  Definition per_tick_inv (t: nat) : iProp := True. 
    
  Definition transition_inv (M: gmap nat nat) (T: nat) : iProp :=
    ⌜∀ (t1 t2: nat) (v: nat), t1 ≤ t2 → 
                                M !!! t1 ≤ v ≤ M !!! t2 → 
                                  ∃ (t: nat), t1 ≤ t ≤ t2 ∧ M !!! t = v⌝.
  
  Definition resources γ_l1 γ_l2 l1 l2 (n1 n2 n: nat) : iProp :=
    l1 ↦ #n1 ∗ l2 ↦ #n2 ∗ ⌜(n1 + n2 = n)%nat⌝
    ∗ own γ_l1 (● MaxNat n1) ∗ own γ_l2 (● MaxNat n2).
*)
    
 (** Helping Inv **)
  
  Definition au N γ_s op (Q : val → iProp) := 
    (AU << ∃∃ n, Cntr γ_s n >> 
          @ ⊤ ∖ (↑(cntrN N) ∪ ↑(threadN N)), ∅
        << ∀∀ n' res, Cntr γ_s n' ∗ ⌜seq_spec op n n' res⌝, COMM Q #res >>)%I.
        
  Definition past_lin M T op res t0 : iProp :=
    ⌜∃ t, t0 ≤ t ≤ T ∧ seq_spec op (abs (M !!! t)) (abs (M !!! t)) res⌝.

  Definition Pending (P: iProp) M T op vp t0 : iProp := 
    P ∗ £ 1 ∗ ¬ past_lin M T op vp t0.

  Definition Done γ_tk (Q: val → iProp) M T op (vp: nat) t0 : iProp := 
      (Q #vp ∨ own γ_tk (Excl ())) ∗ past_lin M T op vp t0.

  Definition State γ_sy γ_tk P Q M T op vp t0 : iProp :=
      own γ_sy (to_frac_agree (1/2) M)
    ∗ ⌜T = map_max M⌝ 
    ∗ (Pending P M T op vp t0 ∨ Done γ_tk Q M T op vp t0).

  Definition thread_vars γ_t γ_ght γ_sy t_id t0 : iProp := 
    own γ_ght (◯ {[t_id := to_agree (t0, γ_sy)]}) ∗ own γ_t (◯ MaxNat t0).

  Definition Reg N γ_t γ_s γ_ght t_id M : iProp :=
    ∃ γ_tk γ_sy Q op (vp t0: nat) (vtid: val), 
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
    (∃ M T n,
      cntr γ_s n ∗ ⌜abs (M !!! T) = n⌝
    ∗ hist γ_t γ_m M T
    ∗ helping_inv N γ_t γ_s γ_td γ_ght M
    ∗ template_inv M T).
    
  Definition ghost_update_protocol N γ_t γ_s γ_td γ_ght : iProp :=
        ∀ M T n n1 n2, 
          ⌜map_max M = T⌝ -∗   
            cntr γ_s n -∗ own γ_t (● MaxNat T) -∗ 
              helping_inv N γ_t γ_s γ_td γ_ght M ={⊤ ∖ ↑cntrN N}=∗
                helping_inv N γ_t γ_s γ_td γ_ght (<[T := (n1, n2)]> M) 
                ∗ cntr γ_s n ∗ own γ_t (● MaxNat T).

  (** Low-level specs *)
    
  Definition thread_start γ_t γ_ght t_id t0 : iProp := 
    ∃ γ_sy, thread_vars γ_t γ_ght t_id t0 γ_sy.
  
  Definition past_state γ_m (s: snapshot) : iProp :=
    ∃ t, own γ_m (◯ {[t := to_agree s]}).

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
*)


  Lemma incr_low_spec N γ_s γ_t γ_m γ_td γ_ght template_inv l1 l2:
      (ghost_update_protocol N γ_t γ_s γ_td γ_ght) -∗ 
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
              <<< ∀∀ n, Cntr γ_s n >>> 
                     incr #l1 #l2 @ ↑(cntrN N)
              <<< Cntr γ_s (n+1), RET #() >>>.
  Proof.
  (*  
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
  Admitted.              
              
  Lemma incr_high_spec N γ_s γ_t γ_m γ_td γ_ght template_inv l1 l2 :
          ds_inv N γ_t γ_s γ_m γ_td γ_ght template_inv -∗
              <<< ∀∀ n, Cntr γ_s n >>> 
                     incr #l1 #l2 @ ↑(cntrN N)
              <<< Cntr γ_s (n+1), RET #() >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU".
    iAssert (ghost_update_protocol N γ_t γ_s γ_td γ_ght)%I 
                  as "Ghost_updP".
    { iIntros (M T n n1 n2)"HmaxM_T".
      iDestruct "HmaxM_T" as %HmaxM_T.
      iIntros "Hcntr HT Prot". 
      iDestruct "Prot" as (R hγt)"(HR & Hγt & Domm_hγt & Hstar_reg)".
      iAssert (|={⊤ ∖ ↑cntrN N}=> 
                ([∗ set] t_id ∈ R, Reg N γ_t γ_s γ_ght t_id (<[T := (n1, n2)]> M)) 
                ∗ cntr γ_s n ∗ own γ_t (● MaxNat T))%I 
                with "[Hstar_reg Hcntr HT]" 
                as ">(Hstar_reg & Hcntr & HT)".
      { iInduction R as [|tid R' tid_notin_R IH] "HInd" using set_ind_L.
        { iModIntro. iFrame. auto using big_sepS_empty'. } 
        rewrite (big_sepS_delete _ ({[tid]} ∪ R') tid); last by set_solver.
        rewrite (big_sepS_delete _ ({[tid]} ∪ R') tid); last by set_solver.
        assert (({[tid]} ∪ R') ∖ {[tid]} = R') as HR'. set_solver.
        rewrite HR'.
        iDestruct "Hstar_reg" as "(Htid & Hbigstar)". 
        iMod ("HInd" with "[$Hbigstar] [$Hcntr] [$HT]") 
          as "(H' & Hcntr & HT)".
        iFrame "H'".
        iDestruct "Htid" as (γ_tk γ_sy Q op vp t0 vtid)
              "(Hreg_proph & Hreg_gh & Hreg_sy & #Hthinv)".
        iInv "Hthinv" as (M' T')"Hstate".
        iDestruct "Hstate" as "(>Hth_sy & >% & Hstate)".
        iAssert (⌜M' = M⌝)%I as "%". 
        { iPoseProof (own_valid_2 _ _ _ with "[$Hth_sy] [$Hreg_sy]") as "V_H".
          iDestruct "V_H" as %V_H.
          apply frac_agree_op_valid in V_H. destruct V_H as [_ V_H].
          apply leibniz_equiv_iff in V_H.
          by iPureIntro. } subst M'.
        iAssert (⌜T' = T⌝)%I as "%". { admit. } subst T'.
        iCombine "Hreg_sy Hth_sy" as "H'". 
        iEval (rewrite <-frac_agree_op) in "H'".
        iEval (rewrite Qp.half_half) in "H'".
        iMod ((own_update (γ_sy) (to_frac_agree 1 M) 
                  (to_frac_agree 1 (<[T := n]> M))) with "[$H']") as "H'".
        { apply cmra_update_exclusive. 
          unfold valid, cmra_valid. simpl. 
          unfold prod_valid_instance.
          split; simpl; try done. }
        iEval (rewrite <-Qp.half_half) in "H'".
        iEval (rewrite frac_agree_op) in "H'".  
        iDestruct "H'" as "(Hreg_sy & Hth_sy)".
        
        iAssert (⌜t0 ≤ T⌝)%I as %t0_le_T. { admit. }

        iDestruct "Hstate" as "[Hpending | Hdone]".
        - iDestruct "Hpending" as "(AU & >Hc & >%)".
          rename H into HPending.
          destruct (decide (seq_spec op n n vp)) 
            as [Hss | Hss_neg].
          + iMod (lc_fupd_elim_later with "Hc AU") as "AU".
            iMod "AU" as (n')"[Cntr [_ Hclose]]".
            iAssert (⌜n' = n⌝)%I as "%".
            { admit. } subst n'.
            iSpecialize ("Hclose" $! n vp).  
            iMod ("Hclose" with "[Cntr]") as "HQ".
            { iFrame "Cntr". iPureIntro. done. }
            iModIntro. iSplitL "Hth_sy HQ".
            * iNext. iExists (<[T:=(n1, n2)]> M), T. iFrame "∗%". 
              admit.
              (*
              iRight. iSplitL. by iLeft.
              iPureIntro. exists T.
              assert (map_max (<[T:=n]> M) = T) as H'.
              { admit. } rewrite H'.
              split; try done.
              *)
            * iModIntro. iFrame. 
              iExists γ_tk, γ_sy, Q, op, vp, t0, vtid.
              iFrame "∗#".
          + iModIntro. iSplitL "Hth_sy AU".
            * iNext. iExists (<[T:=n]> M), T. iFrame. 
              admit.
              (*
              iLeft. iFrame.
              iPureIntro. intros t.
              assert (map_max (<[T:=n]> M) = T) as H'.
              { admit. } rewrite H'.
              assert (map_max M = T - 1) as H''.
              { admit. } 
              destruct (decide (t = T)).
              ** subst t. intros _; try done.
              ** intros t0_le_t. 
                 assert (t0 ≤ t ≤ map_max M) as Ht.
                 { split. destruct t0_le_t as [H''' _]; try done.
                   rewrite H''. clear -n0 t0_le_t. lia. }
                 rewrite lookup_total_insert_ne; last done.  
                 apply (HPending t Ht).
              *)   
            * iModIntro. iFrame. 
              iExists γ_tk, γ_sy, Q, op, vp, t0, vtid.
              iFrame "∗#".
        - iModIntro.
          iSplitR "Hreg_proph Hreg_sy Hreg_gh Hcntr HT".
          iNext. iExists (<[T := n]> M). iFrame.
          (*
          iRight. iDestruct "Hdone" as "(HQ & %)".
          destruct H as [t [H' H'']].
          iFrame "HQ". iPureIntro.
          exists t. assert (map_max M < map_max (<[T := n]> M)).
          { admit. } split.
          * split; first by destruct H' as [H' _]. lia.
          * assert (<[T:=n]> M !!! t = M !!! t) as H'''. 
            { rewrite lookup_total_insert_ne; try done. admit. }
            by rewrite H'''.
          * iModIntro. iFrame. 
            iExists P, Q, γ_tk, γ_sy, t0, vp, vtid.
            iFrame "∗#".*)
          admit.   }
      
      iModIntro. iFrame "Hcntr HT".
      iExists R, hγt. iFrame. }
    awp_apply incr_low_spec; try done.
    iApply (aacc_aupd_commit with "AU"). set_solver.
    iIntros (n) "Hcntr". 
    iAaccIntro with "Hcntr". 
    { iIntros "HCntr". iModIntro.
      iFrame "HCntr". eauto. }
    iIntros "HCntr". iModIntro.
    iFrame "HCntr". iIntros "HΦ".
    by iModIntro.   
  Admitted.            


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

  (** High-level specs *)
    
  Lemma read_high_spec N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2 :
    counter_inv N γ_s γ_t γ_m γ_td γ_ght γ_l1 γ_l2 l1 l2 -∗
      <<< ∀∀ n, Cntr γ_s n >>>
          read_high #l1 #l2 @ (↑(cntrN N) ∪ ↑(threadN N))
      <<< ∃∃ v, Cntr γ_s n ∗ ⌜read_seq_spec n v⌝, RET #v >>>.
  Proof.
    iIntros "#HInv" (Φ) "AU". wp_lam. wp_pures.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vtid)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 NatTypedProph); first done.
    iIntros (vp p)"Hproph". wp_pures.
    iApply fupd_wp.
    iInv "HInv" as (T0 n0 M0 M0') "(>Hstate & >HT & >HM' & >M_eq_M' 
              & >HTmax & >HMTstate & >HTdiff & >per_tick 
              & >trans_inv & >resources & Prot)".
    iDestruct "Prot" as (R hγt)"(>HR & >Hγt 
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
      - iFrame. iNext. by iPureIntro. }
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

    iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".    
    iMod (own_alloc (Excl ())) as (γ_tk) "Token"; first try done.

    assert (map_max M0 = T0) as M_max. { admit. }
    assert (M0 !!! T0 = n0) as M_T_eq_n. { admit. }
    iAssert (own γ_t (◯ (MaxNat T0))) as "HfragT0".
    { admit. }
    
    destruct (decide (read_seq_spec n0 vp)) as [rss | neg_rss].
    - iDestruct ("AU_back" with "AU") as ">AU".
      iMod "AU" as (n) "[Cntr [_ Hcomm]]".
      iAssert (⌜n = n0⌝)%I as "%". { admit. } subst n. 
      iSpecialize ("Hcomm" $! vp). 
      iMod ("Hcomm" with "[Cntr]") as "HΦ".
      { iFrame. by iPureIntro. }
      iMod (inv_alloc (threadN N) _
              (∃ M, State γ_sy tid γ_tk AU_later (Φ) T0 vp M) 
                                    with "[Token Hreg_sy1]") as "#HthInv".
      { iNext. iExists M0. iFrame "Hreg_sy1".
        iRight. iFrame. iPureIntro.
        exists T0; split. lia. subst n0. try done. }
      
      iModIntro. iSplitR "Hproph HΦ". iNext.
      iExists T0, n0, M0, M0'.  iFrame.
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists AU_later, Φ, γ_tk, γ_sy, T0, vp, vtid. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.  
        
      iModIntro.
      awp_apply read_low_spec without "HΦ"; try done.
      iExists γ_sy. iFrame "Hreg_gh HfragT0".
      iAaccIntro with ""; try done.
      { iIntros "_". iModIntro; try eauto with iFrame. } 
      iIntros (s v t) "(Hpast_state & %)". rename H into t0_le_t.
      iModIntro. iIntros "HΦ". wp_pures.
      wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph"); 
        try done.
      wp_pures. iModIntro. iIntros "%". rename H into vp_eq_v. 
      assert (vp = v). { clear -vp_eq_v. lia. } 
      clear vp_eq_v. wp_pures. iModIntro. by subst vp.
    - iMod (inv_alloc (threadN N) _
              (∃ M, State γ_sy tid γ_tk AU_later (Φ) T0 vp M) 
                                    with "[AU Hreg_sy1]") as "#HthInv".
      { iNext. iExists M0. iFrame "Hreg_sy1".
        iLeft. iFrame. iPureIntro.
        intros t. rewrite M_max.
        intros Ht. assert (t = T0) by lia; subst t.
        subst n0. try done. }

      iModIntro. iSplitR "Hproph Token". iNext.
      iExists T0, n0, M0, M0'.  iFrame.
      iExists (R ∪ {[tid]}), hγt'. iFrame.
      iSplitR. iPureIntro. subst hγt'.
      apply leibniz_equiv. rewrite dom_insert.
      rewrite Domm_hγt. clear; set_solver.
      rewrite (big_sepS_delete _ (R ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar_reg". unfold Reg.
      iExists AU_later, Φ, γ_tk, γ_sy, T0, vp, vtid. iFrame "∗#".
      assert ((R ∪ {[tid]}) ∖ {[tid]} = R) as H' 
                  by (clear -tid_notin_R; set_solver).
      by rewrite H'.

      iModIntro.
      awp_apply read_low_spec; try done.
      iExists γ_sy. iFrame "Hreg_gh HfragT0".
      iAaccIntro with ""; try done.
      { iIntros "_". iModIntro; try eauto with iFrame. }
      iIntros (s v t) "(Hpast_state & H)".
      iDestruct "H" as %[T0_le_t Hrss].
      
      iModIntro. wp_pures.
      wp_apply (typed_proph_wp_resolve1 NatTypedProph with "Hproph");
         try done.
      wp_pures. iModIntro. iIntros "H". iDestruct "H" as %vp_eqZ_v.
      assert (vp = v) as vp_eq_v by (clear -vp_eqZ_v; lia).
      clear vp_eqZ_v. subst vp.
       
      iApply fupd_wp.
      iInv "HthInv" as (M1_th)"(>Hth_sy & Hth_or)".
      iInv "HInv" as (T1 n1 M1 M1') "(>Hstate & >HT & >HM' & >M_eq_M' 
              & >HTmax & >HMTstate & >HTdiff & >per_tick 
              & >trans_inv & >resources & Prot)".
      iDestruct "Prot" as (R1 hγt1)"(>HR & >Hγt 
                                  & >Domm_hγt & Hstar_reg)".
      
      iAssert (⌜tid ∈ R1⌝)%I as "%".
      { iPoseProof (own_valid_2 _ _ _ with "[$HR] [$FP_t]") as "H'".
        iDestruct "H'" as %H'.
        apply auth_both_valid_discrete in H'.
        destruct H' as [H' _].
        apply gset_included in H'.
        iPureIntro. set_solver. }
      rename H into tid_in_R1.
      
      iAssert (▷ (⌜M1_th = M1⌝
               ∗ ([∗ set] t_id ∈ R1, Reg N γ_t γ_s γ_ght t_id M1)
               ∗ own (γ_sy) (to_frac_agree (1 / 2) M1_th) ))%I
                with "[Hstar_reg Hth_sy]" as "(>% & Hstar_reg & >Hth_sy)". 
      { iEval (rewrite (big_sepS_elem_of_acc _ (R1) tid); 
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
        iFrame "∗#". by iNext. } subst M1_th.
        
      assert (t ≤ map_max M1) as t_le_M1max. { admit. }
      assert (M1 !!! t = s) as M1_t_eq_s. { admit. }
      
      iDestruct "Hth_or" as "[Hth_or | Hth_or]".
      { iDestruct "Hth_or" as "(? & >%)".
        rename H into HPending.
        exfalso. 
        assert (T0 ≤ t ≤ map_max M1) as H' by lia.
        pose proof HPending t H' as HPending.
        rewrite M1_t_eq_s in HPending.
        clear -HPending Hrss. try done. }
      
      iDestruct "Hth_or" as "(Hth_or & >%)".  
      iDestruct "Hth_or" as "[Hth_or | >Hth_or]"; last first.
      { iPoseProof (own_valid_2 _ _ _ with "[$Token] [$Hth_or]") as "%".
        exfalso; try done. }
        
      iModIntro. iSplitR "Hth_or Hth_sy Token".
      iExists T1, n1, M1, M1'; iFrame.
      iNext. iExists R1, hγt1; iFrame.     

      iModIntro. iSplitL "Token Hth_sy".
      iNext. iExists M1. iFrame "Hth_sy". 
      iRight. iFrame "∗%".

      iModIntro. wp_pures. by iModIntro.
  Admitted.

End counter.