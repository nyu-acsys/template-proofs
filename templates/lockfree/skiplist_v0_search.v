(* Herlihy Skiplist with a single level : Search *)

From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
Require Export skiplist_v0.

Section skiplist_v0_search.
  Context {Σ} `{!heapGS Σ, !skG Σ}.
  Notation iProp := (iProp Σ).

  (** Some lemmas *)

(*
  Parameter ghost_update_keyset : ∀ γ_k dop (k: K) Cn Cn' res K1 C,
    ⊢   ⌜Ψ dop k Cn Cn' res⌝ 
      ∗ own γ_k (● prod (KS, C)) 
      ∗ own γ_k (◯ prod (K1, Cn))
      ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝ ==∗ 
        ∃ C', 
          ⌜Ψ dop k C C' res⌝ 
        ∗ own γ_k (● prod (KS, C'))
        ∗ own γ_k (◯ prod (K1, Cn')).
*)

  (** Proofs *)
    
  Definition traverse_rec_inv γ_t γ_ght γ_m t_id k s p c : iProp :=
      past_state γ_t γ_ght γ_m t_id s
    ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
    ∗ ⌜¬ mark s p⌝
    ∗ ⌜k ∈ outset K (intf s p) c⌝. 

  Lemma traverse_rec_spec N γ_s γ_t γ_m γ_td γ_ght r t_id (k: K) s p c:
    ⌜k ∈ KS⌝ -∗
      searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r -∗
       thread_id γ_t γ_ght t_id -∗  
        traverse_rec_inv γ_t γ_ght γ_m t_id k s p c -∗
          <<< True >>>
            traverse_rec r #p #c #k @ (↑(sstrN N))
          <<< ∃ (p c: Node) (s: State), 
                past_state γ_t γ_ght γ_m t_id s
              ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
              ∗ ⌜¬ mark s p⌝
              ∗ ⌜k ∈ inset K (intf s p) p⌝
              ∗ ⌜k ∈ outset K (intf s p) c⌝
              ∗ ⌜¬ mark s c⌝
              ∗ ⌜k ∈ keyset (intf s c) c⌝, 
                RET (#p, #c) >>>.
  Proof.
    iIntros "%k_in_KS #HInv #Htid". 
    iLöb as "IH" forall (s p c). 
    iIntros "#Tr_inv" (Φ) "AU".
    wp_lam. wp_pures. awp_apply (findNext_spec).
    iInv "HInv" as (s0 M0 T0) "(>Half & >Res & >Hist & Help)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c.
    { admit. }
    iDestruct "Res" as "(Per_tick & Resources)".
    iEval (unfold resources) in "Resources". 
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Resources" as "(NodeFull_c & Resources_rest)".
    iDestruct "NodeFull_c" as (mc Ic pcc) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "AU". 
      iNext; iExists s0, M0, T0.
      iFrame. unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Resources_rest".
      iExists mc, Ic, pcc. iFrame. }
    iIntros (succ n) "(Node & Hif)".
    destruct mc; destruct succ.
    - iModIntro. iSplitR "AU".
      { admit. }
      wp_pures. awp_apply (try_constraint_trav_spec _ k).
      iInv "HInv" as (s1 M1 T1) "(>Half & >Res & >Hist & Help)".
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p.
      { admit. }
      iDestruct "Res" as "(Per_tick & Resources)".
      iEval (unfold resources) in "Resources". 
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Resources" as "(NodeFull_p & Resources_rest)".
      iDestruct "NodeFull_p" as (mp Ip pcp) "(Node & Node_rest)".
      iAaccIntro with "Node".
      { iIntros "Node". admit. }
      iIntros (succ Ip') "(Node & Hif)".
      destruct succ.
      + iDestruct "Hif" as %((mp_false & k_in_Ip_c) & k_in_Ip'_n).
        admit.
      + iModIntro. iSplitR "AU".
        { admit. } 
        wp_pures.
        admit.
    - iModIntro. iSplitR "AU".
      { admit. }
      wp_pures. iExFalso. admit.
    - iModIntro. iSplitR "AU".
      { admit. } 
      wp_pures. admit.
  Admitted.


  Lemma traverse_spec N γ_s γ_t γ_m γ_td γ_ght r t_id (k: K) :
    ⌜k ∈ KS⌝ -∗
      searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r -∗
       thread_id γ_t γ_ght t_id -∗ 
        <<< True >>>
           traverse r #k @ (↑(sstrN N))
        <<< ∃ (p c: Node) (s: State), 
              past_state γ_t γ_ght γ_m t_id s
            ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
            ∗ ⌜¬ mark s p⌝
            ∗ ⌜k ∈ inset K (intf s p) p⌝
            ∗ ⌜k ∈ outset K (intf s p) c⌝
            ∗ ⌜¬ mark s c⌝
            ∗ ⌜k ∈ keyset (intf s c) c⌝, 
              RET (#p, #c) >>>.
  Proof.
    iIntros "%k_in_KS #HInv #Htid" (Φ) "AU".
    wp_lam. awp_apply (findNext_spec).
    iInv "HInv" as (s0 M0 T0) "(>Half & >Res & >Hist & Help)".
    iAssert (⌜r ∈ FP s0⌝)%I as %FP_r0.
    { admit. }
    iDestruct "Res" as "(Per_tick & Resources)".
    iEval (unfold resources) in "Resources". 
    rewrite (big_sepS_delete _ (FP s0) r); last by eauto.
    iDestruct "Resources" as "(NodeFull_r & Resources_rest)".
    iDestruct "NodeFull_r" as (mr Ir pcr) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "AU". 
      iNext; iExists s0, M0, T0.
      iFrame. unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) r); last by eauto. 
      iFrame "Resources_rest".
      iExists mr, Ir, pcr. iFrame. }
    iIntros (succ n) "(Node & Hif)".
    destruct succ; last first.
    - iAssert (⌜k ∉ KS⌝)%I as %k_notin_KS.
      { iAssert (⌜T0 ∈ dom (gset nat) M0⌝)%I as %t_in_M0.
        { admit. }
        iDestruct "Per_tick" as "(HI & HKS & Ins_r & Out_r 
          & Mark_r & Hbig_star)".
        iDestruct "Hif" as %Hif.
        iDestruct "Out_r" as %Out_r.
        iDestruct "Node_rest" as "(_&%H'&_)".
        iPureIntro. rewrite <-H' in Out_r.
        by rewrite Out_r in Hif. }
      iClear "∗#". clear -k_in_KS k_notin_KS. exfalso; try done.
    - iModIntro.
      iDestruct "Htid" as (t0 γ_sy)"Htid".
      iAssert (own γ_m (◯ {[T0 := to_agree s0]}))%I as "#HT0".
      { admit. }
      iAssert (⌜t0 ≤ T0⌝)%I as %t0_le_T0.
      { admit. }
      iAssert (past_state γ_t γ_ght γ_m t_id s0)%I as "#Hpast".
      { iExists t0, γ_sy, T0. iFrame "#%". }
      iAssert (⌜r ∈ FP s0⌝)%I as %FP_r.
      { admit. }
      iAssert (⌜n ∈ FP s0⌝)%I as %FP_n.
      { admit. }
      iAssert (⌜T0 ∈ dom (gset nat) M0⌝)%I as %T0_in_M0.
      { admit. }
      iDestruct "Per_tick" as "(HI & HKS & %Ins_r & %Out_r 
          & %Mark_r & Hbig_star)".    
      iAssert (⌜k ∈ inset K (intf s0 r) r⌝)%I as %k_in_Insr.
      { iPureIntro. by rewrite Ins_r. }
      iDestruct "Hif" as %k_in_Outr.
      iAssert (⌜n ≠ r⌝)%I as "%n_neq_r".
      { admit. }
      iAssert (⌜n ∈ FP s0 ∖ {[r]}⌝)%I as "%".
      { clear -FP_n n_neq_r. iPureIntro; set_solver. } 
      rewrite (big_sepS_delete _ (FP s0 ∖ {[r]}) n); last by eauto.
      iDestruct "Resources_rest" as "(NodeFull_n & Resources_rest)".
      iDestruct "NodeFull_n" as (mn In pcn) "(Node_n & Node_n_rest)".
      iAssert (⌜Ir = intf s0 r⌝)%I as %HIr.
      { by iDestruct "Node_rest" as "(_&%&_)". }
      rewrite HIr in k_in_Outr.
      iAssert (⌜k ∈ inset K (intf s0 n) n⌝)%I as %k_in_Insn.
      { admit. }
      iAssert (traverse_rec_inv γ_t γ_ght γ_m t_id k s0 r n)%I as "#Tr_inv".
      { iFrame "#%". }
      iSplitR "AU". 
      { iNext. iExists s0, M0, T0.
        iFrame "Half Hist Help". iFrame.
        iSplitR. iPureIntro; repeat split; try done.
        unfold resources. 
        rewrite (big_sepS_delete _ (FP s0) r); last by eauto.
        rewrite (big_sepS_delete _ (FP s0 ∖ {[r]}) n); last by eauto.
        iFrame "Resources_rest". iSplitL "Node Node_rest". 
        iExists mr, Ir, pcr. iFrame.
        iExists mn, In, pcn. iFrame. }   
      wp_pures. awp_apply traverse_rec_spec; try done.
      { by iExists t0, γ_sy. }
      iAaccIntro with ""; try done.
      { iIntros "_". iModIntro. iFrame. }
      iIntros (p c s) "Hpost".
      iMod "AU" as "[_ [_ Hcomm]]".
      iSpecialize ("Hcomm" $! p c s).
      iMod ("Hcomm" with "Hpost") as "HΦ".
      by iModIntro.  
  Admitted.

  
  Lemma search_spec N γ_s γ_t γ_m γ_td γ_ght r t_id (k: K) :
    ⌜k ∈ KS⌝ -∗
      searchstr_inv N γ_s γ_t γ_m γ_td γ_ght r -∗
        thread_id γ_t γ_ght t_id -∗ 
          <<< True >>>
            search r #k @ ⊤ ∖ (↑(sstrN N))
          <<< ∃ (res: bool) (s: State), 
                past_state γ_t γ_ght γ_m t_id s 
              ∗ ⌜seq_spec k (gcont s) res⌝, 
                RET #res >>>.
  Proof.
    iIntros "% #HInv #Htid" (Φ) "AU".
    rename H into k_in_KS.
    wp_lam. wp_pures.
    awp_apply traverse_spec; try done.
    iAaccIntro with ""; try done.
    { eauto with iFrame. }
    iIntros (p c s) "(#Hpast & %)".
    destruct H as [FP_p [FP_c [Unmarkedp [k_in_pins 
      [k_in_pouts [Unmarkedc k_in_cks]]]]]].
    iModIntro. wp_pures.
    awp_apply (inContents_spec).
    iInv "HInv" as (s0 M0 T0) "(>Half & >Res & >Hist & Help)".
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    iDestruct "Res" as "(Per_tick & Resources)".
    iEval (unfold resources) in "Resources". 
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Resources" as "(NodeFull_c & Resources_rest)".
    iDestruct "NodeFull_c" as (mc Ic pcc) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "AU". 
      iNext; iExists s0, M0, T0.
      iFrame. unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Resources_rest".
      iExists mc, Ic, pcc. iFrame. }
    iIntros (res) "(Node & Hres)". iDestruct "Hres" as %Hres.
    iAssert (past_state γ_t γ_ght γ_m t_id s)%I as "#Hpast2". { done. }
    iDestruct "Hpast2" as (t0 γ_sy t)"(Hth_vars & t_s & %)".
    iAssert (⌜t ∈ dom (gset nat) M0⌝)%I as %t_in_M0.
    { admit. }
(*    
    rewrite (big_sepS_delete _ (dom (gset nat) M0) t); last by eauto.
    iDestruct "Per_tick" as "(Tick_t & Per_tick_rest)".
    iAssert (⌜M0 !!! t = s⌝)%I as %M0_t_s.
    { admit. } iEval (rewrite M0_t_s) in "Tick_t". 
    iDestruct "Tick_t" as "(HI & HKS & Ins_r & Out_r & Mark_r & Hbig_star)".
    rewrite (big_sepS_delete _ (FP s) c); last by eauto.
    iDestruct "Hbig_star" as "(Node_local & Hbig_star_rest)".
    iDestruct "Node_local" as "(HIc & Hksc & Hpurec)".
    iAssert (⌜pcc = PC s c⌝)%I as %->.
    { (* interpolation *) admit. }
    iAssert (⌜Ψ searchOp k (C s c) (C s c) res⌝)%I as %HΨ_c.
    { iPureIntro. unfold Ψ. split; try done. destruct res; 
      unfold C; destruct (decide (mark s c)); try done.
      - by apply Hres.
      - intros ?. by apply Hres. }
    iAssert (⌜C s c ⊆ keyset (intf s c) c⌝)%I as %cc_sub_ksc.
    { by iDestruct "Hpurec" as "(_ & % & _)". }
    iMod (ghost_update_keyset (γ_ks s) searchOp k (C s c) (C s c) res 
      (keyset (intf s c) c) (gcont s)
      with "[$HKS $Hksc]") as (C') "(% & HKS & Hksc)".
    { iPureIntro; repeat (split; try done). }
    rename H0 into HΨ.
    iAssert (⌜C' = gcont s⌝)%I as %->.
    { by destruct HΨ as [? _]. }
    iAssert (⌜search_seq_spec k (gcont s) res⌝)%I as %HPost.
    { by iPureIntro. }
    iMod "AU" as "[_ [_ Hcomm]]". admit.
    iSpecialize ("Hcomm" $! res s).
    iMod ("Hcomm" with "[$Hpast]") as "HΦ".
    { by iPureIntro. }
    
    iModIntro. iFrame "HΦ". 
    { iNext. iExists T0, s0, M0, M0'.
      iFrame "Half Hist Help". iFrame "Trans_inv".
      iSplitR "Node Node_rest Resources_rest".
      rewrite (big_sepS_delete _ (dom (gset nat) M0) t); last by eauto.
      iFrame "Per_tick_rest". iEval (rewrite M0_t_s). iFrame "HI HKS".
      rewrite (big_sepS_delete _ (FP s) c); last by eauto.
      iFrame"Hbig_star_rest". iFrame.
      unfold resources. 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Resources_rest". iExists mc, Ic, (PC s c). iFrame. }
*)      
  Admitted.      
          
End skiplist_v0_search.            
      
         
      
      
          
        
    
  
  
  
  
  
  