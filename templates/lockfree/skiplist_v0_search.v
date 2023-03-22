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

  Context {Σ} `{!heapGS Σ, !dsG Σ, !skG Σ}.
  Notation iProp := (iProp Σ).

  (** Proofs *)

  Lemma test γ (N: gset nat) (S: gset proph_id) (F: nat → gset proph_id) :
    own γ (● S) ∗ ([∗ set] n ∈ N, own γ (◯ (F n))) -∗ 
      own γ (● S) ∗ ([∗ set] n ∈ N, own γ (◯ (F n))) ∗ ⌜∀ n, n ∈ N → F n ⊆ S⌝.
  Proof.
    iInduction N as [| n N] "IH" using set_ind_L.
    - iIntros "(HS & Hstar)". iFrame. iPureIntro. intros n Hn; set_solver.
    - iIntros "(HS & Hstar)".
      rewrite (big_sepS_insert _ N n); last by eauto.
      iDestruct "Hstar" as "(Hn & Hstar)".
      iAssert (⌜F n ⊆ S⌝)%I as "%HFn".
      { admit. }
      iCombine "HS Hstar" as "H'".
      iDestruct ("IH" with "H'") as "(HS & star & %IH)".
      iFrame. iPureIntro. 
      intros n'. rewrite elem_of_union.
      intros [Hn | Hn].
      + assert (n' = n) as -> by set_solver.
        try done.
      + apply IH; try done.
  Admitted.
      
  
  Lemma temporal_interpolation_test1 (M : gmap nat nat) (T: nat) (FP: nat → gset K) :
      (∀ t, 0 ≤ t < T → FP (M !!! t) ⊆ FP (M !!! (t+1)%nat)) →
        (∀ t1 t2, 0 ≤ t1 ≤ t2 → t2 < T → FP (M !!! t1) ⊆ FP (M !!! t2)).
  Proof.
    intros Hcons. induction t1.
    - induction t2.
      + intros; try done.
      + intros Ht2 Ht2_T.
        assert (FP (M !!! 0) ⊆ FP (M !!! t2)) as H'.
        { apply IHt2. lia. lia. }
        assert (FP (M !!! t2) ⊆ FP (M !!! S t2)) as H''.
        { assert (t2 + 1 = S t2) as <- by lia.
          apply Hcons. lia. }
        clear -H' H''. set_solver.
    - induction t2.
      + intros H'. exfalso; lia.
      + intros Ht1 Ht2_T.
        assert (FP (M !!! t2) ⊆ FP (M !!! S t2)) as H'.
        { assert (t2 + 1 = S t2) as <- by lia.
          apply Hcons. lia. }
        destruct (decide (S t1 <= t2)).
        * assert (FP (M !!! S t1) ⊆ FP (M !!! t2)) as H''.
          { apply IHt2; try lia. }
          clear -H' H''. set_solver.
        * assert (t1 = t2) by lia.
          by subst t1.
  Qed.
  
  Lemma temporal_interpolation_test2 (M : gmap nat nat) 
    (T t1 t2: nat) (Mark: nat → bool) :
      (∀ t, 0 ≤ t < T → Mark (M !!! t) = true → Mark (M !!! S t) = true) →
        Mark (M !!! t1) = false → Mark (M !!! t2) = true → t1 ≤ t2 ≤ T →
        (∃ t, t1 ≤ t < t2 ∧ Mark (M !!! t) = false ∧ Mark (M !!! S t) = true).
  Proof.
    intros Htrans; induction t1; induction t2; 
    intros Mark1 Mark2 t1_le_t2.
    - exfalso. rewrite Mark2 in Mark1. inversion Mark1.
    - destruct (decide (Mark (M !!! t2) = true)). 
      + assert (0 ≤ t2 ≤ T) as H' by lia.
        pose proof IHt2 Mark1 e H' as IHt2.
        destruct IHt2 as [t [Ht [Mark1' Mark2']]].
        exists t; repeat split; try (done || lia).
      + exists t2. repeat split; try (done || lia).
        by rewrite not_true_iff_false in n.
    - assert (t1 = 0) as -> by lia.
      assert (0 ≤ 0 < T) as H' by lia.
      pose proof Htrans 0 H' Mark2 as Htrans.
      exfalso. rewrite Htrans in Mark1. inversion Mark1.
    - assert (t1 < t2 ∨ t1 = t2) as Hor by lia.
      destruct Hor as [Hor | ->].
      + destruct (decide (Mark (M !!! t2) = true)).
        * assert (Mark (M !!! t1) = false) as H'.
          { destruct (decide (Mark (M !!! t1) = false)); try done.
            rewrite not_false_iff_true in n.
            assert (0 ≤ t1 < T) as H' by lia.
            pose proof Htrans t1 H' n as Htrans.
            rewrite Htrans in Mark1. inversion Mark1. }
          assert (t1 ≤ S t2 ≤ T) as H'' by lia.
          pose proof IHt1 H' Mark2 H'' as IHt1.
          destruct IHt1 as [t [Ht [Mark1' Mark2']]].
          exists t; repeat split; try (done || lia).
          assert (t1 < t ∨ t1 = t) as Hor2 by lia.
          destruct Hor2 as [Hor2 | ->]; try lia.
          rewrite Mark1 in Mark2'. inversion Mark2'.
        * rewrite not_true_iff_false in n.
          exists t2; split; try (done || lia).
      + rewrite Mark1 in Mark2; inversion Mark2.    
  Qed.
  
  Definition traverse_rec_inv γ_m t0 k s p c : iProp :=
      past_state γ_m t0 s
    ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
    ∗ ⌜¬ mark s p⌝
    ∗ ⌜k ∈ outset K (intf s p) c⌝. 

  Lemma traverse_rec_spec N γ_t γ_s γ_m γ_td γ_ght r γ_sy t_id t0 (k: K) s p c:
    ⌜k ∈ KS⌝ -∗
      css_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv r) -∗
       thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        traverse_rec_inv γ_m t0 k s p c -∗
          {{{ True }}}
            traverse_rec r #p #c #k
          {{{ (p' c': Node) s, RET (#p', #c');
                past_state γ_m t0 s
              ∗ ⌜p' ∈ FP s⌝ ∗ ⌜c' ∈ FP s⌝   
              ∗ ⌜¬ mark s p'⌝
              ∗ ⌜k ∈ inset K (intf s p') p'⌝
              ∗ ⌜k ∈ outset K (intf s p') c'⌝
              ∗ ⌜¬ mark s c'⌝
              ∗ ⌜k ∈ keyset (intf s c')⌝ }}}.
  Proof.
    iIntros "%k_in_KS #HInv #Thd". 
    iLöb as "IH" forall (s p c). 
    iIntros "#Tr_inv" (Φ) "!# _ Hpost".
    wp_lam. wp_pures. awp_apply (findNext_spec); try done.
    iInv "HInv" as (M0 T0 s0) "(>CSS & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(PT & %Trans_M & %Trans_s & Res)". 
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_c.
    { admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Res" as "(NodeFull_c & Res_rest)".
    iDestruct "NodeFull_c" as (mc Ic pcc) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "Hpost". 
      iNext; iExists M0, T0, s0.
      iFrame "∗#%". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Res_rest".
      iExists mc, Ic, pcc. iFrame. }
    iIntros (succ n) "(Node & Hif)".
    destruct mc; destruct succ.
    - iModIntro. iSplitR "Hpost".
      { admit. }
      wp_pures. awp_apply (try_constraint_trav_spec k).
      iInv "HInv" as (M1 T1 s1) "(>CSS & >%Habs1 & >Hist & Help & >Templ)".
      { admit. }
      iAssert (⌜p ∈ FP s1⌝)%I as %FP_p.
      { admit. }
      iDestruct "Templ" as "(PT & %Trans_M1 & %Trans_s1 & Res)".
      rewrite (big_sepS_delete _ (FP s1) p); last by eauto.
      iDestruct "Res" as "(NodeFull_p & Res_rest)".
      iDestruct "NodeFull_p" as (mp Ip pcp) "(Node & Node_rest)".
      iAaccIntro with "Node".
      { iIntros "Node". admit. }
      iIntros (succ Ip') "(Node & Hif)".
      destruct succ.
      + iDestruct "Hif" as %((mp_false & k_in_Ip_c) & k_in_Ip'_n).
        admit.
      + iModIntro. iSplitR "Hpost".
        { admit. } 
        wp_pures.
        admit.
    - iModIntro. iSplitR "Hpost".
      { admit. }
      wp_pures. iExFalso. admit.
    - iModIntro. iSplitR "Hpost".
      { admit. } 
      wp_pures. admit.
  Admitted.

  Lemma traverse_spec N γ_t γ_s γ_m γ_td γ_ght r γ_sy t_id t0 (k: K) :
    ⌜k ∈ KS⌝ -∗
      css_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv r) -∗
       thread_vars γ_t γ_ght γ_sy t_id t0 -∗  
        {{{ True }}}
           traverse r #k
        {{{ (p c: Node) s, RET (#p, #c); 
              past_state γ_m t0 s
            ∗ ⌜p ∈ FP s⌝ ∗ ⌜c ∈ FP s⌝   
            ∗ ⌜¬ mark s p⌝
            ∗ ⌜k ∈ inset K (intf s p) p⌝
            ∗ ⌜k ∈ outset K (intf s p) c⌝
            ∗ ⌜¬ mark s c⌝
            ∗ ⌜k ∈ keyset (intf s c)⌝ }}}.
  Proof.
    iIntros "%k_in_KS #HInv #Thd". iIntros (Φ) "!# _ Hpost".
    wp_lam. awp_apply (findNext_spec); try done.
    iInv "HInv" as (M0 T0 s0) "(>CSS & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(PT & %Trans_M & %Trans_s & Res)". 
    iAssert (⌜r ∈ FP s0⌝)%I as %FP_r0.
    { admit. }
    rewrite (big_sepS_delete _ (FP s0) r); last by eauto.
    iDestruct "Res" as "(NodeFull_r & Res_rest)".
    iDestruct "NodeFull_r" as (mr Ir pcr) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "Hpost". 
      iNext; iExists M0, T0, s0.
      iFrame "∗#%". 
      rewrite (big_sepS_delete _ (FP s0) r); last by eauto. 
      iFrame "Res_rest".
      iExists mr, Ir, pcr. iFrame. }
    iIntros (succ n) "(Node & Hif)".
    destruct succ; last first.
    - iAssert (⌜k ∉ KS⌝)%I as %k_notin_KS.
      { iAssert (⌜T0 ∈ dom M0⌝)%I as %t_in_M0.
        { admit. }
        rewrite (big_sepS_delete _ (dom M0) T0); last by eauto.
        iDestruct "PT" as "(PT_T0 & PT_rest)".
        iAssert (per_tick_inv r (s0))%I with "[PT_T0]" as "PT_T0".
        { admit. }
        iDestruct "PT_T0" as "(HI & HKS & Ins_r & Out_r 
          & Mark_r & Hbig_star)".
        iDestruct "Hif" as %Hif.
        iDestruct "Out_r" as %Out_r.
        iDestruct "Node_rest" as "(_&%H'&_)".
        iPureIntro. rewrite <-H' in Out_r.
        by rewrite Out_r in Hif. }
      iClear "∗#". clear -k_in_KS k_notin_KS. exfalso; try done.
    - iModIntro.
      iAssert (past_state γ_m t0 s0)%I as "#Hist_s0".
      { admit. }
      iAssert (⌜n ∈ FP s0⌝)%I as %FP_n.
      { admit. }
      iAssert (⌜T0 ∈ dom M0⌝)%I as %T0_in_M0.
      { admit. }
      rewrite (big_sepS_delete _ (dom M0) T0); last by eauto.
      iDestruct "PT" as "(PT_T0 & PT_rest)".
      iAssert (per_tick_inv r (s0))%I with "[PT_T0]" as "PT_T0".
      { admit. }
      iDestruct "PT_T0" as "(HI & HKS & %Ins_r & %Out_r 
          & %Mark_r & Hbig_star)".
      iAssert (⌜k ∈ inset K (intf s0 r) r⌝)%I as %k_in_Insr.
      { iPureIntro. by rewrite Ins_r. }
      iDestruct "Hif" as %k_in_Outr.
      iAssert (⌜n ≠ r⌝)%I as "%n_neq_r".
      { admit. }
      iAssert (⌜n ∈ FP s0 ∖ {[r]}⌝)%I as "%".
      { clear -FP_n n_neq_r. iPureIntro; set_solver. } 
      rewrite (big_sepS_delete _ (FP s0 ∖ {[r]}) n); last by eauto.
      iDestruct "Res_rest" as "(NodeFull_n & Res_rest)".
      iDestruct "NodeFull_n" as (mn In pcn) "(Node_n & Node_n_rest)".
      iAssert (⌜Ir = intf s0 r⌝)%I as %HIr.
      { by iDestruct "Node_rest" as "(_&%&_)". }
      rewrite HIr in k_in_Outr.
      iAssert (⌜k ∈ inset K (intf s0 n) n⌝)%I as %k_in_Insn.
      { admit. }
      iAssert (traverse_rec_inv γ_m t0 k s0 r n)%I as "#Tr_inv".
      { iFrame "#%". }
      iSplitR "Hpost". 
      { iNext. iExists M0, T0, s0.
        iFrame "∗#%".
        rewrite (big_sepS_delete _ (dom M0) T0); last by eauto.
        iFrame. iSplitL "HI HKS Hbig_star".
        { admit. }
        rewrite (big_sepS_delete (nodeFull s0) (FP s0) r); last by eauto.
        rewrite (big_sepS_delete _ (FP s0 ∖ {[r]}) n); last by eauto.
        iFrame. iSplitL "Node Node_rest". 
        iExists mr, Ir, pcr. iFrame.
        iExists mn, In, pcn. iFrame. }   
      wp_pures. wp_apply traverse_rec_spec; try done.
  Admitted.

  
  Parameter ghost_update_keyset : ∀ γ_k dop (k: K) Cn Cn' res K1 C,
    ⊢   ⌜seq_spec dop Cn Cn' res k⌝ 
      ∗ own γ_k (● prod (KS, C)) 
      ∗ own γ_k (◯ prod (K1, Cn))
      ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝ ==∗ 
        ∃ C', 
          ⌜seq_spec dop C C' res k⌝ 
        ∗ own γ_k (● prod (KS, C'))
        ∗ own γ_k (◯ prod (K1, Cn')).
(*
  Parameter ghost_update_keyset_search : ∀ γ_k (k: K) Cn res K1 C,
    ⊢   ⌜seq_spec searchOp Cn Cn res k⌝ 
      ∗ own γ_k (● prod (KS, C)) 
      ∗ own γ_k (◯ prod (K1, Cn))
      ∗ ⌜Cn' ⊆ K1⌝ ∗ ⌜k ∈ K1⌝ ∗ ⌜k ∈ KS⌝ ==∗  
          ⌜seq_spec searchOp C C' res k⌝ 
        ∗ own γ_k (● prod (KS, C'))
        ∗ own γ_k (◯ prod (K1, Cn')).
*)

  
  Lemma searchOp_spec N γ_s γ_t γ_m γ_td γ_ght r (k: K) γ_sy t_id t0:
        ⌜k ∈ KS⌝ -∗
          css_inv N γ_t γ_s γ_m γ_td γ_ght (skiplist_inv r) -∗
            □ update_helping_protocol N γ_t γ_s γ_td γ_ght -∗
              thread_vars γ_t γ_ght γ_sy t_id t0 -∗
                {{{ True }}} 
                     search r #k
                {{{ res, RET #res; past_lin_witness γ_m searchOp k res t0  }}}.
  Proof.
    iIntros "%k_in_KS #HInv #HUpd #Thd". iIntros (Φ) "!# _ Hpost".
    wp_lam. wp_pures.
    wp_apply traverse_spec; try done.
    iIntros (p c s) "(#Hpast & %)".
    destruct H as [FP_p [FP_c [Unmarked_p [k_in_ins_p 
      [k_in_outs_p [Unmarked_c k_in_ks_c]]]]]].
    wp_pures.
    awp_apply (inContents_spec); try done.
    iInv "HInv" as (M0 T0 s0) "(>CSS & >%Habs0 & >Hist & Help & >Templ)".
    { admit. }
    iDestruct "Templ" as "(PT & %Trans_M1 & %Trans_s1 & Res)". 
    iAssert (⌜c ∈ FP s0⌝)%I as %FP_p0.
    { (* interpolation *) admit. }
    rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
    iDestruct "Res" as "(NodeFull_c & Res_rest)".
    iDestruct "NodeFull_c" as (mc Ic pcc) "(Node & Node_rest)".
    iAaccIntro with "Node".
    { iIntros "Node". iModIntro. iFrame "Hpost". 
      iNext; iExists M0, T0, s0.
      iFrame "∗%#". 
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto. 
      iFrame "Res_rest".
      iExists mc, Ic, pcc. iFrame. }
    iIntros (res) "(Node & Hres)". iDestruct "Hres" as %Hres.
    iSpecialize ("Hpost" $! res).

    iAssert (past_state γ_m t0 s)%I as "#Hpast2". { done. }
    iDestruct "Hpast2" as (t)"(%t0_le_t & #Hist_s)".
    iAssert (⌜t ∈ dom M0⌝)%I as %t_in_M0.
    { admit. }

    rewrite (big_sepS_delete _ (dom M0) t); last by eauto.
    iDestruct "PT" as "(Tick_t & PT_rest)".
    iAssert (⌜M0 !!! t = s⌝)%I as %M0_t_s.
    { admit. } iEval (rewrite M0_t_s) in "Tick_t". 
    iDestruct "Tick_t" as "(HI & HKS & Ins_r & Out_r & Mark_r & Hbig_star)".
    rewrite (big_sepS_delete _ (FP s) c); last by eauto.
    iDestruct "Hbig_star" as "(Node_local & Hbig_star_rest)".
    iDestruct "Node_local" as "(HIc & Hksc & Hpurec)".
    iAssert (⌜pcc = PC s c⌝)%I as %->.
    { (* interpolation *) admit. }
    iAssert (⌜seq_spec searchOp (Cont s c) (Cont s c) res k⌝)%I as %Seq_spec_c.
    { iPureIntro. unfold seq_spec. split; try done. destruct res; 
      unfold Cont; destruct (decide (mark s c)); try done.
      - by apply Hres.
      - intros ?. by apply Hres. }
    iAssert (⌜Cont s c ⊆ keyset (intf s c)⌝)%I as %cc_sub_ksc.
    { by iDestruct "Hpurec" as "(_ & % & _)". }
    iAssert (⌜seq_spec searchOp (abs s) (abs s) res k⌝)%I as %Seq_spec.
    { iPureIntro. unfold seq_spec. split; try done. destruct res.
      - assert (k ∈ Cont s c) as H'.
        { unfold Cont. rewrite decide_False; try done.
          by apply Hres. }
        assert (Cont s c ⊆ abs s) as H''.
        { admit. }
        clear -H' H''; set_solver.
      - (* Need this property from all snapshots *)
        assert (∀ s n k, k ∈ keyset (intf s n) → (k ∈ (Cont s n) ↔ k ∈ abs s)).
        { admit. }
        admit. }
(*        
    iMod (ghost_update_keyset (γ_ks s) searchOp k (Cont s c) (Cont s c) res 
      (keyset (intf s c)) (abs s)
      with "[$HKS $Hksc]") as (C') "(%Seq_spec & HKS & Hksc)".
    { iPureIntro; repeat (split; try done). }
    iAssert (⌜C' = abs s⌝)%I as %->.
    { by destruct Seq_spec as [? _]. }
*)    
    iAssert (past_lin_witness γ_m searchOp k res t0) as "Witn".
    { unfold past_lin_witness, updater_thread. iExists s.
      iFrame "#". by iPureIntro. }

    iModIntro. iSplitR "Hpost"; last first.
    { iApply "Hpost"; try done. } 
    { iNext. iExists M0, T0, s0.
      iFrame "CSS Hist Help %".
      iSplitR "Node Node_rest Res_rest".
      rewrite (big_sepS_delete _ (dom M0) t); last by eauto.
      iFrame "PT_rest". iEval (rewrite M0_t_s). iFrame "HI HKS".
      rewrite (big_sepS_delete _ (FP s) c); last by eauto.
      iFrame"Hbig_star_rest". iFrame.
      rewrite (big_sepS_delete _ (FP s0) c); last by eauto.
      iFrame "Res_rest". iExists mc, Ic, (PC s c). iFrame. }
  Admitted.      
    
                  


    
          
End skiplist_v0_search.            
      
         
      
      
          
        
    
  
  
  
  
  
  