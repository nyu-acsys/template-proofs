From iris.algebra Require Import excl auth gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations.
From iris.heap_lang Require Import proofmode notation par.
From iris.heap_lang.lib Require Import arith nondet_bool increment.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export lang.
Require Import one_shot_proph typed_proph.

Definition get (l: loc) : val :=
  λ: "", "".

Definition increment (l: loc) : val :=
  λ: "", #l <- !#l + #1.

Definition get' (l: loc) : val :=
  λ: "",
    let: "t_id" := NewProph in
    let: "p" := NewProph in
    let: "v" := get l #() in
    resolve_proph: "p" to: "v";;
    "v".  

    
(** Proof setup **)

Definition contUR := authR $ optionUR $ exclR natUR.
Definition valUR := authR max_natUR.
Definition histR := authR (gsetUR nat).
Definition t_idR := authR (gsetUR proph_id).
Definition hist_exclR := authR $ optionUR $ exclR (gsetO nat).
Definition tokenUR    := exclR unitO.
Definition cont_fracR := frac_agreeR (natUR).

Class counterG Σ := COUNTER {
                     counter_contG :> inG Σ contUR;
                     counter_valG :> inG Σ valUR;
                     counter_histG :> inG Σ histR;
                     counter_t_idG :> inG Σ t_idR;
                     counter_hist_exclG :> inG Σ hist_exclR;
                     counter_tokenG :> inG Σ tokenUR;
                     counter_cont_fracG :> inG Σ cont_fracR;
                    }.

Definition counterΣ : gFunctors :=
  #[GFunctor contUR; GFunctor valUR; GFunctor histR; GFunctor hist_exclR;
    GFunctor tokenUR; GFunctor cont_fracR; GFunctor t_idR ].

Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. solve_inG. Qed.

Section counter.
  Context {Σ} `{!heapG Σ, !counterG Σ }.
  Context (N1 N2 : namespace).
  Notation iProp := (iProp Σ).

  Local Definition thN := N2 .@ "thread".
  
  (** Invariants **)
  
  Definition max_of_set (H: gset nat) : nat := 
              let f := λ (n: nat) (v: nat), 
                         if (decide (v < n)) 
                         then n else v in
              set_fold f 0 H.

  Definition C_auth γ_ce γ_he (v: nat) (H: gset nat) : iProp :=
    own γ_ce (● Excl' v) ∗ own γ_he (● Excl' H).

  Definition C γ_ce γ_he (v: nat) (H: gset nat) : iProp :=
    own γ_ce (◯ Excl' v) ∗ own γ_he (◯ Excl' H).

  Definition Ch γ_ce γ_he (v: nat) : iProp := 
    ∃ H, C γ_ce γ_he v H ∗ ⌜max_of_set H = v⌝.

  
  Definition counter γ_ce γ_he γ_fr γ_c γ_s l (v: nat) (H: gset nat) : iProp :=
        l ↦ #v
      ∗ C_auth γ_ce γ_he v H   
      ∗ own γ_c (● (MaxNat v))
      ∗ own γ_s (● H)
      ∗ ⌜max_of_set H = v⌝
      ∗ own γ_fr (to_frac_agree (1/2) (v)).
      

  Definition counter_inv γ_ce γ_he γ_fr γ_c γ_s l : iProp :=
    inv N1 (∃ (v: nat) (H: gset nat), counter γ_ce γ_he γ_fr γ_c γ_s l v H).     

  Definition c_sr γ_s (v0: nat) : iProp := own γ_s (◯ {[v0]}).

  Definition pau γ_ce γ_he P (Q : val → iProp) := 
    (▷ P -∗ ◇ AU << ∀ v : nat, Ch γ_ce γ_he v >> @ ⊤ ∖ (↑N1 ∪ ↑N2), ∅
                 << Ch γ_ce γ_he v, COMM Q #v >>)%I.

  Definition state_lin_pending P v (vp: Z) : iProp := P ∗ ⌜(v < vp)%Z⌝.

  Definition state_lin_done γ_d (Q: val → iProp) v (vp : Z) : iProp := 
                              (Q #vp ∨ own γ_d (Excl ())) ∗ ⌜(vp ≤ v)%Z⌝. 

  Definition get_op_state γ_sy γ_d P Q (v : nat) (vp: Z) : iProp :=
                        own γ_sy (to_frac_agree (1/2) v) 
                     ∗ (state_lin_pending P v vp 
                        ∨ state_lin_done γ_d Q v vp).

  Definition registered γ_ce γ_he γ_sy v t_id : iProp :=
    ∃ P Q vp vt γ_d, 
        proph1 t_id vt
      ∗ own (γ_sy t_id) (to_frac_agree (1/2) v)
      ∗ □ pau γ_ce γ_he P Q 
      ∗ inv thN (∃ v, get_op_state (γ_sy t_id) γ_d P Q v vp).

  Definition helping γ_ce γ_he γ_fr γ_t γ_sy : iProp :=
    ∃ (v: nat) T,
        own γ_fr (to_frac_agree (1/2) v)
      ∗ own γ_t (● T)  
      ∗ ([∗ set] t_id ∈ T, registered γ_ce γ_he γ_sy v t_id).
  
  Definition helping_inv γ_ce γ_he γ_fr γ_t γ_sy : iProp :=
    inv N2 (helping γ_ce γ_he γ_fr γ_t γ_sy).   


  (** Proofs **)


  Lemma get_spec_fail γ_ce γ_he γ_fr γ_c γ_s l v0:
  ⊢ c_sr γ_s v0 -∗ 
      counter_inv γ_ce γ_he γ_fr γ_c γ_s l -∗
        <<< ∀ (v: nat) H, C γ_ce γ_he v H >>>
              get l @ ⊤ ∖ ↑N1
        <<< ∃ (v': nat), C γ_ce γ_he v H ∗ ⌜v' ∈ H⌝ ∗ ⌜v0 ≤ v'⌝, RET #v >>>.
  Proof.
  Admitted.    

  Lemma get_spec_high_fail γ_ce γ_he γ_fr γ_c γ_t γ_s γ_sy l:
  ⊢ counter_inv γ_ce γ_he γ_fr γ_c γ_s l -∗
      helping_inv γ_ce γ_he γ_fr γ_t γ_sy -∗ 
      <<< ∀ (v: nat), Ch γ_ce γ_he v >>>
            get' l #() @ ⊤ ∖ (↑N1 ∪ ↑N2)
      <<<  Ch γ_ce γ_he v, RET #v >>>.
  Proof.
  Admitted.    

  Lemma get_spec γ_ce γ_he γ_fr γ_c γ_s l v0:
  ⊢ c_sr γ_s v0 -∗ 
      counter_inv γ_ce γ_he γ_fr γ_c γ_s l -∗
        {{{ True }}}
              get l #()
        {{{ (v': nat), RET #v'; c_sr γ_s v' ∗ ⌜v0 ≤ v'⌝ }}}.
  Proof.
  Admitted.

(**
  Definition get' (l: loc) : val :=
    λ: "",
      let: "t_id" := NewProph in

        { proph t_id _ }

      let: "p" := NewProph in

        { proph t_id _ ∗ proph p vp }
        
        -- Open counter_inv 
        
        { proph t_id _ ∗ proph p vp ∗ c_sr v0 }
        
        Case 1: vp < v0
        ----------------
        
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ vp < v0 }

          -- Close helping_inv 
          
          let: "v" := get l #() in
          
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ vp < v0
            ∗ c_sr v ∗ v0 ≤ v }

          resolve_proph: "p" to: "v";;

          { proph t_id _ ∗ c_sr v0 ∗ vp < v0
            ∗ c_sr v ∗ v0 ≤ v ∗ vp = v }

          { False }

        Case 2: vp = v0
        ---------------
        
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ vp = v0 }

          -- Linearize
          
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ vp = v0 ∗ Φ (vp) } 

          -- Close counter_inv 
          
          let: "v" := get l #() in
          
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ vp = v0 ∗ Φ (vp)
            ∗ c_sr v ∗ v0 ≤ v }

          resolve_proph: "p" to: "v";;

          { proph t_id _ ∗ c_sr v0 ∗ vp = v0 ∗ Φ (vp)
            ∗ c_sr v ∗ v0 ≤ v ∗ vp = v }

          "v"
            
          { Φ (vp) ∗ vp = v }  

        Case 3: v0 < vp
        ---------------
        
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ v0 < vp }

          -- Register for helping
          -- Open helping_inv
          
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ v0 < vp
            ∗ t_id ∉ T0 }

          { proph p vp ∗ c_sr v0 ∗ v0 < vp
            ∗ t_id ∉ T0 ∗ registered t_id ∗ FP(t_id) }

          -- Close helping_inv
          -- Close counter_inv 
          
          let: "v" := get l #() in
          
          { proph p vp ∗ c_sr v0 ∗ v0 < vp
            ∗ FP(t_id) ∗ c_sr v ∗ v0 ≤ v }

          resolve_proph: "p" to: "v";;

          { c_sr v0 ∗ v0 < vp
            ∗ FP(t_id) ∗ c_sr v ∗ v0 ≤ v ∗ vp = v }
            
          -- Open thread_inv
          -- Helping can be either state_lin_pending or state_lin_done.
          -- With state_lin_done, we get Φ (v) and proof is complete.
          -- Need to show state_lin_pending is not possible.
          -- With state_lin_pending, context as below
          
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ v0 < vp
            ∗ FP(t_id) ∗ c_sr v ∗ v0 ≤ v ∗ vp = v
            ∗ AU ∗ vc < vp }
          
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ v0 < vp
            ∗ FP(t_id) ∗ c_sr v ∗ v0 ≤ v ∗ vp = v
            ∗ AU ∗ vc < vp ∗ v ≤ vc }
          
          { proph t_id _ ∗ proph p vp ∗ c_sr v0 ∗ v0 < vp
            ∗ FP(t_id) ∗ c_sr v ∗ v0 ≤ v ∗ vp = v
            ∗ AU ∗ vc < vp ∗ v ≤ vc }
            
          { vc < vp ∗ vp ≤ vc }
          
          { False }  
             

**)

  
  Lemma get_spec_high γ_ce γ_he γ_fr γ_c γ_t γ_s γ_sy l:
  ⊢ ⌜N1 ## N2⌝ -∗ ⌜N2 ## thN⌝ -∗ ⌜N1 ## thN⌝ -∗
    counter_inv γ_ce γ_he γ_fr γ_c γ_s l -∗
      helping_inv γ_ce γ_he γ_fr γ_t γ_sy -∗ 
      <<< ∀ (v: nat), Ch γ_ce γ_he v >>>
            get' l #() @ ⊤ ∖ (↑N1 ∪ ↑N2)
      <<<  Ch γ_ce γ_he v, RET #v >>>.
  Proof.
    iIntros "% % % #HInv #HInv_h" (Φ) "AU". wp_lam.
    rename H into Disj_ns1. rename H0 into Disj_ns2. rename H1 into Disj_ns3.
    wp_apply wp_new_proph1; try done.
    iIntros (tid vt)"Htid". wp_pures.
    wp_apply (typed_proph_wp_new_proph1 IntTypedProph); first done.
    iIntros (vp p)"Hproph". wp_pures. 
    iApply fupd_wp.
    iInv "HInv" as ">H".
    iDestruct "H" as (v0 H0)"(Hl & Hexcl & Hc & Hs & Hmax & Hfrac)".
    iAssert (own γ_s (◯ {[v0]}))%I as "Hv0". { admit. }
    destruct (decide (vp ≤ v0)%Z).
    - assert ((vp < v0)%Z ∨ vp = v0) as H' by lia.
      destruct H' as [Hcase' | Hcase'].
      + iModIntro. iSplitR "AU Hproph".
        iNext; iExists v0, H0; iFrame.
        iModIntro.
        wp_apply get_spec; try done.
        iIntros (v) "(Hsr & %)". wp_pures.
        wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done.
        wp_pures. iIntros "%". wp_pures.
        clear -H1 H Hcase'. exfalso; lia.
      + iMod "AU" as (v') "[Hch [_ Hcomm]]".
        set_solver.
        iAssert (⌜v' = v0⌝)%I as "%". { admit. }
        subst v'. iMod ("Hcomm" with "Hch") as "HΦ".
        iModIntro. iSplitR "HΦ Hproph".
        iNext; iExists v0, H0; iFrame.
        iModIntro.
        wp_apply get_spec; try done.
        iIntros (v) "(Hsr & %)". wp_pures.
        wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done.
        wp_pures. iIntros "%". wp_pures.
        rewrite <-H1. by rewrite Hcase'.
    - assert ((vp > v0)%Z) by lia.
      iInv "HInv_h" as (v' T0)"(>Hex & >HT & Hstar)".
      iAssert (⌜v' = v0⌝)%I as "%". { admit. } subst v'.
      iAssert (▷ (⌜tid ∉ T0⌝ 
                ∗ ([∗ set] t_id ∈ T0, registered γ_ce γ_he γ_sy v0 t_id) 
                ∗ proph1 tid vt))%I with "[Hstar Htid]" as "(>% & Hstar & Htid)".
      { destruct (decide (tid ∈ T0)); try done.
        - iEval (rewrite (big_sepS_elem_of_acc _ (T0) tid); 
                                last by eauto) in "Hstar".
          iDestruct "Hstar" as "(Hreg_t & Hstar')".
          iDestruct "Hreg_t" as (? ? ? ? ?)"(H' & _)".
          iAssert (▷ False)%I with "[H' Htid]" as "HF".
          iApply (proph1_exclusive tid with "[Htid]"); try done.
          iNext. iExFalso; try done.
        - iFrame. iNext. by iPureIntro. }  
      iAssert (own γ_t (● (T0 ∪ {[tid]})) ∗ own γ_t (◯ {[tid]}))%I
        with "[HT]" as "(HT & #FP_t)". { admit. }
      iAssert (own (γ_sy tid) (to_frac_agree (1/2) v0) ∗
                own (γ_sy tid) (to_frac_agree (1/2) v0))%I as "(Hsy1 & Hsy2)".
      { admit. }
      iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
      iMod (own_alloc (Excl ())) as (γ_d) "Token_d"; first try done.       
      iMod (inv_alloc thN _
              (∃ v, get_op_state (γ_sy tid) γ_d AU_later (Φ) v vp) 
                                    with "[AU Hsy1]") as "#HthInv".
      { iNext. iExists v0. unfold get_op_state. iFrame "∗ #".
        iLeft. unfold state_lin_pending. iFrame. iPureIntro. lia. }

      iModIntro. iSplitL "Htid Hex Hstar HT". iNext.
      iExists v0, (T0 ∪ {[tid]}). iFrame.
      rewrite (big_sepS_delete _ (T0 ∪ {[tid]}) tid); last by set_solver.
      iSplitR "Hstar". unfold registered.
      iExists AU_later, Φ, vp, vt, γ_d. iFrame "∗#".
      assert ((T0 ∪ {[tid]}) ∖ {[tid]} = T0) by (clear -H1; set_solver).
      by rewrite H2.
      
      iModIntro. iSplitR "Token_d Hproph".
      iNext. iExists v0, H0; iFrame.
      
      iModIntro. wp_apply get_spec; try done.
      iIntros (v) "(#Hsr & %)". wp_pures.
      wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done.
      wp_pures. iIntros "%".
      iApply fupd_wp.
      iInv "HthInv" as (v1)"(>Hv & Hor)".
      iInv "HInv_h" as (v1' T1)"(>Hex & >HT & Hstar)".
      iAssert (⌜v1' = v1⌝)%I as "%". { admit. } subst v1'.
      iInv "HInv" as ">H".
      iDestruct "H" as (v1' H1')"H".
      iAssert (⌜v1' = v1⌝)%I as "%". { admit. } subst v1'.
      iAssert (⌜v ≤ v1⌝)%I as "%". { admit. }
      iDestruct "Hor" as "[Hor | Hor]".
      { iDestruct "Hor" as "(? & >%)".
        exfalso. lia. }
      iDestruct "Hor" as "(Hor & >%)".  
      iDestruct "Hor" as "[Hor | >Hor]"; last first.
      { admit. }
      
      iModIntro. iSplitL "H".
      iExists v1, H1'; iFrame.

      iModIntro. iSplitL "Hstar HT Hex".
      iNext. iExists v1, T1; iFrame.
      
      iModIntro. iSplitL "Token_d Hv".
      iNext. iExists v1. iFrame "Hv". 
      iRight. iFrame "∗%".
      
      iModIntro. wp_pures. by rewrite H3.
  Admitted.
  
(** 
1) The current value of the data structure needs to be shared 
   between the invariants becuase helping protocol depends on it. 
2) Due to 1), the upsert/increment proof will need to linearize
   the threads. The low-level proof cannot be separated.
3) History quantity has been made redundant, and we can prove
   high-level specs directly. Maybe the invariant can also be 
   simplified a little.
**)  
  
  Lemma ghost_update_registered γ_ce γ_he γ_sy v0 T :
      ([∗ set] t_id ∈ T, registered γ_ce γ_he γ_sy v0 t_id) ={⊤ ∖ ↑N1 ∖ ↑N2}=∗ 
          ([∗ set] t_id ∈ T, registered γ_ce γ_he γ_sy (v0 + 1) t_id).
  Proof.
    iInduction T as [|x T' ? IH] "H" using set_ind_L; auto using big_sepS_empty'.
    rewrite (big_sepS_delete _ ({[x]} ∪ T') x); last by set_solver.
    rewrite (big_sepS_delete _ ({[x]} ∪ T') x); last by set_solver.
    assert (({[x]} ∪ T') ∖ {[x]} = T'). set_solver. rewrite H0.
    iIntros "(Hx & Hbigstar)". 
    iMod ("H" with "Hbigstar") as "H'".
    iSplitL "Hx"; last by iFrame.
    iDestruct "Hx" as (P Q vp vt γ_d)"(Hproph & Hfr & #Pau & #Hthinv)".
    iInv "Hthinv" as (v)"Hstate". admit.
    iDestruct "Hstate" as "(>Hfr' & Hstate)".
    iAssert (⌜v = v0⌝)%I as "%". { admit. } subst v.
    iAssert (own (γ_sy x) (to_frac_agree (1 / 2) (v0+1)) ∗
              own (γ_sy x) (to_frac_agree (1 / 2) (v0+1)))%I 
                with "[Hfr Hfr']" as "(Hfr & Hfr')".
    { admit. }              
    iDestruct "Hstate" as "[Hpending | Hdone]".
    - iDestruct "Hpending" as "(P & >%)".
      destruct (decide ((v0 + 1)%Z = vp)).
      + iDestruct ("Pau" with "P") as ">AU".
        iMod "AU" as (v)"[Hpre [_ Hclose]]". admit.
        iAssert (⌜v = (v0 + 1)%nat⌝)%I as "%".
        { admit. } subst v.
        iMod ("Hclose" with "Hpre") as "HQ".
        iModIntro. iSplitL "Hfr' HQ".
        iNext. iExists (v0 + 1)%nat. iFrame.
        iRight. iSplitL. iLeft. rewrite <-e. admit.
        iPureIntro. lia.
        iModIntro. iFrame.
        iExists P, Q, vp, vt, γ_d.
        iFrame "∗#".
      + iModIntro. iSplitR "Hproph Hfr".
        iNext. iExists (v0 + 1)%nat. iFrame.
        iLeft. iFrame. iPureIntro. lia.
        iModIntro. iFrame.             
        iExists P, Q, vp, vt, γ_d.
        iFrame "∗#".
    - iModIntro.
      iSplitR "Hproph Hfr".
      iNext. iExists (v0 + 1)%nat. iFrame.
      iRight. iDestruct "Hdone" as "(HQ & %)".
      iFrame "HQ". iPureIntro. lia.
      iModIntro. iFrame. 
      iExists P, Q, vp, vt, γ_d.
      iFrame "∗#".
  Admitted.        
  
  Lemma increment_spec_high_fail γ_ce γ_he γ_fr γ_c γ_t γ_s γ_sy l:
  ⊢ ⌜N1 ## N2⌝ -∗ ⌜N2 ## thN⌝ -∗ ⌜N1 ## thN⌝ -∗
    counter_inv γ_ce γ_he γ_fr γ_c γ_s l -∗
      helping_inv γ_ce γ_he γ_fr γ_t γ_sy -∗ 
      <<< ∀ v, Ch γ_ce γ_he v >>>
            increment l #() @ ⊤ ∖ (↑N1 ∪ ↑N2)
      <<< Ch γ_ce γ_he (v + 1), RET #() >>>.
  Proof.
    iIntros "% % % #HInv #HInv_h" (Φ) "AU". wp_lam.
    rename H into Disj_ns1. rename H0 into Disj_ns2. rename H1 into Disj_ns3.
    wp_bind(! _)%E.
    iInv "HInv" as ">H".
    iDestruct "H" as (v0 H0)"(Hl & Hexcl & Hc & Hs & Hmax & Hfrac)".
    wp_load. iModIntro.
    iSplitR "AU".
    iNext. iExists v0, H0. iFrame.
    wp_bind (_ + _)%E ; wp_op.
    iInv "HInv" as ">H".
    iDestruct "H" as (v1 H1)"(Hl & Hexcl & Hc & Hs & Hmax & Hfrac)".
    iAssert (⌜v1 = v0⌝)%I as "%". { admit. } subst v1.
    iInv "HInv_h" as (v' T0)"(>Hfr & >HT & Hstar)".
    wp_store.
    iMod "AU" as (v)"[Hch [_ Hcomm]]". set_solver.
    iDestruct "Hch" as (H)"(Hc_auth & Hmax1)".
    iAssert (⌜v = v0⌝)%I as "%". { admit. } subst v.
    iAssert (⌜H = H1⌝)%I as "%". { admit. } subst H.
    iAssert (C_auth γ_ce γ_he (v0 + 1) (H1 ∪ {[v0]}) 
              ∗ C γ_ce γ_he (v0 + 1) (H1 ∪ {[v0]}))%I
                with "[Hc_auth Hexcl]" as "(Hc_auth & Hexcl)".
    { admit. }
    iAssert (Ch γ_ce γ_he (v0 + 1))%I with "[Hc_auth]" as "Hc_auth".
    { admit. }
    iMod ("Hcomm" with "Hc_auth") as "HΦ".  
    iAssert (own γ_c (● {| max_nat_car := v0 + 1 |}))%I 
                with "[Hc]" as "Hc".
    { admit. }
    iAssert (own γ_s (● (H1 ∪ {[v0]} )))%I 
                with "[Hs]" as "Hs".
    { admit. }
    iAssert (⌜v' = v0⌝)%I as "%". { admit. } subst v'.
    iAssert (own γ_fr (to_frac_agree (1 / 2) (v0 + 1)) ∗
              own γ_fr (to_frac_agree (1 / 2) (v0 + 1)))%I
              with "[Hfrac Hfr]" as "(Hfrac & Hfr)".
    { admit. }
    iMod (ghost_update_registered with "Hstar") as "Hstar".
  Admitted.
  
      
  

  


