(*Add LoadPath "/home/nisarg/academics/multicopy-iris/templates/" as Pt.*)
From iris.algebra Require Import excl auth gmap agree gset numbers.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.heap_lang.lib Require Import arith nondet_bool increment.
From iris.bi.lib Require Import fractional.
(*From iris.bi Require Import derived_laws_sbi.
From iris_examples.proph.lib Require Import one_shot_proph. *)
Require Import one_shot_proph typed_proph.

Definition get : val :=
  λ: "l0" "l1",
  let: "p" := NewProph in
  let: "v0" := !"l0" in
  let: "v1" := !"l1" in 
  resolve_proph: "p" to: "v0" + "v1";;  
  "v0" + "v1".

Definition increment : val :=
  λ: "l0" "l1",
  let: "r" := nondet_bool #() in
  if: "r" then
    incr_phy "l0" 
  else 
    incr_phy "l1".

(** ** Proof setup *)

Definition contUR := authR $ optionUR $ exclR natUR.
Definition valUR := authR natUR.
Definition tokenUR    := exclR unitO.

Class counterG Σ := COUNTER {
                     counter_contG :> inG Σ contUR;
                     counter_valG :> inG Σ valUR;
                     counter_tokG :> inG Σ tokenUR;
                    }.

Definition counterΣ : gFunctors :=
  #[GFunctor contUR; GFunctor valUR; GFunctor tokenUR ].

Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. solve_inG. Qed.

Section counter.
  Context {Σ} `{!heapG Σ, !counterG Σ }.
  Context (N : namespace).
  Context (T : gset proph_id).
  Notation iProp := (iProp Σ).

  Implicit Types γ_a γ_b γ_c : gname.
  Implicit Types l_a l_b : loc.
  Implicit Types p : proph_id.
(*   Implicit Types γ_t: proph_id → gname. *)

  Local Definition toyN := N .@ "toy".
  Local Definition thN := N .@ "thread".


  (** The view of the authority agrees with the local view. *)
  Lemma auth_agree γ xs ys :
    own γ (● (Excl' xs)) -∗ own γ (◯ (Excl' ys)) -∗ ⌜xs = ys⌝.
  Proof.
(*
    iIntros "Hγ● Hγ◯". by iDestruct (own_valid_2 with "Hγ● Hγ◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.
*)
  Admitted.
  
  (** The view of the authority can be updated together with the local view. *)
  Lemma auth_update γ ys xs1 xs2 :
    own γ (● (Excl' xs1)) -∗ own γ (◯ (Excl' xs2)) ==∗
      own γ (● (Excl' ys)) ∗ own γ (◯ (Excl' ys)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' ys ⋅ ◯ Excl' ys)
      with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.
  
  Lemma excl_false γ v v' : own γ (◯ Excl' v) ∗ own γ (◯ Excl' v') -∗ False.
  Proof. 
    iIntros "(H1 & H2)".
    iPoseProof (own_valid_2 with "[$] [$]") as "%".
    exfalso; try done.
  Qed.  

  (** Definition of the invariant *)

  Definition toy_cont γ_c n := own γ_c (◯ (Some (Excl (n)))).


  Definition pau γ_c P (Q : val → iProp) := (▷ P -∗ 
                                        ◇ AU << ∀ n : nat, toy_cont γ_c n >> @ ⊤ ∖ ↑N, ∅
                                             << toy_cont γ_c n, COMM Q #n >>)%I.

  Definition state_lin_pending γ_c P v (vp: Z) : iProp := P ∗ ⌜(v < vp)%Z⌝.

  Definition state_lin_done γ_d (Q: val → iProp) v (vp : Z) : iProp := 
                              (Q #vp ∨ own γ_d (Excl ())) ∗ ⌜(vp ≤ v)%Z⌝. 

  Definition read_op_state γ_c γ_s γ_d P Q (v : nat) (vp: Z) : iProp :=
                            own γ_s (●{1/2} (v)%nat) 
                          ∗ (state_lin_pending γ_c P v vp ∨ state_lin_done γ_d Q v vp).

(*
  Definition help_inv γ_c P Q (vp: Z) : iProp := 
                      inv thN (∃ (v: nat) (b: bool), own γ_c (●{1/2} (Excl' (v))) 
                                  ∗ if (Z.leb vp v) then True else read_op_state γ_c P Q v vp).
*)

  Definition toy_inv γ_a γ_b γ_c γ_s γ_t la lb : iProp := 
                       ∃ (va vb : nat),
                         la ↦ #va%nat ∗ lb ↦ #vb%nat 
                       ∗ own γ_a (● va) ∗ own γ_b (● vb)
                       ∗ own γ_c (● (Excl' (va + vb)%nat))
                       ∗ ([∗ set] t_id ∈ T, ∃ (b:bool), 
                              (if b then
                                (∃ P Q vp vt γ_d, 
                                    typed_proph1_prop IntTypedProph t_id vt
                                  ∗ own (γ_s t_id) (●{1/2} (va + vb)%nat)
                                  ∗ □ pau γ_c P Q 
                                  ∗ inv thN (∃ v, read_op_state γ_c (γ_s t_id) γ_d P Q v vp))
                               else own γ_t (Excl ()) 
                                  ∗ (own (γ_s t_id) (● (va + vb)%nat) 
                                  ∨ ∃vt, typed_proph1_prop IntTypedProph t_id vt))).         

(*
  Definition toy_inv γ_a γ_b γ_c γ_s γ_t la lb tid : iProp := 
                       ∃ (va vb : nat) (b: bool),
                         la ↦ #va%nat ∗ lb ↦ #vb%nat 
                       ∗ own γ_a (● va) ∗ own γ_b (● vb)
                       ∗ own γ_c (● (Excl' (va + vb)%nat))
                       ∗ (if b then (∃ P Q vp vt γ_d, typed_proph1_prop IntTypedProph tid vt
                                        ∗ own γ_s (●{1/2} (va + vb)%nat) 
                                        ∗ inv thN (∃ v, read_op_state γ_c γ_s γ_d P Q v vp))
                               else own γ_t (Excl ()) 
                                  ∗ (own γ_s (● (va + vb)%nat) 
                                      ∨ ∃vt, typed_proph1_prop IntTypedProph tid vt)).         
*)                                                     
(*                        ∗ ([∗ set] v ∈ S, ([∗ set] t ∈ T, ∃ a, typed_proph1_prop IntTypedProph t a 
                                                            ∗ read_op_state (γ_t t) P Q)).*)

  Definition is_toy γ_a γ_b γ_c γ_s γ_t la lb := inv toyN (toy_inv γ_a γ_b γ_c γ_s γ_t la lb).

  Lemma read_atomic_spec γ_a γ_b γ_c γ_s γ_t la lb tid vt : 
          typed_proph1_prop IntTypedProph tid vt -∗ ⌜tid ∈ T⌝ -∗
                    is_toy γ_a γ_b γ_c γ_s γ_t la lb -∗ 
                          <<< ∀ (n: nat), toy_cont γ_c n >>>
                                  get #la #lb @ ⊤∖↑N
                          <<< toy_cont γ_c n, RET #n >>>.
  Proof.
    iIntros "Hid t_in_T #HInv".
    iDestruct "t_in_T" as %t_in_T.
    iIntros (Φ) "AU".
    wp_lam. wp_pures.
    wp_apply (typed_proph_wp_new_proph1 IntTypedProph); first done.
    iIntros (vp p) "Hproph". wp_pures.
    wp_bind (! _)%E.
    iInv "HInv" as "H".
    iDestruct "H" as (va vb) "(>Ha & >Hb & >Howna & >Hownb & >Hcont & Hbigstar)".
    wp_load.
    destruct (decide (va + vb < vp)%Z).
    - rewrite (big_sepS_elem_of_acc _ (T) tid); last by eauto.
      iDestruct "Hbigstar" as "(Ht & Hbigstar')".
      iDestruct "Ht" as (b)"Ht".
      iAssert (⌜b = false⌝)%I as "%".
      { destruct b; try done. admit. } subst b.
      iDestruct "Ht" as "(Hexcl & Hsync)".
      iDestruct "Hsync" as "[Hsync | H]"; last first.
      iDestruct "H" as (vt') "H". iExFalso. admit.
      iAssert (own (γ_s tid) (●{1/2} (va + vb)%nat) ∗ own (γ_s tid) (●{1/2} (va + vb)%nat))%I
                 with "[Hsync]" as "(Half1 & Half2)". admit.  
      iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
      iMod (own_alloc (Excl ())) as (γ_d) "Token_d"; first try done. 
      iMod (inv_alloc thN _ (∃ v0, read_op_state (γ_c) (γ_s tid) γ_d AU_later (Φ) (v0) vp%nat)
                                    with "[AU Half1]") as "#HthInv".
      { iNext. iExists (va + vb)%nat. unfold read_op_state. iFrame "∗ #".
        iLeft. unfold state_lin_pending. iFrame. iPureIntro. lia. }
      iModIntro. iSplitR "Hexcl Hproph Token_d". iNext. iExists va, vb.
      iFrame. iApply "Hbigstar'". iExists true.
      iExists AU_later, Φ, vp, vt, γ_d. iFrame "∗#".
      wp_pures. wp_bind (! _)%E.
      iInv "HInv" as "H".
      iDestruct "H" as (va1 vb1) "(>Ha & >Hb & >Howna & >Hownb & >Hcont & Hbigstar)".
      iInv "HthInv" as "H". wp_load.
      iDestruct "H" as (v0)"Hread". 
      rewrite (big_sepS_elem_of_acc _ (T) tid); last by eauto.
      iDestruct "Hbigstar" as "(Ht & Hbigstar')".
      iDestruct "Ht" as (b)"Ht".
      assert (b = true). admit. subst b.
      assert (v0 = (va1 + vb1)%nat). admit. subst v0.
  Admitted.      
(*
      iDestruct "Hread" as "[H1 H2]". iDestruct "H2" as "[H2 | H3]".
      { iEval (unfold state_lin_pending) in "H2". iDestruct "H2" as "(AU_later & pau & %)".
        iModIntro. iSplitL "AU_later pau H1". iNext. iExists (va1 + vb1)%nat.
        unfold read_op_state. iFrame. iLeft. iFrame. iPureIntro. lia.
        iModIntro. iSplitR "Hproph Token_d". iNext. iExists va1, vb1. iFrame.
        iApply "Hbigstar'". iExists true. done. wp_pures.   
        wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done.
        wp_pures. iIntros "%". assert (va ≤ va1). admit. exfalso. lia. }
      iEval (unfold state_lin_done) in "H3". iDestruct "H3" as "(H & %)".
      iDestruct "H" as "[HΦ | Hd]"; last first. iExFalso. admit.    
      iModIntro. iSplitL "Token_d H1". iNext. iExists (va1 + vb1)%nat.
      iFrame. iRight. iFrame "∗#%". iModIntro. iSplitR "HΦ Hproph".
      iNext. iExists va1, vb1. iFrame.
      iApply "Hbigstar'". iExists true. done.
      wp_pures. wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done.
      wp_pures. iIntros "%". wp_pures. by subst vp.   
    - admit.
  Admitted.      
*)      
(*      
      iDestruct "Hif" as (? ? ? vt' ?)"(H & _)".
      iFrame. iRight. by iExists vt'.
      wp_pures. wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done.
      wp_pures. iIntros "%". wp_pures. by subst vp.   

    - assert (vp ≤ va + vb); try lia. destruct (decide (vp = va + vb)).
      + iMod "AU" as (m) "[H◯ [_ Hcl]]".
        iDestruct (auth_agree with "Hcont H◯") as %<-.
        iMod ("Hcl" with "H◯") as "HΦ".
        iModIntro. iSplitR "HΦ Hproph". iNext.
        iExists va, vb, b. iFrame. wp_pures.
        wp_bind (! _)%E. iInv "HInv" as "H".
        iDestruct "H" as (va1 vb1 b1) "(>Ha & >Hb & >Howna & >Hownb & >Hcont & Hif)".
        wp_load. iModIntro. iSplitR "Hproph HΦ".
        iNext. iExists va1, vb1, b1. eauto with iFrame. wp_pures.
        wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done. 
        wp_pures. iIntros "%". wp_pures.
        rewrite e in a0. assert (vb1 = vb); try lia.
        iEval (rewrite H0). admit.
      + iModIntro. iSplitR "Hproph AU".
        iNext. iExists va, vb, b. eauto with iFrame.
        wp_pures. wp_bind (! _)%E. iInv "HInv" as "H".
        iDestruct "H" as (va1 vb1 b1) "(>Ha & >Hb & >Howna & >Hownb & >Hcont & Hif)".
        wp_load. iMod "AU" as (m) "[H◯ [_ Hcl]]".
        iDestruct (auth_agree with "Hcont H◯") as %<-.
        iMod ("Hcl" with "H◯") as "HΦ". iModIntro.
        iSplitR "Hproph HΦ". iNext. iExists va1, vb1, b1.
        eauto with iFrame. wp_pures. 
        wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph"); try done. 
        wp_pures. iIntros "%". wp_pures. admit.


    - assert (b = false). admit. subst b.
      iDestruct "Hif" as "(Hexcl & Hsync)".
      iAssert (own γ_s (●{1/2} (va + vb)%nat) ∗ own γ_s (●{1/2} (va + vb)%nat))%I
                 with "[Hsync]" as "(Half1 & Half2)". admit.  
      iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
      iMod (inv_alloc thN _ (∃ v0, read_op_state (γ_c) (γ_s) AU_later (Φ) (v0) vp%nat)
                                    with "[AU Half1]") as "#HthInv".
      { iNext. iExists (va + vb)%nat. unfold read_op_state. iFrame.
        iLeft. unfold state_lin_pending. iFrame. iSplit.
        iAlways. unfold pau. done. iPureIntro. lia. }
      iModIntro. iSplitR "Hexcl". iNext. iExists va, vb, true.
      iFrame. iExists AU_later, Φ. iApply "HthInv".
      wp_pures. wp_bind (! _)%E.
      iInv "HInv" as "H".
      iDestruct "H" as (va1 vb1 b1) "(>Ha & >Hb & >Howna & >Hownb & >Hcont & Hif)".
      iInv "HthInv" as "H". wp_load.
      iDestruct "H" as (v0)"Hread". 
      assert (b1 = true). admit. subst b1.
      assert (v0 = (va1 + vb1)%nat). admit. subst v0.
      iDestruct "Hread" as "[H1 H2]". iDestruct "H2" as "[H2 | H3]".
      { iEval (unfold state_lin_pending) in "H2". iDestruct "H2" as "(AU_later & pau & %)".
        iModIntro. iSplitL "AU_later pau H1". iNext. iExists (va1 + vb1)%nat.
        unfold read_op_state. iFrame. iLeft. iFrame. iPureIntro. lia.
        iModIntro. iSplit. iNext. iExists va1, vb1, true. iFrame.
        wp_pures.   
        wp_apply (typed_proph_wp_resolve1 IntTypedProph with "Hproph").


      destruct (decide (t_id ∈ T)).
      { rewrite (big_sepS_elem_of _ _ t_id); last done. 
      iDestruct "Hbigstar" as (a' v' P Q)"(Hid' & _)". iExFalso.
      iApply (typed_proph1_prop_excl IntTypedProph). iFrame "Hid Hid'". }
      iSplitR "Hp". iNext. iExists va, vb, S, (T ∪ {[t_id]}). iFrame.
      rewrite (big_sepS_union _ T {[t_id]}); try set_solver. iFrame.
      rewrite (big_sepS_singleton _ t_id).
      iExists a, #v, AU_later, Φ. iFrame "∗ #".
      wp_pures.       
*)

(*
  Lemma g_update (A : iProp) : (|={⊤}=> A -∗ A)%I.
  Proof. 
    iIntros "HR HA".
  Admitted.  
*)
  Lemma ghost_update γ_t γ_s γ_c va vb :
              own γ_c (● Excl' (va + vb + 1)%nat) -∗ 
                      ([∗ set] t_id ∈ T, ∃ b : bool,
                                 if b
                                 then
                                  ∃ P (Q : val → iProp) 
                                    (vp : Z) (vt : typed_proph_type IntTypedProph) 
                                    (γ_d : gname),
                                    typed_proph1_prop IntTypedProph t_id vt
                                    ∗ own (γ_s t_id) (●{1 / 2} (va + vb)%nat)
                                      ∗ □ pau γ_c P Q
                                      ∗ inv thN
                                          (∃ v : nat, read_op_state γ_c (γ_s t_id) γ_d P Q v vp)
                                 else
                                  own γ_t (Excl ())
                                  ∗ (own (γ_s t_id) (● (va + vb)%nat)
                                     ∨ (∃ vt : typed_proph_type IntTypedProph,
                                          typed_proph1_prop IntTypedProph t_id vt)))
                  ={⊤ ∖ ↑toyN }=∗
               own γ_c (● Excl' (va + vb + 1)%nat) ∗ 
                      ([∗ set] t_id ∈ T, ∃ b : bool,
                                 if b
                                 then
                                  ∃ P (Q : val → iProp) 
                                    (vp : Z) (vt : typed_proph_type IntTypedProph) 
                                    (γ_d : gname),
                                    typed_proph1_prop IntTypedProph t_id vt
                                    ∗ own (γ_s t_id) (●{1 / 2} (va + 1 + vb)%nat)
                                      ∗ □ pau γ_c P Q
                                      ∗ inv thN
                                          (∃ v : nat, read_op_state γ_c (γ_s t_id) γ_d P Q v vp)
                                 else
                                  own γ_t (Excl ())
                                  ∗ (own (γ_s t_id) (● (va + 1 + vb)%nat)
                                     ∨ (∃ vt : typed_proph_type IntTypedProph,
                                          typed_proph1_prop IntTypedProph t_id vt))).
  Proof.
    iIntros "Hcont Hbigstar". 
    iInduction T as [|x T' ? IH] "H" using set_ind_L; auto using big_sepS_empty'.
    rewrite (big_sepS_delete _ ({[x]} ∪ T') x); last by set_solver.
    iDestruct "Hbigstar" as "(Hx & Hbigstar')".
    rewrite (big_sepS_delete _ ({[x]} ∪ T') x); last by set_solver.
    assert (({[x]} ∪ T') ∖ {[x]} = T'). set_solver.
    rewrite H0. iDestruct "Hx" as (b)"Hx". destruct b.
    - iDestruct "Hx" as (P Q vp vt γ_d)"(Hproph & Hs & #Pau & #Hinv)".
      iInv "Hinv" as (v)"H'". iEval (unfold read_op_state) in "H'".
      iDestruct "H'" as "(>Hs' & H')".
      iAssert (⌜v = (va + vb)%nat⌝)%I as "%". 
      { admit. } subst v.
      iDestruct "H'" as "[H1 | H2]".
      + iEval (unfold state_lin_pending) in "H1".
        iAssert (own (γ_s x) (●{1 / 2} (va + 1 + vb)%nat) 
               ∗ own (γ_s x) (●{1 / 2} (va + 1 + vb)%nat))%I
                      with "[Hs Hs']" as "(Hs & Hs')". { admit. }
        iDestruct "H1" as "(P & >%)".
        destruct (decide ((va + 1 + vb)%Z = vp)).
        * iDestruct ("Pau" with "P") as ">AU".
          iMod "AU" as (n)"[Hpre [_ Hclose]]".
          iAssert (⌜(va + 1 + vb)%nat = n⌝)%I with "[Hcont Hpre]" as "%".
         { admit. } subst n.
         iMod ("Hclose" with "Hpre") as "HΦ".
         iDestruct ("H" with "Hcont") as "H'".
         iDestruct ("H'" with "Hbigstar'") as "Hbigstar'".
         iModIntro. iSplitR "Hbigstar' Hproph Hs".
         iNext. iExists (va + 1 + vb)%nat. iFrame.
         iRight. unfold state_lin_done.
         iSplitL. iLeft. rewrite <-e. admit.
         iPureIntro. lia. iFrame.
         iDestruct "Hbigstar'" as ">(Hcont & Hbigstar')".
         iModIntro. iFrame.
         iExists true. iExists P, Q, vp, vt, γ_d.
         iFrame "∗#".
       * iDestruct ("H" with "Hcont") as "H'".
         iDestruct ("H'" with "Hbigstar'") as "Hbigstar'".
         iModIntro. iSplitR "Hbigstar' Hproph Hs".
         iNext. iExists (va + 1 + vb)%nat. iFrame.
         iLeft. iFrame. iPureIntro. lia.
         iDestruct "Hbigstar'" as ">(Hcont & Hbigstar')".
         iModIntro. iFrame.             
         iExists true. iExists P, Q, vp, vt, γ_d.
         iFrame "∗#".
      + iDestruct ("H" with "Hcont") as "H'".
        iDestruct ("H'" with "Hbigstar'") as "Hbigstar'".
        iAssert (own (γ_s x) (●{1 / 2} (va + 1 + vb)%nat) 
               ∗ own (γ_s x) (●{1 / 2} (va + 1 + vb)%nat))%I
                      with "[Hs Hs']" as "(Hs & Hs')". { admit. }
        iDestruct "H2" as "(Hor & >%)".              
        iModIntro. iSplitR "Hbigstar' Hproph Hs".
        iNext. iExists (va + 1 + vb)%nat. iFrame. 
        iRight. iSplitL. done. iPureIntro. lia.
        iDestruct "Hbigstar'" as ">(Hcont & Hbigstar')".
        iModIntro. iFrame.             
        iExists true. iExists P, Q, vp, vt, γ_d.
        iFrame "∗#".
    - iDestruct ("H" with "Hcont") as "H'".
      iDestruct ("H'" with "Hbigstar'") as ">Hbigstar'".
      iDestruct "Hbigstar'" as "(Hcont & Hbigstar')".
      iDestruct "Hx" as "(Hexcl & Hor)".
      iDestruct "Hor" as "[H1 | H2]". 
      + iAssert (own (γ_s x) (● (va + 1 + vb)%nat)) 
                      with "[H1]" as "H1". { admit. }
        iModIntro. iFrame. iExists false. iFrame.              
      + iModIntro. iFrame. iExists false. iFrame.
  Admitted.
  
  Lemma write_atomic_spec γ_a γ_b γ_c γ_s γ_t la lb : 
          is_toy γ_a γ_b γ_c γ_s γ_t la lb -∗ 
              <<< ∀ (n: nat), toy_cont γ_c n >>>
                       increment #la #lb @ ⊤∖↑N
              <<< toy_cont γ_c (n+1)%nat, RET #() >>>.
  Proof.
    iIntros "#HInv". iIntros (Φ) "AU".
    wp_lam. wp_pures. wp_bind (nondet_bool #())%E.
    iApply nondet_bool_spec; try done.
    iNext. iIntros (b) "_". wp_pures.
    destruct b.
    - wp_pures.
      awp_apply incr_phy_spec.
      iInv "HInv" as "H".
      iDestruct "H" as (va vb) "(>Ha & >Hb & >Howna & >Hownb & >Hcont & Hbigstar)".
      iAaccIntro with "Ha". { admit. }
      iIntros "Ha".
      iMod "AU" as (n) "[H◯ [_ Hcl]]".
      iDestruct (auth_agree with "Hcont H◯") as %<-.
      iAssert (toy_cont γ_c (va + vb + 1)%nat ∗ own γ_c (● Excl' (va + vb + 1)%nat))%I
                with "[H◯ Hcont]" as "(H◯ & Hcont)". { admit. }  
      iMod ("Hcl" with "H◯") as "HΦ".
      iAssert (own γ_a (● (va+1)%nat))%I with "[Howna]" as "Howna".
      { admit. }
      iDestruct (ghost_update with "[Hcont]") as "H". iFrame "Hcont".
      iDestruct ("H" with "Hbigstar") as "Hbigstar".
      iSplitR "HΦ". iExists (va + 1)%nat, vb.
      iFrame. 
      iSplitL "Ha". iModIntro. iNext. admit.
      iDestruct "Hbigstar" as "H".
      iModIntro.


      iDestruct "Hbigstar" as ">H".
      iApply fupd_intro.
      iSplitL "Hcont". admit.
      
    - admit.            
      
      
      
    







