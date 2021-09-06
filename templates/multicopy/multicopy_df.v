From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export lock multicopy multicopy_util.

Parameter inContents : val.
Parameter findNext : val.
Parameter addContents: val.

(** Template algorithms *)

Definition search (r d: Node) : val := 
  λ: "k",
    lockNode #r;;
    match: (inContents #r "k") with
      SOME "v" => unlockNode #r;; "v"
    | NONE => unlockNode #r;;
              lockNode #d;;
              match: (inContents #d "k") with
                SOME "v" => unlockNode #d;; "v"
              | NONE => unlockNode #d;; #bot end end.
  
Definition upsert (r: Node) : val :=
  rec: "upsert_rec" "k" "v" := 
    lockNode #r ;;
    let: "res" := addContents #r "k" "v" in
    if: "res" then       
      unlockNode #r
    else
      unlockNode #r;;
      "upsert_rec" "k" "v".

(** Proof setup *)

Definition prod3O A B C :=
  prodO (prodO A B) C.

Definition per_node :=
    prod3O (gmapO K (prodO ZO natO)) (gmapO K ZO) (gmapO K natO).

Definition frac_contR := frac_agreeR (per_node).
Definition timeR := authR (max_natUR).

Class multicopy_dfG Σ := MULTICOPY_DF {
                            multicopy_df_frac_contG :> inG Σ frac_contR;
                            multicopy_df_timeG :> inG Σ timeR;
                      }.

Definition multicopy_dfΣ : gFunctors :=
  #[GFunctor frac_contR; GFunctor timeR ].

Instance subG_multicopy_dfΣ {Σ} : subG multicopy_dfΣ Σ → multicopy_dfG Σ.
Proof. solve_inG. Qed.

Section multicopy_df.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_dfG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  (** Assumptions on the implementation made by the template algorithms. *)

  Parameter node : Node → Node → (gmap K V) → iProp.

  Parameter nodeSpatial : Node → iProp.
  
  Parameter node_timeless_proof : ∀ r n V, Timeless (node r n V).
  Global Instance node_timeless r n V: Timeless (node r n V).
  Proof. apply node_timeless_proof. Qed.

  Parameter node_sep_star: ∀ r n V V',
    node r n V ∗ node r n V' -∗ False.

  (** The DF multicopy structure invariant *)

  Definition contents_proj (Cn: gmap K (V*T)) (Vn: gmap K V) (Tn: gmap K T) : iProp :=
      ⌜dom (gset K) Cn = dom (gset K) Vn⌝
    ∗ ⌜dom (gset K) Cn = dom (gset K) Tn⌝
    ∗ ⌜∀ k v t, Cn !! k = Some (v, t) ↔ Vn !! k = Some v ∧ Tn !! k = Some t⌝.

  Definition nodePred γ_s γ_cn r n (Cn: gmap K (V*T)) (Vn: gmap K V) 
                      (Tn: gmap K T) : iProp :=
      node r n Vn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ own (γ_cn) (to_frac_agree (1/2) (Cn, Vn, Tn)).

  Definition cir (H: gset KVT) (Cr Cd: gmap K (V*T)) :=
                   ∀ k v t, ((Cr !! k = Some (v, t) → map_of_set H !! k = Some (v, t))
                 ∧ (Cr !! k = None → map_of_set H !! k = Cd !! k)). 
      
  Definition Inv_DF γ_s γ_cr γ_cd (γ_d: gmap K gname) r d H : iProp :=
    ∃ Cr Vr Tr Cd Vd Td,
      ⌜r ≠ d⌝  
    ∗ ⌜cir H Cr Cd⌝
    ∗ ([∗ set] k ∈ KS, own (γ_d !!! k) (● (MaxNat (Td !!! k))))
    ∗ (∃ br, lockR br r (nodePred γ_s γ_cr r r Cr Vr Tr))
    ∗ own (γ_cr) (to_frac_agree (1/2) (Cr, Vr, Tr))
    ∗ contents_proj Cr Vr Tr
    ∗ (∃ bd, lockR bd d (nodePred γ_s γ_cd r d Cd Vd Td))
    ∗ own (γ_cd) (to_frac_agree (1/2) (Cd, Vd, Td))
    ∗ contents_proj Cd Vd Td.

  Global Instance Inv_DF_timeless γ_s γ_cr γ_cd (γ_d: gmap K gname) r d H:
    Timeless (Inv_DF γ_s γ_cr γ_cd γ_d r d H).
  Proof.
    rewrite /Inv_DF.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    repeat (intros; apply bi.exist_timeless; intros).
    apply bi.sep_timeless; try apply _.
    destruct x5; try apply _.    
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct x5; try apply _.
  Qed.
  
  (** Helper functions specs *)

  Parameter inContents_spec : ∀ r n Vn (k: K),
     ⊢ ({{{ node r n Vn }}}
           inContents #n #k
       {{{ (v: option V), 
              RET (match v with Some v => SOMEV #v | None => NONEV end);
                  node r n Vn ∗ ⌜Vn !! k = v⌝ }}})%I.

  Parameter addContents_spec : ∀ r n Vn (k: K) (v: V),
     ⊢ ({{{ node r n Vn ∗ ⌜n = r⌝ }}}
           addContents #r #k #v
       {{{ (succ: bool) (Vn': gmap K V),
              RET #succ;
                  node r n Vn' ∗ if succ then ⌜Vn' = <[k := v]> Vn⌝ 
                                else ⌜Vn' = Vn⌝ }}})%I.
                                                                   
  (** Lock module **)
    
  Lemma lockNode_spec_high N γ_te γ_he γ_s Prot γ_cr γ_cd γ_d r d n:
    ⊢ mcs_inv N γ_te γ_he γ_s Prot (Inv_DF γ_s γ_cr γ_cd γ_d r d) -∗
        ⌜n = r ∨ n = d⌝ -∗
              <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ γ_cn Cn Vn Tn, nodePred γ_s γ_cn r n Cn Vn Tn
              ∗ ⌜(n = r ∧ γ_cn = γ_cr) ∨ (n = d ∧ γ_cn = γ_cd)⌝ , RET #() >>>.
  Proof.
    iIntros "#mcsInv %". rename H into n_eq_rd.
    iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iInv "mcsInv" as (T H) "(mcs_high & >Inv_DF)".
    iDestruct "Inv_DF" as (Cr Vr Tr Cd Vd Td)"(r_neq_d & Hcir & Hbigstar 
                & HlockR_r & Half_r & Hcts_r & HlockR_d & Half_d & Hcts_d)".
    destruct n_eq_rd as [? | ?]; subst n.            
    - iDestruct "HlockR_r" as (br)"HlockR_r".
      iAaccIntro with "HlockR_r".
      { iIntros "HlockR_r". iModIntro. 
        iFrame "AU". iNext. iExists T, H. 
        eauto 20 with iFrame. }              
      iIntros "(HlockR_r & HnP_r)".
      iMod "AU" as "[_ [_ Hcomm]]".
      iSpecialize ("Hcomm" $! γ_cr Cr Vr Tr).
      iAssert (⌜r = r ∧ γ_cr = γ_cr ∨ r = d ∧ γ_cr = γ_cd⌝)%I as "node_matches".
      {
        iPureIntro. left. done.
      }
      iCombine "HnP_r" "node_matches" as "HnP_r".
      iMod ("Hcomm" with "HnP_r") as "HΦ".
      iModIntro. iFrame "HΦ".
      iNext; iExists T, H. iFrame.
      iExists Cr, Vr, Tr, Cd, Vd, Td. iFrame.
      iExists true; try done.
    - iDestruct "HlockR_d" as (bd)"HlockR_d".
      iAaccIntro with "HlockR_d".
      { iIntros "HlockR_d". iModIntro. 
        iFrame "AU". iNext. iExists T, H. 
        eauto 20 with iFrame. }              
      iIntros "(HlockR_d & HnP_d)".
      iMod "AU" as "[_ [_ Hcomm]]".
      iSpecialize ("Hcomm" $! γ_cd Cd Vd Td).
      iAssert (⌜d = r ∧ γ_cd = γ_cr ∨ d = d ∧ γ_cd = γ_cd⌝)%I as "node_matches".
      {
        iPureIntro. right. done.
      }
      iCombine "HnP_d" "node_matches" as "HnP_d".
      iMod ("Hcomm" with "HnP_d") as "HΦ".
      iModIntro. iFrame "HΦ".
      iNext; iExists T, H. iFrame.
      iExists Cr, Vr, Tr, Cd, Vd, Td. iFrame.
      iExists true; try done.
  Qed.

  Lemma unlockNode_spec_high N γ_te γ_he γ_s Prot γ_cr γ_cd γ_d r d 
                             n Cn Vn Tn γ_cn:
    ⊢ mcs_inv N γ_te γ_he γ_s Prot (Inv_DF γ_s γ_cr γ_cd γ_d r d) -∗
        ⌜(n = r ∧ γ_cn = γ_cr) ∨ (n = d ∧ γ_cn = γ_cd)⌝ -∗
          nodePred γ_s γ_cn r n Cn Vn Tn -∗
              <<< True >>>
                unlockNode #n    @ ⊤ ∖ ↑(mcsN N)
              <<< True, RET #() >>>.
  Proof.
    iIntros "#mcsInv % Hnp". rename H into n_eq_rd.
    iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iInv "mcsInv" as (T H) "(mcs_high & >Inv_DF)".
    iDestruct "Inv_DF" as (Cr Vr Tr Cd Vd Td)"(r_neq_d & Hcir & Hbigstar 
                & HlockR_r & Half_r & Hcts_r & HlockR_d & Half_d & Hcts_d)".
    destruct n_eq_rd as [[? ?] | [? ?]]; subst n γ_cn.            
    - iDestruct "HlockR_r" as (br)"HlockR_r".
      iAssert (⌜Cn = Cr⌝ ∗ ⌜Vn = Vr⌝ ∗ ⌜Tn = Tr⌝)%I as "(% & % & %)".
      { iDestruct "Hnp" as "(_ & _ & Hf)".
        iPoseProof (own_valid_2 _ _ _ with "[$Hf] [$Half_r]") as "H'".
        iDestruct "H'" as %H'. apply frac_agree_op_valid in H'.
        destruct H' as [_ H']. apply leibniz_equiv_iff in H'.
        inversion H'. by iPureIntro. } subst Cn Vn Tn.
      iAssert (lockR true r (nodePred γ_s γ_cr r r Cr Vr Tr)
                ∗ nodePred γ_s γ_cr r r Cr Vr Tr)%I 
                    with "[HlockR_r Hnp]" as "H".
      { destruct br eqn: Hb.
        - (* Case n locked *)
          iFrame "∗".
        - (* Case n unlocked: impossible *)
          iDestruct "Hnp" as "(node & _)".
          iDestruct "HlockR_r" as "(_ & Hnp')".
          iDestruct "Hnp'" as "(node' & _)".
          iExFalso; iApply node_sep_star; try iFrame. }
      iAaccIntro with "H".
      { iIntros "(HlockR_r & Hnp)".
        iModIntro. iFrame.
        iNext; iExists T, H; iFrame.
        iExists Cr, Vr, Tr, Cd, Vd, Td; iFrame.
        iExists true; try done. }
      iIntros "HlockR_r".
      iMod "AU" as "[_ [_ Hcomm]]".
      iMod ("Hcomm" with "[]") as "HΦ"; try done.
      iModIntro. iFrame "HΦ". iNext; iExists T, H.
      iFrame. iExists Cr, Vr, Tr, Cd, Vd, Td. iFrame.
      iExists false; try done.                        
    - iDestruct "HlockR_d" as (bd)"HlockR_d".
      iAssert (⌜Cn = Cd⌝ ∗ ⌜Vn = Vd⌝ ∗ ⌜Tn = Td⌝)%I as "(% & % & %)".
      { iDestruct "Hnp" as "(_ & _ & Hf)".
        iPoseProof (own_valid_2 _ _ _ with "[$Hf] [$Half_d]") as "H'".
        iDestruct "H'" as %H'. apply frac_agree_op_valid in H'.
        destruct H' as [_ H']. apply leibniz_equiv_iff in H'.
        inversion H'. by iPureIntro. } subst Cn Vn Tn.
      iAssert (lockR true d (nodePred γ_s γ_cd r d Cd Vd Td)
                ∗ nodePred γ_s γ_cd r d Cd Vd Td)%I 
                    with "[HlockR_d Hnp]" as "H".
      { destruct bd eqn: Hb.
        - (* Case n locked *)
          iFrame "∗".
        - (* Case n unlocked: impossible *)
          iDestruct "Hnp" as "(node & _)".
          iDestruct "HlockR_d" as "(_ & Hnp')".
          iDestruct "Hnp'" as "(node' & _)".
          iExFalso; iApply node_sep_star; try iFrame. }
      iAaccIntro with "H".
      { iIntros "(HlockR_d & Hnp)".
        iModIntro. iFrame.
        iNext; iExists T, H; iFrame.
        iExists Cr, Vr, Tr, Cd, Vd, Td; iFrame.
        iExists true; try done. }
      iIntros "HlockR_d".
      iMod "AU" as "[_ [_ Hcomm]]".
      iMod ("Hcomm" with "[]") as "HΦ"; try done.
      iModIntro. iFrame "HΦ". iNext; iExists T, H.
      iFrame. iExists Cr, Vr, Tr, Cd, Vd, Td. iFrame.
      iExists false; try done.                        
  Qed.        

End multicopy_df.           
