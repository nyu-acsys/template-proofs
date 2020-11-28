From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Import general_multicopy.

Section compact_proof.
  Context {Σ} `{!heapG Σ, !multicopyG Σ}.
  Notation iProp := (iProp Σ).  
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  Definition nodePred' γ_gh γ_t γ_s lc r n Cn Bn Qn 
                  γ_en γ_cn γ_bn γ_qn γ_cirn es t : iProp :=
      node r n es Cn
    ∗ own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})  
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ (if decide (n = r) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t else ⌜True⌝)%I.

  Definition nodeShared' γ_I γ_R γ_f γ_gh r n Cn Bn Qn H t 
                        γ_en γ_cn γ_bn γ_qn γ_cirn es In Rn: iProp :=
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn  
    ∗ singleton_interfaces_ghost_state γ_I γ_R n In Rn 
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ outflow_constraints n In Rn es Qn
    ∗ (if decide (n = r) then ⌜Bn = map_of_set H⌝ ∗ ⌜inflow_zero In⌝ else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cirn !!! (k)) (● (MaxNat (Bn !!! k))))
    ∗ ⌜φ0 es Qn⌝ ∗ ⌜φ1 Bn Cn Qn⌝ ∗ ⌜φ2 n Bn In⌝ ∗ ⌜φ3 n Bn Rn⌝ 
    ∗ ⌜φ4 n Rn⌝ ∗ ⌜φ5 Bn Qn⌝ ∗ ⌜φ6 Bn t⌝ ∗ ⌜φ7 n es Rn Qn⌝ ∗ ⌜φ8 n In⌝. 

  Definition nodePred_aux γ_gh γ_t γ_s lc r n (Cn Bn Qn : gmap K natUR) 
                          γ_en γ_cn γ_bn γ_qn γ_cirn es t: iProp :=
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})  
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ (if decide (n = r) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t else ⌜True⌝)%I.

  Definition nodeShared_aux γ_I γ_R γ_f γ_gh r n Cn Bn Qn H
                γ_en γ_cn γ_bn γ_qn γ_cirn es In Rn : iProp :=
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_bn γ_qn γ_cirn]})
    ∗ frac_ghost_state γ_en γ_cn γ_bn γ_qn es Cn Bn Qn  
    ∗ singleton_interfaces_ghost_state γ_I γ_R n In Rn 
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ (if decide (n = r) then ⌜Bn = map_of_set H⌝ ∗ ⌜inflow_zero In⌝ else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cirn !!! (k)) (● (MaxNat (Bn !!! k)))).


  Lemma maxnat_set_update (γ: gmap K gname) (S: gset K) (B B': gmap K nat) :
        (⌜∀ k, k ∈ S → B !!! k ≤ B' !!! k⌝) -∗ 
          ([∗ set] k ∈ S, own (γ !!! k) (● MaxNat (B !!! k))) ==∗
            ([∗ set] k ∈ S, own (γ !!! k) (● MaxNat (B' !!! k))).
  Proof.
    iIntros "%".
    iInduction S as [| s S' H'] "IHs" using set_ind_L.
    - iIntros "_"; iModIntro; try done.
    - iIntros "H". 
      rewrite (big_sepS_delete _ ({[s]} ∪ S') s); last first.
      clear; set_solver. 
      iDestruct "H" as "(Hs & H')".
      iMod (own_update (γ !!! s) (● (MaxNat (B !!! s))) 
                    (● (MaxNat (B' !!! s))) with "Hs") as "Hs".
      { apply (auth_update_auth _ _ (MaxNat (B' !!! s))).
        apply max_nat_local_update. simpl. 
        apply H; try set_solver. }
      assert (({[s]} ∪ S') ∖ {[s]} = S') as HS.
      { clear -H'; set_solver. } rewrite HS. 
      rewrite (big_sepS_delete _ ({[s]} ∪ S') s); last first.
      clear; set_solver. iSplitL "Hs". iModIntro; iFrame "Hs".
      rewrite HS. iMod ("IHs" with "[] [$H']") as "H'".
      iPureIntro; intros k Hk; apply H; set_solver. 
      iModIntro; iFrame.
  Qed.

  Lemma ghost_update_contExt γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r lc
                T0' H0 hγ0 I0 R0 
                m Cm0 esm0 Bm0 Qm0 Im0 Rm0
                n Cn Bn Qn γ_en γ_cn γ_bn γ_qn γ_cirn (esn: esT) T In0 Rn0 :
            ⌜m ∉ domm I0⌝
          ∗ ⌜Cm0 = ∅⌝
          ∗ ⌜esm0 = ∅⌝
          ∗ ⌜Bm0 = ∅⌝
          ∗ ⌜Qm0 = ∅⌝
          ∗ ⌜Im0 = int {| infR := {[m := ∅]} ; outR := ∅ |}⌝
          ∗ ⌜Rm0 = int {| infR := {[m := ∅]} ; outR := ∅ |}⌝          
          -∗
            inFP γ_f n
          ∗ nodePred_aux γ_gh γ_t γ_s lc r n Cn Bn Qn 
                         γ_en γ_cn γ_bn γ_qn γ_cirn esn T  
          ∗ nodeShared' γ_I γ_R γ_f γ_gh r n Cn Bn Qn H0 T0' 
                        γ_en γ_cn γ_bn γ_qn γ_cirn esn In0 Rn0
          ∗ global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r T0' H0 hγ0 I0 R0
          ==∗
          ∃ hγ' I0' R0' γ_em γ_cm γ_bm γ_qm γ_cirm,
            inFP γ_f m
          ∗ nodePred_aux γ_gh γ_t γ_s lc r n Cn Bn Qn 
                         γ_en γ_cn γ_bn γ_qn γ_cirn esn T
          ∗ nodeShared' γ_I γ_R γ_f γ_gh r n Cn Bn Qn H0 T0' 
                        γ_en γ_cn γ_bn γ_qn γ_cirn esn In0 Rn0
          ∗ nodePred_aux γ_gh γ_t γ_s lc r m Cm0 Bm0 Qm0 
                         γ_em γ_cm γ_bm γ_qm γ_cirm esm0 T
          ∗ nodeShared_aux γ_I γ_R γ_f γ_gh r m Cm0 Bm0 Qm0 H0 
                            γ_em γ_cm γ_bm γ_qm γ_cirm esm0 Im0 Rm0
          ∗ global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r T0' H0 hγ' I0' R0'
          ∗ ⌜esn !!! m = ∅⌝
          ∗ ⌜out In0 m = 0%CCM⌝
          ∗ ⌜out Rn0 m = 0%CCM⌝
          ∗ ⌜domm I0' = domm I0 ∪ {[m]}⌝
          ∗ ⌜m ≠ r⌝ ∗ ⌜m ≠ n⌝.
  Proof.
    iIntros "(%&%&%&%&%&%&%) (#FP_n & HnP_aux & HnS_n' & Hglob)".
    rename H into m_notin_I0. rename H1 into Em_Cm0. rename H2 into Hesm.
    rename H3 into HBm0. rename H4 into HQm0. rename H5 into HIm0.
    rename H6 into HRm0.
        iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".   

        iAssert (⌜n ∈ domm I0⌝)%I as "%". 
        { by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rename H into n_in_I0.  

        iDestruct "HnP_aux" as "(HnP_gh & HnP_frac & HnP_C & HnP_t)".
        iDestruct "HnS_n'" as 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".

        iAssert (⌜r ∈ domm I0⌝)%I as "%". 
        { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
        rename H into r_in_I0.
        assert (m ≠ r) as m_neq_r. 
        { clear -m_notin_I0 r_in_I0. set_solver. }
        assert (m ≠ n) as m_neq_n. 
        { clear -m_notin_I0 n_in_I0. set_solver. }
        assert (domm Im0 = {[m]}) as Domm_Im0.
        { subst Im0. unfold domm, dom, flowint_dom.
          unfold inf_map. simpl. apply leibniz_equiv. 
          by rewrite dom_singleton. }
        assert (domm Rm0 = {[m]}) as Domm_Rm0.
        { subst Rm0. unfold domm, dom, flowint_dom.
          unfold inf_map. simpl. apply leibniz_equiv. 
          by rewrite dom_singleton. }  

        iAssert (⌜esn !!! m = ∅⌝)%I as %Esn_empty.
        { destruct (decide (esn !!! m = ∅)); try done.
          iAssert (⌜esn !!! m ≠ ∅⌝)%I as "H'".
          by iPureIntro. 
          iPoseProof ("HnS_cl" with "H'") as "Hfp_m".
          iAssert (⌜m ∈ domm I0⌝)%I as "%". 
          { by iPoseProof (inFP_domm _ _ _ with "[$Hfp_m] [$Hf]") as "H''". }
          iPureIntro. clear -H m_notin_I0. set_solver. }
        
        iPoseProof (own_valid with "HI") as "%".
        rename H into Valid_I0.
        rewrite auth_auth_valid in Valid_I0 *; intros Valid_I0. 

        iDestruct "HnS_si" as "(HnI & HnR & Domm_In0 & Domm_Rn0)".
        iPoseProof (own_valid with "HnI") as "%".
        rename H into Valid_In0. 
        rewrite auth_frag_valid in Valid_In0 *; intros Valid_In0.
        iPoseProof (own_valid with "HnR") as "%".
        rename H into Valid_Rn0. 
        rewrite auth_frag_valid in Valid_Rn0 *; intros Valid_Rn0.
        iDestruct "Domm_In0" as %Domm_In0.
        iDestruct "Domm_Rn0" as %Domm_Rn0.
        
        assert (✓ Im0) as Valid_Im0.
        { unfold valid, cmra_valid, flowint_valid.
          subst Im0. simpl. split.
          solve_map_disjoint. 
          intros _; try done. }
        assert (✓ Rm0) as Valid_Rm0.
        { unfold valid, cmra_valid, flowint_valid.
          subst Rm0. simpl. split.
          solve_map_disjoint. 
          intros _; try done. }

        iPoseProof ((auth_own_incl γ_I I0 In0) with "[$HI $HnI]") as "%".
        rename H into Incl_In0. destruct Incl_In0 as [Iz Incl_In0].
        iDestruct "Out_I" as %Out_I.
        assert (out In0 m = 0%CCM ∧ out Iz m = 0%CCM) as [Out_In_m Out_Iz_m].
        { unfold outflow_zero in Out_I.
          rewrite Incl_In0 in Valid_I0*; intro H'.
          rewrite Incl_In0 in m_notin_I0*; intro H''.
          pose proof (intComp_unfold_out In0 Iz H' m H'') as Hout.
          unfold out in Hout. unfold out.
          rewrite <-Incl_In0 in Hout. rewrite Out_I in Hout. 
          rewrite nzmap_lookup_empty in Hout. 
          unfold ccmunit, ccm_unit in Hout. simpl in Hout.
          unfold lift_unit in Hout. unfold ccmop, ccm_op in Hout.
          simpl in Hout. unfold lift_op in Hout.
          unfold ccmop, ccm_op in Hout. simpl in Hout.
          rewrite nzmap_eq in Hout*; intros Hout.
          unfold ccmunit, lift_unit. split; apply nzmap_eq;
          intros k; rewrite nzmap_lookup_empty;
          unfold ccmunit, ccm_unit; simpl;
          unfold nat_unit; pose proof Hout k as Hout;
          rewrite nzmap_lookup_empty in Hout;
          unfold ccmunit, ccm_unit in Hout;
          simpl in Hout; unfold nat_unit, nat_op in Hout;
          rewrite nzmap_lookup_merge in Hout; clear-Hout; lia. }

        assert (✓ (In0 ⋅ Im0)) as Valid_Inm0.
        { apply intValid_composable. unfold intComposable.
          repeat split; try done.
          * rewrite Domm_In0 Domm_Im0.
            clear -m_notin_I0 n_in_I0.
            set_solver.
          * unfold map_Forall. intros n' x Hinf.
            subst Im0. unfold out. simpl.
            rewrite nzmap_lookup_empty.
            rewrite ccm_left_id. rewrite ccm_pinv_unit.
            unfold inf. by rewrite Hinf.
          * unfold map_Forall. intros n' x Hinf.
            destruct (decide (n' = m)).
            ** subst n'. rewrite Out_In_m.
               rewrite ccm_left_id. rewrite ccm_pinv_unit.
               unfold inf. by rewrite Hinf.
            ** subst Im0. simpl in Hinf.
               rewrite lookup_singleton_ne in Hinf; try done. }

        assert (domm (In0 ⋅ Im0) = {[n; m]}) as Domm_Inm0.
        { rewrite flowint_comp_fp; try done.
          by rewrite Domm_In0 Domm_Im0. }
        assert (domm I0 = domm In0 ∪ domm Iz) as Domm_Inz.
        { rewrite Incl_In0. rewrite flowint_comp_fp. done.
          by rewrite <-Incl_In0. }   
        assert (n ∉ domm Iz) as n_notin_Iz.
        { rewrite Incl_In0 in Valid_I0 *; intros Valid_In0'.
          apply intComposable_valid in Valid_In0'.
          unfold intComposable in Valid_In0'.
          destruct Valid_In0' as [_ [_ [H' _]]].
          rewrite Domm_In0 in H'. clear -H'; set_solver. }

        assert (m ∉ domm Iz) as m_notin_Iz.
        { clear -Domm_Inz m_notin_I0. set_solver. }
          
                
        iMod (own_updateP (flowint_update_P (_) I0 In0 (In0 ⋅ Im0)) γ_I
                   (● I0 ⋅ ◯ (In0)) with "[HI HnI]") as (Io) "H'".
        { rewrite Incl_In0. apply flowint_update. 
          split; last split.
          - unfold contextualLeq.
            repeat split; try done.
            + rewrite flowint_comp_fp; try done.
              clear; set_solver.
            + intros n' H'.
              assert (n' = n) as Hn.
              { rewrite Domm_In0 in H'.
                clear -H'; set_solver. }
              subst n'.
              pose proof (intComp_inf_1 In0 Im0 Valid_Inm0 n H') as H''.
              rewrite H''. subst Im0; unfold out; simpl.
              rewrite nzmap_lookup_empty.
              by rewrite ccm_pinv_unit. 
            + intros n' H'.
              pose proof (intComp_unfold_out In0 Im0 Valid_Inm0 n' H') as H''.
              rewrite H''. unfold out at 3, out_map. subst Im0.
              simpl. rewrite nzmap_lookup_empty.
              by rewrite ccm_right_id.
          - rewrite Domm_Inm0. clear -n_notin_Iz m_notin_Iz.
            set_solver.
          - intros n' Hn'. rewrite Domm_Inm0 Domm_In0 in Hn'.
            assert (n' = m) as H'. clear -Hn'. set_solver.
            subst n'. by unfold out in Out_Iz_m. }              

        { rewrite own_op. iFrame. }                        
        iPoseProof ((flowint_update_result' γ_I I0 In0 (In0 ⋅ Im0))
                        with "H'") as (I0') "(% & % & (HI & HIn))".
        rename H into ContLeq_I0. clear Io. 
        destruct H1 as [Io [HI0 HI0']].
        iEval (rewrite auth_frag_op) in "HIn".
        iDestruct "HIn" as "(HIn & HIm)".
        iPoseProof (own_valid with "HI") as "%".
        rename H into Valid_I0'.
        rewrite auth_auth_valid in Valid_I0' *; intros Valid_I0'. 

        assert (domm I0' = domm I0 ∪ {[m]}) as Domm_I0'.
        { rewrite Incl_In0 in HI0*; intros H'.
          apply intComp_cancelable in H'. 
          rewrite HI0'. repeat rewrite flowint_comp_fp.
          rewrite Domm_Im0 H'. clear; set_solver.
          rewrite Incl_In0 in Valid_I0 *; intros H''.
          done. done. apply leibniz_equiv_iff in HI0'. 
          by rewrite <-HI0'. by rewrite <-Incl_In0. }

        assert (domm I0' ∖ {[m]} = domm I0) as Domm_I0_m.
        { clear -Domm_I0' m_notin_I0. set_solver. }  

        
        iAssert (⌜r ∈ domm R0⌝)%I as "%". 
        { iDestruct "domm_IR" as %H'. iPureIntro. by rewrite <-H'. }
        rename H into r_in_R0.
        iAssert (⌜m ∉ domm R0⌝)%I as "%".
        { iDestruct "domm_IR" as %H'. iPureIntro. by rewrite <-H'. }
        rename H into m_notin_R0.
        iAssert (⌜n ∈ domm R0⌝)%I as "%".
        { iDestruct "domm_IR" as %H'. iPureIntro. by rewrite <-H'. }
        rename H into n_in_R0.        
        
        iPoseProof (own_valid with "HR") as "%".
        rename H into Valid_R0.
        rewrite auth_auth_valid in Valid_R0 *; intros Valid_R0. 
        
        iPoseProof ((auth_own_incl γ_R R0 Rn0) with "[$HR $HnR]") as "%".
        rename H into Incl_Rn0. destruct Incl_Rn0 as [Rz Incl_Rn0].
        iDestruct "Out_R" as %Out_R.
        assert (out Rn0 m = 0%CCM ∧ out Rz m = 0%CCM) as [Out_Rn_m Out_Rz_m].
        { unfold outflow_zero in Out_R.
          rewrite Incl_Rn0 in Valid_R0*; intro H'.
          rewrite Incl_Rn0 in m_notin_R0*; intro H''.
          pose proof (intComp_unfold_out Rn0 Rz H' m H'') as Hout.
          unfold out in Hout. unfold out.
          rewrite <-Incl_Rn0 in Hout. rewrite Out_R in Hout. 
          rewrite nzmap_lookup_empty in Hout. 
          unfold ccmunit, ccm_unit in Hout. simpl in Hout.
          unfold lift_unit in Hout. unfold ccmop, ccm_op in Hout.
          simpl in Hout. unfold lift_op in Hout.
          unfold ccmop, ccm_op in Hout. simpl in Hout.
          rewrite nzmap_eq in Hout*; intros Hout.
          unfold ccmunit, lift_unit. split; apply nzmap_eq;
          intros k; rewrite nzmap_lookup_empty;
          unfold ccmunit, ccm_unit; simpl;
          unfold nat_unit; pose proof Hout k as Hout;
          rewrite nzmap_lookup_empty in Hout;
          unfold ccmunit, ccm_unit in Hout;
          simpl in Hout; unfold nat_unit, nat_op in Hout;
          rewrite nzmap_lookup_merge in Hout; clear-Hout; lia. }

        assert (✓ (Rn0 ⋅ Rm0)) as Valid_Rnm0.
        { apply intValid_composable. unfold intComposable.
          repeat split; try done.
          * rewrite Domm_Rn0 Domm_Rm0.
            clear -m_notin_R0 n_in_R0.
            set_solver.
          * unfold map_Forall. intros n' x Hinf.
            subst Rm0. unfold out. simpl.
            rewrite nzmap_lookup_empty.
            rewrite ccm_left_id. rewrite ccm_pinv_unit.
            unfold inf. by rewrite Hinf.
          * unfold map_Forall. intros n' x Hinf.
            destruct (decide (n' = m)).
            ** subst n'. rewrite Out_Rn_m.
               rewrite ccm_left_id. rewrite ccm_pinv_unit.
               unfold inf. by rewrite Hinf.
            ** subst Rm0. simpl in Hinf.
               rewrite lookup_singleton_ne in Hinf; try done. }

        assert (domm (Rn0 ⋅ Rm0) = {[n; m]}) as Domm_Rnm0.
        { rewrite flowint_comp_fp; try done.
          by rewrite Domm_Rn0 Domm_Rm0. }
        assert (domm R0 = domm Rn0 ∪ domm Rz) as Domm_Rnz.
        { rewrite Incl_Rn0. rewrite flowint_comp_fp. done.
          by rewrite <-Incl_Rn0. }   
        assert (n ∉ domm Rz) as n_notin_Rz.
        { rewrite Incl_Rn0 in Valid_R0 *; intros Valid_Rn0'.
          apply intComposable_valid in Valid_Rn0'.
          unfold intComposable in Valid_Rn0'.
          destruct Valid_Rn0' as [_ [_ [H' _]]].
          rewrite Domm_Rn0 in H'. clear -H'; set_solver. }
        assert (m ∉ domm Rz) as m_notin_Rz.
        { clear -Domm_Rnz m_notin_R0. set_solver. }               

        iMod (own_updateP (flowint_update_P (_) R0 Rn0 (Rn0 ⋅ Rm0)) γ_R
                   (● R0 ⋅ ◯ (Rn0)) with "[HR HnR]") as (Ro) "H'".
        { rewrite Incl_Rn0. apply flowint_update. 
          split; last split.
          - unfold contextualLeq.
            repeat split; try done.
            + rewrite flowint_comp_fp; try done.
              clear; set_solver.
            + intros n' H'.
              assert (n' = n) as Hn.
              { rewrite Domm_Rn0 in H'.
                clear -H'; set_solver. }
              subst n'.
              pose proof (intComp_inf_1 Rn0 Rm0 Valid_Rnm0 n H') as H''.
              rewrite H''. subst Rm0; unfold out; simpl.
              rewrite nzmap_lookup_empty.
              by rewrite ccm_pinv_unit. 
            + intros n' H'.
              pose proof (intComp_unfold_out Rn0 Rm0 Valid_Rnm0 n' H') as H''.
              rewrite H''. unfold out at 3, out_map. subst Rm0.
              simpl. rewrite nzmap_lookup_empty.
              by rewrite ccm_right_id.
          - rewrite Domm_Rnm0. clear -n_notin_Rz m_notin_Rz.
            set_solver.
          - intros n' Hn'. rewrite Domm_Rnm0 Domm_Rn0 in Hn'.
            assert (n' = m) as H'. clear -Hn'. set_solver.
            subst n'. by unfold out in Out_Rz_m. }              
        { rewrite own_op. iFrame. }                        
        iPoseProof ((flowint_update_result γ_R R0 Rn0 (Rn0 ⋅ Rm0))
                        with "H'") as (R0') "(% & % & (HR & HRn))".
        rename H into ContLeq_R0. clear Ro. 
        destruct H1 as [Ro [HR0 HR0']].
        iEval (rewrite auth_frag_op) in "HRn".
        iDestruct "HRn" as "(HRn & HRm)".
        iPoseProof (own_valid with "HR") as "%".
        rename H into Valid_R0'.
        rewrite auth_auth_valid in Valid_R0' *; intros Valid_R0'. 

        assert (domm R0' = domm R0 ∪ {[m]}) as Domm_R0'.
        { rewrite Incl_Rn0 in HR0*; intros H'.
          apply intComp_cancelable in H'. 
          rewrite HR0'. repeat rewrite flowint_comp_fp.
          rewrite Domm_Rm0 H'. clear; set_solver.
          rewrite Incl_Rn0 in Valid_R0 *; intros H''.
          done. done. apply leibniz_equiv_iff in HR0'. 
          by rewrite <-HR0'. by rewrite <-Incl_Rn0. }
        assert (domm R0' ∖ {[m]} = domm R0) as Domm_R0_m.
        { clear -Domm_R0' m_notin_R0. set_solver. }
        iDestruct "Inf_R" as %Inf_R.  
        iAssert (⌜inflow_R R0' r⌝)%I as "Inf_R'".
        { iPureIntro. unfold inflow_R. intros n' k.
          destruct (decide (n' = r)) eqn: Hn'.
          + subst n'. pose proof Inf_R r k as Inf_R.
            rewrite Hn' in Inf_R.
            unfold contextualLeq in ContLeq_R0.
            destruct ContLeq_R0 as [_ [_ [_ [H' _]]]].
            pose proof H' r r_in_R0 as H'.
            unfold in_inset. unfold in_inset in Inf_R.
            by rewrite <-H'. 
          + pose proof Inf_R n' k as Inf_R.
            rewrite Hn' in Inf_R.
            unfold contextualLeq in ContLeq_R0.
            destruct ContLeq_R0 as [_ [_ [_ [H' H'']]]].
            destruct (decide (n' ∈ domm R0)).
            * pose proof H' n' e as H'.
              unfold in_inset. unfold in_inset in Inf_R.
              by rewrite <-H'.
            * destruct (decide (n' = m)).
              ** subst n'.
                 pose proof (intComp_inf_2 R0 Rm0) as Hinf.
                 rewrite cmra_comm in HR0' *; intros HR0'.
                 rewrite cmra_assoc in HR0' *; intros HR0'.
                 rewrite cmra_comm in HR0 *; intros HR0.
                 rewrite <-HR0 in HR0'.
                 rewrite HR0' in Valid_R0'.
                 assert (m ∈ domm Rm0) as m_in_Rm0.
                 { rewrite Domm_Rm0. clear; set_solver. }
                 pose proof Hinf Valid_R0' m m_in_Rm0 as Hinf.
                 apply leibniz_equiv_iff in HR0'. 
                 rewrite <-HR0' in Hinf.
                 unfold in_inset. rewrite Hinf.
                 unfold outflow_zero_R in Out_R.
                 unfold out. rewrite Out_R.
                 rewrite nzmap_lookup_empty.
                 subst Rm0. unfold inf. simpl.
                 rewrite lookup_singleton.
                 simpl. rewrite ccm_pinv_unit.
                 clear. unfold dom_ms, dom, nzmap_dom.
                 set_solver.
              ** assert (n' ∉ domm R0') as Hdom.
                 { rewrite Domm_R0'.
                   clear -n1 n2. set_solver. }
                 unfold domm, dom, flowint_dom in Hdom.
                 destruct R0' as [ [Rinf Rout] | ]; last by contradiction.
                 simpl in Hdom. rewrite not_elem_of_dom in Hdom *; intros Hdom.
                 unfold in_inset. unfold inf, inf_map.
                 simpl. rewrite Hdom. simpl.
                 unfold ccmunit, ccm_unit, lift_unit.
                 unfold dom_ms, dom, flowint_dom, nzmap_dom.
                 unfold nzmap_unit. simpl. clear; set_solver. }

        iMod (own_update γ_f (● domm I0) (● (domm I0 ∪ {[m]}) ⋅ ◯ ({[m]}))
                         with "[Hf]") as "(Hf & H')"; try done.
        { apply (auth_update_alloc (domm I0) (domm I0 ∪ {[m]}) ({[m]})).
          apply local_update_discrete.
          intros mz _ Hmz. split; try done.
          rewrite gset_opM in Hmz. rewrite gset_opM.
          rewrite Hmz. clear. set_solver. }
        iEval (rewrite <-Domm_I0') in "Hf".
        iAssert (inFP γ_f m) with "H'" as "#FP_m".
        iDestruct "H'" as "HnS_FPm".
        
        iMod (own_alloc (to_frac_agree (1) (esm0))) 
              as (γ_em)"Hesm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hesm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hesm_f". 
        iDestruct "Hesm_f" as "(HnS_esm & HnP_esm)".        

        iMod (own_alloc (to_frac_agree (1) (Cm0))) 
              as (γ_cm)"Hcm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hcm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hcm_f". 
        iDestruct "Hcm_f" as "(HnS_cm & HnP_cm)".        

        iMod (own_alloc (to_frac_agree (1) (Bm0))) 
              as (γ_bm)"Hbm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hbm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hbm_f". 
        iDestruct "Hbm_f" as "(HnS_bm & HnP_bm)".        

        iMod (own_alloc (to_frac_agree (1) (Qm0))) 
              as (γ_qm)"Hqm_f". { try done. }
        iEval (rewrite <-Qp_half_half) in "Hqm_f".      
        iEval (rewrite (frac_agree_op (1/2) (1/2) _)) in "Hqm_f". 
        iDestruct "Hqm_f" as "(HnS_qm & HnP_qm)".
        
        iAssert (frac_ghost_state γ_em γ_cm γ_bm γ_qm esm0 Cm0 Bm0 Qm0
                ∗ frac_ghost_state γ_em γ_cm γ_bm γ_qm esm0 Cm0 Bm0 Qm0)%I
                with "[HnS_esm HnP_esm HnS_cm HnP_cm HnS_bm HnP_bm HnS_qm HnP_qm]"
                as "(HnS_fracm & HnP_fracm)".
        { iFrame. }               

        iMod (own_alloc_set KS with "[]") as "HnS_starm"; first done.
        iDestruct "HnS_starm" as (γ_cirm)"HnS_starm".
        
        iDestruct "domm_IR" as "#domm_IR".
        iDestruct "domm_Iγ" as "#domm_Iγ".
        iMod ((ghost_heap_update γ_gh hγ0 m γ_em γ_cm γ_bm γ_qm γ_cirm) 
                    with "[] [$Hγ]") as "(Hγ & #HnS_ghm)".
        { iDestruct "domm_Iγ" as %H'. iPureIntro.
          rewrite <-H'. apply m_notin_I0. }            

        assert (set_of_map Cm0 = ∅) as Set_of_Cm0.
        { unfold set_of_map. subst Cm0.
          by rewrite map_fold_empty. }
        iMod (own_update γ_s (● H0) (● H0 ⋅ ◯ (set_of_map Cm0))
                 with "[$HH]") as "HH".
        { apply (auth_update_alloc _ (H0) (set_of_map Cm0)).
          rewrite Set_of_Cm0.
          apply local_update_discrete. intros mz Valid_H1 H1_eq.
          split; try done. }
        iDestruct "HH" as "(HH & HnP_Cm)".

        iAssert (⌜history_init H0⌝)%I as "%".
        { by iDestruct "Hist" as "%". }
        rename H into Hist.
        
        iAssert (closed γ_f esm0) as "HnS_clm".
        { iIntros (n')"%". rename H into H'.
          exfalso. rewrite Hesm in H'.
          rewrite /(∅ !!! n') in H'.
          unfold finmap_lookup_total in H'.
          rewrite lookup_empty in H'.
          simpl in H'. clear -H'; done. }

        iAssert (⌜outflow_zero I0'⌝)%I as "Out_I'".
        { iPureIntro. unfold outflow_zero.
          apply nzmap_eq. intros n'.
          destruct (decide (n' ∈ domm I0')).
          + pose proof intValid_in_dom_not_out I0' n' Valid_I0' e as H'.
            unfold out in H'. rewrite H'.
            by rewrite nzmap_lookup_empty.
          + destruct ContLeq_I0 as [_ [_ [_ [H' H'']]]].
            pose proof H'' n' n0 as H''.
            unfold out in H''. rewrite <-H''.
            apply leibniz_equiv in Out_I.
            rewrite nzmap_eq in Out_I *; intros Out_I.
            pose proof Out_I n' as Out_I.
            by rewrite Out_I. }  

        iAssert (⌜outflow_zero_R R0'⌝)%I as "Out_R'".
        { iPureIntro. unfold outflow_zero.
          apply nzmap_eq. intros n'.
          destruct (decide (n' ∈ domm R0')).
          + pose proof intValid_in_dom_not_out R0' n' Valid_R0' e as H'.
            unfold out in H'. rewrite H'.
            by rewrite nzmap_lookup_empty.
          + destruct ContLeq_R0 as [_ [_ [_ [H' H'']]]].
            pose proof H'' n' n0 as H''.
            unfold out in H''. rewrite <-H''.
            apply leibniz_equiv in Out_R.
            rewrite nzmap_eq in Out_R *; intros Out_R.
            pose proof Out_R n' as Out_R.
            by rewrite Out_R. }  

        
    iModIntro. iExists (<[m:=ghost_loc γ_em γ_cm γ_bm γ_qm γ_cirm]> hγ0), 
                    I0', R0', γ_em, γ_cm, γ_bm, γ_qm, γ_cirm. 
    iSplitR. iFrame "FP_m".
    iSplitL "HnP_gh HnP_frac HnP_C HnP_t". { iFrame. }
    iSplitL "HnS_gh HnS_frac HnS_FP HnS_cl HnS_oc HnS_H HnS_star HIn HRn Hφ".
    { iFrame. by iPureIntro. }
    iSplitL "HnP_fracm HnP_Cm". 
    { iFrame "∗#". destruct (decide (m = r)); try done. }
    iSplitL "HnS_fracm HnS_starm HIm HRm".
    { iFrame "∗#". iSplitR. by iPureIntro.
      iSplitR. destruct (decide (m = r)); try done. 
      iApply (big_sepS_mono 
                (λ y, own (γ_cirm !!! y) (● {| max_nat_car := 0 |}) )%I
                (λ y, own (γ_cirm !!! y) (● {| max_nat_car := Bm0 !!! y |}))%I
                KS); try done.
      { intros k HKS. iFrame. rewrite HBm0. rewrite /(∅ !!! k). 
        unfold finmap_lookup_total. rewrite lookup_empty.
        simpl. try eauto. } }
    iFrame "∗#". iDestruct "domm_IR" as %domm_IR.
    iDestruct "domm_Iγ" as %domm_Iγ.
    iPureIntro. repeat split; try done.
    by rewrite Domm_I0' Domm_R0' domm_IR.
    apply leibniz_equiv. rewrite dom_insert.
    rewrite Domm_I0' domm_Iγ. clear; set_solver.
  Qed.

  
  Lemma ghost_update_interface_mod γ_I γ_R γ_f γ_gh γ_t γ_s lc r H0 T0'  
                m Cm0 esm0 Bm0 Qm0 γ_em γ_cm γ_bm γ_qm
               γ_cirm Im0 Rm0
                n Cn Bn Qn γ_en γ_cn γ_bn γ_qn γ_cirn esn esn' T In0 Rn0 :
            ⌜Cm0 = ∅⌝
          ∗ ⌜esm0 = ∅⌝
          ∗ ⌜Bm0 = ∅⌝
          ∗ ⌜Qm0 = ∅⌝
          ∗ ⌜Im0 = int {| infR := {[m := ∅]} ; outR := ∅ |}⌝
          ∗ ⌜Rm0 = int {| infR := {[m := ∅]} ; outR := ∅ |}⌝
          ∗ ⌜esn' = <[m := (esn' !!! m)]> esn⌝
          ∗ ⌜esn !!! m = ∅⌝
          ∗ ⌜out In0 m = 0%CCM⌝
          ∗ ⌜out Rn0 m = 0%CCM⌝
          ∗ ⌜history_init H0⌝          
          ∗ ⌜m ≠ r⌝
          -∗
            node r n esn' Cn
          ∗ nodePred_aux γ_gh γ_t γ_s lc r n Cn Bn Qn 
                         γ_en γ_cn γ_bn γ_qn γ_cirn esn T  
          ∗ nodeShared' γ_I γ_R γ_f γ_gh r n Cn Bn Qn H0 T0' 
                        γ_en γ_cn γ_bn γ_qn γ_cirn esn In0 Rn0
          ∗ node r m esm0 Cm0
          ∗ nodePred_aux γ_gh γ_t γ_s lc r m Cm0 Bm0 Qm0 γ_em γ_cm γ_bm γ_qm
               γ_cirm esm0 T
          ∗ nodeShared_aux γ_I γ_R γ_f γ_gh r m Cm0 Bm0 Qm0 H0 γ_em γ_cm γ_bm
               γ_qm γ_cirm esm0 Im0 Rm0     
          ==∗
          ∃ Bn0' Qn0',
            nodePred' γ_gh γ_t γ_s lc r n Cn Bn0' Qn0' 
                      γ_en γ_cn γ_bn γ_qn γ_cirn esn' T 
          ∗ nodeShared γ_I γ_R γ_f γ_gh r n Cn Bn0' Qn0' H0 T0' 
          ∗ nodePred' γ_gh γ_t γ_s lc r m Cm0 Bm0 Qm0 
                         γ_em γ_cm γ_bm γ_qm γ_cirm esm0 T
          ∗ nodeShared γ_I γ_R γ_f γ_gh r m Cm0 Bm0 Qm0 H0 T0'.
  Proof.
    iIntros "(%&%&%&%&%&%&%&%&%&%&%&%) (node_n & HnP_aux & HnS_n' & 
                            node_m & HnP_auxm & HnS_auxm)".
    rename H into Em_Cm0. rename H1 into Hesm. rename H2 into HBm0. 
    rename H3 into HQm0. rename H4 into HIm0. rename H5 into HRm0. 
    rename H6 into Hesn'. rename H7 into Esn_empty.
    rename H8 into Out_In_m. rename H9 into Out_Rn_m.
    rename H10 into Hist. rename H11 into m_neq_r.
    
        iDestruct "HnP_aux" as "(HnP_gh & HnP_frac & HnP_C & HnP_t)".
        iDestruct "HnS_auxm" as "(HnS_ghm & HnS_fracm & HnS_sim & #HnS_FPm 
                                & HnS_clm & HnS_Hm & HnS_starm)".
        iDestruct "HnS_n'" as  
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".

        iDestruct "HnS_si" as "(HIn & HRn & Domm_In0 & Domm_Rn0)".
        iDestruct "HnS_sim" as "(HIm & HRm & Domm_Im0 & Domm_Rm0)".
        iDestruct "Domm_In0" as %Domm_In0.
        iDestruct "Domm_Im0" as %Domm_Im0.
        iDestruct "Domm_Rn0" as %Domm_Rn0.
        iDestruct "Domm_Rm0" as %Domm_Rm0.
        
        set (Sr := KS ∩ (esn' !!! m ∩ inset K Rn0 n)).
        set (Sr_map := map_restriction Sr ∅).
        set (Sr_mset := map_subset Sr ∅).
        set (Sb := KS ∩ (Sr ∖ dom (gset K) Cn)).
        set (Sb_map := map_restriction Sb ∅). 
        set (Qn0' := gmap_insert_map Qn Sr_map).
        set (Bn0' := gmap_insert_map Bn Sb_map).
        set (In0' := outflow_insert_set In0 m Sr_mset).
        set (Im0' := inflow_insert_set Im0 m Sr_mset). 
        set (Rn0' := outflow_insert_set Rn0 m Sr).
        set (Rm0' := inflow_insert_set Rm0 m Sr).


        iMod ((frac_update γ_en γ_cn γ_bn γ_qn esn Cn Bn Qn esn' Cn Bn0' Qn0') 
             with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".

        iPoseProof ((node_edgeset_disjoint r n) with "[$node_n]") as "%".
        rename H into Disj_esn'.                        

        iAssert (closed γ_f esn')%I with "[HnS_cl]" as "HnS_cl".
        { unfold closed. iIntros (n')"%". rename H into Hn'.
          destruct (decide (n' = m)).
          + subst n'; try done.
          + rewrite Hesn' in Hn'.
            rewrite lookup_total_insert_ne in Hn'; try done.
            iApply "HnS_cl". by iPureIntro. }

        assert (∀ k, k ∈ Sr → (∀ n', k ∉ esn !!! n')) as Esn_not.
        { intros k Hk. subst Sr. 
          rewrite !elem_of_intersection in Hk*; intros Hk.
          destruct Hk as [_ [Hk _]].
          intros n'. destruct (decide (k ∈ esn !!! n')); try done.
          destruct (decide (n' = m)).
          - subst n'. clear -e Esn_empty. set_solver.
          - assert (k ∈ esn' !!! n') as H'. 
            rewrite Hesn'. rewrite lookup_total_insert_ne; try done.
            pose proof Disj_esn' n' m n0 as H''.
            clear -H'' H' Hk. set_solver.  } 

        iAssert (⌜φ0 esn Qn⌝)%I as "%".
        { by iDestruct "Hφ" as "(%&_)". }
        rename H into Hφ0.

        iAssert (⌜∀ k, k ∈ Sb → Bn !!! k = 0⌝)%I as %HSb.
        { iDestruct "Hφ" as "(_&%&_)". rename H into Hφ1.
          iPureIntro. intros k Hk. subst Sb. 
          rewrite elem_of_intersection in Hk *; intros Hk.
          destruct Hk as [_ Hk].
          rewrite elem_of_difference in Hk *; intros Hk.
          destruct Hk as [Hk1 Hk2].
          rewrite not_elem_of_dom in Hk2*; intros Hk2.
          pose proof (Esn_not k Hk1) as Hk'.
          subst Sr.  rewrite elem_of_intersection in Hk1*; intros Hk1.
          destruct Hk1 as [H' H'']. apply Hφ1 in Hk2.
          apply Hφ0 in Hk'. rewrite lookup_total_alt.
          rewrite Hk2 Hk'; by simpl. try done.
          try done. try done. }

        assert (dom (gset K) Sb_map = Sb) as Domm_Sbmap.
        { subst Sb_map. by rewrite map_restriction_dom. }

        iAssert (⌜∀ k, Bn !!! k ≤ Bn0' !!! k⌝)%I as "%".
        { iPureIntro. intros k.
          destruct (decide (k ∈ Sb)).
          - rewrite HSb; try done. lia. 
          - subst Bn0'. rewrite !lookup_total_alt. 
            rewrite gmap_lookup_insert_map_ne. done.
            by rewrite Domm_Sbmap.  }
        rename H into Bn_le_Bn0'.

        iPoseProof((maxnat_set_update γ_cirn KS Bn Bn0') 
                        with "[] [$HnS_star]") as ">HnS_star".
        { iPureIntro; intros k Hk; apply Bn_le_Bn0'. }

        assert (domm Rm0' = {[m]}) as Domm_Rm0'.
        { pose proof (flowint_inflow_insert_set_dom Rm0 m Sr Rm0') as H'.
          subst Rm0'. rewrite H'. clear -Domm_Rm0; set_solver.
          done. }
          
        assert (domm Im0' = {[m]}) as Domm_Im0'.
        { pose proof (flowint_inflow_insert_set_dom Im0 m Sr_mset Im0') as H'.
          subst Im0'. rewrite H'. clear -Domm_Im0; set_solver.
          done. }         


        iAssert (own γ_R (◯ Rn0') ∗ own γ_R (◯ Rm0'))%I 
                with "[HRn HRm]" as "(HRn & HRm)".
        { iCombine "HRn HRm" as "HRnm".
          assert (Rn0' = outflow_insert_set Rn0 m Sr) 
                  as HRn0'. done.
          assert (Rm0' = inflow_insert_set Rm0 m Sr)
                  as HRm0'. done. 
          iPoseProof (own_valid with "[$HRnm]") as "%".
          rename H into Valid_Rnm. 
          rewrite auth_frag_valid in Valid_Rnm*; intros Valid_Rnm.
          assert (m ∈ domm Rm0) by (clear -Domm_Rm0; set_solver).
          assert (domm Rn0 ≠ ∅) by (clear -Domm_Rn0; set_solver).
          pose proof (flowint_insert_eq Rn0 Rn0' Rm0 Rm0' 
                  m Sr H H1 HRn0' HRm0' Valid_Rnm) as HRnm0'.
          iEval (rewrite HRnm0') in "HRnm".
          iEval (rewrite auth_frag_op) in "HRnm".
          iDestruct "HRnm" as "(?&?)". iFrame. }

        iAssert (own γ_I (◯ In0') ∗ own γ_I (◯ Im0'))%I 
                with "[HIn HIm]" as "(HIn & HIm)".
        { iCombine "HIn HIm" as "HInm".
          assert (In0' = outflow_insert_set In0 m Sr_mset) 
                  as HIn0'. done.
          assert (Im0' = inflow_insert_set Im0 m Sr_mset)
                  as HIm0'. done.         
          iPoseProof (own_valid with "[$HInm]") as "%".
          rename H into Valid_Inm. 
          rewrite auth_frag_valid in Valid_Inm*; intros Valid_Inm.
          assert (m ∈ domm Im0) by (clear -Domm_Im0; set_solver).
          assert (domm In0 ≠ ∅) by (clear -Domm_In0; set_solver).
          pose proof (flowint_insert_eq In0 In0' Im0 Im0' 
                  m Sr_mset H H1 HIn0' HIm0' Valid_Inm) as HInm0'.
          iEval (rewrite HInm0') in "HInm".
          iEval (rewrite auth_frag_op) in "HInm".
          iDestruct "HInm" as "(?&?)". iFrame. }




        
        assert (dom (gset K) Sr_map = Sr) as Domm_Srmap.
        { subst Sr_map. by rewrite map_restriction_dom. }


        assert (∀ k, k ∈ Sr → Qn0' !! k = Some 0) as Lookup_Qn0'.
        { intros k Hk. subst Qn0'. rewrite gmap_lookup_insert_map.
          subst Sr_map. rewrite lookup_map_restriction; try done.
          by rewrite Domm_Srmap. }

        assert (∀ k, k ∉ Sr → Qn0' !! k = Qn !! k) as Lookup_Qn0'_ne.
        { intros k Hk. subst Qn0'. 
          rewrite gmap_lookup_insert_map_ne; try done.
          by rewrite Domm_Srmap. }

        assert (∀ k, k ∈ Sb → Bn0' !! k = Some 0) as Lookup_Bn0'.
        { intros k Hk. subst Bn0'. rewrite gmap_lookup_insert_map.
          subst Sb_map. rewrite lookup_map_restriction; try done.
          by rewrite Domm_Sbmap. }

        assert (∀ k, k ∉ Sb → Bn0' !! k = Bn !! k) as Lookup_Bn0'_ne.
        { intros k Hk. subst Bn0'. 
          rewrite gmap_lookup_insert_map_ne; try done.
          by rewrite Domm_Sbmap. }
        
        assert (∀ k t, (k, t) ∈ Sr_mset ↔ k ∈ Sr ∧ t = 0) as HSr_mset.
        { intros k t. subst Sr_mset. apply map_subset_member. }      

        
        iDestruct "HnS_oc" as "(%&%&%)".
        rename H into OC1. rename H1 into OC2. rename H2 into OC3.

        iAssert (outflow_constraints n In0' Rn0' esn' Qn0')%I as "HnS_oc".
        { iPureIntro. split; last split; try done.
          - intros n' k t HKS. destruct (decide (n' = m)).
            + subst n'. assert (outset KT In0' m = Sr_mset) as Hout.
              { assert (outset KT In0 m = ∅).
                { unfold outset. rewrite Out_In_m. 
                  unfold ccmunit, ccm_unit. unfold lift_unit.
                  unfold nzmap_unit, dom_ms, dom, nzmap_dom.
                  simpl. apply leibniz_equiv. by rewrite dom_empty. }
                assert (In0' = outflow_insert_set In0 m Sr_mset) as H' by done.  
                pose proof (outflow_insert_set_outset In0 m Sr_mset In0' H').
                rewrite H in H1. clear -H1; set_solver. }
              rewrite Hout. split.
              * intros H'. apply HSr_mset in H'. 
                destruct H' as [H1' H2'].
                split. subst Sr. clear -H1'. set_solver.
                rewrite (Lookup_Qn0' k H1').
                by rewrite H2'.
              * intros [Hkt1 Hkt2].
                destruct (decide (k ∈ Sr)).
                ** rewrite (Lookup_Qn0' k e) in Hkt2.
                   inversion Hkt2. rewrite HSr_mset.
                   split; try done. 
                ** assert (∀ n', k ∉ esn !!! n') as Hnot.
                   { intros n'. destruct (decide (n' = m)).
                     subst n'. rewrite Esn_empty. clear; set_solver.
                     destruct (decide (k ∈ esn !!! n')); try done.
                     assert (k ∈ esn' !!! n') as H'. rewrite Hesn'. 
                     rewrite lookup_total_insert_ne; try done.
                     pose proof Disj_esn' n' m n1 as Disj_esn'.
                     clear -Disj_esn' Hkt1 H'. set_solver. }
                   rewrite (Lookup_Qn0'_ne k n0) in Hkt2.   
                   pose proof Hφ0 k HKS Hnot as H'. rewrite H' in Hkt2.
                   done.
            + rewrite Hesn'. rewrite lookup_total_insert_ne; try done.
              assert (outset KT In0' n' = outset KT In0 n') as Hout.
              { assert (In0' = outflow_insert_set In0 m Sr_mset) as H' by done.  
                by pose proof (outflow_insert_set_outset_ne In0 m 
                                                Sr_mset In0' n' n0 H'). }
                rewrite Hout. split.
              * destruct (decide (k ∈ Sr)).
                ** intros H'. apply OC1 in H'.
                   destruct H' as [H' _].
                   pose proof Esn_not k e n' as H''.
                   clear -H' H''. set_solver. done.
                ** rewrite (Lookup_Qn0'_ne k n1). apply OC1. done.   
              * intros [Hkt1 Hkt2]. destruct (decide (k ∈ Sr)).
                ** pose proof Esn_not k e n' as H''.
                   clear -Hkt1 H''. set_solver.
                ** rewrite (Lookup_Qn0'_ne k n1) in Hkt2.
                   apply OC1; try done.   
          - intros n' k HKS. assert (inset K Rn0' n = inset K Rn0 n) as Hin.
            { try done. } rewrite Hin. destruct (decide (n' = m)).
            + subst n'. assert (outset K Rn0' m = Sr) as Hout.
              { assert (outset K Rn0 m = ∅).
                { unfold outset. rewrite Out_Rn_m. 
                  unfold ccmunit, ccm_unit. unfold lift_unit.
                  unfold nzmap_unit. unfold dom_ms, dom, nzmap_dom.
                  simpl. apply leibniz_equiv. by rewrite dom_empty. }  
                assert (Rn0' = outflow_insert_set Rn0 m Sr) as H' by done.  
                pose proof (outflow_insert_set_outset Rn0 m Sr Rn0' H').
                rewrite H in H1. clear -H1; set_solver. } rewrite Hout. 
              subst Sr.  rewrite !elem_of_intersection.
              split; try done. intros [H' [H'' H''']]; split; try done.
            + assert (outset K Rn0' n' = outset K Rn0 n') as Hout.
              { assert (Rn0' = outflow_insert_set Rn0 m Sr) as H' by done.  
                by pose proof (outflow_insert_set_outset_ne Rn0 m Sr 
                          Rn0' n' n0 H'). } rewrite Hout. rewrite Hesn'. 
              rewrite lookup_total_insert_ne; try done.
              by pose proof OC2 n' k HKS.
          - intros n' kt. destruct (decide (n' = m)).
            + subst n'. subst In0'.
              destruct (decide (kt ∈ Sr_mset)).
              * unfold out, out_map. unfold outflow_insert_set.
                unfold outflow_map_set. simpl.
                rewrite nzmap_lookup_total_insert.
                rewrite nzmap_lookup_total_map_set.
                rewrite Out_In_m. unfold ccmunit, ccm_unit.
                simpl. unfold lift_unit. rewrite nzmap_lookup_empty.
                unfold ccmunit, ccm_unit. simpl. lia. done.
              * unfold out, out_map. unfold outflow_insert_set.
                unfold outflow_map_set. simpl.
                rewrite nzmap_lookup_total_insert.
                rewrite nzmap_lookup_total_map_set_ne.
                rewrite Out_In_m. unfold ccmunit, ccm_unit.
                simpl. unfold lift_unit. rewrite nzmap_lookup_empty.
                unfold ccmunit, ccm_unit. simpl. unfold nat_unit. lia. done.
            + subst In0'. unfold outflow_insert_set.
              unfold out at 1, out_map at 1; simpl.
              rewrite nzmap_lookup_total_insert_ne; try done.
              pose proof OC3 n' kt as H'. by unfold out in H'.  }
       
        iAssert (outflow_constraints m Im0' Rm0' esm0 Qm0)%I as "HnS_ocm".
        { iPureIntro. split; last split.
          - intros n' k t HKS. split.
            + unfold outset, dom_ms. 
              rewrite nzmap_elem_of_dom_total. unfold out, out_map. 
              subst Im0. simpl. rewrite nzmap_lookup_empty. 
              unfold ccmunit, ccm_unit. simpl.
              unfold lift_unit.
              rewrite nzmap_lookup_empty.
              unfold ccmunit, ccm_unit. simpl. done.
            + subst esm0. rewrite /(∅ !!! n'). 
              unfold finmap_lookup_total. rewrite lookup_empty.
              simpl. clear; set_solver.
          - unfold outflow_constraint_R. 
            intros n' k. unfold outset.
            assert (out Rm0' n' = out Rm0 n') as Hout.
            { assert (Rm0' = inflow_insert_set Rm0 m Sr) as H' by done.  
              by pose proof (inflow_insert_set_out_eq Rm0 m Sr Rm0' n' H'). }
            rewrite Hout. split.
            + unfold in_outset, dom_ms. 
              rewrite nzmap_elem_of_dom_total. unfold out, out_map. 
              subst Rm0. simpl. rewrite nzmap_lookup_empty. 
              unfold ccmunit, ccm_unit. simpl.
              unfold lift_unit.
              rewrite nzmap_lookup_empty.
              unfold ccmunit, ccm_unit. simpl. done.
            + subst esm0. rewrite /(∅ !!! n'). 
              unfold finmap_lookup_total. rewrite lookup_empty.
              simpl. clear; set_solver.
          - intros n' kt. unfold out, out_map; subst Im0; simpl.
            rewrite nzmap_lookup_empty. unfold ccmunit, ccm_unit.
            simpl. unfold lift_unit. rewrite nzmap_lookup_empty.
            unfold ccmunit, ccm_unit; simpl. unfold nat_unit. lia. }

        iAssert (⌜φ0 esn' Qn0'⌝ ∗ ⌜φ1 Bn0' Cn Qn0'⌝ ∗ ⌜φ2 n Bn0' In0'⌝ 
           ∗ ⌜φ3 n Bn0' Rn0'⌝ ∗ ⌜φ4 n Rn0'⌝ ∗ ⌜φ5 Bn0' Qn0'⌝ 
           ∗ ⌜φ6 Bn0' T0'⌝ ∗ ⌜φ7 n esn' Rn0' Qn0'⌝ ∗ ⌜φ8 n In0'⌝)%I 
                with "[Hφ]" as "Hφ".
        { iDestruct "Hφ" as "(%&%&%&%&%&%&%&%&%)".         
          clear H. rename H1 into Hφ1. 
          rename H2 into Hφ2. rename H3 into Hφ3.
          rename H4 into Hφ4. rename H5 into Hφ5.
          rename H6 into Hφ6. rename H7 into Hφ7.
          rename H8 into Hφ8.
          iPureIntro. split; last split; last split; 
          last split; last split; last split; last split; last split.
          - intros k HKS Hnot. destruct (decide (k ∈ Sr)). 
            + subst Sr. rewrite !elem_of_intersection in e*; intros e. 
              destruct e as [_ [e _]]. pose proof Hnot m as Hnot. 
              clear -Hnot e. set_solver.  
            + rewrite (Lookup_Qn0'_ne k n0). apply Hφ0. done. 
              intros n'. destruct (decide (n' = m)).
              * subst n'. rewrite Esn_empty.
                clear; set_solver.
              * pose proof Hnot n' as Hnot.
                rewrite Hesn' in Hnot.
                rewrite lookup_total_insert_ne in Hnot; try done.
          - intros k t HKS. destruct (decide (k ∈ Sr)).
            + split.
              * intros HCn.
                assert (is_Some(Cn !! k)). by exists t; try done.
                rewrite <-elem_of_dom in H.
                assert (k ∉ Sb) as Hk.
                { destruct (decide (k ∈ Sb)); try done.
                  subst Sb. rewrite elem_of_intersection in e0*; intros e0.
                  destruct e0 as [_ e0].
                  clear -e0 H. set_solver. }
                rewrite (Lookup_Bn0'_ne k Hk).
                by apply Hφ1.
              * intros HCn. rewrite <-not_elem_of_dom in HCn.
                assert (k ∈ Sb) as Hk.
                { subst Sb. clear -e HCn HKS. set_solver. }
                rewrite (Lookup_Bn0' k Hk).
                rewrite (Lookup_Qn0' k e).
                done.
            + assert (k ∉ Sb) as Hk.
              { destruct (decide (k ∈ Sb)); try done.
                subst Sb. rewrite elem_of_intersection in e*; intros e.
                destruct e as [_ e]. clear -e n0. set_solver. }
              rewrite (Lookup_Bn0'_ne k Hk).
              rewrite (Lookup_Qn0'_ne k n0).
              apply Hφ1. done.
          - intros k t HKS. assert (inset KT In0' n = inset KT In0 n) as Hin. 
            { assert (In0' = outflow_insert_set In0 m Sr_mset) by done.
              by pose proof (outflow_insert_set_inset In0 m Sr_mset In0' n H). }
            rewrite Hin. destruct (decide (k ∈ Sb)). 
            + intros H'. apply Hφ2 in H'. rewrite lookup_total_alt.
              rewrite (Lookup_Bn0' k e). simpl.
              by rewrite (HSb k e) in H'. done.
            + rewrite lookup_total_alt. rewrite (Lookup_Bn0'_ne k n0).
              rewrite <-lookup_total_alt. apply Hφ2. done.
          - intros k HKS. assert (inset K Rn0' n = inset K Rn0 n) as Hin.
            { assert (Rn0' = outflow_insert_set Rn0 m Sr) by done.
              by pose proof (outflow_insert_set_inset Rn0 m Sr Rn0' n H). }
            rewrite Hin.
            destruct (decide (k ∈ Sb)).
            + right. subst Sb. subst Sr. clear -e. set_solver.
            + rewrite (Lookup_Bn0'_ne k n0).
              by pose proof Hφ3 k HKS.
          - try done.
          - intros k. destruct (decide (k ∈ Sb)).
            + destruct (decide (k ∈ Sr)).
              * rewrite !lookup_total_alt. 
                rewrite (Lookup_Bn0' k e).
                rewrite (Lookup_Qn0' k e0).
                by simpl.
              * subst Sb Sr; clear -e n0; set_solver.
            + destruct (decide (k ∈ Sr)).
              * rewrite lookup_total_alt.
                rewrite (Lookup_Qn0' k e).
                simpl. lia.
              * rewrite !lookup_total_alt. 
                rewrite (Lookup_Bn0'_ne k n0).
                rewrite (Lookup_Qn0'_ne k n1).
                rewrite <-!lookup_total_alt.
                by apply Hφ5.
          - intros k HKS. rewrite lookup_total_alt. 
            destruct (decide (k ∈ Sb)).
            * rewrite (Lookup_Bn0' k e). simpl. lia.
            * rewrite (Lookup_Bn0'_ne k n0).
              rewrite <-lookup_total_alt.
              by pose proof Hφ6 k HKS.
          - intros k HKS. intros [H' H''].
            destruct H' as [n' H'].
            destruct (decide (n' = m)).
            + subst n'. rewrite elem_of_dom. 
              assert (k ∈ Sr).
              { subst Sr. rewrite !elem_of_intersection.
                split; try done. }
              rewrite (Lookup_Qn0' k H).
              by exists 0.
            + assert (inset K Rn0' n = inset K Rn0 n) as Hin.
              { assert (Rn0' = outflow_insert_set Rn0 m Sr). done. 
                by pose proof (outflow_insert_set_inset Rn0 m Sr Rn0' n' H). } 
              rewrite Hesn' in H'.
              rewrite lookup_total_insert_ne in H'; try done.
              destruct (decide (k ∈ Sr)).
              * pose proof Lookup_Qn0' k e as H'''.
                rewrite elem_of_dom. rewrite H'''.
                by exists 0.
              * rewrite elem_of_dom. rewrite (Lookup_Qn0'_ne k n1).
                rewrite <-elem_of_dom. apply Hφ7. done.
                split; try done. by exists n'.
          - try done. }
      
        iAssert (⌜φ0 esm0 Qm0⌝ ∗ ⌜φ1 Bm0 Cm0 Qm0⌝ ∗ ⌜φ2 m Bm0 Im0'⌝ 
              ∗ ⌜φ3 m Bm0 Rm0'⌝ ∗ ⌜φ4 m Rm0'⌝ ∗ ⌜φ5 Bm0 Qm0⌝  
              ∗ ⌜φ6 Bm0 T0'⌝ ∗ ⌜φ7 m esm0 Rm0' Qm0⌝ ∗ ⌜φ8 m Im0'⌝)%I
                 as "Hφm".
        { iPureIntro. subst esm0 Cm0 Bm0 Qm0.
          repeat split; try done.
          - unfold φ2.
            assert (inset KT Im0' m = Sr_mset) as Hin.
            { assert (inset KT Im0 m = ∅) as Hin.
              subst Im0. unfold inset, dom_ms, inf; simpl.
              rewrite lookup_insert. simpl.
              unfold dom, nzmap_dom. apply leibniz_equiv.
              by rewrite dom_empty.
              assert (Im0' = inflow_insert_set Im0 m Sr_mset). done.
              pose proof (inflow_insert_set_inset Im0 m Sr_mset Im0' H).
              rewrite H1; rewrite Hin; clear; set_solver. } 
            rewrite Hin. intros k t HKS Hkt.
            apply HSr_mset in Hkt.
            destruct Hkt as [_ H'].
            rewrite lookup_total_alt; rewrite lookup_empty; by simpl.
          - unfold φ3. intros k HKS; left.
            rewrite /(∅ !!! k). unfold finmap_lookup_total.
            rewrite lookup_empty. by simpl.
          - unfold φ4. intros k.
            subst Rm0; unfold inf, inf_map; simpl.
            rewrite lookup_insert. simpl.
            unfold inf, inf_map; simpl.
            rewrite lookup_insert. simpl.
            destruct (decide (k ∈ Sr)). 
            + rewrite nzmap_lookup_total_map_set.
              rewrite nzmap_lookup_empty. 
              unfold ccmunit, ccm_unit; simpl.
              lia. done.
            + rewrite nzmap_lookup_total_map_set_ne.
              rewrite nzmap_lookup_empty. 
              unfold ccmunit, ccm_unit; simpl.
              unfold nat_unit.
              lia. done.
          - intros k HKS. rewrite /(∅ !!! k).
            unfold finmap_lookup_total.
            rewrite lookup_empty. by simpl.  
          - unfold φ6. intros k HKS. rewrite /(∅ !!! k). 
            unfold finmap_lookup_total. rewrite lookup_empty.
            simpl. lia.
          - intros k HKS [Hkt1 Hkt2].
            destruct Hkt1 as [n' H'].
            clear -H'. set_solver.
          - intros kt. subst Im0'. unfold inflow_insert_set, inflow_map_set.
            unfold inf; simpl. rewrite !lookup_insert. simpl.
            destruct (decide (kt ∈ Sr_mset)).
            + rewrite nzmap_lookup_total_map_set; try done.
              rewrite HIm0. unfold inf_map; simpl.
              rewrite lookup_insert. simpl.
              rewrite nzmap_lookup_empty.
              unfold ccmunit, ccm_unit; simpl; lia.
            + rewrite nzmap_lookup_total_map_set_ne; try done.
              rewrite HIm0. unfold inf_map; simpl.
              rewrite lookup_insert. simpl.
              rewrite nzmap_lookup_empty.
              unfold ccmunit, ccm_unit; simpl. unfold nat_unit; lia. }

                    
    iModIntro. iExists Bn0', Qn0'.
    iSplitL "node_n HnP_gh HnP_C HnP_frac HnP_t". { iFrame. }
    iSplitL "HnS_gh HnS_FP HnS_H HnS_frac HnS_cl HnS_star HRn HIn Hφ".
    { iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn', In0', Rn0'.
      iFrame. iFrame "HnS_oc". iSplitR. by iPureIntro.
      destruct (decide (n = r)); try done.
      - subst n. iDestruct "HnS_H" as "(%&%)".
              rename H into Bn_eq_H0. rename H1 into Infz_In0. 
              iPureIntro. repeat split; try done.
              apply map_eq. intros k.
              destruct (decide (k ∈ Sb)).
              + rewrite (Lookup_Bn0' k e).
                rewrite map_eq_iff in Bn_eq_H0*; intros Bn_eq_H0.
                pose proof Bn_eq_H0 k as H'. 
                pose proof (HSb k e) as H''.
                subst Sb. rewrite elem_of_intersection in e*; intros e.
                destruct e as [e _].                
                pose proof Hist k e as Hist.
                pose proof (map_of_set_lookup_some H0 k 0 Hist) as Hm.
                destruct Hm as [u Hm]. rewrite Hm.
                rewrite lookup_total_alt in H''.
                rewrite H' in H''. rewrite Hm in H''. 
                simpl in H''. by rewrite H''.
              + subst Bn0'. rewrite gmap_lookup_insert_map_ne.
                rewrite map_eq_iff in Bn_eq_H0*; intros Bn_eq_H0.
                by pose proof Bn_eq_H0 k as H'.
                by rewrite Domm_Sbmap. }
    iSplitL "node_m HnP_auxm". { iFrame. }
    iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm0, Im0', Rm0'.
    iFrame "∗#". iSplitR. by iPureIntro.
    destruct (decide (m = r)); try done.               
  Qed.          

  
  Lemma mergeContents_ghost_update γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh 
              lc r T' H hγ I R
              n Cn Bn0' Qn0' γ_en γ_cn γ_bn γ_qn γ_cirn esn' T Cn'
              m Cm Bm Qm γ_em γ_cm γ_bm γ_qm γ_cirm esm Tm Cm' :

          ⌜m ≠ r⌝
        ∗ ⌜set_of_map Cn' ⊆ set_of_map Cn⌝
        ∗ ⌜set_of_map Cm' ⊆ set_of_map Cn ∪ set_of_map Cm⌝
        ∗ ⌜set_of_map Cn ∩ set_of_map Cm' ## set_of_map Cn'⌝
        ∗ ⌜dom (gset K) Cm ⊆ dom (gset K) Cm'⌝
        ∗ ⌜merge Cn (esn' !!! m) Cm = merge Cn' (esn' !!! m) Cm'⌝ 
        -∗
          node r n esn' Cn' ∗ nodePred_aux γ_gh γ_t γ_s lc r n Cn Bn0' Qn0' 
                                          γ_en γ_cn γ_bn γ_qn γ_cirn esn' T
        ∗ node r m esm Cm' ∗ nodePred_aux γ_gh γ_t γ_s lc r m Cm Bm Qm 
                                          γ_em γ_cm γ_bm γ_qm γ_cirm esm Tm
        ∗ nodeShared γ_I γ_R γ_f γ_gh r n Cn Bn0' Qn0' H T'
        ∗ nodeShared γ_I γ_R γ_f γ_gh r m Cm Bm Qm H T'
        ∗ global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r T' H hγ I R
        ==∗
          ∃ Qn' Bm', nodePred γ_gh γ_t γ_s lc r n Cn' Bn0' Qn'
        ∗ nodeShared γ_I γ_R γ_f γ_gh r n Cn' Bn0' Qn' H T' 
        ∗ nodePred γ_gh γ_t γ_s lc r m Cm' Bm' Qm
        ∗ nodeShared γ_I γ_R γ_f γ_gh r m Cm' Bm' Qm H T'
        ∗ global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r T' H hγ I R.
  Proof.
    iIntros "(%&%&%&%&%&%)". rename H0 into m_neq_r. 
    rename H1 into Subset_Cn. rename H2 into Subset_Cm.
    rename H3 into Subset_disj. rename H4 into Cm_sub_Cm'.
    rename H5 into MergeEq.
    

    iIntros "(node_n & HnP_aux & node_m & HnP_auxm & HnS_n & HnS_m & Hglob)".
    iDestruct "HnP_aux" as "(HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iDestruct "HnP_auxm" as "(HnP_ghm & HnP_fracm & HnP_Cm & HnP_tm)".
    iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                  "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                            & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
    iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                              as "(% & % & % & % & %)".
    subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
    iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
    destruct H0 as [Hes _]. subst es'.
    iDestruct "HnS_m" as (γ_em' γ_cm' γ_bm' γ_qm' γ_cirm' es' Im Rm) 
                  "(HnS_ghm & HnS_fracm & HnS_sim & HnS_FPm 
                            & HnS_clm & HnS_ocm & HnS_Hm & HnS_starm & Hφm)".
    iPoseProof (ghost_heap_sync with "[$HnP_ghm] [$HnS_ghm]") 
                              as "(% & % & % & % & %)".
    subst γ_em'. subst γ_cm'. subst γ_bm'. subst γ_qm'. subst γ_cirm'.
    iPoseProof (frac_eq with "[$HnP_fracm] [$HnS_fracm]") as "%".
    destruct H0 as [Hes _]. subst es'.

    set (S := KS ∩ (dom (gset K) Cn ∖ dom (gset K) Cn')).
    set (S_map := map_restriction S Cn).
    set (Qn_old := map_subset S Qn0').
    set (Qn_new := map_subset S Cn).
    set (Qn' := gmap_insert_map Qn0' S_map).
    set (Bm' := gmap_insert_map Bm S_map).
    set (In_temp := outflow_delete_set In m Qn_old).
    set (In' := outflow_insert_set In_temp m Qn_new).
    set (Im_temp := inflow_delete_set Im m Qn_old).
    set (Im' := inflow_insert_set Im_temp m Qn_new).

    iPoseProof ((node_edgeset_disjoint r n) with "[$node_n]") as "%".
    rename H0 into Disj_esn'.                        

    iMod ((frac_update γ_en γ_cn γ_bn γ_qn esn' Cn Bn0' Qn0' esn' Cn' Bn0' Qn') 
         with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".

    iMod ((frac_update γ_em γ_cm γ_bm γ_qm esm Cm Bm Qm esm Cm' Bm' Qm) 
         with "[$HnP_fracm $HnS_fracm]") as "(HnP_fracm & HnS_fracm)".

        assert (S ⊆ esn' !!! m) as S_sub_es.
        { intros k Hk. destruct (decide (k ∈ esn' !!! m)); try done.
          rewrite map_eq_iff in MergeEq *; intros MergeEq.
          pose proof MergeEq k as MergeEq.
          unfold merge in MergeEq.
          rewrite !gmap_imerge_prf in MergeEq.
          unfold f_merge in MergeEq.
          destruct (decide (Cn !! k ≠ None)) eqn: Hd. 
          - destruct (decide (Cn' !! k ≠ None)) eqn: Hd'. 
            + pose proof dom_lookup Cn k n1 as H'.
              pose proof dom_lookup Cn' k n2 as H''.
              clear -H' H'' S Hk. set_solver.
            + destruct (decide (k ∈ esn' !!! m)); try done.
          - destruct (decide (k ∈ esn' !!! m)); try done.
            clear Hd. apply dec_stable in n1. 
            apply not_elem_of_dom in n1. 
            clear -n1 S Hk. set_solver. }


        assert (∀ k t, (k,t) ∈ Qn_new ↔ k ∈ S ∧ t = Cn !!! k) as HQn_new.
        { intros k t. subst Qn_new. apply map_subset_member. } 
        assert (∀ k t, (k,t) ∈ Qn_old ↔ k ∈ S ∧ t = Qn0' !!! k) as HQn_old.
        { intros k t. subst Qn_old. apply map_subset_member. } 
        assert (dom (gset K) S_map = S) as Dom_Smap.
        { subst S_map. apply map_restriction_dom. }

        assert (∀ k, k ∈ S → S_map !! k = Some(Cn !!! k)) as Lookup_Smap.
        { intros k Hk. subst S_map. by rewrite lookup_map_restriction. }
        assert (∀ k, k ∈ S → Qn' !! k = Cn !! k) as Lookup_Qn'.
        { intros k Hk. subst Qn'. rewrite gmap_lookup_insert_map.
          rewrite (Lookup_Smap k Hk).
          assert (k ∈ dom (gset K) Cn) as H'.
          { subst S. clear -Hk; set_solver. }
          rewrite elem_of_dom in H'*; intros H'. destruct H' as [t H'].
          rewrite lookup_total_alt. rewrite H'; by simpl.
          by rewrite Dom_Smap. }
        assert (∀ k, k ∉ S → Qn' !! k = Qn0' !! k) as Lookup_Qn'_ne.
        { intros k Hk. subst Qn'. rewrite gmap_lookup_insert_map_ne.
          done. by rewrite Dom_Smap. }
        assert (∀ k t, k ∉ S → (k,t) ∉ Qn_old) as HQn_old_ne.
        { intros k t Hk. destruct (decide ((k,t) ∈ Qn_old)); try done. 
          rewrite HQn_old in e*; intros e. destruct e as [e _].
          clear -e Hk; set_solver. }
        assert (∀ k t, k ∉ S → (k,t) ∉ Qn_new) as HQn_new_ne.
        { intros k t Hk. destruct (decide ((k,t) ∈ Qn_new)); try done. 
          rewrite HQn_new in e*; intros e. destruct e as [e _].
          clear -e Hk; set_solver. }
        
        assert (∀ k, k ∈ S → Cn !! k = Cm' !! k) as Lookup_merge.
        { intros k Hk. assert (Hes := Hk).
          apply S_sub_es in Hes. subst S.
          rewrite elem_of_intersection in Hk*; intros Hk.
          destruct Hk as [HKS Hk].
          rewrite elem_of_difference in Hk*; intros Hk.
          destruct Hk as [H' H''].
          rewrite elem_of_dom in H'*; intros H'.
          rewrite not_elem_of_dom in H''*; intros H''.
          destruct H' as [t H'].
          rewrite map_eq_iff in MergeEq*; intros MergeEq.
          pose proof MergeEq k as Hm.
          unfold merge in Hm. rewrite !gmap_imerge_prf in Hm.
          unfold f_merge in Hm. rewrite decide_True in Hm.
          rewrite decide_False in Hm. rewrite decide_True in Hm.
          done. done. rewrite H''. intros ?; contradiction.
          rewrite H'; try done. }
        
        iAssert (⌜∀ k, k ∈ S → k ∈ inset K Rn n⌝)%I as %S_sub_insetn.
        { iDestruct "Hφ" as "(_&%&_&%&_)".
          rename H0 into Hφ1. rename H1 into Hφ3. iPureIntro.
          intros k Hk. subst S. 
          rewrite elem_of_intersection in Hk*; intros Hk.
          destruct Hk as [HKS Hk].
          rewrite elem_of_difference in Hk*; intros Hk.
          destruct Hk as [Hk _].
          pose proof Hφ3 k as Hφ3.
          destruct Hφ3 as [H' | H']; try done.
          rewrite elem_of_dom in Hk*; intros Hk.
          destruct Hk as [t Hk]. apply Hφ1 in Hk.
          rewrite H' in Hk. done. done. }

        iAssert(⌜S ⊆ KS⌝)%I as %S_sub_KS.
        { iPureIntro. subst S. clear; set_solver. }

        iAssert (⌜∀ k, k ∈ S → k ∈ outset K Rn m⌝)%I as %Out_Rn_m.
        { iDestruct "HnS_oc" as "(_&%&_)". rename H0 into OC2.
          iPureIntro; intros k Hk. apply OC2.
          by apply S_sub_KS in Hk.
         
          split; try done. by apply S_sub_es.
          by apply S_sub_insetn. }
        
        iAssert (⌜∀ k, k ∈ S → k ∈ inset K Rm m⌝)%I as %S_sub_insetm.
        { iDestruct "HnS_si" as "(_&HRn&_&Domm_Rn)".
          iDestruct "HnS_sim" as "(_&HRm&_&Domm_Rm)".
          iCombine "HRn HRm" as "HRnm".
          iPoseProof (own_valid with "[$HRnm]") as "%".
          rename H0 into Valid_Rnm. 
          rewrite auth_frag_valid in Valid_Rnm*; intros Valid_Rnm.
          iDestruct "Domm_Rn" as %Domm_Rn.
          iDestruct "Domm_Rm" as %Domm_Rm. 
          assert (m ∈ domm Rm) as m_in_Rm. 
          clear -Domm_Rm; set_solver. 
          pose proof intComp_unfold_inf_2 Rn Rm Valid_Rnm m m_in_Rm as H'. 
          unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op in H'.
          iPureIntro. rewrite nzmap_eq in H' *; intros H'.
          intros k Hk. pose proof H' k as H'.
          unfold inset. rewrite nzmap_elem_of_dom_total.
          unfold ccmunit, ccm_unit. simpl.
          unfold nat_unit.
          rewrite nzmap_lookup_merge in H'.
          unfold ccmop, ccm_op in H'. simpl in H'.
          unfold nat_op in H'.
          assert (1 ≤ out Rn m !1 k) as Hout.
          { pose proof Out_Rn_m k Hk as H''.
            unfold outset in H''.
            rewrite nzmap_elem_of_dom_total in H'' *; 
            intros H''.
            unfold ccmunit, ccm_unit in H''.
            simpl in H''. unfold nat_unit in H''.
            clear - H''. lia. }
          assert (1 ≤ inf Rm m !1 k) as Hin.
          { clear -H' Hout. 
            assert (∀ (x y z: nat), 1 ≤ y → x = z + y → 1 ≤ x) as H''.
            lia. by pose proof H'' _ _ _ Hout H'. }
          clear -Hin. lia. }

        iAssert (⌜∀ k, k ∈ S → (k, Qn0' !!! k) ∈ outset KT In m⌝)%I 
                                                as %Out_In_m.
        { iDestruct "HnS_oc" as "(%&_)". 
          iDestruct "Hφ" as "(_&_&_&_&_&_&_&%&_)". 
          rename H0 into OC1. rename H1 into Hφ7.
          iPureIntro; intros k Hk. apply OC1.
          by apply S_sub_KS in Hk.
          split; try done. by apply S_sub_es.
          pose proof Hφ7 k as H'.
          assert (k ∈ dom (gset K) Qn0') as H''.
          apply H'. by apply S_sub_KS in Hk. split.
          exists m; by apply S_sub_es in Hk.
          by apply S_sub_insetn. 
          rewrite elem_of_dom in H''*; intros H''.
          destruct H'' as [t H''].
          rewrite lookup_total_alt; rewrite H''; by simpl. }


        iAssert (⌜∀ k, k ∈ S → (k, Qn0' !!! k) ∈ inset KT Im m⌝)%I as %Ins_Im.
        { iDestruct "HnS_si" as "(HIn&_&Domm_In&_)".
          iDestruct "HnS_sim" as "(HIm&_&Domm_Im&_)".
          iCombine "HIn HIm" as "HInm".
          iPoseProof (own_valid with "[$HInm]") as "%".
          rename H0 into Valid_Inm. 
          rewrite auth_frag_valid in Valid_Inm*; intros Valid_Inm.
          iDestruct "Domm_In" as %Domm_In.
          iDestruct "Domm_Im" as %Domm_Im. 
          assert (m ∈ domm Im) as m_in_Im. 
          clear -Domm_Im; set_solver. 
          pose proof intComp_unfold_inf_2 In Im Valid_Inm m m_in_Im as H'. 
          unfold ccmop, ccm_op in H'. simpl in H'. unfold lift_op in H'.
          iPureIntro. rewrite nzmap_eq in H' *; intros H'.
          intros k Hk. pose proof H' (k, Qn0' !!! k) as H'.
          unfold inset. rewrite nzmap_elem_of_dom_total.
          unfold ccmunit, ccm_unit. simpl.
          unfold nat_unit.
          rewrite nzmap_lookup_merge in H'.
          unfold ccmop, ccm_op in H'. simpl in H'.
          unfold nat_op in H'.
          assert (1 ≤ out In m !1 (k, Qn0' !!! k)) as Hout.
          { pose proof Out_In_m k Hk as H''.
            unfold outset in H''.
            rewrite nzmap_elem_of_dom_total in H'' *; 
            intros H''.
            unfold ccmunit, ccm_unit in H''.
            simpl in H''. unfold nat_unit in H''.
            clear - H''. lia. }
          assert (1 ≤ inf Im m !1 (k, Qn0' !!! k)) as Hin.
              { clear -H' Hout. 
                assert (∀ (x y z: nat), 1 ≤ y → x = z + y → 1 ≤ x) as H''.
                lia. by pose proof H'' _ _ _ Hout H'. }
              clear -Hin. lia. }

        iAssert (⌜∀ k, k ∈ S → Bm !!! k = Qn0' !!! k⌝)%I as %Bm_eq_Qn.
        { iDestruct "Hφm" as "(_&_&%&_)".
          rename H0 into Hφ2.
          iPureIntro. intros k Hk.
          pose proof Ins_Im k Hk as H'.
          apply S_sub_KS in Hk.
          by pose proof Hφ2 k (Qn0' !!! k) Hk H' as H''. }

        iAssert (⌜∀ k, Bm !!! k ≤ Bm' !!! k⌝)%I as "%".
        { iDestruct "Hφ" as "(_&%&_&_&_&%&_)".
          rename H0 into Hφ1. rename H1 into Hφ5.
          iPureIntro. intros k. subst Bm'.
          destruct (decide (k ∈ S)).
          - pose proof Bm_eq_Qn k e as H'.
            rewrite H'. rewrite /(gmap_insert_map Bm S_map !!! k).
            unfold finmap_lookup_total.
            rewrite gmap_lookup_insert_map.
            rewrite (Lookup_Smap k e). simpl. subst S. 
            rewrite elem_of_intersection in e*; intros e.
            destruct e as [HKS e].
            rewrite elem_of_difference in e*; intros e.
            destruct e as [Hc _].
            rewrite elem_of_dom in Hc*; intros Hc.
            destruct Hc as [t Hc].
            pose proof Hφ1 k t as [Hc' _]. done.
            pose proof Hc' Hc.
            rewrite lookup_total_alt.
            rewrite Hc. apply leibniz_equiv_iff in H0. 
            rewrite <-H0. rewrite <-lookup_total_alt.
            apply Hφ5. done. by rewrite Dom_Smap. 
          - rewrite !lookup_total_alt.
            rewrite gmap_lookup_insert_map_ne.
            done. by rewrite Dom_Smap. }
        rename H0 into Bm_le_Bm'.

        iPoseProof((maxnat_set_update γ_cirm KS Bm Bm') 
                        with "[] [$HnS_starm]") as ">HnS_starm".
        { iPureIntro; intros k Hk; apply Bm_le_Bm'. }


        iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".

        iAssert (⌜set_of_map Cn ⊆ H⌝)%I as %Cn_sub_H.
        { iPoseProof ((auth_own_incl γ_s H _) with "[$HH $HnP_C]") as "%".
          rename H0 into H'. by apply gset_included in H'. }

        iAssert (⌜set_of_map Cm ⊆ H⌝)%I as %Cm_sub_H.
        { iPoseProof ((auth_own_incl γ_s H _) with "[$HH $HnP_Cm]") as "%".
          rename H0 into H'. by apply gset_included in H'. }

        iAssert (⌜set_of_map Cn' ⊆ H⌝)%I as %Cn'_sub_H.
        { iPureIntro. clear -Subset_Cn Cn_sub_H.  set_solver. }

        iAssert (⌜set_of_map Cm' ⊆ H⌝)%I as %Cm'_sub_H.
        { iPureIntro. clear -Subset_Cm Cm_sub_H Cn_sub_H.  set_solver. }

        iAssert (⌜∀ k, Cn !!! k ≤ T'⌝)%I as %Cn_le_T'.
        { iDestruct "Max_ts" as %H'. iPureIntro. 
          intros k. destruct (Cn !! k) as [t |] eqn: Hcn.
          - rewrite lookup_total_alt.
            rewrite Hcn; simpl. 
            apply set_of_map_member in Hcn.
            apply Cn_sub_H in Hcn.
            destruct H' as [H' _].
            apply H' in Hcn. clear -Hcn.
            lia.
          - rewrite lookup_total_alt.
            rewrite Hcn; simpl. lia. }
        
        iMod (own_update γ_s (● H) 
             (● H ⋅ ◯ (set_of_map Cn' ⋅ set_of_map Cm')) with "[$HH]") as "HH".
        { apply (auth_update_alloc _ (H) (set_of_map Cn' ⋅ set_of_map Cm')).
          apply local_update_discrete. intros mc Valid_H1 H1_eq.
          split; try done. rewrite /(ε ⋅? mc) in H1_eq.
          destruct mc. rewrite gset_op_union in H1_eq. 
          rewrite left_id in H1_eq *; intros H1_eq.
          rewrite <-H1_eq. 
          rewrite /(set_of_map Cn' ⋅ set_of_map Cm' ⋅? Some H).
          rewrite !gset_op_union.
          clear - Cn'_sub_H Cm'_sub_H. set_solver.
          rewrite /(set_of_map Cn' ⋅ set_of_map Cm' ⋅? None).
          rewrite gset_op_union.
          clear - Cn'_sub_H Cm'_sub_H H1_eq. set_solver. }
         
        iClear "HnP_C HnP_Cm".
        iDestruct "HH" as "(HH & (HnP_C & HnP_Cm))".
        
        iAssert (global_state γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r T' H hγ I R)
          with "[MCS_auth HH Hist Ht HI Out_I HR Out_R 
            Inf_R Hf Hγ FP_r Max_ts domm_IR domm_Iγ]" as "Hglob".
        { iFrame. }     
        
        
        iDestruct "HnS_oc" as "(%&%&%)".
        rename H0 into OC1. rename H1 into OC2. rename H2 into OC3.
        iAssert (outflow_constraints n In' Rn esn' Qn')%I as "HnS_oc".
        { iPureIntro. split; last split; try done.
          - intros n' k t HKS. destruct (decide (n' = m)).
            + subst n'. 
              assert (outset KT In' m = 
                          outset KT In m ∖ Qn_old ∪ Qn_new) as Outset'.
              { assert (In_temp = outflow_delete_set In m Qn_old) by done.
                assert (In' = outflow_insert_set In_temp m Qn_new) by done.
                assert (∀ kt, kt ∈ Qn_old → out In m !1 kt ≤ 1).
                { intros kt Hkt. apply OC3. } 
                pose proof (outflow_insert_set_outset In_temp m Qn_new In' H1).
                pose proof (outflow_delete_set_outset In m Qn_old In_temp H2 H0).
                by rewrite H4 in H3. }
              split.
              * intros Hout. rewrite Outset' in Hout.
                rewrite elem_of_union in Hout*; intros Hout.
                destruct Hout as [Hout | Hout].
                ** rewrite elem_of_difference in Hout *; intros Hout.
                   destruct Hout as [Hout1 Hout2].
                   apply (OC1 m k t) in Hout1.
                   destruct Hout1 as [H' H''].
                   assert (Ht := H'').
                   apply lookup_total_correct in H''.
                   rewrite <-H'' in Hout2.
                   assert (k ∉ S) as Hk.
                   { destruct (decide (k ∈ S)); try done.
                     assert ((k, Qn0' !!! k) ∈ Qn_old) as HkQn.
                     apply (HQn_old k (Qn0' !!! k)). 
                     split; try done. clear -Hout2 HkQn. done. }
                   split; try done. subst Qn'.
                   rewrite gmap_lookup_insert_map_ne.
                   done. by rewrite Dom_Smap. done.
                ** apply HQn_new in Hout.
                   destruct Hout as [Hout1 Hout2].
                   split. clear -Hout1 S_sub_es. set_solver.
                   subst Qn'. 
                   rewrite gmap_lookup_insert_map.
                   rewrite (Lookup_Smap k Hout1).
                   by rewrite Hout2. by rewrite Dom_Smap.
              * destruct (decide (k ∈ S)).
                ** subst Qn'.
                   rewrite gmap_lookup_insert_map; try done.
                   rewrite (Lookup_Smap k e). simpl.
                   intros [H1' H2'].
                   assert (k ∈ S ∧ t = Cn !!! k) as H''.
                   split; try done. by inversion H2'.
                   apply (HQn_new k t) in H''.
                   clear -H'' Outset'. set_solver.
                   by rewrite Dom_Smap.
                ** rewrite (Lookup_Qn'_ne k n0).
                   intros H'. apply OC1 in H'.
                   apply (HQn_old_ne k t) in n0.
                   clear -H' Outset' n0. set_solver. done.
            + assert (outset KT In' n' = outset KT In n') as Outset'.
              { assert (In' = outflow_insert_set In_temp m Qn_new) by done.
                assert (In_temp = outflow_delete_set In m Qn_old) by done.
                pose proof (outflow_insert_set_outset_ne In_temp m 
                                                Qn_new In' n' n0 H0).
                pose proof (outflow_delete_set_outset_ne In m  
                                                Qn_old In_temp n' n0 H1).
                by rewrite H3 in H2. } rewrite Outset'.
              split.
              * intros Hout. apply OC1 in Hout.
                destruct Hout as [Hout1 Hout2].
                assert (k ∉ S) as Hk.
                { destruct (decide (k ∈ S)); try done.
                  apply S_sub_es in e.
                  pose proof Disj_esn' n' m n0.
                  clear -H0 e Hout1. set_solver. }
                rewrite (Lookup_Qn'_ne k Hk).
                split; try done. done.
              * intros Hkt.
                assert (k ∉ S) as Hk.
                { destruct Hkt as [Hkt1 Hkt2].
                  destruct (decide (k ∈ S)); try done.
                  apply S_sub_es in e.
                  pose proof Disj_esn' n' m n0.
                  clear -H0 e Hkt1. set_solver. }
                rewrite (Lookup_Qn'_ne k Hk) in Hkt.
                by apply OC1 in Hkt. 
          - unfold outflow_le_1. intros n' kt. 
            destruct (decide (n' = m)).
            * subst n'. subst In'. unfold out, out_map. 
              unfold outflow_insert_set. simpl.
              rewrite nzmap_lookup_total_insert.
              unfold out, out_map.
              unfold In_temp, outflow_delete_set.
              simpl. rewrite nzmap_lookup_total_insert.
              pose proof OC3 m kt as OC3.
              destruct (decide (kt ∈ Qn_new)).
              ** rewrite nzmap_lookup_total_map_set; try done.
                 destruct (decide (kt ∈ Qn_old)).
                 *** rewrite nzmap_lookup_total_map_set; try done.
                     clear -OC3. lia.
                 *** rewrite nzmap_lookup_total_map_set_ne; try done.
                     assert (∀ (x: nat), x ≤ 1 → x = 0 ∨ x = 1) as Hx.
                     { lia. } apply Hx in OC3.
                     destruct OC3 as [OC3 | OC3].
                     rewrite OC3. lia.
                     assert (kt ∈ outset KT In m) as Hkt.
                     { unfold outset, dom_ms.
                       rewrite nzmap_elem_of_dom_total.
                       rewrite OC3. unfold ccmunit, ccm_unit; simpl.
                       by unfold nat_unit. }
                     destruct kt as [k t].
                     apply OC1 in Hkt.
                     destruct Hkt as [_ H'].
                     apply lookup_total_correct in H'.
                     rewrite <-H' in n0.
                     assert ((k, Qn0' !!! k) ∈ Qn_old) as H''.
                     { apply HQn_old. apply HQn_new in e.
                       destruct e as [e _]. split; try done. }
                     clear -H'' n0. done. apply HQn_new in e. 
                     destruct e as [e _]. apply S_sub_KS in e. done.
              ** rewrite nzmap_lookup_total_map_set_ne; try done.
                 destruct (decide (kt ∈ Qn_old)).
                 *** rewrite nzmap_lookup_total_map_set; try done.
                     clear -OC3. lia.
                 *** rewrite nzmap_lookup_total_map_set_ne; try done.
            * subst In'. unfold out, out_map. 
              unfold outflow_insert_set. simpl.
              rewrite nzmap_lookup_total_insert_ne; try done.
              rewrite nzmap_lookup_total_insert_ne; try done.
              pose proof OC3 n' kt as OC3.
              by unfold out in OC3. }

        iDestruct "HnS_ocm" as "(%&%&%)".
        rename H0 into OC1m. rename H1 into OC2m. rename H2 into OC3m.

        iAssert (outflow_constraints m Im' Rm esm Qm)%I as "HnS_ocm".
        { iPureIntro. split; last split; try done. }

        iAssert (⌜domm In = {[n]}⌝)%I as %Domm_In.
        { iDestruct "HnS_si" as "(_&_&%&_)". by iPureIntro. }

        iAssert (⌜domm Im = {[m]}⌝)%I as %Domm_Im.
        { iDestruct "HnS_sim" as "(_&_&%&_)". by iPureIntro. }

        assert (domm In' = {[n]}) as Domm_In'.
        { try done. }

        iAssert (⌜domm Im_temp = {[m]}⌝)%I as %Domm_Im_temp.
        { assert (Im_temp = inflow_delete_set Im m Qn_old) by done.
          pose proof (flowint_inflow_delete_set_dom Im m Qn_old Im_temp H0).
          iPureIntro; rewrite H1 Domm_Im. clear; set_solver. } 

        assert (domm In_temp = {[n]}) as Domm_In_temp.
        { try done. }


        assert (domm Im' = {[m]}) as Domm_Im'.
        { assert (Im' = inflow_insert_set Im_temp m Qn_new) by done.
          pose proof (flowint_inflow_insert_set_dom Im_temp m Qn_new Im' H0).
          rewrite H1 Domm_Im_temp. clear; set_solver. }

        iAssert (singleton_interfaces_ghost_state γ_I γ_R n In' Rn
            ∗ singleton_interfaces_ghost_state γ_I γ_R m Im' Rm)%I 
                    with "[HnS_si HnS_sim]" as "(HnS_si & HnS_sim)".
        { iDestruct "HnS_si" as "(HIn & HRn & Domm_In & Domm_Rn)".
          iDestruct "HnS_sim" as "(HIm & HRm & Domm_Im & Domm_Rm)".
          iCombine "HIn HIm" as "HInm".
          assert (Im_temp = inflow_delete_set Im m Qn_old) 
              as HIm_temp. done.
          assert (In_temp = outflow_delete_set In m Qn_old)
              as HIn_temp. done.
          assert (In' = outflow_insert_set In_temp m Qn_new)
              as HIn'. done.
          assert (Im' = inflow_insert_set Im_temp m Qn_new)
              as HIm'. done.
          iPoseProof (own_valid with "[$HInm]") as "%".
          rename H0 into Valid_Inm. 
          rewrite auth_frag_valid in Valid_Inm*; intros Valid_Inm.
          assert (m ∈ domm Im) by (clear -Domm_Im; set_solver).
          assert (domm In ≠ ∅) by (clear -Domm_In; set_solver).
          assert (∀ kt, kt ∈ Qn_old → 1 ≤ out In m !1 kt).
          { intros [k t] Hkt. apply HQn_old in Hkt.
            destruct Hkt as [Hkt1 Hkt2].
            apply Out_In_m in Hkt1. subst t.
            clear -Hkt1. unfold outset in Hkt1.
            rewrite nzmap_elem_of_dom_total in Hkt1*; intros Hkt1.
            unfold ccmunit, ccm_unit in Hkt1. simpl in Hkt1.
            unfold nat_unit in Hkt1. 
            assert (∀ x: nat, x ≠ 0 → 1 ≤ x). lia.
            apply H; try done. }
          pose proof (flowint_delete_eq In In_temp Im Im_temp 
                  m Qn_old H2 H0 H1 HIn_temp HIm_temp Valid_Inm) as HInm_temp.
          rewrite HInm_temp in Valid_Inm.
          assert (m ∈ domm Im_temp) by (clear -Domm_Im_temp; set_solver).
          assert (domm In_temp ≠ ∅) by (clear -Domm_In_temp; set_solver).
          pose proof (flowint_insert_eq In_temp In' Im_temp Im' 
                  m Qn_new H3 H4 HIn' HIm' Valid_Inm) as HInm'.
          iEval (rewrite HInm_temp) in "HInm".
          iEval (rewrite HInm') in "HInm".
          iEval (rewrite auth_frag_op) in "HInm".
          iDestruct "HInm" as "(?&?)". iFrame. by iPureIntro. }

        
        iAssert (⌜φ0 esn' Qn'⌝ ∗ ⌜φ1 Bn0' Cn' Qn'⌝ ∗ ⌜φ2 n Bn0' In'⌝ 
                  ∗ ⌜φ3 n Bn0' Rn⌝ ∗ ⌜φ4 n Rn⌝ ∗ ⌜φ5 Bn0' Qn'⌝ 
                  ∗ ⌜φ6 Bn0' T'⌝ ∗ ⌜φ7 n esn' Rn Qn'⌝ ∗ ⌜φ8 n In'⌝)%I
                with "[Hφ]" as "Hφ".
        { iDestruct "Hφ" as "(%&%&%&%&%&%&%&%&%)". 
          rename H0 into Hφ0. rename H1 into Hφ1.
          rename H2 into Hφ2. rename H3 into Hφ3.
          rename H4 into Hφ4. rename H5 into Hφ5. 
          rename H6 into Hφ6. rename H7 into Hφ7.
          rename H8 into Hφ8.
          iPureIntro. split; last split; last split; 
          last split; last split; last split; last split; last split.
          - unfold φ0. intros k HKS Hnot.
            assert (k ∉ S) as Hk.
            { destruct (decide (k ∈ S)); try done.
              apply S_sub_es in e. pose proof Hnot m as Hnot.
              clear -e Hnot. set_solver. }
            rewrite (Lookup_Qn'_ne k Hk).
            apply Hφ0; try done.  
          - unfold φ1. intros k t' HKS.
            rewrite map_eq_iff in MergeEq*; intros MergeEq.
            pose proof MergeEq k as MergeEq.
            rewrite !gmap_imerge_prf in MergeEq.
            unfold f_merge in MergeEq. split.
            + intros HCn'k. destruct (Cn !! k) as [t |] eqn: HCnk.
              * destruct (decide (Some t ≠ None)); try done.
                ** destruct (decide (Cn' !! k ≠ None)); try done.
                   pose proof Hφ1 k t as [H' _]. done.
                   pose proof H' HCnk as H'.
                   rewrite <-HCn'k, H'. by rewrite MergeEq.
                   exfalso; apply n1. rewrite HCn'k; try done.
                ** exfalso; apply n0. intros H'; inversion H'.    
              * pose proof set_of_map_member_ne Cn k HCnk t' as H'.
                pose proof set_of_map_member Cn' k t' HCn'k as H''.
                apply Subset_Cn in H''. clear -H' H''.
                set_solver.
            + intros HCn'. destruct (Cn !! k) as [t |] eqn: HCnk.
              * assert (k ∈ S) as Hk.
                { assert (k ∈ dom (gset K) Cn) as H1'.
                  rewrite elem_of_dom. rewrite HCnk; by exists t.
                  assert (k ∉ dom (gset K) Cn') as H2'.
                  rewrite not_elem_of_dom. done. 
                  subst S. clear - HKS H1' H2'. set_solver. }
                rewrite (Lookup_Qn' k Hk).
                pose proof Hφ1 k t as H'.
                destruct H' as [H' _]. done.
                pose proof H' HCnk as H'. 
                by rewrite H'.
              * assert (k ∉ S) as Hk.
                { assert (k ∉ dom (gset K) Cn) as H1'.
                  rewrite not_elem_of_dom. done. 
                  subst S. clear -H1'. set_solver. }
                rewrite (Lookup_Qn'_ne k Hk).
                pose proof Hφ1 k 0 as H'.
                destruct H' as [_ H']. done.
                by pose proof H' HCnk as H'. 
          - unfold φ2. try done.
          - unfold φ3. try done.
          - try done.
          - intros k HKS. destruct (decide (k ∈ S)).
            + rewrite /(Qn' !!! k).
              unfold finmap_lookup_total. 
              rewrite (Lookup_Qn' k e).
              destruct (Cn !! k) as [t |] eqn: HCnk.
              * pose proof Hφ1 k t as H'.
                destruct H' as [H' _]. done.
                pose proof H' HCnk as H'.
                rewrite lookup_total_alt.
                by rewrite H'.
              * by simpl; lia.
            + rewrite /(Qn' !!! k).
              rewrite /(Bn0' !!! k). 
              unfold finmap_lookup_total. 
              rewrite (Lookup_Qn'_ne k n0).
              pose proof Hφ5 k HKS as H'.    
              rewrite /(Qn0' !!! k) in H'.
              by rewrite /(Bn0' !!! k) in H'. 
          - try done.
          - intros k. intros H'. rewrite elem_of_dom.
            apply Hφ7 in H'. rewrite elem_of_dom in H'*; intros H'.
            destruct (decide (k ∈ S)).
            * rewrite (Lookup_Qn' k e).
              assert (k ∈ dom (gset K) Cn) as H''.
              { subst S. clear -e; set_solver. }
              by rewrite elem_of_dom in H''*; intros H''.
            * by rewrite (Lookup_Qn'_ne k n0).
          - try done. }
                              
        iAssert (⌜φ0 esm Qm⌝ ∗ ⌜φ1 Bm' Cm' Qm⌝ ∗ ⌜φ2 m Bm' Im'⌝ 
                  ∗ ⌜φ3 m Bm' Rm⌝ ∗ ⌜φ4 m Rm⌝ ∗ ⌜φ5 Bm' Qm⌝ 
                  ∗ ⌜φ6 Bm' T'⌝ ∗ ⌜φ7 m esm Rm Qm⌝ ∗ ⌜φ8 m Im'⌝)%I
                with "[Hφm]" as "Hφm".
        { iDestruct "Hφm" as "(%&%&%&%&%&%&%&%&%)". 
          rename H0 into Hφ0. rename H1 into Hφ1.
          rename H2 into Hφ2. rename H3 into Hφ3.
          rename H4 into Hφ4. rename H5 into Hφ5. 
          rename H6 into Hφ6. rename H7 into Hφ7.
          rename H8 into Hφ8. 
          iPureIntro. split; last split; last split; 
          last split; last split; last split; 
          last split; last split.
          - unfold φ0. try done.
          - unfold φ1. intros k t HKS.
            rewrite map_eq_iff in MergeEq*; intros MergeEq.
            pose proof MergeEq k as MergeEq.
            rewrite !gmap_imerge_prf in MergeEq.
            unfold f_merge in MergeEq. split.
            + intros HCm'k. assert (H' := HCm'k). 
              apply set_of_map_member in H'.
              apply Subset_Cm in H'.
              rewrite elem_of_union in H'*; intros H'.
              destruct H' as [H' | H'].
              * apply set_of_map_member_rev in H'.
                subst Bm'. destruct (Cn' !! k) as [t' | ] eqn: HCn'k.
                ** rewrite decide_True in MergeEq.
                   destruct (decide (Some t' ≠ None)).
                   assert (t' = t) as Ht.
                   { rewrite H' in MergeEq.
                     by inversion MergeEq. }
                   subst t'. 
                   apply set_of_map_member in H'.
                   apply set_of_map_member in HCm'k.
                   apply set_of_map_member in HCn'k.
                   clear -H' HCm'k  HCn'k Subset_disj. set_solver.
                   exfalso; apply n0. intros H''; inversion H''.
                   rewrite H'; try done.
                ** rewrite decide_True in MergeEq.
                   destruct (decide (None ≠ None)).
                   exfalso; apply n0; done.
                   destruct (decide (k ∈ esn' !!! m)).
                   *** assert (k ∈ S) as Hk.
                       { subst S. rewrite elem_of_intersection.
                         split; try done.
                         rewrite elem_of_difference.
                         split. rewrite elem_of_dom.
                         rewrite H'. by exists t.
                         by rewrite not_elem_of_dom. }
                       rewrite gmap_lookup_insert_map.
                       rewrite (Lookup_Smap k Hk).
                       rewrite /(Cn !!! k). 
                       unfold finmap_lookup_total.
                       rewrite H'; by simpl.
                       rewrite Dom_Smap. done.
                   *** rewrite H' in MergeEq.
                       inversion MergeEq.
                   *** rewrite H'. done.
                * apply set_of_map_member_rev in H'.
                  pose proof Hφ1 k t as H''.
                  destruct H'' as [H'' _]. done.
                  pose proof H'' H' as HBm.
                  destruct (decide (k ∈ S)).
                  ** subst Bm'.
                     rewrite gmap_lookup_insert_map.
                     rewrite (Lookup_Smap k e).
                     destruct (Cn !! k) as [t' | ] eqn: HCnk.
                     *** destruct (decide (Some t' ≠ None)); last first.
                         exfalso; apply n0. intros H'''; inversion H'''. 
                         destruct (Cn' !! k) as [t'' | ] eqn: HCn'k.
                         **** assert (k ∉ S) as Hk.
                              { assert (k ∈ dom (gset K) Cn). 
                                rewrite elem_of_dom. rewrite HCnk.
                                by exists t'.
                                assert (k ∈ dom (gset K) Cn'). 
                                rewrite elem_of_dom. rewrite HCn'k.
                                by exists t''. subst S.
                                clear -H1 H0. set_solver. }
                              clear -Hk e.
                              set_solver.
                         **** rewrite decide_True in MergeEq.
                              apply f_equal. apply lookup_total_correct.
                              rewrite HCnk. apply leibniz_equiv.
                              apply leibniz_equiv_iff in HCm'k. 
                              rewrite <-HCm'k. by rewrite MergeEq. 
                              by apply S_sub_es in e. 
                     *** assert (k ∉ S) as Hk.
                         { assert (k ∉ dom (gset K) Cn). 
                           rewrite not_elem_of_dom. rewrite HCnk.
                           done. subst S. clear -H0; set_solver. }
                         clear -Hk e. set_solver.
                     *** by rewrite Dom_Smap.
                  ** rewrite gmap_lookup_insert_map_ne.
                     done. by rewrite Dom_Smap.
            + intros HCm'. assert (Cm !! k = None) as HCm.
              { destruct (Cm !! k) eqn: HCmk; try done.
                assert (k ∈ dom (gset K) Cm).
                { rewrite elem_of_dom. rewrite HCmk.
                  by exists n0. }
                assert (k ∉ dom (gset K) Cm').
                { by rewrite not_elem_of_dom. }
                clear -H0 H1 Cm_sub_Cm'.
                set_solver. }
              pose proof Hφ1 k 0 as H'.
              destruct H' as [_ H']. done.
              pose proof H' HCm as H'.
              assert (k ∉ S) as Hk.
              { destruct (decide (k ∈ S)); try done.
                subst S. assert (k ∈ dom (gset K) Cn) as H1'.
                { clear -e. set_solver. }
                assert (k ∉ dom (gset K) Cn') as H2'.
                { clear -e. set_solver. }
                rewrite elem_of_dom in H1'*; intros H1'.
                rewrite not_elem_of_dom in H2'*; intros H2'.
                destruct H1' as [t' H1'].
                rewrite decide_True in MergeEq.
                rewrite decide_False in MergeEq.
                rewrite decide_True in MergeEq.
                rewrite HCm' in MergeEq.
                rewrite MergeEq in H1'. inversion H1'.
                by apply S_sub_es in e.
                rewrite H2'. intros ?; try done.
                rewrite H1'; try done. }
              subst Bm'. rewrite gmap_lookup_insert_map_ne.
              done. by rewrite Dom_Smap.
          - unfold φ2. intros k t HKS Hkt.
            assert (inset KT Im' m = 
                          inset KT Im m ∖ Qn_old ∪ Qn_new) as Hinset.
            { assert (Im_temp = inflow_delete_set Im m Qn_old) by done.
              assert (Im' = inflow_insert_set Im_temp m Qn_new) by done.
              assert (∀ kt, kt ∈ Qn_old → inf Im m !1 kt ≤ 1) as H'.
              { intros kt kt_in_Qnold. apply Hφ8. }   
              pose proof (inflow_delete_set_inset Im m Qn_old Im_temp H' H0).
              pose proof (inflow_insert_set_inset Im_temp m Qn_new Im' H1).
              by rewrite H3 H2. }
            rewrite Hinset in Hkt.
            rewrite elem_of_union in Hkt*; intros Hkt.
            destruct Hkt as [Hkt | Hkt].
            * rewrite elem_of_difference in Hkt*; intros Hkt.
              destruct Hkt as [Hkt1 Hkt2].
              apply Hφ2 in Hkt1; try done.
              destruct (decide (k ∈ S)).
              ** pose proof Bm_eq_Qn k e as H'.
                 assert ((k,t) ∈ Qn_old) as H''.
                 { apply HQn_old. split; try done.
                   by rewrite H' in Hkt1. }
                 clear -H'' Hkt2. set_solver.
              ** rewrite lookup_total_alt. subst Bm'.
                 rewrite gmap_lookup_insert_map_ne.
                 by rewrite lookup_total_alt in Hkt1.
                 by rewrite Dom_Smap.
            * apply HQn_new in Hkt.
              destruct Hkt as [Hkt1 Hkt2].
              rewrite lookup_total_alt.
              subst Bm'. rewrite gmap_lookup_insert_map.
              rewrite (Lookup_Smap k Hkt1).
              by simpl. by rewrite Dom_Smap.
          - unfold φ3. intros k.
            destruct (decide (k ∈ S)).
            + apply S_sub_insetm in e.
              right. unfold in_inset.
              by unfold inset in e.
            + subst Bm'.
              rewrite gmap_lookup_insert_map_ne.
              apply Hφ3. by rewrite Dom_Smap.
          - try done.
          - intros k HKS. 
            apply (Nat.le_trans _ (Bm !!! k) _).
            apply Hφ5. done. apply Bm_le_Bm'.
          - intros k HKS. destruct (decide (k ∈ S)).
            + rewrite /(Bm' !!! k).
              unfold finmap_lookup_total.
              subst Bm'.
              rewrite gmap_lookup_insert_map.
              rewrite (Lookup_Smap k e). simpl.    
              apply Cn_le_T'. by rewrite Dom_Smap.
            + rewrite /(Bm' !!! k).
              unfold finmap_lookup_total.
              subst Bm'.
              rewrite gmap_lookup_insert_map_ne.
              apply Hφ6. done. by rewrite Dom_Smap.
          - try done.
          - intros kt. subst Im'. unfold inflow_insert_set.
            unfold inflow_map_set. unfold inf; simpl.
            rewrite !lookup_insert. simpl.
            destruct (decide (kt ∈ Qn_new)).
            + rewrite nzmap_lookup_total_map_set; try done.
              destruct (decide (kt ∈ Qn_old)).
              * rewrite nzmap_lookup_total_map_set; try done.
                pose proof Hφ8 kt as H'. clear -H'. lia.
              * rewrite nzmap_lookup_total_map_set_ne; try done.
                pose proof Hφ8 kt as H'.
                assert (inf Im m !1 kt = 0 ∨ inf Im m !1 kt = 1).
                { clear -H'; lia. }
                destruct H0 as [H0 | H0].
                ** rewrite H0; lia.
                ** assert (kt ∈ inset KT Im m).
                   { unfold inset. rewrite nzmap_elem_of_dom_total.
                     rewrite H0. unfold ccmunit, ccm_unit; simpl.
                     unfold nat_unit; lia. }
                   destruct kt as [k t]. apply Hφ2 in H1.
                   apply HQn_new in e. destruct e as [e1 e2].
                   pose proof Ins_Im k e1. apply Hφ2 in H2.
                   rewrite H2 in H1.
                   assert ((k, t) ∈ Qn_old).
                   apply HQn_old. split; try done.
                   done. apply S_sub_KS in e1. done.
                   apply HQn_new in e. destruct e as [e _].
                   apply S_sub_KS in e. done.
            + rewrite nzmap_lookup_total_map_set_ne; try done.
              destruct (decide (kt ∈ Qn_old)).
              * rewrite nzmap_lookup_total_map_set; try done.
                pose proof Hφ8 kt as H'. clear -H'; lia.
              * rewrite nzmap_lookup_total_map_set_ne; try done. }

    iModIntro. iExists Qn', Bm'. iFrame "Hglob". 
    iSplitL "node_n HnP_gh HnP_t HnP_C HnP_frac".
    { iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn', T. iFrame. }
    iSplitL "HnS_gh HnS_FP HnS_cl HnS_H HnS_star HnS_frac Hφ HnS_si".
    { iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn', In', Rn. iFrame "∗#". }
    iSplitL "node_m HnP_ghm HnP_tm HnP_Cm HnP_fracm".
    { iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm, Tm. iFrame. }
    iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm, Im', Rm. iFrame "∗#".
    destruct (decide (m = r)); try done.
  Qed.        
         




  Lemma compact_spec N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r (n: Node) :
      ⊢ mcs_inv N γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh lc r -∗
          inFP γ_f n -∗ <<< ∀ t H, MCS γ_te γ_he t H >>> 
                              compact #n @ ⊤ ∖ ↑N
                        <<< MCS γ_te γ_he t H, RET #() >>>.
  Proof.
    iIntros "#HInv". iLöb as "IH" forall (n).
    iIntros "#FP_n". iIntros (Φ) "AU". wp_lam.
    awp_apply lockNode_spec_high; try done.
    iAaccIntro with ""; try eauto with iFrame.
    iIntros (Cn Bn Qn)"HnP_n". iModIntro.
    wp_pures. iDestruct "HnP_n" as (γ_en γ_cn γ_bn γ_qn γ_cirn esn T)"(node_n   
                            & HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iPoseProof ((node_edgeset_disjoint r n) with "[$node_n]") as "%".
    rename H into Disj_esn.                        
    wp_apply (atCapacity_spec with "node_n").
    iIntros (b) "(node_n & _)". destruct b; last first; wp_pures.
    - awp_apply (unlockNode_spec_high with "[] [] [-AU]"); try done.
      iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn, T. iFrame.
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iMod "AU" as (t H)"[MCS [_ Hclose]]".
      iMod ("Hclose" with "MCS") as "HΦ".
      by iModIntro.
    - wp_apply (chooseNext_spec with "node_n").
      iIntros (m esn' esm0 Cm0)"(node_n & es_ne & Hor)".
      iDestruct "es_ne" as %es_ne.
      iDestruct "Hor" as "[ Hesn' | 
                      (Hesn' & node_m & Hl_m & Hcm & Hesm) ]"; last first.
      + iDestruct "Hesn'" as %Hesn'.
        iDestruct "Hcm" as %Hcm.
        iDestruct "Hesm" as %Hesm.
        wp_pures.
        iApply fupd_wp. iInv "HInv" as ">H".
        iDestruct "H" as (T0' H0 hγ0 I0 R0) "(Hglob & Hstar)".

        iAssert (⌜m ∉ domm I0⌝)%I as "%".
        { destruct (decide (m ∈ domm I0)); try done.
          rewrite (big_sepS_delete _ (domm I0) m); last by eauto.
          iDestruct "Hstar" as "(Hm & _)".
          iDestruct "Hm" as (bm Cm Bm Qm)"(Hl_m' & _)".
          iDestruct (mapsto_valid_2 with "Hl_m Hl_m'") as "%".
          exfalso. done. }
          

        iAssert (⌜n ∈ domm I0⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rename H into m_notin_I0. rename H1 into n_in_I0.  

        rewrite (big_sepS_delete _ (domm I0) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn' Bn' Qn')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In0 Rn0) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn'. subst Bn'. subst Qn'.

        iAssert (nodePred_aux γ_gh γ_t γ_s lc r n Cn Bn Qn 
                                          γ_en γ_cn γ_bn γ_qn γ_cirn esn T)%I
                   with "[HnP_gh HnP_frac HnP_C HnP_t]" as "HnP_aux".
        { iFrame. }
        
        iAssert (nodeShared' γ_I γ_R γ_f γ_gh r n Cn Bn Qn H0 T0' 
                        γ_en γ_cn γ_bn γ_qn γ_cirn esn In0 Rn0) with
                  "[HnS_gh HnS_frac HnS_si HnS_FP 
                        HnS_cl HnS_oc HnS_H HnS_star Hφ]" as "HnS_n'".
        { iFrame. }                

        set (Qm0 := ∅ : gmap K nat).  
        set (Bm0 := ∅ : gmap K nat).  
        set (Im0 := int {| infR := {[m := ∅]} ; outR := ∅|}: multiset_flowint_ur KT).
        set (Rm0 := int {| infR := {[m := ∅]} ; outR := ∅|}: multiset_flowint_ur K).
               

        iMod ((ghost_update_contExt γ_te γ_he γ_s γ_t γ_I γ_R γ_f γ_gh r lc
                T0' H0 hγ0 I0 R0 
                m Cm0 esm0 Bm0 Qm0 Im0 Rm0
                n Cn Bn Qn γ_en γ_cn γ_bn γ_qn γ_cirn (esn: esT) T In0 Rn0) with 
                "[] [$FP_n $HnP_aux HnS_n' $Hglob]") 
                    as (hγ' I0' R0' γ_em γ_cm γ_bm γ_qm γ_cirm)"H".
        { iPureIntro; try done. }
        { iDestruct "HnS_n'" as 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                      & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)". iFrame. }
            
        iDestruct "H" as "(#FP_m & HnP_aux & HnS_n' & HnP_auxm & HnS_auxm 
                  & Hglob & Esn_empty & Out_In_m & Out_Rn_m 
                  & Domm_I0' & m_neq_r & m_neq_n)".
        iDestruct "Esn_empty" as %Esn_empty.
        iDestruct "Out_In_m" as %Out_In_m.
        iDestruct "Out_Rn_m" as %Out_Rn_m.
        iDestruct "Domm_I0'" as %Domm_I0'.
        iDestruct "m_neq_r" as %m_neq_r.
        iDestruct "m_neq_n" as %m_neq_n.                   

        iAssert (⌜history_init H0⌝)%I as %Hist.
        { by iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)". }

        iMod ((ghost_update_interface_mod) with 
                "[] [$node_n $HnP_aux $HnS_n' $node_m $HnP_auxm $HnS_auxm]") 
                    as "H".
        { iPureIntro; try repeat split; try done. }            

        iDestruct "H" as (Bn0' Qn0')"(HnP_n' & HnS_n & HnP_m' & HnS_m)".
        
        iAssert (⌜bn = true⌝)%I as "%".
        { destruct bn; try done.
          iDestruct "HnP_n'" as "(node_n & _)".
          iDestruct "Hlif_n" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r n) with "[$]") as "%".
          contradiction. } subst bn.


        iModIntro. iSplitR "AU HnP_n'".
        { iNext. iExists T0', H0, hγ', I0', R0'.
          iFrame "Hglob". rewrite Domm_I0'.     
          rewrite (big_sepS_delete _ (domm I0 ∪ {[m]}) m); 
              last first. { clear; set_solver. }
          iSplitL "Hl_m HnP_m' HnS_m".
          { iExists false, Cm0, Bm0, Qm0. iFrame "Hl_m".
            iFrame "HnS_m". 
            iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm0, T.
            iFrame. }
          assert ((domm I0 ∪ {[m]}) ∖ {[m]} = domm I0) as H'.
          { clear -m_notin_I0. set_solver. }
          rewrite H'. rewrite (big_sepS_delete _ (domm I0) n); 
              last apply n_in_I0.
          iFrame "Hstar'". iExists true, Cn, Bn0', Qn0'.
          iFrame. } 
            
        iModIntro.
        clear γ_em γ_cm γ_bm γ_qm γ_cirm.
        
        awp_apply lockNode_spec_high; try done.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros (Cm Bm Qm)"HnP_m". iModIntro.
        wp_pures.
        iDestruct "HnP_m" as (γ_em γ_cm γ_bm γ_qm γ_cirm esm Tm)"(node_m   
                            & HnP_ghm & HnP_fracm & HnP_Cm & HnP_tm)".
        iDestruct "HnP_n'" as "(node_n & HnP_gh & HnP_frac & HnP_C & HnP_t)".
        wp_apply (mergeContents_spec with "[$node_n $node_m]"); try done.
        iIntros (Cn' Cm') "(node_n & node_m & Subset_Cn & Subset_Cm 
                                     & Subset_disj & Cm_sub_Cm' & MergeEq)".  
        iDestruct "Subset_Cn" as %Subset_Cn.
        iDestruct "Subset_Cm" as %Subset_Cm.
        iDestruct "Subset_disj" as %Subset_disj.
        iDestruct "Cm_sub_Cm'" as %Cm_sub_Cm'.
        iDestruct "MergeEq" as %MergeEq. wp_pures.
        iApply fupd_wp. iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rename H1 into n_in_I.  
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn'' Bn'' Qn'')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn''. subst Bn''. subst Qn''.
        iAssert (⌜m ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_m] [$Hf]") as "H'". }
        rename H1 into m_in_I.
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) m); last by set_solver.
        iDestruct "Hstar'" as "(H_m & Hstar')".
        iDestruct "H_m" as (bm Cm'' Bm'' Qm'')"(Hl_m & Hlif_m & HnS_m)".
        iDestruct "HnS_m" as (γ_em' γ_cm' γ_bm' γ_qm' γ_cirm' es' Im Rm) 
                      "(HnS_ghm & HnS_fracm & HnS_sim & HnS_FPm 
                                & HnS_clm & HnS_ocm & HnS_Hm & HnS_starm & Hφm)".
        iPoseProof (ghost_heap_sync with "[$HnP_ghm] [$HnS_ghm]") 
                                  as "(% & % & % & % & %)".
        subst γ_em'. subst γ_cm'. subst γ_bm'. subst γ_qm'. subst γ_cirm'.
        iPoseProof (frac_eq with "[$HnP_fracm] [$HnS_fracm]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cm''. subst Bm''. subst Qm''.

        iAssert (⌜bn = true⌝)%I as "%".
        { destruct bn; try done.
          iDestruct "Hlif_n" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r n) with "[$]") as "%".
          contradiction. } subst bn.
                
        iAssert (⌜bm = true⌝)%I as "%".
        { destruct bm; try done.
          iDestruct "Hlif_m" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r m) with "[$]") as "%".
          contradiction. } subst bm.

        iAssert (nodePred_aux γ_gh γ_t γ_s lc r n Cn Bn0' Qn0' 
                                          γ_en γ_cn γ_bn γ_qn γ_cirn esn' T)%I
                   with "[HnP_gh HnP_frac HnP_C HnP_t]" as "HnP_aux".
        { iFrame. }           

        iAssert (nodePred_aux γ_gh γ_t γ_s lc r m Cm Bm Qm 
                                          γ_em γ_cm γ_bm γ_qm γ_cirm esm Tm)%I
                   with "[HnP_ghm HnP_fracm HnP_Cm HnP_tm]" as "HnP_auxm".
        { iFrame. }
        
        iAssert (nodeShared γ_I γ_R γ_f γ_gh r n Cn Bn0' Qn0' H T')%I
                  with "[HnS_gh HnS_frac HnS_si HnS_FP HnS_cl 
                    HnS_oc HnS_H HnS_star Hφ]" as "HnS_n".
        { iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn', In, Rn. iFrame. }
                              
        iAssert (nodeShared γ_I γ_R γ_f γ_gh r m Cm Bm Qm H T')%I
                  with "[HnS_ghm HnS_fracm HnS_sim HnS_FPm HnS_clm 
                    HnS_ocm HnS_Hm HnS_starm Hφm]" as "HnS_m".
        { iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm, Im, Rm. iFrame. }
        
        iMod (mergeContents_ghost_update with 
                "[] [$node_n $HnP_aux $node_m $HnP_auxm $HnS_n $HnS_m $Hglob]") 
                    as (Qn' Bm') "(HnP_n & HnS_n & HnP_m & HnS_m & Hglob)".
        { iPureIntro; try done. }            
        
        iModIntro.
        iSplitR "AU HnP_n HnP_m".
        { iNext. iExists T', H, hγ, I, R. iFrame "Hglob".
          rewrite (big_sepS_delete _ (domm I) n); last by eauto.
          iSplitL "Hl_n HnS_n".
          { iExists true, Cn', Bn0', Qn'. iFrame "Hl_n".
            iSplitR; try done. }
          rewrite (big_sepS_delete _ (domm I ∖ {[n]}) m); last first.
          clear - m_neq_n m_in_I. set_solver. 
          iFrame "Hstar'". iExists true, Cm', Bm', Qm.
          iFrame "Hl_m Hlif_m". iFrame. }
        iModIntro.
        awp_apply (unlockNode_spec_high with "[] [] 
            [$HnP_n]"); try done.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_"; iModIntro. wp_pures.
        awp_apply (unlockNode_spec_high with "[] [] 
            [$HnP_m]"); try done.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_"; iModIntro. wp_pures.
        iApply "IH"; try done.
    + wp_pures.
      iDestruct "Hesn'" as "%".
      subst esn'.
    
      iApply fupd_wp.
      iInv "HInv" as ">H".
      iDestruct "H" as (T0' H0 hγ0 I0 R0) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I0⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
      rename H into n_in_I0.    

      rewrite (big_sepS_delete _ (domm I0) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn'' Bn'' Qn'')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In0 Rn0) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn''. subst Bn''. subst Qn''.
        
        iAssert (inFP γ_f m)%I as "#FP_m".
        { iApply "HnS_cl". iPureIntro; clear -es_ne; set_solver. }
        
        iAssert (⌜m ∈ domm I0⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_m] [$Hf]") as "H'". }
        rename H into m_in_I0.  
        
        iAssert (⌜m ≠ n ∧ m ≠ r⌝)%I as %H'.
        { iPoseProof (node_edgeset_empty_root_self with "[$node_n]") as "%".
          destruct H as [Esn_r Esn_n]. iPureIntro. split.
          - destruct (decide (m = n)); try done.
            subst m. clear -es_ne Esn_n. set_solver.
          - destruct (decide (m = r)); try done.
            subst m. clear -es_ne Esn_r. set_solver. }
        destruct H' as [m_neq_n m_neq_r].    
                  
        iAssert (⌜bn = true⌝)%I as "%".
        { destruct bn; try done.
          iDestruct "Hlif_n" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r n) with "[$]") as "%".
          contradiction. } subst bn.
        
        iModIntro. iSplitR "AU node_n HnP_frac HnP_gh HnP_C HnP_t".
        { iNext. iExists T0', H0, hγ0, I0, R0. iFrame "Hglob".
          rewrite (big_sepS_delete _ (domm I0) n); last by eauto.
          iFrame "Hstar'". iExists true, Cn, Bn, Qn. iFrame.
          iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn, In0, Rn0.
          iFrame. } 
        
        iModIntro.
      

        awp_apply lockNode_spec_high; try done.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros (Cm Bm Qm)"HnP_m". iModIntro.
        wp_pures.
        iDestruct "HnP_m" as (γ_em γ_cm γ_bm γ_qm γ_cirm esm Tm)"(node_m   
                            & HnP_ghm & HnP_fracm & HnP_Cm & HnP_tm)".
        wp_apply (mergeContents_spec with "[$node_n $node_m]"); try done.
        iIntros (Cn' Cm') "(node_n & node_m & Subset_Cn & Subset_Cm 
                                     & Subset_disj & Cm_sub_Cm' & MergeEq)".  
        iDestruct "Subset_Cn" as %Subset_Cn.
        iDestruct "Subset_Cm" as %Subset_Cm.
        iDestruct "Subset_disj" as %Subset_disj.
        iDestruct "Cm_sub_Cm'" as %Cm_sub_Cm'.
        iDestruct "MergeEq" as %MergeEq. wp_pures.
        iApply fupd_wp. iInv "HInv" as ">H".
        iDestruct "H" as (T' H hγ I R) "(Hglob & Hstar)".
        iAssert (⌜n ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_n] [$Hf]") as "H'". }
        rename H1 into n_in_I.  
        rewrite (big_sepS_delete _ (domm I) n); last by eauto.
        iDestruct "Hstar" as "(H_n & Hstar')".
        iDestruct "H_n" as (bn Cn'' Bn'' Qn'')"(Hl_n & Hlif_n & HnS_n)".
        iDestruct "HnS_n" as (γ_en' γ_cn' γ_bn' γ_qn' γ_cirn' es' In Rn) 
                      "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                                & HnS_cl & HnS_oc & HnS_H & HnS_star & Hφ)".
        iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                                  as "(% & % & % & % & %)".
        subst γ_en'. subst γ_cn'. subst γ_bn'. subst γ_qn'. subst γ_cirn'.
        iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cn''. subst Bn''. subst Qn''.
        iAssert (⌜m ∈ domm I⌝)%I as "%". 
        { iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HR 
            & Out_R & Inf_R & Hf & Hγ & FP_r & Max_ts & domm_IR & domm_Iγ)".
          by iPoseProof (inFP_domm _ _ _ with "[$FP_m] [$Hf]") as "H'". }
        rename H1 into m_in_I.
        rewrite (big_sepS_delete _ (domm I ∖ {[n]}) m); last by set_solver.
        iDestruct "Hstar'" as "(H_m & Hstar')".
        iDestruct "H_m" as (bm Cm'' Bm'' Qm'')"(Hl_m & Hlif_m & HnS_m)".
        iDestruct "HnS_m" as (γ_em' γ_cm' γ_bm' γ_qm' γ_cirm' es' Im Rm) 
                      "(HnS_ghm & HnS_fracm & HnS_sim & HnS_FPm 
                                & HnS_clm & HnS_ocm & HnS_Hm & HnS_starm & Hφm)".
        iPoseProof (ghost_heap_sync with "[$HnP_ghm] [$HnS_ghm]") 
                                  as "(% & % & % & % & %)".
        subst γ_em'. subst γ_cm'. subst γ_bm'. subst γ_qm'. subst γ_cirm'.
        iPoseProof (frac_eq with "[$HnP_fracm] [$HnS_fracm]") as "%".
        destruct H1 as [Hes [Hc [Hb Hq]]]. 
        subst es'. subst Cm''. subst Bm''. subst Qm''.

        iAssert (⌜bn = true⌝)%I as "%".
        { destruct bn; try done.
          iDestruct "Hlif_n" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r n) with "[$]") as "%".
          contradiction. } subst bn.
                
        iAssert (⌜bm = true⌝)%I as "%".
        { destruct bm; try done.
          iDestruct "Hlif_m" as 
              (γ_er' γ_cr' γ_br' γ_qr' γ_cirr' es' T'')"(node' & _)".
          iPoseProof ((node_sep_star r m) with "[$]") as "%".
          contradiction. } subst bm.

        iAssert (nodePred_aux γ_gh γ_t γ_s lc r n Cn Bn Qn 
                                          γ_en γ_cn γ_bn γ_qn γ_cirn esn T)%I
                   with "[HnP_gh HnP_frac HnP_C HnP_t]" as "HnP_aux".
        { iFrame. }           

        iAssert (nodePred_aux γ_gh γ_t γ_s lc r m Cm Bm Qm 
                                          γ_em γ_cm γ_bm γ_qm γ_cirm esm Tm)%I
                   with "[HnP_ghm HnP_fracm HnP_Cm HnP_tm]" as "HnP_auxm".
        { iFrame. }
        
        iAssert (nodeShared γ_I γ_R γ_f γ_gh r n Cn Bn Qn H T')%I
                  with "[HnS_gh HnS_frac HnS_si HnS_FP HnS_cl 
                    HnS_oc HnS_H HnS_star Hφ]" as "HnS_n".
        { iExists γ_en, γ_cn, γ_bn, γ_qn, γ_cirn, esn, In, Rn. iFrame. }
                              
        iAssert (nodeShared γ_I γ_R γ_f γ_gh r m Cm Bm Qm H T')%I
                  with "[HnS_ghm HnS_fracm HnS_sim HnS_FPm HnS_clm 
                    HnS_ocm HnS_Hm HnS_starm Hφm]" as "HnS_m".
        { iExists γ_em, γ_cm, γ_bm, γ_qm, γ_cirm, esm, Im, Rm. iFrame. }
        
        iMod (mergeContents_ghost_update with 
                "[] [$node_n $HnP_aux $node_m $HnP_auxm $HnS_n $HnS_m $Hglob]") 
                    as (Qn' Bm') "(HnP_n & HnS_n & HnP_m & HnS_m & Hglob)".
        { iPureIntro; repeat split; try done. }
        
        iModIntro.
        iSplitR "AU HnP_n HnP_m".
        { iNext. iExists T', H, hγ, I, R. iFrame "Hglob".
          rewrite (big_sepS_delete _ (domm I) n); last by eauto.
          iSplitL "Hl_n HnS_n".
          { iExists true, Cn', Bn, Qn'. iFrame "Hl_n".
            iSplitR; try done. }
          rewrite (big_sepS_delete _ (domm I ∖ {[n]}) m); last first.
          clear - m_neq_n m_in_I. set_solver. 
          iFrame "Hstar'". iExists true, Cm', Bm', Qm.
          iFrame "Hl_m Hlif_m". iFrame. }
        iModIntro.
        awp_apply (unlockNode_spec_high with "[] [] 
            [$HnP_n]"); try done.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_"; iModIntro. wp_pures.
        awp_apply (unlockNode_spec_high with "[] [] 
            [$HnP_m]"); try done.
        iAaccIntro with ""; try eauto with iFrame.
        iIntros "_"; iModIntro. wp_pures.
        iApply "IH"; try done.
  Qed.    

End compact_proof.
