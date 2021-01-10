From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export auth_ext general_multicopy.

Section gen_multicopy_util.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !gen_multicopyG Σ}.
  Notation iProp := (iProp Σ).  
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  (** Useful lemmas *)

  Global Instance HnP_t_laterable (r n: Node) γ_t lc T : 
              Laterable (if decide (n = r) 
                         then own γ_t (●{1 / 2} MaxNat T) ∗ clock lc T 
                         else True)%I.
  Proof.
    destruct (decide (n = r)); apply timeless_laterable; apply _.
  Qed.

  Lemma inFP_domm γ_f n D : inFP γ_f n -∗ own γ_f (● D) -∗ ⌜n ∈ D⌝.
  Proof.
    iIntros "FP HD".
    iPoseProof (own_valid_2 _ _ _ with "[$HD] [$FP]") as "H'".
    iDestruct "H'" as %H'.
    apply auth_both_valid_discrete in H'.
    destruct H' as [H' _].
    apply gset_included in H'.
    iPureIntro. set_solver.
  Qed.
  
  Lemma inFP_domm_glob γ_t γ_I γ_J γ_f γ_gh r T H hγ I J n : 
    inFP γ_f n -∗ global_state γ_t γ_I γ_J γ_f γ_gh r T H hγ I J -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "#FP_n Hglob".
    iDestruct "Hglob" as "(Ht & HI & Out_I & HJ 
            & Out_J & Inf_J & Hf & Hγ & FP_r & domm_IJ & domm_Iγ)".
    iPoseProof (inFP_domm with "[$FP_n] [$]") as "%".
    by iPureIntro.
  Qed.
  
  Lemma own_alloc_set (S: gset K): True ==∗ 
          ∃ (γ: gmap K gname), ([∗ set] k ∈ S, own (γ !!! k) (● (MaxNat 0))).
  Proof.
    iIntros "_".
    iInduction S as [| s S] "IH" using set_ind_L.
    - iModIntro. iExists _. try done.
    - iMod (own_alloc (● (MaxNat 0))) as (γs)"H'".
      { rewrite auth_auth_valid. try done. }
      iDestruct "IH" as ">IH".
      iDestruct "IH" as (γ)"IH". 
      iModIntro. iExists (<[s := γs]> γ).
      rewrite (big_sepS_delete _ ({[s]} ∪ S) s); last by set_solver.
      iSplitL "H'". by rewrite lookup_total_insert.
      assert (({[s]} ∪ S) ∖ {[s]} = S) as HS. set_solver.
      rewrite HS. 
      iApply (big_sepS_mono 
                  (λ y, own (γ !!! y) (● {| max_nat_car := 0 |}) )%I
                  (λ y, own (<[s:=γs]> γ !!! y) (● {| max_nat_car := 0 |}))%I
                  S); try done.
      intros k k_in_S. iFrame. iIntros "H'".
      rewrite lookup_total_insert_ne; last by set_solver. 
      done.
      (* No idea what is happening here *) 
      Unshelve. exact (∅: gmap K gname).
  Qed.


  Lemma ghost_heap_sync γ_gh n γ_en γ_cn γ_qn γ_cirn 
                                      γ_en' γ_cn' γ_qn' γ_cirn' : 
    own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_qn γ_cirn]}) 
      -∗ own γ_gh (◯ {[n := ghost_loc γ_en' γ_cn' γ_qn' γ_cirn']}) 
          -∗ ⌜γ_en = γ_en'⌝ ∗ ⌜γ_cn = γ_cn'⌝ 
              ∗ ⌜γ_qn = γ_qn'⌝ ∗ ⌜γ_cirn = γ_cirn'⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1" "H2" as "H".
    iPoseProof (own_valid with "H") as "Valid".
    iDestruct "Valid" as %Valid.
    rewrite auth_frag_valid in Valid *; intros Valid.
    apply singleton_valid in Valid.
    apply to_agree_op_inv in Valid.
    apply leibniz_equiv in Valid.
    inversion Valid.
    by iPureIntro.
  Qed.

  Lemma ghost_heap_update γ_gh (hγ: gmap Node per_node_gl) n 
                                γ_en γ_cn γ_qn γ_cirn :
    ⌜n ∉ dom (gset Node) hγ⌝ -∗ 
          own γ_gh (● hγ) ==∗ 
            own γ_gh (● <[n := ghost_loc γ_en γ_cn γ_qn γ_cirn]> hγ)
          ∗ own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_qn γ_cirn]}).
  Proof.
    iIntros "%". rename H into n_notin_hγ.
    iIntros "Hown". set (<[ n := ghost_loc γ_en γ_cn γ_qn γ_cirn ]> hγ) as hγ'.
    iDestruct (own_update _ _ 
        (● hγ' ⋅ ◯ {[ n := ghost_loc γ_en γ_cn γ_qn γ_cirn ]})
               with "Hown") as "Hown".
    { apply auth_update_alloc. 
      rewrite /hγ'.
      apply alloc_local_update; last done.
      by rewrite <-not_elem_of_dom. }
    iMod (own_op with "Hown") as "[Ht● Ht◯]".
    iModIntro. iFrame.
  Qed.    

  Lemma frac_eq γ_e γ_c γ_q es Cn Qn es' Cn' Qn' : 
              frac_ghost_state γ_e γ_c γ_q es Cn Qn -∗
                  frac_ghost_state γ_e γ_c γ_q es' Cn' Qn' -∗ 
                    ⌜es = es'⌝ ∗ ⌜Cn = Cn'⌝ ∗ ⌜Qn = Qn'⌝.
  Proof.
    iIntros "H1 H2". unfold frac_ghost_state.
    iDestruct "H1" as "(H1_es & H1_c & H1_q)".
    iDestruct "H2" as "(H2_es & H2_c & H2_q)".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_es] [$H2_es]") as "Hes".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_c] [$H2_c]") as "Hc".
    iPoseProof (own_valid_2 _ _ _ with "[$H1_q] [$H2_q]") as "Hq".
    iDestruct "Hes" as %Hes. iDestruct "Hc" as %Hc. iDestruct "Hq" as %Hq.
    apply frac_agree_op_valid in Hes. destruct Hes as [_ Hes].
    apply frac_agree_op_valid in Hc. destruct Hc as [_ Hc].
    apply frac_agree_op_valid in Hq. destruct Hq as [_ Hq].
    apply leibniz_equiv_iff in Hes.
    apply leibniz_equiv_iff in Hc. 
    apply leibniz_equiv_iff in Hq.
    iPureIntro. repeat split; try done.   
  Qed.

  Lemma frac_update γ_e γ_c γ_q es Cn Qn es' Cn' Qn' : 
              frac_ghost_state γ_e γ_c γ_q es Cn Qn ∗ 
                 frac_ghost_state γ_e γ_c γ_q es Cn Qn ==∗ 
                      frac_ghost_state γ_e γ_c γ_q es' Cn' Qn' ∗ 
                        frac_ghost_state γ_e γ_c γ_q es' Cn' Qn'.
  Proof.
    iIntros "(H1 & H2)". 
    iDestruct "H1" as "(H1_es & H1_c & H1_q)".
    iDestruct "H2" as "(H2_es & H2_c & H2_q)".
    iCombine "H1_es H2_es" as "Hes". 
    iEval (rewrite <-frac_agree_op) in "Hes". 
    iEval (rewrite Qp_half_half) in "Hes". 
    iCombine "H1_c H2_c" as "Hc". 
    iEval (rewrite <-frac_agree_op) in "Hc". 
    iEval (rewrite Qp_half_half) in "Hc". 
    iCombine "H1_q H2_q" as "Hq". 
    iEval (rewrite <-frac_agree_op) in "Hq". 
    iEval (rewrite Qp_half_half) in "Hq".
    iMod ((own_update (γ_e) (to_frac_agree 1 es) 
                  (to_frac_agree 1 es')) with "[$Hes]") as "Hes".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hes".
    iEval (rewrite frac_agree_op) in "Hes".  
    iDestruct "Hes" as "(H1_es & H2_es)".            
    iMod ((own_update (γ_c) (to_frac_agree 1 Cn) 
                  (to_frac_agree 1 Cn')) with "[$Hc]") as "Hc".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hc".
    iEval (rewrite frac_agree_op) in "Hc".  
    iDestruct "Hc" as "(H1_c & H2_c)".
    iMod ((own_update (γ_q) (to_frac_agree 1 Qn) 
                  (to_frac_agree 1 Qn')) with "[$Hq]") as "Hq".
    { apply cmra_update_exclusive. 
      unfold valid, cmra_valid. simpl. unfold prod_valid.
      split; simpl; try done. }
    iEval (rewrite <-Qp_half_half) in "Hq".
    iEval (rewrite frac_agree_op) in "Hq".  
    iDestruct "Hq" as "(H1_q & H2_q)".
    iModIntro. iFrame.
  Qed.

  Lemma flowint_update_result (γ: gname) (I I_n I_n': multiset_flowint_ur K) x :
    ⌜flowint_update_P (_) I I_n I_n' x⌝ ∗ own γ x -∗
    ∃ I', ⌜contextualLeq (_) I I'⌝
          ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
          ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (view_auth_proj x); last first.
    - intros Hx. iIntros "(% & ?)". iExFalso. done.
    - intros [q a] Hx.
      iIntros "[HI' Hown]". iDestruct "HI'" as %HI'.
      destruct HI' as [I' HI'].
      destruct HI' as [Hagree [Hq [HIn [Hcontxl HIo]]]].
      iExists I'.
      iSplit. by iPureIntro.
      iSplit. by iPureIntro. destruct x.
      simpl in Hx. simpl in HIn.
      rewrite Hx. rewrite <-HIn.
      rewrite Hq Hagree.
      assert (● I' ⋅ ◯ I_n' = View (Some (1%Qp, to_agree I')) I_n') as H'.
      { rewrite /(● I' ⋅ ◯ I_n'). unfold cmra_op.
        simpl. unfold view_op. simpl.
        assert (ε ⋅ I_n' = I_n') as H'. by rewrite left_id.
        rewrite H'. unfold op, cmra_op. by simpl. }   
      by iEval (rewrite H').
  Qed.

  Lemma flowint_update_result' (γ: gname) (I I_n I_n': multiset_flowint_ur KT) x :
    ⌜flowint_update_P (_) I I_n I_n' x⌝ ∗ own γ x -∗
    ∃ I', ⌜contextualLeq (_) I I'⌝
          ∗ ⌜∃ I_o, I = I_n ⋅ I_o ∧ I' = I_n' ⋅ I_o⌝
          ∗ own γ (● I' ⋅ ◯ I_n').
  Proof.
    unfold flowint_update_P.
    case_eq (view_auth_proj x); last first.
    - intros Hx. iIntros "(% & ?)". iExFalso. done.
    - intros [q a] Hx.
      iIntros "[HI' Hown]". iDestruct "HI'" as %HI'.
      destruct HI' as [I' HI'].
      destruct HI' as [Hagree [Hq [HIn [Hcontxl HIo]]]].
      iExists I'.
      iSplit. by iPureIntro.
      iSplit. by iPureIntro. destruct x.
      simpl in Hx. simpl in HIn.
      rewrite Hx. rewrite <-HIn.
      rewrite Hq Hagree.
      assert (● I' ⋅ ◯ I_n' = View (Some (1%Qp, to_agree I')) I_n') as H'.
      { rewrite /(● I' ⋅ ◯ I_n'). unfold cmra_op.
        simpl. unfold view_op. simpl.
        assert (ε ⋅ I_n' = I_n') as H'. by rewrite left_id.
        rewrite H'. unfold op, cmra_op. by simpl. }   
      by iEval (rewrite H').
  Qed.    

  Lemma dom_lookup (C: gmap K nat) k :
        C !! k ≠ None → k ∈ dom (gset K) C.
  Proof.
    intros Hcn. destruct (C !! k) eqn: Hcnk.
    rewrite elem_of_dom. rewrite Hcnk.
    by exists n. done.
  Qed.
  
  Definition map_subset (S: gset K) (C: gmap K nat) :=
              let f := λ a s', s' ∪ {[(a, C !!! a)]} in
                        set_fold f (∅: gset KT) S.          

  Definition map_restriction (S: gset K) (C: gmap K nat) := 
              let f := λ a m, <[a := C !!! a ]> m in
                        set_fold f (∅: gmap K nat) S.
                        
  
  Lemma lookup_map_restriction S (C: gmap K nat) (k: K):
              k ∈ S → map_restriction S C !! k = Some (C !!! k).
  Proof.
    set (P := λ (m: gmap K nat) (X: gset K),
                    ∀ x, x ∈ X → m !! x = Some (C !!! x)).
    apply (set_fold_ind_L P); try done.
    intros x X r Hx HP.
    unfold P in HP. unfold P.
    intros x' Hx'.
    destruct (decide (x' = x)).
    - subst x'. by rewrite lookup_insert.
    - assert (x' ∈ X) as x'_in_X. set_solver.
      rewrite lookup_insert_ne. apply HP.
      done. done.
  Qed.

  Lemma map_subset_member S C k t:
              (k, t) ∈ map_subset S C ↔ k ∈ S ∧ t = C !!! k.
  Proof.
    set (P := λ (m: gset KT) (X: gset K),
                    ∀ kx tx, (kx, tx) ∈ m ↔ kx ∈ X ∧ tx = C !!! kx).
    apply (set_fold_ind_L P); try done.
    - unfold P. intros kx tx. set_solver.
    - intros x X r Hx HP. unfold P.
      unfold P in HP. intros kx' tx'.
      split.
      + intros Hktx. rewrite elem_of_union in Hktx*; intros Hktx.
        destruct Hktx as [H' | H'].
        * apply HP in H'. destruct H' as [H' H''].
          split; try done. set_solver.
        * rewrite elem_of_singleton in H'*; intros H'.
          inversion H'. split; try done; set_solver.
      + intros [H' H'']. rewrite elem_of_union in H'*; intros H'.
        destruct H' as [H' | H'].
        rewrite elem_of_singleton in H'*; intros H'.
        rewrite H'. rewrite H''. set_solver.
        assert ((kx', tx') ∈ r) as Hkt.
        apply HP. split; try done.
        set_solver.       
  Qed.              

  Lemma map_restriction_dom S C :
              dom (gset K) (map_restriction S C) = S.
  Proof.
    set (P := λ (m: gmap K nat) (X: gset K), dom (gset K) m = X).
    apply (set_fold_ind_L P); try done.
    - unfold P; set_solver. 
    - intros x X r Hx HP. unfold P. unfold P in HP. 
      apply leibniz_equiv. rewrite dom_insert.
      rewrite HP. done.
  Qed.            

  Lemma map_of_set_lookup_some_aux (H: gset KT) k :
          (∀ t, (k,t) ∉ H) ∨ (∃ T, (k, T) ∈ H ∧ (∀ t', (k,t') ∈ H → t' ≤ T)).
  Proof.
    set (P := λ (X: gset KT), (∀ t, (k,t) ∉ X) ∨ 
                  (∃ T, (k, T) ∈ X ∧ (∀ t', (k,t') ∈ X → t' ≤ T))).
    apply (set_ind_L P); try done.
    - unfold P. left. intros t. set_solver.
    - intros [k' t'] X Hkt HP. subst P.
      simpl in HP. simpl. destruct (decide (k' = k)).
      + subst k'. destruct HP as [H' | H'].
        * right. exists t'. split.
          set_solver. intros t. destruct (decide (t' = t)).
          subst t'. intros; done.
          intros H''. assert ((k,t) ∈ X).
          set_solver. pose proof H' t as H'.
          done.
        * right. destruct H' as [T H']. 
          destruct (decide (t' < T)).
          ** exists T. split.
             destruct H' as [H' _].
             set_solver. intros t Hkt'.
             rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia. 
             destruct H' as [_ H'']. apply H''; try done.
          ** exists t'. split. set_solver.
             intros t Hkt'. rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia.
             destruct H' as [_ H'']. 
             apply (Nat.le_trans _ T _); try lia.
             apply H''. try done.
      + destruct HP as [H' | H'].
        * left. intros t. set_solver.
        * right. destruct H' as [T H'].
          exists T. destruct H' as [H' H''].
          split. set_solver. intros t.
          intros Hkt'. rewrite elem_of_union in Hkt'*; intros Hkt'.
          destruct Hkt' as [Hkt' | Hkt'].
          rewrite elem_of_singleton in Hkt'*; intros Hkt'.
          inversion Hkt'. done. apply H''; try done.
  Qed.

  Lemma map_of_set_lookup_some (H: gset KT) k t :
              (k, t) ∈ H → is_Some(map_of_set H !! k).
  Proof.
    intros Hkt.
    pose proof map_of_set_lookup_some_aux H k as Hkt'.
    destruct Hkt' as [Hkt' | Hkt'].
    { pose proof Hkt' t as H'. set_solver. }
    pose proof (map_of_set_lookup_cases H k) as H'.
    destruct H' as [H' | H'].
    - destruct H' as [T' H'].
      destruct H' as [_ [_ H']].
      rewrite H'. by exists T'.
    - destruct Hkt' as [T Hkt'].
      destruct Hkt' as [Hkt' _].
      destruct H' as [H' _].
      pose proof H' T as H'.
      set_solver.   
  Qed.
  
  Lemma map_of_set_lookup_lb H k t :
    (k,t) ∈ H → t ≤ map_of_set H !!! k.
  Proof.
    intros kt_in_H.
    pose proof map_of_set_lookup_cases H k as [H' | H'].
    - destruct H' as [T [kT_in_H [H' H_k]]].
      rewrite lookup_total_alt. rewrite H_k.
      simpl. apply H'; try done.
    - destruct H' as [H' _].
      pose proof H' t as H'.
      contradiction.  
  Qed.   

  Lemma set_of_map_member_ne (C: gmap K nat) k :
            C !! k = None →    
              ∀ t, (k, t) ∉ set_of_map C.
  Proof.
    set (P := λ (s: gset KT) (m: gmap K nat), 
                   m !! k = None → ∀ t, (k, t) ∉ s). 
    apply (map_fold_ind P); try done.
    intros kx tx m r Hm HP. unfold P.
    unfold P in HP. destruct (decide (kx = k)).
    - subst kx. rewrite lookup_insert. try done.
    - rewrite lookup_insert_ne; try done. 
      intros Hm'. pose proof HP Hm' as HP. 
      intros t. intros Hnot. 
      rewrite elem_of_union in Hnot*; intros Hnot.
      destruct Hnot as [Hnot | Hnot].
      + by apply HP in Hnot.
      + rewrite elem_of_singleton in Hnot*; intros Hnot.
        inversion Hnot. try done.
  Qed.

  Lemma set_of_map_member (C: gmap K nat) k t :
            C !! k = Some(t) →    
              (k, t) ∈ set_of_map C.
  Proof.
    intros Hc. unfold set_of_map.
    set (P := λ (s: gset KT) (m: gmap K nat), 
                  ∀ j x, m !! j = Some x → (j,x) ∈ s). 
    apply (map_fold_ind P); try done.
    intros i x m s Hmi Hp. unfold P.
    intros j x'. destruct (decide (i = j)).
    - replace j. rewrite lookup_insert. 
      intros H'; inversion H'. set_solver.
    - rewrite lookup_insert_ne; try done.
      pose proof Hp j x' as Hp'. set_solver.
  Qed.

  Lemma set_of_map_member_rev (C: gmap K nat) k t :
            (k, t) ∈ set_of_map C → 
                C !! k = Some(t).
  Proof.
    set (P := λ (s: gset KT) (m: gmap K nat), 
                  ∀ j x, (j,x) ∈ s → m !! j = Some x).
    apply (map_fold_ind P); try done.
    intros i x m r Hmi Hp. unfold P.
    intros j x'. destruct (decide (i = j)).
    - replace j. rewrite lookup_insert.
      rewrite elem_of_union. intros [Hr | Hr].
      unfold P in Hp. pose proof Hp i x' Hr as Hp.
      rewrite Hp in Hmi. inversion Hmi.
      assert (x = x') by set_solver. by replace x.              
    - intros H'. assert ((j,x') ∈ r) as Hj by set_solver.
      pose proof Hp j x' Hj as Hp.
      rewrite lookup_insert_ne; try done.
  Qed.

  Lemma set_of_map_insert_subseteq (C: gmap K nat) k t :
         set_of_map (<[k := t]> C) ⊆ set_of_map C ∪ {[(k, t)]}.
  Proof.
    intros [k' t'] Hkt. destruct (decide (k' = k)).
    - replace k'. rewrite e in Hkt. 
      apply set_of_map_member_rev in Hkt.
      rewrite lookup_insert in Hkt.
      inversion Hkt. set_solver.
    - apply set_of_map_member_rev in Hkt.
      rewrite lookup_insert_ne in Hkt; try done.
      apply set_of_map_member in Hkt.
      set_solver.  
  Qed.          

  Lemma nodePred_nodeShared_eq γ_I γ_J γ_f γ_gh r n 
                               γ_en γ_cn γ_qn γ_cirn
                               γ_en' γ_cn' γ_qn' γ_cirn'
                               es Cn Qn es' Cn' Qn'
                               Bn In Jn H :
        own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_qn γ_cirn]}) -∗
          frac_ghost_state γ_en γ_cn γ_qn es Cn Qn -∗
            nodeShared' γ_I γ_J γ_f γ_gh r n Cn' Qn' H 
                        γ_en' γ_cn' γ_qn' γ_cirn' es' Bn In Jn -∗
              frac_ghost_state γ_en γ_cn γ_qn es Cn Qn
              ∗ nodeShared' γ_I γ_J γ_f γ_gh r n Cn Qn H 
                          γ_en γ_cn γ_qn γ_cirn es Bn In Jn
              ∗ ⌜es' = es⌝ ∗ ⌜Cn' = Cn⌝  ∗ ⌜Qn' = Qn⌝.
  Proof.
    iIntros "HnP_gh HnP_frac HnS".
    iDestruct "HnS" as "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                        & HnS_cl & HnS_oc & HnS_Bn & HnS_H  & HnS_star & Hφ)".
    iPoseProof (ghost_heap_sync with "[$HnP_gh] [$HnS_gh]") 
                              as "(% & % & % & %)".
    subst γ_en'. subst γ_cn'. subst γ_qn'. subst γ_cirn'.
    iPoseProof (frac_eq with "[$HnP_frac] [$HnS_frac]") as "%".
    destruct H0 as [Hes [Hc Hq]]. 
    subst es'. subst Cn'. subst Qn'.
    iFrame. by iPureIntro.
  Qed.                                        
  
  (** Lock module **)

(*  
  Parameter getLockLoc_spec : ∀ (n: Node),
    ⊢ ({{{ True }}}
        general_multicopy.getLockLoc #n
       {{{ (l:loc), RET #l; ⌜general_multicopy.lockLoc n = l⌝ }}})%I.
         
  Lemma lockNode_spec (n: Node):
    ⊢ <<< ∀ (b: bool), (general_multicopy.lockLoc n) ↦ #b >>>
      lockNode #n    @ ⊤
    <<< (general_multicopy.lockLoc n) ↦ #true ∗ ⌜b = false⌝ , RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_bind(general_multicopy.getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "#Hl". wp_let. wp_bind (CmpXchg _ _ _)%E.
    iMod "AU" as (b) "[Hb HAU]". iDestruct "Hl" as %Hl.
    iEval (rewrite Hl) in "Hb". destruct b.
    - wp_cmpxchg_fail. iDestruct "HAU" as "[HAU _]".
      iEval (rewrite Hl) in "HAU".
      iMod ("HAU" with "Hb") as "H".
      iModIntro. wp_pures. iApply "IH".
      iEval (rewrite <-Hl) in "H". done.
    - wp_cmpxchg_suc. iDestruct "HAU" as "[_ HAU]".
      iEval (rewrite Hl) in "HAU".
      iMod ("HAU" with "[Hb]") as "HΦ". iFrame; done.
      iModIntro. wp_pures. done.
  Qed.
*)
  Lemma lockNode_spec_high N γ_te γ_he γ_s γ_fr γ_t γ_I γ_J γ_f γ_gh lc r n:
    ⊢ mcs_inv N γ_te γ_he γ_s γ_fr (mcs_conc γ_s γ_t γ_I γ_J γ_f γ_gh lc r) -∗
        inFP γ_f n -∗
              <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ Cn Qn, nodePred γ_gh γ_t γ_s lc r n Cn Qn, RET #() >>>.
  Proof.
    iIntros "#mcsInv #FP_n".
    iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iInv "mcsInv" as ">mcs". 
    iDestruct "mcs" as (T H) "(mcs_high & mcs_conc)".
    iDestruct "mcs_conc" as (hγ I J) "(Hglob & Hstar)".
    iPoseProof (inFP_domm_glob with "[$FP_n] [$Hglob]") as "%". 
    rename H0 into n_in_I.
    iEval (rewrite (big_sepS_elem_of_acc (_) (domm I) n); 
           last by eauto) in "Hstar".
    iDestruct "Hstar" as "(Hn & Hstar')".
    iDestruct "Hn" as (b Cn Qn) "(HlockR & Hns)".
    iAaccIntro with "HlockR".
    { iIntros "HlockRn". iModIntro.
      iSplitR "AU".
      { iExists T, H. iNext. iFrame.
        iExists hγ, I, J. iFrame.
        iPoseProof ("Hstar'" with "[-]") as "Hstar".
        iExists b, Cn, Qn. iFrame.
        iFrame.
      }
      iFrame.
    }
    iIntros "(HlockRn & Hnp)".
    iMod "AU" as "[_ [_ Hclose]]".
    iMod ("Hclose" with "[Hnp]") as "HΦ"; try done.
    iModIntro. iSplitR "HΦ".
    iNext. iExists T, H. iFrame.
    iExists hγ, I, J. iFrame.
    iPoseProof ("Hstar'" with "[HlockRn Hns]") as "Hstar".
    iExists true, Cn, Qn. iFrame.
    iFrame. done.
  Qed.

(*
  Lemma unlockNode_spec (n: Node) :
    ⊢ <<< general_multicopy.lockLoc n ↦ #true >>>
      unlockNode #n    @ ⊤
    <<< general_multicopy.lockLoc n ↦ #false, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". wp_lam. 
    wp_bind(general_multicopy.getLockLoc _)%E.
    wp_apply getLockLoc_spec; first done.
    iIntros (l) "#Hl". wp_let.
    iMod "AU" as "[Hy [_ Hclose]]".
    iDestruct "Hl" as %Hl.
    iEval (rewrite Hl) in "Hy".
    wp_store. iEval (rewrite Hl) in "Hclose".
    iMod ("Hclose" with "Hy") as "HΦ".
    iModIntro. done.
  Qed.
  
  Lemma int_domm γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh r t H hγ I J n In :
    own γ_I (◯ In) -∗ ⌜domm In = {[n]}⌝
    -∗ global_state γ_te γ_he γ_s γ_t γ_I γ_J γ_f γ_gh r t H hγ I J
    -∗ ⌜n ∈ domm I⌝.
  Proof.
    iIntros "Hi Dom_In Hglob".
    iDestruct "Dom_In" as %Dom_In.
    iDestruct "Hglob" as "(MCS_auth & HH & Hist & Ht & HI & Out_I & HJ 
            & Out_J & Inf_J & Hf & Hγ & FP_r & Max_ts & domm_IJ & domm_Iγ)".
    iPoseProof ((auth_own_incl γ_I (I) (In)) with "[$]") as "%".
    rename H0 into I_incl. destruct I_incl as [Io I_incl].
    iPoseProof (own_valid with "HI") as "%". rename H0 into Valid_I.
    iPureIntro. rewrite I_incl. rewrite flowint_comp_fp.
    rewrite Dom_In. set_solver. rewrite <- I_incl.
    by apply auth_auth_valid.
  Qed.
*)
  Lemma nodePred_lockR_true γ_gh γ_t γ_s lc r bn n es Cn Cn' Qn' : 
    node r n es Cn -∗ 
      lockR bn n (nodePred γ_gh γ_t γ_s lc r n Cn' Qn') -∗
        ⌜bn = true⌝.
  Proof.
    iIntros "node Hl_n".
    destruct bn; try done.
    iDestruct "Hl_n" as "(Hl & HnP')".
    iDestruct "HnP'" as (? ? ? ? ? ?) "(n' & _)".
    iExFalso. iApply (node_sep_star r n). iFrame.
  Qed.          

  Lemma lockR_true Cn' Qn' γ_gh γ_t γ_s lc r n Cn Qn:
    lockR true n (nodePred γ_gh γ_t γ_s lc r n Cn Qn) -∗
      lockR true n (nodePred γ_gh γ_t γ_s lc r n Cn' Qn').
  Proof.
    iIntros "(Hl & _)". iFrame.
  Qed.       

  Lemma unlockNode_spec_high N γ_te γ_he γ_s γ_fr γ_t γ_I γ_J γ_f γ_gh lc r 
                                                          n Cn Qn:
    ⊢ mcs_inv N γ_te γ_he γ_s γ_fr (mcs_conc γ_s γ_t γ_I γ_J γ_f γ_gh lc r) -∗
        inFP γ_f n -∗ nodePred γ_gh γ_t γ_s lc r n Cn Qn -∗
              <<< True >>>
                unlockNode #n    @ ⊤ ∖ ↑(mcsN N)
              <<< True, RET #() >>>.
  Proof.
    iIntros "#mcsInv #FP_n Hnp". iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iInv "mcsInv" as ">mcs".
    iDestruct "mcs" as (T H) "(mcs_high & mcs_conc)".
    iDestruct "mcs_conc" as (hγ I J) "(Hglob & Hstar)".
    iPoseProof (inFP_domm_glob with "[$FP_n] [$Hglob]") as "%". 
    rename H0 into n_in_I.
    iEval (rewrite (big_sepS_elem_of_acc (_) (domm I) n); 
           last by eauto) in "Hstar".
    iDestruct "Hstar" as "(Hn & Hstar')".
    iDestruct "Hn" as (b Cn' Qn') "(HlockR & Hns)".
    iAssert (lockR true n (nodePred γ_gh γ_t γ_s lc r n Cn Qn) 
              ∗ (nodePred γ_gh γ_t γ_s lc r n Cn Qn))%I
      with "[HlockR Hnp]" as "HlockR".
    {
      destruct b eqn: Hb.
    - (* Case n locked *)
      iFrame "∗".
    - (* Case n unlocked: impossible *)
      iDestruct "Hnp" as (? ? ? ? ? ?)"(node & _)".
      iPoseProof (nodePred_lockR_true with "[$node] [$HlockR]") as "H'".
      iDestruct "H'" as %H'; inversion H'.
    }
    iAaccIntro with "HlockR".
    { iIntros "(HlockR & Hnp)". iModIntro.
      iSplitR "Hnp AU".
      iExists T, H. iNext. iFrame.
      iExists hγ, I, J. iFrame.
      iPoseProof ("Hstar'" with "[HlockR Hns]") as "Hstar".
      iExists true, Cn', Qn'. iFrame.
      iFrame. iFrame. 
    }
    iIntros "HlockR".
    iMod "AU" as "[_ [_ Hclose]]".
    iMod ("Hclose" with "[]") as "HΦ"; try done.
    iModIntro. iSplitR "HΦ".
    iNext. iExists T, H. iFrame.
    iExists hγ, I, J. iFrame.
    iPoseProof ("Hstar'" with "[HlockR Hns]") as "Hstar".
    iExists false, Cn, Qn.
    iAssert (lockR false n (nodePred γ_gh γ_t γ_s lc r n Cn Qn)
                      ∗ nodeShared γ_I γ_J γ_f γ_gh r n Cn Qn H)%I
      with "[Hns HlockR]" as "(HlockR & Hns)".
    {
      iDestruct "HlockR" as "(Hl & Hnp)".
      iDestruct "Hnp" as (γ_en γ_cn γ_qn γ_cirn esn T')
                             "(node_n & #HnP_gh & HnP_frac & HnP_C & HnP_t)".
      iDestruct "Hns" as (γ_en' γ_cn' γ_qn' γ_cirn' es' Bn' In0 Jn0) "Hns'".
      iPoseProof (nodePred_nodeShared_eq with "[$HnP_gh] [$HnP_frac] [$Hns']")
         as "(HnP_frac & Hns' & % & % & %)".
      iSplitR "Hns'".                          
      - iFrame. iExists γ_en, γ_cn, γ_qn, γ_cirn, esn, T'.
        iFrame "∗#".
      - iExists γ_en, γ_cn, γ_qn, γ_cirn, esn, Bn', In0, Jn0.
        iFrame.
    }
    iFrame. iFrame. iFrame.
  Qed.

End gen_multicopy_util.