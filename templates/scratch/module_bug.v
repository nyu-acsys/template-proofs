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

Module M_ZERO.
  Parameter test1 : val.

End M_ZERO.

Module M_ONE.
  Import M_ZERO.
  
  Definition test2 : val :=
    λ: "r",
      test1 "r".

  Definition m0 : val :=
    rec: "m0r" "m1r" "v" :=
      if: "v" = #0 then
        #true
      else
        "m1r" ("v" - #1).
  
  Definition m1 : val :=
    rec: "m1r" "m0r" "v" :=
      if: "v" = #0 then
        #false
      else
        "m0r" ("v" - #1).
  
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma m0_spec : ∀ (v: nat), 
    {{{ True }}} m0 m1 #v {{{ b, RET #b; ⌜Nat.even v = b⌝ }}}.
  Proof.
    iIntros (v Φ) "_ Hpost".
    wp_lam. wp_pures.
  Admitted.


  Lemma m1_3 : {{{ True }}} m1 m0 #3 {{{ RET #true; True}}}.
  Proof.
    iIntros (Φ) "_ Hpost".
    wp_lam. wp_pures. wp_lam.
  Admitted.
  
  Parameter test1_spec: ∀ (r: nat),
    {{{ True }}} test1 #r {{{ l, RET #l; l ↦ #0 }}}.

End M_ONE.

Module M_TWO.
  Import M_ONE.
  

  Lemma test2_spec: ∀ (r: nat),
    {{{ True }}} test2 #r {{{ l, RET #l; l ↦ #0 }}}.
  Proof.
    intros r. iIntros (Φ) "_ Hpost".
    wp_lam. wp_apply test1_spec; try done.
  Qed.

End M_TWO.
  
Module M_THREE.

  Definition test : val :=
    rec: "tr" "p" :=
      let: "b" := nondet_bool #() in
      resolve_proph: "p" to: "b";;
      if: "b" then
        #()
      else
        "tr" "p".

  Definition test2 : val :=
    rec: "tr" "l" :=
      let: "b" := nondet_bool #() in
      if: "b" then
        let: "v" := ! "l" in
        "v"
      else
        FAA "l" #1;;
        "tr" "l".

  Context `{!heapGS Σ}.

  Lemma test_spec1 (l : loc) (v: Z):
    ⊢ {{{ l ↦ #v }}} test2 #l
      {{{ (v': Z), RET #v'; l ↦ #v' ∗ ⌜(v ≤ v')%Z⌝ }}}. 
  Proof.
    iLöb as "IH" forall (v). iIntros  (Φ) "!# Hl Hpost". wp_lam. 
    wp_apply nondet_bool_spec; try done. iIntros (b)"_". wp_pures.
    destruct b; wp_pures.
    - wp_load. wp_pures. iApply "Hpost". iFrame. by iPureIntro.
    - wp_faa. wp_pures. iApply ("IH" with "[Hl]"); try done.
      iNext. iIntros (v')"(Hl&%)".
      iApply "Hpost". iFrame "∗". iPureIntro; lia.
  Qed.

  Lemma test_spec2 (l : loc) (v: Z):
    ⊢ l ↦ #v -∗ 
      <<{ ∀∀ [_: ()], True }>> test2 #l @ ⊤
      <<{ ∃∃ [_: ()], True | (v': Z), RET #v'; l ↦ #v' ∗ ⌜(v ≤ v')%Z⌝ }>>. 
  Proof.
    iLöb as "IH" forall (v). iIntros "Hl" (Φ) "AU". wp_lam. 
    wp_apply nondet_bool_spec; try done. iIntros (b)"_". wp_pures.
    destruct b; wp_pures.
    - wp_load. wp_pures. iMod "AU" as (_)"[_ [_ H']]". iSpecialize ("H'" $! _).
      iMod ("H'" with "[]") as "Hpost"; try done. 
      iApply "Hpost". iFrame. by iPureIntro.
    - wp_faa. wp_pures. iApply ("IH" with "[Hl]"); try done.
      (* Stuck *)
  Admitted.


  Lemma test_spec1 (p: proph_id) pvs:
    ⊢ {{{ proph p pvs }}} test #p
      {{{ prf pvs', RET #(); proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝ }}}. 
  Proof.
    iLöb as "IH" forall (pvs). iIntros  (Φ) "!# Hproph Hpost". wp_lam. 
    wp_apply nondet_bool_spec; try done. iIntros (b)"_". wp_pures.
    wp_apply (wp_resolve with "[$Hproph]"). try done.
    wp_pures. iModIntro. iIntros (pvs') "%Hpvs' Hproph".
    wp_pures. destruct b; wp_pures.
    - iApply ("Hpost" $! [(#(), #true)]). iFrame. iPureIntro. set_solver.
    - iApply ("IH" with "[$Hproph]"). iNext.
      iIntros (prf' pvs'') "(Hproph & %Hpvs'')". 
      iApply ("Hpost" $! ((#(), #false) :: prf')). iFrame.
      iPureIntro. rewrite Hpvs' Hpvs''. set_solver.
  Qed.

  Lemma test_spec2 (p: proph_id) pvs:
    ⊢ proph p pvs -∗
      <<{ ∀∀ [_: ()], True }>> test #p @ ⊤
      <<{ ∃∃ [_: ()], True | 
          prf pvs', RET #(); proph p pvs' ∗ ⌜pvs = prf ++ pvs'⌝}>>. 
  Proof.
    iLöb as "IH" forall (pvs). iIntros "Hproph" (Φ) "AU". wp_lam. 
    wp_apply nondet_bool_spec; try done. iIntros (b)"_". wp_pures.
    wp_apply (wp_resolve with "[$Hproph]"). try done.
    wp_pures. iModIntro. iIntros (pvs') "%Hpvs' Hproph".
    wp_pures. destruct b; wp_pures.
    - iMod "AU" as (_)"[_ [_ H']]".
      iSpecialize ("H'" $! ()).
      iMod ("H'" with "[]") as "Hpost"; try done.
      iApply ("Hpost" $! [(#(), #true)]). iFrame. iPureIntro. set_solver.
    - iApply ("IH" with "[$Hproph]"). iNext.
      iIntros (prf' pvs'') "(Hproph & %Hpvs'')". 
      iApply ("Hpost" $! ((#(), #false) :: prf')). iFrame.
      iPureIntro. rewrite Hpvs' Hpvs''. set_solver.
  Qed.
  
End M_THREE.  
  
