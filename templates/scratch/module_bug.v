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
    wp_lam. wp_pures. wp_lam.


  Lemma m1_3 : {{{ True }}} m1 m0 #3 {{{ RET #true; True}}}.
  Proof.
    iIntros (Φ) "_ Hpost".
    wp_lam. wp_pures. wp_lam.
  
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
  
  
  
