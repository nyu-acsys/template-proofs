From iris.algebra Require Import excl auth gmap agree gset.
From iris.heap_lang Require Export lifting notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode atomic_heap notation par.
From iris.bi.lib Require Import fractional.
From iris.bi Require Import derived_laws_sbi.
Set Default Proof Using "Type*".

Definition lockNode : val :=
  rec: "lockN" "y" :=
    if: CAS "y" #false #true
    then #()
    else "lockN" "y".

Definition unlockNode : val :=
  λ: "y",
  "y" <- #false.

Definition prog : val := 
  λ: "x" "y" "v",
  lockNode "y";;
  "x" <- "v";;
  unlockNode "y";; "v".

Section Toy_Template.
  Context `{!heapG Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  (* We should be able to prove the following specs: *)

  Lemma lock_spec (y: loc) :
    <<< ∀ (b: bool), y ↦ #b >>>
        lockNode #y @ ⊤
    <<< y ↦ #true ∗ if b then False else True, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". wp_lam.
    wp_bind(CmpXchg _ _ _)%E.
(* ***** This is where I get the error ***** *)
(*     awp_apply (cmpxchg_spec y #false #true). *)
  Admitted.

  Lemma unlock_spec (y: loc) :
    <<< y ↦ #true >>>
        unlockNode #y @ ⊤
    <<< y ↦ #false, RET #() >>>.
  Proof. Admitted.

  Definition is_locked_ref x y v : iProp :=
    (∃ (b: bool), y ↦ #b ∗ if b then True else x ↦ v)%I.

  Lemma prog_spec (x y: loc) (v: val) :
    <<< ∀ (u: val), is_locked_ref x y u >>>
        prog #x #y v @ ⊤
    <<< is_locked_ref x y v, RET #() >>>.
  Proof.
    unfold is_locked_ref.
    iIntros (Φ) "HP". iLöb as "IH".
    wp_lam. wp_pures. wp_bind (lockNode _)%E.
(*  atomic spec for lock  *)
    awp_apply (lock_spec).
(* peeking into the AU *)
    iApply (aacc_aupd_abort with "HP"). done.
    iIntros (v0) "Hislock". 
    iDestruct "Hislock" as (b) "(Hy & Hif)".
    iAaccIntro with "Hy".
(* the atomic lock_spec either aborts or commits, which are the two cases below *)
    - (* abort *)
      iIntros "Hy". iModIntro.
      iSplitL. iExists b. iFrame.
      eauto with iFrame.
    - (* commit, below is the post-condition of lock_spec *)
      iIntros "(Hy & Hif')".
      destruct (b).
      + iExFalso. done.
      + iModIntro.
        (* left-most spatial proposition is giving back the AU, after peeking *)
        iSplitR "Hif". 
        (* here is where we give away y ↦ #true *)
        iExists true. iFrame.
        iIntros "HP". iModIntro.
        wp_pures. wp_store.
        awp_apply (unlock_spec).
        (* need y ↦ #true to open the atomic accessor (AACC thing), but we don't have,
           we can peek into the AU again, but that does not give us y ↦ #true, just y ↦ some b *)
        iApply (aacc_aupd_abort with "HP"). done.
        iIntros (v1) "Hislock".
        iDestruct "Hislock" as (b') "(Hy & H')".
(*  At this point, we need y ↦ #true, but we don't have that information.
    This is because when we apply the lock_spec, we need y ↦ _ for the 
    lock_spec, which we obtain by peeking into the AU. That gives us is_locked_ref
    (and y ↦ _) but we have to give back is_locked_ref after the atomic step. At that point,
    we have y ↦ #true from the post-condition of the lock_spec, but we 
    have to use it to give bakc is_locked_ref. When we have to unlock later,
    we thus does not have y ↦ #true, which is required by the pre-condition
    of unlock_spec. In this scenario, I think what we may work is fractional
    mapping, of the form y ↦{1/2} _. One-half belongs in the spec, the other half in the
    is_locked_ref. The store is allowed only if we have the full ownership, which
    we will by writing appropriate specs for lock and unlock.
    Hope this makes sense, haha!     *)
