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
    iIntros (Φ) "HP".
    wp_lam. wp_pures. wp_bind (lockNode _)%E.
    (*  atomic spec for lock *)
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
        (* Sid: note I'm using the commit case because this is the 
           linearization point.
         *)
        iApply (aacc_aupd with "HP"); first done.
        iIntros (u) "Hlock".
        iDestruct "Hlock" as (b') "(Hy & Hifx)".
        destruct (b').
        { (* b' == True *)
          iAaccIntro with "Hy".
          {
            iIntros "Hy". iModIntro. iSplitL.
            iExists true. iFrame.
            eauto with iFrame.
            (* Sid: Help, what's going on here? *)
            admit.
          }
          {
            iIntros "Hy". iModIntro.
            (* Here, pick the second disjunct and prove it to finish the proof. *)
            admit.
          }
        }
        { (* b' == False *)
          (* Sid: we do know y ↦ #true at this point,
             because H' ==> x ↦ v1 if b' = false. That will give us a context
             containing two intances of x ↦ _, contradiction!
           *)
          admit.
        }
  Admitted.
