From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export notation locations lang.
From iris.heap_lang Require Import proofmode.
Set Default Proof Using "All".
From flows Require Export flows.

(* Some lemmas for manipulating HeapLang arrays *)

Definition is_array Σ (Hg1 : heapGS Σ) (array : loc) (xs : list Node) : iProp Σ :=
  let vs := (fun n => # (LitLoc n)) <$> xs
  in array ↦∗ vs.

Lemma array_store Σ Hg1 E (i : nat) (v : Node) arr (xs : list Node) :
  {{{ ⌜i < length xs⌝ ∗ ▷ is_array Σ Hg1 arr xs }}}
    #(arr +ₗ i) <- #v @ E 
  {{{ RET #(); is_array Σ Hg1 arr (<[i:=v]>xs) }}}.
Proof.
  iIntros (ϕ) "[% isArr] Post".
  unfold is_array.
  iApply (wp_store_offset with "isArr").
  { apply lookup_lt_is_Some_2. by rewrite fmap_length. }
  rewrite (list_fmap_insert ((λ b : loc, #b) : loc → heap_lang.val) xs i v).
  iAssumption.
Qed.

Lemma array_repeat Σ Hg1 (b : Node) (n : nat) :
  {{{ ⌜0 < n⌝ }}} AllocN #n #b 
  {{{ arr, RET #arr; is_array Σ Hg1 arr (replicate n b) }}}.
Proof.
  iIntros (ϕ ?%inj_lt) "Post".
  iApply wp_allocN; try done.
  iNext. iIntros (l) "[lPts _]".
  iApply "Post".
  unfold is_array.
  rewrite Nat2Z.id.
  rewrite -> fmap_replicate.
  iAssumption.
Qed.

