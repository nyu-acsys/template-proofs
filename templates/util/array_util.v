(** Code borrowed from Iris/examples repository : https://gitlab.mpi-sws.org/iris/examples/ *)
(** File at /theories/locks/array_based_queuing_lock/abql.v *)

(* All files in this development are distributed under the terms of the 3-clause
BSD license (https://opensource.org/licenses/BSD-3-Clause), included below.

Copyright: Iris developers and contributors

------------------------------------------------------------------------------

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors
      may be used to endorse or promote products derived from this software
      without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

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

