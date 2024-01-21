From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import dfrac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
From iris.bi.lib Require Import fractional.
From flows Require Import array_util misc_ra gset_seq.

(* Module for the node interface *)
(* Includes node predicate and helper function specs *)

Module Type NODE_IMPL.

  Parameter L : nat. (* Maximum Height *)
  Parameter W : nat. (* Keyspace *)
  Parameter W_gt_0 : 0 < W.
  Parameter L_gt_1 : 1 < L.

  Definition MarkT := gmap nat bool.
  Definition NextT := gmap nat Node.

  Parameter node : ∀ Σ, heapGS Σ → Node → nat → MarkT → NextT → nat → iProp Σ.
  #[global] Declare Instance node_timeless_proof : ∀ Σ Hg1 n h mark next k, 
    Timeless (node Σ Hg1 n h mark next k).

  Parameter node_sep_star: ∀ Σ Hg1 n h mark next k h' mark' next' k',
    node Σ Hg1 n h mark next k -∗ node Σ Hg1 n h' mark' next' k' -∗ False.

  Parameter findNext : val.
  Parameter changeNext : val.
  Parameter changeNext' : val.
  Parameter markNode : val.
  Parameter markNode' : val.
  Parameter getKey : val.
  Parameter createNode : val.
  Parameter getHeight : val.
  Parameter createTail : val.
  Parameter createHead : val.

  Parameter createTail_spec : ∀ Σ Hg1,
  ⊢  {{{ True }}}
        createTail #()
      {{{ (tl: Node) mark,
        RET #tl;
          node Σ Hg1 tl L mark ∅ W
        ∗ ⌜dom mark = gset_seq 0 (L-1)⌝
        ∗ (⌜∀ i, i < L → mark !! i = Some false⌝) }}}.

  Parameter createHead_spec : ∀ Σ Hg1 (tl : Node),
  ⊢  {{{ True }}}
        createHead #tl
      {{{ (hd: Node) mark next,
          RET #hd;
            node Σ Hg1 hd L mark next 0
          ∗ ⌜dom mark = gset_seq 0 (L-1)⌝ ∗ ⌜dom next = gset_seq 0 (L-1)⌝
          ∗ (⌜∀ i, i < L → mark !! i = Some false⌝)
          ∗ (⌜∀ i, i < L → next !! i = Some tl⌝) }}}.

  Parameter createNode_spec : ∀ Σ Hg1 (succs: loc) ss (k h: nat),
  ⊢  {{{ is_array Σ _ succs ss ∗ ⌜length ss = L⌝ ∗ ⌜0 < h < L⌝ }}}
           createNode #k #h #succs
        {{{ (n: Node) mark next,
            RET #n;
              is_array Σ _ succs ss
            ∗ node Σ Hg1 n h mark next k
            ∗ ⌜dom mark = gset_seq 0 (h-1)⌝ ∗ ⌜dom next = gset_seq 0 (h-1)⌝
            ∗ (⌜∀ i, i < h → mark !! i = Some false⌝)
            ∗ (⌜∀ i, i < h → next !! i = Some (ss !!! i)⌝) }}}.

  Parameter findNext_spec : ∀ Σ Hg1 (n: Node) (i: nat),
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜i < h⌝ }>>
          findNext #n #i @ ∅
      <<{ ∃∃ (m: bool) (n': Node),
              node Σ Hg1 n h mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !!! i = n'⌝ |
              RET (#m, #n') }>>.

  Parameter changeNext_spec : ∀ Σ Hg1 (n m m': Node) (i: nat),
    ⊢  <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜i < h⌝ }>>
            changeNext #n #m #m' #i @ ∅
      <<{ ∃∃ (success: bool) next',
              node Σ Hg1 n h mark next' k
            ∗ (match success with true => ⌜next !!! i = m 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := m']> next⌝
                                | false => ⌜(next !!! i ≠ m ∨ 
                                              mark !!! i = true)
                                            ∧ next' = next⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end) }>>.

  Parameter changeNext_proph_spec : ∀ Σ Hg1 (n m m': Node) (p: proph_id) pvs,
    ⊢ proph p pvs -∗
      <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜0 < h⌝ }>>
            changeNext' #n #m #m' #p @ ∅
      <<{ ∃∃ (success: bool) next' prf pvs',
              node Σ Hg1 n h mark next' k
            ∗ proph p pvs'
            ∗ ⌜Forall (λ x, ∃ v1, x = ((v1, #false)%V, #())) prf⌝
            ∗ (match success with 
                true => ⌜next !!! 0 = m 
                        ∧ mark !!! 0 = false
                        ∧ next' = <[0 := m']> next
                        ∧ (∃ v1, pvs = prf ++ [((v1, #true)%V, #())] ++ pvs')⌝
              | false => ⌜(next !!! 0 ≠ m ∨ mark !!! 0 = true)
                          ∧ next' = next
                          ∧ pvs = prf ++ pvs'⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end) }>>.

  Parameter getKey_spec : ∀ Σ Hg1 (n: Node),
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k }>>
           getKey #n @ ∅
     <<{ node Σ Hg1 n h mark next k | RET #k }>>.

  Parameter markNode_spec : ∀ Σ Hg1 (n: Node) (i: nat),
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜i < h⌝ }>>
            markNode #n #i @ ∅
      <<{ ∃∃ (success: bool) mark',
              node Σ Hg1 n h mark' next k
            ∗ (match success with true => ⌜mark !!! i = false
                                            ∧ mark' = <[i := true]> mark⌝
                                | false => ⌜mark !!! i = true
                                            ∧ mark' = mark⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  }>>.

  
  Parameter markNode_proph_spec : ∀ Σ Hg1 (n: Node) (p: proph_id) pvs,
  ⊢ proph p pvs -∗ 
    <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k ∗ ⌜0 < h⌝ }>>
          markNode' #n #p @ ∅
    <<{ ∃∃ (success: bool) mark' prf pvs',
            node Σ Hg1 n h mark' next k
          ∗ proph p pvs'
          ∗ ⌜Forall (λ x, ∃ v1, x = ((v1, #false)%V, #())) prf⌝
          ∗ (match success with 
              true => ⌜mark !!! 0 = false
                      ∧ mark' = <[0 := true]> mark
                      ∧ (∃ v1, pvs = prf ++ [((v1, #true)%V, #())] ++ pvs')⌝
            | false => ⌜mark !!! 0 = true
                      ∧ mark' = mark
                      ∧ pvs = prf ++ pvs'⌝ end) |
            RET (match success with true => SOMEV #() 
                                  | false => NONEV end)  }>>.

  Parameter getHeight_spec : ∀ Σ Hg1 (n: Node),
    ⊢ <<{ ∀∀ h mark next k, node Σ Hg1 n h mark next k }>>
          getHeight #n @ ∅
      <<{ node Σ Hg1 n h mark next k | RET #h }>>.

End NODE_IMPL.