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
From flows Require Import array_util bool_ra gset_seq.

Module Type NODE_IMPL.

  Definition MarkT := gmap nat bool.
  Definition NextT := gmap nat Node.

  Parameter node : ∀ Σ, Node → nat → MarkT → NextT → nat → iProp Σ.
  #[global] Declare Instance node_timeless_proof : ∀ Σ n h mark next k, 
    Timeless (node Σ n h mark next k).

  Parameter node_sep_star: ∀ Σ n h mark next k h' mark' next' k',
    node Σ n h mark next k -∗ node Σ n h' mark' next' k' -∗ False.

  Parameter inContents : val.
  Parameter findNext : val.
  Parameter changeNext : val.
  Parameter markNode : val.
  Parameter compareKey : val.
  Parameter getKey : val.
  Parameter createNode : val.
  Parameter getHeight : val.
  Parameter permute_levels : val.

  Parameter createNode_spec : ∀ Σ (H' : heapGS Σ) (succs: loc) ss (L k: nat),
  ⊢  {{{ is_array Σ _ succs ss ∗ ⌜length ss = L⌝ }}}
           createNode #k #succs
        {{{ (n: Node) (h: nat) mark next,
            RET #n;
              is_array Σ _ succs ss
            ∗ node Σ n h mark next k
            ∗ ⌜0 < h < L⌝
            ∗ ⌜dom mark = gset_seq 0 (h-1)⌝ ∗ ⌜dom next = gset_seq 0 (h-1)⌝
            ∗ (⌜∀ i, i < h → mark !! i = Some false⌝)
            ∗ (⌜∀ i, i < h → next !! i = Some (ss !!! i)⌝) }}}.

  Parameter findNext_spec : ∀ Σ (H' : heapGS Σ) (n: Node) (i: nat),
    ⊢ <<{ ∀∀ h mark next k, node Σ n h mark next k ∗ ⌜i < h⌝ }>>
          findNext #n #i @ ∅
      <<{ ∃∃ (m: bool) (n': Node),
              node Σ n h mark next k ∗ ⌜mark !!! i = m⌝ ∗ ⌜next !!! i = n'⌝ |
              RET (#m, #n') }>>.

  Parameter changeNext_spec : ∀ Σ (H' : heapGS Σ) (n m m': Node) (i: nat),
    ⊢  <<{ ∀∀ h mark next k, node Σ n h mark next k ∗ ⌜i < h⌝ }>>
            changeNext #n #m #m' #i @ ∅
      <<{ ∃∃ (success: bool) next',
              node Σ n h mark next' k
            ∗ (match success with true => ⌜next !!! i = m 
                                            ∧ mark !!! i = false
                                            ∧ next' = <[i := m']> next⌝
                                | false => ⌜(next !!! i ≠ m ∨ 
                                              mark !!! i = true)
                                            ∧ next' = next⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end) }>>.

  Parameter changeNext_proph_spec : ∀ Σ (H' : heapGS Σ) (n m m': Node) (p: proph_id) pvs,
    ⊢ proph p pvs -∗
      <<{ ∀∀ h mark next k, node Σ n h mark next k ∗ ⌜0 < h⌝ }>>
            changeNext #n #m #m' #p @ ∅
      <<{ ∃∃ (success: bool) next' prf pvs',
              node Σ n h mark next' k
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

  Parameter compareKey_spec : ∀ Σ (H' : heapGS Σ) (n: Node) (k': nat),
    ⊢ <<{ ∀∀ h mark next k, node Σ n h mark next k }>>
           compareKey #n #k' @ ∅
     <<{ ∃∃ (res: nat),
            node Σ n h mark next k 
          ∗ ⌜if decide (res = 0) then k < k'
             else if decide (res = 1) then k = k'
             else k > k'⌝ |
         RET #res }>>.

  Parameter getKey_spec : ∀ Σ (H' : heapGS Σ) (n: Node),
    ⊢ <<{ ∀∀ h mark next k, node Σ n h mark next k }>>
           getKey #n @ ∅
     <<{ node Σ n h mark next k | RET #k }>>.

  Parameter markNode_spec : ∀ Σ (n: Node) (H' : heapGS Σ) (i: nat),
    ⊢ <<{ ∀∀ h mark next k, node Σ n h mark next k ∗ ⌜i < h⌝ }>>
            markNode #n #i @ ∅
      <<{ ∃∃ (success: bool) mark',
              node Σ n h mark' next k
            ∗ (match success with true => ⌜mark !!! i = false
                                            ∧ mark' = <[i := true]> mark⌝
                                | false => ⌜mark !!! i = true
                                            ∧ mark' = mark⌝ end) |
              RET (match success with true => SOMEV #() 
                                    | false => NONEV end)  }>>.

  
  Parameter markNode_proph_spec : ∀ Σ (H' : heapGS Σ) (n: Node) (p: proph_id) pvs,
  ⊢ proph p pvs -∗ 
    <<{ ∀∀ h mark next k, node Σ n h mark next k ∗ ⌜0 < h⌝ }>>
          markNode #n #p @ ∅
    <<{ ∃∃ (success: bool) mark' prf pvs',
            node Σ n h mark' next k
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

  Parameter getHeight_spec : ∀ Σ (H' : heapGS Σ) (n: Node) (i: nat),
    ⊢ <<{ ∀∀ h mark next k, node Σ n h mark next k }>>
          getHeight #n @ ∅
      <<{ node Σ n h mark next k | RET #h }>>.

End NODE_IMPL.