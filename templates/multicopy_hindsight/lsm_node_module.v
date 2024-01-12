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

Module Type LSM_NODE_IMPL.

  Definition K := Z.
  Definition V := Z.
  Parameter KS : gset K.
  Definition bot : V := 0%CCM.

  Definition esT : Type := gmap Node (gset K).
  Canonical Structure esRAC := leibnizO esT.

  Parameter node : ∀ Σ, heapGS Σ → Node → Node → esT → gmap K V → iProp Σ.
  #[global] Declare Instance node_timeless_proof : ∀ Σ Hg1 r n es V, 
    Timeless (node Σ Hg1 r n es V).

  Parameter node_sep_star: ∀ Σ Hg1 r n es V es' V',
    node Σ Hg1 r n es V ∗ node Σ Hg1 r n es' V' -∗ False.

  Parameter node_es_disjoint: ∀ Σ Hg1 r n es V,
    node Σ Hg1 r n es V -∗ ⌜∀ n1 n2, n1 ≠ n2 → es !!! n1 ∩ es !!! n2 = ∅⌝.  

  Parameter node_es_empty: ∀ Σ Hg1 r n es V,
    node Σ Hg1 r n es V -∗ ⌜es !!! r = ∅ ∧ es !!! n = ∅⌝.
  
  Parameter lockLoc : Node → loc.
  Definition lockR Σ (Hg1 : heapGS Σ) (b: bool) (n: Node) (R: iProp Σ) : iProp Σ :=
      ((lockLoc n) ↦ #b ∗ (if b then True else R))%I.

  Parameter inContents : val.
  Parameter findNext : val.
  Parameter addContents: val.
  Parameter lockNode : val.
  Parameter unlockNode : val.

  Parameter inContents_spec : ∀ Σ Hg1 r n esn (Vn: gmap K V) (k: K),
  ⊢ ({{{ node Σ Hg1 r n esn Vn }}}
        inContents #n #k
    {{{ (v: option V), 
          RET (match v with Some v => SOMEV #v | None => NONEV end);
              node Σ Hg1 r n esn Vn ∗ ⌜Vn !! k = v⌝ }}})%I.
  
  Parameter findNext_spec : ∀ Σ Hg1 r n esn (Vn: gmap K V) (k: K),
  ⊢ ({{{ node Σ Hg1 r n esn Vn }}}
        findNext #n #k
    {{{ (n': option Node),
          RET (match n' with Some n' => SOMEV #n' | None => NONEV end);
              node Σ Hg1 r n esn Vn 
              ∗ (match n' with Some n' => ⌜k ∈ esn !!! n'⌝ 
                              | None => ⌜∀ n'', k ∉ esn !!! n''⌝ end) }}})%I.

  Parameter addContents_spec : ∀ Σ Hg1 r n esn (Vn: gmap K V) (k: K) (v: V),
  ⊢ ({{{ node Σ Hg1 r n esn Vn ∗ ⌜n = r⌝ }}}
        addContents #r #k #v
    {{{ (succ: bool) (Vn': gmap K V),
          RET #succ;
              node Σ Hg1 r n esn Vn' ∗ if succ then ⌜Vn' = <[k := v]> Vn⌝ 
                            else ⌜Vn' = Vn⌝ }}})%I.
  
  Parameter lockNode_spec : ∀ Σ Hg1 (n: Node),
  ⊢ <<{ ∀∀ b R, lockR Σ Hg1 b n R }>>
        lockNode #n  @ ∅
    <<{ lockR Σ Hg1 true n R ∗ R | RET #() }>>.

  Parameter unlockNode_spec : ∀ Σ Hg1 (n: Node),
  ⊢ <<{ ∀∀ R, lockR Σ Hg1 true n R ∗ R }>>
        unlockNode #n  @ ∅
    <<{ lockR Σ Hg1 false n R | RET #() }>>.

End LSM_NODE_IMPL.