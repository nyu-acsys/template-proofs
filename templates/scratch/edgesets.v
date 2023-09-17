From Coq Require Import QArith Qcanon.
From stdpp Require Export gmap.
Require Export multiset_flows.

Section edgesets.
  Context `{Countable K}.

  Definition esT : Type := gmap K Node.
  
  (*
  Definition edgeset (es: gmap Node esT) n1 n2 : gset K :=
    (es !!! n1) !!! n2.
  *)
  
  Definition dom_esT (es: esT) : gset Node :=
    let f := λ (k: K) n res, res ∪ {[n]} in
      map_fold f (∅: gset Node) es.
  
  Definition es_rank_rel (es: gmap Node esT) (rank: Node → Qc) :=
    ∀ n1 n2, n2 ∈ dom_esT (es !!! n1) → (rank n1 < rank n2)%Qc. 

  Definition es_closed (es: gmap Node esT) 
    (I: gmap Node (multiset_flowint_ur K)) :=
      (dom es = dom I)
    ∧ (∀ n, dom_esT (es !!! n) ⊆ dom I).
  
  Definition es_outset_rel (n: Node) (esn: esT) In :=
    ∀ n' k, k ∈ outset K In n' ↔ esn !! k = Some n' ∧ k ∈ inset K In n.

  Definition es_marking_upd (esn esn' : esT) :=
      (dom esn ⊆ dom esn')
    ∧ (∀ k, k ∈ dom esn → esn !! k = esn' !! k)
    ∧ (dom_esT esn' = dom_esT esn).
  
  Lemma es_closed_upd n0 es es_n0' I :
    let es_n0 := es !!! n0 in
    let es' := <[n0 := es_n0']> es in
    n0 ∈ dom es →
    es_marking_upd es_n0 es_n0' →
    es_closed es I →
      es_closed es' I.
  Proof.
    intros es_n0 es' n0_in_es ES_upd ES_cl.
    rewrite /es'. split.
    - rewrite dom_insert_L.
      destruct ES_cl as [H' _]. set_solver.
    - intros n. 
      destruct (decide (n = n0)) as [-> | Hn].
      + rewrite lookup_total_insert.
        destruct ES_upd as [H1' [H2' H3']].
        rewrite H3'. apply ES_cl.
      + rewrite lookup_total_insert_ne; try done.
        by destruct ES_cl as [_ H''].
  Qed.
  
  Lemma es_rank_upd n0 es es_n0' rank :
    let es_n0 := es !!! n0 in
    let es' := <[n0 := es_n0']> es in
    es_marking_upd es_n0 es_n0' →
    es_rank_rel es rank →
      es_rank_rel es' rank.
  Proof.
    intros es_n0 es' ES_upd ES_rank.
    rewrite /es'.
    intros n1 n2 ES_n12.
    apply ES_rank.
    destruct (decide (n1 = n0)) as [-> | Hn1].
    - rewrite lookup_total_insert in ES_n12.
      destruct ES_upd as [H1' [H2' H3']].
      rewrite H3' in ES_n12. try done.
    - rewrite lookup_total_insert_ne in ES_n12; try done.
  Qed.

End edgesets.  
