#!/bin/bash
set -e -x

[ -d "./ecoop24_artifact" ] && rm -rf ecoop24_artifact
mkdir ecoop24_artifact
cd ecoop24_artifact

cp ../README_ecoop24.md .
mv README_ecoop24.md README.md

cp ../LICENSE_ecoop24 .
mv LICENSE_ecoop24 LICENSE

mkdir -p templates/flows
mkdir -p templates/util
mkdir -p templates/hindsight
mkdir -p templates/lockfree
mkdir -p templates/multicopy_hindsight


files=(
"templates/xp_ecoop24.sh"
"templates/xp_ecoop24_short.sh"
"templates/_CoqProject_ecoop24"
"templates/flows/gmap_more.v"
"templates/flows/ccm.v"
"templates/flows/ccm_big_op.v"
"templates/flows/flows.v"
"templates/flows/flows_big_op.v"
"templates/flows/multiset_flows.v"
"templates/flows/list_flow_upd.v"
"templates/flows/list_flow_upd_marking.v"
"templates/flows/list_flow_upd_insert.v"
"templates/flows/list_flow_upd_unlink.v"
"templates/util/keyset_ra.v"
"templates/util/misc_ra.v"
"templates/util/one_shot_proph.v"
"templates/util/typed_proph.v"
"templates/util/gset_seq.v"
"templates/util/array_util.v"
"templates/hindsight/hindsight.v"
"templates/hindsight/hindsight_proof.v"
"templates/lockfree/node_module.v"
"templates/lockfree/traverse_module.v"
"templates/lockfree/skiplist.v"
"templates/lockfree/skiplist_util.v"
"templates/lockfree/traverse_spec_module.v"
"templates/lockfree/skiplist_delete_maintenance.v"
"templates/lockfree/skiplist_delete.v"
"templates/lockfree/skiplist_insert_maintenance.v"
"templates/lockfree/skiplist_insert.v"
"templates/lockfree/skiplist_search.v"
"templates/lockfree/skiplist_spec.v"
"templates/lockfree/eager.v"
"templates/lockfree/lazy.v"
"templates/lockfree/node_impl1.v"
"templates/lockfree/node_impl2.v"
"templates/multicopy_hindsight/lsm_node_module.v"
"templates/multicopy_hindsight/lsm.v"
"templates/multicopy_hindsight/lsm_util.v"
"templates/multicopy_hindsight/lsm_search.v"
"templates/multicopy_hindsight/lsm_upsert.v"
"templates/multicopy_hindsight/lsm_spec.v"
)

for t in ${files[@]}; do
  cp ../$t $t
done

mv templates/_CoqProject_ecoop24 templates/_CoqProject

cd ..

zip -r ecoop24_artifact.zip ecoop24_artifact/

rm -rf ecoop24_artifact/
