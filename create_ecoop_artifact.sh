#!/bin/bash
set -e -x

mkdir ecoop21_artifact
cd ecoop21_artifact

cp ../README_ecoop21.md .
mv README_ecoop21.md README.md
cp ../run_experiments_ecoop21.sh .
mv run_experiments_ecoop21.sh run_experiments.sh
cp ../setup.sh .

mkdir implementations
mkdir templates
mkdir templates/flows
mkdir templates/util
mkdir templates/multicopy

files=(
"implementations/xp_ecoop21.sh" 
"implementations/array_util.spl"
"implementations/ordered_type.spl"
"implementations/multicopy-lsm.spl"
"templates/xp_ecoop21.sh"
"templates/_CoqProject_ecoop21"
"templates/flows/gmap_more.v"
"templates/flows/ccm.v"
"templates/flows/flows.v"
"templates/flows/multiset_flows.v"
"templates/util/auth_ext.v"
"templates/util/lock.v"
"templates/util/one_shot_proph.v"
"templates/util/typed_proph.v"
"templates/multicopy/multicopy.v"
"templates/multicopy/multicopy_util.v"
"templates/multicopy/multicopy_client_level.v"
"templates/multicopy/multicopy_lsm.v"
"templates/multicopy/multicopy_lsm_util.v"
"templates/multicopy/multicopy_lsm_search.v"
"templates/multicopy/multicopy_lsm_upsert.v"
"templates/multicopy/multicopy_lsm_compact.v"
)

for t in ${files[@]}; do
  cp ../$t $t
done

mv templates/_CoqProject_ecoop21 templates/_CoqProject

cd ..

zip -r ecoop21_artifact.zip ecoop21_artifact/

rm -rf ecoop21_artifact/
