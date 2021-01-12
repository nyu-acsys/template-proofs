#!/bin/bash

mkdir ecoop21_artifact
cd ecoop21_artifact

# Download and build Grasshopper 

[ ! -d "./grasshopper" ] && git clone https://github.com/wies/grasshopper.git grasshopper
pushd ./grasshopper/
./build.sh
popd

cp ../README_ecoop21.md .
mv README_ecoop21.md README.md
cp ../run_experiments_ecoop21.sh .
mv run_experiments_ecoop21.sh run_experiments.sh

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
"templates/_CoqProject"
"templates/flows/gmap_more.v"
"templates/flows/ccm.v"
"templates/flows/flows.v"
"templates/flows/multiset_flows.v"
"templates/util/auth_ext.v"
"templates/util/lock.v"
"templates/multicopy/one_shot_proph.v"
"templates/multicopy/typed_proph.v"
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


zip -r ecoop21_artifact.zip ecoop21_artifact/

rm -rf ecoop21_artifact/
