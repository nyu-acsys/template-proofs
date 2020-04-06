#!/bin/bash
set -e

# This is a script for the PLDI'20 artifact VM


# Assumes https://github.com/nyu-acsys/templates-iris is in ~/templates

pushd ./templates/
echo ""
echo "Checking template proofs using Iris/Coq:"
echo ""
./xp_pldi20.sh
popd

# Assumes https://github.com/wies/grasshopper/ is in ~/grasshopper

pushd ./implementations/
echo ""
echo "Checking implementation proofs using GRASShopper:"
echo ""
./bin/xp_pldi20.sh
popd
