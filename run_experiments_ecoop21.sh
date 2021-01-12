#!/bin/bash
set -e -x

# This is a script for the ECOOP'21 artifact


# Assumes template proofs are in ~/templates

pushd ./templates/
echo ""
echo "Checking template proofs using Iris/Coq:"
echo ""
./xp_ecoop21.sh
popd

# Assumes GRASShopper is in ~/grasshopper

pushd ./implementations/
echo ""
echo "Checking implementation proofs using GRASShopper:"
echo ""
./xp_ecoop21.sh
popd
