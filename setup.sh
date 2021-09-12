#!/bin/bash
set -e -x

# Download and build GRASShopper

[ ! -d "./grasshopper" ] && git clone https://github.com/wies/grasshopper.git grasshopper
pushd ./grasshopper/
git checkout 5828de4
./build.sh
popd

