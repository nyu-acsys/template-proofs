#!/bin/bash
set -e -x

# Download and build GRASShopper

[ ! -d "./grasshopper" ] && git clone https://github.com/wies/grasshopper.git grasshopper
pushd ./grasshopper/
./build.sh
popd

