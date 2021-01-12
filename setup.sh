#!/bin/bash
set -e

# Download and build GRASShopper

[ ! -d "./grasshopper" ] && git clone https://github.com/wies/grasshopper.git grasshopper
pushd ./grasshopper/
./build.sh
popd

