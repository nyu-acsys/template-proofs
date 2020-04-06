#!/bin/bash
set -e

# Download and build GRASShopper

[ ! -d "./grasshopper" ] && git clone -b pldi_2020 https://github.com/wies/grasshopper.git grasshopper
pushd ./grasshopper/
./build.sh
popd

