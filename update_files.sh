#!/bin/bash
set -e

# Update all proof scripts from github

# Assumes https://github.com/nyu-acsys/templates-iris is in ~/templates

pushd ~/templates/
git pull
cp update_files.sh ../
cp run_experiments.sh ../
popd

# Assumes https://github.com/wies/grasshopper/ is in ~/grasshopper

pushd ~/grasshopper/
git pull
popd
