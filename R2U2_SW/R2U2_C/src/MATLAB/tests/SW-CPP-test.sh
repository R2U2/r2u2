#!/bin/bash


pushd ./
cd $1/src
mv $2.fts test.ftasm
cd $1
./Debug/MTL

popd