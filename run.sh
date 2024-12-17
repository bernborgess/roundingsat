#!/bin/bash

cd build_debug
cmake -DCMAKE_BUILD_TYPE=Debug ..
make
cd ..
./build_debug/roundingsat input.opb --proof-log=output