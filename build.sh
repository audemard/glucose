#!/bin/bash
export FM=$PWD/sources/SatElite/ForMani

cd sources/SatElite/SatELite
make r
cp SatELite_release ../../..

cd ../../glucose/core
make rs
cp glucose_static ../../..
 
