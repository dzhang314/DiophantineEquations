#!/bin/sh

set -e

mkdir -p bin

clang++ -std=c++20 \
    -Weverything -Wno-c++98-compat -Wno-c++98-compat-pedantic \
    -Wno-poison-system-directories \
    -O3 -march=native src/ListAllPolynomials.cpp -o bin/ListAllPolynomials
