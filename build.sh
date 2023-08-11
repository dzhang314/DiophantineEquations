#!/bin/sh

set -e

mkdir -p bin
mkdir -p data

clang++ -std=c++20 \
    -Weverything -Wno-c++98-compat -Wno-c++98-compat-pedantic \
    -Wno-poison-system-directories \
    -O3 -march=native -flto \
    src/ListAllPolynomials.cpp -o bin/ListAllPolynomials
