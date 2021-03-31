#!/usr/bin/bash

if [[ -z "$KREMLIN_HOME" ]]; then
    echo "Set KREMLIN_HOME"
    exit 1
fi

rm -rf build/*
cp *.fst build/
cd build
$KREMLIN_HOME/krml -skip-compilation TLWE.fst -drop WasmSupport -o libintro.a
make -f Makefile.basic
