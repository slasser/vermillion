#!/bin/bash


SOURCE_FILES=("Parser.v"
	      "Grammar.v"
	      "Derivation.v"
	      "ParserTest.v"
	      "DerivationTest.v"
	     )


for v_file in "${SOURCE_FILES[@]}"; do
    coqc "${v_file}"
done
