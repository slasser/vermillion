#!/bin/bash


SOURCE_FILES=("Grammar.v"
	      "ExampleGrammars.v"
	      "ParseTable.v"
	      "ParseTree.v"
	      "Parser.v"
	      #"ParserTests.v"
	      "Derivation.v"
	      "DerivationTests.v"
	     )


for v_file in "${SOURCE_FILES[@]}"; do
    coqc "${v_file}"
done
