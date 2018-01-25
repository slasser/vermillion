#!/bin/bash


SOURCE_FILES=("Grammar.v"
	      "ExampleGrammars.v"
	      "ParserUtils.v"
	      "ParseTable.v"
	      "ParseTableTests.v"
	      "Derivation.v"
	      "ParserTactics"
	      "DerivationTests.v"
	      "ParseTree.v"
	      "Parser.v"
	      "ParserTests.v"
	      "ParserCorrectnessProofs.v"	      
	     )


for v_file in "${SOURCE_FILES[@]}"; do
    coqc "${v_file}"
done
