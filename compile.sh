#!/bin/bash


SOURCE_FILES=("Grammar.v"
	      "ExampleGrammars.v"
	      "ParserUtils.v"
	      "Derivation.v"
	      "ParserTactics"
	      "DerivationTests.v"
	      "ParseTable.v"
	      "ParseTableTests.v"
	      "ParseTree.v"
	      "Parser.v"
	      "ParserTests.v"
	      "ParserCorrectnessProofs.v"	      
	     )


for v_file in "${SOURCE_FILES[@]}"; do
    coqc "${v_file}"
done
