# Vermillion

## LL(1) parser generator verified in Coq

This project has been tested with Coq version 8.8.1.

To build the project:

  `make`

To delete generated files:

  `make clean`

`Main.v` contains the main correctness theorems:
- LL(1) parse table generator soundness and completeness
- LL(1) parser soundness, safety, and completeness

`Example.v` contains a tutorial on how to use the tool.
