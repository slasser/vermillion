To run the evaluation experiment:

1. `./build.sh`

(This compiles the OCaml code extracted from Coq, the experiment code in `test.ml`, etc.)

2. `./test.native`

(This runs the evaluation and writes the results to `benchmark_results.json`.)

3. `python plot.py`

(This plots the results in a .png file. The Python script requires the numpy and matplotlib libraries to be installed.)