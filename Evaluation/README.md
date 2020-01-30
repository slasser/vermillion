To run the evaluation experiment:

1. `make nc`

-    This compiles the OCaml code extracted from Coq, the experiment code in `test.ml`, etc.

2. `./test <JSON_test_data_directory> <benchmark_results_file>`

-    This runs the evaluation and writes the results to `benchmark_results_file` (it might take ~30 seconds).

-    Example: `./test nobel_data benchmark_results.json`

3. `python plot.py <benchmark_results_file> <plot_file>`

-    This plots the results in a .eps file. The Python script requires the numpy and matplotlib libraries to be installed.

-    Example: `python plot.py benchmark_results.json benchmark_results.eps`


To undo the build:

`make clean`