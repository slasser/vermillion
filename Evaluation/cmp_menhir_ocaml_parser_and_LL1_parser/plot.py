import numpy as np
import matplotlib.pyplot as plt

"""
0.001263 0.000311 0.001329 0.001640
0.001333 0.000683 0.002244 0.002927
0.001094 0.000868 0.003271 0.004139
0.001151 0.001179 0.004287 0.005465
0.001508 0.001461 0.005495 0.006956
0.001817 0.001925 0.006731 0.008656
0.002335 0.002684 0.006622 0.009307
0.002931 0.003209 0.008761 0.011970
0.003567 0.004633 0.010306 0.014939
0.004086 0.005969 0.012481 0.018450
"""

fileSizes = (26,
             43,
             64,
             84,
             104,
             131,
             164,
             205,
             243,
             284)


menhirParserTimes = (0.001263,
                     0.001333, 
                     0.001094,
                     0.001151, 
                     0.001508, 
                     0.001817, 
                     0.002335, 
                     0.002931, 
                     0.003567, 
                     0.004086)

menhirTokenizerTimes = (0.000311, 
                        0.000683,
                        0.000868, 
                        0.001179,
                        0.001461,
                        0.001925,
                        0.002684,
                        0.003209,
                        0.004633,
                        0.005969)

ll1ParserTimes = (0.001329,
                  0.002244,
                  0.003271,
                  0.004287,
                  0.005495,
                  0.006731,
                  0.006622,
                  0.008761,
                  0.010306,
                  0.012481)

N = 10

ind = np.arange(N)    # the x locations for the groups
width = 5       # the width of the bars: can also be len(x) sequence

p1 = plt.bar(fileSizes, menhirParserTimes, width)
p2 = plt.bar([fs + width for fs in fileSizes], menhirTokenizerTimes, width)
p3 = plt.bar([fs + width for fs in fileSizes], ll1ParserTimes, width, bottom = menhirTokenizerTimes)

"""
p2 = plt.bar(ind + width, menhirTokenizerTimes, width)
p3 = plt.bar(ind + width, menhirParserTimes, width, bottom = menhirTokenizerTimes)
"""
plt.xlabel("File Size (KB)")
plt.ylabel("Time (s)")
plt.xticks(fileSizes, [str(fs) for fs in fileSizes])
plt.legend((p1[0], p2[0], p3[0]), ("Menhir Parser", "Menhir Tokenizer", "Vermillion Parser"))
"""plt.yticks(np.arange(0, 81, 10))
plt.legend((p1[0], p2[0]), ('Men', 'Women'))
"""
plt.savefig("JSON_parser_evaluation.png")
