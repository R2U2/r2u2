# Signal Map Files [`.map`]

A signal map file is a UTF-8 text file with a .map file extension.
Each line of the input file should be of the form `SYMBOL : NUMERAL` such that if SYMBOL corresponds to a signal identifier in the MLTL file, its signal ID is set to the integer value of NUMERAL.

Note that if SYMBOL is not present in the MLTL file, the line is ignored.
