# Call this script first before feeding the atomic input file from regerssion test (VHDL test)
import argparse
import re

# map the assembly atomic into sequenced atomic according to atomic input file
# e.g atomic b0 in the assembly code. We look into b0 in atomic input file and decide the location


def parserInfo():
	parser = argparse.ArgumentParser(description='ACOW: Model Checking tool for MLTL')
	parser.add_argument('-i','--input', help='Choose Atomic Input File', required=True)
	parser.add_argument('-a','--assembly', help='Choose Assembly File', required=True)
	args = vars(parser.parse_args())
	return args

def strtr(s, repl):
	pattern = '|'.join(map(re.escape, sorted(repl, key=len, reverse=True)))
	return re.sub(pattern, lambda m: repl[m.group()], s)

def main():
	args = parserInfo()

	with open(args['input'],"r") as f:
		first_line = f.readline()
		while(len(first_line.strip())==0 or first_line.lstrip()[0]=='#'):
			first_line = f.readline()
		token = re.split(r'\s|,',first_line.strip())
		tokenMap = {item:'a'+str(i) for i,item in enumerate(token)}
	print(tokenMap)
	with open(args['assembly'],"rt") as fin:
		with open("assembly.tmp", "wt") as fout:
			for line in fin:
				fout.write(strtr(line, tokenMap))


if __name__ == "__main__":
	main()