from matplotlib import rc
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
import sys
import re
import numpy as np
import argparse

def reorganize4Plot(mix):
	xData, yData = [], []
	for i,j in mix:
		xData.append(i)
		yData.append(j)
	return [xData,yData]

def expand(MTL_res):
	preT = -1
	newMTL_res = []
	for t,v in MTL_res:
		for i in range(preT+1,t):
			newMTL_res.append([i,v])
		newMTL_res.append([t,v])
		preT = t
	return newMTL_res

def parserInfo():
	parser = argparse.ArgumentParser(description='Auto Plot for R2U2 Runtime Verification Result')
	parser.add_argument('-f','--file', help='Input the trace file name', required=False)
	args = vars(parser.parse_args())
	return args
################################
'''
format of input file, each row is an output RV trace. 0 is false, 1 is true.
(2,1),(3,1),(10,0),(15,1)
(0,1),(2,1),(8,0),(10,0)
'''
###########################################################################
def main():

	# Write the input trace file here or use the sys argument
	input_RV_Result_file = 'sample_input.trace'
	# Map the legend name to trace file here:
	label = [r'a0',r'$\square_{[0,3]}V\_threshold$',r'$\square_{[0,3]}Agree\_EncAPS2$',r'$\box$']
	# Example of plot color
	colorList = ('#8C1515','#FFDF00','#1e90ff','y','c','m','k','r','r')

	args = parserInfo()
	if(args['file']):
		input_RV_Result_file = args['file']
	file = open(input_RV_Result_file,'r')
	input_RV_Result = []
	for line in file:
		if(len(line.strip())!=0):
			tmp = []
			l = re.compile("\\s*,\\s*(?=\\()").split(line)
			for eachTuple in l:
				timestamp,verdict = re.sub("\\(|\\)","",eachTuple).split(",")
				tmp.append([int(timestamp),int(verdict)])
			input_RV_Result.append(tmp)


	plt.rc('text', usetex=True)
	plt.rc('text.latex', preamble=r'\usepackage{amsmath} \usepackage{MnSymbol} \usepackage{wasysym}')
	
	fig, ax = plt.subplots(len(input_RV_Result),1 , figsize=(10.5, 1.6),sharex=True)
	x_len = max(len(i) for i in input_RV_Result)
	ax[0].set_xlim(0,x_len+1)
	plt.xticks(np.arange(0, x_len+1, 5/0.5))
	ticks_x = ticker.FuncFormatter(lambda x, pos: '{0:g}'.format(x*0.5))
	ax[0].xaxis.set_major_formatter(ticks_x)

	for idx, sub_result in enumerate(input_RV_Result):
		ax[idx].plot(*reorganize4Plot(expand(sub_result)),color =colorList[idx], linestyle='dashed',marker = '.',label=label[idx],lw=0.5)
		ax[idx].legend(loc="best")
		ax[idx].set_ylim(0,1)
		ax[idx].set_yticks([0,1])
	fig.canvas.draw()

	for ax_sub in ax:
		labels = [item.get_text() for item in ax_sub.get_yticklabels()]
		labels[0],labels[1] = 'False','True'
		ax_sub.set_yticklabels(labels)
		ax_sub.spines['right'].set_visible(False)
		ax_sub.spines['top'].set_visible(False)

	ax[len(input_RV_Result)-1].set_xlabel('Time (sec)', fontsize=13)
	plt.savefig(input_RV_Result_file+"_res.pdf",bbox_inches='tight')
	plt.show()


if __name__ == "__main__":
   main()
