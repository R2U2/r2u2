import matplotlib.pyplot as plt
import numpy as np

'''
traceverdictplot function takes in 2 arguments: values and verdicts
values: list of sensor values to be plotted
verdicts: list of binary true/false values for plotting
traceverdictplot function plots values and verdicts on subplots with aligned x-axis(time)
'''

def traceverdictplot(values,verdicts):
    time = np.arange(0,len(values))
    values = values
    verdicts = verdicts
    if max(values) < 0:
        fig, (ax1, ax2) = plt.subplots(2,sharex=True,figsize=(16,5))
    
        plt.xticks(time)
        plt.xlabel('Time (sec)' ,size='14')
        ax2.set_yticks([1.0, 0.0])
        ax2.set_yticklabels(['True', 'False'])
        ax1.grid(linestyle='--')
        ax2.xaxis.grid(linestyle='--')
        ax1.set_title('Values',fontsize='16')
        ax2.set_title('Verdicts',fontsize='16')
        ax1.tick_params(axis = 'y', labelsize = '14')
        ax2.tick_params(axis = 'y', labelsize = '14')
        plt.tick_params(axis = 'x', labelsize = '14')
        ax1.set_ylabel('Radius',fontsize='16')
        ax1.yaxis.set_ticks(np.arange(min(values), max(values)+1, 1.0))
            
        ax1.step(time, values, linewidth = 4)
        ax2.step(time, verdicts, linewidth = 4)
    else:
        fig, (ax1, ax2, ax3) = plt.subplots(3, sharex=True, figsize=(16,8))
        plt.xticks(time)
        plt.xlabel('Time (sec)' ,size='14')
        ax3.set_yticks([1.0, 0.0])
        ax3.set_yticklabels(['True', 'False'])
        ax1.grid(linestyle='--')
        ax2.grid(linestyle='--')
        ax3.xaxis.grid(linestyle='--')
        ax1.set_title('Values',fontsize='16')
        ax3.set_title('Verdicts',fontsize='16')
        ax1.tick_params(axis = 'y', labelsize = '14')
        ax2.tick_params(axis = 'y', labelsize = '14')
        ax3.tick_params(axis = 'y', labelsize = '14')
        plt.tick_params(axis = 'x', labelsize = '14')
        ax1.set_ylabel('Radius',fontsize='16')
        ax1.yaxis.set_ticks(np.arange(998, 1001, 1.0))
        ax2.yaxis.set_ticks(np.arange(-5, 1, 1.0))
        ax1.set_ylim(997,1000.5)
        ax2.set_ylim(-6, 1)
        ax1.spines['bottom'].set_visible(False)
        ax2.spines['top'].set_visible(False)
        ax1.xaxis.tick_top()
        ax1.tick_params(labeltop=False)
        ax2.xaxis.tick_bottom()
        d = .015
        kwargs = dict(transform=ax1.transAxes, color='k', clip_on=False)
        ax1.plot((-d, +d), (-d, +d), **kwargs)
        ax1.plot((1 - d, 1 + d), (-d, +d), **kwargs)
        
        kwargs.update(transform=ax2.transAxes)
        ax2.plot((-d, +d), (1 - d, 1 + d), **kwargs)
        ax2.plot((1 - d, 1 + d), (1 - d, 1 + d), **kwargs)
            
        ax1.step(time, values, linewidth = 4)
        ax2.step(time, values, linewidth = 4)
        ax3.step(time, verdicts, linewidth = 4)
    #end if
#end function
