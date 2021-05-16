import h5py
import matplotlib.pyplot as plt
import numpy as np

'''
hdf5plot function takes in 2 arguments: filename and sensornamepath
filename: name of file with extension to be read and plotted
sensornamepath: path to dataset for plotting
hdf5plot function returns a plot of the given dataset
'''

filename = '2018_03_26_145222_smt_log_ssh.hdf5'
sensornamepath = ''


def hdf5plot(filename, sensornamepath):
    with h5py.File(filename, 'r') as f:
        data = f[sensornamepath]
        nCols = len(data[0])
        fig, ax = plt.subplots(nCols, sharex=True)
        for i in range(0, nCols):
            time = np.arange(0, len(data))
            values = data[:,i]
            ax[i].plot(time, values, linewidth = 4)
            plt.xlabel('Time (s)')
            fig.suptitle(str(sensornamepath),fontsize=14)
            ax[i].grid(linestyle = '--')
        #end for
    #end with
    return

hdf5plot(filename, sensornamepath)