from isort import file
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path


RESULTS_DIR = "results/"

def gen_rewrite_plot() -> None:
  data = [{},{}]
  pre = 0
  post = 1

  for filename in [f for f in Path("./" + RESULTS_DIR).iterdir()]:
    len_str = filename.stem[5:7]
    len = 0
    try:
      len = int(len_str)
    except:
      len = int(filename.stem[5])

    num_vars = int(filename.stem[3])

    if not num_vars in data[pre]:
      data[pre][num_vars] = {}
    if not num_vars in data[post]:
      data[post][num_vars] = {}

    if not data[pre][num_vars]:
      data[pre][num_vars] = {}

    if not data[post][num_vars]:
      data[post][num_vars] = {}

    with open(filename) as f:
      result = f.read().split(",")
      data[pre][num_vars][len] = int(result[pre])
      data[post][num_vars][len] = int(result[post])
      
  lens = np.arange(5,50,5)

  pre_data = []
  post_data = []

  mem_percent = []
  for n in range(1,6):
    pre_data.append([])
    post_data.append([])
    for l in lens:
      pre_data[n-1].append(data[pre][n][l])
      post_data[n-1].append(data[post][n][l])
      mem_percent.append((data[pre][n][l]-data[post][n][l])/data[pre][n][l])

  print(np.average(mem_percent))

  # print(pre_1_data)
  fig, ax = plt.subplots(layout='constrained')
  ax.plot(lens, pre_data[0], 'b', label='Original 1 Variable')
  ax.plot(lens, post_data[0], 'b--', label='Optimized 1 Variable')
  # ax.plot(lens, pre_data[1], 'g', label='Original 2 Variables')
  # ax.plot(lens, post_data[1], 'g--', label='Optimized 2 Variables')
  ax.plot(lens, pre_data[2], 'r', label='Original 3 Variables')
  ax.plot(lens, post_data[2], 'r--', label='Optimized 3 Variables')
  # ax.plot(lens, pre_data[3], 'm', label='Original 4 Variables')
  # ax.plot(lens, post_data[3], 'm--', label='Optimized 4 Variables')
  ax.plot(lens, pre_data[4], 'k', label='Original 5 Variables')
  ax.plot(lens, post_data[4], 'k--', label='Optimized 5 Variables')

  ax.legend(loc='upper left')
  ax.set_xlabel('Formula Length (Number of operators+operands)')
  ax.set_ylabel('Encoding Size (Bits)')

  ax.grid(True)

  plt.show()  


if __name__ == "__main__":
  gen_rewrite_plot()