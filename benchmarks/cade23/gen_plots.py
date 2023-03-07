import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path


RESULTS_DIR = "results/"
CSE_REWRITE_RESULTS = RESULTS_DIR+"rewrite/results.out"
DYN_SET_RESULTS = RESULTS_DIR+"dyn-set/results.out"

def gen_rewrite_plot() -> None:
  data = [{},{}]
  pre = 0
  post = 1

  with open(CSE_REWRITE_RESULTS,"r") as f:
    for line in f.read().splitlines():
      entries = line.split(",")
      test_name = entries[0]
      len = int(test_name[7]) if test_name[8] == "M" else (int(test_name[7:9]) if test_name[9] == "M" else int(test_name[7:10]))
      prob = int(test_name[3])

      print(entries[0])
      print(len)

      if not prob in data[pre]:
        data[pre][prob] = {}
      if not prob in data[post]:
        data[post][prob] = {}

      if not data[pre][prob]:
        data[pre][prob] = {}
      if not data[post][prob]:
        data[post][prob] = {}

      data[pre][prob][len] = int(entries[1])
      data[post][prob][len] = int(entries[2])
        
  lens = np.array([15,25,35,50,65,75,100])

  pre_data = []
  post_data = []

  mem_percent = []


  for l in lens:
    pre_data.append([])
    post_data.append([])
    pre_data[0].append(data[pre][5][l])
    post_data[0].append(data[post][5][l])
    mem_percent.append((data[pre][5][l]-data[post][5][l])/data[pre][5][l])

    pre_data.append([])
    post_data.append([])
    pre_data[1].append(data[pre][9][l])
    post_data[1].append(data[post][9][l])
    print(data[post][9][l])
    mem_percent.append((data[pre][9][l]-data[post][9][l])/data[pre][9][l])

  # for prob in [5,9]:
  #   pre_data.append([])
  #   post_data.append([])
  #   for l in lens:
  #     pre_data[n-1].append(data[pre][n][l])
  #     post_data[n-1].append(data[post][n][l])
  #     mem_percent.append((data[pre][n][l]-data[post][n][l])/data[pre][n][l])

  print(np.average(mem_percent))

  # print(pre_1_data)
  fig, ax = plt.subplots(layout='constrained')
  ax.plot(lens, pre_data[0], 'b', label='Original 1 Variable')
  ax.plot(lens, post_data[0], 'b--', label='Optimized 1 Variable')
  ax.plot(lens, pre_data[1], 'g', label='Original 2 Variables')
  ax.plot(lens, post_data[1], 'g--', label='Optimized 2 Variables')

  ax.legend(loc='upper left')
  ax.set_xlabel('Formula Length (Number of operators+operands)')
  ax.set_ylabel('Encoding Size (Bits)')

  ax.grid(True)

  plt.show()  


def gen_dyn_set_plot() -> None:
  data = [{},{}]
  pre = 0
  post = 1

  with open(DYN_SET_RESULTS,"r") as f:
    for line in f.read().splitlines():
      entries = line.split(",")
      test_name = entries[0]
      len = int(test_name[7]) if test_name[8] == "M" else (int(test_name[7:9]) if test_name[9] == "M" else int(test_name[7:10]))
      prob = int(test_name[3])

      print(entries[0])
      print(len)

      if not prob in data[pre]:
        data[pre][prob] = {}
      if not prob in data[post]:
        data[post][prob] = {}

      if not data[pre][prob]:
        data[pre][prob] = {}
      if not data[post][prob]:
        data[post][prob] = {}

      data[pre][prob][len] = int(entries[1])
      data[post][prob][len] = int(entries[2])
        
  lens = np.array([3,5,8,10,12,15,20])

  pre_data = []
  post_data = []

  mem_percent = []


  for l in lens:
    pre_data.append([])
    post_data.append([])
    pre_data[0].append(data[pre][5][l])
    post_data[0].append(data[post][5][l])
    mem_percent.append((data[pre][5][l]-data[post][5][l])/data[pre][5][l])

    # pre_data.append([])
    # post_data.append([])
    # pre_data[1].append(data[pre][9][l])
    # post_data[1].append(data[post][9][l])
    # print(data[post][9][l])
    # mem_percent.append((data[pre][9][l]-data[post][9][l])/data[pre][9][l])

  # for prob in [5,9]:
  #   pre_data.append([])
  #   post_data.append([])
  #   for l in lens:
  #     pre_data[n-1].append(data[pre][n][l])
  #     post_data[n-1].append(data[post][n][l])
  #     mem_percent.append((data[pre][n][l]-data[post][n][l])/data[pre][n][l])

  print(np.average(mem_percent))

  # print(pre_1_data)
  fig, ax = plt.subplots(layout='constrained')
  ax.plot(lens, pre_data[0], 'b', label='Original 1 Variable')
  ax.plot(lens, post_data[0], 'b--', label='Optimized 1 Variable')
  # ax.plot(lens, pre_data[1], 'g', label='Original 2 Variables')
  # ax.plot(lens, post_data[1], 'g--', label='Optimized 2 Variables')

  ax.legend(loc='upper left')
  ax.set_xlabel('Formula Length (Number of operators+operands)')
  ax.set_ylabel('Encoding Size (Bits)')

  ax.grid(True)

  plt.show()  


if __name__ == "__main__":
  # gen_rewrite_plot()
  gen_dyn_set_plot()