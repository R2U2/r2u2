import argparse

def prec_chain_1_n(ub: int, chain: list[int]) -> str:
    assert len(chain) > 0
    template = "F[{ub},{ub}] (a1 & {{}}) -> F[0,{ub}] a0".format(ub=ub)
    for i in range(len(chain) - 1):
        template = template.format(f"F[0,{chain[i]}] (a{2+i} & {{}})")
    return template.format(f"F[0,{chain[-1]}] a{len(chain)+1}")


parser = argparse.ArgumentParser()
parser.add_argument("ub", type=int, help="upper bound for s and chain elements")
parser.add_argument("chain_len", type=int, help="number of elements in chain (nesting depth)")
# parser.add_argument("warmup", type=int, help="number of empty timestamps at beginning of trace for warmup")
# parser.add_argument("epilogue", type=int, help="number of empty timestamps to add to end of trace")

args = parser.parse_args()

ub = args.ub
chain = [int(args.ub) for _ in range(args.chain_len)]
# warmup = args.warmup
# epilogue = args.epilogue

print(prec_chain_1_n(ub, chain))

# with open("prec_chain.mltl", "w") as f:
#     f.write(prec_chain_1_n(ub, chain) + "\n")

# trace = []
# trace += [[1, 0] + [0 for _ in range(len(chain))] for _ in range(warmup)]
# trace += [[0, 0] + [0 for _ in range(len(chain))] for _ in range(ub)]
# trace += [[0, 1]  + [0 for _ in range(len(chain))]]
# for i,gap in enumerate(chain):
#     trace += [[0, 0] + [0 for _ in range(len(chain))] for _ in range(gap-1)]
#     trace += [[0, 0] + [0 for _ in range(i)] + [1] + [0 for _ in range(len(chain) - i - 1)]]
# trace += [[0, 0] + [0 for _ in range(len(chain))] for _ in range(epilogue)]

# with open("prec_chain.csv", "w") as f:
#     for line in trace:
#         f.write(",".join([str(i) for i in line]) + "\n")
