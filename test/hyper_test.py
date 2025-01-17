from tqdm.auto import tqdm
from itertools import product, repeat, chain, combinations_with_replacement, count
from collections import namedtuple
import subprocess
import tempfile
import csv
import re
from math import log, log10, comb
from functools import lru_cache

C2PO_PATH = "../compiler"
R2U2_PATH = "../monitors/c/build"

TestConfig = namedtuple('TestConfig', ['max_depth', 'max_interval', 'max_atoms', 'max_time', 'cumulative'])

class Operator(namedtuple('Operator', ['name', 'arity', 'tense', 'temporal', 'format', 'oracle'])):

    def __new__(cls, *args):
        self = super(Operator, cls).__new__(cls, *args)
        if self.temporal:
            self.interval = None
        return self

    def print(self, children):

        if self.arity == 0:
            return self.format.format(*children)
        elif not self.temporal:
            return self.format.format(*[child[0].print(child[1]) for child in children])
        elif self.arity == 1:
            return self.format.format(*self.interval, *[child[0].print(child[1]) for child in children])
        elif self.arity == 2:
            return self.format.format(children[0][0].print(children[0][1]), *self.interval, children[1][0].print(children[1][1]))

    def __repr__(self):
        if self.temporal and self.interval is not None:
            return self.name+"[{},{}]".format(*self.interval)
        return self.name

def temporal_roi(i, interval, T_MAX):
    # Compute the Region of Interest (ROI) for this operation:
    #   ROI starts at the current time plus the lower bound of the operator
    #   while the ROI ends at the current time plus the upper bound, or the
    #   largest timestamp in the trace (T_MAX - 1 since T_MAX is the
    #   number of timesteps), and since python's range operator excludes
    #   the upper end of the range, we add one.
    #
    # Invarient: max(temporal_roi(interval, T_MAX)) < T_MAX
    roi = range(i+interval[0], min(i+interval[1], T_MAX-1)+1)
    assert((len(roi) == 0) or (max(roi) < T_MAX))
    return roi

def mltl_not_oracle(signal, interval, T_MAX):
    trace = set()
    for i in range(T_MAX):
        if not i in signal:
            trace.add(i)
    return trace

def mltl_and_oracle(signal, interval, T_MAX):
    left_signal, right_signal = signal
    trace = set()
    for i in range(T_MAX):
        if (i in left_signal) and (i in right_signal):
            trace.add(i)
    return trace

def mltl_global_oracle(signal, interval, T_MAX):
    # Returns a set of timesteps where the given signal holds over the offset
    # interval gives, that is ...
    trace = set()
    for i in range(T_MAX):
        # Python for-else checks all elemetns of the ROI, but only runs the
        # the else clause if the loop was not exited with a break
        for j in temporal_roi(i, interval, T_MAX):
            if not j in signal:
                # Here the signal did not hold in the ROI, thus we don't hold
                # Breaking the for loop prevent the else clause from executing
                break
        else:
            # Here the signal held at all steps of the ROI, thus we hold too
            trace.add(i)
    return trace

def mltl_until_oracle(signal, interval, T_MAX):
    left_signal, right_signal = signal
    trace = set()
    for i in range(T_MAX):
        for j in temporal_roi(i, interval, T_MAX):
            if j in right_signal:
                for k in temporal_roi(i, interval, j):
                    if k not in left_signal:
                        break
                else:
                    trace.add(i)
                    break
    return trace


atom = Operator('atom', 0, 'any', False, "(a{})", None)
operators = [
    Operator('not',    1, 'future', False,
             "(! {})", mltl_not_oracle),
    Operator('and',    2, 'future', False,
             "({} & {})", mltl_and_oracle),
    Operator('global', 1, 'future', True,
             "(G[{},{}] {})", mltl_global_oracle),
    Operator('until',  2, 'future', True,
             "(({}) U[{},{}] ({}))", mltl_until_oracle),
]

# Limits:
#   - J_MAX: Maximum bound in any temporal interval, i.e. bounds range from [0,0] to [J,J]
#   - D_MAX: Maximum number of nested operators in the formula AST, i.e. 0 is just an atomic
#   - A_MAX: Maximum number of atomics to generate, None to disable limit, 0 to disable trace generation, i.e. formula gen only
#   - T_MAX: Number of timesteps to generate
# J_MAX = 1# 2
# D_MAX = 2# 3
# A_MAX = 100# 2
# T_MAX = 2# 8

# assert(T_MAX > J_MAX)


# Lengths:
#   - J_LEN: The number of temporal intervals. Since the lower bound must be
#            less than or equal to the upperbound, this is a combination
#            choose 2 with replacement of the integers {0, ..., J_MAX}
#            J_LEN = (J_MAX+1) * (J_MAX+2) / 2 (simplified from multichoose 2)
#   - O_LEN: The number of availabe operators
#   - F_LEN: The number of formulas ..., a geometric series 
#            F_LEN = A_LEN * ((1 - (O_LEN**(D_MAX + 1))) / (1 - O_LEN))
#   - T_LEN: The number of input signals, a double premutation with replacement
#            We can choose T or F for each atomic, at each timestep, thefore
#            T_LEN = (2 ^ A_LEN) ^ T_MAX
#
# Note: Max vs range ... 
# J_LEN = (J_MAX+1) * (J_MAX+2) // 2
# T_LEN = (2**A_LEN)**T_MAX
# O_LEN = sum([x.arity * (J_LEN if x.temporal else 1) for x in operators])
# F_LEN = A_LEN * ((1 - (O_LEN**(D_MAX + 1))) // (1 - O_LEN))


def formulas(depth):
    choices = [atom] + [op for op in operators if depth > 0]
    for op in choices:
        yield from zip(repeat(op), product(formulas(depth-1), repeat=op.arity))

def temporalize(formula, j_max):
    op, children = formula
    if op.temporal and op.interval is None:
        for interval in combinations_with_replacement(range(j_max+1), 2):
            sub_op = op._replace()
            sub_op.interval = interval
            if sub_op.arity == 1:
                yield from zip(repeat(sub_op), [(x,) for x in temporalize(children[0], j_max)])
            elif sub_op.arity == 2:
                yield from zip(repeat(sub_op), product(temporalize(children[0], j_max), temporalize(children[1], j_max)))
    elif op.arity == 1:
        yield from zip(repeat(op), [(x,) for x in temporalize(children[0], j_max)])
    elif op.arity == 2:
        yield from zip(repeat(op), product(temporalize(children[0], j_max), temporalize(children[1], j_max)))
    else:
        yield formula

def formula_max_depth(formula):
    op, children = formula
    return 0 if (op.arity == 0) else 1 + max([formula_max_depth(x) for x in children], default=0)

def count_atoms(formula):
    op, children = formula
    return 1 if (op.arity == 0) else sum((count_atoms(x) for x in children))

def assign_atoms(formula, assignments):

    assign = iter(assignments)
    def _recurisve(formula, asn_itr):
        op, children = formula
        if op.arity == 0:
            return (op, (next(assign), ))
        elif op.arity == 1:
            return (op, (_recurisve(children[0], asn_itr),))
        elif op.arity == 2:
            return (op,
            (_recurisve(children[0], asn_itr),
            _recurisve(children[1], asn_itr)))

    # print(f"Assigning {assignments} to {formula}...")
    res = _recurisve(formula, assign)
    # print(res)
    return res

def max_signal(formula):
    op, children = formula
    return children[0] if (op.arity == 0) else max((max_signal(x) for x in children))

def partition(length, limit=0):
    limit = length if limit == 0 else limit
    res = [0] * length
    while True:
        yield res
        for index in range(length-1, -1, -1):
            if res[index] < min(index, limit-1) and res[index] in res[:index]:
                res[index] += 1
                res[index+1:] = [0] * len(res[index+1:])
                break
        else:
            break

def atomize(formula, a_max):
    num_atoms = count_atoms(formula)
    for asignment in partition(num_atoms, a_max):
        yield assign_atoms(formula, asignment)

def count_intervals(formula):
    op, children = formula
    if op.arity == 0:
        res = 0
    elif op.arity == 1:
        res = count_intervals(children[0])
    elif op.arity == 2:
        res = count_intervals(children[0]) + count_intervals(children[1])

    if op.temporal:
        res = res +1

    return res

@lru_cache(maxsize=None)
def depth_size(depth):
    if depth == 0:
        return 1
    else:
        f_prev = depth_size(depth - 1)
        return 1 + (2*f_prev) + (2 * (f_prev**2))

@lru_cache(maxsize=None)
def depth_size_with_temporal(depth, j_max):
    if depth == 0:
        return 1
    else:
        j = (j_max+1) * (j_max+2) // 2
        f_prev = depth_size_with_temporal(depth - 1, j_max)
        return 1 + ((j+1)*f_prev) + ((j+1)*(f_prev**2))

@lru_cache(maxsize=None)
def depth_size_by_leaves(depth, j, num_leaf, output=False):
    if output: print(f"\t\t{depth} {num_leaf}")
    if (depth == 0) and (num_leaf == 1):
        return 1
    elif (depth == 0) and (num_leaf != 1):
        # print(f"\t\t0 ways to make {num_leaf} with {depth} operators")
        return 0
    else:
        ops = comb(j+2,2) + 1

        foo = depth_size_by_leaves(0,j,num_leaf)
        if output: print(f"\t\t\t{foo}")

        foo += ops * depth_size_by_leaves(depth-1,j, num_leaf, output=False)
        if output: print(f"\t\t\t{foo}")
        # print(f"\t\t{foo} ways to make {num_leaf} with a unary and {depth-1} operators")
        for i in range(num_leaf+1):
            bar = depth_size_by_leaves(depth-1,j,num_leaf-i, output=False)
            baz = depth_size_by_leaves(depth-1,j,i, output=False)
            if output: print(f"\t\t\t{i} {bar} {baz} {bar * baz}")
            foo += ops * (bar * baz)
        # print(f"\t\t{foo} ways to make {num_leaf} with a any op and {depth-1} operators")
        if output: print(f"\t\t{depth} {num_leaf} <{ops}>: {foo}")
        return foo
        # print(f"\t\t{depth_size_by_leaves(depth-1, num_leaf)} ways to make {num_leaf} from {depth} with a unary operator")
        # return (depth_size_by_leaves(depth-1, num_leaf)) + (sum(depth_size_by_leaves(depth-1,num_leaf-i) * depth_size_by_leaves(depth-1,i) for i in range(1,num_leaf-1)))

def depth_count():
    for depth in range(4):
        size = depth_size(depth)
        print(f"[{depth}]: {size} - {depth_size_with_temporal(depth, J_MAX)}")
        nesting = [0] * (2**depth)
        atoms = [0] * (2**depth)
        for template in tqdm(formulas(depth), total=size, leave=False):
            # print(template)
            # total += sum(1 for _ in temporalize(template,J_MAX))
            # index = count_intervals(template)
            # nesting[index] +=1
            # if index == (2**depth)-1:
            #     print(template)
            atoms[count_atoms(template)-1] += 1
            # for formula in temporalize(template,J_MAX):
            #     atoms[count_atoms(formula)-1] += 1
        for index, count in enumerate(atoms):
                print(f"\t{index+1}: {count} ({depth_size_by_leaves(depth,J_MAX, index+1)})")
                # assert(depth_size_by_leaves(depth, index+1) == count)


        # for index in range(2**depth):
        #     print(f"\t{index}: {nesting[index]}")

        # assert(total == depth_size_with_temporal(depth, J_MAX))

        # print(f"\tTemporalized: {sum(1 for _ in [temporalize(x,3) for x in formulas(depth)])}")

# Formula
#

def gen_specs(conf):
    for depth in range(conf.max_depth + 1) if conf.cumulative else [conf.max_depth]:
        for template in formulas(depth):
            if formula_max_depth(template) != depth: continue
            for formula in temporalize(template, conf.max_interval):
                for spec in atomize(formula, conf.max_atoms):
                    yield spec

def gen_signals(spec, conf):
    for signal in product(product([0,1], repeat=min(max_signal(spec)+1, conf.max_atoms) if conf.max_atoms > 0 else max_signal(spec)+1), repeat=conf.max_time):
        yield signal

def c2po_compile(spec, tmpdir):

    with open(tmpdir+'/formula.mltl', 'w', newline='') as mltlfile:
        mltlfile.write(spec[0].print(spec[1])+"\n")

    try:
        subprocess.run(f"python3 {C2PO_PATH}/c2po.py --output {tmpdir}/spec.bin -bz {tmpdir}/formula.mltl", shell=True, capture_output=True, check=True)
    except subprocess.CalledProcessError as e:
        print(e.stderr)
        raise e

    return tmpdir + "/spec.bin"

def r2u2_monitor(signal, tmpdir):
    with open(tmpdir+'/signal.csv', 'w', newline='') as csvfile:
        csvwriter = csv.writer(csvfile)
        for row in signal:
            csvwriter.writerow(row)

    try:
        subprocess.run(f"{R2U2_PATH}/r2u2 {tmpdir}/spec.bin {tmpdir}/signal.csv > {tmpdir}/R2U2.log", shell=True, capture_output=True, check=True)
    except subprocess.CalledProcessError as e:
        print(e.stderr)
        raise e

    with open(tmpdir+'/R2U2.log') as logfile:
        trace = set()
        t_next = 0
        for line in logfile:
            result = re.match(r"^0:(?P<time>[0-9]+),(?P<verdict>[TF])$", line).groups()
            if result[1] == 'T':
                [trace.add(x) for x in range(t_next, int(result[0]) + 1)]
            t_next = int(result[0]) + 1

    return trace

def consult_oracle(spec, signal, t_max):
    op, children = spec
    if op.arity == 0:
        return set([i for i in range(t_max) if signal[i][children[0]]])
    elif op.arity == 1:
        return op.oracle(consult_oracle(children[0], signal, t_max), op.interval if (op.temporal) else None, t_max)
    elif op.arity == 2:
        return op.oracle([consult_oracle(child, signal, t_max) for child in children], op.interval if (op.temporal) else None, t_max)

def check_r2u2():
    pass

# def B(n):
    # if (n==0): return 1
    # for k in range(0,n):
        # print(f"\t\t\tB({n}), k={k}: (n k){comb(n,k)} B={sum(comb(n,k) * B(k) for k in range(0,n))}")
    # return sum(comb(n,k) * B(k) for k in range(0,n))
# f=lambda n,k=0:n<1or k*f(n-1,k)+f(n-1,k+1)

@lru_cache(maxsize=None)
def sn2k(elements, partitions):
    if (elements == 0) or (partitions == 0): return 0
    if (elements == partitions): return 1
    return (partitions * sn2k(elements-1,partitions)) + sn2k(elements-1, partitions-1)

def total_test_cases(conf):
    total = 0
    for num_atoms in range(1,(2**conf.max_depth)+1):
        # print(f"\t{num_atoms} Atoms, {depth_size_by_leaves(conf.max_depth,conf.max_interval,num_atoms)} specs")
        for num_parts in range(1,(min(num_atoms, conf.max_atoms) if conf.max_atoms > 0 else num_atoms)+1):
            # print(f"\t\t{num_parts} partitions, {sn2k(num_atoms, num_parts)} assignments, {(2**num_parts)**conf.max_time} signals")
            total += depth_size_by_leaves(conf.max_depth,conf.max_interval,num_atoms) * sn2k(num_atoms, num_parts) * ((2**num_parts)**conf.max_time)

        # print(f"\t{num_atoms}: {depth_size_by_leaves(D,num_atoms)} {f(num_atoms)} {(2**num_atoms)**T}")
    return total if (conf.cumulative or (conf.max_depth == 0)) else (total - total_test_cases(conf._replace(max_depth=conf.max_depth-1,cumulative=True)))

def count_tests(conf):
    cases = 0
    specs = 0
    # for template in formulas(depth):
    #     for formula in temporalize(template, j):
    #         for spec in atomize(formula, a):
    for spec in gen_specs(conf):
                # print(f"{spec}")
                specs += 1
                signals = 0
                for signal in product(product([0,1], repeat=min(max_signal(spec)+1, conf.max_atoms) if conf.max_atoms > 0 else max_signal(spec)+1), repeat=conf.max_time):
                    # print(f"\t{signal}")
                    signals += 1
                    cases += 1
                # print(f"\t\tS({min(max_signal(spec)+1, A_MAX)}) = {signals}\t{spec}")
    # if cases != total_test_cases(conf):
    print(f"{conf.max_depth}: {specs} {cases} ({total_test_cases(conf)})")
    assert(cases == total_test_cases(conf))

def enum_tests():
    for d in range(5):
        for j in range(4):
            for t in range(9):
                print(f"{d},{j},{t} = {total_test_cases(d,j,t)}")

def main(conf):
    bar = tqdm(total=total_test_cases(conf), leave=True)
    fault_count = 0
    faults = []
    with tempfile.TemporaryDirectory() as tmpdir:
        for spec in gen_specs(conf):
            # print(f"{signal}")
            c2po_compile(spec, tmpdir)
            for signal in gen_signals(spec, conf):
                # print(f"\t{signal}")
                r2u2_trace = r2u2_monitor(signal, tmpdir)
                oracle_trace = consult_oracle(spec, signal, conf.max_time)
                # print(f"\t\t{r2u2_trace}")
                # print(f"\t\t{oracle_trace}")
                if not (r2u2_trace <= oracle_trace):
                    fault_count += 1
                    print(f"{spec}\n\tAtom: {signal}\n\tOrcl: {oracle_trace}\n\tR2U2: {r2u2_trace}")
                bar.update(1)
    bar.close()
    print(f"Total faults: {fault_count}")

if __name__ == '__main__':
    # conf = TestConfig(2,2,0,6,True)
    conf = TestConfig(2,1,2,6,True)
    print(conf)
    main(conf)
    # print(total_test_cases(conf))
    # count_tests(conf)

    # for settings in product(range(4), repeat=4):
    #     conf = TestConfig(*settings, True)
    #     print(conf)
    #     main(conf)
    # depth_count()
    #     print(conf)
    #     count_tests(conf)
    #     conf = TestConfig(*settings, False)
    #     print(conf)
    #     count_tests(conf)
    # enum_tests()
    # for i in range(11):
    #     print(f"{i}: {total_test_cases(i,10,10)}")
    # for n in range(5):
    #     for i in range(1,(2**n)+1):
    #         print(f"{n,i}: {depth_size_by_leaves(n, i)} v.s. {F(n,J_MAX,i)}")
    #         assert(depth_size_by_leaves(n, i, output=True) == F(n,J_MAX,i))
    #     depth_size_by_leaves(n,J_MAX,)

# for a_num in range(1,6):
#     print(f"{a_num}: {sum(1 for _ in partition(a_num))}")
#     for lim in range(a_num-1,0,-1):
#         print(f"\t{lim}: {sum(1 for _ in partition(a_num, limit=lim))}")
#         [print(f"\t\t{x}") for x in partition(a_num, limit=lim)]

    # print(f"{depth}")
    # print(f"\tTemplates: {sum(1 for _ in formulas(depth))}")
    # print(f"\tFormula: {sum(1 for _ in chain(temporalize(tem, J_MAX) for tem in cooler_formulas(depth)))}")
    # print([x for x in chain(temporalize(tem, J_MAX) for tem in cooler_formulas(depth))])
    # for template in cooler_formulas(depth):
    #     print(f"\t{template}")
    #     for formula in temporalize(template, J_MAX):
    #         print(f"\t\t{formula}")
    # print(f"\tFormulas: {sum(1 for _ in [temporalize(x, J_MAX) for x in cooler_formulas(depth)])}")
          # \n\tFormulas: {sum(1 for _ in temporalize([x for x in cooler_formulas(depth)], J_MAX))}")
    # for x in cooler_formulas(depth):
    # [print(f"\t{x}") for x in cooler_formulas(depth)]
