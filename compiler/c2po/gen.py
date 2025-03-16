from typing import cast
import sys

from c2po import cpt

TAB = "    "

def ceildiv(a: int, b: int) -> int:
    return -(a // -b)

def hexlit(value: int, word_size: int) -> str:
    return f"{value:#0{(word_size // 8) * 2 + 2}x}"

def gen_code(formula: cpt.Expression, context: cpt.Context, word_size: int) -> str:

    # formula = cpt.unroll_untils(formula, context)

    def shift(val: str, amt: int) -> str:
        return val if amt == 0 else f"({val} << {amt})" if amt > 0 else f"({val} >> {-amt})"
    
    # def singleton() -> str:
    #     nonlocal word_size
    #     return (
    #         f"(({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[child]}] << {i % word_size}) | "
    #         f"({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead - 1})%{size[child]}] >> {word_size - (i % word_size)}))" 
    #     )

    def gen_compute_expr_code_new(
        expr: cpt.Expression,
        fid: dict[cpt.Expression, str],
        size: dict[cpt.Expression, int],
        word_wpd: dict[cpt.Expression, int],
        tau: str,
    ) -> str:
        nonlocal word_size
        if isinstance(expr, cpt.Signal):
            return f"{TAB*2}{fid[expr]}[{tau}%{size[expr]}] = {str(expr)}[{tau}];\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return (
                f"{TAB}{fid[expr]}[({tau}-{word_wpd[expr]})%{size[expr]}] = "
                f"~ {fid[expr.children[0]]}[({tau}-{word_wpd[expr]})%{size[expr]}];\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return (
                f"{TAB}{fid[expr]}[({tau}-{word_wpd[expr]})%{size[expr]}] = "
                f"{' & '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})%{size[c]}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return (
                f"{TAB}{fid[expr]}[({tau}-{word_wpd[expr]})%{size[expr]}] = "
                f"{' | '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})%{size[c]}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            words = []
            for i in range(interval.lb, interval.ub + 1):
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words += [f"{fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[child]}]"]
                    continue
                words += [ 
                    f"(({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[child]}] << {i % word_size}) | "
                    f"({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead - 1})%{size[child]}] >> {word_size - (i % word_size)}))" 
                ]
            return f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})%{size[expr]}] |= {' | '.join(words)};\n"
            # interval = cast(cpt.TemporalOperator, expr).interval
            # child = expr.children[0]
            # updates = []
            # for i in range(interval.lb // word_size, ((word_size - 1) + interval.ub) // word_size + 1):
            #     low = min(max(interval.lb - word_size * i, -(word_size-1)), word_size-1) 
            #     high = min(max(interval.ub - word_size * i, -(word_size-1)), word_size-1)
            #     dir = 1

            #     print(f"low: {low}, high: {high}", file=sys.stderr)

            #     if low < 0:
            #         tmp = low
            #         low = high
            #         high = tmp
            #         dir = -1
                    
            #     print(f"low: {low}, high: {high}, dir: {dir}", file=sys.stderr)
            #     high = high+1 if high>0 else high-1

            #     words = [shift(f"{fid[child]}[({tau}-{word_wpd[child]})%{size[child]}]", j) for j in range(low, high, dir)]
            #     updates.append(
            #         f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[child] + i})%{size[expr]}] |= {' | '.join(words)};\n"
            #     )
            # return "".join(updates)
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            words = []
            for i in range(interval.lb, interval.ub + 1):
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words += [f"{fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[child]}]"]
                    continue
                words += [ 
                    f"(({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[child]}] << {i % word_size}) | "
                    f"({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead - 1})%{size[child]}] >> {word_size - (i % word_size)}))" 
                ]
            return f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})%{size[expr]}] |= {' & '.join(words)};\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lhs = expr.children[0]
            rhs = expr.children[1]
            word_lookahead = interval.ub // word_size
            if interval.ub % word_size == 0:
                words = (
                    f"{fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[rhs]}]"
                )
            else:
                words = (
                    f"(({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[rhs]}] << {interval.ub % word_size}) | "
                    f"({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead - 1})%{size[rhs]}] >> {word_size - (interval.ub % word_size)}))" 
                )
            for i in range(interval.ub - 1, interval.lb - 1, -1):
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words = (
                        f"({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[rhs]}] "
                        " | "
                        f"({fid[lhs]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[lhs]}] "
                        " & "
                        + words 
                    )
                    continue
                words = (
                    f"((({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[rhs]}] << {i % word_size}) | "
                    f"({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead - 1})%{size[rhs]}] >> {word_size - (i % word_size)}))" 
                    " | "
                    f"((({fid[lhs]}[({tau}-{word_wpd[expr] - word_lookahead})%{size[lhs]}] << {i % word_size}) | "
                    f"({fid[lhs]}[({tau}-{word_wpd[expr] - word_lookahead - 1})%{size[lhs]}] >> {word_size - (i % word_size)}))" 
                    " & "
                    + words 
                )
            return f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})%{size[expr]}] |= {words}{')'*((interval.ub-interval.lb-1)*2+2)};\n"
        
        return ""

    def gen_compute_expr_code_begin(
        expr: cpt.Expression,
        fid: dict[cpt.Expression, str],
        size: dict[cpt.Expression, int],
        word_wpd: dict[cpt.Expression, int],
        tau: int,
    ) -> str:
        nonlocal word_size
        if isinstance(expr, cpt.Signal):
            return f"{TAB}{fid[expr]}[{tau % size[expr]}] = {str(expr)}[{tau}];\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return (
                f"{TAB}{fid[expr]}[({tau-word_wpd[expr]})%{size[expr]}] = "
                f"~ {fid[expr.children[0]]}[({tau-word_wpd[expr]})%{size[expr]}];\n"
            ) if word_wpd[expr] <= tau else ""
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return (
                f"{TAB}{fid[expr]}[({tau-word_wpd[expr]})%{size[expr]}] = "
                f"{' & '.join([f'{fid[c]}[({tau-word_wpd[expr]})%{size[c]}]' for c in expr.children])};\n"
            ) if word_wpd[expr] <= tau else ""
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return (
                f"{TAB}{fid[expr]}[({tau-word_wpd[expr]})%{size[expr]}] = "
                f"{' | '.join([f'{fid[c]}[({tau-word_wpd[expr]})%{size[c]}]' for c in expr.children])};\n"
            ) if word_wpd[expr] <= tau else ""
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            if tau - word_wpd[expr] < 0:
                return ""
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            words = []
            for i in range(interval.lb, interval.ub + 1):
                # each element of word is an expression representing a word of F[a,a] phi
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words += [f"{fid[child]}[{(tau - word_wpd[expr] + word_lookahead) % size[child]}]"]
                    continue
                words += [ 
                    f"(({fid[child]}[{(tau - word_wpd[expr] + word_lookahead) % size[child]}] << {i % word_size}) | "
                    f"({fid[child]}[{(tau - word_wpd[expr] + word_lookahead + 1) % size[child]}] >> {word_size - (i % word_size)}))" 
                ]
            return f"{TAB}{fid[expr]}[{(tau - word_wpd[expr]) % size[expr]}] |= {' | '.join(words)};\n"
            # interval = cast(cpt.TemporalOperator, expr).interval
            # child = expr.children[0]
            # updates = []
            # for i in [
            #     i
            #     for i in range(
            #         interval.lb // word_size,
            #         ((word_size - 1) + interval.ub) // word_size + 1,
            #     )
            #     if tau - word_wpd[child] - i >= 0
            # ]:
            #     low = min(max(interval.lb - word_size * i, -(word_size-1)), word_size-1)
            #     high = min(max(interval.ub - word_size * i, -(word_size-1)), word_size-1) 
            #     words = [
            #         f"({fid[child]}[({tau-word_wpd[child]})%{size[child]}] << {abs(k)})" 
            #         if k >= 0 else 
            #         f"({fid[child]}[({tau-word_wpd[child]})%{size[child]}] >> {abs(k)})"
            #         for k in range(low, high+1)
            #     ]
            #     updates.append(
            #         f"{TAB}{fid[expr]}[({tau - word_wpd[child] - i})%{size[expr]}] |= {' | '.join(words)};\n"
            #     )
            # return "".join(updates)
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            if tau - word_wpd[expr] < 0:
                return ""
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            words = []
            for i in range(interval.lb, interval.ub + 1):
                # each element of word is an expression representing a word of G[a,a] phi
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words += [f"{fid[child]}[{(tau - word_wpd[expr] + word_lookahead) % size[child]}]"]
                    continue
                words += [ 
                    f"(({fid[child]}[{(tau - word_wpd[expr] + word_lookahead) % size[child]}] << {i % word_size}) | "
                    f"({fid[child]}[{(tau - word_wpd[expr] + word_lookahead + 1) % size[child]}] >> {word_size - (i % word_size)}))" 
                ]
            return f"{TAB}{fid[expr]}[{(tau - word_wpd[expr]) % size[expr]}] |= {' & '.join(words)};\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            if tau - word_wpd[expr] < 0:
                return ""
            interval = cast(cpt.TemporalOperator, expr).interval
            lhs = expr.children[0]
            rhs = expr.children[1]
            word_lookahead = interval.ub // word_size
            words = (
                f"(({fid[rhs]}[{(tau-word_wpd[expr] - word_lookahead) % size[rhs]}] << {interval.ub % word_size}) | "
                f"({fid[rhs]}[{(tau-word_wpd[expr] - word_lookahead - 1) % size[rhs]}] >> {word_size - (interval.ub % word_size)}))" 
            )
            for i in range(interval.ub - 1, interval.lb - 1, -1):
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words = (
                        f"({fid[rhs]}[{(tau-word_wpd[expr] - word_lookahead) % size[rhs]}] "
                        " | "
                        f"({fid[lhs]}[{(tau-word_wpd[expr] - word_lookahead) % size[lhs]}] "
                        " & "
                        + words 
                    )
                    continue
                words = (
                    f"((({fid[rhs]}[{(tau-word_wpd[expr] - word_lookahead) % size[rhs]}] << {i % word_size}) | "
                    f"({fid[rhs]}[{(tau-word_wpd[expr] - word_lookahead - 1) % size[rhs]}] >> {word_size - (i % word_size)}))" 
                    " | "
                    f"((({fid[lhs]}[{(tau-word_wpd[expr] - word_lookahead) % size[lhs]}] << {i % word_size}) | "
                    f"({fid[lhs]}[{(tau-word_wpd[expr] - word_lookahead - 1) % size[lhs]}] >> {word_size - (i % word_size)}))" 
                    " & "
                    + words 
                )
            return f"{TAB*2}{fid[expr]}[{(tau-word_wpd[expr]) % size[expr]}] |= {words}{')'*((interval.ub-interval.lb-1)*2+2)};\n"
        return ""

    code = f"""#include <stdio.h>
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>
#include <fcntl.h>

#ifdef DEBUG
void print_binary(uint{word_size}_t value) 
{{
    for (int i = {word_size - 1}; i >= 0; i--) {{
        printf("%{"llu" if word_size == 64 else "u" if word_size == 32 else "hu" if word_size == 16 else "hhu"}", (value >> i) & 1);
    }}
}}
#endif

int main(int argc, char const *argv[]) 
{{
    if (argc != 2) {{
        fprintf(stderr, "usage: %s <trace-file>\\n", argv[0]);
        return 1;
    }}

    int f = open(argv[1], O_RDONLY);
    if (f < 0) {{
        fprintf(stderr, "failed to open file '%s'\\n", argv[1]);
        return 1; 
    }}

    uint64_t num_words;
    read(f, &num_words, 8);

    uint{word_size}_t *trace = mmap(NULL, 8 + ({len(context.signals)} * num_words * {word_size // 8}), PROT_READ, MAP_PRIVATE, f, 0);
    if (trace == NULL) {{ 
        fprintf(stderr, "mmap fail\\n");
        return 1; 
    }}

"""

    for signal in sorted(context.signals.keys()):
        aid = int(signal[1:])
        code += f"{TAB}uint{word_size}_t *{signal} = trace + {'1' if word_size == 64 else '2' if word_size == 32 else '4' if word_size == 16 else '8'} + {aid} * num_words;\n"
    code += "\n"

    fid: dict[cpt.Expression, str] = {}
    size: dict[cpt.Expression, int] = {}
    word_wpd: dict[cpt.Expression, int] = {} # how many words to wait until all children are computed
    word_bpd: dict[cpt.Expression, int] = {} 
    cnt = 0
    for expr in cpt.postorder(formula, context):
        fid[expr] = f"f_{cnt}"
        cnt += 1
        size[expr] = 1

        if isinstance(expr, cpt.TemporalOperator):
            lb = expr.interval.lb
            ub = expr.interval.ub
            size[expr] = max(((word_size - 1) + ub) // word_size - (lb // word_size) + 1, size[expr]) + 1
        
        max_child_word_wpd = max([word_wpd[c] for c in expr.children] + [0])
        ub = (expr.interval.ub if isinstance(expr, cpt.TemporalOperator) else 0)
        word_wpd[expr] = (((word_size - 1) + ub) // word_size) + max_child_word_wpd

        min_child_word_bpd = min([word_bpd[c] for c in expr.children] + [word_wpd[expr]])
        lb = (expr.interval.lb if isinstance(expr, cpt.TemporalOperator) else 0)
        word_bpd[expr] = (lb // word_size) + min_child_word_bpd

        max_child_size = max([size[c] for c in expr.children] + [0])
        for c in expr.children:
            size[expr] = max(size[expr], max_child_size)

    # For now, force all sub-formulas to be of size word_wpd[formula] + 1
    for expr in cpt.postorder(formula, context):
        size[expr] = word_wpd[formula] + 1

    for expr in cpt.postorder(formula, context):
        code += f"{TAB}uint{word_size}_t {fid[expr]}[{size[expr]}] = {{0}}; // {expr}\n"
    code += "\n"

    # First we fill the buffers for each sub-formula until we have sufficient data to start computing the first word of `formula`
    for word in range(word_wpd[formula]):
        for expr in cpt.postorder(formula, context):
            code += gen_compute_expr_code_begin(expr, fid, size, word_wpd, word)
            if word-word_wpd[expr] >= 0:
                code += "#ifdef DEBUG\n"
                code += (
                    f'\t\tprintf("{fid[expr]:3}@%d: ", {word-word_wpd[expr]});\n'
                    f'\t\tprint_binary({fid[expr]}[({word-word_wpd[expr]})%{size[expr]}]); printf("\\n");\n'
                )
                code += "#endif\n"
    code += "\n"

    code += "\tuint64_t word;\n"
    code += f"\tfor (word = {word_wpd[formula]}; word < num_words; ++word) {{\n"
    for expr in cpt.postorder(formula, context):
        code += gen_compute_expr_code_new(expr, fid, size, word_wpd, "word")
        code += "#ifdef DEBUG\n"
        code += (
            f'\t\tprintf("{fid[expr]:3}@%llu: ", word-{word_wpd[expr]});\n'
            f'\t\tprint_binary({fid[expr]}[(word-{word_wpd[expr]})%{size[expr]}]); printf("\\n");\n'
        )
        code += "#endif\n"

    code += "#ifdef OUTPUT\n"
    code += f'\t\tprintf("%0{"16llx" if word_size == 64 else "8x" if word_size == 32 else "4hx" if word_size == 16 else "2hhx"}", {fid[formula]}[(word-{word_wpd[formula]})%{size[formula]}]);\n'
    code += "#endif\n"

    for expr in cpt.postorder(formula, context):
        code += f"\t\t{fid[expr]}[(word+1)%{size[expr]}] = 0;\n"

    code += "\t}\n"

    # After we have reached the end of the trace, go through and compute what we can
    # for word in range(ceildiv(formula.wpd, word_size) - 1, 0, -1):
    #     for expr in cpt.postorder(formula, context):
    #         offset = ceildiv(max([c.wpd for c in expr.children] + [0]), word_size) # how many words to wait until all children are computed
    #         code += gen_compute_expr_code_end(expr, fid, size, offset, f"num_words-{word}")
    # code += "\n"
    
    code += "}"
    print(code)
    return code

def gen_code_exact_trace_len(
    formula: cpt.Expression, context: cpt.Context, word_size: int, trace_len: int
) -> str:
    num_words = ceildiv(trace_len, word_size)

    code = f"""#include <stdio.h>
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>
#include <fcntl.h>

#ifdef DEBUG
void print_binary(uint{word_size}_t value) 
{{
    for (int i = {word_size - 1}; i >= 0; i--) {{
        printf("%{"llu" if word_size == 64 else "lu" if word_size == 32 else "hu" if word_size == 16 else "hhu"}", (value >> i) & 1);
    }}
}}
#endif

int main(int argc, char const *argv[]) 
{{
    if (argc != 2) {{
        fprintf(stderr, "usage: %s <trace-file>\\n", argv[0]);
        return 1;
    }}

    int f = open(argv[1], O_RDONLY);
    if (f < 0) {{
        fprintf(stderr, "failed to open file '%s'\\n", argv[1]);
        return 1; 
    }}

    uint64_t num_words;
    read(f, &num_words, 8);

    uint{word_size}_t *trace = mmap(NULL, {8 + (len(context.signals) * num_words * word_size // 8)}, PROT_READ, MAP_PRIVATE, f, 0);
    if (trace == NULL) {{ 
        fprintf(stderr, "mmap fail\\n");
        return 1; 
    }}

"""

    for signal in sorted(context.signals.keys()):
        aid = int(signal[1:])
        code += f"{TAB}uint{word_size}_t *{signal} = trace + {(1 if word_size == 64 else 2 if word_size == 32 else 4 if word_size == 16 else 8) + aid * num_words};\n"
    code += "\n"

    fid: dict[cpt.Expression, str] = {}
    cnt = 0
    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            fid[expr] = str(expr)
            continue
        fid[expr] = f"f_{cnt}"
        cnt += 1
        code += f"{TAB}uint{word_size}_t {fid[expr]}[{num_words}]; // {expr}\n"

    code += "\n"
    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue

        for word in range(num_words):
            if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
                code += (
                    f"{TAB}{fid[expr]}[{word}] = ~ {fid[expr.children[0]]}[{word}];\n"
                )
            elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
                code += (
                    f"{TAB}{fid[expr]}[{word}] = "
                    f"{' & '.join([f'{fid[c]}[{word}]' for c in expr.children])};\n"
                )
            elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
                code += (
                    f"{TAB}{fid[expr]}[{word}] = "
                    f"{' | '.join([f'{fid[c]}[{word}]' for c in expr.children])};\n"
                )
            elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
                interval = cast(cpt.TemporalOperator, expr).interval
                words = [
                    hexlit((2**word_size) - 1, word_size)
                        if word + (i // word_size) >= num_words else 
                    f"{fid[expr.children[0]]}[{word + (i // word_size)}]"
                        if i % word_size == 0 else 
                    f"(({fid[expr.children[0]]}[{word + (i // word_size)}] << {i % word_size}) | "
                    f"{hexlit((2**word_size) - 1 >> word_size - (i % word_size), word_size)})"
                        if word + (i // word_size) + 1 >= num_words else 
                    f"(({fid[expr.children[0]]}[{word + (i // word_size)}] << {i % word_size}) | "
                    f"(({fid[expr.children[0]]}[{word + (i // word_size) + 1}] & "
                    f"{hexlit(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]), word_size)}) >> "
                    f"{word_size - (i % word_size)}))"
                    for i in range(interval.lb, interval.ub + 1)
                ]
                code += f"{TAB}{fid[expr]}[{word}] = \n{TAB * 2}{f' &\n{TAB * 2}'.join(words)};\n"
            elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
                interval = cast(cpt.TemporalOperator, expr).interval
                words = [
                    hexlit(0, word_size)
                        if word + (i // word_size) >= num_words else 
                    f"{fid[expr.children[0]]}[{word + (i // word_size)}]"
                        if i % word_size == 0 else 
                    f"({fid[expr.children[0]]}[{word + (i // word_size)}] << {i % word_size})"
                        if word + (i // word_size) + 1 >= num_words else 
                    f"(({fid[expr.children[0]]}[{word + (i // word_size)}] << {i % word_size}) | "
                    f"(({fid[expr.children[0]]}[{word + (i // word_size) + 1}] & "
                    f"{hexlit(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]), word_size)}) >> "
                    f"{word_size - (i % word_size)}))"
                    for i in range(interval.lb, interval.ub + 1)
                ]
                code += f"{TAB}{fid[expr]}[{word}] = \n{TAB * 2}{f' |\n{TAB * 2}'.join(words)};\n"
            elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
                interval = cast(cpt.TemporalOperator, expr).interval
                lb = interval.lb
                ub = interval.ub
                lhs = expr.children[0]
                rhs = expr.children[1]
                value = (
                    hexlit(0, word_size)
                        if word + (ub // word_size) >= num_words else 
                    f"{fid[rhs]}[{word + (ub // word_size)}]"
                        if ub % word_size == 0 else 
                    f"({fid[rhs]}[{word + (ub // word_size)}] << {ub % word_size})"
                        if word + (ub // word_size) + 1 >= num_words else 
                    f"(({fid[rhs]}[{word + (ub // word_size)}] << {ub % word_size}) | "
                    f"(({fid[rhs]}[{word + (ub // word_size) + 1}] & "
                    f"{hexlit(sum([2**j for j in range(word_size - 1, word_size - (ub % word_size) - 1, -1)]), word_size)}) >> "
                    f"{word_size - (ub % word_size)}))"
                )
                for i in range(ub - 1, lb - 1, -1):
                    value = (
                        "("
                        + (
                            hexlit(0, word_size)
                                if word + (i // word_size) >= num_words else 
                            f"({fid[rhs]}[{word + (i // word_size)}] << {i % word_size})"
                                if word + (i // word_size) + 1 >= num_words else 
                            f"(({fid[rhs]}[{word + (i // word_size)}] << {i % word_size}) | "
                            f"({fid[rhs]}[{word + (i // word_size) + 1}] & "
                            f"{hexlit(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]), word_size)}) >> "
                            f"{word_size - (i % word_size)})"
                        )
                        + " | ("
                        + (
                            hexlit(0, word_size)
                                if word + (i // word_size) >= num_words else 
                            f"({fid[lhs]}[{word + (i // word_size)}] << {i % word_size})"
                                if word + (i // word_size) + 1 >= num_words else 
                            f"(({fid[lhs]}[{word + (i // word_size)}] << {i % word_size}) | "
                            f"({fid[lhs]}[{word + (i // word_size) + 1}] & "
                            f"{hexlit(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]), word_size)}) >> "
                            f"{word_size - (i % word_size)})"
                        )
                        + " & "
                        + value
                    )
                code += f"{TAB}{fid[expr]}[{word}] = \n{TAB * 2}{value}{')' * (ub - lb + 1)};\n"
            else:
                raise ValueError(f"Unimplemented for bvmon code gen {type(expr)}")

        code += "\n"

    code += "\n#ifdef DEBUG\n"
    code += "\n\n".join(
        [
            (
                f'\tprintf("{fid[expr]:3}: ");\n'
                + "\n".join(
                    [
                        f'\tprint_binary({fid[expr]}[{word}]); printf(" ");'
                        for word in range(num_words)
                    ]
                )
                + '\n\tprintf("\\n");'
            )
            for expr in cpt.postorder(formula, context)
        ]
    )
    code += "\n#endif\n"

    code += "\n}"
    print(code)
    return code


"""
    After filling the buffers, we can compute normally for the rest of the trace.

    - We do not want to compute values for words past the end of the trace, so we stop once start
      indexing the trace past this point.
    - If num_words=N, then the final value we compute for a formula Phi will require indexing a
      proposition at N-1.
    - Consider the formula Phi=F[20,20]p with word_size=8 and num_words=5.
    - To compute the value for Phi[0], we have to compute Phi at each bit 0 thru 7. For bit 0, we
      take the 20th bit of p, for bit 1 take the 21st bit of p, and so on thru for bit 7 which is
      the 27th bit of p.

        Let P[i] be the ith word of P, P`i be the ith bit of P, and P[i]`j be the jth bit of the ith word of P
        Phi[0]`0 = p`20 = p[2]`4
        Phi[0]`1 = p`21 = p[2]`5
        Phi[0]`2 = p`22 = p[2]`6
        Phi[0]`3 = p`23 = p[2]`7
        Phi[0]`4 = p`24 = p[3]`0
        Phi[0]`5 = p`25 = p[3]`1
        Phi[0]`6 = p`26 = p[3]`2
        Phi[0]`7 = p`27 = p[3]`3

    - The 20th bit of p is in word 2 (since 20 // 8 = 2), while the 27th bit is in word 3. (since
      27 // 8 = 3). So, bits 0-3 use word 2 of p and bits 4-7 use word 3 of p.
    - So for word w, the max word indexed in p will be w+3.
    - Since we have 5 words, that means we can compute up to Phi[1] (computed the w in w+3=num_words-1)

    Consider Phi=F[16,16]p.
        Phi[0]`0 = p`16 = p[2]`0
        Phi[0]`1 = p`17 = p[2]`1
        Phi[0]`2 = p`18 = p[2]`2
        Phi[0]`3 = p`19 = p[2]`3
        Phi[0]`4 = p`20 = p[2]`4
        Phi[0]`5 = p`21 = p[2]`5
        Phi[0]`6 = p`22 = p[2]`6
        Phi[0]`7 = p`23 = p[2]`7

    - For word w, the max word indexed in p will be w+2.
    - Generally, for a formula with worst-case propagation delay `wpd`, the max word indexed for
      any proposition of the formula at word `w` will be w + ceildiv(wpd, word_size)
    - If we know there are exactly N words in the trace, then the final word we compute will be
              N - (ceildiv(wpd, word_size) + 1).
    """




# def gen_compute_expr_code_end(
#     expr: cpt.Expression,
#     fid: dict[cpt.Expression, str],
#     size: dict[cpt.Expression, int],
#     offset: int,
#     i: str,
# ) -> str:
#     nonlocal word_size
#     if isinstance(expr, cpt.Signal):
#         return f"{TAB*2}{fid[expr]}[{i}%{size[expr]}] = {str(expr)}[{i}];\n"
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
#         return (
#             f"{TAB}{fid[expr]}[({i}-{offset})%{size[expr]}] = "
#             f"~ {fid[expr.children[0]]}[({i}-{offset})%{size[expr]}];\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
#         return (
#             f"{TAB}{fid[expr]}[({i}-{offset})%{size[expr]}] = "
#             f"{' & '.join([f'{fid[c]}[({i}-{offset})%{size[c]}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
#         return (
#             f"{TAB}{fid[expr]}[({i}-{offset})%{size[expr]}] = "
#             f"{' | '.join([f'{fid[c]}[({i}-{offset})%{size[c]}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         child = expr.children[0]
#         updates = []
#         for j in range(interval.lb // word_size - 1, ceildiv(interval.ub, word_size)):
#             low = min(
#                 max(interval.lb - word_size * j, -(word_size - 1)), word_size - 1
#             )
#             high = min(
#                 max(interval.ub - word_size * j, -(word_size - 1)), word_size - 1
#             )
#             words = [
#                 f"({fid[child]}[({i}+{j})%{size[child]}] << {abs(k)})"
#                 if k >= 0
#                 else f"({fid[child]}[({i}+{j})%{size[child]}] >> {abs(k)})"
#                 for k in range(low, high + 1)
#             ]
#             updates.append(
#                 f"{TAB * 2}{fid[expr]}[{i}%{size[expr]}] |= {' | '.join(words)};\n"
#             )
#         return "".join(updates)
#     return ""

# def gen_compute_expr_code(
#     expr: cpt.Expression,
#     fid: dict[cpt.Expression, str],
#     size: dict[cpt.Expression, int],
#     offset: int,
# ) -> str:
#     nonlocal word_size
#     if isinstance(expr, cpt.Signal):
#         return f"{TAB}{fid[expr]}[(word+{offset})%{size[expr]}] = {str(expr)}[word+{offset}];\n"
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
#         return (
#             f"{TAB}{fid[expr]}[(word+{offset})%{size[expr]}] = "
#             f"~ {fid[expr.children[0]]}[(word+{offset})%{size[expr]}];\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
#         return (
#             f"{TAB}{fid[expr]}[(word+{offset})%{size[expr]}] = "
#             f"{' & '.join([f'{fid[c]}[(word+{offset})%{size[expr]}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
#         return (
#             f"{TAB}{fid[expr]}[(word+{offset})%{size[expr]}] = "
#             f"{' | '.join([f'{fid[c]}[(word+{offset})%{size[expr]}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         child = expr.children[0]
#         words = [
#             f"{fid[child]}[(word+{(i // word_size) + offset})%{size[child]}]"
#                 if i % word_size == 0 else 
#             f"(({fid[child]}[(word+{(i // word_size) + offset})%{size[child]}] << {i % word_size}) | "
#             f"(({fid[child]}[(word+{(i // word_size) + 1 + offset})%{size[child]}] & "
#             f"{hex(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]))}) >> "
#             f"{word_size - (i % word_size)}))"
#             for i in range(interval.lb, interval.ub + 1)
#         ]
#         return f"{TAB}{fid[expr]}[(word+{offset})%{size[expr]}] = \n{TAB * 3}{f' &\n{TAB * 3}'.join(words)};\n"
#     elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         child = expr.children[0]
#         words = [
#             f"{fid[child]}[(word+{(i // word_size) + offset})%{size[child]}]"
#                 if i % word_size == 0 else 
#             f"(({fid[child]}[(word+{(i // word_size) + offset})%{size[child]}] << {i % word_size}) | "
#             f"(({fid[child]}[(word+{(i // word_size) + 1 + offset})%{size[child]}] & "
#             f"{hex(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]))}) >> "
#             f"{word_size - (i % word_size)}))"
#             for i in range(interval.lb, interval.ub + 1)
#         ]
#         return (
#             f"{TAB}{fid[expr]}[(word+{offset})%{size[expr]}] = {fid[expr]}[(word+{offset})%{size[expr]}] |\n"
#             f"{TAB * 3}{f' |\n{TAB * 3}'.join(words)};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lb = interval.lb
#         ub = interval.ub
#         lhs = expr.children[0]
#         rhs = expr.children[1]
#         w = (
#             f"(({fid[rhs]}[word+{(ub // word_size)}] << {ub % word_size}) | "
#             f"(({fid[rhs]}[word+{(ub // word_size) + 1}] & "
#             f"{sum([2**j for j in range(word_size - 1, word_size - (ub % word_size) - 1, -1)])}) >> "
#             f"{word_size - (ub % word_size)}))"
#         )
#         for b in range(ub - 1, lb - 1, -1):
#             w = (
#                 "("
#                 + (
#                     f"(({fid[rhs]}[word+{(b // word_size)}] << {b % word_size}) | "
#                     f"({fid[rhs]}[word+{(b // word_size) + 1}] & "
#                     f"{sum([2**j for j in range(word_size - 1, word_size - (b % word_size) - 1, -1)])}) >> "
#                     f"{word_size - (b % word_size)})"
#                 )
#                 + " | ("
#                 + (
#                     f"(({fid[lhs]}[word+{(b // word_size)}] << {b % word_size}) | "
#                     f"({fid[lhs]}[word+{(b // word_size) + 1}] & "
#                     f"{sum([2**j for j in range(word_size - 1, word_size - (b % word_size) - 1, -1)])}) >> "
#                     f"{word_size - (b % word_size)})"
#                 )
#                 + " & "
#                 + w
#             )
#         return f"{TAB}{fid[expr]}[word] = \n{TAB * 2}{w}{')' * (ub - lb + 1)};\n"
#     else:
#         raise ValueError(f"Unimplemented for bvmon code gen {type(expr)}")

# def gen_compute_expr_code_end_of_trace(
#     expr: cpt.Expression,
#     fid: dict[cpt.Expression, str],
#     word_size: int,
#     offset: int,
# ) -> str:
#     size = ceildiv((expr.aub - expr.alb), word_size) + 1
#     if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
#         return (
#             f"{TAB}{fid[expr]}[(word+{offset})%{size}] = "
#             f"~ {fid[expr.children[0]]}[(word+{offset})%{size}];\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
#         return (
#             f"{TAB}{fid[expr]}[(word+{offset})%{size}] = "
#             f"{' & '.join([f'{fid[c]}[(word+{offset})%{size}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
#         return (
#             f"{TAB}{fid[expr]}[(word+{offset})%{size}] = "
#             f"{' | '.join([f'{fid[c]}[(word+{offset})%{size}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
#         # Let word_size=8, trace_len=24
#         # G[0,15] G[0,15] p

#         # p:  8b 8b 8b
#         # f1: 8b 8b
#         # f2: 8b
#         # p:  8b 8b 8b
#         # f1:    8b 8b
#         # f2:    8b
#         # p:  8b 8b 8b
#         # f1:       8b
#         # f2:       8b

#         child_size = (
#             ceildiv((expr.children[0].aub - expr.children[0].alb), word_size) + 1
#         )
#         interval = cast(cpt.TemporalOperator, expr).interval
#         words = [
#             f"{fid[expr.children[0]]}[(word+{(i // word_size) + offset})%{child_size}]"
#             if i % word_size == 0
#             else f"(({fid[expr.children[0]]}[(word+{(i // word_size) + offset})%{child_size}] << {i % word_size}) | "
#             f"(({fid[expr.children[0]]}[(word+{(i // word_size) + 1 + offset})%{child_size}] & "
#             f"{hex(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]))}) >> "
#             f"{word_size - (i % word_size)}))"
#             for i in range(interval.lb, interval.ub + 1)
#         ]
#         return f"{TAB}{fid[expr]}[(word+{offset})%{size}] = \n{TAB * 2}{f' &\n{TAB * 2}'.join(words)};\n"
#     elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
#         child_size = (
#             ceildiv((expr.children[0].aub - expr.children[0].alb), word_size) + 1
#         )
#         interval = cast(cpt.TemporalOperator, expr).interval
#         words = [
#             f"{fid[expr.children[0]]}[(word+{(i // word_size) + offset})%{child_size}]"
#             if i % word_size == 0
#             else f"(({fid[expr.children[0]]}[(word+{(i // word_size) + offset})%{child_size}] << {i % word_size}) | "
#             f"(({fid[expr.children[0]]}[(word+{(i // word_size) + 1 + offset})%{child_size}] & "
#             f"{hex(sum([2**j for j in range(word_size - 1, word_size - (i % word_size) - 1, -1)]))}) >> "
#             f"{word_size - (i % word_size)}))"
#             for i in range(interval.lb, interval.ub + 1)
#         ]
#         return f"{TAB}{fid[expr]}[(word+{offset})%{size}] = \n{TAB * 2}{f' |\n{TAB * 2}'.join(words)};\n"
#     elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lb = interval.lb
#         ub = interval.ub
#         lhs = expr.children[0]
#         rhs = expr.children[1]
#         w = (
#             f"(({fid[rhs]}[word+{(ub // word_size)}] << {ub % word_size}) | "
#             f"(({fid[rhs]}[word+{(ub // word_size) + 1}] & "
#             f"{sum([2**j for j in range(word_size - 1, word_size - (ub % word_size) - 1, -1)])}) >> "
#             f"{word_size - (ub % word_size)}))"
#         )
#         for b in range(ub - 1, lb - 1, -1):
#             w = (
#                 "("
#                 + (
#                     f"(({fid[rhs]}[word+{(b // word_size)}] << {b % word_size}) | "
#                     f"({fid[rhs]}[word+{(b // word_size) + 1}] & "
#                     f"{sum([2**j for j in range(word_size - 1, word_size - (b % word_size) - 1, -1)])}) >> "
#                     f"{word_size - (b % word_size)})"
#                 )
#                 + " | ("
#                 + (
#                     f"(({fid[lhs]}[word+{(b // word_size)}] << {b % word_size}) | "
#                     f"({fid[lhs]}[word+{(b // word_size) + 1}] & "
#                     f"{sum([2**j for j in range(word_size - 1, word_size - (b % word_size) - 1, -1)])}) >> "
#                     f"{word_size - (b % word_size)})"
#                 )
#                 + " & "
#                 + w
#             )
#         return f"{TAB}{fid[expr]}[word] = \n{TAB * 2}{w}{')' * (ub - lb + 1)};\n"
#     else:
#         raise ValueError(f"Unimplemented for bvmon code gen {type(expr)}")
