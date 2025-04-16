import math
from typing import cast

from c2po import cpt

TAB = "    "
PROFILE = False
BUFSZ2 = True

def ceildiv(a: int, b: int) -> int:
    return -(a // -b)

def hexlit(value: int, word_size: int) -> str:
    return f"{value:#0{(word_size // 8) * 2 + 2}x}"

def gen_code(formula: cpt.Expression, context: cpt.Context, word_size: int, nsigs: int) -> str:
    
    def gen_compute_expr_code_func(
            expr: cpt.Expression,
            fid: dict[cpt.Expression, str],
            size: dict[cpt.Expression, int],
            word_wpd: dict[cpt.Expression, int],
            buffer_size: dict[cpt.Expression, int],
            tau: str,
        ) -> str:
        nonlocal word_size
        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return (
                f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"~ {fid[expr.children[0]]}[({tau} - {word_wpd[expr]}) % {size[expr]}];\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return (
                f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"{' & '.join([f'{fid[c]}[({tau} - {word_wpd[expr]}) % {size[c]}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return (
                f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"{' | '.join([f'{fid[c]}[({tau} - {word_wpd[expr]}) % {size[c]}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            lhs = expr.children[0]
            rhs = expr.children[1]
            return (
                f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"(~ {fid[lhs]}[({tau} - {word_wpd[expr]}) % {size[expr]}]) | {fid[rhs]}[({tau} - {word_wpd[expr]}) % {size[expr]}];\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            interval = cast(cpt.TemporalOperator, expr).interval
            lb = interval.lb
            ub = interval.ub
            child = expr.children[0]
            return (
                f"{TAB * 2}{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"future({fid[child]}, {fid[expr]}_buf, {buffer_size[expr]}, {tau}, {word_wpd[expr]}, {lb}, {ub});\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lb = interval.lb
            ub = interval.ub
            child = expr.children[0]
            return (
                f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"global({fid[child]}, {fid[expr]}_buf, {buffer_size[expr]}, {tau}, {word_wpd[expr]}, {lb}, {ub});\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lb = interval.lb
            ub = interval.ub
            lhs = expr.children[0]
            rhs = expr.children[1]
            return (
                f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"until({fid[lhs]}, {fid[rhs]}, {fid[expr]}_buf_1, {fid[expr]}_buf_2, {buffer_size[expr]}, {tau}, {word_wpd[expr]}, {lb}, {ub});\n"
            )
        
        raise NotImplementedError(f"Operator '{expr.symbol}' not implemented")

    fid: dict[cpt.Expression, str] = {}
    size: dict[cpt.Expression, int] = {}
    word_wpd: dict[cpt.Expression, int] = {} # how many words to wait until all children are computed
    buffer_size: dict[cpt.Expression, int] = {} 

    formula = cpt.decompose_intervals(formula, context)

    cnt = 0
    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            aid = int(str(expr)[1:])
            fid[expr] = f"atomics[{aid}]"
        else:
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

    for expr in cpt.postorder(formula, context):
        # For now, force all sub-formulas to be at least of size word_wpd[formula] + 1
        # Also nice if it's a power of two, then modulo operations become *much* faster

        if BUFSZ2:
            size[expr] = 1 << (word_wpd[formula]).bit_length()
        else:
            size[expr] = word_wpd[formula]

    code = f"""#include <stdio.h>
#include <stdint.h>
#include <string.h>
{'#include <sys/time.h>' if PROFILE else ''}

#define MAXLINE 256
"""

#     code += f"""
# #ifdef DEBUG
# void print_binary(uint{word_size}_t value) 
# {{
#     for (int i = {word_size - 1}; i >= 0; i--) {{
#         printf("%{"llu" if word_size == 64 else "u" if word_size == 32 else "hu" if word_size == 16 else "hhu"}", (value >> i) & 1);
#     }}
# }}
# #endif
# """

    code += f"""
void print_output(uint64_t word, uint64_t offset, uint{word_size}_t value) 
{{
    for (int j = {word_size - 1}; j >= 0; j--) {{
        printf("%llu:%{"llu" if word_size == 64 else "u" if word_size == 32 else "hu" if word_size == 16 else "hhu"}\\n", ((word - offset) * {word_size}) + ({word_size - 1} - j), (value >> j) & 1);
    }}
}}
"""
    
#     for profiling purposes only
#     code += f"""
# int read_inputs(FILE *f, int (*abuf)[{nsigs}], uint{word_size}_t (*atomics)[{nsigs}][{size[formula]}], uint64_t word)
# {{
#     for (int i = 0; i < {word_size}; ++i) {{
#         if(fscanf(f, "{','.join(['%d' for _ in range(nsigs)])}\\n", {', '.join([f'&(*abuf)[{i}]' for i in range(nsigs)])}) != {nsigs}) {{
#             return 1;
#         }}
#         {f'\n{TAB*2}'.join([f'(*atomics)[{i}][word % {size[formula]}] = ((*atomics)[{i}][word % {size[formula]}] << 1) | ((*abuf)[{i}] == 1);' for i in range(nsigs)])}
#     }}
#     return 0;
# }}
# """
    
    log_word_size = int(math.log2(word_size))
    code += f"""
uint{word_size}_t future(uint{word_size}_t *a, uint{word_size}_t *buf, uint64_t nbuf, uint64_t word, uint64_t word_wpd, uint64_t lb, uint64_t ub) 
{{
    uint64_t i, j;
    for(i = 0; i < nbuf; ++i) {{
        buf[i] = ((lb & {word_size - 1}) == 0) ?
            a[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] :
            (
                (a[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] << (lb & {word_size - 1})) | 
                (a[(word - word_wpd + i + (lb >> {log_word_size}) + 1) % {size[formula]}] >> ({word_size} - (lb & {word_size - 1})))
            );
    }}

    for(j = 1; j <= (({word_size // 2} < ((ub - lb + 1) >> 1)) ? {word_size // 2} : (ub - lb + 1) >> 1); j <<= 1) {{
        for(i = 0; i < nbuf - 1; ++i) {{
            buf[i] |= (buf[i] << j) | (buf[i+1] >> ({word_size} - j));
        }}
        buf[i] |= buf[i] << j;
    }}

    for(j = {word_size}; j <= (ub - lb + 1) >> 1; j <<= 1) {{
        for(i = 0; (i + (j >> {log_word_size})) < nbuf; ++i) {{
            buf[i] |= buf[i + (j >> {log_word_size})];
        }}
    }}
  
  return buf[0];
}}

uint{word_size}_t global(uint{word_size}_t *a, uint{word_size}_t *buf, uint64_t nbuf, uint64_t word, uint64_t word_wpd, uint64_t lb, uint64_t ub) 
{{
    uint64_t i, j;
    for(i = 0; i < nbuf; ++i) {{
        buf[i] = ((lb & {word_size - 1}) == 0) ?
            a[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] :
            (
                (a[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] << (lb & {word_size - 1})) | 
                (a[(word - word_wpd + i + (lb >> {log_word_size}) + 1) % {size[formula]}] >> ({word_size} - (lb & {word_size - 1})))
            );
    }}

    for(j = 1; j <= (({word_size // 2} < ((ub - lb + 1) >> 1)) ? {word_size // 2} : (ub - lb + 1) >> 1); j <<= 1) {{
        for(i = 0; i < nbuf - 1; ++i) {{
            buf[i] &= (buf[i] << j) | (buf[i+1] >> ({word_size} - j));
        }}
        buf[i] &= buf[i] << j;
    }}

    for(j = {word_size}; j <= (ub - lb + 1) >> 1; j <<= 1) {{
        for(i = 0; (i + (j >> {log_word_size})) < nbuf; ++i) {{
            buf[i] &= buf[i + (j >> {log_word_size})];
        }}
    }}
    
    return buf[0];
}}

uint{word_size}_t until(uint{word_size}_t *a1, uint{word_size}_t *a2, uint{word_size}_t *buf1, uint{word_size}_t *buf2, uint64_t nbuf, uint64_t word, uint64_t word_wpd, uint64_t lb, uint64_t ub) 
{{
    uint64_t i, j;
    for(i = 0; i < nbuf; ++i) {{
        buf1[i] = ((lb & {word_size - 1}) == 0) ?
            a1[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] :
            (
                (a1[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] << (lb & {word_size - 1})) | 
                (a1[(word - word_wpd + i + (lb >> {log_word_size}) + 1) % {size[formula]}] >> ({word_size} - (lb & {word_size - 1})))
            );
        buf2[i] = ((lb & {word_size - 1}) == 0) ?
            a2[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] :
            (
                (a2[(word - word_wpd + i + (lb >> {log_word_size})) % {size[formula]}] << (lb & {word_size - 1})) | 
                (a2[(word - word_wpd + i + (lb >> {log_word_size}) + 1) % {size[formula]}] >> ({word_size} - (lb & {word_size - 1})))
            );
    }}

    for(j = 1; j <= (({word_size // 2} < ((ub + 1) >> 1)) ? {word_size // 2} : (ub + 1) >> 1); j <<= 1) {{
        for(i = 0; i < nbuf - 1; ++i) {{
            buf2[i] |= buf1[i] & ((buf2[i] << j) | (buf2[i+1] >> ({word_size} - j)));
            buf1[i] &= (buf1[i] << j) | (buf1[i+1] >> ({word_size} - j));
        }}
        buf2[nbuf - 1] |= buf1[nbuf - 1] & (buf2[nbuf - 1] << j);
        buf1[nbuf - 1] &= buf1[nbuf - 1] << j;
    }}

    for(j = {word_size}; j <= (ub + 1) >> 1; j <<= 1) {{
        for(i = 0; (i + (j >> {log_word_size})) < nbuf; ++i) {{
            buf2[i] |= buf1[i] & buf2[i + (j >> {log_word_size})];
            buf1[i] &= buf1[i + (j >> {log_word_size})];
        }}
    }}

    return buf2[0];
}}
"""

    code += """
int main(int argc, char const *argv[]) 
{
    FILE *f;
    if (argc == 1) {
        f = stdin;
    } else if (argc == 2) {
        f = fopen(argv[1], "r");
        if (f == NULL) {
            fprintf(stderr, "failed to open file '%s'\\n", argv[1]);
            return 1; 
        }
    } else {
        fprintf(stderr, "usage: %s [trace-file]\\n", argv[0]);
        return 1;
    }

"""

    # for aid in range(nsigs):
    #     signal = f"a{aid}"
    #     sigsize[signal] = 1 << (word_wpd[formula]).bit_length()
    #     code += f"{TAB}uint{word_size}_t {signal}[{sigsize[signal]}] = {{0}};\n"
    code += f"{TAB}uint{word_size}_t atomics[{nsigs}][{size[formula]}] = {{0}};\n"

    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue
        code += f"{TAB}uint{word_size}_t {fid[expr]}[{size[expr]}] = {{0}}; // {expr}\n"
    code += "\n"

    for expr in cpt.postorder(formula, context):
        if not cpt.is_temporal_operator(expr):
            continue
        expr = cast(cpt.TemporalOperator, expr)
        lb = expr.interval.lb
        ub = expr.interval.ub
        buffer_size[expr] = (((word_size - 1) + ub) // word_size) -  (lb // word_size) + 1
        if cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            code += f"{TAB}uint{word_size}_t {fid[expr]}_buf_1[{buffer_size[expr]}];\n"
            code += f"{TAB}uint{word_size}_t {fid[expr]}_buf_2[{buffer_size[expr]}];\n"
        else:
            code += f"{TAB}uint{word_size}_t {fid[expr]}_buf[{buffer_size[expr]}];\n"

    code += f"""
    uint64_t i, word = 0;
    int abuf[{nsigs}];
    {f'struct timeval stop[{size[formula]}], start[{size[formula]}];' if PROFILE else ''}
    while(1) {{
        for (int i = 0; i < {word_size}; ++i) {{
            if(fscanf(f, "{','.join(['%d' for _ in range(nsigs)])}\\n", {', '.join([f'&abuf[{i}]' for i in range(nsigs)])}) != {nsigs}) {{
                return 0;
            }}
            """ + f'\n{TAB*3}'.join([f'atomics[{i}][word % {size[formula]}] = (atomics[{i}][word % {size[formula]}] << 1) | (abuf[{i}] == 1);' for i in range(nsigs)]) + """
        }
"""
    # for aid in range(nsigs-1):
    #     signal = f"a{aid}"
    #     code += f"{TAB*2}_read(f, &{signal}[word&{sigsize[signal]-1}], {word_size // 8});\n"
    #     if debug:
    #         code += "#ifdef DEBUG\n"
    #         code += (
    #             f'{TAB*2}printf("{signal:3}@%llu: ", word);\n'
    #             f'{TAB*2}print_binary({signal}[word&{sigsize[signal]-1}]); printf("\\n");\n'
    #         )
    #         code += "#endif\n"
    # signal = f"a{nsigs-1}"
    # code += f"{TAB*2}r = _read(f, &{signal}[word&{sigsize[signal]-1}], {word_size // 8});\n"
    # code += f"{TAB*2}if (r == 0) {{ break; }}\n"

    if PROFILE:
         code += f"gettimeofday(&start[word % {size[formula]}], NULL);\n"

    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue
        code += gen_compute_expr_code_func(expr, fid, size, word_wpd, buffer_size, "word")
        # if debug:
        #     code += "#ifdef DEBUG\n"
        #     code += (
        #         f'{TAB*2}printf("{fid[expr]:3}@%llu: ", word-{word_wpd[expr]});\n'
        #         f'{TAB*2}print_binary({fid[expr]}[(word-{word_wpd[expr]})&{size[expr] - 1}]); printf("\\n");\n'
        #     )
        #     code += "#endif\n"

    code += f"\n{TAB*2}if (word >= {word_wpd[formula]}) {{"
    if PROFILE:
        code += f"""
            gettimeofday(&stop[(word - {word_wpd[formula]}) % {size[formula]}], NULL);
            fprintf(stderr, "%llu 0.%06d\\n", word - {word_wpd[formula]}, 
                    stop[(word - {word_wpd[formula]}) % {size[formula]}].tv_usec - start[(word - {word_wpd[formula]}) % {size[formula]}].tv_usec
            );"""
    code += f"""
            printf("%0{"16llx" if word_size == 64 else "8x" if word_size == 32 else "4hx" if word_size == 16 else "2hhx"}\\n", {fid[formula]}[(word - {word_wpd[formula]}) % {size[formula]}]);
        }}
"""

#     code += f"""
#         if (word >= {word_wpd[formula]}) {{
            
#             printf("%0{"16llx" if word_size == 64 else "8x" if word_size == 32 else "4hx" if word_size == 16 else "2hhx"}\\n", {fid[formula]}[(word - {word_wpd[formula]}) % {size[formula]}]);
#         }}
# """

    # code += "#ifdef OUTPUT\n"
    # code += f"{TAB*2}if (word >= {word_wpd[formula]}) {{\n"
    # code += f'{TAB*3}printf("%0{"16llx" if word_size == 64 else "8x" if word_size == 32 else "4hx" if word_size == 16 else "2hhx"}", {fid[formula]}[(word-{word_wpd[formula]})&{size[formula]-1}]);\n'
    # code += f"{TAB*2}}}\n"
    # code += "#endif\n"

    for expr in cpt.postorder(formula, context):
        code += f"{TAB*2}{fid[expr]}[(word + 1) % {size[expr]}] = 0;\n"

    code += """
        word++;
    }
    return 0;
}
"""

    print(code)
    return code


def gen_code_linear(formula: cpt.Expression, context: cpt.Context, word_size: int, nsigs: int, unroll_c: bool, debug: bool) -> str:

    def gen_compute_expr_code_unroll(
        expr: cpt.Expression,
        fid: dict[cpt.Expression, str],
        size: dict[cpt.Expression, int],
        word_wpd: dict[cpt.Expression, int],
        tau: str,
    ) -> str:
        nonlocal word_size
        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"~ {fid[expr.children[0]]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}];\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"{' & '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"{' | '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            words = []
            for i in range(interval.lb, interval.ub + 1):
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words += [f"{fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[child]-1}]"]
                    continue
                words += [ 
                    f"(({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[child]-1}] << {i % word_size}) | "
                    f"({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead - 1})&{size[child]-1}] >> {word_size - (i % word_size)}))" 
                ]
            return f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] |= {' | '.join(words)};\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            words = []
            for i in range(interval.lb, interval.ub + 1):
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words += [f"{fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[child]-1}]"]
                    continue
                words += [ 
                    f"(({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[child]-1}] << {i % word_size}) | "
                    f"({fid[child]}[({tau}-{word_wpd[expr] - word_lookahead - 1})&{size[child]-1}] >> {word_size - (i % word_size)}))" 
                ]
            return f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] |= {' & '.join(words)};\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lhs = expr.children[0]
            rhs = expr.children[1]
            word_lookahead = interval.ub // word_size
            if interval.ub % word_size == 0:
                words = (
                    f"{fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[rhs]-1}]"
                )
            else:
                words = (
                    f"(({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[rhs]-1}] << {interval.ub % word_size}) | "
                    f"({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead - 1})&{size[rhs]-1}] >> {word_size - (interval.ub % word_size)}))" 
                )
            for i in range(interval.ub - 1, interval.lb - 1, -1):
                word_lookahead = i // word_size
                if i % word_size == 0:
                    words = (
                        f"({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[rhs]-1}] "
                        " | "
                        f"({fid[lhs]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[lhs]-1}] "
                        " & "
                        + words 
                    )
                    continue
                words = (
                    f"((({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[rhs]-1}] << {i % word_size}) | "
                    f"({fid[rhs]}[({tau}-{word_wpd[expr] - word_lookahead - 1})&{size[rhs]-1}] >> {word_size - (i % word_size)}))" 
                    " | "
                    f"((({fid[lhs]}[({tau}-{word_wpd[expr] - word_lookahead})&{size[lhs]-1}] << {i % word_size}) | "
                    f"({fid[lhs]}[({tau}-{word_wpd[expr] - word_lookahead - 1})&{size[lhs]-1}] >> {word_size - (i % word_size)}))" 
                    " & "
                    + words 
                )
            return f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = {words}{')'*((interval.ub-interval.lb-1)*2+2)};\n"
        
        return ""

    def gen_compute_expr_code(
        expr: cpt.Expression,
        fid: dict[cpt.Expression, str],
        size: dict[cpt.Expression, int],
        word_wpd: dict[cpt.Expression, int],
        tau: str,
    ) -> str:
        nonlocal word_size
        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"~ {fid[expr.children[0]]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}];\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"{' & '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"{' | '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            ret =  f"{TAB*2}{fid[expr]}_v = 0;\n"
            ret += f"{TAB*2}for (i = {interval.lb}; i <= {interval.ub}; ++i) " "{\n"
            ret += (f"{TAB*3}"
                f"{fid[expr]}_v |= "
                f"((i & {word_size - 1}) == 0) ? {fid[child]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[child]-1}] : "
                f"(({fid[child]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[child]-1}] << (i & {word_size - 1})) | "
                f"({fid[child]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))}) - 1))&{size[child]-1}] >> ({word_size} - (i & {word_size - 1}))));\n" 
                f"{TAB*2}" "}\n"
            )
            ret += f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = {fid[expr]}_v;\n"
            return ret
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            ret =  f"{TAB*2}{fid[expr]}_v = " + hexlit((2**word_size)-1, word_size) + ";\n"
            ret += f"{TAB*2}for (i = {interval.lb}; i <= {interval.ub}; ++i) " "{\n"
            ret += (f"{TAB*3}"
                f"{fid[expr]}_v &= "
                f"((i & {word_size - 1}) == 0) ? {fid[child]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[child]-1}] : "
                f"(({fid[child]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[child]-1}] << (i & {word_size - 1})) | "
                f"({fid[child]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))}) - 1))&{size[child]-1}] >> ({word_size} - (i & {word_size - 1}))));\n" 
                f"{TAB*2}" "}\n"
            )
            ret += f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = {fid[expr]}_v;\n"
            return ret
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lhs = expr.children[0]
            rhs = expr.children[1]
            ret = (
                f"{TAB*2}{fid[expr]}_v = " +
                (
                    f"{fid[rhs]}[({tau} - {word_wpd[expr] - (interval.ub // word_size)})&{size[rhs]-1}];\n"
                    if interval.ub % word_size == 0 else 
                    f"(({fid[rhs]}[({tau} - {word_wpd[expr] - (interval.ub // word_size)})&{size[rhs]-1}] << {interval.ub % word_size}) | "
                    f"({fid[rhs]}[({tau} - {word_wpd[expr] - (interval.ub // word_size) - 1})&{size[rhs]-1}] >> {word_size - (interval.ub % word_size)}));\n"
                )
            )
            ret += f"{TAB*2}for (i = {interval.ub - 1}; {'i < UINT64_MAX' if interval.lb == 0 else f'i >= {interval.lb}'}; --i) " "{\n"
            ret += (
                f"{TAB*3}{fid[expr]}_v &= "
                f"((i & {word_size - 1}) == 0) ? {fid[lhs]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[lhs]-1}] : "
                f"(({fid[lhs]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[lhs]-1}] << (i & {word_size - 1})) |"
                f" ({fid[lhs]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))}) - 1))&{size[lhs]-1}] >> ({word_size} - (i & {word_size - 1}))));\n" 
                f"{TAB*3}{fid[expr]}_v |= "
                f"((i & {word_size - 1}) == 0) ? {fid[rhs]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[rhs]-1}] : "
                f"(({fid[rhs]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))})))&{size[rhs]-1}] << (i & {word_size - 1})) |"
                f" ({fid[rhs]}[({tau} - ({word_wpd[expr]} - (i >> {int(math.log2(word_size))}) - 1))&{size[rhs]-1}] >> ({word_size} - (i & {word_size - 1}))));\n" 
                f"{TAB*2}" "}\n"
            )
            ret += f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = {fid[expr]}_v;\n"
            return ret
        
        return ""

    fid: dict[cpt.Expression, str] = {}
    sigsize: dict[str, int] = {}
    size: dict[cpt.Expression, int] = {}
    word_wpd: dict[cpt.Expression, int] = {} # how many words to wait until all children are computed

    cnt = 0
    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            fid[expr] = str(expr)
        else:
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

    for expr in cpt.postorder(formula, context):
        # For now, force all sub-formulas to be at least of size word_wpd[formula] + 1
        # Also nice if it's a power of two, then modulo operations become *much* faster
        size[expr] = 1 << (word_wpd[formula]).bit_length()

    code = """#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
"""

    code += """
// for profiling --- parse time is shown to be insignificant
ssize_t _read(int fd, void *buf, size_t count)
{
    return read(fd, buf, count);
}

int main(int argc, char const *argv[]) 
{
    if (argc != 2) {
        fprintf(stderr, "usage: %s <trace-file>\\n", argv[0]);
        return 1;
    }

    int f = open(argv[1], O_RDONLY);
    if (f < 0) {
        fprintf(stderr, "failed to open file '%s'\\n", argv[1]);
        return 1; 
    }

    uint64_t num_words;
    _read(f, &num_words, 8);

"""
    for aid in range(nsigs):
        signal = f"a{aid}"
        sigsize[signal] = 1 << (word_wpd[formula]).bit_length()
        code += f"{TAB}uint{word_size}_t {signal}[{sigsize[signal]}] = {{0}};\n"

    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue
        code += f"{TAB}uint{word_size}_t {fid[expr]}[{size[expr]}] = {{0}};\n"
    code += "\n"

    if not unroll_c:
        for expr in cpt.postorder(formula, context):
            if not cpt.is_temporal_operator(expr):
                continue
            code += f"{TAB}uint{word_size}_t {fid[expr]}_v;\n"
        code += f"{TAB}uint64_t i;\n"
        code += "\n"

    code += f"{TAB}uint64_t word;\n"
    code += f"{TAB}for (word = 0; word < num_words; ++word) {{\n"
    for aid in range(nsigs):
        signal = f"a{aid}"
        code += f"{TAB*2}_read(f, &{signal}[word&{sigsize[signal]-1}], {word_size // 8});\n"
        if debug:
            code += "#ifdef DEBUG\n"
            code += (
                f'{TAB*2}printf("{signal:3}@%llu: ", word);\n'
                f'{TAB*2}print_binary({signal}[word&{sigsize[signal]-1}]); printf("\\n");\n'
            )
            code += "#endif\n"
    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue
        if unroll_c:
            code += gen_compute_expr_code_unroll(expr, fid, size, word_wpd, "word")
        else:
            code += gen_compute_expr_code(expr, fid, size, word_wpd, "word")
        if debug:
            code += "#ifdef DEBUG\n"
            code += (
                f'{TAB*2}printf("{fid[expr]:3}@%llu: ", word-{word_wpd[expr]});\n'
                f'{TAB*2}print_binary({fid[expr]}[(word-{word_wpd[expr]})&{size[expr] - 1}]); printf("\\n");\n'
            )
            code += "#endif\n"

    code += "#ifdef OUTPUT\n"
    code += f"{TAB*2}if (word >= {word_wpd[formula]}) {{\n"
    code += f'{TAB*3}printf("%0{"16llx" if word_size == 64 else "8x" if word_size == 32 else "4hx" if word_size == 16 else "2hhx"}", {fid[formula]}[(word-{word_wpd[formula]})&{size[formula]-1}]);\n'
    code += f"{TAB*2}}}\n"
    code += "#endif\n"

    for expr in cpt.postorder(formula, context):
        code += f"{TAB*2}{fid[expr]}[(word+1)&{size[expr] - 1}] = 0;\n"

    code += f"{TAB}}}\n"
    
    # we return the final value computed only so that if -DOUTPUT or -DDEBUG are not defined, then
    # the compiler doesn't just do nothing. (if -DOUTPUT or -DDEBUG are not defined then the
    # compiler doesn't think the program does anything useful, since it will print nothing and
    # return 0 in all cases.)
    code += f"{TAB}return {fid[formula]}[(num_words-1)&{size[formula]-1}];\n"
    code += "}"
    print(code)
    return code


def gen_code_cuda(formula: cpt.Expression, context: cpt.Context, word_size: int, nsigs: int, debug: bool) -> str:

    def gen_compute_expr_code(
        expr: cpt.Expression,
        fid: dict[cpt.Expression, str],
        size: dict[cpt.Expression, int],
        word_wpd: dict[cpt.Expression, int],
        tau: str,
    ) -> str:
        nonlocal word_size
        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"~ {fid[expr.children[0]]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}];\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"{' & '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return (
                f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
                f"{' | '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            return f"""
        cudaMemcpy(dev_{fid[child]}, {fid[child]}, {size[child] * (word_size // 8)}, cudaMemcpyHostToDevice);
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[child]}, dev_{fid[child]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        cub::DeviceReduce::Reduce(
            dev_tmp_storage_{fid[child]}, dev_tmp_storage_{fid[child]}_bytes,
            dev_{fid[child]}_tmp, dev_{fid[expr]}, {interval.ub - interval.lb + 1}, bvor_op, bvor_init
        );
        cudaMemcpy(&{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}], dev_{fid[expr]}, {word_size // 8}, cudaMemcpyDeviceToHost);
"""
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            return f"""
        cudaMemcpy(dev_{fid[child]}, {fid[child]}, {size[child] * (word_size // 8)}, cudaMemcpyHostToDevice);
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[child]}, dev_{fid[child]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        cub::DeviceReduce::Reduce(
            dev_tmp_storage_{fid[child]}, dev_tmp_storage_{fid[child]}_bytes,
            dev_{fid[child]}_tmp, dev_{fid[expr]}, {interval.ub - interval.lb + 1}, bvand_op, bvand_init
        );
        cudaMemcpy(&{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}], dev_{fid[expr]}, {word_size // 8}, cudaMemcpyDeviceToHost);
"""
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lhs = expr.children[0]
            rhs = expr.children[1]
            return f"""
        cudaMemcpy(dev_{fid[lhs]}, {fid[lhs]}, {size[lhs] * (word_size // 8)}, cudaMemcpyHostToDevice);
        cudaMemcpy(dev_{fid[rhs]}, {fid[rhs]}, {size[rhs] * (word_size // 8)}, cudaMemcpyHostToDevice);
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[lhs]}, dev_{fid[lhs]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[rhs]}, dev_{fid[rhs]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        cudaMemcpy({fid[lhs]}_arr, dev_{fid[lhs]}_tmp, {(interval.ub - interval.lb + 1) * (word_size // 8)}, cudaMemcpyDeviceToHost);
        cudaMemcpy({fid[rhs]}_arr, dev_{fid[rhs]}_tmp, {(interval.ub - interval.lb + 1) * (word_size // 8)}, cudaMemcpyDeviceToHost);
        {fid[expr]}_v = {fid[rhs]}_arr[{interval.ub - interval.lb}];
        for (i = {interval.ub - interval.lb - 1}; i != UINT64_MAX; --i) {{
            {fid[expr]}_v &= {fid[lhs]}_arr[i];
            {fid[expr]}_v |= {fid[rhs]}_arr[i];
        }}
        {fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = {fid[expr]}_v;
"""
        return ""

    def gen_compute_expr_code_begin(
        expr: cpt.Expression,
        fid: dict[cpt.Expression, str],
        size: dict[cpt.Expression, int],
        word_wpd: dict[cpt.Expression, int],
        tau: int,
    ) -> str:
        nonlocal word_size
        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return (
                f"{TAB}{fid[expr]}[{(tau - word_wpd[expr]) % size[expr]}] = "
                f"~ {fid[expr.children[0]]}[{(tau - word_wpd[expr]) % size[expr]}];\n"
            ) if word_wpd[expr] <= tau else ""
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return (
                f"{TAB}{fid[expr]}[{(tau - word_wpd[expr]) % size[expr]}] = "
                f"{' & '.join([f'{fid[c]}[{(tau-word_wpd[expr]) % size[c]}]' for c in expr.children])};\n"
            ) if word_wpd[expr] <= tau else ""
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return (
                f"{TAB}{fid[expr]}[{(tau - word_wpd[expr]) % size[expr]}] = "
                f"{' | '.join([f'{fid[c]}[{(tau-word_wpd[expr]) % size[c]}]' for c in expr.children])};\n"
            ) if word_wpd[expr] <= tau else ""
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            return f"""
        cudaMemcpy(dev_{fid[child]}, {fid[child]}, {size[child] * (word_size // 8)}, cudaMemcpyHostToDevice);
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[child]}, dev_{fid[child]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        cub::DeviceReduce::Reduce(
            dev_tmp_storage_{fid[child]}, dev_tmp_storage_{fid[child]}_bytes,
            dev_{fid[child]}_tmp, dev_{fid[expr]}, {interval.ub - interval.lb + 1}, bvor_op, bvor_init
        );
        cudaMemcpy(&{fid[expr]}[{tau - word_wpd[expr] % size[expr]}], dev_{fid[expr]}, {word_size // 8}, cudaMemcpyDeviceToHost);
"""
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            interval = cast(cpt.TemporalOperator, expr).interval
            child = expr.children[0]
            return f"""
        cudaMemcpy(dev_{fid[child]}, {fid[child]}, {size[child] * (word_size // 8)}, cudaMemcpyHostToDevice);
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[child]}, dev_{fid[child]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        cub::DeviceReduce::Reduce(
            dev_tmp_storage_{fid[child]}, dev_tmp_storage_{fid[child]}_bytes,
            dev_{fid[child]}_tmp, dev_{fid[expr]}, {interval.ub - interval.lb + 1}, bvand_op, bvand_init
        );
        cudaMemcpy(&{fid[expr]}[{tau - word_wpd[expr] % size[expr]}], dev_{fid[expr]}, {word_size // 8}, cudaMemcpyDeviceToHost);
"""
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lhs = expr.children[0]
            rhs = expr.children[1]
            return f"""
        cudaMemcpy(dev_{fid[lhs]}, {fid[lhs]}, {size[lhs] * (word_size // 8)}, cudaMemcpyHostToDevice);
        cudaMemcpy(dev_{fid[rhs]}, {fid[rhs]}, {size[rhs] * (word_size // 8)}, cudaMemcpyHostToDevice);
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[lhs]}, dev_{fid[lhs]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        singleton<<<blocksPerGrid, threadsPerBlock>>>(dev_{fid[rhs]}, dev_{fid[rhs]}_tmp, word, {interval.lb}, {interval.ub}, {word_wpd[expr]});
        cudaMemcpy({fid[lhs]}_arr, dev_{fid[lhs]}_tmp, {(interval.ub - interval.lb + 1) * (word_size // 8)}, cudaMemcpyDeviceToHost);
        cudaMemcpy({fid[rhs]}_arr, dev_{fid[rhs]}_tmp, {(interval.ub - interval.lb + 1) * (word_size // 8)}, cudaMemcpyDeviceToHost);
        {fid[expr]}_v = {fid[rhs]}_arr[{interval.ub - interval.lb}];
        for (i = {interval.ub - interval.lb - 1}; i != UINT64_MAX; --i) {{
            {fid[expr]}_v &= {fid[lhs]}_arr[i];
            {fid[expr]}_v |= {fid[rhs]}_arr[i];
        }}
        {fid[expr]}[{tau - word_wpd[expr] % size[expr]}] = {fid[expr]}_v;
"""
        return ""

    fid: dict[cpt.Expression, str] = {}
    sigsize: dict[str, int] = {}
    size: dict[cpt.Expression, int] = {}
    word_wpd: dict[cpt.Expression, int] = {} # how many words to wait until all children are computed
    word_bpd: dict[cpt.Expression, int] = {} 
    max_interval: int = 0

    cnt = 0
    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            fid[expr] = str(expr)
        else:
            fid[expr] = f"f_{cnt}"
            cnt += 1
        size[expr] = 1

        if isinstance(expr, cpt.TemporalOperator):
            lb = expr.interval.lb
            ub = expr.interval.ub
            size[expr] = max(((word_size - 1) + ub) // word_size - (lb // word_size) + 1, size[expr]) + 1
            max_interval = max(max_interval, ub - lb + 1)

        max_child_word_wpd = max([word_wpd[c] for c in expr.children] + [0])
        ub = (expr.interval.ub if isinstance(expr, cpt.TemporalOperator) else 0)
        word_wpd[expr] = (((word_size - 1) + ub) // word_size) + max_child_word_wpd

        min_child_word_bpd = min([word_bpd[c] for c in expr.children] + [word_wpd[expr]])
        lb = (expr.interval.lb if isinstance(expr, cpt.TemporalOperator) else 0)
        word_bpd[expr] = (lb // word_size) + min_child_word_bpd

        max_child_size = max([size[c] for c in expr.children] + [0])
        size[expr] = max(size[expr], max_child_size)

    for expr in cpt.postorder(formula, context):
        # For now, force all sub-formulas to be at least of size word_wpd[formula] + 1
        # Also nice if it's a power of two, then modulo operations become *much* faster
        size[expr] = 1 << (word_wpd[formula]).bit_length()

    code = """#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
#include <cuda_runtime.h>
#include <cub/device/device_reduce.cuh>
"""

    if debug:
        code += f"""
#ifdef DEBUG
void print_binary(uint{word_size}_t value) 
{{
    for (int i = {word_size - 1}; i >= 0; i--) {{
        printf("%{"llu" if word_size == 64 else "u" if word_size == 32 else "hu" if word_size == 16 else "hhu"}", (value >> i) & 1);
    }}
}}
#endif
"""

    code += f"""
struct BitwiseOr
{{
    template <typename T>
    __device__ __forceinline__
    T operator()(const T &a, const T &b) const {{
        return a | b;
    }}
}};

struct BitwiseAnd
{{
    template <typename T>
    __device__ __forceinline__
    T operator()(const T &a, const T &b) const {{
        return a & b;
    }}
}};

__global__ void singleton(const uint{word_size}_t *in, uint{word_size}_t *out,
                        const uint64_t word, const uint64_t low, const uint64_t high, const uint64_t word_wpd) {{
    int i = blockDim.x * blockIdx.x + threadIdx.x;
    if (i <= high - low) {{
        out[i] = ((low + i) & {word_size - 1} == 0) ? 
            in[(word - (word_wpd - ((low + i) / {word_size})))&{size[formula]-1}] : 
            ((in[(word - (word_wpd - ((low + i) / {word_size})))&{size[formula]-1}] << ((low + i) & {word_size - 1})) | (in[(word - (word_wpd - ((low + i) / {word_size}) - 1))&{size[formula]-1}] >> ({word_size} - ((low + i) & {word_size - 1}))));
    }}
}}

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
    uint64_t i;

    // FIXME: mess with these values
    int threadsPerBlock = 512;
    // FIXME: Should blocksPerGrid be a power of 2?
    int blocksPerGrid = ({max_interval} + threadsPerBlock - 1) / threadsPerBlock;

"""

    for aid in range(nsigs):
        signal = f"a{aid}"
        sigsize[signal] = 1 << (word_wpd[formula]).bit_length()
        code += f"{TAB}uint{word_size}_t {signal}[{sigsize[signal]}] = {{0}};\n"

    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue
        code += f"{TAB}uint{word_size}_t {fid[expr]}[{size[expr]}] = {{0}}; // {expr}\n"
    
    code += f"""
    BitwiseOr bvor_op;
    uint{word_size}_t bvor_init = {hexlit(0, word_size)};
    BitwiseAnd bvand_op;
    uint{word_size}_t bvand_init = {hexlit((2**word_size)-1, word_size)};
    
"""

    # Each temporal operator requires the following variables on the device:
    # - its inputs
    # - its output
    # - a temporary vector of the interval size for the GPU computation
    dev_vars: set[cpt.Expression] = set()
    for expr in cpt.postorder(formula, context):
        if not cpt.is_temporal_operator(expr):
            continue
        expr = cast(cpt.TemporalOperator, expr)
        lb = expr.interval.lb
        ub = expr.interval.ub
        for c in [c for c in expr.children if c not in dev_vars]:
            code += f"{TAB}uint{word_size}_t *dev_{fid[c]};\n"
            code += f"{TAB}cudaMalloc((void**) &dev_{fid[c]}, {size[c] * (word_size // 8)});\n"
            code += f"{TAB}uint{word_size}_t *dev_{fid[c]}_tmp;\n"
            code += f"{TAB}cudaMalloc((void**) &dev_{fid[c]}_tmp, {(ub - lb + 1) * (word_size // 8)});\n"
            dev_vars.add(c)
        if expr not in dev_vars:
            code += f"{TAB}uint{word_size}_t *dev_{fid[expr]};\n"
            code += f"{TAB}cudaMalloc((void**) &dev_{fid[expr]}, {word_size // 8});\n"
            dev_vars.add(expr)
        if expr.operator is cpt.OperatorKind.UNTIL:
            # cannot do parallel reduction on untils :(
            lhs = expr.children[0]
            rhs = expr.children[1]
            code += f"{TAB}uint{word_size}_t {fid[lhs]}_arr[{(ub - lb + 1) * (word_size // 8)}];\n"
            code += f"{TAB}uint{word_size}_t {fid[rhs]}_arr[{(ub - lb + 1) * (word_size // 8)}];\n"
            code += f"{TAB}uint{word_size}_t {fid[expr]}_v = 0;\n"
            continue
        child = expr.children[0] # future and global have only 1 child
        code += f"{TAB}void *dev_tmp_storage_{fid[child]} = nullptr;\n"
        code += f"{TAB}size_t dev_tmp_storage_{fid[child]}_bytes = 0;"
        code += f"""
    cub::DeviceReduce::Reduce(
        dev_tmp_storage_{fid[child]}, dev_tmp_storage_{fid[child]}_bytes,
        dev_{fid[child]}_tmp, dev_{fid[child]}, {(ub - lb + 1)}, bvor_op, bvor_init
    );
    cudaMalloc(&dev_tmp_storage_{fid[child]}, dev_tmp_storage_{fid[child]}_bytes);

"""

    # First we fill the buffers for each sub-formula until we have sufficient data to start
    # computing the first word of `formula`
    for word in range(word_wpd[formula]):
        for aid in range(nsigs):
            signal = f"a{aid}"
            code += f"{TAB}read(f, &{signal}[{word % sigsize[signal]}], {word_size // 8});\n"
            if debug:
                code += "#ifdef DEBUG\n"
                code += (
                    f'{TAB*2}printf("{signal:3}@%d: ", {word});\n'
                    f'{TAB*2}print_binary({signal}[({word})&{sigsize[signal]-1}]); printf("\\n");\n'
                )
                code += "#endif\n"

        for expr in cpt.postorder(formula, context):
            if isinstance(expr, cpt.Signal):
                continue
            code += gen_compute_expr_code_begin(expr, fid, size, word_wpd, word)
            if debug and word-word_wpd[expr] >= 0:
                code += "#ifdef DEBUG\n"
                code += (
                    f'{TAB*2}printf("{fid[expr]:3}@%d: ", {word-word_wpd[expr]});\n'
                    f'{TAB*2}print_binary({fid[expr]}[({word-word_wpd[expr]})&{size[expr] - 1}]); printf("\\n");\n'
                )
                code += "#endif\n"
    code += "\n"

    code += f"{TAB}uint64_t word;\n"
    code += f"{TAB}for (word = {word_wpd[formula]}; word < num_words; ++word) {{\n"
    for aid in range(nsigs):
        signal = f"a{aid}"
        code += f"{TAB*2}read(f, &{signal}[word&{sigsize[signal]-1}], {word_size // 8});\n"
        if debug:
            code += "#ifdef DEBUG\n"
            code += (
                f'{TAB*2}printf("{signal:3}@%llu: ", word);\n'
                f'{TAB*2}print_binary({signal}[word&{sigsize[signal]-1}]); printf("\\n");\n'
            )
            code += "#endif\n"
    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue
        code += gen_compute_expr_code(expr, fid, size, word_wpd, "word")
        if debug:
            code += "#ifdef DEBUG\n"
            code += (
                f'{TAB*2}printf("{fid[expr]:3}@%llu: ", word-{word_wpd[expr]});\n'
                f'{TAB*2}print_binary({fid[expr]}[(word-{word_wpd[expr]})&{size[expr] - 1}]); printf("\\n");\n'
            )
            code += "#endif\n"

    code += "#ifdef OUTPUT\n"
    code += f'{TAB*2}printf("%0{"16llx" if word_size == 64 else "8x" if word_size == 32 else "4hx" if word_size == 16 else "2hhx"}", {fid[formula]}[(word-{word_wpd[formula]})&{size[formula]-1}]);\n'
    code += "#endif\n"

    for expr in cpt.postorder(formula, context):
        code += f"{TAB*2}{fid[expr]}[(word+1)&{size[expr] - 1}] = 0;\n"

    code += f"{TAB}}}\n"
    
    # we return the final value computed only so that if -DOUTPUT or -DDEBUG are not defined, then
    # the compiler doesn't just do nothing. (if -DOUTPUT or -DDEBUG are not defined then the
    # compiler doesn't think the program does anything useful, since it will print nothing and
    # return 0 in all cases.)
    code += f"{TAB}return {fid[formula]}[(num_words-1)&{size[formula]-1}];\n"
    code += "}"
    print(code)
    return code


# def gen_compute_expr_code_unroll(
#         expr: cpt.Expression,
#         fid: dict[cpt.Expression, str],
#         size: dict[cpt.Expression, int],
#         word_wpd: dict[cpt.Expression, int],
#         buffer_size: dict[cpt.Expression, int],
#         tau: str,
#     ) -> str:
#     nonlocal word_size
#     if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
#         return (
#             f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
#             f"~ {fid[expr.children[0]]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}];\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
#         return (
#             f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
#             f"{' & '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
#         return (
#             f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
#             f"{' | '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lb = interval.lb
#         ub = interval.ub
#         child = expr.children[0]

#         ret = ""
#         for i in range(buffer_size[expr]):
#             if lb > 0 and lb % word_size == 0:
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf[{i}] = "
#                     f"{fid[child]}[({tau} - {word_wpd[expr] - i - (lb // word_size)}) & {size[child]-1}];\n"
#                 )
#             elif lb > 0:
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf[{i}] = "
#                     f"(({fid[child]}[({tau} - {word_wpd[expr] - i - lb // word_size}) & {size[child]-1}] << {lb % word_size}) | "
#                     f"({fid[child]}[({tau} - {word_wpd[expr] - i - lb // word_size - 1}) & {size[child]-1}] >> {word_size - (lb % word_size)}));\n" 
#                     f"{TAB*2};\n"
#                 )
#             else:
#                 ret += f"{TAB*2}{fid[expr]}_buf[{i}] = {fid[child]}[({tau} - {word_wpd[expr] - i}) & {size[child]-1}];\n"
        
#         ub -= lb
#         # then lb = 0 and ub > 0 where ub = (2^k)-1 for some k
        
#         log_ub = int(math.log2(ub + 1))
#         for shift_amt in [2**j for j in range(log_ub)]:
#             for i in range(buffer_size[expr] - 1):
#                 if shift_amt < word_size: 
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf[{i}] |= "
#                             f"({fid[expr]}_buf[{i}] << {shift_amt}) | "
#                             f"({fid[expr]}_buf[{i+1}] >> {word_size - shift_amt});\n"
#                     )
#                 elif (
#                     i % ((shift_amt << 1) // word_size) == 0 and 
#                     i + (shift_amt // word_size) < buffer_size[expr]
#                 ):
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf[{i}] |= "
#                             f"{fid[expr]}_buf[{i + (shift_amt // word_size)}];\n"
#                     )

#             if shift_amt >= word_size or shift_amt < ((ub + 1) >> 1):
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf[{buffer_size[expr] - 1}] |= {fid[expr]}_buf[{buffer_size[expr] - 1}] << {shift_amt};\n" 
#                     if shift_amt < word_size else
#                     ""
#                 )

#         ret += f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) & {size[expr] - 1}] = {fid[expr]}_buf[0];\n"
#         return ret
#     elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lb = interval.lb
#         ub = interval.ub
#         child = expr.children[0]

#         ret = ""
#         for i in range(buffer_size[expr]):
#             if lb > 0 and lb % word_size == 0:
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf[{i}] = "
#                     f"{fid[child]}[({tau} - {word_wpd[expr] - i - (lb // word_size)}) & {size[child]-1}];\n"
#                 )
#             elif lb > 0:
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf[{i}] = "
#                     f"(({fid[child]}[({tau} - {word_wpd[expr] - i - lb // word_size}) & {size[child]-1}] << {lb % word_size}) | "
#                     f"({fid[child]}[({tau} - {word_wpd[expr] - i - lb // word_size - 1}) & {size[child]-1}] >> {word_size - (lb % word_size)}));\n" 
#                     f"{TAB*2};\n"
#                 )
#             else:
#                 ret += f"{TAB*2}{fid[expr]}_buf[{i}] = {fid[child]}[({tau} - {word_wpd[expr] - i}) & {size[child]-1}];\n"
        
#         ub -= lb
#         # then lb = 0 and ub > 0 where ub = (2^k)-1 for some k
        
#         log_ub = int(math.log2(ub + 1))
#         for shift_amt in [2**j for j in range(log_ub)]:
#             for i in range(buffer_size[expr] - 1):
#                 if shift_amt < word_size: 
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf[{i}] &= "
#                             f"({fid[expr]}_buf[{i}] << {shift_amt}) | "
#                             f"({fid[expr]}_buf[{i+1}] >> {word_size - shift_amt});\n"
#                     )
#                 elif (
#                     i % ((shift_amt << 1) // word_size) == 0 and 
#                     i + (shift_amt // word_size) < buffer_size[expr]
#                 ):
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf[{i}] &= "
#                             f"{fid[expr]}_buf[{i + (shift_amt // word_size)}];\n"
#                     )

#             if shift_amt >= word_size or shift_amt < ((ub + 1) >> 1):
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf[{buffer_size[expr] - 1}] &= {fid[expr]}_buf[{buffer_size[expr] - 1}] << {shift_amt};\n" 
#                     if shift_amt < word_size else
#                     ""
#                 )

#         ret += f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) & {size[expr] - 1}] = {fid[expr]}_buf[0];\n"
#         return ret
#     elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lhs = expr.children[0]
#         rhs = expr.children[1]
#         lb = interval.lb
#         ub = interval.ub
        
#         ret = ""
#         for i in range(buffer_size[expr]):
#             if lb > 0 and lb % word_size == 0:
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf_1[{i}] = "
#                     f"{fid[lhs]}[({tau} - {word_wpd[expr] - i - (lb // word_size)}) & {size[lhs]-1}];\n"
#                 )
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf_2[{i}] = "
#                     f"{fid[rhs]}[({tau} - {word_wpd[expr] - i - (lb // word_size)}) & {size[rhs]-1}];\n"
#                 )
#             elif lb > 0:
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf_1[{i}] = "
#                     f"(({fid[lhs]}[({tau} - {word_wpd[expr] - i - lb // word_size}) & {size[lhs]-1}] << {lb % word_size}) | "
#                     f"({fid[lhs]}[({tau} - {word_wpd[expr] - i - lb // word_size - 1}) & {size[lhs]-1}] >> {word_size - (lb % word_size)}));\n" 
#                 )
#                 ret += (
#                     f"{TAB*2}{fid[expr]}_buf_2[{i}] = "
#                     f"(({fid[rhs]}[({tau} - {word_wpd[expr] - i - lb // word_size}) & {size[rhs]-1}] << {lb % word_size}) | "
#                     f"({fid[rhs]}[({tau} - {word_wpd[expr] - i - lb // word_size - 1}) & {size[rhs]-1}] >> {word_size - (lb % word_size)}));\n" 
#                 )
#             else:
#                 ret += f"{TAB*2}{fid[expr]}_buf_1[{i}] = {fid[lhs]}[({tau} - {word_wpd[expr] - i}) & {size[lhs]-1}];\n"
#                 ret += f"{TAB*2}{fid[expr]}_buf_2[{i}] = {fid[rhs]}[({tau} - {word_wpd[expr] - i}) & {size[rhs]-1}];\n"
        
#         ub -= lb
#         # then lb = 0 and ub > 0 where ub = (2^k)-1 for some k

#         # b2 |= (b1 & (b2 << 2^k))
#         # b1 &= (b1 << 2^k)
        
#         log_ub = int(math.log2(ub + 1))
#         for shift_amt in [2**j for j in range(log_ub)]:
#             for i in range(buffer_size[expr] - 1):
#                 if shift_amt < word_size: 
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf_2[{i}] |= "
#                             f"{fid[expr]}_buf_1[{i}] & "
#                             f"(({fid[expr]}_buf_2[{i}] << {shift_amt}) | "
#                             f"({fid[expr]}_buf_2[{i+1}] >> {word_size - shift_amt}));\n"
#                     )
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf_1[{i}] &= "
#                             f"(({fid[expr]}_buf_1[{i}] << {shift_amt}) | "
#                             f"({fid[expr]}_buf_1[{i+1}] >> {word_size - shift_amt}));\n"
#                     )
#                 elif (
#                     i % ((shift_amt << 1) // word_size) == 0 and 
#                     i + (shift_amt // word_size) < buffer_size[expr]
#                 ):
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf_2[{i}] |= "
#                             f"{fid[expr]}_buf_1[{i}] & "
#                             f"{fid[expr]}_buf_2[{i + (shift_amt // word_size)}];\n"
#                     )
#                     ret += (
#                         f"{TAB*2}{fid[expr]}_buf_1[{i}] &= "
#                             f"{fid[expr]}_buf_1[{i + (shift_amt // word_size)}];\n"
#                     )

#             if shift_amt >= word_size or shift_amt < ((ub + 1) >> 1):
#                 ret += (
#                     (
#                         f"{TAB*2}{fid[expr]}_buf_2[{buffer_size[expr] - 1}] |= " 
#                             f"{fid[expr]}_buf_1[{buffer_size[expr] - 1}] & "
#                             f"({fid[expr]}_buf_2[{buffer_size[expr] - 1}] << {shift_amt});\n" 
#                         f"{TAB*2}{fid[expr]}_buf_1[{buffer_size[expr] - 1}] &= " 
#                             f"{fid[expr]}_buf_1[{buffer_size[expr] - 1}] << {shift_amt};\n" 
#                     ) if shift_amt < word_size else
#                     ""
#                 )

#         ret += f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) & {size[expr] - 1}] = {fid[expr]}_buf_2[0];\n"
#         return ret
#     return ""

# def gen_compute_expr_code(
#     expr: cpt.Expression,
#     fid: dict[cpt.Expression, str],
#     size: dict[cpt.Expression, int],
#     word_wpd: dict[cpt.Expression, int],
#     buffer_size: dict[cpt.Expression, int],
#     tau: str,
# ) -> str:
#     nonlocal word_size
#     if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
#         return (
#             f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
#             f"~ {fid[expr.children[0]]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}];\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
#         return (
#             f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
#             f"{' & '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
#         return (
#             f"{TAB*2}{fid[expr]}[({tau}-{word_wpd[expr]})&{size[expr] - 1}] = "
#             f"{' | '.join([f'{fid[c]}[({tau}-{word_wpd[expr]})&{size[c]-1}]' for c in expr.children])};\n"
#         )
#     elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lb = interval.lb
#         ub = interval.ub
#         child = expr.children[0]
#         ret = ""
        
#         ret = f"{TAB*2}for(i = 0; i < {buffer_size[expr]}; ++i) {{\n"
#         if lb > 0 and lb % word_size == 0:
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf[i] = "
#                 f"{fid[child]}[({tau} - {word_wpd[expr] - (lb // word_size)} + i) & {size[child]-1}];\n"
#             )
#         elif lb > 0:
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf[i] = "
#                 f"(({fid[child]}[({tau} - {word_wpd[expr] - lb // word_size} + i) & {size[child]-1}] << {lb % word_size}) | "
#                 f"({fid[child]}[({tau} - {word_wpd[expr] - lb // word_size - 1} + i) & {size[child]-1}] >> {word_size - (lb % word_size)}));\n" 
#             )
#         else:
#             ret += f"{TAB*3}{fid[expr]}_buf[i] = {fid[child]}[({tau} - {word_wpd[expr]} + i) & {size[child]-1}];\n"
#         ret += f"{TAB*2}}}\n"
            
#         ub -= lb
#         # then lb = 0 and ub > 0 where ub = (2^k)-1 for some k
        
#         ret += f"{TAB*2}for(j = 1; j <= {min(word_size // 2, (ub + 1) // 2)}; j <<= 1) {{\n"
#         ret += f"{TAB*3}for(i = 0; i < {buffer_size[expr] - 1}; ++i) {{\n" 
#         ret += (
#             f"{TAB*4}{fid[expr]}_buf[i] |= "
#                 f"({fid[expr]}_buf[i] << j) | "
#                 f"({fid[expr]}_buf[i+1] >> ({word_size} - j));\n"
#         )
#         ret += f"{TAB*3}}}\n"
#         ret += f"{TAB*3}{fid[expr]}_buf[i] |= {fid[expr]}_buf[i] << j;\n"
#         ret += f"{TAB*2}}}\n"

#         if ((ub + 1) // 2) > (word_size // 2):
#             ret += f"{TAB*2}for(j = {word_size}; j <= {(ub + 1) // 2}; j <<= 1) {{\n"
#             ret += f"{TAB*3}for(i = 0; (i + (j >> {int(math.log2(word_size))})) < {buffer_size[expr]}; ++i) {{\n" 
#             ret += (
#                 f"{TAB*4}{fid[expr]}_buf[i] |= "
#                     f"{fid[expr]}_buf[i + (j >> {int(math.log2(word_size))})];\n"
#             )
#             ret += f"{TAB*3}}}\n"
#             ret += f"{TAB*2}}}\n"

#         ret += f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) & {size[expr] - 1}] = {fid[expr]}_buf[0];\n"
#         return ret
#     elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lb = interval.lb
#         ub = interval.ub
#         child = expr.children[0]
#         ret = ""
        
#         ret = f"{TAB*2}for(i = 0; i < {buffer_size[expr]}; ++i) {{\n"
#         if lb > 0 and lb % word_size == 0:
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf[i] = "
#                 f"{fid[child]}[({tau} - {word_wpd[expr] - (lb // word_size)} + i) & {size[child]-1}];\n"
#             )
#         elif lb > 0:
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf[i] = "
#                 f"(({fid[child]}[({tau} - {word_wpd[expr] - lb // word_size} + i) & {size[child]-1}] << {lb % word_size}) | "
#                 f"({fid[child]}[({tau} - {word_wpd[expr] - lb // word_size - 1} + i) & {size[child]-1}] >> {word_size - (lb % word_size)}));\n" 
#             )
#         else:
#             ret += f"{TAB*3}{fid[expr]}_buf[i] = {fid[child]}[({tau} - {word_wpd[expr]} + i) & {size[child]-1}];\n"
#         ret += f"{TAB*2}}}\n"
            
#         ub -= lb
#         # then lb = 0 and ub > 0 where ub = (2^k)-1 for some k
        
#         ret += f"{TAB*2}for(j = 1; j <= {min(word_size // 2, (ub + 1) // 2)}; j <<= 1) {{\n"
#         ret += f"{TAB*3}for(i = 0; i < {buffer_size[expr] - 1}; ++i) {{\n" 
#         ret += (
#             f"{TAB*4}{fid[expr]}_buf[i] &= "
#                 f"({fid[expr]}_buf[i] << j) | "
#                 f"({fid[expr]}_buf[i+1] >> ({word_size} - j));\n"
#         )
#         ret += f"{TAB*3}}}\n"
#         ret += f"{TAB*3}{fid[expr]}_buf[i] &= {fid[expr]}_buf[i] << j;\n"
#         ret += f"{TAB*2}}}\n"

#         if ((ub + 1) // 2) > (word_size // 2):
#             ret += f"{TAB*2}for(j = {word_size}; j <= {(ub + 1) // 2}; j <<= 1) {{\n"
#             ret += f"{TAB*3}for(i = 0; (i + (j >> {int(math.log2(word_size))})) < {buffer_size[expr]}; ++i) {{\n" 
#             ret += (
#                 f"{TAB*4}{fid[expr]}_buf[i] &= "
#                     f"{fid[expr]}_buf[i + (j >> {int(math.log2(word_size))})];\n"
#             )
#             ret += f"{TAB*3}}}\n"
#             ret += f"{TAB*2}}}\n"

#         ret += f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) & {size[expr] - 1}] = {fid[expr]}_buf[0];\n"
#         return ret
#     elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
#         interval = cast(cpt.TemporalOperator, expr).interval
#         lhs = expr.children[0]
#         rhs = expr.children[1]
#         lb = interval.lb
#         ub = interval.ub
        
#         ret = f"{TAB*2}for(i = 0; i < {buffer_size[expr]}; ++i) {{\n"
#         if lb > 0 and lb % word_size == 0:
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf_1[i] = "
#                 f"{fid[lhs]}[({tau} - {word_wpd[expr] - (lb // word_size)} + i) & {size[lhs]-1}];\n"
#             )
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf_2[i] = "
#                 f"{fid[rhs]}[({tau} - {word_wpd[expr] - (lb // word_size)} + i) & {size[rhs]-1}];\n"
#             )
#         elif lb > 0:
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf_1[i] = "
#                 f"(({fid[lhs]}[({tau} - {word_wpd[expr] - lb // word_size} + i) & {size[lhs]-1}] << {lb % word_size}) | "
#                 f"({fid[lhs]}[({tau} - {word_wpd[expr] - lb // word_size - 1} + i) & {size[lhs]-1}] >> {word_size - (lb % word_size)}));\n" 
#             )
#             ret += (
#                 f"{TAB*3}{fid[expr]}_buf_2[i] = "
#                 f"(({fid[rhs]}[({tau} - {word_wpd[expr] - lb // word_size} + i) & {size[rhs]-1}] << {lb % word_size}) | "
#                 f"({fid[rhs]}[({tau} - {word_wpd[expr] - lb // word_size - 1} + i) & {size[rhs]-1}] >> {word_size - (lb % word_size)}));\n" 
#             )
#         else:
#             ret += f"{TAB*3}{fid[expr]}_buf_1[i] = {fid[lhs]}[({tau} - {word_wpd[expr]} + i) & {size[lhs]-1}];\n"
#             ret += f"{TAB*3}{fid[expr]}_buf_2[i] = {fid[rhs]}[({tau} - {word_wpd[expr]} + i) & {size[rhs]-1}];\n"
#         ret += f"{TAB*2}}}\n"
            
#         ub -= lb
#         # then lb = 0 and ub > 0 where ub = (2^k)-1 for some k

#         ret += f"{TAB*2}for(j = 1; j <= {min(word_size // 2, (ub + 1) // 2)}; j <<= 1) {{\n"
#         ret += f"{TAB*3}for(i = 0; i < {buffer_size[expr] - 1}; ++i) {{\n"  
#         ret += (
#             f"{TAB*4}{fid[expr]}_buf_2[i] |= "
#                 f"{fid[expr]}_buf_1[i] & "
#                 f"(({fid[expr]}_buf_2[i] << j) | "
#                 f"({fid[expr]}_buf_2[i+1] >> ({word_size} - j)));\n"
#         )
#         ret += (
#             f"{TAB*4}{fid[expr]}_buf_1[i] &= "
#                 f"(({fid[expr]}_buf_1[i] << j) | "
#                 f"({fid[expr]}_buf_1[i+1] >> ({word_size} - j)));\n"
#         )
#         ret += f"{TAB*3}}}\n"
#         ret += (
#             f"{TAB*2}{fid[expr]}_buf_2[{buffer_size[expr] - 1}] |= " 
#                 f"{fid[expr]}_buf_1[{buffer_size[expr] - 1}] & "
#                 f"({fid[expr]}_buf_2[{buffer_size[expr] - 1}] << j);\n" 
#             f"{TAB*2}{fid[expr]}_buf_1[{buffer_size[expr] - 1}] &= " 
#                 f"{fid[expr]}_buf_1[{buffer_size[expr] - 1}] << j;\n" 
#         )
#         ret += f"{TAB*2}}}\n"

#         if ((ub + 1) // 2) > (word_size // 2):
#             ret += f"{TAB*2}for(j = {word_size}; j <= {(ub + 1) // 2}; j <<= 1) {{\n"
#             ret += f"{TAB*3}for(i = 0; (i + (j >> {int(math.log2(word_size))})) < {buffer_size[expr]}; ++i) {{\n" 
#             ret += (
#                 f"{TAB*2}{fid[expr]}_buf_2[i] |= "
#                     f"{fid[expr]}_buf_1[i] & "
#                     f"{fid[expr]}_buf_2[i + (j >> {int(math.log2(word_size))})];\n"
#             )
#             ret += (
#                 f"{TAB*2}{fid[expr]}_buf_1[i] &= "
#                     f"{fid[expr]}_buf_1[i + (j >> {int(math.log2(word_size))})];\n"
#             )
#             ret += f"{TAB*3}}}\n"
#             ret += f"{TAB*2}}}\n"

#         ret += f"{TAB*2}{fid[expr]}[({tau} - {word_wpd[expr]}) & {size[expr] - 1}] = {fid[expr]}_buf_2[0];\n"
#         return ret
    
#     return ""