import math
from typing import cast

from c2po import cpt

TAB = "    "
PROFILE = False # enable profiling
BUFSZ2 = True # force buffer size to be a power of 2 (modulo operations become bitwise-ands)

def ceildiv(a: int, b: int) -> int:
    return -(a // -b)

def hexlit(value: int, word_size: int) -> str:
    return f"{value:#0{(word_size // 8) * 2 + 2}x}"

def line(s: str, indent: int = 0) -> str:
    return f"{TAB*indent}{s}\n"

def gen_code(formula: cpt.Expression, context: cpt.Context, word_size: int, nsigs: int, decompose: bool = True) -> str:

    if word_size not in [8, 16, 32, 64]:
        raise ValueError("word_size must be 8, 16, 32, or 64")
    
    def gen_compute_expr_code_func(
            expr: cpt.Expression,
            fid: dict[cpt.Expression, str],
            size: dict[cpt.Expression, int],
            word_wpd: dict[cpt.Expression, int],
            buffer_size: dict[cpt.Expression, int],
            tau: str,
            indent: int = 2,
        ) -> str:
        nonlocal word_size
        if cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            return line(
                f"{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"~ {fid[expr.children[0]]}[({tau} - {word_wpd[expr]}) % {size[expr]}];", indent
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            return line(
                f"{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"{' & '.join([f'{fid[c]}[({tau} - {word_wpd[expr]}) % {size[c]}]' for c in expr.children])};", indent
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            return line(
                f"{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"{' | '.join([f'{fid[c]}[({tau} - {word_wpd[expr]}) % {size[c]}]' for c in expr.children])};", indent
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            lhs = expr.children[0]
            rhs = expr.children[1]
            return line(
                f"{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"(~ {fid[lhs]}[({tau} - {word_wpd[expr]}) % {size[expr]}]) | {fid[rhs]}[({tau} - {word_wpd[expr]}) % {size[expr]}];", indent
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            interval = cast(cpt.TemporalOperator, expr).interval
            lb = interval.lb
            ub = interval.ub
            child = expr.children[0]
            return line(
                f"{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"future({fid[child]}, {fid[expr]}_buf, {buffer_size[expr]}, {tau}, {word_wpd[expr]}, {lb}, {ub});", indent
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lb = interval.lb
            ub = interval.ub
            child = expr.children[0]
            return line(
                f"{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"global({fid[child]}, {fid[expr]}_buf, {buffer_size[expr]}, {tau}, {word_wpd[expr]}, {lb}, {ub});", indent
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            interval = cast(cpt.TemporalOperator, expr).interval
            lb = interval.lb
            ub = interval.ub
            lhs = expr.children[0]
            rhs = expr.children[1]
            return line(
                f"{fid[expr]}[({tau} - {word_wpd[expr]}) % {size[expr]}] = "
                f"until({fid[lhs]}, {fid[rhs]}, {fid[expr]}_buf_1, {fid[expr]}_buf_2, {buffer_size[expr]}, {tau}, {word_wpd[expr]}, {lb}, {ub});", indent
            )
        
        raise NotImplementedError(f"Operator '{expr.symbol}' not implemented")

    fid: dict[cpt.Expression, str] = {}
    size: dict[cpt.Expression, int] = {}
    word_wpd: dict[cpt.Expression, int] = {} # how many words to wait until all children are computed
    buffer_size: dict[cpt.Expression, int] = {} 

    formula = cpt.decompose_intervals(formula, context) if decompose else formula

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

    if PROFILE:
        code += f"""
int read_inputs(FILE *f, int (*abuf)[{nsigs}], uint{word_size}_t (*atomics)[{nsigs}][{size[formula]}], uint64_t word)
{{
    for (int i = 0; i < {word_size}; ++i) {{
        if(fscanf(f, "{','.join(['%d' for _ in range(nsigs)])}\\n", {', '.join([f'&(*abuf)[{i}]' for i in range(nsigs)])}) != {nsigs}) {{
            return 1;
        }}
        {f'\n{TAB*2}'.join([f'(*atomics)[{i}][word % {size[formula]}] = ((*atomics)[{i}][word % {size[formula]}] << 1) | ((*abuf)[{i}] == 1);' for i in range(nsigs)])}
    }}
    return 0;
}}
"""

    # The following is the structure of the future, global, and until functions:
    # 1. Shift all words in the buffer by the lower bound.
    #   a. If the lower bound is a multiple of the word size, then the words of the buffer are all shifted. 
    #   b. Otherwise, each word is shifted by the lower bound and the next word is shifted by the remaining bits.
    # 2. Shift and compute the buffer up to the largest power of two less than the upper bound.
    #   a. If the upper bound is smaller than the word size, then the words of the buffer are all shifted.
    # 3 .Shift and compute the buffer by the remaining amount of the interval.
    
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

    for(; j <= (ub - lb + 1) >> 1; j <<= 1) {{
        for(i = 0; (i + (j >> {log_word_size})) < nbuf; ++i) {{
            buf[i] |= buf[i + (j >> {log_word_size})];
        }}
    }}

    // Check if there is a leftover shift amount
    // j is the largest power of two less than the interval size
    if (((ub - lb + 1) & (j - 1)) != 0) {{
        uint64_t leftover_shift = (ub - lb + 1) & (j - 1);
        for(i = 0; i < nbuf; ++i) {{ 
            buf[i] |= ((leftover_shift & {word_size - 1}) == 0) ?
                buf[i + (leftover_shift >> {log_word_size})] :
                (buf[i] << leftover_shift) | (buf[i+1] >> ({word_size} - leftover_shift));
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

    for(; j <= (ub - lb + 1) >> 1; j <<= 1) {{
        for(i = 0; (i + (j >> {log_word_size})) < nbuf; ++i) {{
            buf[i] &= buf[i + (j >> {log_word_size})];
        }}
    }}

    // Check if there is a leftover shift amount
    // j is the largest power of two less than the interval size
    if (((ub - lb + 1) & (j - 1)) != 0) {{
        uint64_t leftover_shift = (ub - lb + 1) & (j - 1);
        for(i = 0; i < nbuf; ++i) {{ 
            buf[i] &= ((leftover_shift & {word_size - 1}) == 0) ?
                buf[i + (leftover_shift >> {log_word_size})] :
                (buf[i] << leftover_shift) | (buf[i+1] >> ({word_size} - leftover_shift));
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

    for(; j <= (ub + 1) >> 1; j <<= 1) {{
        for(i = 0; (i + (j >> {log_word_size})) < nbuf; ++i) {{
            buf2[i] |= buf1[i] & buf2[i + (j >> {log_word_size})];
            buf1[i] &= buf1[i + (j >> {log_word_size})];
        }}
    }}

    // Check if there is a leftover shift amount
    // j is the largest power of two less than the interval size
    if (((ub - lb + 1) & (j - 1)) != 0) {{
        uint64_t leftover_shift = (ub - lb + 1) & (j - 1);
        for(i = 0; i < nbuf; ++i) {{ 
            buf2[i] |= ((leftover_shift & {word_size - 1}) == 0) ?
                buf1[i] & buf2[i + (leftover_shift >> {log_word_size})] :
                buf1[i] & ((buf2[i] << leftover_shift) | (buf2[i+1] >> ({word_size} - leftover_shift)));
            buf1[i] &= ((leftover_shift & {word_size - 1}) == 0) ?
                buf1[i + (leftover_shift >> {log_word_size})] :
                (buf1[i] << leftover_shift) | (buf1[i+1] >> ({word_size} - leftover_shift));
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
    code += line(f"uint{word_size}_t atomics[{nsigs}][{size[formula]}] = {{0}};", 1)

    for expr in cpt.postorder(formula, context):
        if isinstance(expr, cpt.Signal):
            continue
        code += line(f"uint{word_size}_t {fid[expr]}[{size[expr]}] = {{0}}; // {expr}", 1)
    code += "\n"

    for expr in cpt.postorder(formula, context):
        if not cpt.is_temporal_operator(expr):
            continue
        expr = cast(cpt.TemporalOperator, expr)
        lb = expr.interval.lb
        ub = expr.interval.ub
        buffer_size[expr] = (((word_size - 1) + ub) // word_size) -  (lb // word_size) + 1
        if cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            code += line(f"uint{word_size}_t {fid[expr]}_buf_1[{buffer_size[expr]}];", 1)
            code += line(f"uint{word_size}_t {fid[expr]}_buf_2[{buffer_size[expr]}];", 1)
        else:
            code += line(f"uint{word_size}_t {fid[expr]}_buf[{buffer_size[expr]}];", 1)

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

    if PROFILE:
         code += line(f"gettimeofday(&start[word % {size[formula]}], NULL);", 0)

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
