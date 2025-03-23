#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <arpa/inet.h>

#define BUFFER_SIZE 16384

#ifndef WORD_TYPE
#define WORD_TYPE uint32_t
#define WORD_SIZE 32
#endif

// Method comes from the top answer here:
// https://stackoverflow.com/questions/35795110/fast-way-to-generate-pseudo-random-bits-with-a-given-probability-of-0-or-1-for-e
//
// We don't need high granularity, we just want to investigate at what level of "sparseness" does
// the timepoint/even-based semantics beat the discrete semantics.
//
// To generate the random traces quickly, we will generate nrandom numbers and bitwise-and them
// together, where n is some input that determines the density of the trace:
//
// expression                | number of 1s per m bits (on average)
// --------------------------|-----------------------------
// b1                        | 1 out of every 2
// b1 & b2                   | 1 out of every 4
// b1 & b2 & b3              | 1 out of every 8
// ...
// b1 & b2 & b3 & ... & bn   | 1 out of every 2^n
//
// If density=5 then we will generate a trace where each proposition occurs once every 2^5=32
// timesteps on average.

int main(int argc, char *argv[])
{
    char usage[100];
    sprintf(usage, "%s <trace-len> <num-sigs> <density>", argv[0]);

    if (argc != 4)
    {
        fprintf(stderr, "%s\n", usage);
        return 1;
    }

    uint64_t trace_len;
    uint8_t nsigs, density;

    sscanf(argv[1], "%llu", &trace_len);
    sscanf(argv[2], "%hhu", &nsigs);
    sscanf(argv[3], "%hhu", &density);

    if (trace_len < WORD_SIZE) {
        fprintf(stderr, "Trace length must be greater than or equal to word size.\n");
        return 1;
    }

    uint64_t i, j;
    uint8_t d, b, sig_val[nsigs], any, s;
    WORD_TYPE value, buffer[nsigs][BUFFER_SIZE];

    FILE *r2u2_file = fopen("trace.r2u2.log", "w");
    FILE *hydra_file = fopen("trace.hydra.log", "w");
    int bvmon_fd = open("trace.bvmon.log", O_CREAT | O_TRUNC | O_RDWR, S_IRWXU);

    uint64_t num_words = trace_len / WORD_SIZE;
    write(bvmon_fd, &num_words, sizeof(uint64_t));

    uint64_t num_gen = trace_len / WORD_SIZE; // number of words to generate
    for (i = 0; i <= num_gen; ++i) { 
        // arc4random() creates 32 bit random numbers, so for 64 bit words we need to concatenate two together
        if (WORD_SIZE == 64) {
            for (s = 0; s < nsigs; ++s) {
                value = (((WORD_TYPE) arc4random()) << 32) | ((WORD_TYPE) arc4random());
                for (d = 1; d < density; ++d) { 
                    value &= (((WORD_TYPE) arc4random()) << 32) | ((WORD_TYPE) arc4random()); 
                }
                buffer[s][i % BUFFER_SIZE] = (WORD_TYPE) value;
            }
        } else {
            for (s = 0; s < nsigs; ++s) {
                value = arc4random();
                for (d = 1; d < density; ++d) { value &= arc4random(); }
                buffer[s][i % BUFFER_SIZE] = (WORD_TYPE) value;
            }
        }

        // write-out and reset buffer once buffer is full or have generated all words
        if (((i % BUFFER_SIZE == 0) && (i > 0)) || i == num_gen) { 
            // write-out to r2u2 trace
            for (j = 0; j < ((i % BUFFER_SIZE != 0) ? (i % BUFFER_SIZE) : BUFFER_SIZE); ++j) {
                for (b = 0; b < WORD_SIZE; ++b) {
                    any = 0;
                    for (s = 0; s < nsigs; ++s) {
                        sig_val[s] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[s][j] << b)) > 0;
                        any |= sig_val[s];
                    }
                    if (any) {
                        // Number of buffer write-outs so far = ceildiv(i, BUFFER_SIZE) - 1 
                        //                                    = (((i + BUFFER_SIZE - 1) / BUFFER_SIZE) - 1)
                        // Number of timestamps per buffer write-out = (WORD_SIZE * BUFFER_SIZE)
                        // Offset in buffer = (j * WORD_SIZE)
                        // Offset in word = b
                        fprintf(r2u2_file, "@%llu", ((((i + BUFFER_SIZE - 1) / BUFFER_SIZE) - 1) * (WORD_SIZE * BUFFER_SIZE)) + (j * WORD_SIZE) + b);
                        for (s = 0; s < nsigs; ++s) {
                            fprintf(r2u2_file, ",%hhu", sig_val[s]);
                        }
                        fprintf(r2u2_file, "\n");
                    }
                }
            }

            // write-out to hydra trace
            for (j = 0; j < ((i % BUFFER_SIZE != 0) ? (i % BUFFER_SIZE) : BUFFER_SIZE); ++j) {
                for (b = 0; b < WORD_SIZE; ++b) {
                    // Number of buffer write-outs so far = ceildiv(i, BUFFER_SIZE) - 1 
                    //                                    = (((i + BUFFER_SIZE - 1) / BUFFER_SIZE) - 1)
                    // Number of timestamps per buffer write-out = (WORD_SIZE * BUFFER_SIZE)
                    // Offset in buffer = (j * WORD_SIZE)
                    // Offset in word = b
                    fprintf(hydra_file, "@%llu", ((((i + BUFFER_SIZE - 1) / BUFFER_SIZE) - 1) * (WORD_SIZE * BUFFER_SIZE)) + (j * WORD_SIZE) + b);
                    for (s = 0; s < nsigs; ++s) {
                        sig_val[s] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[s][j] << b)) > 0;
                        if (sig_val[s]) fprintf(hydra_file, " a%hhu", s);
                    }
                    fprintf(hydra_file, "\n");
                }
            }

            // write-out to bvmon trace
            for (j = 0; j < ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE); ++j) {
                for (s = 0; s < nsigs; ++s) {
                    write(bvmon_fd, &buffer[s][j], sizeof(WORD_TYPE));
                }
            }

            // reset the buffer
            memset(buffer, 0, BUFFER_SIZE * sizeof(WORD_TYPE));
        }
    }

    fclose(r2u2_file);
    fclose(hydra_file);
    close(bvmon_fd);

    return 0;
}
