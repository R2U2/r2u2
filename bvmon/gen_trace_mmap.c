#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <arpa/inet.h>

#define BUFFER_SIZE 65536
#define NSIGS 5

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

// For trace lengths of large sizes (>1GB, for example), we want to buffer the output and write to
// each file when the buffer is filled. However, r2u2 and hydra have trace formats where each
// timestamp lists the propositions that hold at that time, and bvmon has a format where each
// proposition's trace is listed one-after-another. To solve this, we store a buffer for each
// proposition and write-out all buffers when they're full, and for bvmon we write each proposition
// to a different (temporary) file. Then at the end we stitch those files together.

int main(int argc, char *argv[])
{
    char usage[100];
    sprintf(usage, "%s <trace-len> <density>", argv[0]);

    if (argc != 3)
    {
        fprintf(stderr, "%s\n", usage);
        return 1;
    }

    uint64_t trace_len;
    uint8_t density;

    sscanf(argv[1], "%llu", &trace_len);
    sscanf(argv[2], "%hhu", &density);

    if (trace_len < WORD_SIZE) {
        fprintf(stderr, "Trace length must be greater than or equal to word size.\n");
        return 1;
    }

    uint64_t i, j, s;
    uint8_t d, b, sig_val[NSIGS];
    WORD_TYPE value, buffer[NSIGS][BUFFER_SIZE];

    int bvmon_sig_fds[NSIGS];
    bvmon_sig_fds[0] = open("trace.bvmon.log.0", O_CREAT | O_TRUNC | O_RDWR, S_IRWXU);
    bvmon_sig_fds[1] = open("trace.bvmon.log.1", O_CREAT | O_TRUNC | O_RDWR, S_IRWXU);
    bvmon_sig_fds[2] = open("trace.bvmon.log.2", O_CREAT | O_TRUNC | O_RDWR, S_IRWXU);
    bvmon_sig_fds[3] = open("trace.bvmon.log.3", O_CREAT | O_TRUNC | O_RDWR, S_IRWXU);
    bvmon_sig_fds[4] = open("trace.bvmon.log.4", O_CREAT | O_TRUNC | O_RDWR, S_IRWXU);

    FILE *r2u2_file = fopen("trace.r2u2.log", "w");
    FILE *hydra_file = fopen("trace.hydra.log", "w");

    uint64_t num_gen = trace_len / WORD_SIZE; // since each random value is WORD_SIZE bits
    for (i = 0; i < num_gen; ++i) {
        // arc4random() creates 32 bit random numbers, so for 64 bit words we need to concatenate two together
        if (WORD_SIZE == 64) {
            for (s = 0; s < NSIGS; ++s) {
                value = (((WORD_TYPE) arc4random()) << 32) | ((WORD_TYPE) arc4random());
                for (d = 1; d < density; ++d) { 
                    value &= (((WORD_TYPE) arc4random()) << 32) | ((WORD_TYPE) arc4random()); 
                }
                buffer[s][i % BUFFER_SIZE] = (WORD_TYPE) value;
            }
        } else {
            for (s = 0; s < NSIGS; ++s) {
                value = arc4random();
                for (d = 1; d < density; ++d) { value &= arc4random(); }
                buffer[s][i % BUFFER_SIZE] = (WORD_TYPE) value;
            }
        }

        // write-out and reset buffer once buffer is full
        if (((i % BUFFER_SIZE == 0) && (i > 0)) || i == num_gen-1) { 
            // write-out to r2u2 trace
            for (j = 0; j < ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE); ++j) {
                for (b = 0; b < WORD_SIZE; ++b) {
                    sig_val[0] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[0][j] << b)) > 0;
                    sig_val[1] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[1][j] << b)) > 0;
                    sig_val[2] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[2][j] << b)) > 0;
                    sig_val[3] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[3][j] << b)) > 0;
                    sig_val[4] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[4][j] << b)) > 0;
                    if (sig_val[0] | sig_val[1] | sig_val[2] | sig_val[3] | sig_val[4]) {
                        fprintf(r2u2_file, "@%llu,%hhu,%hhu,%hhu,%hhu,%hhu\n", 
                            (i / BUFFER_SIZE) + (j * WORD_SIZE) + b, sig_val[0], sig_val[1], sig_val[2], sig_val[3], sig_val[4]);
                    }
                }
            }

            // write-out to hydra trace
            for (j = 0; j < ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE); ++j) {
                for (b = 0; b < WORD_SIZE; ++b) {
                    sig_val[0] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[0][j]) << b) > 0;
                    sig_val[1] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[1][j]) << b) > 0;
                    sig_val[2] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[2][j]) << b) > 0;
                    sig_val[3] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[3][j]) << b) > 0;
                    sig_val[4] = ((((WORD_TYPE) 1) << (WORD_SIZE-1)) & (buffer[4][j]) << b) > 0;
                    fprintf(hydra_file, "@%llu", (i / BUFFER_SIZE) + (j * WORD_SIZE) + b);
                    if (sig_val[0]) fprintf(hydra_file, " a0");
                    if (sig_val[1]) fprintf(hydra_file, " a1");
                    if (sig_val[2]) fprintf(hydra_file, " a2");
                    if (sig_val[3]) fprintf(hydra_file, " a3");
                    if (sig_val[4]) fprintf(hydra_file, " a4");
                    fprintf(hydra_file, "\n");
                }
            }

            // write-out to bvmon trace
            write(bvmon_sig_fds[0], buffer[0], ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE) * sizeof(WORD_TYPE));
            write(bvmon_sig_fds[1], buffer[1], ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE) * sizeof(WORD_TYPE));
            write(bvmon_sig_fds[2], buffer[2], ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE) * sizeof(WORD_TYPE));
            write(bvmon_sig_fds[3], buffer[3], ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE) * sizeof(WORD_TYPE));
            write(bvmon_sig_fds[4], buffer[4], ((i < BUFFER_SIZE) ? i+1 : BUFFER_SIZE) * sizeof(WORD_TYPE));

            // reset the buffer
            memset(buffer, 0, BUFFER_SIZE * sizeof(WORD_TYPE));
        }
    }

    lseek(bvmon_sig_fds[0], 0, SEEK_SET);
    lseek(bvmon_sig_fds[1], 0, SEEK_SET);
    lseek(bvmon_sig_fds[2], 0, SEEK_SET);
    lseek(bvmon_sig_fds[3], 0, SEEK_SET);
    lseek(bvmon_sig_fds[4], 0, SEEK_SET);

    // stitch together the bvmon temporary files
    int bvmon_fd = open("trace.bvmon.log", O_CREAT | O_TRUNC | O_RDWR, S_IRWXU);
    WORD_TYPE *bvmon_mmaps[NSIGS];
    bvmon_mmaps[0] = mmap(NULL, i * sizeof(WORD_TYPE), PROT_READ, MAP_PRIVATE, bvmon_sig_fds[0], 0);
    bvmon_mmaps[1] = mmap(NULL, i * sizeof(WORD_TYPE), PROT_READ, MAP_PRIVATE, bvmon_sig_fds[1], 0);
    bvmon_mmaps[2] = mmap(NULL, i * sizeof(WORD_TYPE), PROT_READ, MAP_PRIVATE, bvmon_sig_fds[2], 0);
    bvmon_mmaps[3] = mmap(NULL, i * sizeof(WORD_TYPE), PROT_READ, MAP_PRIVATE, bvmon_sig_fds[3], 0);
    bvmon_mmaps[4] = mmap(NULL, i * sizeof(WORD_TYPE), PROT_READ, MAP_PRIVATE, bvmon_sig_fds[4], 0);

    uint64_t num_words = trace_len / WORD_SIZE;
    write(bvmon_fd, &num_words, sizeof(uint64_t));
    write(bvmon_fd, bvmon_mmaps[0], i * sizeof(WORD_TYPE));
    write(bvmon_fd, bvmon_mmaps[1], i * sizeof(WORD_TYPE));
    write(bvmon_fd, bvmon_mmaps[2], i * sizeof(WORD_TYPE));
    write(bvmon_fd, bvmon_mmaps[3], i * sizeof(WORD_TYPE));
    write(bvmon_fd, bvmon_mmaps[4], i * sizeof(WORD_TYPE));

    fclose(r2u2_file);
    fclose(hydra_file);
    close(bvmon_sig_fds[0]);
    close(bvmon_sig_fds[1]);
    close(bvmon_sig_fds[2]);
    close(bvmon_sig_fds[3]);
    close(bvmon_sig_fds[4]);
    close(bvmon_fd);
    // remove("trace.bvmon.log.0");
    // remove("trace.bvmon.log.1");
    // remove("trace.bvmon.log.2");
    // remove("trace.bvmon.log.3");
    // remove("trace.bvmon.log.4");

    return 0;
}
