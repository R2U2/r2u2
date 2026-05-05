#!/bin/bash
> all.txt
while IFS= read -r file; do \
    case "${file}" in \
        */boeing-wbs/*.c2po) echo "${file}" >> all.txt ;; \
        */nasa-atc/*.c2po) echo "${file}" >> all.txt ;; \
        */mtl-patterns/*.mltl) echo "${file}" >> all.txt ;; \
        *.mltl) echo "${file}" >> all.txt ;; \
    esac; \
done < <(find /home/cgjohann/Git/r2u2/benchmarks -type f \( -name '*.mltl' -o -name '*.c2po' \) | sort)
