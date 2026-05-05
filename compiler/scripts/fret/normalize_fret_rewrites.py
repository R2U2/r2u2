"""
This script processes the FRET rewrite rules from the FRET paper.
It outputs a set of files, where each file contains a pair of formulas, one on each line.

Each instance of `__p` in the formulas is replaced with `a0`, `__q` with `a1`, etc.

All instances of `=>` are replaced with `->`.

All instances of `X` are replaced with `F[1,1]`.
All instances of `G` are replaced with `G[0,M]`.
All instances of `F` are replaced with `F[0,M]`.
All instance of `U` are replaced with `U[0,M]`.
All instance of `V` are replaced with `R[0,M]`.

All instances of `Op` are replaced with `G`, `F`, `U`, or `V`.
All instances of `Op[<= __h]` are replaced with `Op[0, ub]`.
All instances of `Op[= __h]` are replaced with `Op[ub, ub]`.
All instances of `Op[n, __h]` are replaced with `Op[n, ub]` where `n` is a natural number.

After generating the files, it tests the MLTL parser on all generated files.

Usage:
python3 normalize_fret_rewrites.py
"""

import os
import sys
from pathlib import Path

CURDIR = Path(os.getcwd())
MLTLDIR = CURDIR / "equiv"

# List of rules. The last two elements are the LHS and RHS of the rule.
# The other elements are the assumptions of the rule.
FRETFutureTimeSimplifications: list[list[str]] = [
    # Future Time Simplifications[ '! (! __p)',  '__p'],
    ['__p | __p', '__p'],
    ['__p & __p', '__p'],
    ['! ((! __p) & (! __q))','__p | __q'],
    ['(__p & __q) | (__p & __r)', '__p & (__q | __r)'],
    ['(__p & (__q | __r)) | __r', '(__p & __q) | __r'],
    ['(! __p) | (__p & __q)', '(! __p) | __q'],
    ['__p | ((! __p) & __q)', '__p | __q'],
    ['__p | (__q & (! __p))', '__p | __q'],
    ['(! __p) & ! (__q | __p)', '(! __p) & (! __q)'],
    ['(! __p) & ! (__p & __q)', '! __p'],
    ['__p & ! ((! __p) & __q)', '__p'],
    ['__p & (__p & __q)', '__p & __q'],
    ['(! (__p & __q)) & (! (__r | __q))', '(! __q) & (! __r)'],
    ['! FALSE','TRUE'], 
    ['! TRUE', 'FALSE'],
    ['__p | FALSE','__p'], 
    ['FALSE | __p','__p'],
    ['__p | TRUE','TRUE'], 
    ['TRUE | __p','TRUE'],
    ['__p & TRUE','__p'],
    ['TRUE & __p','__p'],
    ['__p & FALSE', 'FALSE'], 
    ['FALSE & __p', 'FALSE'],
    ['TRUE => __p', '__p'],  
    ['FALSE => __p', 'TRUE'],
    ['__p => TRUE', 'TRUE'],  
    ['__p => FALSE', '(! __p)'],

    # Boolean Simplifications
    ['(! __p) | (__p & __q)', '__p => __q'],
    ['(! __p) | __q', '__p => __q'],
    ['(__p => __q) | __q', '__p => __q'],
    ['__p => (__q => __r)', '(__p & __q) => __r'],
    ['__p => ((__p & __q) | __r)', '__p => (__q | __r)'],
    ['(__p & (__q & __r)) => (__s & __r)', '(__p & (__q & __r)) => __s'],
    ['(__p & (__q & __r)) => ((__r & __s) | __t)', '(__p & (__q & __r)) => (__s | __t)'],
    ['__p => (__q & (__r => ((__p & __s) | __t)))', '__p => (__q & (__r => (__s | __t)))'], 
    ['(__p & __q) => ((__q & __r) | __s)', '(__p & __q) => (__r | __s)'],
    ['(__p & __r) => ((__p & __q) | __s)', '(__p & __r) => (__q | __s)'],

    # Simplifications to reduce Next with temporal interval:
    # (Note: the first two may not seem like simplifications but they make
    # the rest of the simplifications easier to write.)
    ['X (__p & __r)', '(X __p) & (X __r)'],
    ['X (__p | __r)', '(X __p) | (X __r)'],
    ['X (X __p)', 'F[2,2] __p'],
    ['X (G (G[0,0] __r))', 'G[1,M] __r'],
    ['X (G[<= __h] __p)', 'G[1, __h+1] __p'],
    ['X (G[= __h] __p)', 'G[__h+1, __h+1] __p'],
    ['X (F __p)', 'F[1,M] __p'], 
    ['X (F[< __h] __p)', 'F[1, __h] __p'],
    ['X (F[<= __h] __p)', 'F[1, __h+1] __p'],
    ['X (F[= __h] __p)', 'F[__h+1, __h+1] __p'],
    ['X (F[1,__h] __p)', 'F[2,__h+1] __p'],
    ['X (__p U __q)', '__p U[1,M] __q'],
    ['X ((G[0,0] __p) V (G[0,0] __q))', '__p V[1,M] __q'],
    ['X (__p V[<= __h] __q)', '__p V[1, __h+1] __q'],

    # Simplifications reducing Next via distributive law:
    ['(X __p) U ((X __q) & ((F[1, __h+1] __r) | (G[(__h+1)+1, (__h+1)+1] __s)))', 'X (__p U (__q & ((F[<= __h] __r) | (G[= __h+1] __s))))'], # 51
    ['(X __p) U ((X __q) & (F[1, __h+1] __r))', 'X (__p U (__q & (F[<= __h] __r)))'],
    ['(X __p) U ((X __q) & (G[1, __h+1] __r))', 'X (__p U (__q & (G[<= __h] __r)))'],
    ['(X __p) U ((X __q) & (F[1,M] __r))', 'X (__p U (__q & (F __r)))'],
    ['(X __p) U ((X __q) & (X (G __r)))', 'X (__p U (__q & (G __r)))'], # 55
    ['(X __p) U ((X __q) & ((X (__r V __s)) | (X (G __t))))', 'X (__p U (__q & ((__r V __s) | G __t)))'],
    ['(X __p) U ((X __q) & (X (__r V __s)))', 'X (__p U (__q & (__r V __s)))'],
    ['(X __p) U ((X __q) & (F[2,2] __r))', 'X (__p U (__q & (X __r)))'],
    ['(X __p) U ((X __q) & (X __r))', 'X(__p U (__q & __r))'],
    ['(X __p) U ((X __q) & ((X (G __r)) & (X __s)))', 'X (__p U (__q & ((G __r) & __s)))'],
    ['G (X __p)', 'X (G __p)'],
    ['F[__l,__h] (X __p)', 'X (F[__l,__h] __p)'],

    # Simplifications reducing when in or not in a mode:
    ['(! __p) => (__q | (G (! ((! __p) & (X __p)))))', '(! __p) => (__q | (G[1,M] (! __p)))'],
    ['(__p) => (__q | F[< __h] (__p & (X (! __p))))', '(__p) => (__q | F[< __h] (X (! __p)))'],
    ['(__p & __r) => (__q | F[< __h] (__p & (X (! __p))))', '(__p & __r) => (__q | F[< __h] (X (! __p)))'],
    ['(! __p) => (__q | F[< __h] ((! __p) & (X __p)))', '(! __p) => (__q | F[< __h] (X __p))'],
    ['((! __p) & __r) => (__q | F[< __h] ((! __p) & (X __p)))', '((! __p) & __r) => (__q | F[< __h] (X __p))'],
    ['(! __p) => ((__q | (F[< __h] ((! __p) & (X __p)))) | __r)', '(! __p) => ((__q | (F[< __h] (X __p))) | __r)'],
    ['((! __p) & __r) => ((__q | (F[< __h] ((! __p) & (X __p)))) | __s)', '((! __p) & __r) => ((__q | (F[< __h] (X __p))) | __s)'],
    ['(__p) => (__s & (__q | F[< __h] (__p & (X (! __p)))))', '(__p) => (__s & (__q | F[< __h] (X (! __p))))'],
    ['(__p & __r) => (__s & (__q | F[< __h] (__p & (X (! __p)))))', '(__p & __r) => (__s & (__q | F[< __h] (X (! __p))))'],
    ['(! __p) => (__s & (__q | F[< __h] ((! __p) & (X __p))))', '(! __p) => (__s & (__q | F[< __h] (X __p)))'],
    ['((! __p) & __r) => (__s & (__q | F[< __h] ((! __p) & (X __p))))', '((! __p) & __r) => (__s & (__q | F[< __h] (X __p)))'],
    ['(__p & (X (! __p))) => (X (__q => (__r | (F[< __h] ((! __p) & (X __p))))))', '(__p & (X (! __p))) => (X (__q => (__r | (F[< __h] (X __p)))))'],
    ['((! __p) & (X __p)) => (X (__q => (__r | (F[< __h] (__p & (X (! __p)))))))', '((! __p) & (X __p)) => (X (__q => (__r | (F[< __h] (X (! __p))))))'],
    ['(__p & (X (! __p))) => (X (__q => (__s & (__r | (F[< __h] ((! __p) & (X __p)))))))', '(__p & (X (! __p))) => (X (__q => (__s & (__r | (F[< __h] (X __p))))))'],
    ['((! __p) & (X __p)) => (X (__q => (__s & (__r | (F[< __h] (__p & (X (! __p))))))))', '((! __p) & (X __p)) => (X (__q => (__s & (__r | (F[< __h] (X (! __p)))))))'],
    ['(__p & (X (! __p))) => (X (__r =>  ((__t | (F[< __h] ((! __p) & (X __p)))) | __q)))', '(__p & (X (! __p))) => (X (__r =>  ((__t | (F[< __h] (X __p))) | __q)))'],
    ['(__p & (X (! __p))) => (__q | F[1, __h] ((! __p) & (X __p)))', '(__p & (X (! __p))) => (__q | F[1, __h] (X __p))'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => (__t | (F[1,__h] ((! __p) & (X __p))))', '((! __p) & (__r & (__s & (X (! __p))))) => (__t | (F[1,__h] (X __p)))'],
    ['((! __p) & (X __p)) => (__q | F[1, __h] (__p & (X (! __p))))', '((! __p) & (X __p)) => (__q | F[1, __h] (X (! __p)))'],
    ['(__p & (__r & (__s & (X __p)))) => (__t | (F[1,__h] (__p & (X (! __p)))))', '(__p & (__r & (__s & (X __p)))) => (__t | (F[1,__h] (X (! __p))))'],
    ['(__p & (X (! __p))) => (__s & (__q | F[1, __h] ((! __p) & (X __p))))', '(__p & (X (! __p))) => (__s & (__q | F[1, __h] (X __p)))'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => (__q & (__t | (F[1,__h] ((! __p) & (X __p)))))', '((! __p) & (__r & (__s & (X (! __p))))) => (__q & (__t | (F[1,__h] (X __p))))'],
    ['((! __p) & (X __p)) => (__s & (__q | F[1, __h] (__p & (X (! __p)))))', '((! __p) & (X __p)) => (__s & (__q | F[1, __h] (X (! __p))))'],
    ['(__p & (__r & (__s & (X __p)))) => (__q & (__t | (F[1,__h] (__p & (X (! __p))))))', '(__p & (__r & (__s & (X __p)))) => (__q & (__t | (F[1,__h] (X (! __p)))))'],
    ['(__p & (X (! __p))) => ((__q | (F[1,__h] ((! __p) & (X __p)))) | __r)', '(__p & (X (! __p))) => ((__q | (F[1,__h] (X __p))) | __r)'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => ((__t | (F[1,__h] ((! __p) & (X __p)))) | __q)', '((! __p) & (__r & (__s & (X (! __p))))) => ((__t | (F[1,__h] (X __p))) | __q)'],
    ['__p => ((! (__p & (X (! __p)))) U __q)', '__p => ((X __p) U __q)'],
    ['(__p & __r) => ((! (__p & (X (! __p)))) U __q)', '(__p & __r) => ((X __p) U __q)'],
    ['(! __p) => ((! ((! __p) & (X __p))) U __q)', '(! __p) => ((X (! __p)) U __q)'],
    ['((! __p) & __r) => ((! ((! __p) & (X __p))) U __q)', '((! __p) & __r) => ((X (! __p)) U __q)'],
    ['(__p & (X (! __p))) => ((! ((! __p) & (X __p))) U[1,__h] __q)', '(__p & (X (! __p))) => ((X (! __p)) U[1,__h] __q)'],
    ['(__q & (__r & (X (! __p)))) => ((! ((! __p) & (X __p))) U[1, __h] __s)', '(__q & (__r & (X (! __p)))) => ((X (! __p)) U[1, __h] __s)'],
    ['((! __p) & (X __p)) => ((! (__p & (X (! __p)))) U[1,__h] __q)', '((! __p) & (X __p)) => ((X __p) U[1,__h] __q)'],
    ['(__q & (__r & (X __p))) => ((! (__p & (X (! __p)))) U[1, __h] __s)', '(__q & (__r & (X __p))) => ((X __p) U[1, __h] __s)'],
    ['__p => (__q & (__r => ((! (__p & (X (! __p)))) U __s)))', '__p => (__q & (__r => ((X __p) U __s)))'],
    ['(! __p) => (__q & (__r => ((! ((! __p) & (X __p))) U __s)))', '(! __p) => (__q & (__r => ((X (! __p)) U __s)))'],
    ['(__p & (X (! __p))) => (__q & (X (__r => ((! ((! __p) & (X __p))) U __s))))', '(__p & (X (! __p))) => (__q & (X (__r => ((X (! __p)) U __s))))'],
    ['((! __p) & (X __p)) => (__q & (X (__r => ((! (__p & (X (! __p)))) U __s))))', '((! __p) & (X __p)) => (__q & (X (__r => ((X __p) U __s))))'],
    ['(! __p) => (((! ((! __p) & (X __p))) U (((! __p) & (X __p)) & __r)) | __q)', '(! __p) => (((X (! __p)) U ((X __p) & __r)) | __q)'],
    ['__p => ((__p & (X (! __p))) V __q)', '__p => ((X (! __p)) V __q)'],
    ['(__p & __r) => ((__p & (X (! __p))) V __q)', '(__p & __r) => ((X (! __p)) V __q)'],
    ['(! __p) => (((! __p) & (X __p)) V __q)', '(! __p) => ((X __p) V __q)'],
    ['((! __p) & __r) => (((! __p) & (X __p)) V __q)', '((! __p) & __r) => ((X __p) V __q)'],
    ['__p => (((__p & (X (! __p))) V __r) & __s)', '__p => (((X (! __p)) V __r) & __s)'],
    ['(! __p) => ((((! __p) & (X __p)) V __r) & __s)', '(! __p) => (((X __p) V __r) & __s)'],
    ['__p => ((__q | (__p & (X (! __p)))) V __r)', '__p => ((__q | (X (! __p))) V __r)'],
    ['(__p & __r) => ((__q | (__p & (X (! __p)))) V __s)', '(__p & __r) => ((__q | (X (! __p))) V __s)'],
    ['(! __p) => ((__q | ((! __p) & (X __p))) V __r)', '(! __p) => ((__q | (X __p)) V __r)'],
    ['((! __p) & __r) => ((__q | ((! __p) & (X __p))) V __s)', '((! __p) & __r) => ((__q | (X __p)) V __s)'],
    ['(! __p) => ((__q => ((! __p) & (X __p))) V __r)', '(! __p) => ((__q => (X __p)) V __r)'],
    ['((! __p) & __r) => ((__q => ((! __p) & (X __p))) V __s)', '((! __p) & __r) => ((__q => (X __p)) V __s)'],
    ['__p => (__q & (__r => ((__p & (X (! __p))) V __s)))', '__p => (__q & (__r => ((X (! __p)) V __s)))'],
    ['(! __p) => (__q & (__r => (((! __p) & (X __p)) V __s)))', '(! __p) => (__q & (__r => ((X __p) V __s)))'],
    ['(__p & (X (! __p))) => (__q & (X (__r => (((! __p) & (X __p)) V __s))))', '(__p & (X (! __p))) => (__q & (X (__r => ((X __p) V __s))))'],
    ['((! __p) & (X __p)) => (__q & (X (__r => ((__p & (X (! __p))) V __s))))', '((! __p) & (X __p)) => (__q & (X (__r => ((X (! __p)) V __s))))'],
    ['__p => (((X (! __p)) V ((__q & (__r & (! (__p & (X (! __p)))))) => __s)) & __t)', '__p => (((X (! __p)) V ((__q & (__r & (G[1,1] __p))) => __s)) & __t)'], # 118
    ['(! __p) => (((X __p) V ((__q & (__r & (! ((! __p) & (X __p))))) => __s)) & __t)', '(! __p) => (((X __p) V ((__q & (__r & (G[1,1] (! __p)))) => __s)) & __t)'], # 119
    ['__p => (__q | ((__p & (X (! __p))) V[<= __h] __r))', '__p => (__q | ((X (! __p)) V[<= __h] __r))'],
    ['(__p & __r) => (__q | ((__p & (X (! __p))) V[<= __h] __s))', '(__p & __r) => (__q | ((X (! __p)) V[<= __h] __s))'],
    ['(! __p) => (__q | (((! __p) & (X __p)) V[<= __h] __r))', '(! __p) => (__q | ((X __p) V[<= __h] __r))'],
    ['((! __p) & __r) => (__q | (((! __p) & (X __p)) V[<= __h] __s))', '((! __p) & __r) => (__q | ((X __p) V[<= __h] __s))'],
    ['(! __p) => (__q | (__r | (((! __p) & (X __p)) V[<= __h] __s)))', '(! __p) => (__q | (__r | ((X __p) V[<= __h] __s)))'],
    ['((! __p) & __r) => (__q | (__s | (((! __p) & (X __p)) V[<= __h] __t)))', '((! __p) & __r) => (__q | (__s | ((X __p) V[<= __h] __t)))'],
    ['__p => ((__q | ((__p & (X (! __p))) V[<= __h] __r)) & __s)', '__p => ((__q | ((X (! __p)) V[<= __h] __r)) & __s)'],
    ['(__p & __r) => ((__q | ((__p & (X (! __p))) V[<= __h] __s)) & __t)', '(__p & __r) => ((__q | ((X (! __p)) V[<= __h] __s)) & __t)'],
    ['(! __p) => ((__q | ((((! __p) & (X __p))) V[<= __h] __r)) & __s)', '(! __p) => ((__q | ((X __p) V[<= __h] __r)) & __s)'],
    ['((! __p) & __r) => ((__q | ((((! __p) & (X __p))) V[<= __h] __s)) & __t)', '((! __p) & __r) => ((__q | ((X __p) V[<= __h] __s)) & __t)'],
    ['(__p & (X (! __p))) => ((__q => ((! __p) & (X __p))) V[1,__h] __r)', '(__p & (X (! __p))) => ((__q => (X __p)) V[1,__h] __r)'],
    ['(__p & (X (! __p))) => (X (__r => (((__q | ((! __p) & (X __p))) V __s))))', '(__p & (X (! __p))) => (X (__r => (((__q | (X __p)) V __s))))'], 
    ['((! __p) & (X __p)) => (X (__r => ((__q | (__p & (X (! __p)))) V __s)))', '((! __p) & (X __p)) => (X (__r => ((__q | (X (! __p))) V __s)))'],
    ['(__p & (X (! __p))) => (X (__r => (((__q => ((! __p) & (X __p))) V __s))))', '(__p & (X (! __p))) => (X (__r => (((__q => (X __p)) V __s))))'],
    ['(__p & (X (! __p))) => (X (__q => (__r | (((! __p) & (X __p)) V[<= __h] __s))))', '(__p & (X (! __p))) => (X (__q => (__r | ((X __p) V[<= __h] __s))))'],
    ['((! __p) & (X __p)) => (X (__q => (__r | ((__p & (X (! __p)) V[<= __h] __s)))))', '((! __p) & (X __p)) => (X (__q => (__r | ( (X (! __p)) V[<= __h] __s))))'],
    ['(__p & (X (! __p))) => (X (__q => (__r | (__t | (((! __p) & (X __p)) V[<= __h] __s)))))', '(__p & (X (! __p))) => (X (__q => (__r | (__t | ((X __p) V[<= __h] __s)))))'],
    ['(__p & (X (! __p))) => (X (__q => ((__r | (((! __p) & (X __p)) V[<= __h] __s)) & __u)))', '(__p & (X (! __p))) => (X (__q => ((__r | ((X __p) V[<= __h] __s)) & __u)))'],
    ['((! __p) & (X __p)) => (X (__q => ((__r | (__p & (X (! __p)) V[<= __h] __s)) & __u)))', '((! __p) & (X __p)) => (X (__q => ((__r | ( (X (! __p)) V[<= __h] __s)) & __u)))'],
    ['(__p & (X (! __p))) => (((! __p) & (X __p)) V[1,__h] __q)', '(__p & (X (! __p))) => ((X __p) V[1,__h] __q)'],
    ['(__q & (__r & (X (! __p)))) => (((! __p) & (X __p)) V[1, __h] __s)', '(__q & (__r & (X (! __p)))) => ((X __p) V[1, __h] __s)'],
    ['((! __p) & (X __p)) => ((__p & (X (! __p))) V[1,__h] __q)', '((! __p) & (X __p)) => ((X (! __p)) V[1,__h] __q)'],
    ['(__q & (__r & (X __p))) => ((__p & (X (! __p))) V[1, __h] __s)', '(__q & (__r & (X __p))) => ((X (! __p)) V[1, __h] __s)'],
    ['(__p & (X (! __p))) => (__q | (((! __p) & (X __p)) V[1,__h] __r))', '(__p & (X (! __p))) => (__q | ((X __p) V[1,__h] __r))'],
    ['((! __p) & (X __p)) => (__q | ((__p & (X (! __p))) V[1,__h] __r))', '((! __p) & (X __p)) => (__q | ((X (! __p)) V[1,__h] __r))'],
    ['(__p & (X (! __p))) => ((((! __p) & (X __p)) V[1,__h] __r) & __s)', '(__p & (X (! __p))) => (((X __p) V[1,__h] __r) & __s)'],
    ['((! __p) & (X __p)) => (((__p & (X (! __p))) V[1,__h] __r) & __s)', '((! __p) & (X __p)) => (((X (! __p)) V[1,__h] __r) & __s)'],
    ['((! __p) & (X __p)) => (((X (! __p)) V[1,__h] ((__q & (__r & (! (__p & (X (! __p)))))) => __s)) & __t)', '((! __p) & (X __p)) => (((X (! __p)) V[1,__h] ((__q & (__r & (X __p))) => __s)) & __t)'],
    ['(__p & (X (! __p))) => (((X __p) V[1,__h] ((__q & (__r & (! ((! __p) & (X __p))))) => __s)) & __t)', '(__p & (X (! __p))) => (((X __p) V[1,__h] ((__q & (__r & (X (! __p)))) => __s)) & __t)'],
    ['(__p & (X (! __p))) => ((__q | ((((! __p) & (X __p))) V[1,__h] __r)) & __s)', '(__p & (X (! __p))) => ((__q | ((X __p) V[1,__h] __r)) & __s)'],
    ['((! __p) & (X __p)) => ((__q | ((__p & (X (! __p))) V[1,__h] __r)) & __s)', '((! __p) & (X __p)) =>((__q | ((X (! __p)) V[1,__h] __r)) & __s)'],
    ['(__p & (X (! __p))) => (__q | (__r | (((! __p) & (X __p)) V[1,__h] __s)))', '(__p & (X (! __p))) => (__q | (__r | ((X __p) V[1,__h] __s)))'],
    ['(__p & (X (! __p))) => ((__q | ((! __p) & (X __p))) V[1,__h] __r)', '(__p & (X (! __p))) => ((__q | (X __p)) V[1,__h] __r)'],
    ['((! __p) & (X __p)) => ((__q | (__p & (X (! __p)))) V[1,__h] __r)', '((! __p) & (X __p)) => ((__q | (X (! __p))) V[1,__h] __r)'],
    ['(__p & (__r & (__s & (X __p)))) => ((__t | (__p & (X (! __p)))) V[1, __h] __q)', '(__p & (__r & (__s & (X __p)))) => ((__t | (X (! __p))) V[1, __h] __q)'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => ((__t | ((! __p) & (X __p))) V[1, __h] __q)', '((! __p) & (__r & (__s & (X (! __p))))) => ((__t | (X __p)) V[1, __h] __q)'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => (__t | (((! __p) & (X __p)) V[1,__h] __q))', '((! __p) & (__r & (__s & (X (! __p))))) => (__t | ((X __p) V[1,__h] __q))'],
    ['(__p & (__r & (__s & (X __p)))) => (__t | ((__p & (X (! __p))) V[1,__h] __q))', '(__p & (__r & (__s & (X __p)))) => (__t | ((X (! __p)) V[1,__h] __q))'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => ((__t | (((! __p) & (X __p)) V[1,__h] __q)) & __u)', '((! __p) & (__r & (__s & (X (! __p))))) => ((__t | ((X __p) V[1,__h] __q)) & __u)'],
    ['(__p & (__r & (__s & (X __p)))) => ((__t | ((__p & (X (! __p))) V[1,__h] __q)) & __u)', '(__p & (__r & (__s & (X __p)))) => ((__t | ((X (! __p)) V[1,__h] __q)) & __u)'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => (__t | (__u | (((! __p) & (X __p)) V[1,__h] __q)))', '((! __p) & (__r & (__s & (X (! __p))))) => (__t | (__u | ((X __p) V[1,__h] __q)))'],
    ['((! __p) & (__r & (__s & (X (! __p))))) => ((__t => ((! __p) & (X __p))) V[1, __h] __q)', '((! __p) & (__r & (__s & (X (! __p))))) => ((__t => (X __p)) V[1, __h] __q)'],
    ['(__p & (X (! __p))) => (__q & (X (__r => (((! __p) & (X __p)) | __s))))', '(__p & (X (! __p))) => (__q & (X (__r => ((X __p) | __s))))'],
    ['((! __p) & (X __p)) => (__q & (X (__r => ((__p & (X (! __p))) | __s))))', '((! __p) & (X __p)) => (__q & (X (__r => ((X (! __p)) | __s))))'],
    
    # Simplifications reducing interval bounds:
    ['__h <= M', '(G[__l,__h] __p) | (__q V __p)', '(G[__l,__h] __p) | (__q V[<= __h] __p)'],
    ['(__p U __q) & (F[<= __h] __q)', '__p U[<= __h] __q'],
    ['(G[<= __h] (! __p)) & (F[<= __h+1] __p)', '(G[<= __h] (! __p)) & (F[= __h+1] __p)'],
    ['(F[<= __h] __p) | (G[<= __h+1] (! __p))', '(F[<= __h] __p) | (G[= __h+1] (! __p))'],
    ['(__r V[<= __h] (! __q)) & ((F[<= __h+1] __q) | (F[< __h+1] __r))', '(__r V[<= __h] (! __q)) & ((F[= __h+1] __q) | (F[< __h+1] __r))'],
    ['__h <= M', '(G[__l,__h] __p) | G __p', 'G[__l,__h] __p'],
    
    # Misc. simplifications reducing temporal operators:
    ['!(__p U __q)', '(! __p) V (! __q)'],
    ['!(F __p)', 'G (! __p)'],
    ['((__p & __q) | __r) V __p', '(__q | __r) V __p'],
    ['((__p | __q) V (__r | __s)) | (__q V __r)', '((__p | __q) V (__r | __s))'],
    ['((__p | __q) V !(__r & __s)) | (__q V (! __r))', '((__p | __q) V !(__r & __s))'],
    ['((TRUE) U (__p)) | (G (! __p))', 'TRUE'], # modified -- rewrote '((! __p) U __p)' as 'TRUE'
    
    # Simplifications reducing Release to an external Globally:
    ['(G ((! __p & (X __p)) => ((X(! __p)) V[1,M] (G[0,0] __q)))) & (__p => ((X(! __p)) V __q))', 'G (__p => __q)'], # modified -- added G[0,0]
    ['(G ((__p & (X (! __p))) => ((X __p) V[1,M] (G[0,0] __q)))) & ((! __p) => ((X __p) V __q))', 'G ((! __p) => __q)'], # modified -- added G[0,0]
    ['(G ((! __p & (X __p)) => (((X(! __p)) V[1,M] (G[0,0] __q)) & (X __r)))) & (__p => (((X(! __p)) V __q) & __r))', '(G ((__p => __q) & (((! __p) & (X __p) => (X __r))))) & (__p => __r)'], # modified -- added G[0,0]
    ['(G ((__p & (X (! __p))) => (((X __p) V[1,M] (G[0,0] __q)) & (X __r)))) & ((! __p) => (((X __p) V __q) & __r))', '(G (((! __p) => __q) & ((__p & (X (! __p)) => (X __r))))) & ((! __p) => __r)'], # modified -- added G[0,0]
]

os.makedirs(MLTLDIR, exist_ok=True)

def normalize_formula(formula: str) -> str:
    formula = formula.replace("TRUE", "true")
    formula = formula.replace("FALSE", "false")

    formula = formula.replace("__p", "a0")
    formula = formula.replace("__q", "a1")
    formula = formula.replace("__r", "a2")
    formula = formula.replace("__s", "a3")
    formula = formula.replace("__t", "a4")
    formula = formula.replace("__u", "a5")
    
    formula = formula.replace("X", "F[1,1]")
    formula = formula.replace("G ", "G[0,M] ")
    formula = formula.replace("F ", "F[0,M] ")
    formula = formula.replace("U ", "U[0,M] ")
    formula = formula.replace("V ", "R[0,M] ")
    
    formula = formula.replace("=>", "->")
    formula = formula.replace("&&", "&")
    formula = formula.replace("||", "|")

    formula = formula.replace("V", "R")
    
    for op in ["G", "F", "U", "R"]:
        formula = formula.replace(f"{op}[<= __h]", f"{op}[0, __h]")
        formula = formula.replace(f"{op}[<= __h+1]", f"{op}[0, __h+1]")
        formula = formula.replace(f"{op}[< __h]", f"{op}[0, __h-1]")
        formula = formula.replace(f"{op}[< __h+1]", f"{op}[0, __h]")
        formula = formula.replace(f"{op}[= __h]", f"{op}[__h, __h]")
        formula = formula.replace(f"{op}[= __h+1]", f"{op}[__h+1, __h+1]")
        formula = formula.replace(f"{op}[1, __h]", f"{op}[1, __h]")
        formula = formula.replace(f"{op}[1,__h]", f"{op}[1, __h]")
        formula = formula.replace(f"{op}[1, __h+1]", f"{op}[1, __h+1]")
        formula = formula.replace(f"{op}[1,__h+1]", f"{op}[1, __h+1]")
        formula = formula.replace(f"{op}[(__h+1)+1, (__h+1)+1]", f"{op}[__h+2, __h+2]")

    formula = formula.replace("__l", "b0")
    formula = formula.replace("__h", "b1")
    # formula = formula.replace("M", "b2")

    return formula

def process_fret_rewrites():
    """Process FRET rewrite rules and generate MLTL files."""
    processed_rules = []

    for i, rule in enumerate(FRETFutureTimeSimplifications):
        assumptions = ' & '.join(normalize_formula(a) for a in rule[:-2])
        lhs = normalize_formula(rule[-2])
        rhs = normalize_formula(rule[-1])
            
        with open(MLTLDIR / f"fret_{i}.equiv", "w") as f:
            if assumptions:
                f.write(f"c: {assumptions}\n")
            f.write(f"{lhs}\n{rhs}\n")

        processed_rules.append((lhs, rhs))

    print('\n\n'.join([f"{i+1}: {lhs} <=> {rhs}" for i, (lhs, rhs) in enumerate(processed_rules)]))

def main():
    """Main function that generates FRET rewrite files and tests them."""
    print("Processing FRET rewrite rules...")
    process_fret_rewrites()
    print(f"Generated {len(FRETFutureTimeSimplifications)} MLTL files in {MLTLDIR}")

if __name__ == "__main__":
    sys.exit(main())
