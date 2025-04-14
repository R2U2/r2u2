# Runtime Monitoring

Recall from the MLTL/ptMLTL formal semantics that we interpret an MLTL/ptMLTL formula $\varphi$ over a finite trace (aka computation) $\pi$, and check that $\pi$ models (satisfies) an MLTL/ptMLTL formula $\varphi$ starting from time index $i \geq 0$, denoted as $\pi,i\models \varphi$.

R2U2 implements real-time, stream-based runtime verification. So our $\pi$ consists of the traces of relevant sensor and software values from the (currently running) system. R2U2 answers the question of whether $\varphi$ holds starting from time $i$, evaluated over computation $\pi$ and outputs a stream of $\langle time, verdict\rangle$ pairs, one for every time $i$. We formally write this runtime verification question as: $\forall i: \pi, i \models \varphi$.

For example, let $\pi$ be the signals for $p$ and $q$:

```{figure} always_if_p_q_timeline.png
A timing diagram for a computation $\pi$ with propositions $p$ and $q$. Each propositional variable's value during the trace is depicted as a line. When the line is high, the proposition is true; when the line is low, it is false.
```

Let $\varphi$ be $\textcolor{red}{\bf \Box_{[0,1]} (p \wedge q)}$


Then R2U2 will output the following given the computation above (where an empty row means no output occurs).


| Current System Time | R2U2 Output |
| ------------------: | :---------- |
|  0 | $(\textcolor{red}{false},0)$
|  1 |
|  2 | $(\textcolor{red}{false},2)$
|  3 | $(\textcolor{red}{false},3)$
|  4 | $(\textcolor{red}{false},4)$
|  5 |
|  6 | $(\textcolor{blue}{true},5)$
|  7 | $(\textcolor{red}{false},7)$
|  8 | $(\textcolor{red}{false},8)$
|  9 | $(\textcolor{red}{false},9)$
| 10 | $(\textcolor{red}{false},10)$
| 11 | $(\textcolor{red}{false},11)$
| 12 | $(\textcolor{red}{false},12)$

Notice that at times $i = 2$ and $i = 7$ we get two outputs: at time 2 we know that $\varphi$ is false when evaluated from times 1 and 2; at time 7 we know that $\varphi$ is false when evaluated from times 6 and 7. We do not get any output when there is not enough information in the system to know absolutely whether $\varphi$ is true or false.
