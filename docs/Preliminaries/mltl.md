# Mission-time Linear Temporal Logic

Mission-time Linear Temporal Logic (MLTL) and past-time MLTL (ptMLTL) enables unambiguous descriptions of behaviors, including complex, temporal behaviors, that comprise requirements, fault signatures, sanity checks, or other properties of a system we might want to observe using R2U2. While there are many temporal logics, MLTL strikes a nice balance of being expressive enough to capture many common properties from aerospace operational concepts while still being easy to validate and efficiently monitorable. 

## References

MLTL was first defined in {footcite:p}`RRS14`. MLTL satisfiability and its complexity appears in {footcite:p}`LVR19`. MLTL validation (checking that an MLTL formula represents exactly the behavior intended) strategies include consulting the formal semantics, truth table validation, satisfiability checking, transition machine visualizations, which all appear in detail in {footcite:p}`RDR22`. We can also validate formulas through oracle generation {footcite:p}`LR18`. The WEST tool provides an (open-source) interactive GUI for MLTL visualization {footcite:p}`EGSTWR23`. The R2U2 GUI provides additional tools for profiling MLTL specifications, including calculating the size of monitor instances for equivalent MLTL formulas {footcite:p}`JJKRZ23`.

## MLTL Formal Semantics

R2U2 implements the following formal semantics for MLTL and ptMLTL.

We interpret MLTL and ptMLTL formulas over finite traces bounded by base-10 (decimal) intervals. A finite trace, denoted by $\pi$, is a finite sequence of sets of atomic propositions. The $i^{th}$ set is denoted by $\pi(i)$ and contains the atomic propositions that are satisfied at the $i^{th}$ time step. $|\pi|$ denotes the length of $\pi$ (where $|\pi| < \infty$), and $\pi[lb,ub]$ denotes the trace segment $\pi(lb),\pi(lb+1),...,\pi(ub)$.


Let $lb, ub \in \mathbb{N}_0, lb \le ub$ and let $I$ be a closed interval $[lb,ub]$; we recursively define that $\pi$ models (satisfies) an MLTL formula $\phi$ starting from time index $i \geq 0$, denoted as $\pi,i\models \phi$, as follows:

* $\pi,i\models \sf true$
* $\pi,i\models p$ for $p \in \mathcal{AP}$ iff $p \in \pi(i)$
* $\pi,i\models \neg \psi$ iff $\pi,i\not\models\psi$
* $\pi,i\models\psi\ \wedge\ \xi$ iff $\pi,i\models\psi$ and $\pi,i\models\xi$
* $\pi,i\models\psi\ \vee\ \xi$ iff $\pi,i\models\psi$ or $\pi,i\models\xi$
* $\pi,i\models \Box_{[lb,ub]} \psi$ iff $|\pi|\leq i+lb$ or $\forall j\in[i+lb,i+ub]$, $\pi,j\models\psi$
* $\pi,i\models \Diamond_{[lb,ub]} \psi$ iff $|\pi|> i+lb$ and $\exists j\in[i+lb,i+ub]$ such that $\pi,j\models\psi$
* $\pi,i\models \psi\ \mathcal{U}_{[lb,ub]}\ \xi$ iff $|\pi| > i+lb$ and $\exists j\in [i+lb,i+ub]$ such that $\pi,j\models\xi$ and $\forall k<j$ where $k\in [i+lb, i+ub]$, $\pi,k\models\psi$
* $\pi,i\models \psi\ \mathcal{R}_{[lb,ub]}\ \xi$ iff $|\pi| \leq i+lb$ or if $\exists j\in [i+lb,i+ub]$ where $\pi,j\not\models\xi$, then $\exists k < j$ where $k\in [i+lb, i+ub]$ such that $\pi,k\models\psi$

Given two MLTL formulas $\psi$ and $\xi$, they are semantically equivalent (denoted by $\psi \equiv \xi$) if and only if $\pi \models \psi \Leftrightarrow \pi \models \xi$ for all traces $\pi$. MLTL also keeps the standard operator equivalences from LTL, including $\sf false \equiv \neg \sf true$, $\psi\ \vee\ \xi\equiv\neg(\neg \psi\ \wedge\ \neg \xi)$, $\psi \rightarrow \xi \equiv \neg \psi \vee \xi$, $\psi\leftrightarrow\xi\equiv \neg(\psi\oplus\xi)$, $\neg(\psi\ \mathcal{U}_I\ \xi)\equiv(\neg\psi\ \mathcal{R}_I\ \neg\xi)$, $\neg\Diamond_I\psi\equiv\Box_I\neg\psi$, $\Diamond_I\psi\equiv(\sf true\ \mathcal{U}_I\ \psi)$, and $\Box_I\psi\equiv(\sf false\ \mathcal{R}_I\ \psi)$. Notably, MLTL discards the next ($\mathcal{N}$) operator since $\mathcal{N}\psi \equiv \Box_{[1,1]}\psi$.

Let $lb, ub \in \mathbb{N}_0, lb \le ub$ and let $I$ be a closed interval $[lb,ub]$; we recursively define that $\pi$ models (satisfies) an ptMLTL formula $\phi$ starting from time index $i \geq 0$, denoted as $\pi,i\models \phi$, as follows:

* $\pi,i\models \sf true$
* $\pi,i\models p$ for $p \in \mathcal{AP}$ iff $p \in \pi(i)$
* $\pi,i\models \neg \psi$ iff $\pi,i\not\models\psi$
* $\pi,i\models\psi\ \wedge\ \xi$ iff $\pi,i\models\psi$ and $\pi,i\models\xi$
* $\pi,i\models\psi\ \vee\ \xi$ iff $\pi,i\models\psi$ or $\pi,i\models\xi$
* $\pi,i\models \mathcal{H}_{[lb,ub]} \psi$ iff $|\pi|\leq i-ub$ or $\forall j\in[i-ub,i-lb]$, $\pi,j\models\psi$
* $\pi,i\models \mathcal{O}_{[lb,ub]} \psi$ iff $|\pi| > i-ub$ and $\exists j\in[i-ub,i-lb]$ such that $\pi,j\models\psi$
* $\pi,i\models \psi\ \mathcal{S}_{[lb,ub]}\ \xi$ iff $|\pi| > i-ub$ and $\exists j\in [i-ub,i-lb]$ such that $\pi,j\models\xi$ and $\forall k>j$ where $k\in [i-ub, i-lb]$, $\pi,k\models\psi$
* $\pi,i\models \psi\ \mathcal{T}_{[lb,ub]}\ \xi$ iff $|\pi| \leq i-ub$ or if $\exists j\in [i-ub,i-lb]$ where $\pi,j\not\models\xi$, then $\exists k > j$ where $k\in [i-ub, i-lb]$ such that $\pi,k\models\psi$

Given two ptMLTL formulas $\psi$ and $\xi$, they are semantically equivalent (denoted by $\psi \equiv \xi$) if and only if $\pi \models \psi \Leftrightarrow \pi \models \xi$ for all traces $\pi$. ptMLTL also keeps the standard operator equivalences from ptLTL, including $\sf false \equiv \neg \sf true$, $\psi\ \vee\ \xi\equiv\neg(\neg \psi\ \wedge\ \neg \xi)$, $\psi \rightarrow \xi \equiv \neg \psi \vee \xi$, $\psi\leftrightarrow\xi\equiv \neg(\psi\oplus\xi)$, $\neg\mathcal{O}_I\psi\equiv\mathcal{H}_I\neg\psi$, $\mathcal{O}\psi\equiv(\sf true\ \mathcal{S}_I\ \psi)$, and $\mathcal{H}\psi\equiv(\sf false\ \mathcal{T}_I\ \psi)$. Notably, ptMLTL discards the previous ($\mathcal{P}$) operator since $\mathcal{P}\psi \equiv \mathcal{H}_{[1,1]}\psi$.

## References
:::{footbibliography}
:::
