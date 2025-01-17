# Mission-time Linear Temporal Logic

Mission-time Linear Temporal Logic (MLTL) enables unambiguous descriptions of behaviors, including complex, temporal behaviors, that comprise requirements, fault signatures, sanity checks, or other properties of a system we might want to observe using R2U2. While there are many temporal logics, MLTL strikes a nice balance of being expressive enough to capture many common properties from aerospace operational concepts while still being easy to validate and efficiently monitorable. 

## References

MLTL was first defined in {footcite:p}`RRS14`. MLTL satisfiability and its complexity appears in {footcite:p}`LVR19`. MLTL validation (checking that an MLTL formula represents exactly the behavior intended) strategies include consulting the formal semantics, truth table validation, satisfiability checking, transition machine visualizations, which all appear in detail in {footcite:p}`RDR22`. We can also validate formulas through oracle generation {footcite:p}`LR18`. The WEST tool provides an (open-source) interactive GUI for MLTL visualization {footcite:p}`EGSTWR23`. The R2U2 GUI provides additional tools for profiling MLTL specifications, including calculating the size of monitor instances for equivalent MLTL formulas {footcite:p}`JJKRZ23`.

## MLTL Formal Semantics

R2U2 implements the following formal semantics for MLTL.

We interpret MLTL formulas over finite traces bounded by base-10 (decimal) intervals.
Let $\pi$ be a finite computation of bounded length $|\pi| <+\infty$.
We use $\pi_i\ (|\pi|>i\geq 0)$ to represent the suffix of $\pi$ starting from position $i$ (including $i$).
$\pi_i = \epsilon$ (empty trace) if $i\geq |\pi|$.
Let $a, b \in \mathbb{I}, a \le b$; we define that $\pi$ models (satisfies) an MLTL formula $\phi$, denoted as $\pi\models \phi$, as follows:

* $\pi\models p$ iff $p\in\pi[0]$;
* $\pi\models \neg \phi$ iff $\pi\not\models\phi$;
* $\pi\models\phi\wedge\psi$ iff $\pi\models\phi$ and $\pi\models\psi$;
* $\pi\models \phi \ \mathcal{U}_{[a,b]} \ \psi$ iff $|\pi|> a$ and, there exists $i\in [a,b]$, $i<|\pi|$ such that $\pi_i\models\psi$ and for every $j\in [a,b], j<i$ it holds that $\pi_j\models\phi$;
* $\pi\models \phi \mathcal{R}_{[a,b]}\psi$ iff $|\pi|\leq a$ or for every $i\in [a,b]$, $i<|\pi|$, either  $\pi_i\models\psi$ holds or there exists $j\in [a,b]$, $j\leq i$ s.t. $\pi_j \models \phi$.

## References
:::{footbibliography}
:::
