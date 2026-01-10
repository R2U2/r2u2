**Key for Interval Definitions:**

* *`[time(a0)]`*: `[t_l, t_u]`
* *`[lmintime(a0)]`*: `[t_l, M]`
* *`[umintime(a0)]`*: `[0, t_l]`
* *`[utb(a0)]`*: `[0, t_u]`
* *`utb(a0)`* is translated to **`[0, t_u]`** (representing ).
* *`[gap(a0)]`* / *`[maxgap(a0)]`*: `[0, t_gap]` (representing )
* *`[trigger(a0)]`*: `[0, M]` (Default mission time as table entry is empty)
* *`[elapsed(a0)]`*: `[0, M]` (Used as a temporal bound for "eventually" in Before a2 scopes)
* Operators without explicit bounds in the source are assigned **`[0, M]`**.

* *Note: `Ch(i)` is defined recursively as `F[0, t_u] (T_i & Ch(i+1))*`

Table 3: Occurrence Patterns

#### 1. Absence

* **Globally**: `G[t_l, t_u] !a0`
* **Before {a2}**: `F[t_l, M] a2 -> (!a0 U[t_l, t_u] a2 | G[t_l, t_u] !a0)`
* **After {a1}**: `a1 -> G[t_l, t_u] !a0`
* **Between {a1} and {a2}**: `(a1 & G[0, t_l] !a2 & F[t_l, M] a2) -> (!a0 U[t_l, t_u] a2 | G[t_l, t_u] !a0)`
* **After {a1} until {a2}**: `(a1 & G[0, t_l] !a2) -> ((!a0 U[t_l, t_u] a2) | G[t_l, t_u] !a0)`

#### 2. Universality

* **Globally**: `G[t_l, t_u] a0`
* **Before {a2}**: `F[t_l, M] a2 -> (a0 U[t_l, t_u] a2 | G[t_l, t_u] a0)`
* **After {a1}**: `a1 -> G[t_l, t_u] a0`
* **Between {a1} and {a2}**: `(a1 & G[0, t_l] !a2 & F[t_l, M] a2) -> (a0 U[t_l, t_u] a2 | G[t_l, t_u] a0)`
* **After {a1} until {a2}**: `(a1 & G[0, t_l] !a2) -> ((a0 U[t_l, t_u] a2) | G[t_l, t_u] a0)`

#### 3. Existence

* **Globally**: `F[t_l, t_u] a0`
* **Before {a2}**: `(!a2 U[t_l, t_u] (a0 & !a2)) | G[t_l, t_u] !a2`
* **After {a1}**: `a1 -> F[t_l, t_u] a0`
* **Between {a1} and {a2}**: `(a1 & G[0, t_l] !a2 & F[t_l, M] a2) -> (!a2 U[t_l, t_u] (a0 & !a2))`
* **After {a1} until {a2}**: `(a1 & G[0, t_l] !a2) -> (!a2 U[t_l, t_u] (a0 & !a2))`

#### 4. Minimum Duration

* **Globally**: `a0 | ((!a0 U[0, M] G[0, t_u] a0) | G[0, M] !a0)`
* **Before {a2}**: `(a0 | (!a0 U[0, M] (G[0, t_u] (a0 & !a2) | a2))) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (a0 | ((!a0 U[0, M] G[0, t_u] a0) | G[0, M] !a0))`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[0, M] a2) -> ((a0 | (!a0 U[0, M] (G[0, t_u] (a0 & !a2) | a2))) U[0, M] a2)`
* **After {a1} until {a2}**: `(a1 & !a2) -> (((a0 | ((!a0 U[0, M] (G[0, t_u] (a0 & !a2) | a2)) | G[0,M] !a0)) U[0, M] a2) | G[0,M] (a0 | ((!a0 U[0, M] (G[0, t_u] (a0 & !a2) | a2)) | G[0,M] !a0)))`

#### 5. Maximum Duration

* **Globally**: `a0 | ((!a0 U[0, M] (a0 & F[0, t_u] !a0)) | G[0, M] !a0)`
* **Before {a2}**: `(a0 | (!a0 U[0, M] ((a0 & F[0, t_u] (!a0 & a2)) | a2))) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (a0 | ((!a0 U[0, M] (a0 & F[0, t_u] !a0)) | G[0, M] !a0))`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[0, M] a2) -> ((a0 | (!a0 U[0, M] ((a0 & F[0, t_u] (!a0 & a2)) | a2))) U[0, M] a2)`
* **After {a1} until {a2}**: `(a1 & !a2) -> (((a0 | ((!a0 U[0, M] (a0 & F[0, t_u] (!a0 & a2) | a2)) | G[0,M] (!a0))) U[0, M] a2) | G[0,M] (a0 | ((!a0 U[0, M] (a0 & F[0, t_u] (!a0 & a2) | a2)) | G[0,M] (!a0))))`

#### 6. Recurrence

* **Globally**: `F[0, t_u] a0`
* **Before {a2}**: `(F[0, t_u] (a0 | a2)) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (F[0, t_u] a0)`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[0, M] a2) -> ((F[0, t_u] (a0 | a2)) U[0, M] a2)`
* **After {a1} until {a2}**: `(a1 & !a2) -> (((F[0, t_u] (a0 | a2)) U[0, M] a2) | G[0, M] (F[0, t_u] (a0 | a2)))`

---

Table 4: Order Patterns (Precedence Family and Until) 

#### 1. Precedence

* **Globally**: `F[0, M] a0 -> F[0, t_gap] a4`
* **Before {a2}**: `F[t_l, M] a2 -> (F[0, M] a0 -> (F[0, t_gap] a4 | F[0, M] a2)) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (F[0, M] a0 -> F[0, t_gap] a4)`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[t_l, M] a2) -> (F[0, M] a0 -> (F[0, t_gap] a4 | F[0, M] a2)) U[0, M] a2`
* **After {a1} until {a2}**: `(a1 & !a2) -> (((F[0, M] a0 -> (F[0, t_gap] a4 | F[0, M] a2)) U[0, M] a2) | G[0, M] (F[0, M] a0 -> (F[0, t_gap] a4 | F[0, M] a2)))`

#### 2. Precedence Chain (N causes - 1 effect)

* **Globally**: `(F[0, M] (a4 & Ch(1))) -> F[0, t_gap] a0`
* **Before {a2}**: `F[t_l, M] a2 -> ((F[0, M] (a4 & Ch(1))) -> (F[0, t_gap] a0 | F[0, t_gap] a2)) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] ((F[0, M] (a4 & Ch(1))) -> F[0, t_gap] a0)`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[t_l, M] a2) -> ((F[0, M] (a4 & Ch(1))) -> (F[0, t_gap] a0 | F[0, t_gap] a2)) U[0, M] a2`
* **After {a1} until {a2}**: `(a1 & !a2) -> ((((F[0, M] (a4 & Ch(1))) -> (F[0, t_gap] a0 | F[0, t_gap] a2)) U[0, M] a2) | G[0, M] ((F[0, M] (a4 & Ch(1))) -> (F[0, t_gap] a0 | F[0, t_gap] a2)))`

#### 3. Constrained Precedence Chain

* **Globally**: `(a3 U[0, M] (F[0, M] (a4 & Ch(1)))) -> F[0, t_gap] a0`
* **Before {a2}**: `F[t_l, M] a2 -> (a3 U[0, M] ((F[0, M] (a4 & Ch(1))) -> (F[0, t_gap] a0 | F[0, t_gap] a2))) U[0, M] a2`
* **After {a1}**: `a1 -> (a0 -> (a3 U[0, M] (F[0, M] (a4 & Ch(1)))))`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[t_l, M] a2) -> (a3 U[0, M] ((F[0, M] (a4 & Ch(1))) -> (F[0, t_gap] a0 | F[0, t_gap] a2))) U[0, M] a2`

#### 4. Until

* **Globally**: `a0 U[t_l, t_u] a4`
* **Before {a2}**: `F[t_l, M] a2 -> (a0 U[t_l, t_u] (a4 | a2))`
* **After {a1}**: `a1 -> (a0 U[t_l, t_u] a4)`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[t_l, M] a2) -> (a0 U[t_l, t_u] (a4 | a2))`
* **After {a1} until {a2}**: `(a1 & F[0, t_l] !a2) -> ((a0 U[t_l, t_u] a2) | G[t_l, t_u] a0)`

---

Table 5: Order Patterns (Response Family) 

#### 1. Response

* **Globally**: `a0 -> F[t_l, t_u] a4`
* **Before {a2}**: `F[t_l, M] a2 -> (a0 -> (a2 | F[t_l, t_u] (a4 & !a2))) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (a0 -> F[t_l, t_u] a4)`
* **Between {a1} and {a2}**: `(a1 & F[0, t_l] !a2 & F[t_l, M] a2) -> (a0 -> (a2 | F[t_l, t_u] (a4 & !a2))) U[0, M] a2`
* **After {a1} until {a2}**: `(a1 & F[0, t_l] !a2) -> (((a0 -> (a2 | F[t_l, t_u] (a4 & !a2))) U[0, M] a2) | G[0, M] (a0 -> (a2 | F[t_l, t_u] (a4 & !a2))))`

#### 2. Constrained Response

* **Globally**: `a0 -> (a3 U[t_l, t_u] a4)`
* **Before {a2}**: `F[t_l, M] a2 -> (a0 -> ((a2 | a3) U[t_l, t_u] (a4 & !a2))) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (a0 -> (a3 U[t_l, t_u] a4))`
* **Between {a1} and {a2}**: `(a1 & F[0, t_l] !a2 & F[t_l, M] a2) -> (a0 -> ((a2 | a3) U[t_l, t_u] (a4 & !a2))) U[0, M] a2`

#### 3. Response Chain (1 stimulus - N responses)

* **Globally**: `a0 -> (F[0, t_u] (a4 & Ch(1)))`
* **Before {a2}**: `F[t_l, M] a2 -> (a0 -> (a2 | F[0, t_u] (a4 & Ch(1)))) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (a0 -> (F[0, t_u] (a4 & Ch(1))))`
* **Between {a1} and {a2}**: `(a1 & !a2 & F[t_l, M] a2) -> (a0 -> (a2 | F[0, t_u] (a4 & Ch(1)))) U[0, M] a2`
* **After {a1} until {a2}**: `(a1 & !a2) -> (((a0 -> (a2 | F[0, t_u] (a4 & Ch(1)))) U[0, M] a2) | G[0, M] (a0 -> (a2 | F[0, t_u] (a4 & Ch(1)))))`
* *Note: `Ch(i)` is defined recursively using `F[0, t_u] (T_i & Ch(i+1))*`

#### 4. Response Invariance

* **Globally**: `a0 -> G[t_l, t_u] a4`
* **Before {a2}**: `F[t_l, M] a2 -> (a0 -> G[t_l, t_u] (a4 & !a2)) U[0, M] a2`
* **After {a1}**: `a1 -> G[0, M] (a0 -> G[t_l, t_u] a4)`
* **Between {a1} and {a2}**: `(a1 & F[0, t_l] !a2 & F[t_l, M] a2) -> (a0 -> G[t_l, t_u] (a4 & !a2)) U[0, M] a2`
* **After {a1} until {a2}**: `(a1 & F[0, t_l] !a2) -> (((a0 -> G[t_l, t_u] (a4 & !a2)) U[0, M] a2) | G[0, M] (a0 -> G[t_l, t_u] (a4 & !a2)))`