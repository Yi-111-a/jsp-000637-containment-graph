import JSPProblem.Basic
import JSPProblem.UpperBound
import JSPProblem.Chain
import JSPProblem.Zero
import JSPProblem.FullPowerset

/-!
# JSP-000637 — Edges of the containment graph of a set family

The *containment graph* of a family `F` of finite sets joins distinct
`A B ∈ F` iff `A ⊆ B` or `B ⊆ A`.  Writing `c(n,m)` for the maximum number of
edges over families of `m` subsets of `Fin n` (the Erdős–Daykin–Frankl
function studied by Alon–Das–Glebov–Sudakov, *Comparable pairs in families of
sets*, JCTB 2015), this development proves:

* `c_le`             — `c n m ≤ m.choose 2` for all `n m`;
* `chainFam_le_c`    — `m.choose 2 ≤ c n m` whenever `m ≤ n + 1`
                       (the family of nested initial segments is a clique);
* `c_eq_choose_two`  — `c n m = m.choose 2` for `m ≤ n + 1`: the containment
                       graph can have at most `m.choose 2` edges and this is
                       tight exactly in the chain regime;
* `c_zero`, `c_one`, `c_eq_zero_of_le_one`, `c_eq_zero_of_lt` — boundary cases;
* `edgeCount_univ_powerset`, `c_two_pow` — the full powerset family has
  exactly `3^n − 2^n` comparable pairs, so `c n (2^n) = 3^n − 2^n`.
-/

/-- The maximum number of edges of the containment graph of a family of `m`
subsets of `Fin n` is `m.choose 2` whenever an `m`-element chain fits in the
Boolean lattice (`m ≤ n + 1`); the bound is attained by nested initial
segments. -/
theorem c_eq_choose_two {n m : ℕ} (h : m ≤ n + 1) : c n m = m.choose 2 :=
  le_antisymm (c_le n m) (chainFam_le_c h)
