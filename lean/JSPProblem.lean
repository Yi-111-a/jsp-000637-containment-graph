import JSPProblem.Basic
import JSPProblem.UpperBound
import JSPProblem.Chain
import JSPProblem.Zero
import JSPProblem.FullPowerset
import JSPProblem.ChainBound
import JSPProblem.LevelBound
import JSPProblem.TwoCube

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

/-- **The extremal characterization of containment-graph edges** (the
Erdős–Daykin–Frankl function `c n m`, resolved asymptotically by
Alon–Das–Glebov–Sudakov, *Comparable pairs in families of sets*, JCTB 2015 —
"ADGS15").

For all `n m`, the maximum number `c n m` of comparable pairs in a family of
`m` distinct subsets of `Fin n` satisfies, regime by regime:

* `m ≤ n + 1` — **chain regime**: `c n m = m.choose 2`, attained by nested
  initial segments (the only regime where the containment graph can be a
  clique);
* `n + 1 < m` — **beyond chains**: `c n m < m.choose 2`; more precisely the
  level-antichain count gives the exact quadratic bound
  `2 (n+1) · c n m ≤ n · m²` (equality at `m = n + 1`, density `≤ n/(n+1)`
  overall);
* `m = 2 ^ n` — **powerset regime**: `c n m = 3 ^ n - 2 ^ n`, attained uniquely
  by the full powerset;
* `m ≤ 1` or `2 ^ n < m` — **degenerate regimes**: `c n m = 0`;
* **Alon–Frankl tower of two cubes** (the extremal construction behind
  ADGS15's sparse-regime analysis): `4 ^ k - 1 ≤ c (2k) (2 ^ (k+1) - 1)`,
  i.e. a family of `2^(k+1) - 1` sets achieves `≈ m²/4` comparable pairs;
* **monotonicity**: `c n m₁ ≤ c n m₂` for `m₁ ≤ m₂ ≤ 2 ^ n`.

No closed form for `c n m` in the intermediate regime `n + 1 < m < 2 ^ n`
exists in the literature; ADGS15 gives asymptotic bounds there.  This theorem
bundles the complete provable characterization over all admissible `n m`. -/
theorem containmentGraph_maxEdges_ADGS15 (n m : ℕ) :
    (m ≤ n + 1 → c n m = m.choose 2) ∧
    (2 * (n + 1) * c n m ≤ n * m * m) ∧
    (n + 1 < m → c n m < m.choose 2) ∧
    (m = 2 ^ n → c n m = 3 ^ n - 2 ^ n) ∧
    (m ≤ 1 ∨ 2 ^ n < m → c n m = 0) ∧
    (∀ k : ℕ, 4 ^ k - 1 ≤ c (2 * k) (2 ^ (k + 1) - 1)) ∧
    (∀ m₁ m₂ : ℕ, m₁ ≤ m₂ → m₂ ≤ 2 ^ n → c n m₁ ≤ c n m₂) :=
  ⟨c_eq_choose_two, two_mul_c_le n m, c_lt_choose_two,
   fun h ↦ h ▸ c_two_pow n,
   fun h ↦ h.elim c_eq_zero_of_le_one c_eq_zero_of_lt,
   twoCube_le_c, fun _ _ ↦ c_mono⟩
