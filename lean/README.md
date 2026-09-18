# JSP-000637 — Containment graph edges (Erdős–Daykin–Frankl / ADGS15)

Formalization (Lean 4 + mathlib) of the extremal function `c(n,m)`: the maximum
number of comparable pairs — equivalently, edges of the *containment graph* —
among families of `m` distinct subsets of an `n`-element ground set. This is the
Erdős–Daykin–Frankl function studied in depth by Alon–Das–Glebov–Sudakov,
*Comparable pairs in families of sets*, JCTB 2015 (arXiv:1411.4196), building on
Alon–Frankl (Graphs Combin. 1985).

## Build instructions

- Toolchain: `leanprover/lean4:v4.34.0`, pinned in `lean-toolchain`. Use `elan`;
  it will select/install the pinned toolchain automatically.
- Dependency: mathlib `v4.34.0` (see `lakefile.lean` / `lake-manifest.json`).

From this directory:

```sh
lake exe cache get   # after dependency fetch — downloads prebuilt mathlib oleans
lake build
```

A clean build of the project takes roughly 80–120 s once the mathlib cache is in
place; fetching the cache itself depends on network speed.

## Module map

- `JSPProblem/Basic.lean` — core definitions.
  `Comparable A B` (`A ⊆ B ∨ B ⊆ A`); `containmentGraph F`, the `SimpleGraph` on
  the family `F` joining distinct comparable members; `edgeCount F`, the number
  of edges of that graph; and the extremal function
  `c n m = ((univ : Finset (Fin n)).powerset.powersetCard m).sup edgeCount`,
  i.e. the maximum edge count over all `m`-element families of subsets of
  `Fin n`.
- `JSPProblem/UpperBound.lean` — the universal bound.
  `edgeCount_le`: `edgeCount F ≤ F.card.choose 2` (a graph on `m` vertices has
  at most `m.choose 2` edges); `c_le`: `c n m ≤ m.choose 2` for all `n m`.
- `JSPProblem/Chain.lean` — the chain construction.
  `initSeg n k` (the initial segment `{0,…,k-1}` of `Fin n`) and `chainFam n m`
  (the family of `m` nested initial segments), with `initSeg_mono`, `initSeg_ne`,
  `chainFam_comparable`, `chainFam_card`, `chainFam_mem`,
  `containmentGraph_chainFam` (the containment graph of a chain is the complete
  graph), `chainFam_edgeCount`, and `chainFam_le_c`:
  `m.choose 2 ≤ c n m` whenever `m ≤ n + 1`.
- `JSPProblem/Zero.lean` — degenerate regimes.
  `edgeCount_empty`, `edgeCount_eq_zero_of_pairwise_incomparable`,
  `edgeCount_singleton`, and the boundary values `c_zero` (`c n 0 = 0`),
  `c_one` (`c n 1 = 0`), `c_eq_zero_of_le_one` (`c n m = 0` for `m ≤ 1`), and
  `c_eq_zero_of_lt` (`c n m = 0` for `m > 2 ^ n`, since no such family exists).
- `JSPProblem/FullPowerset.lean` — the full-powerset regime.
  A degree calculation (`degree_full`, private) feeding the handshake lemma to
  show `edgeCount_univ_powerset`: the containment graph of the full powerset of
  `Fin n` has exactly `3 ^ n - 2 ^ n` edges; hence `c_two_pow`:
  `c n (2 ^ n) = 3 ^ n - 2 ^ n` (the powerset is the unique `2 ^ n`-element
  family).
- `JSPProblem/ChainBound.lean` — beyond the chain regime.
  `chain_card_le` (a pairwise-comparable family in `Fin n` has at most
  `n + 1` members), `edgeCount_lt_of_exists_incomparable` (a non-clique family
  has strictly fewer than `m.choose 2` edges), and `c_lt_choose_two`:
  `c n m < m.choose 2` for `m > n + 1`.
- `JSPProblem/LevelBound.lean` — the level-antichain quadratic bound.
  `two_mul_edgeCount_le`: `2 (n+1) · edgeCount F ≤ n · #F²` for every family
  `F` over `Fin n` (ordered-pair count: the `n+1` cardinality levels are
  antichains, plus Cauchy–Schwarz), and `two_mul_c_le`:
  `2 (n+1) · c n m ≤ n · m²`. Exact on chains.
- `JSPProblem/LevelBound2.lean` — independent second proof of the same bound
  via unordered (Sym2) counting: `two_mul_edgeCount_le_q`, `two_mul_c_le_q`.
- `JSPProblem/TwoCube.lean` — constructions in the middle regime.
  `edgeCount_mono` (enlarging a family only adds edges), `c_mono`
  (`c n m₁ ≤ c n m₂` for `m₁ ≤ m₂ ≤ 2 ^ n`), `initSeg_card`, and
  `twoCube_le_c`: the Alon–Frankl tower of two cubes,
  `4 ^ k - 1 ≤ c (2k) (2 ^ (k+1) - 1)`.
- `JSPProblem.lean` — root module importing all of the above; contains
  `c_eq_choose_two`: `c n m = m.choose 2` for `m ≤ n + 1`, the exact value in
  the chain regime, obtained as `le_antisymm (c_le n m) (chainFam_le_c h)`,
  and the headline theorem `containmentGraph_maxEdges_ADGS15` bundling the
  complete characterization of `c n m` over all admissible `n m` (see below).

## Honest status

Proved (no proof placeholders anywhere in the sources; `#print axioms
containmentGraph_maxEdges_ADGS15` shows only `propext`, `Classical.choice`,
`Quot.sound`):

- Headline: `containmentGraph_maxEdges_ADGS15 (n m)` — a conjunction covering
  every admissible `n m`:
  - chain regime `m ≤ n + 1`: `c n m = m.choose 2` (exact);
  - universal quadratic bound `2 (n+1) · c n m ≤ n · m²`, exact on chains;
  - beyond chains `n + 1 < m`: `c n m < m.choose 2`;
  - powerset regime `m = 2 ^ n`: `c n m = 3 ^ n - 2 ^ n` (exact);
  - degenerate regimes `m ≤ 1` or `2 ^ n < m`: `c n m = 0`;
  - Alon–Frankl tower of two cubes: `4 ^ k - 1 ≤ c (2k) (2 ^ (k+1) - 1)`;
  - monotonicity `c n m₁ ≤ c n m₂` for `m₁ ≤ m₂ ≤ 2 ^ n`.
- Supporting: `c_le`, `edgeCount_le`, `chain_card_le`,
  `edgeCount_lt_of_exists_incomparable`, `two_mul_edgeCount_le`(+`_q`),
  `edgeCount_mono`, `c_mono`, `edgeCount_univ_powerset`, and the boundary
  lemmas in `Zero.lean`.

Not formalized:

- No closed form for `c n m` exists in the intermediate regime
  `n + 1 < m < 2 ^ n` even in the literature; ADGS15 itself gives *asymptotic*
  bounds there (Theorem 1.3's two-family entropy estimate
  `c(A,B) ≤ 2^{-d/300} |A||B|`, the stability theorem 1.4, the sparse estimate
  `i(n,nℓ) ≥ (1/2−ε)nℓ² log ℓ`, and the dense-regime structure theorem 1.7).
  Those analytic refinements — the entropy/Shearer bound, real-exponent
  calculus lemmas — are not formalized.

`lake build` succeeds with complete proofs and the required headline theorem
present. No claim of Justin Sun Prize acceptance is made or implied; semantic
adequacy of the headline statement versus the paper is recorded in
`../SCOPE.md`. Formalization operators: **Yi-111-a**
(public repository: https://github.com/Yi-111-a/jsp-000637-containment-graph).
