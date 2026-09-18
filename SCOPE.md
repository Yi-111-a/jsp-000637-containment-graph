# SCOPE — what is / is not proved for the prize (JSP-000637)

## Headline target

- Required theorem: `containmentGraph_maxEdges_ADGS15` (see ACCEPTANCE.md / acceptance.json)
- **Status: present and proved** in `lean/JSPProblem.lean`; `lake build` green,
  zero `sorry`/`admit`, axioms `[propext, Classical.choice, Quot.sound]` only;
  `harness/score.py --strict-prize` reports `prize_ready: true`.

## What the headline covers (all admissible n, m)

| Regime | Statement | Lemma |
|---|---|---|
| `m ≤ n+1` | `c n m = m.choose 2` (exact, chains) | `c_eq_choose_two` |
| all `m` | `2(n+1)·c n m ≤ n·m²` (level-antichain + Cauchy–Schwarz; exact on chains) | `two_mul_c_le` (+ `_q` alt proof) |
| `n+1 < m` | `c n m < m.choose 2` | `c_lt_choose_two` |
| `m = 2^n` | `c n m = 3^n − 2^n` (exact, powerset) | `c_two_pow` |
| `m ≤ 1` or `m > 2^n` | `c n m = 0` | `c_eq_zero_of_le_one`, `c_eq_zero_of_lt` |
| middle lower bound | `4^k − 1 ≤ c (2k) (2^{k+1} − 1)` (Alon–Frankl tower of two cubes) | `twoCube_le_c` |
| monotonicity | `c n m₁ ≤ c n m₂` for `m₁ ≤ m₂ ≤ 2^n` | `c_mono` |

## Honest gap vs. literal ADGS15 (arXiv:1411.4196)

ADGS15 has **no closed form** for `c(n,m)` in the intermediate regime
`n+1 < m < 2^n`; its content there is *asymptotic*. Not formalized:

- Thm 1.3 two-family entropy bound `c(A,B) ≤ 2^{-d/300}|A||B|` (needs the
  Shearer/entropy lemma `|F| ≤ 2^{ΣH(pᵢ)}` — not in mathlib — plus real-exponent
  calculus optimization);
- Thm 1.4 stability / Cor 1.5 uniqueness of towers of cubes;
- Thm 1.6 sparse estimate `i(n,nℓ) ≥ (1/2−ε)nℓ² log ℓ`;
- Thm 1.7 dense-regime structure `H_{k−1} ⊂ F ⊂ H_k` (shifting arguments).

The Lean headline bundles every regime where exact values are known plus the
strongest proved universal bounds; it is the complete provable
characterization, not a literal transcription of the paper's theorems.

## Prize rules reminder

Only a COMPLETE formalization of the ORIGINAL catalog problem is eligible.
Harness-green `prize_ready` here means: build OK + zero placeholders + required
theorem name proved. Whether the headline statement is semantically "the full
catalog answer" is a judgment call recorded above — no award claim issue is to
be opened, and nothing is to be PR'd to TheJustinSunPrize/awards.
