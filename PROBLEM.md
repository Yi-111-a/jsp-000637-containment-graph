# JSP-000637 — How many edges can the containment graph of a set family have?

- **id:** JSP-000637
- **title:** How many edges can the containment graph of a set family have?
- **area:** Graph theory / Combinatorics
- **status:** Solved
- **Lean:** No
- **Eligible / Claim:** No / Unavailable
- **role:** Trial order #2

## Statement

How many edges can the containment graph of a set family have?

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000637
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- [AlFr85] The maximum number of disjoint pairs in a family of subsets — Graphs Combin. (1985). DOI: https://doi.org/10.1007/bf02582924
- [ADGS15] Comparable pairs in families of sets — JCTB (2015). arXiv: https://arxiv.org/abs/1411.4196

Prefer **ADGS15** as the main formalization source.

## Lean / related libraries

- No complete Lean proof of this problem located.
- mathlib4 has general poset/graph infrastructure, but no ready-made “containment graph extremal number” theorem that can be submitted as the full proof.
- No corresponding erdosproblems.com entry located (catalog also unbound to an Erdős number).

## Success criteria

- `lake build` succeeds
- `sorry` and `admit` counts are zero
- no new axioms
- final commit SHA and build evidence recorded

## Notes

Expect to define the containment graph from scratch in Lean. Exact hypotheses and extremal expression must match ADGS15 / catalog before submission.
