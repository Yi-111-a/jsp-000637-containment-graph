# ACCEPTANCE — JSP-000637 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000637
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> How many edges can the containment graph of a set family have?

Catalog description matches the above. The accepted answer is the full extremal characterization of the maximum number of containment-graph edges (comparable pairs) among families of \(m\) subsets of an \(n\)-element ground set, as solved in ADGS15 (Alon–Das–Glebov–Sudakov, *Comparable pairs in families of sets*, JCTB 2015), building on AlFr85.

Partial regimes alone (e.g. only the chain case \(m\le n+1\), or only the full powerset \(m=2^n\)) are **not** the full original statement.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `containmentGraph_maxEdges_ADGS15` | Full ADGS15 characterization of \(c(n,m)\) (maximum containment-graph edges) for all admissible \(n,m\), matching the catalog/paper theorem (not only chain or powerset special cases). |

**Not sufficient for prize_ready:** `c_eq_choose_two` (chain regime only), `c_two_pow` (powerset only), `c_le`, `c_eq_zero_of_lt`, or other fragment lemmas.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.

`partial_ok` may be true for harness-green partial regimes; never treat as SUCCESS for the prize.
