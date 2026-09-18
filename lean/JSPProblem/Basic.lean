import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# JSP-000637 — Edges of the containment graph of a set family

For a family `F` of finite sets, its *containment graph* has vertex set `F`
with `A B` joined iff `A ≠ B` and `A ⊆ B` or `B ⊆ A`.  The extremal function
`c(n,m)` (Erdős–Daykin–Frankl; Alon–Das–Glebov–Sudakov, *Comparable pairs in
families of sets*, JCTB 2015) is the maximum number of comparable pairs
occurring in a family of `m` distinct subsets of `Fin n`.
-/

open Finset

variable {α : Type*} [DecidableEq α]

/-- Two finsets are *comparable* when one contains the other. -/
def Comparable (A B : Finset α) : Prop := A ⊆ B ∨ B ⊆ A

/-- The containment graph of a family `F` of finsets: vertices are the members
of `F`; `A B` are adjacent iff they are distinct and comparable. -/
def containmentGraph (F : Finset (Finset α)) : SimpleGraph F where
  Adj A B := A ≠ B ∧ (A.1 ⊆ B.1 ∨ B.1 ⊆ A.1)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- The number of edges of the containment graph of `F`, i.e. the number of
unordered comparable pairs of distinct members of `F`. -/
noncomputable def edgeCount (F : Finset (Finset α)) : ℕ := by
  classical
  exact (containmentGraph F).edgeFinset.card

/-- `c n m`: the maximum number of comparable pairs among families of `m`
distinct subsets of `Fin n`. -/
noncomputable def c (n m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).powerset.powersetCard m).sup edgeCount
