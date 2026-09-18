import JSPProblem.Basic

/-!
# JSP-000637 — Degenerate cases of `c n m`

Boundary values of the extremal function `c n m`: the edge count vanishes
for the empty family, for pairwise-incomparable families, and hence
`c n m = 0` for `m ≤ 1` or `m > 2 ^ n`.
-/

open Finset

variable {α : Type*} [DecidableEq α]

/-- The empty family has no edges. -/
theorem edgeCount_empty : edgeCount (∅ : Finset (Finset α)) = 0 := by
  simp only [edgeCount, Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty]
  rw [SimpleGraph.eq_bot_iff_forall_not_adj]
  intro a _ _
  exact absurd a.2 (Finset.notMem_empty _)

/-- If every two distinct members of `F` are incomparable, the edge count is 0. -/
theorem edgeCount_eq_zero_of_pairwise_incomparable
    (F : Finset (Finset α))
    (hF : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬ A ⊆ B ∧ ¬ B ⊆ A) :
    edgeCount F = 0 := by
  simp only [edgeCount, Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty]
  rw [SimpleGraph.eq_bot_iff_forall_not_adj]
  rintro ⟨A, hA⟩ ⟨B, hB⟩ hAdj
  obtain ⟨hne, hsub⟩ := hAdj
  obtain ⟨h1, h2⟩ := hF A hA B hB fun h ↦ hne (Subtype.ext h)
  exact hsub.elim h1 h2

/-- A one-member family has no edges. -/
theorem edgeCount_singleton (A : Finset α) : edgeCount {A} = 0 :=
  edgeCount_eq_zero_of_pairwise_incomparable _ fun X hX Y hY hne ↦
    (hne ((Finset.mem_singleton.mp hX).trans (Finset.mem_singleton.mp hY).symm)).elim

/-- No family has more sets than the full powerset, so `c n m = 0` when
`m > 2 ^ n`. -/
theorem c_eq_zero_of_lt {n m : ℕ} (h : 2 ^ n < m) : c n m = 0 := by
  have hcard : (univ : Finset (Fin n)).powerset.card = 2 ^ n := by
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  have hempty : (univ : Finset (Fin n)).powerset.powersetCard m = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by rwa [hcard])
  simp only [c, hempty, Finset.sup_empty, Nat.bot_eq_zero]

/-- `c n 0 = 0`: the only 0-member family is `∅`, which has no edges. -/
theorem c_zero (n : ℕ) : c n 0 = 0 := by
  simp only [c, Finset.powersetCard_zero, Finset.sup_singleton, edgeCount_empty]

/-- `c n 1 = 0`: a one-member family contains no comparable pair. -/
theorem c_one (n : ℕ) : c n 1 = 0 := by
  simp only [c, ← Nat.bot_eq_zero, Finset.sup_eq_bot_iff]
  intro F hF
  rw [Finset.mem_powersetCard] at hF
  obtain ⟨A, hA⟩ := Finset.card_eq_one.mp hF.2
  rw [hA, Nat.bot_eq_zero]
  exact edgeCount_singleton A

/-- `c n m = 0` whenever `m ≤ 1`. -/
theorem c_eq_zero_of_le_one {n m : ℕ} (h : m ≤ 1) : c n m = 0 := by
  rcases m with _ | _ | m
  · exact c_zero n
  · exact c_one n
  · omega
