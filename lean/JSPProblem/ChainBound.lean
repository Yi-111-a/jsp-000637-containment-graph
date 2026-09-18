import JSPProblem.Basic

/-!
# JSP-000637 — Strict bound on the containment graph of a non-chain family

A family of pairwise-comparable subsets of `Fin n` has at most `n + 1`
members (cardinality is injective on a chain).  Consequently, whenever
`m > n + 1` every `m`-element family contains an incomparable pair, so its
containment graph is a *strict* subgraph of the complete graph and has
strictly fewer than `m.choose 2` edges.  Hence `c n m < m.choose 2`.
-/

open Finset

variable {α : Type*} [DecidableEq α]

/-- In a family of pairwise-comparable subsets of `Fin n`, cardinality is
injective, so the family has at most `n + 1` members. -/
theorem chain_card_le {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : ∀ A ∈ F, ∀ B ∈ F, Comparable A B) : F.card ≤ n + 1 := by
  have hinj : Set.InjOn Finset.card (F : Set (Finset (Fin n))) := by
    intro A hA B hB hAB
    rw [Finset.mem_coe] at hA hB
    rcases hF A hA B hB with hsub | hsub
    · exact Finset.eq_of_subset_of_card_le hsub hAB.ge
    · exact (Finset.eq_of_subset_of_card_le hsub hAB.le).symm
  rw [← Finset.card_image_of_injOn hinj]
  calc (F.image Finset.card).card
      ≤ (Finset.range (n + 1)).card := Finset.card_le_card (by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨A, -, rfl⟩ := hx
        rw [Finset.mem_range]
        have hc : A.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ A)
        rw [Finset.card_univ, Fintype.card_fin] at hc
        omega)
    _ = n + 1 := Finset.card_range (n + 1)

/-- If a family contains an incomparable pair, its containment graph is a
strict subgraph of the complete graph, so it has strictly fewer than
`F.card.choose 2` edges. -/
theorem edgeCount_lt_of_exists_incomparable {F : Finset (Finset α)}
    (h : ∃ A ∈ F, ∃ B ∈ F, A ≠ B ∧ ¬ Comparable A B) :
    edgeCount F < F.card.choose 2 := by
  classical
  obtain ⟨A, hA, B, hB, hne, hinc⟩ := h
  have hne' : (⟨A, hA⟩ : ↥F) ≠ ⟨B, hB⟩ := fun e ↦ hne (congrArg Subtype.val e)
  unfold edgeCount
  rw [← Fintype.card_coe F, ← SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  apply Finset.card_lt_card
  rw [SimpleGraph.edgeFinset_ssubset_edgeFinset, lt_top_iff_ne_top]
  intro htop
  have hadj : (containmentGraph F).Adj ⟨A, hA⟩ ⟨B, hB⟩ := by
    rw [htop]
    exact (SimpleGraph.top_adj _ _).mpr hne'
  exact hinc hadj.2

/-- When `m > n + 1`, no `m`-element family of subsets of `Fin n` can be a
chain, so `c n m` is strictly less than `m.choose 2`. -/
theorem c_lt_choose_two {n m : ℕ} (h : n + 1 < m) : c n m < m.choose 2 := by
  classical
  have hpos : 0 < m.choose 2 := Nat.choose_pos (show 2 ≤ m by omega)
  suffices hs : c n m ≤ m.choose 2 - 1 by omega
  unfold c
  apply Finset.sup_le
  intro F hF
  rw [Finset.mem_powersetCard] at hF
  obtain ⟨hsub, hcard⟩ := hF
  have hnp : ¬ (∀ A ∈ F, ∀ B ∈ F, Comparable A B) := fun hchain ↦ by
    have hle := chain_card_le hchain
    omega
  push Not at hnp
  obtain ⟨A, hA, B, hB, hinc⟩ := hnp
  have hne : A ≠ B := by
    rintro rfl
    exact hinc (Or.inl (Finset.Subset.refl A))
  have hlt := edgeCount_lt_of_exists_incomparable ⟨A, hA, B, hB, hne, hinc⟩
  rw [hcard] at hlt
  omega
