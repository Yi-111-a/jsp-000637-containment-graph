import JSPProblem.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card

open Finset

/-- The ordered-pair bound: the containment graph of a family `F` of subsets of
`Fin n` satisfies `2 (n+1) · #edges ≤ n · #F²`.  Counting ordered pairs of
distinct members of `F` gives `#C + #I = #F² - #F` where `C` are the comparable
pairs (`#C = 2 · #edges` by the handshake lemma).  Distinct same-cardinality
sets are incomparable, so the `f k · (f k − 1)` pairs inside each level
`lvl k` lie in `I`, giving `2·e + ∑ f k² ≤ #F²`.  Cauchy–Schwarz
`#F² = (∑ f k)² ≤ (n+1) ∑ f k²` then finishes the proof. -/
theorem two_mul_edgeCount_le {n : ℕ} (F : Finset (Finset (Fin n))) :
    2 * (n + 1) * edgeCount F ≤ n * F.card * F.card := by
  classical
  set m := F.card with hm
  set lvl : ℕ → Finset (Finset (Fin n)) := fun k ↦ F.filter (fun A ↦ A.card = k) with hlvl
  set f : ℕ → ℕ := fun k ↦ (lvl k).card with hf
  have hcardF : ∀ A ∈ F, A.card ∈ Finset.range (n + 1) := by
    intro A hA
    have h := Finset.card_le_univ A
    rw [Fintype.card_fin] at h
    exact Finset.mem_range.mpr (by omega)
  -- The level sizes `f k` sum to `m`.
  have hsumf : (∑ k ∈ Finset.range (n + 1), f k) = m := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (s := F) (t := Finset.range (n + 1)) (f := fun A ↦ A.card)
      (fun A hA ↦ Finset.mem_coe.mpr (hcardF A (Finset.mem_coe.mp hA)))
    rw [← hm] at hfib
    rw [hfib]
  -- `m ≤ m²` is needed to clear natural subtractions.
  have hmm : m ≤ m * m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · nth_rewrite 1 [← mul_one m]
      exact Nat.mul_le_mul (Nat.le_refl m) h
  -- The comparable ordered pairs number `2 * edgeCount F` (handshake lemma).
  have hC : #(F.offDiag.filter (fun p ↦ p.1 ⊆ p.2 ∨ p.2 ⊆ p.1)) = 2 * edgeCount F := by
    have hinj : Function.Injective (fun q : ↥F × ↥F ↦ (q.1.1, q.2.1)) := by
      rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      exact Prod.ext_iff.mpr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have himg : F.offDiag.filter (fun p ↦ p.1 ⊆ p.2 ∨ p.2 ⊆ p.1) =
        (Finset.univ.filter (fun (x, y) ↦ (containmentGraph F).Adj x y)).image
          (fun q : ↥F × ↥F ↦ (q.1.1, q.2.1)) := by
      apply Finset.ext
      rintro ⟨A, B⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_image,
        Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hAF, hBF, hne⟩, hcomp⟩
        exact ⟨(⟨A, hAF⟩, ⟨B, hBF⟩),
          ⟨fun e ↦ hne (Subtype.ext_iff.mp e), hcomp⟩, rfl, rfl⟩
      · rintro ⟨⟨a, b⟩, hAdj, h1, h2⟩
        subst h1; subst h2
        obtain ⟨hne, hcomp⟩ := hAdj
        exact ⟨⟨a.2, b.2, fun e ↦ hne (Subtype.ext e)⟩, hcomp⟩
    rw [himg, Finset.card_image_of_injective _ hinj]
    unfold edgeCount
    exact (SimpleGraph.two_mul_card_edgeFinset (containmentGraph F)).symm
  -- Comparable and incomparable ordered pairs partition `F.offDiag`.
  have hCI : #(F.offDiag.filter (fun p ↦ p.1 ⊆ p.2 ∨ p.2 ⊆ p.1)) +
      #(F.offDiag.filter (fun p ↦ ¬(p.1 ⊆ p.2 ∨ p.2 ⊆ p.1))) = m * m - m := by
    rw [hm, ← Finset.offDiag_card]
    exact Finset.card_filter_add_card_filter_not _
  -- All ordered pairs of distinct same-cardinality members are incomparable.
  have hsub : (Finset.range (n + 1)).biUnion (fun k ↦ (lvl k).offDiag) ⊆
      F.offDiag.filter (fun p ↦ ¬(p.1 ⊆ p.2 ∨ p.2 ⊆ p.1)) := by
    rw [Finset.biUnion_subset]
    intro k _ p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨hp1, hp2, hne⟩ := hp
    simp only [hlvl, Finset.mem_filter] at hp1 hp2
    obtain ⟨hF1, hk1⟩ := hp1
    obtain ⟨hF2, hk2⟩ := hp2
    rw [Finset.mem_filter, Finset.mem_offDiag]
    refine ⟨⟨hF1, hF2, hne⟩, fun hor ↦ ?_⟩
    rcases hor with hsub | hsub
    · exact hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hk2.trans hk1.symm)))
    · exact hne ((Finset.eq_of_subset_of_card_le hsub
        (le_of_eq (hk1.trans hk2.symm))).symm)
  -- The level off-diagonals are pairwise disjoint.
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
      (fun k ↦ (lvl k).offDiag) := by
    intro k₁ _ k₂ _ hne
    refine Finset.disjoint_left.mpr fun p hp1 hp2 ↦ ?_
    rw [Finset.mem_offDiag] at hp1 hp2
    simp only [hlvl, Finset.mem_filter] at hp1 hp2
    exact hne (hp1.1.2.symm.trans hp2.1.2)
  -- Their total cardinality is `∑ k, (f k * f k - f k)`.
  have hcard_bU : #((Finset.range (n + 1)).biUnion (fun k ↦ (lvl k).offDiag))
      = ∑ k ∈ Finset.range (n + 1), (f k * f k - f k) := by
    rw [Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [Finset.offDiag_card])
  -- Hence `2e + ∑ (f k * f k - f k) ≤ m * m - m`.
  have hle : 2 * edgeCount F +
      #((Finset.range (n + 1)).biUnion (fun k ↦ (lvl k).offDiag)) ≤ m * m - m := by
    have hIle := Finset.card_le_card hsub
    omega
  -- Rewrite `∑ f k * f k` without subtraction: `∑ f k² = #biUnion + m`.
  have hS : (∑ k ∈ Finset.range (n + 1), f k * f k) =
      #((Finset.range (n + 1)).biUnion (fun k ↦ (lvl k).offDiag)) + m := by
    have hff : ∀ k, f k ≤ f k * f k := by
      intro k
      rcases Nat.eq_zero_or_pos (f k) with h | h
      · simp [h]
      · nth_rewrite 1 [← mul_one (f k)]
        exact Nat.mul_le_mul (Nat.le_refl _) h
    calc (∑ k ∈ Finset.range (n + 1), f k * f k)
        = ∑ k ∈ Finset.range (n + 1), (f k * f k - f k + f k) :=
          Finset.sum_congr rfl (fun k _ ↦ (Nat.sub_add_cancel (hff k)).symm)
      _ = (∑ k ∈ Finset.range (n + 1), (f k * f k - f k)) +
            ∑ k ∈ Finset.range (n + 1), f k := Finset.sum_add_distrib
      _ = #((Finset.range (n + 1)).biUnion (fun k ↦ (lvl k).offDiag)) + m := by
          rw [← hcard_bU, hsumf]
  -- So `2e + ∑ f k² ≤ m²`.
  have hmain : 2 * edgeCount F + (∑ k ∈ Finset.range (n + 1), f k * f k) ≤ m * m := by
    omega
  -- Cauchy–Schwarz: `m² = (∑ f k)² ≤ (n+1) ∑ f k²`.
  have hCS : m * m ≤ (n + 1) * (∑ k ∈ Finset.range (n + 1), f k * f k) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (n + 1)) (f := f)
    rw [Finset.card_range, hsumf] at h
    simp only [sq] at h
    exact h
  -- Multiply by `n + 1`, cancel `m * m` on the right.
  have h3 := Nat.mul_le_mul (Nat.le_refl (n + 1)) hmain
  rw [mul_add, mul_left_comm (n + 1) 2 (edgeCount F),
    ← mul_assoc 2 (n + 1) (edgeCount F)] at h3
  have h5 : (n + 1) * (m * m) = n * (m * m) + m * m := by rw [add_mul, one_mul]
  rw [h5] at h3
  have h4 : 2 * (n + 1) * edgeCount F + m * m ≤ n * (m * m) + m * m := by omega
  have h6 : 2 * (n + 1) * edgeCount F ≤ n * (m * m) := by omega
  rwa [← mul_assoc] at h6

/-- `2 (n+1) · c n m ≤ n · m²`: the sup is attained by some family of `m` sets,
to which `two_mul_edgeCount_le` applies (or the index finset is empty). -/
theorem two_mul_c_le (n m : ℕ) : 2 * (n + 1) * c n m ≤ n * m * m := by
  classical
  unfold c
  rcases Finset.eq_empty_or_nonempty
      ((Finset.univ : Finset (Fin n)).powerset.powersetCard m) with h | h
  · rw [h, Finset.sup_empty]
    simp
  · obtain ⟨F, hF, hsup⟩ := Finset.exists_mem_eq_sup _ h edgeCount
    rw [hsup]
    rw [Finset.mem_powersetCard] at hF
    rw [← hF.2]
    exact two_mul_edgeCount_le F
