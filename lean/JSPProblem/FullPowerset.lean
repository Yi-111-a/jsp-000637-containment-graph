import JSPProblem.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Card

open Finset

/-- Classical finiteness instance for neighbourhoods in the containment graph of
the full powerset of `Fin n`, fixed so it agrees with the classical instances
inside `edgeCount`. -/
private noncomputable instance instFintypeNbr (n : ℕ)
    (v : ↥(univ : Finset (Fin n)).powerset) :
    Fintype ((containmentGraph univ.powerset).neighborSet v) := by
  classical
  infer_instance

/-- The degree of a vertex `A` in the containment graph of the full powerset of
`Fin n`: its neighbours are the strict subsets of `A` (`2 ^ #A - 1` many) and the
strict supersets of `A` inside `univ` (`2 ^ (n - #A) - 1` many). -/
private lemma degree_full (n : ℕ) (A : Finset (Fin n))
    (hA : A ∈ (univ : Finset (Fin n)).powerset) :
    (containmentGraph univ.powerset).degree ⟨A, hA⟩ = (2 ^ #A - 1) + (2 ^ (n - #A) - 1) := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hdisj : Disjoint (Iio A) (Ioc A (univ : Finset (Fin n))) := by
    rw [Finset.disjoint_left]
    intro B hB1 hB2
    exact absurd (mem_Ioc.mp hB2).1 (not_lt_of_gt (mem_Iio.mp hB1))
  have hcard : #((containmentGraph univ.powerset).neighborFinset ⟨A, hA⟩) =
      #(Iio A ∪ Ioc A (univ : Finset (Fin n))) := by
    apply Finset.card_bij (fun w _ ↦ w.1)
    · intro ⟨B, hB⟩ hw
      dsimp only
      rw [SimpleGraph.mem_neighborFinset] at hw
      obtain ⟨hne, hsub⟩ := hw
      rw [mem_union, mem_Iio, mem_Ioc]
      rcases hsub with h | h
      · exact Or.inr ⟨Finset.ssubset_iff_subset_ne.mpr
          ⟨h, fun e ↦ hne (Subtype.ext_iff.mpr e)⟩, subset_univ B⟩
      · exact Or.inl (Finset.ssubset_iff_subset_ne.mpr
          ⟨h, fun e ↦ hne (Subtype.ext_iff.mpr e.symm)⟩)
    · intro a₁ _ a₂ _ e
      exact Subtype.ext e
    · intro B hB
      rw [mem_union, mem_Iio, mem_Ioc] at hB
      refine ⟨⟨B, mem_powerset.mpr (subset_univ B)⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      rcases hB with h | h
      · obtain ⟨hle, hne⟩ := Finset.ssubset_iff_subset_ne.mp h
        exact ⟨fun e ↦ hne (Subtype.ext_iff.mp e).symm, Or.inr hle⟩
      · obtain ⟨hle, hne⟩ := Finset.ssubset_iff_subset_ne.mp h.1
        exact ⟨fun e ↦ hne (Subtype.ext_iff.mp e), Or.inl hle⟩
  rw [hcard, card_union_of_disjoint hdisj, card_Iio_finset,
    card_Ioc_finset (subset_univ A), card_univ, Fintype.card_fin]

/-- The containment graph of the full powerset of `Fin n` has exactly
`3^n − 2^n` edges (natural subtraction). -/
theorem edgeCount_univ_powerset (n : ℕ) :
    edgeCount (Finset.univ : Finset (Fin n)).powerset = 3 ^ n - 2 ^ n := by
  classical
  have hPcard : #((univ : Finset (Fin n)).powerset) = 2 ^ n := by
    rw [card_powerset, card_univ, Fintype.card_fin]
  have hsum1 : ∑ A ∈ (univ : Finset (Fin n)).powerset, 2 ^ #A = 3 ^ n := by
    rw [sum_powerset_apply_card, card_univ, Fintype.card_fin]
    rw [show (3 : ℕ) ^ n = (2 + 1) ^ n from rfl, add_pow]
    apply sum_congr rfl
    intro m _
    rw [nsmul_eq_mul, one_pow, mul_one, mul_comm]
  have hsum2 : ∑ A ∈ (univ : Finset (Fin n)).powerset, 2 ^ (n - #A) = 3 ^ n := by
    rw [sum_powerset_apply_card (fun k ↦ 2 ^ (n - k)), card_univ, Fintype.card_fin]
    rw [show (3 : ℕ) ^ n = (1 + 2) ^ n from rfl, add_pow]
    apply sum_congr rfl
    intro m _
    rw [nsmul_eq_mul, one_pow, one_mul, mul_comm]
  have hdeg : ∑ v : ↥(univ : Finset (Fin n)).powerset,
      (containmentGraph univ.powerset).degree v = 2 * (3 ^ n - 2 ^ n) := by
    have e1 : ∑ v : ↥(univ : Finset (Fin n)).powerset,
        (containmentGraph univ.powerset).degree v =
        ∑ A ∈ (univ : Finset (Fin n)).powerset, ((2 ^ #A - 1) + (2 ^ (n - #A) - 1)) := by
      refine (Finset.sum_coe_sort univ.powerset
        (fun A ↦ (containmentGraph univ.powerset).degree
          ⟨A, mem_powerset.mpr (subset_univ A)⟩)).trans ?_
      apply sum_congr rfl
      intro A hA
      exact degree_full n A _
    rw [e1, sum_add_distrib,
      sum_tsub_distrib _ (fun A _ ↦ pow_pos (by norm_num : (0 : ℕ) < 2) _),
      sum_tsub_distrib _ (fun A _ ↦ pow_pos (by norm_num : (0 : ℕ) < 2) _),
      hsum1, hsum2, ← card_eq_sum_ones, hPcard, ← two_mul]
  have hs := (containmentGraph (univ : Finset (Fin n)).powerset).sum_degrees_eq_twice_card_edges
  have hfin : (containmentGraph (univ : Finset (Fin n)).powerset).edgeFinset.card
      = 3 ^ n - 2 ^ n := by
    omega
  unfold edgeCount
  exact hfin

/-- The powerset is the unique family of size `2^n`, so `c n (2^n)` is its edge count. -/
theorem c_two_pow (n : ℕ) : c n (2 ^ n) = 3 ^ n - 2 ^ n := by
  have hcard : #((univ : Finset (Fin n)).powerset) = 2 ^ n := by
    rw [card_powerset, card_univ, Fintype.card_fin]
  have hpow : (univ : Finset (Fin n)).powerset.powersetCard (2 ^ n) = {univ.powerset} := by
    rw [← hcard]
    exact powersetCard_self _
  unfold c
  rw [hpow, sup_singleton]
  exact edgeCount_univ_powerset n
