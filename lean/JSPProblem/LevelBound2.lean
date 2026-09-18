import JSPProblem.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic

/-!
# Level bound for the containment graph (Sym2 route)

For a family `F` of `m` subsets of `Fin n`, the containment graph has at most
`n * m * m / (2 * (n + 1))` edges.  The proof counts, for each cardinality level
`k`, the `(f k).choose 2` unordered pairs of distinct members of `F` lying in
that level; such pairs cannot be edges of the containment graph, and they are
disjoint across levels.  Together with `edgeCount F` they fit inside the
`m.choose 2` unordered pairs of vertices, which yields
`2 * edgeCount F + ∑ f k ^ 2 ≤ m ^ 2`, and Cauchy–Schwarz finishes.
-/

open Finset

/-- The `k`-th level of `F`: its members of cardinality `k`. -/
private abbrev lvl {n : ℕ} (F : Finset (Finset (Fin n))) (k : ℕ) :
    Finset (Finset (Fin n)) :=
  F.filter fun A ↦ A.card = k

/-- The inclusion of the `k`-th level of `F` into `F`, as vertices. -/
private abbrev lvlInc {n : ℕ} {F : Finset (Finset (Fin n))} {k : ℕ} :
    ↥(lvl F k) → ↥F :=
  fun a ↦ ⟨a.1, (Finset.mem_filter.mp a.2).1⟩

private lemma lvlInc_injective {n : ℕ} {F : Finset (Finset (Fin n))} {k : ℕ} :
    Function.Injective (@lvlInc n F k) := by
  intro a b h
  have h' : (a : Finset (Fin n)) = (b : Finset (Fin n)) :=
    congr_arg (fun u : ↥F ↦ u.1) h
  exact Subtype.ext h'

/-- All unordered pairs of distinct vertices of `F`. -/
private def topPairs {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Sym2 ↥F) :=
  (⊤ : SimpleGraph ↥F).edgeFinset

/-- Non-edges of the containment graph inside level `k`. -/
private def NL {n : ℕ} (F : Finset (Finset (Fin n))) (k : ℕ) : Finset (Sym2 ↥F) :=
  (topPairs F).filter fun e ↦ ∀ a ∈ e, a.1.card = k

private lemma mem_topPairs {n : ℕ} {F : Finset (Finset (Fin n))} {e : Sym2 ↥F} :
    e ∈ topPairs F ↔ ¬e.IsDiag := by
  unfold topPairs
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
  simp

private lemma mem_NL {n : ℕ} {F : Finset (Finset (Fin n))} {k : ℕ} {e : Sym2 ↥F} :
    e ∈ NL F k ↔ ¬e.IsDiag ∧ ∀ a ∈ e, a.1.card = k := by
  unfold NL
  rw [Finset.mem_filter, mem_topPairs]

private lemma card_topPairs {n : ℕ} (F : Finset (Finset (Fin n))) :
    (topPairs F).card = F.card.choose 2 := by
  unfold topPairs
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe]

/-- The number of within-level unordered pairs of distinct members of level `k`
is `(lvl F k).card.choose 2`. -/
private lemma card_NL_q {n : ℕ} (F : Finset (Finset (Fin n))) (k : ℕ) :
    (NL F k).card = (lvl F k).card.choose 2 := by
  rw [← card_topPairs (lvl F k)]
  symm
  apply Finset.card_bij (fun e _ ↦ Sym2.map (@lvlInc n F k) e)
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_topPairs, Sym2.mk_isDiag_iff] at he
      rw [Sym2.map_mk, mem_NL, Sym2.mk_isDiag_iff, Sym2.ball]
      exact ⟨fun h ↦ he (lvlInc_injective h), (Finset.mem_filter.mp x.2).2,
        (Finset.mem_filter.mp y.2).2⟩
  · intro e₁ _ e₂ _ h
    exact Sym2.map.injective lvlInc_injective h
  · intro b hb
    induction b using Sym2.ind with
    | h x y =>
      rw [mem_NL, Sym2.ball, Sym2.mk_isDiag_iff] at hb
      obtain ⟨hxy, hxk, hyk⟩ := hb
      refine ⟨s(⟨x.1, Finset.mem_filter.mpr ⟨x.2, hxk⟩⟩,
          ⟨y.1, Finset.mem_filter.mpr ⟨y.2, hyk⟩⟩), ?_, ?_⟩
      · rw [mem_topPairs, Sym2.mk_isDiag_iff]
        exact fun h ↦ hxy (Subtype.ext (congr_arg (fun u : ↥(lvl F k) ↦ u.1) h))
      · rw [Sym2.map_mk, Sym2.eq_iff]
        exact Or.inl ⟨Subtype.ext rfl, Subtype.ext rfl⟩

/-- Counting bound: the edges of the containment graph plus the within-level
unordered pairs fit inside all `F.card.choose 2` unordered pairs of vertices. -/
private lemma edgeCount_add_sum_choose_le_q {n : ℕ} (F : Finset (Finset (Fin n))) :
    edgeCount F + ∑ k ∈ Finset.range (n + 1), (lvl F k).card.choose 2 ≤
      F.card.choose 2 := by
  classical
  have hec : edgeCount F = (containmentGraph F).edgeFinset.card := by
    unfold edgeCount
    apply congr_arg Finset.card
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
  have hsub : (containmentGraph F).edgeFinset ∪ (Finset.range (n + 1)).biUnion (NL F)
      ⊆ topPairs F := by
    refine Finset.union_subset ?_ ?_
    · intro e he
      rw [mem_topPairs]
      exact SimpleGraph.not_isDiag_of_mem_edgeFinset he
    · rw [Finset.biUnion_subset]
      exact fun k _ ↦ Finset.filter_subset _ _
  have hdisj : Disjoint (containmentGraph F).edgeFinset
      ((Finset.range (n + 1)).biUnion (NL F)) := by
    rw [Finset.disjoint_biUnion_right]
    intro k _
    rw [Finset.disjoint_left]
    intro e heG heNL
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_NL, Sym2.ball] at heNL
      obtain ⟨-, hxk, hyk⟩ := heNL
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heG
      obtain ⟨hne, hcmp⟩ := heG
      have hxy : x.1 = y.1 := by
        rcases hcmp with h | h
        · exact Finset.eq_of_subset_of_card_le h (by omega)
        · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
      exact hne (Subtype.ext hxy)
  have hpair : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint (NL F) := by
    intro k₁ _ k₂ _ hne
    show Disjoint (NL F k₁) (NL F k₂)
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    have ha : e.out.1 ∈ e := Sym2.out_fst_mem e
    have h₁ := (mem_NL.mp he₁).2 _ ha
    have h₂ := (mem_NL.mp he₂).2 _ ha
    exact hne (h₁.symm.trans h₂)
  have hcardU : ((containmentGraph F).edgeFinset ∪
        (Finset.range (n + 1)).biUnion (NL F)).card =
      edgeCount F + ∑ k ∈ Finset.range (n + 1), (lvl F k).card.choose 2 := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_biUnion hpair, hec]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ card_NL_q F k
  calc edgeCount F + ∑ k ∈ Finset.range (n + 1), (lvl F k).card.choose 2
      = ((containmentGraph F).edgeFinset ∪
          (Finset.range (n + 1)).biUnion (NL F)).card := hcardU.symm
    _ ≤ (topPairs F).card := Finset.card_le_card hsub
    _ = F.card.choose 2 := card_topPairs F

/-- Doubling a binomial coefficient `a.choose 2` and adding `a` gives `a * a`. -/
private lemma two_mul_choose_two_add_self_q (a : ℕ) : 2 * a.choose 2 + a = a * a := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one a)]
  cases a with
  | zero => simp
  | succ b => rw [Nat.add_sub_cancel]; ring

/-- The Erdős–Daykin–Frankl upper bound: the containment graph of a family `F`
of subsets of `Fin n` has at most `n * F.card ^ 2 / (2 * (n + 1))` edges. -/
theorem two_mul_edgeCount_le_q {n : ℕ} (F : Finset (Finset (Fin n))) :
    2 * (n + 1) * edgeCount F ≤ n * F.card * F.card := by
  classical
  have hsum : ∑ k ∈ Finset.range (n + 1), (lvl F k).card = F.card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise (f := fun A : Finset (Fin n) ↦ A.card)
    intro A _
    rw [Finset.mem_coe, Finset.mem_range]
    show A.card < n + 1
    have hle := Finset.card_le_univ A
    rw [Fintype.card_fin] at hle
    omega
  have hterm : ∀ a : ℕ, 2 * a.choose 2 + a = a * a := fun a ↦
    two_mul_choose_two_add_self_q a
  have h2 : 2 * (∑ k ∈ Finset.range (n + 1), ((lvl F k).card).choose 2) + F.card
      = ∑ k ∈ Finset.range (n + 1), (lvl F k).card * (lvl F k).card := by
    rw [Finset.mul_sum, ← hsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ hterm (lvl F k).card
  have h3 : 2 * F.card.choose 2 + F.card = F.card * F.card := hterm _
  have hcount := edgeCount_add_sum_choose_le_q F
  have key : 2 * edgeCount F +
      ∑ k ∈ Finset.range (n + 1), (lvl F k).card * (lvl F k).card
      ≤ F.card * F.card := by
    omega
  have hcs : F.card * F.card
      ≤ (n + 1) * ∑ k ∈ Finset.range (n + 1), (lvl F k).card * (lvl F k).card := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (n + 1))
      (f := fun k ↦ (lvl F k).card)
    simpa [pow_two, Finset.card_range, hsum] using h
  have hgoal : 2 * (n + 1) * edgeCount F + F.card * F.card
      ≤ (n + 1) * (F.card * F.card) := by
    have h1 : (n + 1) * (2 * edgeCount F +
        ∑ k ∈ Finset.range (n + 1), (lvl F k).card * (lvl F k).card)
        ≤ (n + 1) * (F.card * F.card) := Nat.mul_le_mul le_rfl key
    have h2' : 2 * (n + 1) * edgeCount F + (n + 1) *
        ∑ k ∈ Finset.range (n + 1), (lvl F k).card * (lvl F k).card =
        (n + 1) * (2 * edgeCount F +
        ∑ k ∈ Finset.range (n + 1), (lvl F k).card * (lvl F k).card) := by ring
    omega
  have hsplit : (n + 1) * (F.card * F.card) =
      n * F.card * F.card + F.card * F.card := by ring
  omega

/-- The extremal function `c n m` satisfies the same bound. -/
theorem two_mul_c_le_q (n m : ℕ) : 2 * (n + 1) * c n m ≤ n * m * m := by
  classical
  unfold c
  rcases ((Finset.univ : Finset (Fin n)).powerset.powersetCard m).eq_empty_or_nonempty
    with h | h
  · rw [h, Finset.sup_empty]
    exact Nat.zero_le _
  · obtain ⟨F₀, hF₀, hsup⟩ := Finset.exists_mem_eq_sup _ h edgeCount
    rw [hsup]
    rw [Finset.mem_powersetCard] at hF₀
    have hF := two_mul_edgeCount_le_q F₀
    rw [hF₀.2] at hF
    exact hF
