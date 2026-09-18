import JSPProblem.Basic
import Mathlib.Data.Sym.NatCard

open Finset

/-- The initial segment {0,…,k-1} inside `Fin n`. -/
def initSeg (n k : ℕ) : Finset (Fin n) := Finset.univ.filter fun i ↦ i.val < k

/-- The family of `m` nested initial segments of `Fin n`. -/
def chainFam (n m : ℕ) : Finset (Finset (Fin n)) := (Finset.range m).image (initSeg n)

theorem initSeg_mono {n k l : ℕ} (h : k ≤ l) : initSeg n k ⊆ initSeg n l := by
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ x, lt_of_lt_of_le (Finset.mem_filter.mp hx).2 h⟩

theorem initSeg_ne {n k l : ℕ} (hkl : k < l) (hl : l ≤ n) :
    initSeg n k ≠ initSeg n l := by
  have hkn : k < n := lt_of_lt_of_le hkl hl
  intro heq
  have h1 : (⟨k, hkn⟩ : Fin n) ∈ initSeg n l :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl⟩
  rw [← heq] at h1
  exact lt_irrefl _ (Finset.mem_filter.mp h1).2

theorem chainFam_comparable {n m : ℕ} :
    ∀ A ∈ chainFam n m, ∀ B ∈ chainFam n m, A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hB
  rcases le_total a b with hab | hba
  · exact Or.inl (initSeg_mono hab)
  · exact Or.inr (initSeg_mono hba)

theorem chainFam_card {n m : ℕ} (h : m ≤ n + 1) : (chainFam n m).card = m := by
  have hinj : Set.InjOn (initSeg n) ↑(Finset.range m) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd hab (initSeg_ne hlt (by omega))
    · exact heq
    · exact absurd hab.symm (initSeg_ne hgt (by omega))
  exact (Finset.card_image_of_injOn hinj).trans (Finset.card_range m)

theorem chainFam_mem {n m : ℕ} (h : m ≤ n + 1) :
    chainFam n m ∈ (Finset.univ : Finset (Fin n)).powerset.powersetCard m := by
  rw [Finset.mem_powersetCard]
  exact ⟨fun A _ ↦ Finset.mem_powerset.mpr (Finset.subset_univ A), chainFam_card h⟩

theorem containmentGraph_chainFam {n m : ℕ} (h : m ≤ n + 1) :
    containmentGraph (chainFam n m) = ⊤ := by
  ext A B
  simp only [SimpleGraph.top_adj]
  constructor
  · intro hAB
    exact hAB.1
  · intro hne
    exact ⟨hne, chainFam_comparable A.1 A.2 B.1 B.2⟩

theorem chainFam_edgeCount {n m : ℕ} (h : m ≤ n + 1) :
    edgeCount (chainFam n m) = m.choose 2 := by
  classical
  have key : edgeCount (chainFam n m) =
      Nat.card ↥((containmentGraph (chainFam n m)).edgeSet) := by
    unfold edgeCount
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  rw [key, containmentGraph_chainFam h, SimpleGraph.edgeSet_top, Nat.card_coe_set_eq,
    Sym2.ncard_diagSet_compl, Nat.card_eq_fintype_card, Fintype.card_coe, chainFam_card h]

theorem chainFam_le_c {n m : ℕ} (h : m ≤ n + 1) : m.choose 2 ≤ c n m := by
  rw [← chainFam_edgeCount h]
  exact Finset.le_sup (chainFam_mem h)
