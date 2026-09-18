import JSPProblem.Basic
import JSPProblem.Chain
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card

/-!
# JSP-000637 — Monotonicity of `c` in `m` and the tower-of-two-cubes bound

* `edgeCount_mono` — enlarging a family can only add comparable pairs.
* `c_mono`         — `c n m₁ ≤ c n m₂` for `m₁ ≤ m₂ ≤ 2 ^ n`: any `m₁`-element
  family extends to an `m₂`-element family inside the same powerset, and the
  extension has at least as many edges.
* `twoCube_le_c`   — the Alon–Frankl "tower of two cubes" construction: for a
  `k`-element set `X ⊆ Fin (2k)`, the family of all subsets of `X` together with
  all supersets of `X` has `2 ^ (k+1) - 1` members and at least `4 ^ k - 1`
  comparable pairs.
-/

open Finset

variable {α : Type*} [DecidableEq α]

/-- Enlarging a family can only add comparable pairs: the containment graph of
`F` embeds (along the inclusion `↥F ↪ ↥G`) into the containment graph of any
`G ⊇ F`. -/
theorem edgeCount_mono {F G : Finset (Finset α)} (h : F ⊆ G) :
    edgeCount F ≤ edgeCount G := by
  classical
  unfold edgeCount
  let f : ↥F ↪ ↥G :=
    ⟨fun x ↦ ⟨x.1, h x.2⟩, fun a b e ↦ by
      have e' : (⟨a.1, h a.2⟩ : ↥G) = ⟨b.1, h b.2⟩ := e
      exact Subtype.ext (congrArg (fun x : ↥G ↦ x.1) e')⟩
  have hsub : (containmentGraph F).edgeFinset.map f.sym2Map ⊆
      (containmentGraph G).edgeFinset := by
    intro e he
    rw [Finset.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset] at he' ⊢
    induction e' using Sym2.inductionOn with
    | hf a b =>
      rw [SimpleGraph.mem_edgeSet] at he'
      obtain ⟨hne, hle⟩ := he'
      simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk,
        SimpleGraph.mem_edgeSet]
      exact ⟨fun e ↦ hne (f.injective e), hle⟩
  calc (containmentGraph F).edgeFinset.card
      = ((containmentGraph F).edgeFinset.map f.sym2Map).card :=
        (Finset.card_map _).symm
    _ ≤ (containmentGraph G).edgeFinset.card := Finset.card_le_card hsub

/-- `c n m` is monotone in `m` for `m ≤ 2 ^ n`: any `m₁`-element family `F` of
subsets of `Fin n` extends to an `m₂`-element family `F ∪ T` inside the same
powerset, and `edgeCount F ≤ edgeCount (F ∪ T) ≤ c n m₂`. -/
theorem c_mono {n m₁ m₂ : ℕ} (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ 2 ^ n) :
    c n m₁ ≤ c n m₂ := by
  classical
  unfold c
  apply Finset.sup_le
  intro F hF
  rw [Finset.mem_powersetCard] at hF
  obtain ⟨hFsub, hFcard⟩ := hF
  have hP : #(univ : Finset (Fin n)).powerset = 2 ^ n := by
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  have hsdiff : #((univ : Finset (Fin n)).powerset \ F) = 2 ^ n - m₁ := by
    rw [Finset.card_sdiff_of_subset hFsub, hP, hFcard]
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (s := (univ : Finset (Fin n)).powerset \ F) (n := m₂ - m₁) (by omega)
  refine le_trans (edgeCount_mono (F := F) (G := F ∪ T)
    Finset.subset_union_left) ?_
  apply Finset.le_sup
  rw [Finset.mem_powersetCard]
  refine ⟨Finset.union_subset hFsub (hTsub.trans Finset.sdiff_subset), ?_⟩
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_right hTsub Finset.disjoint_sdiff),
    hFcard, hTcard]
  omega

section TwoCube

/-- The initial segment `{0, …, k-1} ⊆ Fin n` has `k` elements when `k ≤ n`. -/
theorem initSeg_card {n k : ℕ} (h : k ≤ n) : (initSeg n k).card = k := by
  classical
  have himg : (initSeg n k).image Fin.val = Finset.range k := by
    ext j
    simp only [initSeg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hj
      exact ⟨⟨j, lt_of_lt_of_le hj h⟩, hj, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg,
    Finset.card_range]

/-- The Alon–Frankl "tower of two cubes" lower bound.  For `X = {0,…,k-1} ⊆
Fin (2k)`, the family `F` of all subsets of `X` together with all supersets of
`X` has `2 ^ (k+1) - 1` members, and every pair `(A, B)` with `A ⊆ X ⊆ B`,
`(A, B) ≠ (X, X)`, is an edge of the containment graph: `4 ^ k - 1` edges. -/
theorem twoCube_le_c (k : ℕ) : 4 ^ k - 1 ≤ c (2 * k) (2 ^ (k + 1) - 1) := by
  classical
  set X := initSeg (2 * k) k with hXdef
  set cube1 := X.powerset with hc1def
  set cube2 := (Xᶜ).powerset.image (· ∪ X) with hc2def
  set F := cube1 ∪ cube2 with hFdef
  set P := (cube1 ×ˢ cube2).erase (X, X) with hPdef
  have hXcard : #X = k := initSeg_card (by omega)
  have hsubX : ∀ {A : Finset (Fin (2 * k))}, A ∈ cube1 → A ⊆ X :=
    fun hA ↦ Finset.mem_powerset.mp hA
  have hXsub : ∀ {B : Finset (Fin (2 * k))}, B ∈ cube2 → X ⊆ B := by
    intro B hB
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hB
    exact Finset.subset_union_right
  have hXc1 : X ∈ cube1 := Finset.mem_powerset_self X
  have hXc2 : X ∈ cube2 :=
    Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _),
      Finset.empty_union _⟩
  have hc1card : #cube1 = 2 ^ k := by
    rw [hc1def, Finset.card_powerset, hXcard]
  have hc2card : #cube2 = 2 ^ k := by
    have hinj2 : Set.InjOn (· ∪ X) ↑(Xᶜ).powerset := by
      intro B₁ hB₁ B₂ hB₂ e
      rw [Finset.mem_coe, Finset.mem_powerset] at hB₁ hB₂
      have hI : ∀ B ⊆ Xᶜ, (B ∪ X) ∩ Xᶜ = B := by
        intro B hB
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hB,
          Finset.inter_compl, Finset.union_empty]
      have e' : B₁ ∪ X = B₂ ∪ X := e
      rw [← hI B₁ hB₁, ← hI B₂ hB₂, e']
    have hcc : #(Xᶜ) = k := by
      rw [Finset.card_compl, Fintype.card_fin, hXcard]
      omega
    rw [hc2def, Finset.card_image_of_injOn hinj2, Finset.card_powerset, hcc]
  have hinter : cube1 ∩ cube2 = {X} := by
    ext A
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hA1, hA2⟩
      exact subset_antisymm (hsubX hA1) (hXsub hA2)
    · intro rfl
      exact ⟨hXc1, hXc2⟩
  have hFcard : #F = 2 ^ (k + 1) - 1 := by
    rw [hFdef, Finset.card_union, hc1card, hc2card, hinter,
      Finset.card_singleton, pow_succ]
    omega
  have hFmem : F ∈ (univ : Finset (Fin (2 * k))).powerset.powersetCard
      (2 ^ (k + 1) - 1) := by
    rw [Finset.mem_powersetCard]
    exact ⟨fun A _ ↦ Finset.mem_powerset.mpr (Finset.subset_univ A), hFcard⟩
  have hPcard : #P = 4 ^ k - 1 := by
    rw [hPdef, Finset.card_erase_of_mem (Finset.mk_mem_product hXc1 hXc2),
      Finset.card_product, hc1card, hc2card,
      show (4 : ℕ) ^ k = 2 ^ k * 2 ^ k by
        rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]]
  -- Every `p ∈ P` has `p.1 ≠ p.2`: equal components would lie in
  -- `cube1 ∩ cube2 = {X}`, forcing `p = (X, X) ∉ P`.
  have hne : ∀ {p : Finset (Fin (2 * k)) × Finset (Fin (2 * k))},
      p ∈ P → p.1 ≠ p.2 := by
    intro p hp hpEq
    have h1 : p.1 ∈ cube1 :=
      (Finset.mem_product.mp (Finset.mem_erase.mp hp).2).1
    have h2 : p.2 ∈ cube2 :=
      (Finset.mem_product.mp (Finset.mem_erase.mp hp).2).2
    have hX1 : p.1 = X := by
      have : p.1 ∈ cube1 ∩ cube2 := Finset.mem_inter.mpr ⟨h1, hpEq ▸ h2⟩
      rwa [hinter, Finset.mem_singleton] at this
    have hX2 : p.2 = X := hpEq ▸ hX1
    exact (Finset.mem_erase.mp hp).1 (Prod.ext hX1 hX2)
  have hF1 : ∀ {p : Finset (Fin (2 * k)) × Finset (Fin (2 * k))},
      p ∈ P → p.1 ∈ F := fun hp ↦ Finset.mem_union_left cube2
        (Finset.mem_product.mp (Finset.mem_erase.mp hp).2).1
  have hF2 : ∀ {p : Finset (Fin (2 * k)) × Finset (Fin (2 * k))},
      p ∈ P → p.2 ∈ F := fun hp ↦ Finset.mem_union_right cube1
        (Finset.mem_product.mp (Finset.mem_erase.mp hp).2).2
  have hedge : 4 ^ k - 1 ≤ edgeCount F := by
    unfold edgeCount
    rw [← hPcard, ← Finset.card_attach (s := P)]
    apply Finset.card_le_card_of_injOn
      (f := fun p : ↥P ↦ s((⟨p.1.1, hF1 p.2⟩ : ↥F), ⟨p.1.2, hF2 p.2⟩))
    · intro p _
      apply Finset.mem_coe.mpr
      rw [SimpleGraph.mem_edgeFinset]
      show s((⟨p.1.1, hF1 p.2⟩ : ↥F), ⟨p.1.2, hF2 p.2⟩) ∈
        (containmentGraph F).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨fun e ↦ hne p.2 (Subtype.ext_iff.mp e),
        Or.inl ((hsubX
          (Finset.mem_product.mp (Finset.mem_erase.mp p.2).2).1).trans
          (hXsub (Finset.mem_product.mp (Finset.mem_erase.mp p.2).2).2))⟩
    · intro p _ q _ hpq
      have hpq' : s((⟨p.1.1, hF1 p.2⟩ : ↥F), ⟨p.1.2, hF2 p.2⟩) =
          s((⟨q.1.1, hF1 q.2⟩ : ↥F), ⟨q.1.2, hF2 q.2⟩) := hpq
      rw [Sym2.eq_iff] at hpq'
      rcases hpq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply Subtype.ext
        apply Prod.ext
        · exact congrArg Subtype.val h1
        · exact congrArg Subtype.val h2
      · exfalso
        have e1 : p.1.1 = q.1.2 := congrArg Subtype.val h1
        have e2 : p.1.2 = q.1.1 := congrArg Subtype.val h2
        have hp1 : p.1.1 ⊆ X :=
          hsubX (Finset.mem_product.mp (Finset.mem_erase.mp p.2).2).1
        have hp2 : X ⊆ p.1.2 :=
          hXsub (Finset.mem_product.mp (Finset.mem_erase.mp p.2).2).2
        have hq1 : q.1.1 ⊆ X :=
          hsubX (Finset.mem_product.mp (Finset.mem_erase.mp q.2).2).1
        have hq2 : X ⊆ q.1.2 :=
          hXsub (Finset.mem_product.mp (Finset.mem_erase.mp q.2).2).2
        have hAX : p.1.1 = X :=
          subset_antisymm hp1 (hq2.trans (le_of_eq e1.symm))
        have hBX : p.1.2 = X :=
          subset_antisymm ((le_of_eq e2).trans hq1) hp2
        exact hne p.2 (hAX.trans hBX.symm)
  exact le_trans hedge (Finset.le_sup hFmem)

end TwoCube
