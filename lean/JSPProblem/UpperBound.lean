import JSPProblem.Basic

open Finset

variable {α : Type*} [DecidableEq α]

/-- The containment graph of a family of `m` sets has at most `m.choose 2` edges. -/
theorem edgeCount_le (F : Finset (Finset α)) :
    edgeCount F ≤ F.card.choose 2 := by
  classical
  unfold edgeCount
  rw [← Fintype.card_coe F]
  exact SimpleGraph.card_edgeFinset_le_card_choose_two (G := containmentGraph F)

/-- `c n m` is at most `m choose 2` for all `n m`. -/
theorem c_le (n m : ℕ) : c n m ≤ m.choose 2 := by
  classical
  unfold c
  apply Finset.sup_le
  intro F hF
  rw [Finset.mem_powersetCard] at hF
  rw [← hF.2]
  exact edgeCount_le F
