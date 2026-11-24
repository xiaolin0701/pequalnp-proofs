import Mathlib

namespace LevelSpaceFive.HallRectangle

open Finset

/-- Every permutation meets a rectangle whose row and column counts exceed
the order of the square matrix when added. -/
theorem embedding_hits_rectangle {n : ℕ} (rows cols : Finset (Fin n))
    (large : n < rows.card + cols.card) (e : Fin n ↪ Fin n) :
    ∃ i ∈ rows, e i ∈ cols := by
  classical
  by_contra! avoid
  have hsub : rows.image e ⊆ colsᶜ := by
    rintro _ hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_compl.mpr (avoid i hi)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e.injective, Finset.card_compl,
    Fintype.card_fin] at hcount
  have hc := Finset.card_le_univ cols
  rw [Fintype.card_fin] at hc
  omega

/-- Nonzero constant permanent rules out setting a whole Hall rectangle
to minus one in its direction space. -/
theorem no_negative_one_rectangle {n : ℕ}
    (L : Submodule ℂ (Fin n × Fin n → ℂ)) (c : ℂ) (hc : c ≠ 0)
    (level : ∀ X ∈ L, (∑ e : Fin n ↪ Fin n, ∏ i, (1 + X (i,e i))) = c)
    (rows cols : Finset (Fin n)) (large : n < rows.card + cols.card)
    (X : Fin n × Fin n → ℂ) (hX : X ∈ L) :
    ¬ (∀ i ∈ rows, ∀ j ∈ cols, X (i,j) = -1) := by
  classical
  intro zeroRectangle
  apply hc
  rw [← level X hX]
  apply Finset.sum_eq_zero
  intro e _
  obtain ⟨i, hi, he⟩ := embedding_hits_rectangle rows cols large e
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [zeroRectangle i hi (e i) he]
  ring

end LevelSpaceFive.HallRectangle
