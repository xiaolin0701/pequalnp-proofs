import Mathlib
import PEqualNP.Gct.Helpers.BorderedPerm

namespace LevelSpaceFive.TwoSparseRows

open Finset

private def block (A : Matrix (Fin 3) (Fin 5) ℂ) (f g h k : ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j =>
  ![A 0, A 1, A 2, ![0,0,0,f,g], ![0,0,0,h,k]] i j

private def corner (A : Matrix (Fin 3) (Fin 5) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => A i (Fin.castLE (by decide) j)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 3000000 in
private theorem block_factor (A : Matrix (Fin 3) (Fin 5) ℂ) (f g h k : ℂ) :
    (block A f g h k).permanent = (f*k+g*h) * (corner A).permanent := by
  simp only [PEqualNP.Gct.Helpers.BorderedPerm.permanent_succ_last_row,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.submatrix_apply, Matrix.permanent_isEmpty]
  simp (config := {decide := true}) [block, corner, Matrix.of_apply, Fin.succAbove,
    Fin.castSucc, Fin.last]
  ring

private lemma two_denominators (a b c d : ℂ) (ha : a ≠ 0 ∨ b ≠ 0)
    (hc : c ≠ 0 ∨ d ≠ 0) : ∃ t : ℂ, a*t+b ≠ 0 ∧ c*t-d ≠ 0 := by
  classical
  obtain ⟨t, h⟩ := Infinite.exists_notMem_finset ({-b/a,d/c} : Finset ℂ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  refine ⟨t, ?_, ?_⟩
  · by_cases h₁ : a = 0
    · simpa [h₁] using ha.resolve_left (not_not.mpr h₁)
    · intro e
      apply h.1
      apply (eq_div_iff h₁).mpr
      linear_combination e
  · by_cases h₁ : c = 0
    · simpa [h₁] using hc.resolve_left (not_not.mpr h₁)
    · intro e
      apply h.2
      apply (eq_div_iff h₁).mpr
      linear_combination e

/-- Two independent affine rows of rank four can realize a zero two-column
permanent. The three other rows may depend arbitrarily on those two rows. -/
theorem no_independent_pair (a b c d value : ℂ) (ha : a ≠ 0 ∨ b ≠ 0)
    (hc : c ≠ 0 ∨ d ≠ 0) (hv : value ≠ 0)
    (realize : ∀ f g h k : ℂ, a*f+b*g=1 → c*h+d*k=1 →
      ∃ A : Matrix (Fin 3) (Fin 5) ℂ,
        (Matrix.of fun i j : Fin 5 =>
          ![A 0,A 1,A 2,![0,0,0,f,g],![0,0,0,h,k]] i j).permanent = value) : False := by
  obtain ⟨t, hA, hC⟩ := two_denominators a b c d ha hc
  obtain ⟨A, h⟩ := realize (t/(a*t+b)) (1/(a*t+b)) (t/(c*t-d)) (-1/(c*t-d))
    (by field_simp) (by field_simp; ring)
  change (block A _ _ _ _).permanent = value at h
  rw [block_factor] at h
  apply hv
  rw [← h]
  have zero : t/(a*t+b) * (-1/(c*t-d)) + 1/(a*t+b) * (t/(c*t-d)) = 0 := by ring
  rw [zero, zero_mul]

end LevelSpaceFive.TwoSparseRows
