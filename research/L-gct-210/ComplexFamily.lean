import Mathlib
import PEqualNP.Gct.Helpers.BorderedPerm

namespace LevelSpaceFive.ComplexFamily

open Finset Module

-- Extend the four-row family in L-gct-180 by a direction supported in column 4.
def entry (w : ℂ) (p : Fin 7 → ℂ) : Fin 5 × Fin 5 → ℂ := fun ij =>
  ![![p 0, -p 0, p 1, -p 1, p 6],
    ![w*p 0, -w*p 0, (-1-w)*p 1, (1+w)*p 1, p 6],
    ![(-1-w)*p 0, (1+w)*p 0, w*p 1, -w*p 1, p 6],
    ![p 2, p 3, p 4, p 5, -(p 2+p 3+p 4+p 5)],
    ![0, 0, 0, 0, -3*p 6]] ij.1 ij.2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
private lemma level_identity (w : ℂ) (hw : w^2 + w + 1 = 0) (p : Fin 7 → ℂ) :
    (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + entry w p (i,e i))) = 120 := by
  let M : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j => 1 + entry w p (i,j)
  have switch : (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + entry w p (i,e i))) = M.transpose.permanent :=
    (Equiv.embeddingEquivOfFinite (Fin 5)).sum_comp (fun e => ∏ i, (1 + entry w p (i,e i)))
  rw [switch, Matrix.permanent_transpose]
  have hw2 : w^2 = -1-w := by linear_combination hw
  simp only [PEqualNP.Gct.Helpers.BorderedPerm.permanent_succ_last_row,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.submatrix_apply, Matrix.permanent_isEmpty]
  simp (config := {decide := true}) [M, Matrix.of_apply, entry, Fin.succAbove, Fin.castSucc, Fin.last]
  ring_nf
  rw [hw2]
  ring

def parameterMap (w : ℂ) : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ) where
  toFun := entry w
  map_add' p q := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [entry] <;> ring
  map_smul' c p := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [entry] <;> ring

private lemma independent_parameters (w : ℂ) : Function.Injective (parameterMap w) := by
  intro p q h
  have h0 := congrFun h (0,0)
  have h1 := congrFun h (0,2)
  have h2 := congrFun h (3,0)
  have h3 := congrFun h (3,1)
  have h4 := congrFun h (3,2)
  have h5 := congrFun h (3,3)
  have h6 := congrFun h (0,4)
  funext i
  fin_cases i <;> assumption

theorem seven_dimensional_level_space :
    ∃ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i,e i))) = 120) ∧
      finrank ℂ L = 7 := by
  let w : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩
  have hw : w^2 + w + 1 = 0 := by
    apply Complex.ext
    · simp only [w, sq, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re]
      have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      linarith
    · simp only [w, sq, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im]
      ring
  refine ⟨LinearMap.range (parameterMap w), ?_, ?_⟩
  · rintro _ ⟨p,rfl⟩
    exact level_identity w hw p
  · rw [LinearMap.finrank_range_of_inj (independent_parameters w)]
    simp

end LevelSpaceFive.ComplexFamily
