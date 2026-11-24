import Mathlib
import PEqualNP.Gct.Helpers.BorderedPerm

namespace LevelSpaceFive.ThreeByFiveWitness

open Finset Module

abbrev Entry := Fin 3 × Fin 5 → ℂ

/-- Sum of the 60 products over ordered triples of distinct columns. -/
def rect (X : Entry) : ℂ :=
  ∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
    if i = j ∨ i = k ∨ j = k then 0 else
      (1 + X (0,i)) * (1 + X (1,j)) * (1 + X (2,k))

def entry (t : Fin 5 → ℂ) (ij : Fin 3 × Fin 5) : ℂ :=
  ![![t 0, 0, 0, 0, 0], ![-t 0, 0, 0, 0, 0],
    ![t 1, t 2, t 3, t 4, -(t 1 + t 2 + t 3 + t 4)]] ij.1 ij.2

def parametrization : (Fin 5 → ℂ) →ₗ[ℂ] Entry where
  toFun := entry
  map_add' x y := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [entry] <;> ring
  map_smul' a x := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [entry]
    ring

private theorem independent : Function.Injective parametrization := by
  intro x y h
  have h₀ := congrFun h (0, 0)
  have h₁ := congrFun h (2, 0)
  have h₂ := congrFun h (2, 1)
  have h₃ := congrFun h (2, 2)
  have h₄ := congrFun h (2, 3)
  funext i
  fin_cases i <;> assumption

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
private theorem constant_value (t : Fin 5 → ℂ) : rect (entry t) = 60 := by
  simp (config := {decide := true}) [rect, entry, Fin.sum_univ_succ]
  ring

theorem exists_five_plane :
    ∃ K : Submodule ℂ Entry, (∀ X ∈ K, rect X = 60) ∧ finrank ℂ K = 5 := by
  refine ⟨LinearMap.range parametrization, ?_, ?_⟩
  · rintro _ ⟨t,rfl⟩
    exact constant_value t
  · rw [LinearMap.finrank_range_of_inj independent]
    simp

abbrev Five := Fin 5 × Fin 5 → ℂ

def firstThree : Five →ₗ[ℂ] Entry :=
  LinearMap.funLeft ℂ ℂ (fun ij => (![(0 : Fin 5), 1, 2] ij.1, ij.2))

def lastTwo : Five →ₗ[ℂ] (Fin 2 × Fin 5 → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun ij => (![(3 : Fin 5), 4] ij.1, ij.2))

private def pad (X : Entry) : Five := fun ij =>
  ![X (0,ij.2), X (1,ij.2), X (2,ij.2), 0, 0] ij.1

private def full (X : Five) : ℂ :=
  (Matrix.of fun i j : Fin 5 => 1 + X (i,j)).permanent

set_option maxRecDepth 24000 in
set_option maxHeartbeats 4000000 in
private theorem padded_value (X : Entry) : full (pad X) = 2 * rect X := by
  simp only [full, PEqualNP.Gct.Helpers.BorderedPerm.permanent_succ_last_row,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.submatrix_apply, Matrix.permanent_isEmpty]
  simp (config := {decide := true}) [rect, pad, Fin.sum_univ_succ,
    Matrix.of_apply, Fin.succAbove, Fin.castSucc, Fin.last]
  ring

private theorem reconstruct (X : Five) (h : lastTwo X = 0) : pad (firstThree X) = X := by
  funext ⟨i,j⟩
  have h₃ := congrFun h (0,j)
  have h₄ := congrFun h (1,j)
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact h₃.symm
  · exact h₄.symm

/-- The rectangular upper bound feeds into the five-row problem by taking
the kernel of the joint projection onto two specified rows. -/
theorem bound_by_two_rows {m : ℕ}
    (bound3 : ∀ K : Submodule ℂ Entry, (∀ X ∈ K, rect X = 60) → finrank ℂ K ≤ m)
    (L : Submodule ℂ Five)
    (hL : ∀ X ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + X (i,e i))) = 120) :
    finrank ℂ L ≤ m + finrank ℂ (L.map lastTwo) := by
  classical
  let R := lastTwo.domRestrict L
  let K := LinearMap.ker R
  let D : K →ₗ[ℂ] Entry := firstThree.comp (L.subtype.comp K.subtype)
  have valid (v : K) : rect (D v) = 60 := by
    let X := v.1.1
    have identification : pad (D v) = X := reconstruct X v.2
    have hp : full X = 120 := by
      let M := Matrix.of fun i j : Fin 5 => 1 + X (i,j)
      have he : (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + X (i,e i))) = M.transpose.permanent :=
        (Equiv.embeddingEquivOfFinite (Fin 5)).sum_comp (fun e => ∏ i, (1 + X (i,e i)))
      rw [Matrix.permanent_transpose] at he
      exact he.symm.trans (hL X v.1.2)
    have hn := padded_value (D v)
    rw [identification, hp] at hn
    linear_combination -hn / 2
  have injective : Function.Injective D := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact (reconstruct u.1.1 u.2).symm.trans ((congrArg pad h).trans (reconstruct v.1.1 v.2))
  have dimK : finrank ℂ K ≤ m := by
    rw [← LinearMap.finrank_range_of_inj injective]
    apply bound3
    rintro _ ⟨v,rfl⟩
    exact valid v
  have dims := R.finrank_range_add_finrank_ker
  have hr : LinearMap.range R = L.map lastTwo := LinearMap.range_domRestrict _ _
  change finrank ℂ (LinearMap.range R) + finrank ℂ K = finrank ℂ L at dims
  rw [hr] at dims
  omega

end LevelSpaceFive.ThreeByFiveWitness
