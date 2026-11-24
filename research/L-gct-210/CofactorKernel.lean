import Mathlib
import PEqualNP.Gct.Helpers.BorderedPerm

namespace LevelSpaceFive.CofactorKernel

open Finset Module

abbrev Entry := Fin 5 × Fin 5 → ℂ
abbrev Row := Fin 5 → ℂ

def level (L : Submodule ℂ Entry) : Prop :=
  ∀ t ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i,e i))) = 120

def rowAt : Entry →ₗ[ℂ] Row :=
  LinearMap.funLeft ℂ ℂ (fun j => (Fin.last 4,j))

def minors (x : Entry) : Row := fun j =>
  ((Matrix.of fun i k : Fin 5 => x (i,k)).submatrix Fin.castSucc j.succAbove).permanent

private def shifted (t x : Entry) (a : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun i j => 1 + t (i,j) + a*x (i,j)

private lemma at_level {L : Submodule ℂ Entry} (hL : level L) {t x : Entry}
    (ht : t ∈ L) (hx : x ∈ L) (a : ℂ) : (shifted t x a).permanent = 120 := by
  let u := t + a • x
  have b : u ∈ L := L.add_mem ht (L.smul_mem a hx)
  have h : (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + u (i,e i))) =
      (Matrix.of fun i j : Fin 5 => 1 + u (i,j)).transpose.permanent :=
    (Equiv.embeddingEquivOfFinite (Fin 5)).sum_comp (fun e => ∏ i, (1 + u (i,e i)))
  rw [Matrix.permanent_transpose] at h
  have he : shifted t x a = (Matrix.of fun i j : Fin 5 => 1 + u (i,j)) := by
    ext i j
    change 1 + t (i,j) + a*x (i,j) = 1 + (t (i,j) + a*x (i,j))
    ring
  rw [he,← h]
  exact hL u b

private lemma difference4 (b d : Matrix (Fin 4) (Fin 4) ℂ) :
    (b+(4:ℂ)•d).permanent - 4*(b+(3:ℂ)•d).permanent + 6*(b+(2:ℂ)•d).permanent -
        4*(b+d).permanent + b.permanent = 24*d.permanent := by
  classical
  simp only [Matrix.permanent, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Fin.prod_univ_succ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  ring

theorem paired_minors {L : Submodule ℂ Entry} (hL : level L) {x : Entry} (hx : x ∈ L)
    (hz : rowAt x = 0) (t : Entry) (ht : t ∈ L) :
    (∑ j, (1+t (Fin.last 4,j))*minors x j) = 0 := by
  classical
  let b (j : Fin 5) := (Matrix.of fun i k : Fin 5 => 1+t (i,k)).submatrix Fin.castSucc j.succAbove
  let d (j : Fin 5) := (Matrix.of fun i k : Fin 5 => x (i,k)).submatrix Fin.castSucc j.succAbove
  have per (n : ℂ) : (∑ j, (1+t (Fin.last 4,j))*(b j + n • d j).permanent) = 120 := by
    have h := at_level hL ht hx (n : ℂ)
    rw [PEqualNP.Gct.Helpers.BorderedPerm.permanent_succ_last_row] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro j _
    have hrow : x (Fin.last 4,j) = 0 := congrFun hz j
    have eqm : (shifted t x (n : ℂ)).submatrix Fin.castSucc j.succAbove = b j + n • d j := by
      ext i k
      rfl
    rw [eqm]
    change _ = (1+t (Fin.last 4,j)+n*x (Fin.last 4,j))*_
    rw [hrow,mul_zero,add_zero]
  have hdiff : (∑ j, (1+t (Fin.last 4,j)) *
      ((b j+(4:ℂ)•d j).permanent - 4*(b j+(3:ℂ)•d j).permanent + 6*(b j+(2:ℂ)•d j).permanent -
      4*(b j+d j).permanent+(b j).permanent)) = 0 := by
    have one := per 1
    have zero := per 0
    simp only [one_smul] at one
    simp only [zero_smul,add_zero] at zero
    simp only [mul_add, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [show ∀ a z : ℂ, a*(4*z)=4*(a*z) from fun a z => by ring,
      show ∀ a z : ℂ, a*(6*z)=6*(a*z) from fun a z => by ring]
    simp only [← Finset.mul_sum]
    linear_combination per 4 - 4 * per 3 + 6 * per 2 - 4 * one + zero
  have hh : (24 : ℂ) * (∑ j, (1+t (Fin.last 4,j))*minors x j) = 0 := by
    rw [Finset.mul_sum]
    convert hdiff using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [difference4]
    change 24 * (_ * (d j).permanent) = _ * (24 * (d j).permanent)
    ring
  linear_combination hh / 24

private lemma one_not_in_row {L : Submodule ℂ Entry} (hl : level L) :
    (1 : Row) ∉ L.map rowAt := by
  rintro ⟨t,ht,he⟩
  have h := hl (-t) (L.neg_mem ht)
  have hz : (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + (-t) (i,e i))) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last 4))
    have a : t (Fin.last 4,e (Fin.last 4)) = 1 := congrFun he _
    change 1 + -t (Fin.last 4,e (Fin.last 4)) = 0
    rw [a]
    ring
  rw [hz] at h
  norm_num at h

theorem all_minors_zero {L : Submodule ℂ Entry} (hl : level L)
    (rank : finrank ℂ (L.map rowAt) = 4) {x : Entry} (hx : x ∈ L)
    (hz : rowAt x = 0) : minors x = 0 := by
  classical
  let f : Row →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∑ j, v j * minors x j
      map_add' := fun a b => by simp [add_mul,Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [mul_assoc,Finset.mul_sum] }
  have hone : f 1 = 0 := by
    simpa [f] using paired_minors hl hx hz 0 L.zero_mem
  have hrow : L.map rowAt ≤ LinearMap.ker f := by
    rintro _ ⟨t,ht,rfl⟩
    change (∑ j, t (Fin.last 4,j) * minors x j) = 0
    have a := paired_minors hl hx hz t ht
    simp only [add_mul,one_mul,Finset.sum_add_distrib] at a
    have b : (∑ j, minors x j) = 0 := by simpa [f] using hone
    linear_combination a-b
  have hf : f=0 := by
    by_contra h
    have a := Module.Dual.finrank_ker_add_one_of_ne_zero h
    have b : finrank ℂ Row = 5 := by simp [Row]
    have equal := Submodule.eq_of_le_of_finrank_le hrow (by omega)
    apply one_not_in_row hl
    rw [equal]
    exact hone
  funext j
  have a := LinearMap.congr_fun hf (Pi.single j (1:ℂ))
  simpa [f,Pi.single_apply,ite_mul] using a

end LevelSpaceFive.CofactorKernel
