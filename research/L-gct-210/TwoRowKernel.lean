import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

namespace LevelSpaceFive.TwoRowKernel

open Module

abbrev Entry := Fin 2 × Fin 5 → ℂ

def rowSum (i : Fin 2) (x : Entry) : ℂ := ∑ j, x (i,j)

private lemma common_kernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a f g : V →ₗ[ℂ] ℂ) (h : ∀ x, f x * g x = -(a x)^2)
    (y : V) (hy : a y ≠ 0) (x : V) (hx : a x = 0) : f x = 0 ∧ g x = 0 := by
  have hz : f x * g x = 0 := by simpa [hx] using h x
  have hn : f y * g y ≠ 0 := by rw [h y]; exact neg_ne_zero.mpr (pow_ne_zero _ hy)
  have hf : f y ≠ 0 := left_ne_zero_of_mul hn
  have hg : g y ≠ 0 := right_ne_zero_of_mul hn
  have he := h (y+x)
  simp only [map_add, hx, add_zero] at he
  have mixed : f y * g x + f x * g y = 0 := by linear_combination he - h y - hz
  rcases mul_eq_zero.mp hz with fx | gx
  · simp only [fx, zero_mul, add_zero] at mixed
    exact ⟨fx, (mul_eq_zero.mp mixed).resolve_left hf⟩
  · simp only [gx, mul_zero, zero_add] at mixed
    exact ⟨(mul_eq_zero.mp mixed).resolve_right hg, gx⟩

private def total (N : Submodule ℂ Entry) : N →ₗ[ℂ] ℂ where
  toFun x := rowSum 0 x
  map_add' x y := by simp [rowSum, Finset.sum_add_distrib]
  map_smul' c x := by simp [rowSum, Finset.mul_sum]

private def coord (N : Submodule ℂ Entry) (i : Fin 2) (j : Fin 5) : N →ₗ[ℂ] ℂ where
  toFun x := x.val (i,j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem disjoint_rows (N : Submodule ℂ Entry) (hd : 2 ≤ finrank ℂ N)
    (hsum : ∀ x ∈ N, rowSum 0 x + rowSum 1 x = 0)
    (hid : ∀ x ∈ N, ∀ j : Fin 5,
      (2*x (0,j) - rowSum 0 x)*(2*x (1,j) + rowSum 0 x) = -(rowSum 0 x)^2) :
    (∀ x ∈ N, rowSum 0 x = 0 ∧ rowSum 1 x = 0) ∧
    ∀ j : Fin 5, (∀ x ∈ N, x (0,j) = 0) ∨ (∀ x ∈ N, x (1,j) = 0) := by
  classical
  have vanish : ∀ x : N, total N x = 0 := by
    by_contra! hn
    obtain ⟨y, hy⟩ := hn
    have ker : ∀ x : N, total N x = 0 → x = 0 := by
      intro x hx
      apply Subtype.ext
      funext ij
      obtain ⟨i,j⟩ := ij
      let f := (2 : ℂ) • coord N 0 j - total N
      let g := (2 : ℂ) • coord N 1 j + total N
      have hh := common_kernel (total N) f g (fun v => hid v v.property j) y hy x hx
      change 2 * x.val (0,j) - total N x = 0 ∧ 2 * x.val (1,j) + total N x = 0 at hh
      rw [hx] at hh
      fin_cases i
      · change x.val (0,j) = 0
        linear_combination hh.1 / 2
      · change x.val (1,j) = 0
        linear_combination hh.2 / 2
    have inj : Function.Injective (total N) := by
      intro x y h
      apply sub_eq_zero.mp
      apply ker
      rw [map_sub, h, sub_self]
    have bound := Submodule.finrank_le (LinearMap.range (total N))
    rw [LinearMap.finrank_range_of_inj inj] at bound
    simp at bound
    omega
  have h0 (x : Entry) (hx : x ∈ N) : rowSum 0 x = 0 := vanish ⟨x,hx⟩
  constructor
  · intro x hx
    exact ⟨h0 x hx, by simpa [h0 x hx] using hsum x hx⟩
  · intro j
    have pair (x : Entry) (hx : x ∈ N) : x (0,j) * x (1,j) = 0 := by
      have h := hid x hx j
      rw [h0 x hx] at h
      linear_combination h / 4
    by_cases hall : ∀ x ∈ N, x (0,j) = 0
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨y, hy, hny⟩ := hall
      have hy1 := (mul_eq_zero.mp (pair y hy)).resolve_left hny
      right
      intro x hx
      have h := pair (y+x) (N.add_mem hy hx)
      change (y (0,j) + x (0,j)) * (y (1,j) + x (1,j)) = 0 at h
      have hcross : y (0,j) * x (1,j) = 0 := by
        rw [hy1, zero_add] at h
        linear_combination h - pair x hx
      exact (mul_eq_zero.mp hcross).resolve_left hny

def productSum (x : Entry) : ℂ := ∑ j, x (0,j)*x (1,j)

def matchingSum (x : Entry) : ℂ := rowSum 0 x * rowSum 1 x - productSum x

def deletedMatching (x : Entry) (j : Fin 5) : ℂ :=
  (rowSum 0 x - x (0,j)) * (rowSum 1 x - x (1,j)) -
    (productSum x - x (0,j)*x (1,j))

theorem disjoint_of_deletions (N : Submodule ℂ Entry) (hd : 2 ≤ finrank ℂ N)
    (hsum : ∀ x ∈ N, rowSum 0 x + rowSum 1 x = 0)
    (hmatching : ∀ x ∈ N, matchingSum x = 0)
    (hdeleted : ∀ x ∈ N, ∀ j, deletedMatching x j = 0) :
    (∀ x ∈ N, rowSum 0 x = 0 ∧ rowSum 1 x = 0) ∧
    ∀ j : Fin 5, (∀ x ∈ N, x (0,j) = 0) ∨ (∀ x ∈ N, x (1,j) = 0) := by
  apply disjoint_rows N hd hsum
  intro x hx j
  have h := hdeleted x hx j
  have k := hmatching x hx
  unfold deletedMatching at h
  unfold matchingSum at k
  linear_combination 2*h - 2*k + 2*x (0,j)*(hsum x hx)

private lemma sum_row_add (x y : Entry) (i : Fin 2) :
    rowSum i (x+y) = rowSum i x + rowSum i y := by
  simp [rowSum, Finset.sum_add_distrib]

private lemma sum_row_sub (x y : Entry) (i : Fin 2) :
    rowSum i (x-y) = rowSum i x - rowSum i y := by
  simp [rowSum, Finset.sum_sub_distrib]

private lemma sum_deleted (x : Entry) :
    ∑ j, deletedMatching x j = 3*matchingSum x := by
  have hh (j : Fin 5) : deletedMatching x j =
      matchingSum x - rowSum 0 x * x (1,j) - rowSum 1 x * x (0,j) +
        2*(x (0,j)*x (1,j)) := by unfold deletedMatching matchingSum; ring
  simp only [hh, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change 5 * matchingSum x - rowSum 0 x * rowSum 1 x -
    rowSum 1 x * rowSum 0 x + 2 * productSum x = _
  unfold matchingSum
  ring

private lemma dot_parallelogram (z x : Entry) :
    productSum (z+x) + productSum (z-x) - 2*productSum z = 2*productSum x := by
  unfold productSum
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (z (0,j)+x (0,j))*(z (1,j)+x (1,j)) +
    (z (0,j)-x (0,j))*(z (1,j)-x (1,j)) - 2*(z (0,j)*z (1,j)) = _
  ring

private lemma deleted_parallelogram (z x : Entry) (j : Fin 5) :
    deletedMatching (z+x) j + deletedMatching (z-x) j - 2*deletedMatching z j =
      2*deletedMatching x j := by
  simp only [deletedMatching, sum_row_add, sum_row_sub, Pi.add_apply, Pi.sub_apply]
  linear_combination -dot_parallelogram z x

private lemma first_difference (x : Entry) :
    matchingSum (1+x) - matchingSum (1-x) = 8*(rowSum 0 x + rowSum 1 x) := by
  have d : productSum (1+x) - productSum (1-x) = 2*(rowSum 0 x + rowSum 1 x) := by
    simp only [productSum, rowSum, mul_add, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change (1+x (0,j))*(1+x (1,j)) - (1-x (0,j))*(1-x (1,j)) = _
    ring
  have one (i : Fin 2) : rowSum i 1 = 5 := by simp [rowSum]
  simp only [matchingSum, sum_row_add, sum_row_sub, one]
  linear_combination -d

abbrev Row := Fin 5 → ℂ
abbrev Triple := Entry × Row

def rectangular (x : Entry) (u : Row) : ℂ := ∑ j, u j * deletedMatching x j

theorem disjoint_in_rank_four (K : Submodule ℂ Triple)
    (hlevel : ∀ z ∈ K, rectangular (1+z.1) (1+z.2) = 60)
    (N : Submodule ℂ Entry) (hN : ∀ x ∈ N, (x,(0 : Row)) ∈ K)
    (hd : 2 ≤ finrank ℂ N)
    (hr : finrank ℂ (K.map (LinearMap.snd ℂ Entry Row)) = 4) :
    (∀ x ∈ N, rowSum 0 x = 0 ∧ rowSum 1 x = 0) ∧
    ∀ j : Fin 5, (∀ x ∈ N, x (0,j) = 0) ∨ (∀ x ∈ N, x (1,j) = 0) := by
  classical
  have uone : (1 : Row) ∉ K.map (LinearMap.snd ℂ Entry Row) := by
    rintro ⟨z,hz,he⟩
    change z.2 = 1 at he
    have h := hlevel (-z) (K.neg_mem hz)
    change rectangular (1 + -z.1) (1 + -z.2) = 60 at h
    rw [he, add_neg_cancel] at h
    simp [rectangular] at h
  have deletions (x : Entry) (hx : x ∈ N) : ∀ j, deletedMatching x j = 0 := by
    let F : Row →ₗ[ℂ] ℂ := {
      toFun u := ∑ j, u j * deletedMatching x j
      map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
      map_smul' c v := by simp [Finset.mul_sum, mul_assoc] }
    have ortho (z : Triple) (hz : z ∈ K) : F (1+z.2) = 0 := by
      have pp := hlevel (z+(x,0)) (K.add_mem hz (hN x hx))
      have mm := hlevel (z-(x,0)) (K.sub_mem hz (hN x hx))
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, add_zero, sub_zero,
        ← add_assoc, ← add_sub_assoc] at pp mm
      have h : 2 * F (1+z.2) = rectangular (1+z.1+x) (1+z.2) +
          rectangular (1+z.1-x) (1+z.2) - 2*rectangular (1+z.1) (1+z.2) := by
        simp only [F, rectangular, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        linear_combination -((1+z.2) j)*deleted_parallelogram (1+z.1) x j
      rw [pp, mm, hlevel z hz] at h
      linear_combination h / 2
    have ho : F 1 = 0 := by simpa using ortho 0 K.zero_mem
    have sub : K.map (LinearMap.snd ℂ Entry Row) ≤ LinearMap.ker F := by
      rintro _ ⟨z,hz,rfl⟩
      change F z.2 = 0
      simpa [ho] using ortho z hz
    have hf : F = 0 := by
      by_contra hn
      have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hn
      have h5 : finrank ℂ Row = 5 := by simp [Row]
      have eqn := Submodule.eq_of_le_of_finrank_le sub (by omega)
      exact uone (eqn.symm ▸ ho)
    intro j
    have e := LinearMap.congr_fun hf (Pi.single j (1 : ℂ))
    simpa [F, Pi.single_apply, ite_mul] using e
  apply disjoint_of_deletions N hd _ _ deletions
  · intro x hx
    have hp := hlevel (x,0) (hN x hx)
    have hm := hlevel (-x,0) (hN (-x) (N.neg_mem hx))
    change rectangular (1+x) (1+0) = 60 at hp
    change rectangular (1+ -x) (1+0) = 60 at hm
    simp only [rectangular, add_zero, Pi.one_apply, one_mul, sum_deleted,
      ← sub_eq_add_neg] at hp hm
    linear_combination (hp - hm)/24 - first_difference x / 8
  · intro x hx
    have h := sum_deleted x
    simp only [deletions x hx, Finset.sum_const_zero] at h
    linear_combination -h / 3

end LevelSpaceFive.TwoRowKernel
