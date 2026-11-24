import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import PEqualNP.Outside.L_gct_215

namespace LevelSpaceFive

open Module Finset

abbrev Matrix5 := Fin 5 × Fin 5 → ℂ
abbrev Matrix4x5 := Fin 4 × Fin 5 → ℂ

def level {r : ℕ} (L : Submodule ℂ (Fin r × Fin 5 → ℂ)) : Prop :=
  ∀ t ∈ L, (∑ e : Fin r ↪ Fin 5, ∏ a, (1 + t (a,e a))) = 120

def rowAt (i : Fin 5) : Matrix5 →ₗ[ℂ] (Fin 5 → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun j => (i,j))

def removeRow (i : Fin 5) : Matrix5 →ₗ[ℂ] Matrix4x5 :=
  LinearMap.funLeft ℂ ℂ (fun p => (i.succAbove p.1,p.2))

private def restrictEmbedding (i : Fin 5) (e : Fin 5 ↪ Fin 5) : Fin 4 ↪ Fin 5 :=
  i.succAboveEmb.trans e

private lemma restriction_bijective (i : Fin 5) : Function.Bijective (restrictEmbedding i) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b h
    have agree (j : Fin 5) (hj : j ≠ i) : a j = b j := by
      obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
      exact DFunLike.congr_fun h k
    obtain ⟨j,hj⟩ := Finite.surjective_of_injective b.injective (a i)
    have hji : j = i := by
      by_contra hn
      exact hn (a.injective ((agree j hn).trans hj))
    apply DFunLike.ext
    intro k
    by_cases hk : k = i
    · subst k
      simpa [hji] using hj.symm
    · exact agree k hk
  · simp only [Fintype.card_embedding_eq, Fintype.card_fin]
    decide

private lemma removeRow_sum (i : Fin 5) (t : Matrix5) (h : rowAt i t = 0) :
    (∑ e : Fin 4 ↪ Fin 5, ∏ a, (1 + removeRow i t (a,e a))) =
    (∑ e : Fin 5 ↪ Fin 5, ∏ a, (1 + t (a,e a))) := by
  classical
  let E := Equiv.ofBijective _ (restriction_bijective i)
  rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 5 => ∏ a, (1 + removeRow i t (a,e a)))]
  apply Finset.sum_congr rfl
  intro e _
  conv_rhs => rw [Fin.prod_univ_succAbove (fun a => 1 + t (a,e a)) i]
  have hz : t (i,e i) = 0 := congrFun h (e i)
  change _ = (1 + t (i,e i)) * _
  rw [hz, add_zero, one_mul]
  rfl

theorem row_rank (L : Submodule ℂ Matrix5) (hL : level L) (i : Fin 5) :
    finrank ℂ (L.map (rowAt i)) ≤ 4 := by
  have hone : (1 : Fin 5 → ℂ) ∉ L.map (rowAt i) := by
    rintro ⟨t, ht, hrow⟩
    have hzero : (∑ e : Fin 5 ↪ Fin 5, ∏ a, (1 + (-t) (a,e a))) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hh : t (i,e i) = 1 := congrFun hrow (e i)
      change 1 + -t (i,e i) = 0
      rw [hh]; ring
    have := hL (-t) (L.neg_mem ht)
    rw [hzero] at this
    norm_num at this
  have hne : L.map (rowAt i) ≠ ⊤ := fun hh => hone (hh.symm ▸ Submodule.mem_top)
  have h := Submodule.finrank_lt hne
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

theorem bound_by_row {m : ℕ} (bound4 : ∀ W : Submodule ℂ Matrix4x5, level W → finrank ℂ W ≤ m)
    (L : Submodule ℂ Matrix5) (hL : level L) (i : Fin 5) :
    finrank ℂ L ≤ m + finrank ℂ (L.map (rowAt i)) := by
  classical
  let R := (rowAt i).domRestrict L
  let K := LinearMap.ker R
  let D : K →ₗ[ℂ] Matrix4x5 := (removeRow i).comp (L.subtype.comp K.subtype)
  have down : level (LinearMap.range D) := by
    rintro _ ⟨v,rfl⟩
    exact (removeRow_sum i v.1.1 v.2).trans (hL v.1.1 v.1.2)
  have hinj : Function.Injective D := by
    intro u v he
    apply Subtype.ext
    apply Subtype.ext
    funext ⟨a,b⟩
    by_cases ha : a = i
    · subst a
      exact congrFun ((show rowAt i u.1.1 = 0 from u.2).trans
        (show rowAt i v.1.1 = 0 from v.2).symm) b
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq ha
      exact congrFun he (k,b)
  have dimK : finrank ℂ K ≤ m := by
    rw [← LinearMap.finrank_range_of_inj hinj]
    exact bound4 _ down
  have add := R.finrank_range_add_finrank_ker
  have rangeR : LinearMap.range R = L.map (rowAt i) := LinearMap.range_domRestrict _ _
  change finrank ℂ (LinearMap.range R) + finrank ℂ K = finrank ℂ L at add
  rw [rangeR] at add
  omega

-- The assembled four-row theorem in L-gct-215, in its embedding-sum formulation.
private theorem fourRowBound (W : Submodule ℂ Matrix4x5) (h : level W) : finrank ℂ W ≤ 7 := by
  exact PEqualNP.Outside.L_gct_215.Ac.aDe
    PEqualNP.Outside.L_gct_215.Ac.aEn PEqualNP.Outside.L_gct_215.Ac.aGj
    PEqualNP.Outside.L_gct_215.Ac.aCb PEqualNP.Outside.L_gct_215.Ac.vV
    PEqualNP.Outside.L_gct_215.Ac.aFy PEqualNP.Outside.L_gct_215.Ac.aGe h

theorem universal_bound (L : Submodule ℂ Matrix5) (h : level L) : finrank ℂ L ≤ 11 := by
  have a := bound_by_row fourRowBound L h 0
  have b := row_rank L h 0
  omega

theorem four_row_witness_of_eleven (L : Submodule ℂ Matrix5) (h : level L)
    (d : 11 ≤ finrank ℂ L) : ∃ W : Submodule ℂ Matrix4x5, level W ∧ finrank ℂ W = 7 := by
  by_contra! missing
  have bound6 (W : Submodule ℂ Matrix4x5) (hW : level W) : finrank ℂ W ≤ 6 := by
    have upper := fourRowBound W hW
    have excluded := missing W hW
    omega
  have upper := bound_by_row bound6 L h 0
  have row := row_rank L h 0
  omega

theorem necessary_row_rank (L : Submodule ℂ Matrix5) (h : level L)
    (d : 9 ≤ finrank ℂ L) (i : Fin 5) : 2 ≤ finrank ℂ (L.map (rowAt i)) := by
  have := bound_by_row fourRowBound L h i
  omega

def transpose : Matrix5 →ₗ[ℂ] Matrix5 :=
  LinearMap.funLeft ℂ ℂ Prod.swap

def columnAt (j : Fin 5) : Matrix5 →ₗ[ℂ] (Fin 5 → ℂ) :=
  (rowAt j).comp transpose

private lemma transpose_injective : Function.Injective transpose := by
  intro u v h
  funext ⟨i,j⟩
  exact congrFun h (j,i)

private lemma level_transpose (L : Submodule ℂ Matrix5) (h : level L) :
    level (L.map transpose) := by
  rintro _ ⟨t,ht,rfl⟩
  let M : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j => 1 + t (i,j)
  calc
    _ = M.permanent := (Equiv.embeddingEquivOfFinite (Fin 5)).sum_comp
      (fun e => ∏ i, (1 + t (e i,i)))
    _ = M.transpose.permanent := (Matrix.permanent_transpose M).symm
    _ = (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i,e i))) :=
      ((Equiv.embeddingEquivOfFinite (Fin 5)).sum_comp
        (fun e => ∏ i, (1 + t (i,e i)))).symm
    _ = 120 := h _ ht

theorem necessary_column_rank (L : Submodule ℂ Matrix5) (h : level L)
    (d : 9 ≤ finrank ℂ L) (j : Fin 5) : 2 ≤ finrank ℂ (L.map (columnAt j)) := by
  have eqdim := (Submodule.equivMapOfInjective transpose transpose_injective L).finrank_eq
  have col := necessary_row_rank (L.map transpose) (level_transpose L h) (eqdim ▸ d) j
  have maps : L.map (columnAt j) = (L.map transpose).map (rowAt j) :=
    Submodule.map_comp transpose (rowAt j) L
  rw [maps]
  exact col

end LevelSpaceFive
