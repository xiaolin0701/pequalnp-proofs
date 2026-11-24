import Mathlib.Combinatorics.Configuration
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Meta2796

open scoped LinearAlgebra.Projectivization Classical
open Configuration

theorem plane256_symmetric : ∃ I : Fin 65793 → Fin 65793 → Prop,
    (∀ p l, I p l ↔ I l p) ∧
    (∀ l, Fintype.card {p : Fin 65793 // I p l} = 257) ∧
    ∀ p z, p ≠ z → ∃! l, I p l ∧ I z l := by
  classical
  let K := GaloisField 2 8
  let P := ℙ K (Fin 3 → K)
  let _ := Fintype.ofFinite P
  have hk : Nat.card K = 256 := (GaloisField.card 2 8 (by decide))
  have hc : Fintype.card P = 65793 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (ℙ K (Fin 3 → K)) = _
    rw [Projectivization.card_of_finrank K (Fin 3 → K) (n := 3) (by simp), hk]
    norm_num [Finset.sum_range_succ]
  have hp := ProjectivePlane.card_points P P
  let d := ProjectivePlane.order P P
  change Fintype.card P = d^2 + d + 1 at hp
  rw [hc] at hp
  have hd : d = 256 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have bound : d^2 ≤ 255^2 := Nat.pow_le_pow_left (by omega) 2
      omega
    · have bound : 257^2 ≤ d^2 := Nat.pow_le_pow_left (by omega) 2
      omega
  let e : Fin 65793 ≃ P := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun p l => e p ∈ e l, fun _ _ => Projectivization.orthogonal_comm, ?_, ?_⟩
  · intro l
    let eqv : {p : Fin 65793 // e p ∈ e l} ≃ {p : P // p ∈ e l} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    rw [Fintype.card_congr eqv, ← Nat.card_eq_fintype_card]
    change pointCount P (e l) = 257
    rw [ProjectivePlane.pointCount_eq]
    change d + 1 = 257
    omega
  · intro p z hpz
    obtain ⟨l, hl, hun⟩ := HasLines.existsUnique_line P P (e p) (e z) (e.injective.ne hpz)
    refine ⟨e.symm l, by simpa using hl, ?_⟩
    intro l' hl'
    exact e.injective (by simpa using hun (e l') hl')

theorem plane256 : ∃ I : Fin 65793 → Fin 65793 → Prop,
    (∀ l, Fintype.card {p : Fin 65793 // I p l} = 257) ∧
    ∀ p z, p ≠ z → ∃! l, I p l ∧ I z l := by
  obtain ⟨I, _, h⟩ := plane256_symmetric
  exact ⟨I, h⟩

end Meta2796
