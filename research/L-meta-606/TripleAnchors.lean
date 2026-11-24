import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Lattice.Bounded

namespace Meta606TripleAnchors

variable {P L : Type*}

def missing (I : P → L → Prop) (T : Set L) : Set P :=
  {p | ∀ l ∈ T, ¬ I p l}

/-- The same edge-free assignment tests a singleton for A and a pair (or any set) for B. -/
theorem cross_set (I : P → L → Prop) (A B : Set P → Set L → Prop)
    (aMono : ∀ X, Monotone (A X)) (bMono : ∀ X, Monotone (B X))
    (sound : ∀ X Y, A X Y → B X Y → ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (S T : Set L) : ¬ A (missing I (S ∪ T)) S ∨ ¬ B (missing I (S ∪ T)) T := by
  classical
  by_cases h : A (missing I (S ∪ T)) S
  · right
    intro k
    obtain ⟨p, hp, l, hl, edge⟩ := sound _ _
      (aMono _ Set.subset_union_left h) (bMono _ Set.subset_union_right k)
    exact hp l hl edge
  · exact Or.inl h

open Finset

/-- Count the weight of exceptional anchors with multiplicity across a finite family of tests. -/
theorem exceptional_weight {L T : Type*} (lines : Finset L) (tests : Finset T)
    (w : L → ℕ) (bad : L → T → Prop) [DecidableRel bad] (D : ℕ)
    (cap : ∀ t ∈ tests, (∑ l ∈ lines, if bad l t then w l else 0) ≤ D) :
    ∑ l ∈ lines, w l * (tests.filter (bad l)).card ≤ tests.card * D := by
  calc
    _ = ∑ l ∈ lines, ∑ t ∈ tests, if bad l t then w l else 0 := by
      apply sum_congr rfl
      intro l _
      rw [← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
    _ = ∑ t ∈ tests, ∑ l ∈ lines, if bad l t then w l else 0 := sum_comm
    _ ≤ ∑ _t ∈ tests, D := sum_le_sum cap
    _ = _ := by simp

end Meta606TripleAnchors
