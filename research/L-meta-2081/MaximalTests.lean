import Mathlib.Data.Set.Lattice.Bounded

namespace Meta2081Tests

variable {P L : Type*} (I : P → L → Prop)

def lines (X : Set P) : Set L := {l | ∀ p ∈ X, ¬ I p l}

def points (Y : Set L) : Set P := {p | ∀ l ∈ Y, ¬ I p l}

theorem complete_negative (X : Set P) (Y : Set L) (indep : ∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) :
    ∃ X' : Set P, X ⊆ X' ∧ Y ⊆ lines I X' ∧
      ∀ p ∉ X', ∃ l ∈ lines I X', I p l := by
  classical
  let X' := points I (lines I X)
  have hx : X ⊆ X' := fun p hp l hl => hl p hp
  have eq : lines I X' = lines I X := by
    apply Set.Subset.antisymm
    · exact fun l hl p hp => hl p (hx hp)
    · exact fun l hl p hp => hp l hl
  refine ⟨X', hx, ?_, ?_⟩
  · rw [eq]
    exact fun l hl p hp => indep p hp l hl
  · intro p hp
    rw [eq]
    by_contra! h
    exact hp (fun l hl => h l hl)

end Meta2081Tests
