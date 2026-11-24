import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic

namespace SecondOrOrbits

abbrev Wire := Fin 11
abbrev Pair := Wire × Wire

-- Wire 9 is x0 AND x3; wire 10 reads false before the second gate is appended.
def canonical (a b : Wire) : Finset Wire :=
  let s := ({a,b} : Finset Wire).erase 10
  if 0 ∈ s ∨ 3 ∈ s then s.erase 9 else s

theorem canonical_value (x : Wire → Prop) (zero : ¬ x 10) (gate : x 9 ↔ x 0 ∧ x 3)
    (a b : Wire) : (∃ j ∈ canonical a b, x j) ↔ x a ∨ x b := by
  let s := ({a,b} : Finset Wire).erase 10
  have base : (∃ j ∈ s, x j) ↔ x a ∨ x b := by
    constructor
    · rintro ⟨j, hj, hx⟩
      have hm := (Finset.mem_erase.mp hj).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl|rfl
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (h|h)
      · exact ⟨a, Finset.mem_erase.mpr ⟨fun e => zero (e ▸ h), by simp⟩, h⟩
      · exact ⟨b, Finset.mem_erase.mpr ⟨fun e => zero (e ▸ h), by simp⟩, h⟩
  change (∃ j ∈ (if 0 ∈ s ∨ 3 ∈ s then s.erase 9 else s), x j) ↔ _
  split
  · rename_i active
    refine Iff.trans ?_ base
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, (Finset.mem_erase.mp hj).2, hx⟩
    · rintro ⟨j, hj, hx⟩
      by_cases h : j = 9
      · subst j
        rcases active with h|h
        · exact ⟨0, Finset.mem_erase.mpr ⟨by decide,h⟩, (gate.mp hx).1⟩
        · exact ⟨3, Finset.mem_erase.mpr ⟨by decide,h⟩, (gate.mp hx).2⟩
      · exact ⟨j, Finset.mem_erase.mpr ⟨h,hj⟩, hx⟩
  · exact base

def symmetries : List (Wire → Wire) :=
  [![0,1,2,3,4,5,6,7,8,9,10], ![0,5,8,3,4,1,7,6,2,9,10],
   ![3,2,1,0,4,8,7,6,5,9,10], ![3,8,5,0,4,2,6,7,1,9,10]]

def representatives : List Pair :=
  [(10,10),(0,10),(1,10),(4,10),(6,10),(9,10),
   (0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),
   (4,6),(4,9),(6,7),(6,9)]

def edge (a b : Wire) : Bool :=
  let E : List Pair := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  E.contains (a,b) || E.contains (b,a)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem automorphisms : symmetries.all (fun σ => decide
    ((∀ i, σ (σ i) = i) ∧ (∀ a b, edge (σ a) (σ b) = edge a b) ∧
      (σ 0 = 0 ∧ σ 3 = 3 ∨ σ 0 = 3 ∧ σ 3 = 0) ∧ σ 9 = 9 ∧ σ 10 = 10)) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cover : ∀ a b : Wire, representatives.any (fun r => symmetries.any (fun σ =>
    canonical a b == canonical (σ r.1) (σ r.2))) = true := by decide +kernel

end SecondOrOrbits
