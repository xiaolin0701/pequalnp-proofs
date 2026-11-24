import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Insert
import Mathlib.Tactic

namespace FirstAndStructure

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def edgeSelected (X : Set (Fin 9)) : Prop :=
  ∃ e ∈ edges, e.1 ∈ X ∧ e.2 ∈ X

def firstAnd (X : Set (Fin 9)) : Prop := 0 ∈ X ∧ 3 ∈ X

theorem nonedge_on_minterms (e : Fin 9 × Fin 9) (he : e ∈ edges) :
    ¬ firstAnd ({e.1, e.2} : Set (Fin 9)) := by
  simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h <;> subst e <;>
    simp only [firstAnd, Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide

/-- A monotone tail receives the whole input and the value of the first gate. -/
theorem erase_first_and (D : Set (Fin 9) → Prop → Prop)
    (mono : ∀ X Y, X ⊆ Y → ∀ a b : Prop, (a → b) → D X a → D Y b)
    (correct : ∀ X, D X (firstAnd X) ↔ edgeSelected X) :
    ∀ X, D X False ↔ edgeSelected X := by
  intro X
  constructor
  · intro h
    exact (correct X).1 (mono X X (by rfl) False _ False.elim h)
  · rintro ⟨e, he, h₁, h₂⟩
    let Y : Set (Fin 9) := {e.1, e.2}
    have hy : Y ⊆ X := Set.insert_subset h₁ (Set.singleton_subset_iff.mpr h₂)
    have hit : edgeSelected Y := ⟨e, he, by simp [Y], by simp [Y]⟩
    exact mono Y X hy (firstAnd Y) False (nonedge_on_minterms e he) ((correct Y).2 hit)

/-- A binary gate can belong to at most two of the three direct-consumer sets. -/
theorem two_consumers {G : Type*} [DecidableEq G] (A H₀ H₃ : Finset G)
    (ha : A.Nonempty) (h0 : H₀.Nonempty) (h3 : H₃.Nonempty)
    (binary : ∀ g ∈ A, g ∈ H₀ → g ∈ H₃ → False) :
    2 ≤ (A ∪ H₀).card ∨ 2 ≤ (A ∪ H₃).card := by
  by_contra! small
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := h0
  obtain ⟨c, hc⟩ := h3
  have s0 : (A ∪ H₀).card ≤ 1 := by omega
  have s3 : (A ∪ H₃).card ≤ 1 := by omega
  have hab := Finset.card_le_one.mp s0 a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb)
  have hac := Finset.card_le_one.mp s3 a (Finset.mem_union_left _ ha) c (Finset.mem_union_right _ hc)
  exact binary a ha (hab ▸ hb) (hac ▸ hc)

end FirstAndStructure
