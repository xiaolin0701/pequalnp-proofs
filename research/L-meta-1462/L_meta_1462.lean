import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1462 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (X B : Finset (Fin n))
    (r : Fin n → Fin n → Prop) (f : Fin m → Fin n),
    (∀ a b : Fin n, r a b → ¬ r b a) →
    (∀ i : Fin m, ¬ S i ⊆ X → f i ∈ B ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ B, r (f i) y) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S i = {p}) ∧
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j,
        ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, ((if s ∈ X then ({s} : Finset (Fin n)) else {s, f j}) ∩ S i).Nonempty))) := by
  classical
  intro n m S X B r f hasym hchoose
  have outside (i : Fin m) (p : Fin n) (hp : p ∈ S i) (hx : p ∉ X) : ¬ S i ⊆ X :=
    fun h => hx (h hp)
  have crossing (i j : Fin m) (h : ∃ p ∈ S i \ S j,
      ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) :
      ¬ S i ⊆ X ∧ f i ∈ S j := by
    obtain ⟨p, hp, q, hq⟩ := h
    obtain ⟨hpi, hpj⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hqrow, hqj⟩ := Finset.mem_inter.mp hq
    by_cases hx : p ∈ X
    · simp only [if_pos hx, Finset.mem_singleton] at hqrow
      exact (hpj (hqrow ▸ hqj)).elim
    · refine ⟨outside i p hpi hx, ?_⟩
      simp only [if_neg hx, Finset.mem_insert, Finset.mem_singleton] at hqrow
      rcases hqrow with he | he
      · exact (hpj (he ▸ hqj)).elim
      · exact he ▸ hqj
  constructor
  · intro i p hp
    by_cases hx : p ∈ X
    · ext q
      simp only [if_pos hx, Finset.mem_inter, Finset.mem_singleton]
      exact ⟨And.left, fun he => ⟨he, he ▸ hp⟩⟩
    · have hf := (hchoose i (outside i p hp hx)).2.1
      ext q
      simp only [if_neg hx, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨he | he, hq⟩
        · exact he
        · exact (hf (he ▸ hq)).elim
      · rintro rfl
        exact ⟨Or.inl rfl, hp⟩
  · intro i j _ hij
    obtain ⟨hi, hfi⟩ := crossing i j hij.1
    obtain ⟨hj, hfj⟩ := crossing j i hij.2
    obtain ⟨hBi, _, hri⟩ := hchoose i hi
    obtain ⟨hBj, _, hrj⟩ := hchoose j hj
    exact hasym _ _ (hri _ (Finset.mem_inter.mpr ⟨hfj, hBj⟩))
      (hrj _ (Finset.mem_inter.mpr ⟨hfi, hBi⟩))
