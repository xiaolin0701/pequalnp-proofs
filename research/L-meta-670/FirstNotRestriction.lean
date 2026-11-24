import Mathlib.Data.Fin.VecNotation

namespace PetersenFirstNot

def edge9 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def pin (b : Bool) (y : Fin 8 → Bool) : Fin 9 → Bool :=
  ![y 0, y 1, y 2, y 3, b, y 4, y 5, y 6, y 7]

def edge8 (y : Fin 8 → Bool) : Bool :=
  (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) || (y 1 && y 5) ||
  (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) || (y 5 && y 7) || (y 7 && y 4)

def cycleWithTwoInputs (y : Fin 8 → Bool) : Bool :=
  y 0 || y 3 || (y 1 && y 2) || (y 2 && y 6) || (y 6 && y 4) ||
  (y 4 && y 7) || (y 7 && y 5) || (y 5 && y 1)

theorem restrictions : ∀ y : Fin 8 → Bool,
    edge9 (pin false y) = edge8 y ∧ edge9 (pin true y) = cycleWithTwoInputs y := by
  intro y
  simp [edge9, pin, edge8, cycleWithTwoInputs]
  cases h0 : y 0 <;> cases h3 : y 3 <;>
    simp [h0, h3, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm, Bool.and_comm]

def singleton (j : Fin 8) : Fin 8 → Bool := fun i => decide (i = j)

theorem sensitive (j : Fin 8) (hj : j = 0 ∨ j = 3) :
    edge9 (pin false (singleton j)) = false ∧ edge9 (pin true (singleton j)) = true := by
  rcases hj with rfl | rfl <;> decide

/-- The remaining circuit has a distinguished wire, with a variable replacement value. -/
def realizesSplit (w : (Fin 8 → Bool) → Bool) (d : (Fin 8 → Bool) → Bool → Bool) : Prop :=
  ∀ b y, edge9 (pin b y) = d y ((!b) && w y)

theorem splitAtSensitive {w d} (h : realizesSplit w d) (y : Fin 8 → Bool)
    (hf : edge9 (pin false y) = false) (ht : edge9 (pin true y) = true) :
    w y = true ∧ d y true = false ∧ d y false = true := by
  have h0 := h false y
  have h1 := h true y
  simp only [Bool.not_false, Bool.true_and, hf] at h0
  simp only [Bool.not_true, Bool.false_and, ht] at h1
  cases hx : w y with
  | false =>
    rw [hx] at h0
    exact Bool.noConfusion (h0.trans h1.symm)
  | true =>
    rw [hx] at h0
    exact ⟨rfl, h0.symm, h1.symm⟩

theorem splitNecessary {w d} (h : realizesSplit w d) (j : Fin 8) (hj : j = 0 ∨ j = 3) :
    w (singleton j) = true ∧ d (singleton j) true = false ∧ d (singleton j) false = true :=
  splitAtSensitive h _ (sensitive j hj).1 (sensitive j hj).2

theorem splitNotInput {w d} (h : realizesSplit w d) : ∀ k : Fin 8, w ≠ fun y => y k := by
  intro k hk
  have h0 := (splitNecessary h 0 (Or.inl rfl)).1
  have h3 := (splitNecessary h 3 (Or.inr rfl)).1
  rw [hk] at h0 h3
  simp only [singleton, decide_eq_true_eq] at h0 h3
  omega

def pairWitness (k : Fin 8) : Fin 8 → Bool :=
  fun i => decide (i = k ∨ i = (if k = 1 ∨ k = 4 then 3 else 0))

theorem pairWitnessProperties : ∀ k : Fin 8, pairWitness k k = true ∧
    edge9 (pin false (pairWitness k)) = false ∧ edge9 (pin true (pairWitness k)) = true := by
  decide +kernel

theorem splitNotNegatedInput {w d} (h : realizesSplit w d) : ∀ k : Fin 8, w ≠ fun y => !y k := by
  intro k hk
  obtain ⟨hk1, h0, h1⟩ := pairWitnessProperties k
  have hw := (splitAtSensitive h _ h0 h1).1
  rw [hk] at hw
  simp only [hk1, Bool.not_true] at hw
  exact Bool.noConfusion hw

theorem splitOrInputs {w d} (h : realizesSplit w d) (k l : Fin 8)
    (hw : w = fun y => y k || y l) : (k = 0 ∧ l = 3) ∨ (k = 3 ∧ l = 0) := by
  have h0 := (splitNecessary h 0 (Or.inl rfl)).1
  have h3 := (splitNecessary h 3 (Or.inr rfl)).1
  rw [hw] at h0 h3
  simp only [singleton, Bool.or_eq_true, decide_eq_true_eq] at h0 h3
  omega

theorem splitNeedsNegativeInfluence {w d} (h : realizesSplit w d) :
    ¬ (∀ y, d y false = true → d y true = true) := by
  obtain ⟨_, h1, h0⟩ := splitNecessary h 0 (Or.inl rfl)
  intro mono
  have := mono (singleton 0) h0
  exact Bool.noConfusion (h1.symm.trans this)

end PetersenFirstNot
