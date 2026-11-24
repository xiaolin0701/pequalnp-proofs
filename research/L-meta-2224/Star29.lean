import PEqualNP.Defs

namespace FanoDoubleRead
open PEqualNP.CircuitLowerBounds

/-- The point-centred star circuit, followed by a two-gate absorption. -/
private def gates : List Gate := [
  ⟨.or, [7,13]⟩,
  ⟨.or, [14,11]⟩,
  ⟨.and, [0,15]⟩,
  ⟨.or, [8,7]⟩,
  ⟨.or, [17,12]⟩,
  ⟨.and, [1,18]⟩,
  ⟨.or, [9,8]⟩,
  ⟨.or, [20,13]⟩,
  ⟨.and, [2,21]⟩,
  ⟨.or, [10,9]⟩,
  ⟨.or, [23,7]⟩,
  ⟨.and, [3,24]⟩,
  ⟨.or, [11,10]⟩,
  ⟨.or, [26,8]⟩,
  ⟨.and, [4,27]⟩,
  ⟨.or, [12,11]⟩,
  ⟨.or, [29,9]⟩,
  ⟨.and, [5,30]⟩,
  ⟨.or, [13,12]⟩,
  ⟨.or, [32,10]⟩,
  ⟨.and, [6,33]⟩,
  ⟨.or, [31,34]⟩,
  ⟨.or, [28,35]⟩,
  ⟨.or, [25,36]⟩,
  ⟨.or, [22,37]⟩,
  ⟨.or, [19,38]⟩,
  ⟨.or, [16,39]⟩,
  ⟨.or, [40,0]⟩,
  ⟨.and, [40,41]⟩]

def witness : Circuit := ⟨gates, 42⟩

def incident (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

def pred (x : Fin 14 → Bool) (p : Fin 7) : Prop :=
  x (Fin.castAdd 7 p) = true ∧ ∃ l : Fin 7, incident p l ∧ x (Fin.natAdd 7 l) = true

private def star (x : Fin 14 → Bool) (p : Fin 7) : Bool :=
  x (Fin.castAdd 7 p) && ((x (Fin.natAdd 7 p) || x (Fin.natAdd 7 (p-1))) ||
    x (Fin.natAdd 7 (p-3)))

private theorem star_correct (x : Fin 14 → Bool) (p : Fin 7) : star x p = true ↔ pred x p := by
  simp only [star, pred, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨hp, (h | h) | h⟩
    · exact ⟨hp,p,Or.inl rfl,h⟩
    · exact ⟨hp,p-1,Or.inr (Or.inl (by simp)),h⟩
    · exact ⟨hp,p-3,Or.inr (Or.inr (by simp)),h⟩
  · rintro ⟨hp,l,(h|h|h),hl⟩
    · subst p; exact ⟨hp,Or.inl (Or.inl hl)⟩
    · subst p; exact ⟨hp, Or.inl (Or.inr (by simpa using hl))⟩
    · subst p; exact ⟨hp, Or.inr (by simpa using hl)⟩

theorem shape :
    ∀ j g, witness.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j := by
  intro j g hj
  have h : j < 29 := by
    by_contra! h
    have hn : witness.gates[j]? = none := List.getElem?_eq_none (by exact h)
    rw [hn] at hj; contradiction
  interval_cases j <;> simp [witness,gates] at hj <;> subst g <;> simp

theorem size_exact : witness.size = 29 := by decide

theorem degree_pair : witness.lineDeg 14 {0} = 2 ∧ witness.lineDeg 14 {7} = 2 := by decide +kernel

private theorem eval_stars (x : Fin 14 → Bool) : witness.eval (List.ofFn x) =
    (star x 0 || (star x 1 || (star x 2 || (star x 3 || (star x 4 || (star x 5 || star x 6)))))) := by
  have raw : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13] := rfl
  rw [raw]
  have absorb (a b : Bool) : (a && (a || b)) = a := by cases a <;> rfl
  simp [witness, gates, Circuit.eval, Circuit.wires, GateOp.eval, star, List.getD, List.foldl, absorb]
  rfl
theorem correct (x : Fin 14 → Bool) : witness.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 7, incident p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  rw [eval_stars]
  simp only [Bool.or_eq_true,star_correct]
  constructor
  · intro h
    have hh : ∃ p : Fin 7, pred x p := by
      rcases h with h|h|h|h|h|h|h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
      · exact ⟨3,h⟩
      · exact ⟨4,h⟩
      · exact ⟨5,h⟩
      · exact ⟨6,h⟩
    obtain ⟨p,hp,l,hpl,hl⟩ := hh
    exact ⟨p,l,hpl,hp,hl⟩
  · rintro ⟨p,l,hpl,hp,hl⟩
    have h : pred x p := ⟨hp,l,hpl,hl⟩
    fin_cases p <;> solve_by_elim (maxDepth := 10) only [Or.inl, Or.inr, h]

end FanoDoubleRead
