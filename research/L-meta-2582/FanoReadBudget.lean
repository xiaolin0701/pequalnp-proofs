import Mathlib
import PEqualNP.Defs.ReadK
import PEqualNP.Defs.TopForm

namespace PlaneReadBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

-- A prime input of an exact bipartite incidence circuit is an incident pair.
theorem primeEdge {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (exactFun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) (prime : IsPrimeImplicant (N + N) C S) :
    ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  obtain ⟨yes, minimal⟩ := prime
  rw [exactFun, decide_eq_true_eq] at yes
  obtain ⟨p, l, incident, hp, hl⟩ := yes
  refine ⟨p, l, incident, ?_⟩
  have inside : ({Fin.castAdd N p, Fin.natAdd N l} : Finset _) ⊆ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with eq | last
    · simpa only [eq] using (of_decide_eq_true hp : Fin.castAdd N p ∈ S)
    · simpa only [Finset.mem_singleton.mp last] using (of_decide_eq_true hl : Fin.natAdd N l ∈ S)
  by_contra ne
  have no := minimal _ (Finset.mem_ssubsets.mpr (ssubset_of_subset_of_ne inside (Ne.symm ne)))
  rw [exactFun, decide_eq_false_iff_not] at no
  exact no ⟨p, l, incident, by simp [setInput], by simp [setInput]⟩

theorem readFromEdges {N k : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (exactFun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (edgeTest : ∀ p l, I p l →
      readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) k = true) :
    IsReadK (N + N) C k := by
  intro S prime
  obtain ⟨p, l, hi, rfl⟩ := primeEdge I exactFun S prime
  exact edgeTest p l hi

private def gates : List Gate := [
  ⟨.or, [7, 13]⟩,
  ⟨.or, [14, 11]⟩,
  ⟨.and, [0, 15]⟩,
  ⟨.or, [8, 7]⟩,
  ⟨.or, [17, 12]⟩,
  ⟨.and, [1, 18]⟩,
  ⟨.or, [9, 8]⟩,
  ⟨.or, [20, 13]⟩,
  ⟨.and, [2, 21]⟩,
  ⟨.or, [10, 9]⟩,
  ⟨.or, [23, 7]⟩,
  ⟨.and, [3, 24]⟩,
  ⟨.or, [11, 10]⟩,
  ⟨.or, [26, 8]⟩,
  ⟨.and, [4, 27]⟩,
  ⟨.or, [12, 11]⟩,
  ⟨.or, [29, 9]⟩,
  ⟨.and, [5, 30]⟩,
  ⟨.or, [13, 12]⟩,
  ⟨.or, [32, 10]⟩,
  ⟨.and, [6, 33]⟩,
  ⟨.or, [31, 34]⟩,
  ⟨.or, [28, 35]⟩,
  ⟨.or, [25, 36]⟩,
  ⟨.or, [22, 37]⟩,
  ⟨.or, [19, 38]⟩,
  ⟨.or, [16, 39]⟩]

def witness : Circuit := ⟨gates, 40⟩

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

instance : DecidableRel incident := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem planeAxioms :
    (∀ l : Fin 7, (Finset.univ.filter (fun p => incident p l)).card = 3) ∧
    (∀ p r : Fin 7, p ≠ r → ∃! l : Fin 7, incident p l ∧ incident r l) := by
  simp only [ExistsUnique]
  decide +kernel

theorem size_exact : witness.size = 27 := by decide

theorem ao : PEqualNP.TopForm.IsAO2 14 witness := by decide +kernel

private theorem eval_stars (x : Fin 14 → Bool) : witness.eval (List.ofFn x) =
    (star x 0 || (star x 1 || (star x 2 || (star x 3 || (star x 4 || (star x 5 || star x 6)))))) := by
  have raw : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13] := rfl
  rw [raw]
  simp [witness, gates, Circuit.eval, Circuit.wires, GateOp.eval, star, List.getD, List.foldl]
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

private theorem exactFun (z : Fin 14 → Bool) : circuitFun 14 witness z =
    decide (∃ p l : Fin 7, incident p l ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [circuitFun, decide_eq_true_eq] using correct z

set_option maxRecDepth 20000 in
private theorem edgesChecked : ∀ (p l : Fin 7), incident p l →
    readsAtMost witness 14 (setList {Fin.castAdd 7 p, Fin.natAdd 7 l}) 2 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem readOne : IsReadK 14 witness 1 := by
  apply readFromEdges incident exactFun
  decide +kernel

theorem fano27 (C : Circuit) (budget : 27 ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 14 D ∧
      (∀ z : Fin 14 → Bool, circuitFun 14 D z =
        decide (∃ p l : Fin 7, incident p l ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK 14 D 2 := by
  exact ⟨witness, ao, exactFun, size_exact ▸ budget, readFromEdges incident exactFun edgesChecked⟩

end PlaneReadBudget
