import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import PEqualNP.Defs.MetaComplexityLgpMono

namespace AdjacentORReaders

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LowMergeProof
open scoped Classical

theorem changed_reader (C : Circuit) (x y : List Bool) (n i : ℕ)
    (hx : x.length = n) (hy : y.length = n)
    (hin : ∀ k, k ≠ i → x.getD k false = y.getD k false) (ho : C.output ≠ i)
    (hval : C.eval x ≠ C.eval y) :
    ∃ j : Fin C.size, i ∈ C.gates[j.val].inputs ∧
      (C.wires x).getD (n + j.val) false ≠ (C.wires y).getD (n + j.val) false := by
  classical
  by_contra! hn
  have hall : ∀ k, k ≠ i → (C.wires x).getD k false = (C.wires y).getD k false := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hki
      by_cases hkn : k < n
      · rw [wires_input C x k (by omega), wires_input C y k (by omega)]
        exact hin k hki
      by_cases hkg : k < n + C.size
      · let j : Fin C.size := ⟨k - n, by omega⟩
        have he : n + j.val = k := by dsimp [j]; omega
        by_cases hmem : i ∈ C.gates[j.val].inputs
        · rw [← he]; exact hn j hmem
        have hGx := wires_gate C x j.val j.isLt
        have hGy := wires_gate C y j.val j.isLt
        rw [hx, he] at hGx
        rw [hy, he] at hGy
        rw [hGx, hGy]
        congr 1
        apply List.map_congr_left
        intro z hz
        unfold rd
        split
        · apply ih z (by assumption)
          exact fun hz' => hmem (hz' ▸ hz)
        · rfl
      · rw [List.getD_eq_default _ _ (by rw [wires_length, hx]; exact Nat.le_of_not_gt hkg),
          List.getD_eq_default _ _ (by rw [wires_length, hy]; exact Nat.le_of_not_gt hkg)]
  exact hval (hall _ ho)

-- Enable both endpoints of an edge, then disable just one. The first OR
-- stays true across both assignments, so another gate must read that endpoint.
theorem laterReader {n : ℕ} (C : Circuit) (a b : Fin n) (ne : a ≠ b)
    (firstGate : ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD n false = (z a || z b))
    (edge : circuitFun n C (fun i => decide (i=a ∨ i=b)) = true)
    (aloneA : circuitFun n C (fun i => decide (i=a)) = false)
    (aloneB : circuitFun n C (fun i => decide (i=b)) = false) :
    ∃ j : Fin C.size, 0 < j.val ∧ a.val ∈ C.gates[j.val].inputs := by
  let x : Fin n → Bool := fun i => decide (i=a ∨ i=b)
  let y : Fin n → Bool := fun i => decide (i=b)
  have other (k : ℕ) (hk : k ≠ a.val) : (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
    by_cases h : k<n
    · have neq : (⟨k,h⟩ : Fin n) ≠ a := fun e => hk (congrArg Fin.val e)
      simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,x,y,neq]
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,h]
  have out : C.output ≠ a.val := by
    intro e
    let z : Fin n → Bool := fun i => decide (i = a)
    change (C.wires (List.ofFn z)).getD C.output false = false at aloneA
    rw [e,wires_input C _ _ (by simpa using a.isLt)] at aloneA
    simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,a.isLt,z] using aloneA
  have diff : C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    change circuitFun n C x ≠ circuitFun n C y
    rw [show circuitFun n C x=true from edge,show circuitFun n C y=false from aloneB]
    decide
  obtain ⟨j,uses,changes⟩ := changed_reader C _ _ n a.val (by simp) (by simp) other out diff
  refine ⟨j,?_,uses⟩
  by_contra! hj
  have zero : j.val=0 := by omega
  rw [zero,Nat.add_zero,firstGate x,firstGate y] at changes
  simp [x,y] at changes

end AdjacentORReaders
