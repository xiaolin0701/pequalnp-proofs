import PEqualNP.Defs
namespace Meta3156Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_unique_not (pre post : List Gate) (q : Gate)
    (h : ∀ g ∈ pre ++ post, g.op ≠ GateOp.not) (hq : q.op = GateOp.not) :
    ∃! i : Fin (pre ++ q :: post).length, ((pre ++ q :: post).get i).op = GateOp.not := by
  let mid : Fin (pre ++ q :: post).length := ⟨pre.length, by simp⟩
  refine ⟨mid, ?_, ?_⟩
  · simp [mid, List.get_eq_getElem, List.getElem_append_right]; exact hq
  · intro j hj
    apply Fin.ext
    change j.val = pre.length
    by_contra heq
    change ((pre ++ q :: post)[j.val]).op = GateOp.not at hj
    by_cases left : j.val < pre.length
    · rw [List.getElem_append_left left] at hj
      exact h _ (List.mem_append_left _ (List.getElem_mem _)) hj
    · have r : pre.length ≤ j.val := by omega
      rw [List.getElem_append_right r] at hj
      have pos : 0 < j.val - pre.length := by omega
      cases hh : j.val - pre.length with
      | zero => omega
      | succ n =>
        have hn : n < post.length := by
          have hlen := j.isLt
          simp only [List.length_append,List.length_cons] at hlen
          omega
        have hg : ((q :: post)[j.val-pre.length]'(by simp only [List.length_cons]; omega)) = post[n] := by
          simp [hh]
        rw [hg] at hj
        exact h _ (List.mem_append_right _ (List.getElem_mem _)) hj

theorem of_unique_inverter_bound (bound : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → x4 = x3) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ),   have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ x4 :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   have x7 : (Fin (9 : ℕ) → Bool) → Bool := PEqualNP.MetaComplexity.circuitFun (9 : ℕ) { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x6 → (∀ x9 ∈ x2 ++ x3, x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 = x1 → (∀ (x12 : Fin (9 : ℕ) → Bool), (x6.wires (List.ofFn x12)).getD (9 : ℕ) Bool.false = (x12 (0 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)))) → (∀ (x13 : Fin (9 : ℕ)), x13 = (4 : Fin (9 : ℕ)) ∨ x13 = (6 : Fin (9 : ℕ)) ∨ x13 = (7 : Fin (9 : ℕ)) → (fun (x15 : Fin (8 : ℕ) → Bool) => x7 (x13.insertNth Bool.false x15)) ≠ fun (x15 : Fin (8 : ℕ) → Bool) => x1 (x13.insertNth Bool.false x15)) → (16 : ℕ) ≤ x6.size := by
  dsimp only
  intro pre post q o hf hmono hq he hw _
  let C : Circuit := ⟨pre ++ q :: post,o⟩
  change 16 ≤ C.size
  apply bound C hf (split_unique_not pre post q hmono hq) hw
  funext y
  have h := congrFun he y
  change C.eval (List.ofFn y) = _ at h ⊢
  rw [h]
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  simp [Bool.or_assoc] <;> rfl
end Meta3156Bridge
