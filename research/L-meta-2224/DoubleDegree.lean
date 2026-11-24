import PEqualNP.Defs

namespace FanoDoubleRead
open PEqualNP.CircuitLowerBounds

/-- Append the absorption o AND (o OR i). The first new wire has address n + C.size. -/
def doubleDegree (n : ℕ) (C : Circuit) (i : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output,i]⟩, ⟨.and, [C.output,n+C.size]⟩], n+C.size+1⟩

theorem doubleDegree_size (n : ℕ) (C : Circuit) (i : ℕ) :
    (doubleDegree n C i).size = C.size+2 := by simp [doubleDegree,Circuit.size]

private theorem length_pushes {α β : Type*} (v : List α → β → α) (g : List β) (w : List α) :
    (g.foldl (fun w a => w ++ [v w a]) w).length = w.length + g.length := by
  induction g generalizing w with
  | nil => simp
  | cons a g ih => simp [List.foldl_cons,ih]; omega

private theorem end_value {α : Type*} (w : List α) (b d : α) : (w ++ [b]).getD w.length d = b := by simp

private theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length+C.size :=
  length_pushes _ _ _

private theorem deg_len (C : Circuit) (n : ℕ) (mark : Finset ℕ) :
    (C.lineDegrees n mark).length = n+C.size := by
  simp only [Circuit.lineDegrees,length_pushes,List.length_map,List.length_range,Circuit.size]

theorem doubleDegree_eval (n : ℕ) (C : Circuit) (i : ℕ) (ho : C.output < n+C.size)
    (x : List Bool) (hx : x.length = n) :
    (doubleDegree n C i).eval x = C.eval x := by
  let w := C.wires x
  have hw : w.length = n+C.size := by simp [w,wires_len,hx]
  have hold : C.output < w.length := by omega
  let old := w.getD C.output false
  let aux := old || w.getD i false
  have hor : GateOp.or.eval ([C.output,i].map (fun k => w.getD k false)) = aux := by
    simp [GateOp.eval,aux,old]
  have hprefix : (w ++ [aux]).getD C.output false = old := List.getD_append _ _ _ _ hold
  have hlast : (w ++ [aux]).getD (n+C.size) false = aux := by rw [←hw]; simp
  have hl : (w ++ [aux]).length = n+C.size+1 := by simp [hw]
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
  let a := Gate.mk .or [C.output,i]
  let b := Gate.mk .and [C.output,n+C.size]
  have h1 : step w a = w ++ [aux] := congrArg (fun z => w ++ [z]) hor
  change ((C.gates ++ [a,b]).foldl step x).getD (n+C.size+1) false = old
  rw [List.foldl_append]
  change (step (step w a) b).getD (n+C.size+1) false = old
  rw [h1]
  show ((w ++ [aux]) ++ [GateOp.and.eval ([C.output,n+C.size].map
      (fun k => (w ++ [aux]).getD k false))]).getD (n+C.size+1) false = old
  rw [←hl,end_value]
  simp only [List.map_cons,List.map_nil,hprefix,hlast,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true]
  change (old && (old || w.getD i false)) = old
  cases old <;> rfl

theorem doubleDegree_mark (n : ℕ) (C : Circuit) (i : ℕ) (ho : C.output < n+C.size)
    (mark : Finset ℕ) :
    2*C.lineDeg n mark ≤ (doubleDegree n C i).lineDeg n mark := by
  let w := C.lineDegrees n mark
  have hw : w.length = n+C.size := deg_len C n mark
  have hold : C.output < w.length := by omega
  let old := w.getD C.output 0
  let aux := max old (w.getD i 0)
  have hor : (Gate.mk .or [C.output,i]).lineDegree w = aux := by
    simp [Gate.lineDegree,aux,old]
  have hprefix : (w ++ [aux]).getD C.output 0 = old := List.getD_append _ _ _ _ hold
  have hlast : (w ++ [aux]).getD (n+C.size) 0 = aux := by rw [←hw]; simp
  have hl : (w ++ [aux]).length = n+C.size+1 := by simp [hw]
  let step := fun (w : List ℕ) (g : Gate) => w ++ [g.lineDegree w]
  let a := Gate.mk .or [C.output,i]
  let b := Gate.mk .and [C.output,n+C.size]
  let raw := (List.range n).map (fun i => if i ∈ mark then 1 else 0)
  have h1 : step w a = w ++ [aux] := congrArg (fun z => w ++ [z]) hor
  change 2*old ≤ ((C.gates ++ [a,b]).foldl step raw).getD (n+C.size+1) 0
  rw [List.foldl_append]
  change 2*old ≤ (step (step w a) b).getD (n+C.size+1) 0
  rw [h1]
  show 2*old ≤ ((w ++ [aux]) ++ [(Gate.mk .and [C.output,n+C.size]).lineDegree (w ++ [aux])]).getD (n+C.size+1) 0
  rw [←hl,end_value]
  simp only [Gate.lineDegree,List.map_cons,List.map_nil,hprefix,hlast,List.sum_cons,List.sum_nil,Nat.add_zero]
  have := le_max_left old (w.getD i 0)
  change 2*old ≤ old + max old (w.getD i 0)
  omega

theorem doubleDegree_shape (n : ℕ) (C : Circuit) (i : ℕ) (ho : C.output < n+C.size)
    (hi : i < n+C.size) (hne : C.output ≠ i)
    (hshape : ∀ j g, C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j) :
    ∀ j g, (doubleDegree n C i).gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j := by
  intro j g hj
  change (C.gates ++ [Gate.mk .or [C.output,i],Gate.mk .and [C.output,n+C.size]])[j]? = some g at hj
  by_cases hj' : j < C.gates.length
  · rw [List.getElem?_append_left hj'] at hj
    exact hshape j g hj
  · rw [List.getElem?_append_right (by omega)] at hj
    have hjl : C.size ≤ j := Nat.le_of_not_gt hj'
    cases h : j - C.gates.length with
    | zero =>
      have : j = C.size := by change j = C.gates.length; omega
      subst j
      simp [Circuit.size] at hj; subst g
      exact ⟨Or.inr rfl,C.output,i,rfl,hne,ho,hi⟩
    | succ k =>
      cases k with
      | zero =>
        have : j = C.size+1 := by change j = C.gates.length+1; omega
        subst j
        simp [Circuit.size] at hj; subst g
        exact ⟨Or.inl rfl,C.output,n+C.size,rfl,by omega,by omega,by omega⟩
      | succ k => simp [h] at hj

end FanoDoubleRead
