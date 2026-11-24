import Mathlib
import PEqualNP.Defs

namespace ExtractTwoGates

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem preserve (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

private def clipped (i : ℕ) : Fin 11 := ⟨min i 10, by omega⟩

private theorem clipped_read (w : List Bool) (hw : w.length = 10) (k : ℕ) :
    w.getD (clipped k) false = w.getD k false := by
  change w.getD (min k 10) false = _
  by_cases hk : k ≤ 10
  · rw [Nat.min_eq_left hk]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

private theorem readers (g : Gate) (ho : g.op = GateOp.or) (hl : g.inputs.length ≤ 2) :
    ∃ a b : Fin 11, ∀ w : List Bool, w.length = 10 →
      g.op.eval (g.inputs.map fun i => w.getD i false) = (w.getD a false || w.getD b false) := by
  rw [ho]
  generalize he : g.inputs = ins at *
  cases ins with
  | nil =>
    refine ⟨10,10,?_⟩
    intro w hw
    change false = (w.getD 10 false || w.getD 10 false)
    rw [List.getD_eq_default _ _ (by omega)]
    rfl
  | cons u us =>
    cases us with
    | nil =>
      refine ⟨clipped u, clipped u, ?_⟩
      intro w hw
      rw [clipped_read w hw u]
      simp [GateOp.eval]
    | cons v vs =>
      cases vs with
      | nil =>
        refine ⟨clipped u, clipped v, ?_⟩
        intro w hw
        rw [clipped_read w hw u, clipped_read w hw v]
        simp [GateOp.eval]
      | cons z zs => simp at hl

theorem extract : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) →
      C.gates[1]?.map Gate.op = some GateOp.or →
      ∃ (a b : Fin 11) (D : Circuit), FanInTwo D ∧ D.size + 2 = C.size ∧
        ∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
          D.eval (w ++ [w.getD a false || w.getD b false]) = circuitFun 9 C x := by
  intro C hfan hfirst hsecond
  cases C with
  | mk gates out =>
    cases gates with
    | nil => simp at hsecond
    | cons g gs =>
      cases gs with
      | nil => simp at hsecond
      | cons h tail =>
        have hop : h.op = GateOp.or := by simpa using hsecond
        have hlen : h.inputs.length ≤ 2 := (hfan h (by simp)).2
        obtain ⟨a,b,hab⟩ := readers h hop hlen
        refine ⟨a,b,⟨tail,out⟩, ?_, ?_, ?_⟩
        · intro g' hg'
          exact hfan g' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg'))
        · simp [Circuit.size, Nat.add_assoc]
        · intro x
          let w := List.ofFn x
          have hw : w.length = 9 := by simp [w]
          let v := g.op.eval (g.inputs.map fun i => w.getD i false)
          have hv := hfirst x
          change ((h :: tail).foldl step (w ++ [v])).getD 9 false = _ at hv
          rw [preserve _ _ _ (by simp [hw])] at hv
          rw [List.getD_append_right _ _ _ _ (by omega), hw] at hv
          change v = (x 0 || x 4) at hv
          let w' := w ++ [x 0 || x 4]
          have hpair := hab w' (by simp [w', hw])
          change (tail.foldl step (w' ++ [w'.getD a false || w'.getD b false])).getD out false =
            (tail.foldl step (step (w ++ [v]) h)).getD out false
          rw [hv]
          change _ = (tail.foldl step (w' ++ [h.op.eval (h.inputs.map fun i => w'.getD i false)])).getD out false
          rw [hpair]

end ExtractTwoGates
