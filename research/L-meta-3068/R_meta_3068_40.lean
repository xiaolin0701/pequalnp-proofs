import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3068_40
  (pin : ∀ (C : Circuit), FanInTwo C →
      let f := fun x : Fin 9 → Bool => C.eval (List.ofFn x ++ [x 4 || x 6])
      f (fun j => decide (j = 0 ∨ j = 6)) ≠ f (fun j => decide (j = 0 ∨ j = 4 ∨ j = 6)) →
      f ((4 : Fin 9).insertNth false (fun _ : Fin 8 => false)) ≠
        f ((4 : Fin 9).insertNth false (fun _ : Fin 8 => true)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
        ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f ((4 : Fin 9).insertNth false y))
  (single : ∀ (n : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool),
    FanInTwo C → C.gates.countP (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ 1 →
    f (fun _ => false) = false → f (fun _ => true) = true →
    (∀ x, C.eval (List.ofFn x) = !(f x)) → HasCircuitSize n f C.size)
  (positive : ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool => (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4)) 12)
  (multiple : ∀ C : Circuit, FanInTwo C → C.size ≤ 12 →
    2 ≤ C.gates.countP (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) →
    ¬ ∀ y : Fin 8 → Bool, C.eval (List.ofFn y) = !(y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4)) : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro gs pins hlen hfan _ _
  by_contra hbad
  let E := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
      x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let w := fun x : Fin 9 → Bool => (Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])
  have he (x : Fin 9 → Bool) :
      GateOp.not.eval (pins.map fun i => (w x).getD i.val false) = E x := by
    exact not_ne_iff.mp (fun h => hbad ⟨x,h⟩)
  cases pins with
  | nil =>
    have h := he (fun _ => false)
    change true = false at h
    contradiction
  | cons i rest =>
    let C : Circuit := ⟨gs,i.val⟩
    have hC (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 4 || x 6]) = !(E x) := by
      have h := he x
      change (!((w x).getD i.val false)) = E x at h
      change (w x).getD i.val false = !(E x)
      simpa only [Bool.not_not] using congrArg Bool.not h
    obtain ⟨D,hm,hs,heval⟩ := pin C hfan (by dsimp only; rw [hC,hC]; decide) (by dsimp only; rw [hC,hC]; decide)
    let F := fun y : Fin 8 → Bool => (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4)
    have hsize : D.size ≤ 12 := by
      change D.size + 1 ≤ gs.length at hs
      omega
    have hD (y : Fin 8 → Bool) : D.eval (List.ofFn y) = !(F y) := by
      change D.eval (List.ofFn y) = _
      rw [heval]; dsimp only; rw [hC]
      change (!(y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && false || false && y 0 ||
        y 0 && y 4 || y 1 && y 5 || y 2 && y 6 || y 3 && y 7 ||
        y 4 && y 6 || y 5 && y 7 || y 7 && y 4)) = _
      simp only [Bool.and_false,Bool.false_and,Bool.or_false] <;> rfl
    by_cases hn : D.gates.countP (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ 1
    · obtain ⟨D',hf',hs',he'⟩ := single 8 D F hm hn rfl rfl hD
      exact positive ⟨D',hf',hs'.trans hsize,he'⟩
    · exact multiple D hm hsize (by omega) hD
