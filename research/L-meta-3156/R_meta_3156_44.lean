import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_3156_44
    (sparse : ∀ (pre post : List Gate) (q : Gate) (o : ℕ),
      let C : Circuit := ⟨pre ++ q :: post, o⟩
      let D : Circuit := ⟨pre ++ ⟨.or, []⟩ :: post, o⟩
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))
      FanInTwo C → (∀ g ∈ pre ++ post, g.op ≠ .not) → circuitFun 9 C = f →
      ∀ (v : Fin 9),
        (fun y : Fin 8 → Bool => circuitFun 9 D (v.insertNth false y)) ≠
        (fun y : Fin 8 → Bool => f (v.insertNth false y)) →
        ∃ i j : Fin 9, i ≠ v ∧ j ≠ v ∧
          let x := fun u : Fin 9 => decide (u = i ∨ u = j)
          f x = true ∧ circuitFun 9 D x = false ∧
            let w := (⟨pre,o⟩ : Circuit).wires (List.ofFn x)
            q.op.eval (q.inputs.map (fun k => w.getD k false)) = true)
    (lower : ∀ (pre post : List Gate) (q : Gate) (o : ℕ),
      let C : Circuit := ⟨pre ++ q :: post, o⟩
      let D : Circuit := ⟨pre ++ ⟨.or, []⟩ :: post, o⟩
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))
      FanInTwo C → (∀ g ∈ pre ++ post, g.op ≠ .not) → q.op = .not → circuitFun 9 C = f →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) →
      (∀ v : Fin 9, v = 4 ∨ v = 6 ∨ v = 7 →
        ∃ i j : Fin 9, i ≠ v ∧ j ≠ v ∧
          let x := fun u : Fin 9 => decide (u = i ∨ u = j)
          f x = true ∧ circuitFun 9 D x = false ∧
            let w := (⟨pre,o⟩ : Circuit).wires (List.ofFn x)
            q.op.eval (q.inputs.map (fun k => w.getD k false)) = true) → 16 ≤ C.size) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ),   have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ x4 :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   have x7 : (Fin (9 : ℕ) → Bool) → Bool := PEqualNP.MetaComplexity.circuitFun (9 : ℕ) { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x6 → (∀ x9 ∈ x2 ++ x3, x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 = x1 → (∀ (x12 : Fin (9 : ℕ) → Bool), (x6.wires (List.ofFn x12)).getD (9 : ℕ) Bool.false = (x12 (0 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)))) → (∀ (x13 : Fin (9 : ℕ)), x13 = (4 : Fin (9 : ℕ)) ∨ x13 = (6 : Fin (9 : ℕ)) ∨ x13 = (7 : Fin (9 : ℕ)) → (fun (x15 : Fin (8 : ℕ) → Bool) => x7 (x13.insertNth Bool.false x15)) ≠ fun (x15 : Fin (8 : ℕ) → Bool) => x1 (x13.insertNth Bool.false x15)) → (16 : ℕ) ≤ x6.size := by
  dsimp only
  intro pre post q o hf hn hq he hw hd
  exact lower pre post q o hf hn hq he hw
    (fun v hv => sparse pre post q o hf hn he v (hd v hv))
