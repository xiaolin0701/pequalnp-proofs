import LeastCases

namespace HonestCover1904

theorem solvedForestOrCycle : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (G.IsAcyclic ∨ (5 ≤ n ∧ ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
        G.Adj u v ↔ ((e u).val+1)%n=(e v).val ∨ ((e v).val+1)%n=(e u).val)) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) ∧
      (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) → D.size ≤ C.size) ∧
      ∀ j g, D.gates[j]?=some g → g.op=PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n+j) false=true →
          ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
  rintro n G inst (acyclic | ⟨hn,e,law⟩)
  · exact forests G acyclic
  · exact cycles hn e G law

theorem solvedHonestUpper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ¬(G.IsAcyclic ∨ (5 ≤ n ∧ ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
        G.Adj u v ↔ ((e u).val+1)%n=(e v).val ∨ ((e v).val+1)%n=(e u).val)) →
    ∃ T : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover G T ∧
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) ∧ D.size ≤ G.edgeFinset.card+T.card-1 ∧
        ∀ j g, D.gates[j]?=some g → g.op=PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n+j) false=true →
          ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
  intro n G inst _
  obtain ⟨T,minimal⟩ := leastCover G
  exact ⟨T,minimal,builder G T minimal.1⟩

end HonestCover1904
