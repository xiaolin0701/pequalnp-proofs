import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

-- Forests and individual cycles have minimum honest circuits. For the remaining graphs
-- the upper witness and the numerical lower bound use the same minimum vertex cover.
theorem PEqualNP.Outside.R_meta_1904_271
  (forestsOrCycles : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (G.IsAcyclic ∨ (5 ≤ n ∧ ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
        G.Adj u v ↔ ((e u).val+1)%n=(e v).val ∨ ((e v).val+1)%n=(e u).val)) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) ∧
      (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) → D.size ≤ C.size) ∧
      ∀ j g, D.gates[j]?=some g → g.op=PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n+j) false=true →
          ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
  (honestUpper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ¬(G.IsAcyclic ∨ (5 ≤ n ∧ ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
        G.Adj u v ↔ ((e u).val+1)%n=(e v).val ∨ ((e v).val+1)%n=(e u).val)) →
    ∃ T : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover G T ∧
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) ∧ D.size ≤ G.edgeFinset.card+T.card-1 ∧
        ∀ j g, D.gates[j]?=some g → g.op=PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n+j) false=true →
          ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
  (cyclicLower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
    ¬(G.IsAcyclic ∨ (5 ≤ n ∧ ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
        G.Adj u v ↔ ((e u).val+1)%n=(e v).val ∨ ((e v).val+1)%n=(e u).val)) →
    ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin n → Bool, C.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) → G.edgeFinset.card+T.card-1 ≤ C.size) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  classical
  intro n G inst triangle square
  by_cases simple : (G.IsAcyclic ∨ (5 ≤ n ∧ ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
        G.Adj u v ↔ ((e u).val+1)%n=(e v).val ∨ ((e v).val+1)%n=(e u).val))
  · exact forestsOrCycles n G simple
  · obtain ⟨T,minimal,D,mono,correct,cost,honest⟩ := honestUpper n G simple
    exact ⟨D,mono,correct,fun C hC hc =>
      cost.trans (cyclicLower n G triangle square simple T minimal C hC hc),honest⟩
