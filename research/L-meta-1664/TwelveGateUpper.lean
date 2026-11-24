import Mathlib
import PEqualNP.Defs

namespace PetersenDistanceTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 8 × Fin 8) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(1,5),(2,6),(3,7),(5,7)]

def circuit : Circuit :=
  ⟨[⟨.or,[2,0]⟩, ⟨.or,[3,0]⟩, ⟨.or,[5,3]⟩,
    ⟨.or,[6,3]⟩, ⟨.or,[8,5]⟩, ⟨.and,[9,4]⟩,
    ⟨.and,[10,7]⟩, ⟨.and,[11,2]⟩, ⟨.and,[12,1]⟩,
    ⟨.or,[14,13]⟩, ⟨.or,[16,15]⟩, ⟨.or,[18,17]⟩], 19⟩

theorem upper : Monotone2 circuit ∧ circuit.size = 12 ∧
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2) := by
  refine ⟨?_, (by decide), ?_⟩
  · intro g hg
    simp [circuit] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
  · intro x
    have h : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    simp [circuit,Circuit.eval,Circuit.wires,GateOp.eval,List.getD,edges]
    generalize h0 : x 0 = b0
    generalize h1 : x 1 = b1
    generalize h2 : x 2 = b2
    generalize h3 : x 3 = b3
    generalize h4 : x 4 = b4
    generalize h5 : x 5 = b5
    generalize h6 : x 6 = b6
    generalize h7 : x 7 = b7
    clear h0 h1 h2 h3 h4 h5 h6 h7
    revert b0 b1 b2 b3 b4 b5 b6 b7
    decide +kernel

end PetersenDistanceTwo
