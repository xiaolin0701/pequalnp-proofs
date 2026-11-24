import Mathlib
import PEqualNP.Defs

namespace ThetaThreeFourFour

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 10 × Fin 10) :=
  [(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1), (0, 7), (7, 8), (8, 9), (9, 1)]

def circuit : Circuit :=
  ⟨[⟨.or,[2,4]⟩, ⟨.or,[10,7]⟩, ⟨.and,[0,11]⟩,
    ⟨.or,[3,6]⟩, ⟨.or,[13,9]⟩, ⟨.and,[1,14]⟩,
    ⟨.and,[2,3]⟩, ⟨.or,[4,6]⟩, ⟨.and,[5,17]⟩,
    ⟨.or,[7,9]⟩, ⟨.and,[8,19]⟩, ⟨.or,[12,15]⟩,
    ⟨.or,[21,16]⟩, ⟨.or,[22,18]⟩, ⟨.or,[23,20]⟩], 24⟩

theorem upper : HasCircuitSize 10 (fun x => edges.any (fun e => x e.1 && x e.2)) 15 := by
  refine ⟨circuit, ?_, (by decide), ?_⟩
  · intro g hg
    simp [circuit] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
  · intro x
    have h : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9] := by
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
    generalize h8 : x 8 = b8
    generalize h9 : x 9 = b9
    clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
    decide +kernel

end ThetaThreeFourFour
