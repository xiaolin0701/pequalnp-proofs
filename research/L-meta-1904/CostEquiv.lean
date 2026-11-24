import LeastCases
import PEqualNP.Outside.L_meta_1602

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace HonestCover1904

/-- On a graph without a proper four-cycle, the minimum-circuit witness in L-meta-1904 is
    equivalent to the edges-plus-minimum-cover lower bound for all monotone circuits. -/
theorem characterization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (T : Finset (Fin n)) (minimal : IsMinCover G T) :
    Goal G ↔ ∀ C : Circuit, Monotone2 C → Exact G C → G.edgeFinset.card+T.card-1 ≤ C.size := by
  constructor
  · rintro ⟨⟨gs,out⟩,ops,eval,least,honest⟩ C mono exactC
    obtain ⟨U,cover,charge⟩ := PEqualNP.Outside.L_meta_1602.pairCleanBound n G
      (fun a b c d ac bd ⟨ab,bc,cd,da⟩ => (square a b c d ab bc cd da).elim ac bd)
      gs out (fun g hg => by
        obtain ⟨z,len⟩ := ops g hg
        exact ⟨z,len⟩) eval (by
          intro i x _ andGate fired
          exact honest i.val (gs.get i) (List.getElem?_eq_getElem i.isLt) andGate x fired)
    have count := minimal.2 U cover
    have size := least C mono exactC
    change gs.length ≤ C.size at size
    omega
  · exact fromBudget G T minimal.1

end HonestCover1904
