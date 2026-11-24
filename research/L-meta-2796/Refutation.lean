import FirstGateBound
import GraphSensitivity
import Plane256
import BipartitePlane
import PEqualNP.Defs.ReadK

namespace Meta2796

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical

theorem refutation : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → x1 % (2 : ℕ) = (0 : ℕ) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x10 ∧ (∀ (x11 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x10 (2 : ℕ) ∧ x10.size ≤ (2 : ℕ) * x2) := by
  classical
  intro h
  obtain ⟨I, hsym, hcol, hpair⟩ := plane256_symmetric
  obtain ⟨C, hC, hfun, _, hsize⟩ := h 256 65793 I (by decide) (by decide) hcol hpair (by decide)
  let G := sidesGraph I
  have hex : ExclusiveNeighbors G :=
    separating_neighbors I hsym (fun l => by rw [hcol]; decide) hpair
  have eqn : circuitFun (65793+65793) C = edgeFunction G := by
    funext x
    rw [hfun]
    unfold edgeFunction
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (graph_incidence I x).symm
  have bigger := first_gate_bound (n := 65793+65793) (by decide) (edgeFunction G)
    (graph_sensitive (by decide) hex) (graph_pair_sensitive hex) C hC eqn
  omega

end Meta2796
