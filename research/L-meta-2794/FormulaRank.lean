import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace PlaneFormula

-- A partition into k rank-one leaf rectangles bounds the number of incidences.
-- The two additional blocks record the point and line of every incidence.
theorem overlapBound {E : Type} [Fintype E] {N k : ℕ} (p l : E → Fin N)
    (inj : Function.Injective fun e => (p e,l e)) (left right : Fin k → E → ℚ)
    (decomp : ∀ e f, (∑ i, left i e * right i f) = (if p e=p f ∨ l e=l f then 1 else 0)) :
    Fintype.card E ≤ N+N+k := by
  classical
  let A : Matrix E ((Fin N ⊕ Fin N) ⊕ Fin k) ℚ := fun e => Sum.elim
    (Sum.elim (fun i => if i=p e then 1 else 0) (fun j => if j=l e then 1 else 0))
    (fun i => -(left i e))
  let B : Matrix ((Fin N ⊕ Fin N) ⊕ Fin k) E ℚ := Sum.elim
    (Sum.elim (fun i f => if i=p f then 1 else 0) (fun j f => if j=l f then 1 else 0)) right
  have ident : A*B=1 := by
    ext e f
    rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type, Matrix.one_apply]
    simp only [A,B,Sum.elim_inl,Sum.elim_inr,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true,neg_mul,Finset.sum_neg_distrib,decomp]
    by_cases he : e=f
    · subst f; simp
    · have apart : ¬(p e=p f ∧ l e=l f) := fun h => he (inj (Prod.ext h.1 h.2))
      by_cases a : p e=p f <;> by_cases b : l e=l f <;> simp_all
  have le := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  rw [ident, Matrix.rank_one] at le
  simpa using le

end PlaneFormula
