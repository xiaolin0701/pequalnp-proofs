import FormulaPartition

namespace PlaneFormula

-- Each column factor supplies one coordinate of a linear map. An injective
-- overlap matrix forces this intermediate map to be injective as well.
theorem card_le_factors {E : Type} [Fintype E] {k : ℕ} (R : E → E → Prop) [DecidableRel R]
    (h : Factored k (fun e f => if R e f then 1 else 0))
    (kernel : ∀ z : E → ℚ, (∀ e, (∑ f, if R e f then z f else 0) = 0) → ∀ e, z e = 0) :
    Fintype.card E ≤ k := by
  classical
  obtain ⟨left,right,split⟩ := h
  let A : Matrix E (Fin k) ℚ := fun e i => left i e
  let B : Matrix (Fin k) E ℚ := right
  let M : Matrix E E ℚ := fun e f => if R e f then 1 else 0
  have eq : A*B=M := by
    ext e f
    exact split e f
  have oneToOne : Function.Injective B.mulVecLin := by
    intro x y same
    have zeroB : B.mulVec (x-y)=0 := by
      change B.mulVecLin (x-y)=0
      rw [map_sub,same,sub_self]
    have zeroM : M.mulVec (x-y) = 0 := by
      rw [← eq,← Matrix.mulVec_mulVec,zeroB,Matrix.mulVec_zero]
    apply sub_eq_zero.mp
    funext e
    apply kernel (x-y) _ e
    intro a
    simpa [M,Matrix.mulVec,dotProduct,ite_mul] using congrFun zeroM a
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
    LinearMap.finrank_le_finrank_of_injective oneToOne

end PlaneFormula
