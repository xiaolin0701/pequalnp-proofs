import StarProgram
import PlaneFormulaTree
import RankSamples

namespace PlaneStarWitness

private def toFormula {n : ℕ} : PlaneStar.Tree n → PlaneFormula.Tree (Fin n)
  | .leaf i => .input i
  | .fork true s t => .meet (toFormula s) (toFormula t)
  | .fork false s t => .join (toFormula s) (toFormula t)

private theorem leafCount {n : ℕ} (t : PlaneStar.Tree n) :
    (toFormula t).leaves = t.count+1 := by
  induction t with
  | leaf => rfl
  | fork b s t ih jh =>
    cases b <;> simp [toFormula,PlaneFormula.Tree.leaves,PlaneStar.Tree.count,ih,jh] <;> omega

private theorem evaluates {n : ℕ} (t : PlaneStar.Tree n) (z : Fin n → Bool) :
    (toFormula t).eval z = t.value z := by
  induction t with
  | leaf => rfl
  | fork b s t ih jh =>
    cases b <;> simp [toFormula,PlaneFormula.Tree.eval,PlaneStar.Tree.value,ih,jh]

/-- The line-star formula separates precisely the samples used for the lower
bound, and in fact computes incidence on every input. -/
theorem witness {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (pos : 0<N)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card=q+1) :
    ∃ t : PlaneFormula.Tree (Fin (N+N)), t.leaves=N*(q+2) ∧
      ∀ z : PlaneRankSamples.Input N, t.eval (PlaneRankSamples.raw z)=true ↔
        ∃ p l, I p l ∧ z.1 p=true ∧ z.2 l=true := by
  have sizes (l : Fin N) : (PlaneStar.points I l).length=q+1 := by
    simpa [PlaneStar.points] using cols l
  have hn (l : Fin N) : PlaneStar.points I l ≠ [] := by
    intro empty
    have h := sizes l
    rw [empty] at h
    simp at h
  refine ⟨toFormula (PlaneStar.plane I hn pos),?_,?_⟩
  · rw [leafCount,← PlaneStar.Tree.size]
    exact PlaneStar.plane_count I hn pos sizes
  · intro z
    rw [evaluates, PlaneStar.plane_value]
    simp only [PlaneRankSamples.raw,Fin.addCases_left,Fin.addCases_right]

end PlaneStarWitness
