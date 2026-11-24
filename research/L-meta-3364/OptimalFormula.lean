import StarWitness
import PlaneStarFormula

namespace PlaneStarFormula

open PlaneRankSamples

/-- The exact monotone formula size, counting leaves, for separating the
incident singleton samples from the independent point-line samples. -/
theorem minimumLeaves {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N=q^2+q+1)
    (rows : ∀ p, (Finset.univ.filter (I p)).card=q+1)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) :
    IsLeast {s : ℕ | ∃ t : PlaneFormula.Tree (Fin (N+N)), t.leaves=s ∧
      (∀ e : Edge I, t.eval (raw (pos I e))=true) ∧
      (∀ f : Edge I, t.eval (raw (neg I f))=false)} (N*(q+2)) := by
  obtain ⟨t,size,exactT⟩ := PlaneStarWitness.witness I (by omega : 0<N) cols
  constructor
  · refine ⟨t,size,?_,?_⟩
    · intro e
      apply (exactT _).mpr
      exact ⟨e.val.1,e.val.2,e.property,by simp [pos],by simp [pos]⟩
    · intro f
      cases h : t.eval (raw (neg I f)) with
      | false => rfl
      | true =>
        obtain ⟨p,l,inc,hp,hl⟩ := (exactT _).mp h
        exact False.elim (negativeIndependent I unique f p l hp hl inc)
  · rintro _ ⟨t,rfl,yes,no⟩
    have bound := leaves I hq hN rows cols t yes no
    calc
      N*(q+2) = N*(q+1)+N := by ring
      _ ≤ _ := bound

end PlaneStarFormula
