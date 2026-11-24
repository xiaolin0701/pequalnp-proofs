import Mathlib

namespace PlaneStarRank

-- On the incident edges at a vertex, every off-diagonal entry belongs to
-- that vertex. Some diagonal entries belong to the opposite endpoint.
private theorem principal {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K]
    (missing S : Finset E)
    (shape : (S ⊆ missing ∧ 2 ≤ S.card) ∨ ∃ p ∈ S, p ∉ missing ∧ ∀ i ∈ S, i ∉ missing → i=p)
    (left right : K → E → ℚ)
    (decomp : ∀ e f, (∑ k, left k e * right k f) = if e=f ∧ e∈missing then 0 else 1) :
    S.card ≤ Fintype.card K := by
  classical
  let A : Matrix S K ℚ := fun e k => left k e.val
  let B : Matrix K S ℚ := fun k f => right k f.val
  let M : Matrix S S ℚ := fun e f => if e=f ∧ e.val∈missing then 0 else 1
  have mul : A*B=M := by
    ext e f
    change (∑ k, left k e.val * right k f.val) = if e=f ∧ e.val∈missing then 0 else 1
    rw [decomp]
    by_cases eq : e=f
    · subst f
      simp
    · have ne : e.val≠f.val := fun h => eq (Subtype.ext h)
      simp [eq,ne]
  have ker (z : S → ℚ) (zero : M.mulVec z = 0) : z=0 := by
    let total := ∑ i, z i
    have row (i : S) : total = if i.val∈missing then z i else 0 := by
      have h := congrFun zero i
      change (∑ j, (if i=j ∧ i.val∈missing then (0:ℚ) else 1) * z j) = 0 at h
      by_cases hi : i.val∈missing
      · have calcSum : (∑ j, (if i=j ∧ i.val∈missing then (0:ℚ) else 1) * z j) =
            total-z i := by
          unfold total
          rw [show z i = ∑ j : S, if i=j then z j else 0 by simp, ←Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          by_cases eq : i=j
          · subst j
            simp [hi]
          · simp [hi,eq]
        rw [calcSum] at h
        simpa [hi] using sub_eq_zero.mp h
      · simpa [hi,total] using h
    rcases shape with ⟨all,degree⟩ | ⟨p,hp,keep,unique⟩
    · have const (i : S) : z i=total := by simpa [all i.property] using (row i).symm
      have eq : total = (S.card:ℚ)*total := by
        calc
          total = ∑ _i : S, total := Finset.sum_congr rfl (fun i _ => const i)
          _ = _ := by simp
      have big : (2:ℚ) ≤ S.card := by exact_mod_cast degree
      have tz : total=0 := by
        have prod : ((S.card:ℚ)-1)*total=0 := by linarith
        exact (mul_eq_zero.mp prod).resolve_left (by linarith)
      funext i
      exact (const i).trans tz
    · let a : S := ⟨p,hp⟩
      have tz : total=0 := by simpa [a,keep] using row a
      have off (i : S) (ne : i ≠ a) : z i=0 := by
        have hi : i.val∈missing := by
          by_contra h
          exact ne (Subtype.ext (unique _ i.property h))
        simpa [hi,tz] using (row i).symm
      have atA : total = z a := Finset.sum_eq_single a (fun i _ hi => off i hi) (by simp)
      funext i
      by_cases hi : i=a
      · exact hi ▸ (atA.symm.trans tz)
      · exact off i hi
  have inj : Function.Injective B.mulVecLin := by
    intro x y same
    have bz : B.mulVec (x-y)=0 := by
      change B.mulVecLin (x-y)=0
      rw [map_sub,same,sub_self]
    apply sub_eq_zero.mp
    apply ker
    rw [←mul,←Matrix.mulVec_mulVec,bz,Matrix.mulVec_zero]
  simpa using LinearMap.finrank_le_finrank_of_injective inj

theorem factorBound {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K]
    (missing : Finset E) (degree : 2 ≤ Fintype.card E) (left right : K → E → ℚ)
    (decomp : ∀ e f, (∑ k, left k e * right k f) = if e=f ∧ e∈missing then 0 else 1) :
    missing.card + (if missing=Finset.univ then 0 else 1) ≤ Fintype.card K := by
  classical
  by_cases full : missing=Finset.univ
  · have h := principal missing missing (.inl ⟨fun _ hi => hi, by simpa [full] using degree⟩)
        left right decomp
    simpa [full] using h
  · obtain ⟨p,hp⟩ : ∃ p, p∉missing := by
      by_contra! h
      exact full (Finset.eq_univ_of_forall h)
    have h := principal missing (insert p missing) (.inr ⟨p,Finset.mem_insert_self _ _,hp,
      fun _ hi hm => (Finset.mem_insert.mp hi).resolve_right hm⟩) left right decomp
    simpa [full,Finset.card_insert_of_notMem hp] using h

end PlaneStarRank
