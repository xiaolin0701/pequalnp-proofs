import PEqualNP.Defs

namespace FanoDoubleRead
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.SingleLevel

private def Good (h d : ℕ) (v : Bool) : Prop :=
  (h = 0 → d ≤ 1) ∧ (h = 0 → 0 < d → v = true) ∧ (h ≤ 1 → 2 ≤ d → v = true)

private theorem goodAnd {h j d e : ℕ} {v w : Bool} (p : Good h d v) (q : Good j e w) :
    Good (max h j + 1) (d+e) (v && w) := by
  refine ⟨by omega,by omega,?_⟩
  intro dep high
  have hz : h = 0 := by omega
  have jz : j = 0 := by omega
  have h1 := p.1 hz
  have j1 := q.1 jz
  simp [p.2.1 hz (by omega),q.2.1 jz (by omega)]

private theorem goodOr {h j d e : ℕ} {v w : Bool} (p : Good h d v) (q : Good j e w) :
    Good (max h j) (max d e) (v || w) := by
  refine ⟨fun dep => max_le (p.1 (by omega)) (q.1 (by omega)),?_,?_⟩
  · intro dep high
    rw [Bool.or_eq_true]
    by_cases pos : 0 < d
    · exact Or.inl (p.2.1 (by omega) pos)
    · exact Or.inr (q.2.1 (by omega) (by omega))
  · intro dep high
    rw [Bool.or_eq_true]
    by_cases pos : 2 ≤ d
    · exact Or.inl (p.2.2 (by omega) pos)
    · exact Or.inr (q.2.2 (by omega) (by omega))

private def aligned (hs ds : List ℕ) (vs : List Bool) : Prop :=
  hs.length = ds.length ∧ hs.length = vs.length ∧
    ∀ i, Good (hs.getD i 0) (ds.getD i 0) (vs.getD i false)

private theorem snoc {α} (L : List α) (v d : α) (i : ℕ) :
    (L++[v]).getD i d = if i=L.length then v else L.getD i d := by
  split_ifs with hi
  · subst i; simp
  · by_cases hl : i<L.length
    · exact List.getD_append _ _ _ _ hl
    · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]

private theorem extend {hs ds : List ℕ} {vs : List Bool} {h d : ℕ} {v : Bool}
    (pa : aligned hs ds vs) (g : Good h d v) : aligned (hs++[h]) (ds++[d]) (vs++[v]) := by
  refine ⟨by simp [pa.1],by simp [pa.2.1],?_⟩
  intro i
  simp only [snoc,← pa.1,← pa.2.1]
  split <;> first | exact g | exact pa.2.2 i

private def hStep (w : List ℕ) (g : Gate) :=
  w ++ [(g.inputs.map fun i => w.getD i 0).foldr max 0 + andLevel g]
private def dStep (w : List ℕ) (g : Gate) := w ++ [g.lineDegree w]
private def vStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem steps (gs : List Gate) (typed : ∀ g ∈ gs, ∃ a b,
    g = ⟨.and,[a,b]⟩ ∨ g = ⟨.or,[a,b]⟩) (hs ds : List ℕ) (vs : List Bool)
    (prev : aligned hs ds vs) : aligned (gs.foldl hStep hs) (gs.foldl dStep ds) (gs.foldl vStep vs) := by
  induction gs generalizing hs ds vs with
  | nil => exact prev
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun t ht => typed t (by simp [ht]))
    obtain ⟨a,b,rfl | rfl⟩ := typed g (by simp)
    · apply extend prev
      simpa [hStep,dStep,vStep,andLevel,Gate.lineDegree,GateOp.eval] using goodAnd (prev.2.2 a) (prev.2.2 b)
    · apply extend prev
      simpa [hStep,dStep,vStep,andLevel,Gate.lineDegree,GateOp.eval] using goodOr (prev.2.2 a) (prev.2.2 b)

theorem singleton_acceptance_of_repetition (C : Circuit) (n t : ℕ)
    (typed : ∀ g ∈ C.gates, ∃ a b, g = ⟨.and,[a,b]⟩ ∨ g = ⟨.or,[a,b]⟩)
    (depth : (andDepths C n).getD C.output 0 ≤ 1)
    (degree : 2 ≤ C.lineDeg n {t}) :
    C.eval (List.ofFn (fun i : Fin n => decide (i.val=t))) = true := by
  let hs := List.replicate n 0
  let ds := (List.range n).map (fun i => if i ∈ ({t} : Finset ℕ) then 1 else 0)
  let vs := List.ofFn (fun i : Fin n => decide (i.val=t))
  have base : aligned hs ds vs := by
    refine ⟨by simp [hs,ds],by simp [hs,vs],?_⟩
    intro j
    by_cases hj : j<n
    · have h1 : j<hs.length := by simpa [hs] using hj
      have h2 : j<ds.length := by simpa [ds] using hj
      have h3 : j<vs.length := by simpa [vs] using hj
      rw [List.getD_eq_getElem _ _ h1,List.getD_eq_getElem _ _ h2,List.getD_eq_getElem _ _ h3]
      by_cases ht : j=t <;> simp [hs,ds,vs,Good,ht]
    · rw [List.getD_eq_default _ _ (by simpa [hs] using Nat.le_of_not_gt hj),
          List.getD_eq_default _ _ (by simpa [ds] using Nat.le_of_not_gt hj),
          List.getD_eq_default _ _ (by simpa [vs] using Nat.le_of_not_gt hj)]
      simp [Good]
  exact ((steps C.gates typed hs ds vs base).2.2 C.output).2.2 depth degree

/-- In particular, every syntactically repeated Fano input needs a path through
at least two binary AND gates, because every singleton assignment is negative. -/
theorem nested_and_of_repetition (C : Circuit) (n t : ℕ)
    (typed : ∀ g ∈ C.gates, ∃ a b, g = ⟨.and,[a,b]⟩ ∨ g = ⟨.or,[a,b]⟩)
    (reject : C.eval (List.ofFn (fun i : Fin n => decide (i.val=t))) = false)
    (degree : 2 ≤ C.lineDeg n {t}) : 2 ≤ (andDepths C n).getD C.output 0 := by
  by_contra! small
  have h := singleton_acceptance_of_repetition C n t typed (by omega) degree
  simp [reject] at h

end FanoDoubleRead
