import PlaneFormulaTree
import FormulaRank

namespace PlaneFormula

open scoped Classical

def Factored {E : Type} (k : ℕ) (M : E → E → ℚ) : Prop :=
  ∃ left right : Fin k → E → ℚ, ∀ e f, (∑ i, left i e * right i f) = M e f

noncomputable def mask {E : Type} (M : E → E → ℚ) (X Y : Set E) (e f : E) : ℚ :=
  if e∈X ∧ f∈Y then M e f else 0

theorem factoredAdd {E : Type} {k h : ℕ} {M D : E → E → ℚ}
    (x : Factored k M) (y : Factored h D) : Factored (k+h) (fun e f => M e f+D e f) := by
  obtain ⟨A,B,hab⟩ := x
  obtain ⟨C,D,hcd⟩ := y
  refine ⟨Fin.addCases A C,Fin.addCases B D,?_⟩
  intro e f
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,hab,hcd]

-- A monotone formula splits the positive edges at OR, and the negative samples at AND.
-- The overlap matrix on each resulting leaf rectangle is constant down each column.
theorem formulaPartition {V E : Type} (target : E → E → Prop) [DecidableRel target]
    (pos neg : E → V → Bool)
    (leaf : ∀ e f v, pos e v=true → neg f v=false → (target e f ↔ pos f v=true))
    (T : Tree V) (X Y : Set E) (hx : ∀ e∈X, T.eval (pos e)=true)
    (hy : ∀ f∈Y, T.eval (neg f)=false) :
    Factored T.leaves (mask (fun e f => if target e f then 1 else 0) X Y) := by
  classical
  let M := fun (e f : E) => if target e f then (1 : ℚ) else 0
  change Factored T.leaves (mask M X Y)
  induction T generalizing X Y with
  | input v =>
    refine ⟨fun _ e => if e∈X then 1 else 0,
      fun _ f => if f∈Y ∧ pos f v=true then 1 else 0,?_⟩
    intro e f
    change (∑ _i : Fin 1, _) = _
    rw [Fin.sum_univ_one]
    by_cases row : e∈X
    · by_cases col : f∈Y
      · simp [row,col,mask,M,leaf e f v (hx e row) (hy f col)]
      · simp [row,col,mask]
    · simp [row,mask]
  | bot =>
    refine ⟨fun _ _ => 0,fun _ _ => 0,?_⟩
    intro e f
    have outside : e∉X := fun h => Bool.noConfusion (hx e h)
    simp [outside,mask]
  | join s t ihs iht =>
    let Xs : Set E := {e | e∈X ∧ s.eval (pos e)=true}
    let Xt : Set E := {e | e∈X ∧ s.eval (pos e)≠true}
    have left := ihs Xs Y (fun _ h => h.2) (fun f h => (Bool.or_eq_false_iff.mp (hy f h)).1)
    have right := iht Xt Y (fun e h => (Bool.or_eq_true_iff.mp (hx e h.1)).resolve_left h.2)
      (fun f h => (Bool.or_eq_false_iff.mp (hy f h)).2)
    have eq : (fun e f => mask M Xs Y e f+mask M Xt Y e f) = mask M X Y := by
      funext e f
      by_cases yes : s.eval (pos e)=true <;> simp [mask,Xs,Xt,yes]
    rw [←eq]
    exact factoredAdd left right
  | meet s t ihs iht =>
    let Ys : Set E := {f | f∈Y ∧ s.eval (neg f)=false}
    let Yt : Set E := {f | f∈Y ∧ s.eval (neg f)≠false}
    have left := ihs X Ys (fun e h => (Bool.and_eq_true_iff.mp (hx e h)).1) (fun _ h => h.2)
    have right := iht X Yt (fun e h => (Bool.and_eq_true_iff.mp (hx e h)).2)
      (fun f h => (Bool.and_eq_false_iff.mp (hy f h.1)).resolve_left h.2)
    have eq : (fun e f => mask M X Ys e f+mask M X Yt e f) = mask M X Y := by
      funext e f
      by_cases yes : s.eval (neg f)=false <;> simp [mask,Ys,Yt,yes]
    rw [←eq]
    exact factoredAdd left right

theorem formulaEdgeBound {V E : Type} [Fintype E] {N : ℕ} (p l : E → Fin N)
    (inj : Function.Injective fun e => (p e,l e)) (pos neg : E → V → Bool)
    (leaf : ∀ e f v, pos e v=true → neg f v=false → ((p e=p f ∨ l e=l f) ↔ pos f v=true))
    (T : Tree V) (hx : ∀ e, T.eval (pos e)=true) (hy : ∀ f, T.eval (neg f)=false) :
    Fintype.card E ≤ N+N+T.leaves := by
  classical
  obtain ⟨A,B,decomp⟩ := formulaPartition _ pos neg leaf T Set.univ Set.univ
    (fun e _ => hx e) (fun f _ => hy f)
  apply overlapBound p l inj A B
  simpa only [mask,Set.mem_univ,true_and,ite_true] using decomp

end PlaneFormula
