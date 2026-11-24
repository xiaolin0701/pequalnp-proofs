import LeafProtocol
import FormulaDirection

namespace PlaneLeafProtocol

def tally {V E : Type} [DecidableEq V] {k : ℕ} (a : Tiles V E k) (v : V) : ℕ :=
  ∑ i, if a.color i=v then 1 else 0

theorem tallyAppend {V E : Type} [DecidableEq V] {k j : ℕ} (a : Tiles V E k) (b : Tiles V E j) (v : V) :
    tally (append a b) v = tally a v+tally b v := by
  simp [tally, append, Fin.sum_univ_add]

open scoped Classical in
theorem tracked {V E : Type} [Nonempty V] [DecidableEq V] (pos neg : E → V → Bool) (T : PlaneFormula.Tree V)
    (X Y : Set E) (yes : ∀ e∈X, T.eval (pos e)=true) (no : ∀ f∈Y, T.eval (neg f)=false) :
    ∃ a : Tiles V E T.leaves, (∀ v, T.occurs v ≤ tally a v) ∧ Valid a pos neg ∧
      ∀ e f, weight a e f = if e∈X ∧ f∈Y then 1 else 0 := by
  classical
  induction T generalizing X Y with
  | input v =>
    exact ⟨⟨fun _ => v,fun _ => X,fun _ => Y⟩,(by
      intro w
      change (if v=w then 1 else 0) ≤ ∑ _ : Fin 1, (if v=w then 1 else 0)
      simp),⟨fun _ => yes,fun _ => no⟩,
      fun e f => by
        change (∑ _i : Fin 1, if e∈X ∧ f∈Y then (1:ℕ) else 0) = _
        rw [Fin.sum_univ_one]⟩
  | bot =>
    have outside (e : E) : e∉X := fun h => Bool.noConfusion (yes e h)
    exact ⟨⟨fun _ => Classical.arbitrary V,fun _ => ∅,fun _ => ∅⟩,
      (fun _ => Nat.zero_le _),⟨by simp,by simp⟩,fun e f => by simp [weight,outside]⟩
  | join s t ihs iht =>
    let Xs : Set E := {e | e∈X ∧ s.eval (pos e)=true}
    let Xt : Set E := {e | e∈X ∧ s.eval (pos e)≠true}
    obtain ⟨a,ca,va,wa⟩ := ihs Xs Y (fun _ h => h.2) (fun f h => (Bool.or_eq_false_iff.mp (no f h)).1)
    obtain ⟨b,cb,vb,wb⟩ := iht Xt Y (fun e h => (Bool.or_eq_true_iff.mp (yes e h.1)).resolve_left h.2)
      (fun f h => (Bool.or_eq_false_iff.mp (no f h)).2)
    refine ⟨append a b,(fun v => (Nat.add_le_add (ca v) (cb v)).trans_eq (tallyAppend a b v).symm),valid_append va vb,fun e f => ?_⟩
    change weight (append a b) e f = _
    rw [weight_append,wa,wb]
    by_cases h : s.eval (pos e)=true <;> simp [Xs,Xt,h]
  | meet s t ihs iht =>
    let Ys : Set E := {f | f∈Y ∧ s.eval (neg f)=false}
    let Yt : Set E := {f | f∈Y ∧ s.eval (neg f)≠false}
    obtain ⟨a,ca,va,wa⟩ := ihs X Ys (fun e h => (Bool.and_eq_true_iff.mp (yes e h)).1) (fun _ h => h.2)
    obtain ⟨b,cb,vb,wb⟩ := iht X Yt (fun e h => (Bool.and_eq_true_iff.mp (yes e h)).2)
      (fun f h => (Bool.and_eq_false_iff.mp (no f h.1)).resolve_left h.2)
    refine ⟨append a b,(fun v => (Nat.add_le_add (ca v) (cb v)).trans_eq (tallyAppend a b v).symm),valid_append va vb,fun e f => ?_⟩
    change weight (append a b) e f = _
    rw [weight_append,wa,wb]
    by_cases h : s.eval (neg f)=false <;> simp [Ys,Yt,h]

end PlaneLeafProtocol
