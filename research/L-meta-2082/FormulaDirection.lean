import Mathlib
import PlaneFormulaTree

namespace PlaneFormula.Tree

variable {V : Type} [DecidableEq V]

def occurs : PlaneFormula.Tree V → V → ℕ
  | .input u, v => if u=v then 1 else 0
  | .bot, _ => 0
  | .join s t, v | .meet s t, v => occurs s v+occurs t v

def direction : PlaneFormula.Tree V → (V → Bool) → V → Bool
  | .input u, _, v => decide (u=v)
  | .bot, _, _ => false
  | .join s t, x, v => direction s x v || direction t x v
  | .meet s t, x, v => (s.eval x && direction t x v) || (direction s x v && t.eval x)

theorem direction_absent (T : PlaneFormula.Tree V) (x : V → Bool) (v : V)
    (h : T.occurs v=0) : T.direction x v=false := by
  induction T with
  | input u =>
    by_cases e : u=v <;> simp [occurs,direction,e] at *
  | bot => rfl
  | join s t ihs iht =>
    simp only [occurs,Nat.add_eq_zero_iff] at h
    simp [direction,ihs h.1,iht h.2]
  | meet s t ihs iht =>
    simp only [occurs,Nat.add_eq_zero_iff] at h
    simp [direction,ihs h.1,iht h.2]

/-- At a variable appearing at most once there is no quadratic term when it
is switched on. The AND clause uses the two unmodified singleton values. -/
theorem eval_activate (T : PlaneFormula.Tree V) (x : V → Bool) (v : V)
    (h : T.occurs v≤1) :
    T.eval (fun w => x w || decide (w=v)) = (T.eval x || T.direction x v) := by
  induction T with
  | input u => rfl
  | bot => rfl
  | join s t ihs iht =>
    change s.occurs v + t.occurs v≤1 at h
    simp only [eval,direction,ihs (by omega),iht (by omega)]
    cases s.eval x <;> cases t.eval x <;> cases s.direction x v <;> cases t.direction x v <;> rfl
  | meet s t ihs iht =>
    change s.occurs v + t.occurs v≤1 at h
    simp only [eval,direction,ihs (by omega),iht (by omega)]
    have unused : s.direction x v=false ∨ t.direction x v=false := by
      rcases (show s.occurs v=0 ∨ t.occurs v=0 by omega) with hs|ht
      · exact Or.inl (direction_absent s x v hs)
      · exact Or.inr (direction_absent t x v ht)
    rcases unused with e|e <;> rw [e] <;>
      cases s.eval x <;> cases t.eval x <;> cases s.direction x v <;> cases t.direction x v <;> rfl

theorem direction_of_gain (T : PlaneFormula.Tree V) (x : V → Bool) (v : V)
    (single : T.occurs v≤1) (off : T.eval x=false)
    (on : T.eval (fun w => x w || decide (w=v))=true) :
    T.direction x v=true := by simpa [eval_activate T x v single,off] using on

end PlaneFormula.Tree
