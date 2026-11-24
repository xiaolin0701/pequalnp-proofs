import UnfoldCircuit
import PrivateInputs
import CompressSignals

namespace PlaneFirstGate

open PlaneUnfold PlaneSignalCompression

def reads {k : ℕ} (op : Op (Fin k)) (a : ℕ) : Prop :=
  match op with
  | .empty => False
  | .copy x => a=x.val
  | .join x y | .meet x y => a=x.val ∨ a=y.val

theorem forward {Z : Type} {k : ℕ} (op : Op (Fin k)) (W : ℕ → Set Z) {x y : Z}
    (stable : ∀ i : Fin k, reads op i.val → x∈W i.val → y∈W i.val) :
    x∈op.onSets (fun i => W i.val) → y∈op.onSets (fun i => W i.val) := by
  cases op with
  | empty => exact id
  | copy u => exact stable u rfl
  | join u v => exact Or.imp (stable u (Or.inl rfl)) (stable v (Or.inr rfl))
  | meet u v => exact And.imp (stable u (Or.inl rfl)) (stable v (Or.inr rfl))

theorem rising {Z : Type} {k a : ℕ} (op : Op (Fin k)) (W : ℕ → Set Z)
    {x y : Z} (read : reads op a) (old : x∉W a) (newer : y∈W a) :
    x∈op.onSets (fun i => W i.val) → y∈op.onSets (fun i => W i.val) := by
  cases op with
  | empty => exact read.elim
  | copy u => subst_vars; exact fun _ => newer
  | join u v =>
    rcases read with rfl|rfl
    · exact fun _ => Or.inl newer
    · exact fun _ => Or.inr newer
  | meet u v =>
    rcases read with rfl|rfl
    · exact fun h => False.elim (old h.1)
    · exact fun h => False.elim (old h.2)

/-- A fresh first gate must use different input coordinates. -/
theorem firstPair {Z : Type} {n : ℕ} (op : Op (Fin (n+0))) (W : ℕ → Set Z)
    (law : W n=op.onSets (fun i => W i.val)) (fresh : Fresh W n) :
    ∃ a < n, ∃ b < n, a≠b ∧ reads op a ∧ reads op b := by
  cases op with
  | empty => exact False.elim (fresh.1 law)
  | copy u => exact False.elim (fresh.2 _ u.isLt law)
  | join u v =>
    have ne : u≠v := by
      rintro rfl
      exact fresh.2 _ u.isLt (by simpa [Op.onSets] using law)
    exact ⟨u.val,u.isLt,v.val,v.isLt,fun h => ne (Fin.ext h),Or.inl rfl,Or.inr rfl⟩
  | meet u v =>
    have ne : u≠v := by
      rintro rfl
      exact fresh.2 _ u.isLt (by simpa [Op.onSets] using law)
    exact ⟨u.val,u.isLt,v.val,v.isLt,fun h => ne (Fin.ext h),Or.inl rfl,Or.inr rfl⟩

theorem repeatedRead {Z : Type} {n m o : ℕ} (hn : 2≤n) (W : ℕ → Set Z)
    (ops : PlaneUnfold.Steps n) (law : realizes W m ops) (endBound : o < n+m) (ex : PlanePrivate.Exchange n o W)
    (fresh : Fresh W n) :
    ∃ a < n, ∃ i < m, 0 < i ∧ reads (ops 0) a ∧ reads (ops i) a := by
  have go : n≤o := by
    by_contra! raw
    obtain ⟨d,hd,ne⟩ : ∃ d < n, d≠o :=
      if e : o=0 then ⟨1,by omega,by omega⟩ else ⟨0,by omega,by omega⟩
    obtain ⟨x,hx,y,hy,miss,_,_⟩ := ex d hd o raw ne
    exact miss hx
  have positive : 0 < m := by omega
  obtain ⟨a,ha,b,hb,ne,ra,rb⟩ := firstPair (ops 0) W (law 0 positive) fresh
  refine ⟨a,ha,?_⟩
  by_contra! bad
  obtain ⟨x,hx,y,hy,no,yes,stable⟩ := ex a ha b hb ne
  have respects (w : ℕ) (hw : w < n+m) (diff : w≠a) : x∈W w → y∈W w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w < n
      · exact stable w raw diff
      by_cases base : w=n
      · subst w
        have ok := law 0 positive
        simp only [Nat.add_zero] at ok
        rw [ok]
        exact rising _ W rb no yes
      · let i := w-n
        have eq : n+i=w := by dsimp [i]; omega
        have hi : i < m := by omega
        have nz : 0 < i := by omega
        have notread : ¬reads (ops i) a := fun h => bad i hi nz ra h
        have rule := (congrArg W eq.symm).trans (law i hi)
        rw [rule]
        apply forward
        intro t read
        have earlier : t.val < w := lt_of_lt_of_eq t.isLt eq
        apply ih t.val earlier (by omega)
        exact fun e => notread (e ▸ read)
  exact hy (respects o endBound (by omega) hx)

end PlaneFirstGate
