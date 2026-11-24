import Mathlib
import PlaneFormulaTree

namespace PlaneLeafProtocol

open PlaneFormula

structure Tiles (V E : Type) (k : ℕ) where
  color : Fin k → V
  row : Fin k → Set E
  col : Fin k → Set E

noncomputable def weight {V E : Type} {k : ℕ} (a : Tiles V E k) (e f : E) : ℕ := by
  classical
  exact ∑ i, if e ∈ a.row i ∧ f ∈ a.col i then 1 else 0

def append {V E : Type} {k l : ℕ} (a : Tiles V E k) (b : Tiles V E l) : Tiles V E (k+l) :=
  ⟨Fin.addCases a.color b.color,Fin.addCases a.row b.row,Fin.addCases a.col b.col⟩

theorem weight_append {V E : Type} {k l : ℕ} (a : Tiles V E k) (b : Tiles V E l) (e f : E) :
    weight (append a b) e f = weight a e f + weight b e f := by
  classical
  simp [weight,append,Fin.sum_univ_add]

def Valid {V E : Type} {k : ℕ} (a : Tiles V E k) (pos neg : E → V → Bool) : Prop :=
  (∀ i e, e ∈ a.row i → pos e (a.color i)=true) ∧
  (∀ i f, f ∈ a.col i → neg f (a.color i)=false)

theorem valid_append {V E : Type} {k l : ℕ} {a : Tiles V E k} {b : Tiles V E l}
    {pos neg : E → V → Bool} (x : Valid a pos neg) (y : Valid b pos neg) :
    Valid (append a b) pos neg := by
  constructor <;> apply Fin.addCases
  · simpa [append] using x.1
  · simpa [append] using y.1
  · simpa [append] using x.2
  · simpa [append] using y.2

open scoped Classical in
theorem tiles {V E : Type} [Nonempty V] (pos neg : E → V → Bool) (T : PlaneFormula.Tree V)
    (X Y : Set E) (yes : ∀ e∈X, T.eval (pos e)=true) (no : ∀ f∈Y, T.eval (neg f)=false) :
    ∃ a : Tiles V E T.leaves, Valid a pos neg ∧
      ∀ e f, weight a e f = if e∈X ∧ f∈Y then 1 else 0 := by
  classical
  induction T generalizing X Y with
  | input v =>
    exact ⟨⟨fun _ => v,fun _ => X,fun _ => Y⟩,⟨fun _ => yes,fun _ => no⟩,
      fun e f => by
        change (∑ _i : Fin 1, if e∈X ∧ f∈Y then (1:ℕ) else 0) = _
        rw [Fin.sum_univ_one]⟩
  | bot =>
    have outside (e : E) : e∉X := fun h => Bool.noConfusion (yes e h)
    exact ⟨⟨fun _ => Classical.arbitrary V,fun _ => ∅,fun _ => ∅⟩,
      ⟨by simp,by simp⟩,fun e f => by simp [weight,outside]⟩
  | join s t ihs iht =>
    let Xs : Set E := {e | e∈X ∧ s.eval (pos e)=true}
    let Xt : Set E := {e | e∈X ∧ s.eval (pos e)≠true}
    obtain ⟨a,va,wa⟩ := ihs Xs Y (fun _ h => h.2) (fun f h => (Bool.or_eq_false_iff.mp (no f h)).1)
    obtain ⟨b,vb,wb⟩ := iht Xt Y (fun e h => (Bool.or_eq_true_iff.mp (yes e h.1)).resolve_left h.2)
      (fun f h => (Bool.or_eq_false_iff.mp (no f h)).2)
    refine ⟨append a b,valid_append va vb,fun e f => ?_⟩
    change weight (append a b) e f = _
    rw [weight_append,wa,wb]
    by_cases h : s.eval (pos e)=true <;> simp [Xs,Xt,h]
  | meet s t ihs iht =>
    let Ys : Set E := {f | f∈Y ∧ s.eval (neg f)=false}
    let Yt : Set E := {f | f∈Y ∧ s.eval (neg f)≠false}
    obtain ⟨a,va,wa⟩ := ihs X Ys (fun e h => (Bool.and_eq_true_iff.mp (yes e h)).1) (fun _ h => h.2)
    obtain ⟨b,vb,wb⟩ := iht X Yt (fun e h => (Bool.and_eq_true_iff.mp (yes e h)).2)
      (fun f h => (Bool.and_eq_false_iff.mp (no f h.1)).resolve_left h.2)
    refine ⟨append a b,valid_append va vb,fun e f => ?_⟩
    change weight (append a b) e f = _
    rw [weight_append,wa,wb]
    by_cases h : s.eval (neg f)=false <;> simp [Ys,Yt,h]

theorem oneWinner {V E : Type} {k : ℕ} (a : Tiles V E k) (e f : E) (h : weight a e f = 1) :
    ∃! i, e∈a.row i ∧ f∈a.col i := by
  classical
  change (∑ i : Fin k, if e∈a.row i ∧ f∈a.col i then 1 else 0) = 1 at h
  rw [← Finset.card_filter,Finset.card_eq_one] at h
  obtain ⟨i,hi⟩ := h
  have eq (j : Fin k) : (e∈a.row j ∧ f∈a.col j) ↔ j=i := by
    calc
      _ ↔ j∈Finset.univ.filter (fun j => e∈a.row j ∧ f∈a.col j) := by simp
      _ ↔ j∈({i} : Finset (Fin k)) := by rw [hi]
      _ ↔ _ := Finset.mem_singleton
  exact ⟨i,(eq i).mpr rfl,fun j => (eq j).mp⟩

end PlaneLeafProtocol
