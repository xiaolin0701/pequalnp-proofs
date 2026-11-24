import Mathlib

namespace PlaneRankSamples

abbrev Input (N : ℕ) := (Fin N → Bool) × (Fin N → Bool)
abbrev Edge {N : ℕ} (I : Fin N → Fin N → Prop) := {e : Fin N × Fin N // I e.1 e.2}

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
def pos (e : Edge I) : Input N :=
  (fun p => decide (p = e.val.1), fun l => decide (l = e.val.2))
def neg (f : Edge I) : Input N :=
  (fun p => decide (I p f.val.2 ∧ p ≠ f.val.1),
   fun l => decide (I f.val.1 l ∧ l ≠ f.val.2))

def raw (z : Input N) (i : Fin (N+N)) : Bool :=
  Fin.addCases (motive := fun _ => Bool) z.1 z.2 i

theorem edgeCard {q : ℕ} (rows : ∀ p, (Finset.univ.filter (I p)).card = q+1) :
    Fintype.card (Edge I) = N*(q+1) := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype I), Fintype.card_sigma]
  simp [Fintype.card_subtype, rows]

theorem negativeSparse {q : ℕ} (rows : ∀ p, (Finset.univ.filter (I p)).card = q+1)
    (f : Edge I) : Fintype.card {l // (neg I f).2 l = true} = q := by
  rw [Fintype.card_subtype]
  have same : (Finset.univ.filter fun l => (neg I f).2 l = true) =
      (Finset.univ.filter (I f.val.1)).erase f.val.2 := by
    ext l
    simp [neg, and_comm]
  rw [same,Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.property⟩), rows]
  omega

theorem negativeIndependent
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) (f : Edge I)
    (p l : Fin N) (hp : (neg I f).1 p = true) (hl : (neg I f).2 l = true) : ¬ I p l := by
  obtain ⟨hpL,diffP⟩ := of_decide_eq_true hp
  obtain ⟨hPl,diffL⟩ := of_decide_eq_true hl
  intro incidence
  exact diffL ((unique p f.val.1 diffP).unique ⟨incidence,hPl⟩ ⟨hpL,f.property⟩)

theorem reject {q : ℕ} (F : Set (Input N)) (rows : ∀ p, (Finset.univ.filter (I p)).card = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (mono : ∀ u v : Input N, (∀ p, u.1 p = true → v.1 p = true) →
      (∀ l, u.2 l = true → v.2 l = true) → u ∈ F → v ∈ F)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
      ((fun p => decide (¬ ∃ l, I p l ∧ y l=true)),y) ∉ F) (f : Edge I) : neg I f ∉ F := by
  intro accepted
  apply no _ (negativeSparse I rows f).le
  apply mono (neg I f) ((fun p => decide (¬ ∃ l, I p l ∧ (neg I f).2 l = true)),(neg I f).2) ?_ (fun _ x => x) accepted
  intro p hp
  apply decide_eq_true
  rintro ⟨l,incidence,hl⟩
  exact negativeIndependent I unique f p l hp hl incidence

-- On a separated coordinate, sharing either endpoint is equivalent to that
-- coordinate being positive in the column's singleton assignment.
theorem separated (e f : Edge I) (v : Fin (N+N))
    (row : raw (pos I e) v = true) (col : raw (neg I f) v = false) :
    (e.val.1 = f.val.1 ∨ e.val.2 = f.val.2) ↔ raw (pos I f) v = true := by
  induction v using Fin.addCases with
  | left p =>
    simp [raw,pos,neg] at row col ⊢
    subst p
    constructor
    · rintro (h | h)
      · exact h
      · exact col (h ▸ e.property)
    · exact Or.inl
  | right l =>
    simp only [raw, Fin.addCases_right] at row col ⊢
    simp [pos,neg] at row col ⊢
    subst l
    constructor
    · rintro (h | h)
      · exact col (h ▸ e.property)
      · exact h
    · exact Or.inr

end PlaneRankSamples
