import Mathlib

namespace SparsePlaneIncidence

abbrev Input (N : ℕ) := (Fin N → Bool) × (Fin N → Bool)

def inputLE {N : ℕ} (u v : Input N) : Prop :=
  (∀ p, u.1 p = true → v.1 p = true) ∧ (∀ l, u.2 l = true → v.2 l = true)

def unit {N : ℕ} (a : Fin N) : Fin N → Bool := fun b => decide (b = a)

def outside {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (y : Fin N → Bool) :
    Fin N → Bool := fun p => decide (¬ ∃ l, I p l ∧ y l = true)

-- Union, copy, zero and arbitrary intersection preserve the order in both input vectors.
theorem wireMonotone {N m : ℕ} (W : ℕ → Set (Input N))
    (bits : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
    (gates : ∀ i < m, ∃ a < N+N+i, ∃ b < N+N+i,
      W (N+N+i) = W a ∪ W b ∨ W (N+N+i) = W a ∨ W (N+N+i) = ∅ ∨ W (N+N+i) = W a ∩ W b)
    (o : ℕ) (ho : o < N+N+m) {u v : Input N} (h : inputLE u v) :
    u ∈ W o → v ∈ W o := by
  induction o using Nat.strong_induction_on with
  | ind o ih =>
    by_cases p : o < N
    · let a : Fin N := ⟨o,p⟩
      rw [(bits a).1]
      exact h.1 a
    by_cases l : o < N+N
    · let a : Fin N := ⟨o-N, by omega⟩
      have idx : N+a.val=o := by dsimp [a]; omega
      rw [← idx,(bits a).2]
      exact h.2 a
    let i := o - (N+N)
    have idx : N+N+i=o := by dsimp [i]; omega
    obtain ⟨a, ha, b, hb, law⟩ := gates i (by omega)
    rw [idx] at ha hb law
    have A := ih a ha (by omega)
    have B := ih b hb (by omega)
    rcases law with law | law | law | law
    · rw [law]
      exact Or.imp A B
    · simpa only [law] using A
    · simp [law]
    · rw [law]
      exact fun ⟨ha,hb⟩ => ⟨A ha,B hb⟩

-- Testing only the maximal disjoint point set for each sparse line input gives
-- the exact Boolean answer throughout that entire slice of the cube.
theorem exactOnSparseLines {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (F : Set (Input N))
    (mono : ∀ {u v}, inputLE u v → u ∈ F → v ∈ F)
    (pos : ∀ p l, I p l → (unit p,unit l) ∈ F)
    (neg : ∀ y, Fintype.card {l : Fin N // y l = true} ≤ q → (outside I y,y) ∉ F)
    (x y : Fin N → Bool) (bound : Fintype.card {l : Fin N // y l = true} ≤ q) :
    (x,y) ∈ F ↔ ∃ p l, I p l ∧ x p = true ∧ y l = true := by
  constructor
  · intro accepted
    by_contra none
    apply neg y bound (mono (u := (x,y)) ?_ accepted)
    refine ⟨?_, fun _ hy => hy⟩
    intro p hp
    apply decide_eq_true
    rintro ⟨l, hpL, hy⟩
    exact none ⟨p,l,hpL,hp,hy⟩
  · rintro ⟨p,l,incident,hp,hl⟩
    apply mono (u := (unit p,unit l)) ?_ (pos p l incident)
    constructor
    · intro r hr
      exact (of_decide_eq_true hr : r = p) ▸ hp
    · intro s hs
      exact (of_decide_eq_true hs : s = l) ▸ hl

end SparsePlaneIncidence
