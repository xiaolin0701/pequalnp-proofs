import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin

namespace Meta606RangeTwo

open Finset

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def incidences : Finset (Fin N × Fin N) := univ.filter fun e => I e.1 e.2

def NoRectangle : Prop :=
  ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')

def removedByLine (l : Fin N) : Finset (Fin N × Fin N) :=
  (incidences I).filter fun e => I e.1 l

def removedByPoint (p : Fin N) : Finset (Fin N × Fin N) :=
  (incidences I).filter fun e => I p e.2

def residual (p l : Fin N) (x y : Fin N) : Prop :=
  I x y ∧ ¬ I x l ∧ ¬ I p y

local instance (p l : Fin N) : DecidableRel (residual I p l) :=
  fun x y => inferInstanceAs (Decidable (I x y ∧ ¬ I x l ∧ ¬ I p y))

theorem removedByLine_card (h : NoRectangle I) (l : Fin N) :
    (removedByLine I l).card ≤ 2 * N := by
  classical
  let A := (removedByLine I l).filter fun e => e.2 = l
  let B := (removedByLine I l).filter fun e => e.2 ≠ l
  have ha : A.card ≤ N := by
    have hle : A.card ≤ (univ : Finset (Fin N)).card := by
      apply card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _)
      intro x hx y hy hxy
      have hxl : x.2 = l := (mem_filter.mp hx).2
      have hyl : y.2 = l := (mem_filter.mp hy).2
      exact Prod.ext hxy (hxl.trans hyl.symm)
    simpa using hle
  have hb : B.card ≤ N := by
    have hle : B.card ≤ (univ : Finset (Fin N)).card := by
      apply card_le_card_of_injOn Prod.snd (fun _ _ => mem_univ _)
      intro x hx y hy hxy
      have hx' : I x.1 x.2 ∧ I x.1 l ∧ x.2 ≠ l := by
        simpa [B, removedByLine, incidences, and_assoc] using hx
      have hy' : I y.1 x.2 ∧ I y.1 l ∧ y.2 ≠ l := by
        have hh : I y.1 y.2 ∧ I y.1 l ∧ y.2 ≠ l := by
          simpa [B, removedByLine, incidences, and_assoc] using hy
        exact ⟨hxy ▸ hh.1, hh.2⟩
      apply Prod.ext _ hxy
      by_contra hne
      exact h x.1 y.1 x.2 l hne hx'.2.2 ⟨hx'.1, hx'.2.1, hy'.1, hy'.2.1⟩
    simpa using hle
  have hunion : removedByLine I l = A ∪ B := by
    ext e
    by_cases h : e.2 = l <;> simp [A, B, h]
  rw [hunion]
  have hbound := card_union_le A B
  omega

theorem removedByPoint_card (h : NoRectangle I) (p : Fin N) :
    (removedByPoint I p).card ≤ 2 * N := by
  classical
  let It := fun x y : Fin N => I y x
  have ht : NoRectangle It := by
    intro x y u v hxy huv hf
    exact h u v x y huv hxy ⟨hf.1, hf.2.2.1, hf.2.1, hf.2.2.2⟩
  apply le_trans _ (removedByLine_card It ht p)
  apply card_le_card_of_injOn Prod.swap
  · intro e he
    simpa [It, removedByLine, removedByPoint, incidences] using he
  · intro x _ y _ he
    exact Prod.swap_injective he

theorem loss_bound (h : NoRectangle I) (p l : Fin N) :
    (incidences I).card ≤ (incidences (residual I p l)).card + 4*N := by
  classical
  have hs : incidences I ⊆ incidences (residual I p l) ∪ removedByLine I l ∪ removedByPoint I p := by
    intro e he
    have hi := (mem_filter.mp he).2
    by_cases ha : I e.1 l
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨he, ha⟩))
    by_cases hb : I p e.2
    · exact mem_union_right _ (mem_filter.mpr ⟨he, hb⟩)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hi, ha, hb⟩))
  have h0 := card_le_card hs
  have h1 := card_union_le (incidences (residual I p l) ∪ removedByLine I l) (removedByPoint I p)
  have h2 := card_union_le (incidences (residual I p l)) (removedByLine I l)
  have h3 := removedByLine_card I h l
  have h4 := removedByPoint_card I h p
  omega

def hit (X Y : Finset (Fin N)) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, I x y

def pinPoints (p l : Fin N) (X : Finset (Fin N)) : Finset (Fin N) :=
  insert p (X.filter fun x => ¬ I x l)

def pinLines (p l : Fin N) (Y : Finset (Fin N)) : Finset (Fin N) :=
  insert l (Y.filter fun y => ¬ I p y)

theorem hit_after_pins (p l : Fin N) (hne : ¬ I p l) (X Y : Finset (Fin N)) :
    hit I (pinPoints I p l X) (pinLines I p l Y) ↔ hit (residual I p l) X Y := by
  classical
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    simp only [pinPoints, mem_insert, mem_filter] at hx
    simp only [pinLines, mem_insert, mem_filter] at hy
    rcases hx with rfl | ⟨hx, hxl⟩ <;> rcases hy with rfl | ⟨hy, hpy⟩
    · exact (hne hxy).elim
    · exact (hpy hxy).elim
    · exact (hxl hxy).elim
    · exact ⟨x, hx, y, hy, hxy, hxl, hpy⟩
  · rintro ⟨x, hx, y, hy, hxy, hxl, hpy⟩
    exact ⟨x, mem_insert_of_mem (mem_filter.mpr ⟨hx, hxl⟩), y,
      mem_insert_of_mem (mem_filter.mpr ⟨hy, hpy⟩), hxy⟩

theorem and_factor_after_pins
    (A B : Finset (Fin N) → Finset (Fin N) → Prop)
    (hmono : ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → A X Y → A X' Y')
    (houtput : ∀ X Y, (A X Y ∧ B X Y) ↔ hit I X Y)
    (p l : Fin N) (hnonedge : ¬ I p l) (haccept : A {p} {l})
    (X Y : Finset (Fin N)) :
    B (pinPoints I p l X) (pinLines I p l Y) ↔ hit (residual I p l) X Y := by
  have ha : A (pinPoints I p l X) (pinLines I p l Y) := by
    apply hmono {p} _ {l} _ _ _ haccept
    · exact singleton_subset_iff.mpr (mem_insert_self _ _)
    · exact singleton_subset_iff.mpr (mem_insert_self _ _)
  rw [← hit_after_pins I p l hnonedge, ← houtput]
  exact ⟨fun hb => ⟨ha, hb⟩, And.right⟩

end Meta606RangeTwo
