import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Push

namespace Meta2130

open scoped Classical

variable {E J : Type*} [DecidableEq E] [DecidableEq J]

-- Select the gate columns touched by the chosen rows.
noncomputable def active (S : Finset E) (J₀ : Finset J) (R : E → J → Prop) : Finset J := by
  classical exact J₀.filter (fun j => ∃ e ∈ S, R e j)

noncomputable def fiber (S : Finset E) (R : E → J → Prop) (j : J) : Finset E := by
  classical exact S.filter (fun e => R e j)

-- A smallest violating set has one more row than the total gate budget.
-- Moreover, the union of the rows touched by any k of its active gates has
-- at least budget*k+1 members.
theorem dense_obstruction (S : Finset E) (J₀ : Finset J) (R : E → J → Prop) (b : ℕ)
    (h : b * (active S J₀ R).card < S.card) :
    ∃ T ⊆ S, T.card = b * (active T J₀ R).card + 1 ∧
      ∀ W ⊆ active T J₀ R, W.Nonempty →
        b * W.card < (T.filter (fun e => ∃ j ∈ W, R e j)).card := by
  classical
  let bad (T : Finset E) := T ⊆ S ∧ b * (active T J₀ R).card < T.card
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image
    (S.powerset.filter bad) Finset.card ⟨S, by simp [bad, h]⟩
  have hbad : bad T := (Finset.mem_filter.mp hT).2
  have hproper : ∀ U ⊂ T, U.card ≤ b * (active U J₀ R).card := by
    intro U hu
    by_contra! hU
    have hus := (Finset.ssubset_iff_subset_ne.mp hu).1.trans hbad.1
    have huF : U ∈ S.powerset.filter bad :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hus, hus, hU⟩
    exact (Nat.not_le_of_lt (Finset.card_lt_card hu)) (hmin _ huF)
  have hmono : ∀ {U V : Finset E}, U ⊆ V → active U J₀ R ⊆ active V J₀ R := by
    intro U V huv j hj
    obtain ⟨hj₀, e, he, hr⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hj₀, e, huv he, hr⟩
  have hn : T.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hbad.2)
  obtain ⟨e, he⟩ := hn
  have hd := hproper _ (Finset.erase_ssubset he)
  have hm := Nat.mul_le_mul_left b (Finset.card_le_card (hmono (T.erase_subset e)))
  have hcard := Finset.card_erase_add_one he
  refine ⟨T, hbad.1, by have := hbad.2; omega, ?_⟩
  intro W hw hW
  let A := T.filter (fun e => ∃ j ∈ W, R e j)
  have hAs : A ⊆ T := Finset.filter_subset _ _
  obtain ⟨j, hj⟩ := hW
  obtain ⟨_, x, hx, hr⟩ := Finset.mem_filter.mp (hw hj)
  have hxA : x ∈ A := Finset.mem_filter.mpr ⟨hx, j, hj, hr⟩
  have hpr : T \ A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, by
    intro heq
    have hxm : x ∈ T \ A := by rw [heq]; exact hx
    exact (Finset.mem_sdiff.mp hxm).2 hxA⟩
  have hsub : active (T \ A) J₀ R ⊆ active T J₀ R \ W := by
    intro i hi
    obtain ⟨_, y, hy, hyi⟩ := Finset.mem_filter.mp hi
    obtain ⟨hTy, hnAy⟩ := Finset.mem_sdiff.mp hy
    refine Finset.mem_sdiff.mpr ⟨hmono Finset.sdiff_subset hi, ?_⟩
    exact fun hiW => hnAy (Finset.mem_filter.mpr ⟨hTy, i, hiW, hyi⟩)
  have hl := (hproper _ hpr).trans (Nat.mul_le_mul_left b (Finset.card_le_card hsub))
  have hsplit := Finset.card_sdiff_add_card_eq_card hAs
  have hbudget := congrArg (b * ·) (Finset.card_sdiff_add_card_eq_card hw)
  rw [Nat.mul_add] at hbudget
  change b * W.card < A.card
  have := hbad.2
  omega

end Meta2130
