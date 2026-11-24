import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Push
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Meta2796

open scoped Classical

def sidesAdj {N : ℕ} (I : Fin N → Fin N → Prop) (u v : Fin (N+N)) : Prop :=
  Fin.addCases (fun p => Fin.addCases (fun _ : Fin N => False) (fun l => I p l) v)
    (fun l => Fin.addCases (fun p => I p l) (fun _ : Fin N => False) v) u

def sidesGraph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) where
  Adj := sidesAdj I
  symm := by
    constructor
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;> simp only [sidesAdj,Fin.addCases_left,Fin.addCases_right] <;> tauto
  loopless := by
    constructor
    intro i
    induction i using Fin.addCases <;> simp only [sidesAdj,Fin.addCases_left,Fin.addCases_right] <;> tauto

theorem graph_incidence {N : ℕ} (I : Fin N → Fin N → Prop) (x : Fin (N+N) → Bool) :
    (∃ i j, (sidesGraph I).Adj i j ∧ x i = true ∧ x j = true) ↔
    ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] at h <;> first | contradiction | exact ⟨_,_,h,hi,hj⟩ | exact ⟨_,_,h,hj,hi⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨_,_,by simpa only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] using h,hp,hl⟩

theorem separating_neighbors {N : ℕ} (I : Fin N → Fin N → Prop)
    (sym : ∀ p l, I p l ↔ I l p)
    (many : ∀ l, 2 ≤ Fintype.card {p : Fin N // I p l})
    (uniq : ∀ p z, p ≠ z → ∃! l, I p l ∧ I z l) :
    ∀ i b : Fin (N+N), i ≠ b → ∃ c, c ≠ b ∧ (sidesGraph I).Adj i c ∧ ¬(sidesGraph I).Adj b c := by
  classical
  have other (p k : Fin N) : ∃ l, I p l ∧ l ≠ k := by
    by_contra! hn
    have hcard := many p
    rw [Fintype.card_subtype] at hcard
    have hc : (Finset.univ.filter (fun l => I l p)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro l hl m hm
      exact (hn l ((sym l p).mp (Finset.mem_filter.mp hl).2)).trans
        (hn m ((sym m p).mp (Finset.mem_filter.mp hm).2)).symm
    omega
  have excl (p z : Fin N) (hpz : p ≠ z) : ∃ l, I p l ∧ ¬I z l := by
    obtain ⟨k, _, hk⟩ := uniq p z hpz
    obtain ⟨l, hpl, hlk⟩ := other p k
    exact ⟨l,hpl,fun hzl => hlk (hk l ⟨hpl,hzl⟩)⟩
  have disj (x y : Fin N) : Fin.castAdd N x ≠ Fin.natAdd N y := by
    intro h
    have he := congrArg Fin.val h
    simp at he
    omega
  intro i b
  induction i using Fin.addCases with
  | left p =>
    induction b using Fin.addCases with
    | left z =>
      intro hp
      obtain ⟨l,hi,hz⟩ := excl p z (fun h => hp (h ▸ rfl))
      exact ⟨Fin.natAdd N l,(disj z l).symm,by simpa only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] using hi,
        by simpa only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] using hz⟩
    | right z =>
      intro _
      obtain ⟨l,hi,hz⟩ := other p z
      exact ⟨Fin.natAdd N l,fun h => hz (Fin.natAdd_injective _ _ h),
        by simpa only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] using hi,by simp only [sidesGraph,sidesAdj,Fin.addCases_right,not_false_eq_true]⟩
  | right p =>
    induction b using Fin.addCases with
    | left z =>
      intro _
      obtain ⟨l,hi,hz⟩ := other p z
      exact ⟨Fin.castAdd N l,fun h => hz (Fin.ext (congrArg (fun k : Fin (N+N) => k.val) h)),
        by simpa only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] using (sym p l).mp hi,by simp only [sidesGraph,sidesAdj,Fin.addCases_left,not_false_eq_true]⟩
    | right z =>
      intro hp
      obtain ⟨l,hi,hz⟩ := excl p z (fun h => hp (h ▸ rfl))
      exact ⟨Fin.castAdd N l,disj l z,by simpa only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] using (sym p l).mp hi,
        by simpa only [sidesGraph,sidesAdj,Fin.addCases_left,Fin.addCases_right] using fun h => hz ((sym l z).mp h)⟩

end Meta2796
