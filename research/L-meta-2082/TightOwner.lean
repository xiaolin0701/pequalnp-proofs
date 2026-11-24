import Mathlib

namespace PetersenStarCount

open scoped BigOperators

/-- Sum the local star bounds. Every edge belongs to its owner's star, so at
least half of the vertices must own an edge. -/
theorem tightOwner {V E K : Type*} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (N d : ℕ) (own : E → V) (label : K → V) (star : V → Finset E)
    (dv : ∀ v, (star v).card=d) (incident : ∀ e, e∈star (own e))
    (vcount : Fintype.card V=2*N) (ecount : Fintype.card E=N*d) (positive : 0<d)
    (localBound : ∀ v, (star v).card - (Finset.univ.filter fun e => own e=v).card +
        (if (Finset.univ.filter fun e => own e=v).Nonempty then 1 else 0) ≤
        (Finset.univ.filter fun k => label k=v).card) (limit : Fintype.card K ≤ N*d+N) (e : E) :
    (Finset.univ.filter (fun k => label k=own e)).card=1 := by
  classical
  let owned (v : V) := Finset.univ.filter fun e => own e=v
  let count (v : V) := (Finset.univ.filter fun k => label k=v).card
  let active (v : V) : ℕ := if (owned v).Nonempty then 1 else 0
  have cap (v : V) : (owned v).card ≤ d := by
    rw [← dv v]
    apply Finset.card_le_card
    intro e he
    have key : own e = v := (Finset.mem_filter.mp he).2
    simpa only [← key] using incident e
  have totalOwned : (∑ v, (owned v).card) = N*d := by
    rw [← ecount]
    simpa [owned] using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ own
  have totalCount : (∑ v, count v) = Fintype.card K := by
    simpa [count] using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ label
  have perActive (v : V) : (owned v).card ≤ active v*d := by
    by_cases h : (owned v).Nonempty
    · simpa [active,h] using cap v
    · simp [active,Finset.not_nonempty_iff_eq_empty.mp h]
  have half : N ≤ ∑ v, active v := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) fun v _ => perActive v
    rw [totalOwned,← Finset.sum_mul] at h
    exact Nat.le_of_mul_le_mul_right h positive
  have per (v : V) : d+active v ≤ count v+(owned v).card := by
    have h : d-(owned v).card+active v ≤ count v := by
      simpa only [dv,owned,count,active] using localBound v
    have hc := cap v
    omega
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) fun v _ => per v
  have degreeSum : (∑ _v : V, d) = N*d + N*d := by
    calc
      _ = Fintype.card V*d := by simp
      _ = _ := by rw [vcount]; ring
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,degreeSum,totalCount,totalOwned] at h
  have exactActive : (∑ v, active v)=N := by omega
  have exactOwned : ∀ v, (owned v).card = active v*d := by
    have eq : (∑ v, (owned v).card) = ∑ v, active v*d := by
      rw [← Finset.sum_mul,totalOwned,exactActive]
    exact fun v => (Finset.sum_eq_sum_iff_of_le (fun i _ => perActive i)).1 eq v (Finset.mem_univ _)
  have exactPer : ∀ v, d+active v = count v+(owned v).card := by
    have eq : (∑ v, (d+active v)) = ∑ v, (count v+(owned v).card) := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,degreeSum,totalCount,totalOwned,exactActive]
      omega
    exact fun v => (Finset.sum_eq_sum_iff_of_le (fun i _ => per i)).1 eq v (Finset.mem_univ _)
  have eh : (owned (own e)).Nonempty := ⟨e,by simp [owned]⟩
  have a : active (own e)=1 := by simp [active,eh]
  have full := exactOwned (own e)
  have sharp := exactPer (own e)
  rw [a,one_mul] at full
  change count (own e) = 1
  omega

end PetersenStarCount
