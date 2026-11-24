import StarCover

namespace Heawood2876

/-- The three columns partition the edges into perfect matchings. -/
def matching (t : Fin 3) : Fin 7 → Fin 7 :=
  ![![0,2,1,5,6,3,4], ![1,0,6,4,3,5,2], ![3,6,5,0,4,2,1]] t

private theorem matching_injective (t : Fin 3) : Function.Injective (matching t) := by
  exact (by decide : ∀ t a b, matching t a = matching t b → a = b) t

private theorem matching_adjacent : ∀ (t : Fin 3) (a : Fin 7), adj a (matching t a) = true := by decide

private theorem disjoint_at (a : Fin 7) : Function.Injective (fun t => matching t a) := by
  exact (by decide : ∀ a t u, matching t a = matching u a → t = u) a

/-- Deleting any two edges, including two occurrences of the same edge, leaves
a perfect matching. Each removed pair can damage at most one matching. -/
theorem matching_after_deleting (e f : Fin 7 × Fin 7) :
    ∃ m : Fin 7 → Fin 7, Function.Injective m ∧ ∀ a, (a, m a) ∈ edges \ {e,f} := by
  classical
  let bad (q : Fin 7 × Fin 7) : Fin 3 :=
    if h : ∃ t : Fin 3, matching t q.1 = q.2 then h.choose else 0
  have covered (q : Fin 7 × Fin 7) (t : Fin 3) (h : matching t q.1 = q.2) : t = bad q := by
    have he : ∃ t : Fin 3, matching t q.1 = q.2 := ⟨t,h⟩
    rw [show bad q = he.choose by simp [bad,he]]
    exact disjoint_at q.1 (h.trans he.choose_spec.symm)
  obtain ⟨t,te,tf⟩ := (by decide : ∀ u v : Fin 3, ∃ t, t ≠ u ∧ t ≠ v) (bad e) (bad f)
  refine ⟨matching t, matching_injective t, fun a => Finset.mem_sdiff.mpr ⟨?_,?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,matching_adjacent t a⟩
  · have skip (q : Fin 7 × Fin 7) (hq : t ≠ bad q) : (a,matching t a) ≠ q := by
      rintro rfl
      exact hq (covered _ _ rfl)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using not_or_intro (skip e te) (skip f tf)

/-- Independent rectangle covers remain expensive even after two probe edges
are removed. Counting the edges left also covers repeated or absent deletions. -/
theorem rectangle_cost_after_deleting (e f : Fin 7 × Fin 7) (k : Nat)
    (R S : Fin k → Finset (Fin 7)) (nonempty : ∀ j, (R j).Nonempty ∧ (S j).Nonempty)
    (cover : Finset.univ.biUnion (fun j => (R j).product (S j)) = edges \ {e,f}) :
    (edges \ {e,f}).card + 6 ≤ (∑ j, ((R j).card + (S j).card)) - 1 := by
  obtain ⟨m,hm,hedges⟩ := matching_after_deleting e f
  exact rectangle_cost_of_matching _ Finset.sdiff_subset m hm hedges k R S nonempty cover

end Heawood2876
