import PEqualNP.MetaComplexity.Helpers.Support
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Meta606RangeTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem incident_mem_output_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C =
      fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true))
    {v u : Fin n} (hvu : G.Adj v u) :
    v ∈ (suppsFrom C.gates (inputSupps n)).getD C.output ∅ := by
  classical
  by_contra hmiss
  let x : Fin n → Bool := fun i => decide (i = v ∨ i = u)
  let y : Fin n → Bool := fun i => decide (i = u)
  have hxy := (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output (by
    intro i hi
    have hne : i ≠ v := fun he => hmiss (he ▸ hi)
    simp [x, y, hne])
  change circuitFun n C x = circuitFun n C y at hxy
  rw [hfun] at hxy
  have hx : ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true :=
    ⟨v, u, hvu, by simp [x], by simp [x]⟩
  have hy : ¬ ∃ i j, G.Adj i j ∧ y i = true ∧ y j = true := by
    rintro ⟨i, j, hij, hi, hj⟩
    have ei : i = u := of_decide_eq_true hi
    have ej : j = u := of_decide_eq_true hj
    exact hij.ne (ei.trans ej.symm)
  simp [hx, hy] at hxy

theorem incident_card_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmono : Monotone2 C) (hfun : circuitFun n C =
      fun x : Fin n → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) :
    (Finset.univ.filter (fun v : Fin n => ∃ u, G.Adj v u)).card ≤ C.size + 1 := by
  classical
  have hsub : (Finset.univ.filter (fun v : Fin n => ∃ u, G.Adj v u)) ⊆
      (suppsFrom C.gates (inputSupps n)).getD C.output ∅ := by
    intro v hv
    obtain ⟨u, h⟩ := (Finset.mem_filter.mp hv).2
    exact incident_mem_output_support G C hfun h
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hmono g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    exact hop.elim Or.inl (fun h => Or.inr (Or.inl h))
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact (Finset.card_le_card hsub).trans hc

end Meta606RangeTwo
