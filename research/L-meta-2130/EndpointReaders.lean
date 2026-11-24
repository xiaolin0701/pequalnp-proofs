import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import PEqualNP.Defs.MetaComplexityLgpMono

namespace Meta2130

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LowMergeProof
open scoped Classical

theorem changed_reader (C : Circuit) (x y : List Bool) (n i : ℕ)
    (hx : x.length = n) (hy : y.length = n)
    (hin : ∀ k, k ≠ i → x.getD k false = y.getD k false) (ho : C.output ≠ i)
    (hval : C.eval x ≠ C.eval y) :
    ∃ j : Fin C.size, i ∈ C.gates[j.val].inputs ∧
      (C.wires x).getD (n + j.val) false ≠ (C.wires y).getD (n + j.val) false := by
  classical
  by_contra! hn
  have hall : ∀ k, k ≠ i → (C.wires x).getD k false = (C.wires y).getD k false := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hki
      by_cases hkn : k < n
      · rw [wires_input C x k (by omega), wires_input C y k (by omega)]
        exact hin k hki
      by_cases hkg : k < n + C.size
      · let j : Fin C.size := ⟨k - n, by omega⟩
        have he : n + j.val = k := by dsimp [j]; omega
        by_cases hmem : i ∈ C.gates[j.val].inputs
        · rw [← he]; exact hn j hmem
        have hGx := wires_gate C x j.val j.isLt
        have hGy := wires_gate C y j.val j.isLt
        rw [hx, he] at hGx
        rw [hy, he] at hGy
        rw [hGx, hGy]
        congr 1
        apply List.map_congr_left
        intro z hz
        unfold rd
        split
        · apply ih z (by assumption)
          exact fun hz' => hmem (hz' ▸ hz)
        · rfl
      · rw [List.getD_eq_default _ _ (by rw [wires_length, hx]; exact Nat.le_of_not_gt hkg),
          List.getD_eq_default _ _ (by rw [wires_length, hy]; exact Nat.le_of_not_gt hkg)]
  exact hval (hall _ ho)

theorem active_reader_of_sensitive {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (p : Fin n) (x y : Fin n → Bool) (hs : ∀ k, k ≠ p → x k = y k)
    (hyx : ∀ k, y k = true → x k = true) (ho : C.output ≠ p.val)
    (hx : circuitFun n C x = true) (hy : circuitFun n C y = false) :
    ∃ j : Fin C.size, p.val ∈ C.gates[j.val].inputs ∧
      (C.wires (List.replicate n false)).getD (n + j.val) false = false ∧
      (C.wires (List.ofFn x)).getD (n + j.val) false = true := by
  have hM : IsMonotoneCircuit C := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm _ hg).1
  have hle : LeL (List.ofFn y) (List.ofFn x) := by
    intro k hk
    by_cases h : k < n
    · simp [List.getD_eq_getElem?_getD, h] at hk ⊢
      exact hyx _ hk
    · simp [List.getD_eq_getElem?_getD, h] at hk
  have hb : LeL (List.replicate n false) (List.ofFn y) := by
    intro k h
    simp [List.getD_eq_getElem?_getD] at h
  obtain ⟨j, hr, hv⟩ := changed_reader C (List.ofFn x) (List.ofFn y) n p.val
    (by simp) (by simp) (by
      intro k hkp
      by_cases h : k < n
      · simp [List.getD_eq_getElem?_getD, h]
        apply hs
        exact fun e => hkp (congrArg Fin.val e)
      · simp [List.getD_eq_getElem?_getD, h]) ho (by
          change circuitFun n C x ≠ circuitFun n C y
          rw [hx, hy]; decide)
  have hinc := wires_mono C hM _ _ (by simp) hle (n + j.val)
  have hbase := wires_mono C hM _ _ (by simp) hb (n + j.val)
  refine ⟨j, hr, ?_, ?_⟩ <;> revert hv hinc hbase <;>
    cases (C.wires (List.ofFn x)).getD (n+j.val) false <;>
    cases (C.wires (List.ofFn y)).getD (n+j.val) false <;>
    cases (C.wires (List.replicate n false)).getD (n+j.val) false <;> simp


-- The maximum degree is computed in the selected sample family. The gate set K
-- only contains gates which switch on one of those samples.
theorem edge_count_of_readers {E : Type*} [DecidableEq E] (S : Finset E)
    (a b : E → ℕ) (C : Circuit) (hm : Monotone2 C) (K : Finset (Fin C.size)) (d : ℕ)
    (hdegree : ∀ v, (S.filter (fun e => a e = v)).card +
      (S.filter (fun e => b e = v)).card ≤ d)
    (hr : ∀ e ∈ S, ∀ v ∈ [a e, b e], ∃ j ∈ K, v ∈ C.gates[j.val].inputs) :
    S.card ≤ d * K.card := by
  classical
  let V := S.image a ∪ S.image b
  have ha : ∀ e ∈ S, a e ∈ V := fun e he =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem a he)
  have hb : ∀ e ∈ S, b e ∈ V := fun e he =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem b he)
  have hV : V ⊆ K.biUnion (fun j => C.gates[j.val].inputs.toFinset) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j, hj, h⟩ := hr e he (a e) (by simp)
      exact Finset.mem_biUnion.mpr ⟨j, hj, List.mem_toFinset.mpr h⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j, hj, h⟩ := hr e he (b e) (by simp)
      exact Finset.mem_biUnion.mpr ⟨j, hj, List.mem_toFinset.mpr h⟩
  have hcc : V.card ≤ K.card * 2 := calc
    V.card ≤ _ := Finset.card_le_card hV
    _ ≤ ∑ j ∈ K, C.gates[j.val].inputs.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ K, 2 := Finset.sum_le_sum (fun j _ =>
      (List.toFinset_card_le _).trans ((hm _ (List.getElem_mem _)).2))
    _ = K.card * 2 := by simp
  have hinc : S.card + S.card ≤ V.card * d := calc
    S.card + S.card = (∑ v ∈ V, (S.filter (fun e => a e = v)).card) +
      ∑ v ∈ V, (S.filter (fun e => b e = v)).card :=
        congrArg₂ (· + ·) (Finset.card_eq_sum_card_fiberwise ha) (Finset.card_eq_sum_card_fiberwise hb)
    _ = _ := (Finset.sum_add_distrib).symm
    _ ≤ ∑ _v ∈ V, d := Finset.sum_le_sum (fun v _ => hdegree v)
    _ = _ := by simp
  have := hinc.trans (Nat.mul_le_mul_right d hcc)
  nlinarith


-- This theorem already uses precisely the active-gate count of L-meta-2130.
-- Soundness on singleton inputs suffices for this bounded-degree case.
theorem selected_edge_bound {E : Type*} [DecidableEq E] {n : ℕ}
    (C : Circuit) (hm : Monotone2 C) (S : Finset E) (a b : E → Fin n) (d : ℕ)
    (hsingle : ∀ u : Fin n, circuitFun n C (fun k => decide (k = u)) = false)
    (hpair : ∀ e ∈ S, circuitFun n C (fun k => decide (k = a e ∨ k = b e)) = true)
    (hdegree : ∀ v : ℕ, (S.filter (fun e => (a e).val = v)).card +
      (S.filter (fun e => (b e).val = v)).card ≤ d) :
    S.card ≤ d * Fintype.card {j : Fin C.size //
      (C.wires (List.replicate n false)).getD (n + j.val) false = false ∧
      ∃ e ∈ S, (C.wires (List.ofFn (fun k : Fin n => decide (k = a e ∨ k = b e)))).getD
        (n + j.val) false = true} := by
  classical
  rw [Fintype.card_subtype]
  apply edge_count_of_readers S (fun e => (a e).val) (fun e => (b e).val) C hm _ d hdegree
  intro e he v hv
  have hout (i : Fin n) : C.output ≠ i.val := by
    intro eqO
    have h := hsingle i
    change (C.wires (List.ofFn (fun k : Fin n => decide (k = i)))).getD C.output false = false at h
    rw [eqO, wires_input _ _ _ (by simp)] at h
    simp [List.getD_eq_getElem?_getD, i.isLt] at h
  have applyReader (i j : Fin n) (hij : ∀ k, (k = a e ∨ k = b e) ↔ (k = i ∨ k = j)) :
      ∃ g, g ∈ Finset.univ.filter (fun t : Fin C.size =>
        (C.wires (List.replicate n false)).getD (n + t.val) false = false ∧
        ∃ f ∈ S, (C.wires (List.ofFn (fun k : Fin n => decide (k = a f ∨ k = b f)))).getD
          (n + t.val) false = true) ∧ i.val ∈ C.gates[g.val].inputs := by
    obtain ⟨g, hg, hb, hx⟩ := active_reader_of_sensitive C hm i
      (fun k => decide (k = a e ∨ k = b e)) (fun k => decide (k = j))
      (by intro k hk; simp [hij, hk])
      (by intro k hk; simpa [hij] using (Or.inr (of_decide_eq_true hk) : k = i ∨ k = j))
      (hout i) (hpair e he) (hsingle j)
    exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, e, he, hx⟩, hg⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact applyReader (a e) (b e) (fun _ => Iff.rfl)
  · exact applyReader (b e) (a e) (fun _ => or_comm)


-- The specialized conclusion has exactly the RHS appearing in the posted problem.
theorem selected_incidence_bound (q N : ℕ) (hq : 1 ≤ q)
    (I : Fin N → Fin N → Prop) (C : Circuit) (hm : Monotone2 C)
    (hsound : ∀ x : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
        circuitFun (N + N) C x = false)
    (T : Fin N → Finset (Fin N)) (d : ℕ)
    (hpair : ∀ l p, p ∈ T l → circuitFun (N + N) C
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true)
    (hcol : ∀ l, (T l).card ≤ d)
    (hrow : ∀ p, (Finset.univ.filter (fun l => p ∈ T l)).card ≤ d) :
    ∑ l, (T l).card ≤ d * Fintype.card {j : Fin C.size //
      (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
      ∃ l, ∃ p ∈ T l, (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
          (N + N + j.val) false = true} := by
  classical
  let S : Finset ((_:Fin N) × Fin N) := Finset.univ.sigma T
  let a (e : (_:Fin N) × Fin N) := Fin.castAdd N e.2
  let b (e : (_:Fin N) × Fin N) := Fin.natAdd N e.1
  have single (u : Fin (N + N)) : circuitFun _ C (fun k => decide (k = u)) = false := by
    apply hsound
    · rw [Fintype.card_subtype]
      apply le_trans _ hq
      apply Finset.card_le_one.mpr
      intro l hl k hk
      have h1 : Fin.natAdd N l = u := of_decide_eq_true (Finset.mem_filter.mp hl).2
      have h2 : Fin.natAdd N k = u := of_decide_eq_true (Finset.mem_filter.mp hk).2
      exact Fin.natAdd_injective _ _ (h1.trans h2.symm)
    · rintro ⟨p, l, -, hp, hl⟩
      have h := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
      simp at h
      omega
  have deg (v : ℕ) : (S.filter (fun e => (a e).val = v)).card +
      (S.filter (fun e => (b e).val = v)).card ≤ d := by
    by_cases hv : v < N
    · have hzero : S.filter (fun e => (b e).val = v) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro e _
        change N + e.1.val ≠ v
        omega
      rw [hzero, Finset.card_empty, add_zero]
      apply le_trans _ (hrow ⟨v, hv⟩)
      apply Finset.card_le_card_of_injOn Sigma.fst
      · intro e he
        obtain ⟨heS, hev⟩ := Finset.mem_filter.mp he
        have h2 : e.2 = ⟨v, hv⟩ := Fin.ext hev
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 ▸ (Finset.mem_sigma.mp heS).2⟩
      · rintro ⟨l,p⟩ he ⟨k,z⟩ hf hl
        change l = k at hl
        have hp : p.val = v := (Finset.mem_filter.mp he).2
        have hz : z.val = v := (Finset.mem_filter.mp hf).2
        cases hl
        rw [show p = z from Fin.ext (hp.trans hz.symm)]
    · have hzero : S.filter (fun e => (a e).val = v) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro e _
        change e.2.val ≠ v
        omega
      rw [hzero, Finset.card_empty, zero_add]
      by_cases h2 : v < N+N
      · let l : Fin N := ⟨v-N, by omega⟩
        apply le_trans _ (hcol l)
        apply Finset.card_le_card_of_injOn (fun e => e.2)
        · intro e he
          obtain ⟨heS, hev⟩ := Finset.mem_filter.mp he
          have hl : e.1 = l := by
            apply Fin.ext
            change N + e.1.val = v at hev
            dsimp [l]; omega
          simpa [hl] using (Finset.mem_sigma.mp heS).2
        · rintro ⟨k,p⟩ he ⟨w,z⟩ hf heq
          change p = z at heq
          have hk : N+k.val=v := (Finset.mem_filter.mp he).2
          have hw : N+w.val=v := (Finset.mem_filter.mp hf).2
          rw [show k = w from Fin.ext (by omega), heq]
      · have hz : S.filter (fun e => (b e).val = v) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro e _
          change N + e.1.val ≠ v
          omega
        simp [hz]
  have hh := selected_edge_bound C hm S a b d single
    (fun e he => hpair e.1 e.2 (Finset.mem_sigma.mp he).2) deg
  simpa [S, a, b, Sigma.exists, and_assoc] using hh


-- Counting the other points on the pencil through p from the one-sided plane axioms.
theorem pencil_bound (q N : ℕ) (hpos : 0 < q) (hN : N = q^2 + q + 1)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcol : ∀ l, Fintype.card {z : Fin N // I z l} = q + 1)
    (huniq : ∀ u v : Fin N, u ≠ v → ∃! l : Fin N, I u l ∧ I v l) (p : Fin N) :
    (Finset.univ.filter (I p)).card ≤ q + 1 := by
  classical
  let L := Finset.univ.filter (I p)
  let U (l : Fin N) := (Finset.univ.filter (fun v => I v l)).erase p
  have hsz (l : Fin N) (hl : l ∈ L) : (U l).card = q := by
    have hp : p ∈ Finset.univ.filter (fun v => I v l) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
    have hc := hcol l
    rw [Fintype.card_subtype] at hc
    exact (Finset.card_erase_of_mem hp).trans (by omega)
  have dis : (L : Set (Fin N)).PairwiseDisjoint U := by
    intro l hl k hk hne
    apply Finset.disjoint_left.mpr
    intro z hzl hzk
    obtain ⟨hz, hlz⟩ := Finset.mem_erase.mp hzl
    obtain ⟨_, hkz⟩ := Finset.mem_erase.mp hzk
    obtain ⟨w, -, hw⟩ := huniq p z hz.symm
    exact hne ((hw l ⟨(Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp hlz).2⟩).trans
      (hw k ⟨(Finset.mem_filter.mp hk).2, (Finset.mem_filter.mp hkz).2⟩).symm)
  have hsub : L.biUnion U ⊆ Finset.univ.erase p := by
    intro z hz
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hl).1, Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_biUnion dis, Finset.sum_congr rfl (fun l hl => hsz l hl)] at hle
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ p),
    Finset.card_univ, Fintype.card_fin] at hle
  change L.card ≤ q + 1
  by_contra! h
  have hh := Nat.mul_le_mul_right q (show q+2 ≤ L.card by omega)
  have hn : N - 1 = q*q + q := by rw [hN, pow_two]; omega
  rw [hn] at hle
  nlinarith

end Meta2130




