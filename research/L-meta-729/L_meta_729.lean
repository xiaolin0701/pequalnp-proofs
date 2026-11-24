import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_729

def Walk {α : Type} (R : α → α → Prop) (m : ℕ) (u v : α) : Prop :=
  ∃ c : ℕ → α, c 0 = u ∧ c m = v ∧ ∀ i, i < m → R (c i) (c (i + 1))

lemma stationary {α : Type} (R : α → α → Prop) (u : α) : Walk R 0 u u :=
  ⟨fun _ => u, rfl, rfl, by omega⟩

lemma single {α : Type} {R : α → α → Prop} {u v : α} (e : R u v) : Walk R 1 u v := by
  refine ⟨fun i => if i = 0 then u else v, by simp, by simp, ?_⟩
  intro i hi
  have : i = 0 := by omega
  simpa [this] using e

lemma joinWalk {α : Type} {R : α → α → Prop} {m n : ℕ} {u v w : α}
    (p : Walk R m u v) (q : Walk R n v w) : Walk R (m + n) u w := by
  obtain ⟨a, a0, am, ha⟩ := p
  obtain ⟨b, b0, bn, hb⟩ := q
  by_cases hm : m = 0
  · subst m
    exact ⟨b, b0.trans (am.symm.trans a0), by simpa using bn, by simpa using hb⟩
  refine ⟨fun i => if i < m then a i else b (i - m), by simpa [Nat.pos_of_ne_zero hm] using a0,
    by simpa [show ¬ m + n < m by omega] using bn, ?_⟩
  intro i hi
  by_cases h : i + 1 < m
  · simpa [h, show i < m by omega] using ha i (by omega)
  by_cases h' : i < m
  · have hs : i + 1 = m := by omega
    simpa [h', hs, b0, am] using ha i h'
  · have hidx : i + 1 - m = (i - m) + 1 := by omega
    simpa [h, h', hidx] using hb (i - m) (by omega)

lemma dropFirst {α : Type} {R : α → α → Prop} {m : ℕ} {u v : α}
    (h : Walk R (m + 1) u v) : ∃ w, R u w ∧ Walk R m w v := by
  obtain ⟨c, c0, cm, hc⟩ := h
  refine ⟨c 1, by simpa [c0] using hc 0 (by omega), fun i => c (i + 1), rfl, cm, ?_⟩
  intro i hi
  exact hc (i + 1) (by omega)

lemma allClosedEven {α : Type} {D R : α → α → Prop}
    (sub : ∀ u v, R u v → D u v)
    (noOdd : ¬ ∃ (k : ℕ) (c : ℕ → α), c (2 * k + 1) = c 0 ∧
      ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1)))
    {m : ℕ} {u : α} (p : Walk R m u u) : m % 2 = 0 := by
  by_contra odd
  have h : m = 2 * (m / 2) + 1 := by omega
  obtain ⟨c, c0, cm, hc⟩ := p
  exact noOdd ⟨m / 2, c, h ▸ cm.trans c0.symm, fun i hi =>
    sub _ _ (hc i (by omega))⟩

-- A smallest forward-reachable set is closed under arcs inside A.
-- Every vertex in it can reach its root, so the parity of a return walk is unique.
lemma sinkPart {n : ℕ} (D : Fin n → Fin n → Prop) (A : Finset (Fin n)) (hne : A.Nonempty)
    (noOdd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧
      ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) :
    ∃ K : Set (Fin n), (∃ r ∈ A, r ∈ K) ∧ (∀ u ∈ K, u ∈ A) ∧
      (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
      ∀ u ∈ K, ∀ v ∈ A, D u v → v ∈ K ∨ ∃ w ∈ K, D v w := by
  classical
  let R := fun u v : Fin n => D u v ∧ v ∈ A
  let C := fun u => A.filter (fun v => ∃ m, Walk R m u v)
  have memC (u v) : v ∈ C u ↔ v ∈ A ∧ ∃ m, Walk R m u v := Finset.mem_filter
  have self (u) (hu : u ∈ A) : u ∈ C u := (memC u u).2 ⟨hu, 0, stationary R u⟩
  obtain ⟨r, hr, small⟩ := Finset.exists_min_image A (fun u => (C u).card) hne
  have back (u) (hu : u ∈ C r) : ∃ m, Walk R m u r := by
    obtain ⟨huA, k, pk⟩ := (memC r u).1 hu
    have incl : C u ⊆ C r := by
      intro v hv
      obtain ⟨hvA, l, pl⟩ := (memC u v).1 hv
      exact (memC r v).2 ⟨hvA, k + l, joinWalk pk pl⟩
    have eqC : C u = C r := Finset.eq_of_subset_of_card_le incl (small u huA)
    exact ((memC u r).1 (eqC.symm ▸ self r hr)).2
  let K : Set (Fin n) := {u | u ∈ C r ∧ ∃ m, m % 2 = 0 ∧ Walk R m u r}
  have extend (u v) (hu : u ∈ C r) (e : R u v) : v ∈ C r := by
    obtain ⟨_, m, p⟩ := (memC r u).1 hu
    exact (memC r v).2 ⟨e.2, m + 1, joinWalk p (single e)⟩
  have evenClosed := @allClosedEven (Fin n) D R (fun _ _ h => h.1) noOdd
  refine ⟨K, ⟨r, hr, self r hr, 0, rfl, stationary R r⟩,
    fun u hu => ((memC r u).1 hu.1).1, ?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨_, a, pa⟩ := (memC r u).1 hu.1
    obtain ⟨b, eb, pb⟩ := hu.2
    obtain ⟨c, ec, pc⟩ := hv.2
    have e : R u v := ⟨huv, ((memC r v).1 hv.1).1⟩
    have h₁ := evenClosed (joinWalk pa pb)
    have h₂ := evenClosed (joinWalk (joinWalk pa (single e)) pc)
    omega
  · intro u hu v hv e
    have hvC := extend u v hu.1 ⟨e, hv⟩
    obtain ⟨m, p⟩ := back v hvC
    by_cases even : m % 2 = 0
    · exact Or.inl ⟨hvC, m, even, p⟩
    · obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
      obtain ⟨w, ew, pw⟩ := dropFirst p
      exact Or.inr ⟨w, ⟨extend v w hvC ew, l, by omega, pw⟩, ew.1⟩

lemma kernelOn {n : ℕ} (D : Fin n → Fin n → Prop)
    (noOdd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧
      ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) (A : Finset (Fin n)) :
    ∃ K : Set (Fin n), (∀ u ∈ K, u ∈ A) ∧ (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
      ∀ v ∈ A, v ∉ K → ∃ k ∈ K, D v k := by
  classical
  induction A using Finset.strongInductionOn
  rename_i A ih
  by_cases ne : A.Nonempty
  · obtain ⟨K, ⟨r, hr, hrK⟩, inside, independent, absorb⟩ := sinkPart D A ne noOdd
    let B := A.filter (fun v => v ∉ K ∧ ¬ ∃ w ∈ K, D v w)
    have memB (v) : v ∈ B ↔ v ∈ A ∧ v ∉ K ∧ ¬ ∃ w ∈ K, D v w := Finset.mem_filter
    have lt : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.filter_subset .., fun eq => ((memB r).1 (eq.symm ▸ hr)).2.1 hrK⟩
    obtain ⟨J, inB, indJ, absJ⟩ := ih B lt
    refine ⟨K ∪ J, ?_, ?_, ?_⟩
    · intro u hu
      exact hu.elim (inside u) (fun h => ((memB u).1 (inB u h)).1)
    · intro u hu v hv e
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact independent u hu v hv e
      · obtain ⟨vA, vK, ve⟩ := (memB v).1 (inB v hv)
        exact (absorb u hu v vA e).elim vK ve
      · exact ((memB u).1 (inB u hu)).2.2 ⟨v, hv, e⟩
      · exact indJ u hu v hv e
    · intro v vA outside
      by_cases hit : ∃ k ∈ K, D v k
      · obtain ⟨k, hk, e⟩ := hit
        exact ⟨k, Or.inl hk, e⟩
      · have vB := (memB v).2 ⟨vA, fun hv => outside (Or.inl hv), hit⟩
        obtain ⟨k, hk, e⟩ := absJ v vB (fun hv => outside (Or.inr hv))
        exact ⟨k, Or.inr hk, e⟩
  · exact ⟨∅, by simp, by simp, fun v hv => (ne ⟨v, hv⟩).elim⟩

end PEqualNP.Outside.L_meta_729

theorem PEqualNP.Outside.L_meta_729 : ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
  (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
  (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
  ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro n D _ _ noOdd
  obtain ⟨K, _, ind, abs⟩ := PEqualNP.Outside.L_meta_729.kernelOn D noOdd Finset.univ
  exact ⟨K, ind, fun v => abs v (Finset.mem_univ v)⟩
