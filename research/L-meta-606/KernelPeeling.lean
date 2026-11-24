import Mathlib
import PEqualNP.Outside.L_meta_1708

namespace Meta606RangeTwo.Core

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical

noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.card G.edgeSet

theorem edgeFinset_card_eq {n : ℕ} (G : SimpleGraph (Fin n)) [Fintype G.edgeSet] :
    G.edgeFinset.card = edgeCount G := by
  rw [SimpleGraph.edgeFinset_card, edgeCount, Nat.card_eq_fintype_card]

def realizes {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop := by
  classical
  exact circuitFun n C = fun x : Fin n → Bool =>
    decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)

def minNonzeroDegree {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) : Prop := by
  classical exact ∀ v, G.degree v = 0 ∨ d ≤ G.degree v

theorem peel_to_core (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hm : Monotone2 C) (hf : realizes G C) :
    ∃ H : SimpleGraph (Fin n), ∃ D : Circuit, H ≤ G ∧ minNonzeroDegree d H ∧
      Monotone2 D ∧ realizes H D ∧ D.size ≤ C.size ∧
      edgeCount G + (d-1) * D.size ≤ edgeCount H + (d-1) * C.size := by
  classical
  generalize he : C.size = s
  induction s using Nat.strong_induction_on generalizing G C with
  | ind s ih =>
    by_cases hcore : minNonzeroDegree d G
    · exact ⟨G, C, le_rfl, hcore, hm, hf, he.le, by rw [he]⟩
    change ¬ ∀ v, G.degree v = 0 ∨ d ≤ G.degree v at hcore
    push Not at hcore
    obtain ⟨v, hv, hsmall⟩ := hcore
    obtain ⟨C', hm', hsize, hf'⟩ :=
      PEqualNP.Outside.L_meta_1708_aux.peel G v (Nat.pos_of_ne_zero hv) C hm hf
    have hfnext : realizes (G.deleteIncidenceSet v) C' := by
      unfold realizes
      funext x
      rw [congrFun hf' x]
      by_cases h : ∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true <;> simp [h]
    obtain ⟨H, D, hle, hcore', hD, hfun, hDS, hcount⟩ :=
      ih C'.size (by omega) (G.deleteIncidenceSet v) C' hm' hfnext rfl
    refine ⟨H, D, hle.trans (G.deleteIncidenceSet_le v), hcore', hD, hfun, by omega, ?_⟩
    have hbound : G.degree v ≤ G.edgeFinset.card := by
      rw [← G.card_incidenceFinset_eq_degree v]
      exact Finset.card_le_card (G.incidenceFinset_subset v)
    have hdel := G.card_edgeFinset_deleteIncidenceSet v
    simp only [edgeFinset_card_eq] at hdel hbound
    have hstep := Nat.mul_le_mul_left (d-1) (show C'.size+1 ≤ s by omega)
    rw [Nat.mul_succ] at hstep
    omega

/-- Any gate bound on high-degree cores transfers to all circuits, at the
larger of the core constant and the maximum number of edges removed per step. -/
theorem of_core_bound (d c : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hm : Monotone2 C) (hf : realizes G C)
    (hbound : ∀ (H : SimpleGraph (Fin n)) (D : Circuit), H ≤ G →
      minNonzeroDegree d H → Monotone2 D → realizes H D →
      edgeCount H ≤ c * (D.size + 1)) :
    edgeCount G ≤ max c (d-1) * (C.size+1) := by
  obtain ⟨H, D, hle, hcore, hmon, hfun, hsize, hcount⟩ := peel_to_core d G C hm hf
  have hsplit : (d-1)*C.size = (d-1)*D.size+(d-1)*(C.size-D.size) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hfirst : edgeCount G ≤ edgeCount H + (d-1)*(C.size-D.size) := by omega
  calc
    edgeCount G ≤ edgeCount H + (d-1)*(C.size-D.size) := hfirst
    _ ≤ max c (d-1)*(D.size+1) + max c (d-1)*(C.size-D.size) :=
      Nat.add_le_add ((hbound H D hle hcore hmon hfun).trans
        (Nat.mul_le_mul_right _ (le_max_left c (d-1))))
        (Nat.mul_le_mul_right _ (le_max_right c (d-1)))
    _ = max c (d-1)*(C.size+1) := by
      rw [← Nat.mul_add]
      congr 1
      omega

/-- A graph whose nonempty-edge subgraphs all contain a positive-degree vertex
of degree at most d has at most d times the number of gates. -/
theorem of_degenerate (d : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hm : Monotone2 C) (hf : realizes G C)
    (hdeg : ∀ H : SimpleGraph (Fin n), H ≤ G → edgeCount H ≠ 0 →
      ∃ v, 0 < H.degree v ∧ H.degree v ≤ d) :
    edgeCount G ≤ d * C.size := by
  classical
  obtain ⟨H, D, hle, hcore, _, _, _, hcount⟩ := peel_to_core (d+1) G C hm hf
  have hempty : edgeCount H = 0 := by
    by_contra h
    obtain ⟨v, hv, hsmall⟩ := hdeg H hle h
    have hlarge := hcore v
    omega
  simp only [Nat.add_sub_cancel, hempty, Nat.zero_add] at hcount
  omega

end Meta606RangeTwo.Core
