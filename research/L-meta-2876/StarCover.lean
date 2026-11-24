import Mathlib

namespace Heawood2876

/-- Left and right vertices are both numbered 0 through 6. -/
def adj (x y : Fin 7) : Bool :=
  (([1408, 8832, 12544, 6272, 11264, 5632, 2816] : List Nat).getD x.val 0).testBit (7+y.val)

def edges : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter (fun p => adj p.1 p.2)

def mate (x : Fin 7) : Fin 7 := ![0,2,1,5,6,3,4] x

set_option maxRecDepth 100000 in
theorem square_free : ∀ a b x y : Fin 7,
    adj a x → adj a y → adj b x → adj b y → a=b ∨ x=y := by decide

private theorem mate_inj : Function.Injective mate := by
  intro a b; exact (by decide : ∀ a b : Fin 7, mate a = mate b → a = b) a b

private theorem mate_edge : ∀ a, adj a (mate a) = true := by decide

private theorem edges_card : edges.card = 21 := by decide

/-- For any Heawood subgraph with a perfect matching, an independent
rectangle realization needs at least its edge count plus six gates. -/
theorem rectangle_cost_of_matching (H : Finset (Fin 7 × Fin 7)) (subgraph : H ⊆ edges)
    (m : Fin 7 → Fin 7) (inj_m : Function.Injective m) (in_matching : ∀ a, (a,m a) ∈ H)
    (k : Nat) (R S : Fin k → Finset (Fin 7))
    (nonempty : ∀ j, (R j).Nonempty ∧ (S j).Nonempty)
    (cover : Finset.univ.biUnion (fun j => (R j).product (S j)) = H) :
    H.card + 6 ≤ (∑ j, ((R j).card + (S j).card)) - 1 := by
  classical
  have incidence (j : Fin k) {a b : Fin 7} (ha : a ∈ R j) (hb : b ∈ S j) : adj a b := by
    have h : (a,b) ∈ Finset.univ.biUnion (fun j => (R j).product (S j)) :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_product.mpr ⟨ha,hb⟩⟩
    rw [cover] at h
    exact (Finset.mem_filter.mp (subgraph h)).2
  have one_side (j : Fin k) : (R j).card ≤ 1 ∨ (S j).card ≤ 1 := by
    by_contra! bad
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp bad.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp bad.2
    exact (square_free a b x y (incidence j ha hx) (incidence j ha hy)
      (incidence j hb hx) (incidence j hb hy)).elim hab hxy
  have side_count (j : Fin k) :
      ((R j).product (S j)).card + 1 = (R j).card + (S j).card := by
    rw [show ((R j).product (S j)).card = (R j).card * (S j).card from Finset.card_product _ _]
    have hr := (nonempty j).1.card_pos
    have hs := (nonempty j).2.card_pos
    rcases one_side j with h | h
    · rw [show (R j).card = 1 by omega]; omega
    · rw [show (S j).card = 1 by omega]; omega
  have hit (a : Fin 7) : ∃ j, a ∈ R j ∧ m a ∈ S j := by
    have hm := in_matching a
    rw [← cover] at hm
    obtain ⟨j,_,h⟩ := Finset.mem_biUnion.mp hm
    exact ⟨j, Finset.mem_product.mp h⟩
  choose f hf using hit
  have inj : Function.Injective f := by
    intro a b eq
    obtain ⟨ha,xa⟩ := hf a
    obtain ⟨hb,xb⟩ := hf b
    rw [← eq] at hb xb
    exact (square_free a b (m a) (m b) (incidence _ ha xa) (incidence _ ha xb)
      (incidence _ hb xa) (incidence _ hb xb)).elim id (fun h => inj_m h)
  have lower : 7 ≤ k := by simpa using Fintype.card_le_of_injective f inj
  have areas := Finset.card_biUnion_le (s := Finset.univ) (t := fun j => (R j).product (S j))
  rw [cover] at areas
  simp_rw [← side_count, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- The full incidence graph has 21 edges. A rectangle uses one OR tree per
side followed by an AND, and a final OR tree joins the rectangles. -/
theorem rectangle_cost (k : Nat) (R S : Fin k → Finset (Fin 7))
    (nonempty : ∀ j, (R j).Nonempty ∧ (S j).Nonempty)
    (cover : Finset.univ.biUnion (fun j => (R j).product (S j)) = edges) :
    27 ≤ (∑ j, ((R j).card + (S j).card)) - 1 := by
  have hm (a : Fin 7) : (a,mate a) ∈ edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _,mate_edge a⟩
  simpa only [edges_card] using rectangle_cost_of_matching edges (fun _ h => h) mate mate_inj hm k R S nonempty cover

def neighbors (U : Finset (Fin 7)) := Finset.univ.filter (fun b => ∃ a ∈ U, adj a b = true)
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem expand : ∀ U : Finset (Fin 7), U.Nonempty → U ≠ Finset.univ → U.card < (neighbors U).card := by decide
theorem seven_centers (left right : Finset (Fin 7)) (maxSize : left.card+right.card ≤ 7)
    (covers : ∀ a b, adj a b = true → a ∈ left ∨ b ∈ right) :
    (left = Finset.univ ∧ right = ∅) ∨ (left = ∅ ∧ right = Finset.univ) := by
  classical
  have nb : neighbors leftᶜ ⊆ right := by
    intro b hb
    obtain ⟨a,ha,he⟩ := (Finset.mem_filter.mp hb).2
    exact (covers _ _ he).resolve_left (Finset.mem_compl.mp ha)
  have sum : leftᶜ.card + left.card = 7 := by
    simp
  by_cases hl : left = Finset.univ
  · left
    refine ⟨hl,Finset.card_eq_zero.mp ?_⟩
    subst left
    simpa using maxSize
  have hc : leftᶜ.Nonempty := by
    by_contra! he
    apply hl
    simpa using congrArg (fun u : Finset (Fin 7) => uᶜ) he
  by_cases he : left = ∅
  · right
    refine ⟨he, ?_⟩
    subst left
    have cc : (∅ : Finset (Fin 7))ᶜ = Finset.univ := by simp
    rw [cc] at nb
    have full : neighbors Finset.univ = Finset.univ := by decide
    rw [full] at nb
    exact Finset.Subset.antisymm (Finset.subset_univ _) nb
  have hp : leftᶜ ≠ Finset.univ := by
    intro h
    apply he
    simpa using congrArg (fun u : Finset (Fin 7) => uᶜ) h
  have lt := expand _ hc hp
  have le := Finset.card_le_card nb
  omega

end Heawood2876
