import Mathlib
import PEqualNP.Defs

-- Point degree by counting the other points on the pencil through p.
-- Adapted from the merged PEqualNP.Outside.L_meta_1955.lines_through.
namespace RectangleCost.Geometry

private theorem rectangleLinesThrough (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

end RectangleCost.Geometry

namespace RectangleCost

private theorem edge_count {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (cols : ∀ l, Fintype.card {p // I p l} = q+1) :
    (((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ).filter
      fun e : Fin N × Fin N => I e.1 e.2).card = N*(q+1) := by
  rw [Finset.card_filter, Finset.sum_product_right]
  have eq (l : Fin N) : (∑ p : Fin N, if I p l then 1 else 0) = q+1 := by
    simpa only [← Finset.card_filter, ← Fintype.card_subtype] using cols l
  simp [eq]

theorem lower {q N m : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1) (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (A B : Fin m → Finset (Fin N))
    (rect : ∀ i p, p ∈ A i → ∀ l, l ∈ B i → I p l)
    (cover : ∀ p l, I p l → ∃ i, p ∈ A i ∧ l ∈ B i) :
    N ≤ m ∧ N*(q+2) ≤ ∑ i, ((A i).card+(B i).card) := by
  classical
  have col (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q+1 := by
    simpa only [← Fintype.card_subtype] using cols l
  have row := Geometry.rectangleLinesThrough q N I hq hN col unique
  let area (i : Fin m) := (A i).card * (B i).card
  have one (i : Fin m) : (A i).card ≤ 1 ∨ (B i).card ≤ 1 := by
    by_contra! neg
    obtain ⟨p,hp,r,hr,pr⟩ := Finset.one_lt_card.mp neg.1
    obtain ⟨l,hl,k,hk,lk⟩ := Finset.one_lt_card.mp neg.2
    exact lk ((unique p r pr).unique ⟨rect i p hp l hl,rect i r hr l hl⟩
      ⟨rect i p hp k hk,rect i r hr k hk⟩)
  have bounds (i : Fin m) : area i ≤ q+1 ∧
      (q+2)*area i ≤ (q+1)*((A i).card+(B i).card) := by
    by_cases ha : (A i).Nonempty
    · by_cases hb : (B i).Nonempty
      · obtain ⟨p,hp⟩ := ha
        obtain ⟨l,hl⟩ := hb
        have ac := Finset.card_le_card (show A i ⊆ Finset.univ.filter (fun p => I p l) from
          fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,rect i p hp l hl⟩)
        have bc := Finset.card_le_card (show B i ⊆ Finset.univ.filter (fun l => I p l) from
          fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,rect i p hp l hl⟩)
        rw [col] at ac
        rw [row] at bc
        have ap := Finset.card_pos.mpr (show (A i).Nonempty from ⟨p,hp⟩)
        have bp := Finset.card_pos.mpr (show (B i).Nonempty from ⟨l,hl⟩)
        rcases one i with a | b
        · have ae : (A i).card = 1 := by omega
          simp only [area,ae,one_mul]
          exact ⟨bc,by nlinarith⟩
        · have be : (B i).card = 1 := by omega
          simp only [area,be,mul_one]
          exact ⟨ac,by nlinarith⟩
      · simp [area, Finset.not_nonempty_iff_eq_empty.mp hb]
    · simp [area, Finset.not_nonempty_iff_eq_empty.mp ha]
  have edge : N*(q+1) ≤ ∑ i, area i := by
    let edges := ((Finset.univ : Finset (Fin N)) ×ˢ Finset.univ).filter
      (fun e : Fin N × Fin N => I e.1 e.2)
    have sub : edges ⊆ Finset.univ.biUnion (fun i => A i ×ˢ B i) := by
      intro e he
      obtain ⟨i,ha,hb⟩ := cover e.1 e.2 (Finset.mem_filter.mp he).2
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_product.mpr ⟨ha,hb⟩⟩
    calc
      N*(q+1) = edges.card := (edge_count I cols).symm
      _ ≤ _ := Finset.card_le_card sub
      _ ≤ _ := Finset.card_biUnion_le
      _ = _ := by simp [area]
  constructor
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => (bounds i).1)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
    exact Nat.le_of_mul_le_mul_right (edge.trans h) (by omega)
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => (bounds i).2)
    simp only [← Finset.mul_sum] at h
    have net := (Nat.mul_le_mul_left (q+2) edge).trans h
    rw [show (q+2)*(N*(q+1)) = (q+1)*(N*(q+2)) by ring] at net
    exact Nat.le_of_mul_le_mul_left net (by omega)

-- The line-stars attain the minimum. Extra indices are empty.
theorem upper {q N m : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (cols : ∀ l, Fintype.card {p // I p l} = q+1) (slots : N ≤ m) :
    ∃ A B : Fin m → Finset (Fin N),
      (∀ i p, p ∈ A i → ∀ l, l ∈ B i → I p l) ∧
      (∀ p l, I p l → ∃ i, p ∈ A i ∧ l ∈ B i) ∧
      (∑ i, ((A i).card+(B i).card)) = N*(q+2) := by
  classical
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le slots
  let A : Fin (N+d) → Finset (Fin N) := Fin.addCases
    (fun l => Finset.univ.filter (fun p => I p l)) (fun _ => ∅)
  let B : Fin (N+d) → Finset (Fin N) := Fin.addCases (fun l => {l}) (fun _ => ∅)
  refine ⟨A,B,?_,?_,?_⟩
  · refine Fin.addCases (fun k p hp l hl => ?_) (fun k p hp => ?_)
    · simp [B] at hl
      subst l
      simpa [A] using hp
    · simp [A] at hp
  · intro p l h
    exact ⟨Fin.castAdd d l,by simpa [A] using h,by simp [B]⟩
  · rw [Fin.sum_univ_add]
    simp [A,B,← Fintype.card_subtype,cols,Nat.add_assoc]

theorem budget_iff {q N m : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N = q^2+q+1) (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) :
    (∃ A B : Fin m → Finset (Fin N),
      (∀ i p, p ∈ A i → ∀ l, l ∈ B i → I p l) ∧
      (∀ p l, I p l → ∃ i, p ∈ A i ∧ l ∈ B i) ∧
      (∑ i, ((A i).card+(B i).card)) ≤ 100*m+N) ↔ N*(q+1) ≤ 100*m := by
  constructor
  · rintro ⟨A,B,rect,cover,cost⟩
    have h := ((lower I (by omega) hN cols unique A B rect cover).2).trans cost
    nlinarith
  · intro bound
    have small := (Nat.mul_le_mul_left N (show 100 ≤ q+1 by omega)).trans bound
    rw [Nat.mul_comm N 100] at small
    have slots := Nat.le_of_mul_le_mul_left small (by decide)
    obtain ⟨A,B,rect,cover,cost⟩ := upper I cols slots
    refine ⟨A,B,rect,cover,?_⟩
    rw [cost]
    nlinarith

end RectangleCost
