import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Fuel stability follows the checked proof of L-meta-563.
private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]
private def leftBit {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)

private lemma transferGate {n : ℕ} (C : AndCountCircuit n) (U V W : Finset (Fin n))
    (hw : W ⊆ U ∪ V) (codes : leftBit C U = leftBit C V) (i : Fin C.size) :
    C.gateVal W i = true → C.gateVal U i = true ∨ C.gateVal V i = true := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have side (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
        sideTrue W B F i (C.gateVal W) = true →
          sideTrue U B F i (C.gateVal U) = true ∨ sideTrue V B F i (C.gateVal V) = true := by
      simp only [sideTrue, decide_eq_true_eq]
      rintro (⟨v, hb, hv⟩ | ⟨j, hf, hj, hv⟩)
      · rcases Finset.mem_union.mp (hw hv) with h | h
        · exact Or.inl (Or.inl ⟨v,hb,h⟩)
        · exact Or.inr (Or.inl ⟨v,hb,h⟩)
      · rcases ih j hj hv with h | h
        · exact Or.inl (Or.inr ⟨j,hf,hj,h⟩)
        · exact Or.inr (Or.inr ⟨j,hf,hj,h⟩)
    rw [gateVal_unfold C W i, gateVal_unfold C U i, gateVal_unfold C V i]
    simp only [Bool.and_eq_true]
    rintro ⟨hl, hr⟩
    have e := congrFun codes i
    unfold leftBit at e
    rcases side _ _ hl with h | h <;> rcases side _ _ hr with t | t
    · exact Or.inl ⟨h,t⟩
    · exact Or.inr ⟨e.symm.trans h,t⟩
    · exact Or.inl ⟨e.trans h,t⟩
    · exact Or.inr ⟨h,t⟩

private lemma countRows {n m : ℕ} (C : AndCountCircuit n) (rows : Fin m → Finset (Fin n))
    (distinct : ∀ i j, i ≠ j → ∃ w ∈ rows j, w ∉ rows i)
    (hf : ∀ i, C.eval (rows i) = false)
    (ht : ∀ i w, w ∉ rows i → C.eval (insert w (rows i)) = true) : m ≤ 2 ^ C.size := by
  have inj : Function.Injective (fun i => leftBit C (rows i)) := by
    intro i j h
    by_contra hne
    obtain ⟨w,hw,hwi⟩ := distinct i j hne
    have sub : insert w (rows i) ⊆ rows i ∪ rows j := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_right _ hw
      · exact Finset.mem_union_left _ hv
    have t := ht i w hwi
    have f1 := hf i
    have f2 := hf j
    simp only [eval, decide_eq_true_eq] at t
    simp only [eval, decide_eq_false_iff_not] at f1 f2
    rcases t with ⟨v,ho,hv⟩ | ⟨g,ho,hg⟩
    · rcases Finset.mem_union.mp (sub hv) with hv | hv
      · exact f1 (Or.inl ⟨v,ho,hv⟩)
      · exact f2 (Or.inl ⟨v,ho,hv⟩)
    · rcases transferGate C _ _ _ sub h g hg with hx | hx
      · exact f1 (Or.inr ⟨g,ho,hx⟩)
      · exact f2 (Or.inr ⟨g,ho,hx⟩)
  simpa using Fintype.card_le_of_injective _ inj


private def circuit6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  leftGates := ![∅, ∅, ∅, ∅]
  rightGates := ![∅, ∅, ∅, ∅]
  outVars := ∅
  outGates := {0, 1, 2, 3}

private def rows6 : Fin 9 → Finset (Fin 6) :=
  ![{0, 3}, {1, 3}, {2, 3}, {0, 4}, {1, 4}, {2, 4}, {0, 5}, {1, 5}, {2, 5}]

private def circuit5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  rightVars := ![{1, 4}, {1, 3}, {4}]
  leftGates := ![∅, ∅, ∅]
  rightGates := ![∅, ∅, ∅]
  outVars := ∅
  outGates := {0, 1, 2}

private def rows5 : Fin 5 → Finset (Fin 5) :=
  ![{0, 2}, {0, 3}, {1, 3}, {1, 4}, {2, 4}]

private def circuit7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  leftGates := ![∅, {0}, {1}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

private def rows7 : Fin 7 → Finset (Fin 7) :=
  ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 5}, {0, 6}, {5, 6}]

end PEqualNP.Outside.L_meta_906

open PEqualNP.Outside.L_meta_906 PEqualNP.AndCount

set_option synthInstance.maxSize 10000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_906 : (∀ G : SimpleGraph (Fin 6), G = SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed ∧ C.size ≤ 4 ∧
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed →
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true) →
    4 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 5), G = SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed →
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 7), G = SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed →
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro G rfl
    constructor
    · refine ⟨circuit6, ?_, by decide, ?_⟩
      · unfold AndCountCircuit.WellFormed
        decide +kernel
      · simp only [SimpleGraph.fromRel_adj]
        decide +kernel
    · intro C _hWF hpartial
      have rowdata : ∀ i : Fin 9, (∀ a ∈ rows6 i, ∀ c ∈ rows6 i, ¬ (SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))).Adj a c) ∧ (∀ w : Fin 6, w ∉ rows6 i → ∃ a ∈ rows6 i, (SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ)))).Adj a w) := by
        simp only [SimpleGraph.fromRel_adj]
        decide +kernel
      have h := countRows C rows6 (by decide +kernel)
        (fun i => (hpartial (rows6 i) (rowdata i).1 (rowdata i).2).1)
        (fun i => (hpartial (rows6 i) (rowdata i).1 (rowdata i).2).2)
      by_contra! hlt
      have hh : C.size ≤ 3 := by omega
      have hp : 2 ^ C.size ≤ 2 ^ (3 : ℕ) := Nat.pow_le_pow_right (by decide) hh
      omega
  · rintro G rfl
    constructor
    · refine ⟨circuit5, ?_, by decide, ?_⟩
      · unfold AndCountCircuit.WellFormed
        decide +kernel
      · simp only [SimpleGraph.fromRel_adj]
        decide +kernel
    · intro C _hWF hpartial
      have rowdata : ∀ i : Fin 5, (∀ a ∈ rows5 i, ∀ c ∈ rows5 i, ¬ (SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))).Adj a c) ∧ (∀ w : Fin 5, w ∉ rows5 i → ∃ a ∈ rows5 i, (SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ)))).Adj a w) := by
        simp only [SimpleGraph.fromRel_adj]
        decide +kernel
      have h := countRows C rows5 (by decide +kernel)
        (fun i => (hpartial (rows5 i) (rowdata i).1 (rowdata i).2).1)
        (fun i => (hpartial (rows5 i) (rowdata i).1 (rowdata i).2).2)
      by_contra! hlt
      have hh : C.size ≤ 2 := by omega
      have hp : 2 ^ C.size ≤ 2 ^ (2 : ℕ) := Nat.pow_le_pow_right (by decide) hh
      omega
  · rintro G rfl
    constructor
    · refine ⟨circuit7, ?_, by decide, ?_⟩
      · unfold AndCountCircuit.WellFormed
        decide +kernel
      · simp only [SimpleGraph.fromRel_adj]
        decide +kernel
    · intro C _hWF hpartial
      have rowdata : ∀ i : Fin 7, (∀ a ∈ rows7 i, ∀ c ∈ rows7 i, ¬ (SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))).Adj a c) ∧ (∀ w : Fin 7, w ∉ rows7 i → ∃ a ∈ rows7 i, (SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ)))).Adj a w) := by
        simp only [SimpleGraph.fromRel_adj]
        decide +kernel
      have h := countRows C rows7 (by decide +kernel)
        (fun i => (hpartial (rows7 i) (rowdata i).1 (rowdata i).2).1)
        (fun i => (hpartial (rows7 i) (rowdata i).1 (rowdata i).2).2)
      by_contra! hlt
      have hh : C.size ≤ 2 := by omega
      have hp : 2 ^ C.size ≤ 2 ^ (2 : ℕ) := Nat.pow_le_pow_right (by decide) hh
      omega
