import Mathlib
import PEqualNP.Defs.ReadK

namespace PlaneStarVectors
open PEqualNP.ReadK PEqualNP.CircuitLowerBounds

abbrev Vectors := List (List ℕ)

def op (S : List ℕ) (k : ℕ) (g : GateOp) (ins : List Vectors) : Vectors :=
  match g with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

private theorem insert_mem (v a : List ℕ) (A : Vectors) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases h : a ∈ A
  · simp [h, or_iff_left_of_imp (fun (e : v = a) => e ▸ h)]
  · simp [h]

private theorem fold_mem (v : List ℕ) (B A : Vectors) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons a B ih => simp [ih, insert_mem, or_assoc]

theorem choice (S : List ℕ) (k : ℕ) (A B : Vectors) (v : List ℕ) :
    v ∈ op S k .or [A,B] ↔ v ∈ A ∨ v ∈ B := by
  simp [op, fold_mem]

private theorem pair_mem (k : ℕ) {A B : Vectors} {u v : List ℕ}
    (hu : u ∈ A) (hv : v ∈ B) : capAdd k u v ∈ andStep k A B := by
  simp only [andStep, fold_mem, List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  exact ⟨u,hu,v,hv,rfl⟩

def indicator (S : List ℕ) (i : ℕ) := S.map fun j => if j = i then 1 else 0

theorem leaf (S : List ℕ) (k i : ℕ) (hi : i ∈ S) :
    indicator S i ∈ leafVectors S k i := by
  simp [leafVectors,indicator,hi]

private theorem zero_indicator (S : List ℕ) (k i : ℕ) :
    capAdd k (S.map fun _ => 0) (indicator S i) = indicator S i := by
  induction S with
  | nil => rfl
  | cons j S ih =>
    simp only [indicator,capAdd,List.map_cons,List.zipWith_cons_cons] at ih ⊢
    rw [ih]
    split <;> simp

theorem edge (S : List ℕ) (k p l : ℕ) {A B : Vectors}
    (hp : indicator S p ∈ A) (hl : indicator S l ∈ B) :
    capAdd k (indicator S p) (indicator S l) ∈ op S k .and [A,B] := by
  apply pair_mem _ _ hl
  rw [← zero_indicator S k p]
  exact pair_mem _ (by simp) hp

theorem edge_entries (S : List ℕ) (k p l : ℕ) (ne : p ≠ l) :
    ∀ a ∈ capAdd k (indicator S p) (indicator S l), a ≤ 1 := by
  induction S with
  | nil => simp [capAdd, indicator]
  | cons j S ih =>
    simp only [capAdd, indicator, List.map_cons, List.zipWith_cons_cons, List.mem_cons] at ih ⊢
    intro a h
    rcases h with rfl | h
    · by_cases hp : j=p <;> by_cases hl : j=l <;> simp_all
    · exact ih a h

end PlaneStarVectors
