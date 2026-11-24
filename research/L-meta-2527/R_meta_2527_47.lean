import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2527_47
    (extractPrefix : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) →
      C.gates[1]?.map Gate.op = some GateOp.or →
      ∃ (a b : Fin 11) (D : Circuit), FanInTwo D ∧ D.size + 2 = C.size ∧
        ∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
          D.eval (w ++ [w.getD a false || w.getD b false]) = circuitFun 9 C x)
    (minorFour : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (pin : ∀ (D : Circuit) (a : Fin 11) (f : (Fin 9 → Bool) → Bool), FanInTwo D →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [w.getD a false]) = f x) →
      (∃ x : Fin 9 → Bool, x 0 = true ∧ x 4 = false ∧ f x ≠ f (Function.update x 4 true)) →
      let g := fun y : Fin 8 → Bool => f ![y 0,y 1,y 2,y 3,false,y 4,y 5,y 6,y 7]
      (∃ y z, g y ≠ g z) → HasCircuitSize 8 g (D.size-1))
    (genuine : ∀ (D : Circuit) (a b : Fin 10), FanInTwo D → a < b →
      ¬ (a = 0 ∧ b = 4) → ¬ ((a = 0 ∨ a = 4) ∧ b = 9) →
      (∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (w ++ [w.getD a false || w.getD b false]) = (fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) x) → 14 ≤ D.size) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (∃ x7 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x7.inputs) → (∃ x8 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x8.inputs) → (16 : ℕ) ≤ x2.size := by
  dsimp only
  intro C fan first computes second _ _
  obtain ⟨a,b,D,hD,hs,he⟩ := extractPrefix C fan first second
  let read := fun (x : Fin 9 → Bool) (k : Fin 11) =>
    (List.ofFn x ++ [x 0 || x 4]).getD k false
  have tail : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 4] ++ [read x a || read x b]) = (fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) x :=
    fun x => (he x).trans (congrFun computes x)
  have norm : ∀ i j : Fin 11,
      (∃ k : Fin 11, ∀ x : Fin 9 → Bool, (read x i || read x j) = read x k) ∨
      ∃ u v : Fin 10, u < v ∧ ¬ (u = 0 ∧ v = 4) ∧ ¬ ((u = 0 ∨ u = 4) ∧ v = 9) ∧
        ∀ x : Fin 9 → Bool, (read x i || read x j) = (read x u.castSucc || read x v.castSucc) := by
    intro i j
    have no : ∀ x, read x 10 = false := by intro x; simp [read]
    have last : ∀ x, read x 9 = (x 0 || x 4) := by intro x; simp [read]
    have zero : ∀ x, read x 0 = x 0 := by intro x; simp [read]
    have four : ∀ x, read x 4 = x 4 := by intro x; simp [read]
    by_cases special : ∃ k : Fin 11, ∀ x, (read x i || read x j) = read x k
    · exact Or.inl special
    right
    have diff : i ≠ j := by rintro rfl; exact special ⟨i, by simp⟩
    have hi : i.val < 10 := by
      by_contra! h
      have eq : i = 10 := Fin.ext (by omega)
      exact special ⟨j,by simp [eq,no]⟩
    have hj : j.val < 10 := by
      by_contra! h
      have eq : j = 10 := Fin.ext (by omega)
      exact special ⟨i,by simp [eq,no]⟩
    let u : Fin 10 := ⟨min i.val j.val, by omega⟩
    let v : Fin 10 := ⟨max i.val j.val, by omega⟩
    have uv : u < v := by
      have hn : i.val ≠ j.val := fun e => diff (Fin.ext e)
      change min i.val j.val < max i.val j.val
      omega
    have eqs : (u.castSucc = i ∧ v.castSucc = j) ∨ (u.castSucc = j ∧ v.castSucc = i) := by
      rcases le_total i.val j.val with h|h
      · exact Or.inl ⟨Fin.ext (min_eq_left h),Fin.ext (max_eq_right h)⟩
      · exact Or.inr ⟨Fin.ext (min_eq_right h),Fin.ext (max_eq_left h)⟩
    have heq : ∀ x, (read x i || read x j) = (read x u.castSucc || read x v.castSucc) := by
      rcases eqs with ⟨e,d⟩|⟨e,d⟩ <;> simp [e,d,Bool.or_comm]
    refine ⟨u,v,uv,?_,?_,heq⟩
    · rintro ⟨hu,hv⟩
      apply special
      refine ⟨9,fun x => (heq x).trans ?_⟩
      rw [hu,hv]
      change (read x 0 || read x 4) = read x 9
      rw [zero,four,last]
    · rintro ⟨hu,hv⟩
      apply special
      refine ⟨9,fun x => (heq x).trans ?_⟩
      rcases hu with hu|hu
      · rw [hu,hv]; change (read x 0 || read x 9) = read x 9
        rw [zero,last]; cases x 0 <;> rfl
      · rw [hu,hv]; change (read x 4 || read x 9) = read x 9
        rw [four,last]; cases x 0 <;> cases x 4 <;> rfl
  rcases norm a b with ⟨k,hk⟩ | ⟨u,v,hu,hpair,habs,hv⟩
  · have small := pin D k (fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) hD (fun x => by simpa only [hk] using tail x)
        ⟨fun j => decide (j = 0), by decide +kernel⟩
        ⟨fun _ => false, fun j => decide (j = 0 ∨ j = 1), by decide +kernel⟩
    by_contra! hh
    apply minorFour
    obtain ⟨E,ef,es,ee⟩ := small
    refine ⟨E,ef,by omega,?_⟩
    have eqv : (fun y : Fin 8 → Bool => (fun (x : Fin 9 → Bool) => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) ![y 0,y 1,y 2,y 3,false,y 4,y 5,y 6,y 7]) =
        (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) := by decide +kernel
    exact fun y => (ee y).trans (congrFun eqv y)
  · have bound := genuine D u v hD hu hpair habs (fun x => by
      have t := tail x
      rw [hv x] at t
      exact t)
    omega
