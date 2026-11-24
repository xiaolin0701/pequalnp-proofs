import Mathlib
import PEqualNP.Defs

namespace ThreeCube

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)]

def circuit : Circuit :=
  ⟨[⟨.or,[2,1]⟩, ⟨.or,[7,4]⟩, ⟨.or,[8,7]⟩,
    ⟨.or,[8,4]⟩, ⟨.or,[9,2]⟩, ⟨.or,[9,1]⟩,
    ⟨.and,[10,3]⟩, ⟨.and,[11,0]⟩, ⟨.and,[12,6]⟩,
    ⟨.and,[13,5]⟩, ⟨.or,[15,14]⟩, ⟨.or,[17,16]⟩,
    ⟨.or,[19,18]⟩], 20⟩

theorem upper : Monotone2 circuit ∧ circuit.size = 13 ∧
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) = edges.any (fun e => x e.1 && x e.2) := by
  refine ⟨?_, (by decide), ?_⟩
  · intro g hg
    simp [circuit] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
  · intro x
    have h : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    simp [circuit,Circuit.eval,Circuit.wires,GateOp.eval,List.getD,edges]
    generalize h0 : x 0 = b0
    generalize h1 : x 1 = b1
    generalize h2 : x 2 = b2
    generalize h3 : x 3 = b3
    generalize h4 : x 4 = b4
    generalize h5 : x 5 = b5
    generalize h6 : x 6 = b6
    generalize h7 : x 7 = b7
    clear h0 h1 h2 h3 h4 h5 h6 h7
    revert b0 b1 b2 b3 b4 b5 b6 b7
    decide +kernel

/-- The same 13-gate witness in the exact input-output relation used by L-meta-969. -/
theorem computes (x : Fin 8 → Bool) : circuit.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 8, (u.val, v.val) ∈
      ([(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)] :
        List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  rw [upper.2.2 x, List.any_eq_true]
  change (∃ e ∈ edges, (x e.1 && x e.2) = true) ↔
    ∃ u v : Fin 8, (u.val, v.val) ∈ edges.map (fun e => (e.1.val, e.2.val)) ∧ _
  constructor
  · rintro ⟨⟨u, v⟩, h, ht⟩
    exact ⟨u, v, List.mem_map_of_mem h, (Bool.and_eq_true_iff.mp ht)⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨⟨a,b⟩, hab, he⟩ := List.mem_map.mp h
    have ha : a = u := Fin.ext (congrArg Prod.fst he)
    have hb : b = v := Fin.ext (congrArg Prod.snd he)
    subst u
    subst v
    exact ⟨(a,b), hab, Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩

end ThreeCube
