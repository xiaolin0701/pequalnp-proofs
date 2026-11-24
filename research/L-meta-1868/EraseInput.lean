import Mathlib.Data.List.GetD
import PEqualNP.Defs.MetaComplexityLgpMono

namespace FirstAndErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete input n, hard-wired to false. The new index bad is beyond the completed circuit.
def newIndex (n bad k : ℕ) : ℕ :=
  if k < n then k else if k = n then bad else k - 1

def newGate (n bad : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (newIndex n bad)⟩

def erase (n : ℕ) (C : Circuit) : Circuit :=
  let bad := n + C.size
  ⟨C.gates.map (newGate n bad), newIndex n bad C.output⟩

theorem read_agrees (x tail : List Bool) (bad k : ℕ) (hb : x.length + tail.length ≤ bad) :
    (x ++ tail).getD (newIndex x.length bad k) false = (x ++ false :: tail).getD k false := by
  by_cases h : k < x.length
  · simp only [newIndex, ite_eq_left h]
    rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · by_cases e : k = x.length
    · subst k
      simp only [newIndex, lt_irrefl, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by simpa using hb), List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · have hh : x.length ≤ k - 1 := by omega
      simp only [newIndex, ite_eq_right h, ite_eq_right e]
      rw [List.getD_append_right _ _ _ _ hh, List.getD_append_right _ _ _ _ (by omega)]
      have ee : k - x.length = (k - 1 - x.length) + 1 := by omega
      rw [ee]
      rfl

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_agrees (gs : List Gate) (x t : List Bool) (bad : ℕ)
    (hb : x.length + t.length + gs.length ≤ bad) :
    ∃ t' : List Bool, t'.length = t.length + gs.length ∧
      (gs.map (newGate x.length bad)).foldl step (x ++ t) = x ++ t' ∧
      gs.foldl step (x ++ false :: t) = x ++ false :: t' := by
  induction gs generalizing t with
  | nil => exact ⟨t, by simp, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (x ++ false :: t).getD i false)
    have hv : (newGate x.length bad g).op.eval
        ((newGate x.length bad g).inputs.map fun i => (x ++ t).getD i false) = v := by
      simp only [newGate, List.map_map, v]
      congr 1
      apply List.map_congr_left
      intro i _
      exact read_agrees x t bad i (by omega)
    obtain ⟨t', hl, hlft, hrgt⟩ := ih (t ++ [v]) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)
    refine ⟨t', by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl, ?_, ?_⟩
    · simpa only [List.map_cons, List.foldl_cons, step, hv, List.append_assoc] using hlft
    · simpa only [List.foldl_cons, step, v, List.append_assoc, List.cons_append] using hrgt

theorem erase_eval (C : Circuit) (x : List Bool) :
    (erase x.length C).eval x = C.eval (x ++ [false]) := by
  obtain ⟨t, ht, hleft, hright⟩ := fold_agrees C.gates x [] (x.length + C.size) (by simp [Circuit.size])
  change ((C.gates.map (newGate x.length (x.length+C.size))).foldl step x).getD _ false =
    (C.gates.foldl step (x ++ [false])).getD _ false
  simp only [List.append_nil] at hleft
  rw [hleft, hright]
  exact read_agrees x t _ _ (by simp [ht, Circuit.size])

theorem erase_size (n : ℕ) (C : Circuit) : (erase n C).size = C.size := by simp [erase, Circuit.size]

theorem erase_mono (n : ℕ) (C : Circuit) (h : Monotone2 C) : Monotone2 (erase n C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [newGate] using h g' hg'

end FirstAndErase
