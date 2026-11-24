import Mathlib
import PEqualNP.Defs

namespace Petersen3136
open PEqualNP.CircuitLowerBounds

def relevantOperands (g : Gate) : List ℕ := match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem relevant_eval (g : Gate) (w : List Bool) :
    g.op.eval ((relevantOperands g).map (fun i => w.getD i false)) =
    g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  rcases g with ⟨op,ins⟩
  cases op <;> try rfl
  cases ins <;> rfl

def operandUses (gs : List Gate) : List ℕ := gs.flatMap relevantOperands

private theorem arity_budget (gs : List Gate) (fan : ∀ g ∈ gs, g.inputs.length≤2) :
    (operandUses gs).length≤2*gs.length := by
  induction gs with
  | nil => simp [operandUses]
  | cons g gs ih =>
    have h : (relevantOperands g).length ≤ 2 := by
      have ar := fan g List.mem_cons_self
      cases e : g.op <;> simp [relevantOperands,e,ar]
    have k := ih (fun t ht => fan t (List.mem_cons_of_mem _ ht))
    simp only [operandUses, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

/-- For a live tail with locally numbered gates and 13 initial wires, nine compulsory raw
inputs leave at most two operand slots in a ten-gate tail for prefix results, repeated
uses of any wire, and reductions in fan-in. -/
theorem ten_gate_cone_budget (gs : List Gate) (k : ℕ) (size : gs.length=k) (lim : k ≤ 10)
    (fan : ∀ g ∈ gs, g.inputs.length≤2) (U : Finset ℕ)
    (raw : ∀ i < 9, i ∈ operandUses gs)
    (pfx : ∀ i ∈ U, 9 ≤ i ∧ i < 13 ∧ i ∈ operandUses gs)
    (live : ∀ i ∈ Finset.Ico 13 (13+(k-1)), i ∈ operandUses gs) :
    U.card + ((operandUses gs).length - (operandUses gs).toFinset.card) +
        (2*k-(operandUses gs).length) ≤ 2 := by
  let R := Finset.range 9
  let V := Finset.Ico 13 (13+(k-1))
  have ru : Disjoint R U := Finset.disjoint_left.mpr (fun i hi hu => by
    have h := Finset.mem_range.mp hi; have l := (pfx i hu).1; omega)
  have vv : Disjoint (R ∪ U) V := Finset.disjoint_left.mpr (fun i h hu => by
    have hv := (Finset.mem_Ico.mp hu).1
    rcases Finset.mem_union.mp h with h|h
    · have hr := Finset.mem_range.mp h; omega
    · have hr := (pfx i h).2.1; omega)
  have sub : (R ∪ U) ∪ V ⊆ (operandUses gs).toFinset := by
    intro i hi
    apply List.mem_toFinset.mpr
    rcases Finset.mem_union.mp hi with h|h
    · rcases Finset.mem_union.mp h with h|h
      · exact raw i (Finset.mem_range.mp h)
      · exact (pfx i h).2.2
    · exact live i h
  have bound := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint vv,Finset.card_union_of_disjoint ru] at bound
  simp only [R,V,Finset.card_range,Nat.card_Ico] at bound
  have uses := arity_budget gs fan
  rw [size] at uses
  have dup := (operandUses gs).toFinset_card_le
  omega

end Petersen3136
