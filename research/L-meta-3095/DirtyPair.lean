import Mathlib
import PEqualNP.Outside.L_meta_1602
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PetersenDirtyPair
open PEqualNP.CircuitLowerBounds

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def graph : SimpleGraph (Fin 9) where
  Adj a b := (a,b) ∈ edges ∨ (b,a) ∈ edges
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private theorem noFour : ∀ a b c d : Fin 9, a≠c → b≠d →
    ¬(graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by decide +kernel

private def ordered : Fin 12 → Fin 9 × Fin 9 :=
  ![(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(5,8)]

private theorem twelve (inst : Fintype graph.edgeSet) :
    12 ≤ (@SimpleGraph.edgeFinset _ graph inst).card := by
  let f (i : Fin 12) := s((ordered i).1,(ordered i).2)
  have inc : ∀ i : Fin 12, graph.Adj (ordered i).1 (ordered i).2 := by decide +kernel
  have inj : Function.Injective f := by decide +kernel
  have le := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin 12)))
    (t := @SimpleGraph.edgeFinset _ graph inst) f (fun i _ => SimpleGraph.mem_edgeFinset.mpr (inc i)) inj.injOn
  simpa using le

set_option maxRecDepth 10000 in
private theorem covers : ∀ T : Finset (Fin 9),
    (∀ a b, graph.Adj a b → a∈T ∨ b∈T) → 5 ≤ T.card := by decide +kernel

def small (x : Fin 9 → Bool) := x = (fun _ => false) ∨
  (∃ a : Fin 9, x = fun i => decide (i=a)) ∨ ∃ a b : Fin 9, x = fun i => decide (i=a ∨ i=b)

-- A 15-gate monotone counterexample must have an AND computing a false positive
-- already on the empty input, a singleton or a two-vertex input.
theorem dirtyPair (C : Circuit)
    (ao : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (exactFun : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
      decide (∃ a b, graph.Adj a b ∧ x a=true ∧ x b=true))
    (budget : C.size ≤ 15) :
    ∃ j : Fin C.gates.length, ∃ x : Fin 9 → Bool, small x ∧
      (C.gates.get j).op = .and ∧
      (C.wires (List.ofFn x)).getD (9+j.val) false = true ∧
      ¬ ∃ a b, graph.Adj a b ∧ x a=true ∧ x b=true := by
  classical
  by_contra! clean
  obtain ⟨T,coversAll,count⟩ := PEqualNP.Outside.L_meta_1602.pairCleanBound
    9 graph noFour C.gates C.output ao exactFun clean
  have cov := covers T coversAll
  have es := twelve (inferInstance : Fintype graph.edgeSet)
  change C.gates.length ≤ 15 at budget
  omega

def pair (a b i : Fin 9) : Bool := decide (i=a ∨ i=b)

private theorem nonneighbor : ∀ a : Fin 9, ∃ b : Fin 9, a ≠ b ∧ ¬ graph.Adj a b := by decide +kernel

private theorem extend {x : Fin 9 → Bool} (hs : small x)
    (indep : ¬ ∃ a b, graph.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ a b, a ≠ b ∧ ¬ graph.Adj a b ∧ ∀ i, x i=true → pair a b i=true := by
  rcases hs with rfl|⟨a,rfl⟩|⟨a,b,rfl⟩
  · obtain ⟨b,ne,nj⟩ := nonneighbor 0
    exact ⟨0,b,ne,nj,by simp⟩
  · obtain ⟨b,ne,nj⟩ := nonneighbor a
    exact ⟨a,b,ne,nj,by simp [pair]⟩
  · by_cases h : a=b
    · subst b
      obtain ⟨r,ne,nj⟩ := nonneighbor a
      exact ⟨a,r,ne,nj,by simp [pair]⟩
    · exact ⟨a,b,h,fun adj => indep ⟨a,b,adj,by simp,by simp⟩,fun _ h => h⟩

-- It suffices to look at the 24 unordered nonedges. This test also covers an
-- AND that was already true on the empty assignment or a singleton.
theorem dirtyNonedge (C : Circuit)
    (ao : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (exactFun : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
      decide (∃ a b, graph.Adj a b ∧ x a=true ∧ x b=true))
    (budget : C.size ≤ 15) :
    ∃ (j : Fin C.gates.length) (a b : Fin 9), a ≠ b ∧ ¬ graph.Adj a b ∧
      (C.gates.get j).op = .and ∧ (C.wires (List.ofFn (pair a b))).getD (9+j.val) false = true := by
  obtain ⟨j,x,smallInput,isAnd,yes,no⟩ := dirtyPair C ao exactFun budget
  obtain ⟨a,b,ne,nonedge,le⟩ := extend smallInput no
  refine ⟨j,a,b,ne,nonedge,isAnd,?_⟩
  have mono : IsMonotoneCircuit C := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (ao g hg).1
  apply PEqualNP.MetaComplexity.LowMergeProof.wires_mono C mono (List.ofFn x) (List.ofFn (pair a b)) (by simp) _ _ yes
  intro k hk
  by_cases inRange : k < 9
  · have get (z : Fin 9 → Bool) : (List.ofFn z).getD k false = z ⟨k,inRange⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using inRange)]
      exact List.getElem_ofFn _
    rw [get] at hk ⊢
    exact le _ hk
  · simp [List.getD_eq_getElem?_getD,inRange] at hk

end PetersenDirtyPair
