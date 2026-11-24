import HonestCover
import PEqualNP.MetaComplexity.Helpers.ForestBound
import PEqualNP.MetaComplexity.L106
import PEqualNP.Outside.L_meta_548

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace HonestCover1904

abbrev Exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit) :=
  ∀ x : Fin n → Bool, D.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)

abbrev Honest {n : ℕ} (G : SimpleGraph (Fin n)) (D : Circuit) :=
  ∀ j g, D.gates[j]?=some g → g.op=.and → ∀ x : Fin n → Bool,
    (D.wires (List.ofFn x)).getD (n+j) false=true → ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true

/-- This is the witness and all four conditions of the posted L-meta-1904. -/
abbrev Goal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∃ D : Circuit, Monotone2 D ∧ Exact G D ∧ (∀ C, Monotone2 C → Exact G C → D.size≤C.size) ∧ Honest G D

theorem leastCover {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ T : Finset (Fin n), IsMinCover G T := by
  classical
  let P := fun k => ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧ T.card=k
  have yes : ∃ k, P k := ⟨_,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  obtain ⟨T,cov,eq⟩ := Nat.find_spec yes
  exact ⟨T,cov,fun A hA => eq ▸ Nat.find_min' yes ⟨A,hA,rfl⟩⟩

theorem fromBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (cov : G.IsVertexCover ↑T)
    (lower : ∀ C : Circuit, Monotone2 C → Exact G C → G.edgeFinset.card+T.card-1 ≤ C.size) : Goal G := by
  obtain ⟨D,mono,eval,cost,all⟩ := builder G T cov
  exact ⟨D,mono,eval,fun C hC h => cost.trans (lower C hC h),all⟩

private theorem sizeWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (mono : Monotone2 C) (eval : Exact G C) :
    HasCircuitSize n (fun x => decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) C.size := by
  refine ⟨C,?_,le_rfl,eval⟩
  intro g hg
  obtain ⟨op,len⟩ := mono g hg
  exact ⟨by simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢; tauto,len⟩

theorem forests {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (acyclic : G.IsAcyclic) :
    Goal G := by
  classical
  obtain ⟨T,minimal⟩ := leastCover G
  apply fromBudget G T minimal.1
  intro C mono eval
  by_cases edge : ∃ a b, G.Adj a b
  · have h := Helpers.Forest.forest_bound n T.card C.size G acyclic edge minimal.2
        (sizeWitness G C mono eval)
    omega
  · have bot : G=⊥ := by ext a b; simp_all
    have empty : T.card=0 := by
      have h := minimal.2 ∅ (by rw [bot]; simp [SimpleGraph.IsVertexCover])
      simpa using h
    simp [SimpleGraph.edgeFinset_eq_empty.mpr bot,empty]

/-- Every cyclic relabeling of a cycle of length at least five satisfies the full posted witness. -/
theorem cycles {n : ℕ} (hn : 5≤n) (e : Fin n ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (cyc : ∀ u v, G.Adj u v ↔ ((e u).val+1)%n=(e v).val ∨ ((e v).val+1)%n=(e u).val) :
    Goal G := by
  classical
  obtain ⟨T,minimal⟩ := leastCover G
  apply fromBudget G T minimal.1
  intro C mono eval
  have hs : HasCircuitSize n (graphFun G ∅) C.size := by
    have funEq : graphFun G ∅ = (fun x => decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) := by
      funext x; simp [graphFun]
    rw [funEq]
    exact sizeWitness G C mono eval
  let next (u : Fin n) : Fin n := e.symm ⟨((e u).val+1)%n,Nat.mod_lt _ (by omega)⟩
  have sub : G.edgeFinset ⊆ Finset.univ.image (fun u : Fin n => s(u,next u)) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      rcases (cyc u v).mp (SimpleGraph.mem_edgeFinset.mp he) with h | h
      · have eq : next u = v := by apply e.injective; simpa [next] using Fin.ext h
        exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,by rw [eq]⟩
      · have eq : next v = u := by apply e.injective; simpa [next] using Fin.ext h
        exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,by rw [eq,Sym2.eq_swap]⟩
  have edges : G.edgeFinset.card ≤ n := by
    simpa using (Finset.card_le_card sub).trans Finset.card_image_le
  let evenVertex (t : Fin ((n+1)/2)) : Fin n := e.symm ⟨2*t.val,by have := t.isLt; omega⟩
  let A := Finset.univ.image evenVertex
  have evenMem (u : Fin n) (hu : (e u).val % 2 = 0) : u ∈ A := by
    let k : Fin ((n+1)/2) := ⟨(e u).val/2,by have := (e u).isLt; omega⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,e.injective (by apply Fin.ext; simp [evenVertex,k]; omega)⟩
  have oneEven (u v : Fin n) (h : ((e u).val+1)%n = (e v).val) : u ∈ A ∨ v ∈ A := by
    by_cases he : (e u).val % 2 = 0
    · exact Or.inl (evenMem u he)
    · apply Or.inr (evenMem v ?_)
      by_cases hlt : (e u).val+1 < n
      · rw [Nat.mod_eq_of_lt hlt] at h
        omega
      · have eq : (e u).val+1 = n := by have := (e u).isLt; omega
        have hz : (e v).val = 0 := by simpa [eq] using h.symm
        simp [hz]
  have cover : G.IsVertexCover ↑A := by
    intro u v hadj
    rcases (cyc u v).mp hadj with h | h
    · exact oneEven u v h
    · exact (oneEven v u h).symm
  have cardA : A.card ≤ (n+1)/2 := by simpa [A] using (Finset.card_image_le
    (s := (Finset.univ : Finset (Fin ((n+1)/2)))) (f := evenVertex))
  have coverSize := (minimal.2 A cover).trans cardA
  let H := fun x : Fin n → Bool =>
    decide (∃ i j : Fin n, (i.val+1)%n = j.val ∧ x i = true ∧ x j = true)
  have agrees : (fun x => graphFun G ∅ (x ∘ e)) = H := by
    funext x
    rw [Bool.eq_iff_iff]
    simp only [graphFun, H, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨u,v,ha,hu,hv⟩
      rcases (cyc u v).mp ha with h | h
      · exact ⟨e u,e v,h,hu,hv⟩
      · exact ⟨e v,e u,h,hv,hu⟩
    · rintro ⟨u,v,h,hu,hv⟩
      refine ⟨e.symm u,e.symm v,(cyc _ _).mpr (Or.inl (by simpa using h)),?_,?_⟩ <;> simp [Function.comp,hu,hv]
  have hrel := Gap548Circuit.relabel_size e (graphFun G ∅) C.size hs
  rw [agrees] at hrel
  have exactSize := (PEqualNP.MetaComplexity.L106 n C.size hn).mp hrel
  omega


end HonestCover1904
