import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverCircuit

namespace HonestCover1904

/-- All AND gates in a block pass are enumerated in its list of output wires. -/
private theorem blockOutputs (n : ℕ) (bs : List (ℕ × List ℕ))
    (pos : ∀ b∈bs, 0<b.2.length) (gs : List Gate) (os : List ℕ)
    (invariant : ∀ j g, gs[j]?=some g → g.op=.and → n+j∈os) :
    ∀ j g, (bs.foldl (passStep n) (gs,os)).1[j]?=some g → g.op=.and →
      n+j∈(bs.foldl (passStep n) (gs,os)).2 := by
  induction bs generalizing gs os with
  | nil => exact invariant
  | cons b bs ih =>
    rw [List.foldl_cons]
    apply ih (fun x hx => pos x (by simp [hx]))
    intro j g atGate yes
    change (gs++blockGates (n+gs.length) b)[j]?=some g at atGate
    change n+j∈os++[n+gs.length+b.2.length-1]
    by_cases inOld : j<gs.length
    · rw [List.getElem?_append_left inOld] at atGate
      exact List.mem_append_left _ (invariant j g atGate yes)
    · rw [List.getElem?_append_right (by omega)] at atGate
      let chain := orChain (n+gs.length) (b.2.headD 0) b.2.tail
      change (chain++[_])[j-gs.length]?=some g at atGate
      by_cases inChain : j-gs.length<chain.length
      · rw [List.getElem?_append_left inChain] at atGate
        have hop := (orChain_ops _ _ _ g (List.mem_of_getElem? atGate)).1
        simp [yes] at hop
      · have len := (List.getElem?_eq_some_iff.mp atGate).1
        simp only [List.length_append,List.length_cons,List.length_nil] at len
        have lc : chain.length=b.2.length-1 := by simp [chain,orChain_length,List.length_tail]
        have nz := pos b (by simp)
        exact List.mem_append_right _ (List.mem_singleton.mpr (by omega))

/-- In the explicit cover circuit a firing AND always forces the output. -/
theorem andForces {n : ℕ} (edges : List (ℕ × ℕ)) (cover : List ℕ)
    (valid : ∀ e∈edges, e.1<n ∧ e.2<n) (j : ℕ) (g : Gate)
    (atGate : (coverCircuit n edges cover).gates[j]?=some g) (yes : g.op=.and)
    (x : Fin n → Bool) :
    ((coverCircuit n edges cover).wires (List.ofFn x)).getD (n+j) false=true →
      circuitFun n (coverCircuit n edges cover) x=true := by
  intro fire
  let bs := blocks edges cover
  let bp := blockPass n bs
  let win := List.ofFn x
  let chain := orChain (n+bp.1.length) (bp.2.headD (n+bp.1.length)) bp.2.tail
  change (bp.1++chain)[j]?=some g at atGate
  have before : j<bp.1.length := by
    by_contra! late
    rw [List.getElem?_append_right late] at atGate
    have hor := (orChain_ops _ _ _ g (List.mem_of_getElem? atGate)).1
    simp [yes] at hor
  rw [List.getElem?_append_left before] at atGate
  have out : n+j∈bp.2 := by
    apply blockOutputs n bs (blocks_pos edges cover) [] [] (by simp) j g _ yes
    exact atGate
  have hb := blocks_ok n edges cover valid
  obtain ⟨_,signals⟩ := pass_eval n win (by simp [win]) bs [] [] [] hb (by simp) (by simp)
  rw [←blockPass_eq] at signals
  change bp.2.map (fun a => (run bp.1 win).getD a false) = [] ++ bs.map (blockVal win) at signals
  change (run (bp.1++chain) win).getD (n+j) false=true at fire
  rw [run_append,getD_run _ _ _ (by simpa [run_length,win] using before)] at fire
  have hTrue : true∈bs.map (blockVal win) := by
    rw [List.nil_append] at signals
    rw [←signals]
    exact List.mem_map.mpr ⟨n+j,out,fire⟩
  rw [circuitFun_blocks n edges cover x hb,List.any_eq_true]
  exact List.mem_map.mp hTrue

/-- The explicit circuit meets the cover budget and all of its AND gates imply an active edge. -/
theorem builder {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (cov : ∀ a b, G.Adj a b → a∈T ∨ b∈T) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x)=decide (∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)) ∧
      D.size ≤ G.edgeFinset.card+T.card-1 ∧
      ∀ j g, D.gates[j]?=some g → g.op=.and → ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD (n+j) false=true → ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
  classical
  by_cases edge : ∃ a b, G.Adj a b
  · let es := graph_edges n G
    let cs := graph_cover T
    let D := coverCircuit n es cs
    have eval := circuitFun_eq_graph n es cs G (graph_hG n G) (graph_hE n G) (graph_hT n G T cov)
    have size := size_le n es cs (graph_edges_ne_nil n G edge)
    rw [graph_edges_length,graph_cover_length] at size
    refine ⟨D,?_,fun x => congrFun eval x,by dsimp [D]; omega,?_⟩
    · intro g hg
      have law := gates_ops n es cs g hg
      exact ⟨by rcases law.1 with h|h <;> simp [h],law.2.le⟩
    · intro j g atGate op x fire
      have on := andForces es cs (graph_hE n G) j g atGate op x fire
      rw [eval] at on
      exact of_decide_eq_true on
  · refine ⟨⟨[],n⟩,by simp [Monotone2],?_,by simp [Circuit.size],by simp⟩
    intro x
    have neg : ¬∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := fun ⟨a,b,h,_,_⟩ => edge ⟨a,b,h⟩
    simp [Circuit.eval,Circuit.wires,neg]

end HonestCover1904
