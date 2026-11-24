import Mathlib
import PEqualNP.MetaComplexity.L106
import PEqualNP.Defs.Core
import PEqualNP.MetaComplexity.Helpers.LowMergeWires
import PEqualNP.MetaComplexity.Helpers.Deg3R1
import PEqualNP.Outside.L_meta_1501
import PEqualNP.Outside.L_meta_548
import PEqualNP.MetaComplexity.Helpers.ForestBound
import PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph

/-!
# Shared implicant cones and the residual cover inequality

The target is desk row L-meta-2962. The theorem `forests` proves its exact
inequality for every forest. The theorem `cycles` covers every cycle of length
at least five under any permutation of the inputs. `fromSizeLower` applies more generally to every
graph with the standard edge-plus-cover lower bound for fan-in-two circuits.
The gate family in that theorem may share gates arbitrarily.

The proof uses the repository’s gate-pruning construction, the characterization
of strict cones in L-meta-1501, the OR composition from L-meta-548, the standard
cover circuit, and the forest circuit lower bound.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
open PEqualNP.MetaComplexity.Deg3 PEqualNP.Outside.L_meta_1501

namespace CoreResidual2962

private theorem graphTrue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

private theorem gateMonotone {n : ℕ} {C : Circuit} (hAO : AndOrOnly C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) (j : ℕ) :
    gateVal n C j x = true → gateVal n C j y = true := by
  apply LowMergeProof.wires_mono C hAO (List.ofFn x) (List.ofFn y) (by simp)
  intro k hk
  by_cases hkn : k < n
  · simpa [List.getD_eq_getElem?_getD, hkn] using hxy ⟨k,hkn⟩ (by
      simpa [List.getD_eq_getElem?_getD, hkn] using hk)
  · simp [List.getD_eq_getElem?_getD, hkn] at hk

/-- Replacing any family of implicant gates by its union of accepted edge pairs is valid
after adjoining the residual edge function. The gates may share arbitrary internal wires. -/
theorem reassemble {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (M : Finset ℕ) (hAO : AndOrOnly C)
    (hBelow : ∀ j ∈ M, BelowF G C j) (x : Fin n → Bool) :
    let D := M.biUnion (gammaE G C)
    graphFun G ∅ x = true ↔
      graphFun (G.deleteEdges (D : Set (Sym2 (Fin n)))) ∅ x = true ∨
      ∃ j ∈ M, gateVal n C j x = true := by
  dsimp only
  let D := M.biUnion (gammaE G C)
  constructor
  · intro hx
    obtain ⟨u,v,huv,hxu,hxv⟩ := (graphTrue G x).mp hx
    by_cases hd : s(u,v) ∈ D
    · obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp hd
      obtain ⟨_,a,b,heq,hab⟩ := Finset.mem_filter.mp he
      refine Or.inr ⟨j,hj,gateMonotone hAO ?_ j hab⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        intro k hk <;> simp only [pairInput, decide_eq_true_eq] at hk <;>
        rcases hk with rfl | rfl <;> assumption
    · exact Or.inl ((graphTrue _ x).mpr ⟨u,v,SimpleGraph.deleteEdges_adj.mpr ⟨huv,hd⟩,hxu,hxv⟩)
  · rintro (hr | ⟨j,hj,hjx⟩)
    · obtain ⟨u,v,huv,hxu,hxv⟩ := (graphTrue _ x).mp hr
      exact (graphTrue G x).mpr ⟨u,v,(SimpleGraph.deleteEdges_adj.mp huv).1,hxu,hxv⟩
    · exact hBelow j hj x hjx

theorem maximalCores_reassemble {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) :
    let M := maximalCores G C
    let D := M.biUnion (gammaE G C)
    graphFun G ∅ x = true ↔
      graphFun (G.deleteEdges (D : Set (Sym2 (Fin n)))) ∅ x = true ∨
      ∃ j ∈ M, gateVal n C j x = true := by
  apply reassemble G C _ hAO.1
  intro j hj
  have hmax : IsMaximalCore G C j := (Finset.mem_filter.mp hj).2
  exact hmax.1.2.1.1

private theorem coneTrans {n : ℕ} {C : Circuit} {a b : ℕ} (hab : InCone n C a b) :
    ∀ {c}, InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro h
    obtain ⟨hc,k,hk,hread,hb | hb⟩ := (inCone_iff n C b c).mp h
    · subst k
      exact (inCone_iff n C a c).mpr ⟨hc,b,hk,hread,Or.inr hab⟩
    · exact (inCone_iff n C a c).mpr ⟨hc,k,hk,hread,Or.inr (ih k hk hb)⟩

/-- Extract all selected cones into one circuit. Every original gate in their union is
retained exactly once and the renumbered copies of all selected outputs agree on all inputs. -/
theorem compressCones {n : ℕ} (C : Circuit) (M : Finset ℕ)
    (hM : ∀ m ∈ M, m < C.size) (hAO : IsAO2 n C) :
    let U := M.biUnion (coneSet n C)
    ∃ (B : Circuit) (r : ℕ → ℕ), B.size = U.card ∧ FanInTwo B ∧
      (∀ j ∈ M, r j < n + B.size) ∧ ∀ j ∈ M, ∀ x : Fin n → Bool,
        (B.wires (List.ofFn x)).getD (r j) false = gateVal n C j x := by
  let U := M.biUnion (coneSet n C)
  let κ := fun j => decide (j ∈ U)
  let gs := d3r1Pruned n κ C.gates
  let B : Circuit := ⟨gs,0⟩
  have hκ (t) (ht : κ t = true) : t < C.gates.length := by
    have h : t ∈ U := of_decide_eq_true ht
    obtain ⟨m,hm,htm⟩ := Finset.mem_biUnion.mp h
    rcases Finset.mem_insert.mp htm with rfl | hh
    · exact hM _ hm
    · exact Finset.mem_range.mp (Finset.mem_filter.mp hh).1
  have hclosed (t : ℕ) (ht : t < C.gates.length) (hkeep : κ t = true)
      (a : ℕ) (ha : a ∈ C.gates[t].inputs) (hla : n ≤ a) (hua : a < n + t) :
      κ (a-n) = true := by
    have ha' : n + (a-n) ∈ (gateAt C t).inputs := by
      rw [show n+(a-n)=a by omega]
      simpa [gateAt, ht] using ha
    have haCone : InCone n C (a-n) t := (inCone_iff n C _ _).mpr
      ⟨ht,a-n,by omega,ha',Or.inl rfl⟩
    obtain ⟨m,hm,htm⟩ := Finset.mem_biUnion.mp (of_decide_eq_true hkeep : t ∈ U)
    apply decide_eq_true
    apply Finset.mem_biUnion.mpr
    refine ⟨m,hm,Finset.mem_insert_of_mem <| Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
    rcases Finset.mem_insert.mp htm with rfl | hh
    · exact haCone
    · exact coneTrans haCone (Finset.mem_filter.mp hh).2
  have hrange : ((Finset.range C.gates.length).filter (fun j => j ∈ U)) = U := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨And.right, fun h => ⟨hκ t (decide_eq_true h),h⟩⟩
  have hl : B.size = U.card := by
    change (d3r1Pruned n κ C.gates).length = U.card
    rw [d3r1_pruned_length, ← hrange]
    change ((List.range C.gates.length).filter κ).length = _
    rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    have hr : (List.range C.gates.length).toFinset = Finset.range C.gates.length := by
      ext j
      simp
    simp [κ,hr]
  have hmκ (j) (hj : j ∈ M) : κ j = true :=
    decide_eq_true (Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_insert_self _ _⟩)
  let r := fun j => d3r1New n κ (d3r1Top κ C.gates) (n+j)
  refine ⟨B,r,hl,?_,?_,?_⟩
  · intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    obtain ⟨hrt,_⟩ := List.mem_filter.mp ht
    have hlt := List.mem_range.mp hrt
    have ho := hAO.1 _ (List.getElem_mem (l := C.gates) (n := t) hlt)
    have hf := hAO.2.2 _ (List.getElem_mem (l := C.gates) (n := t) hlt)
    simp only [d3r1PGate, List.getD_eq_getElem _ _ hlt, List.length_map]
    refine ⟨?_, by omega⟩
    rcases ho with h | h <;> simp [h]
  · intro j hj
    have h := (d3r1_pruned_get n κ C.gates j (hM j hj) (hmκ j hj)).choose
    simpa [r,d3r1New,hmκ j hj,B,gs,Circuit.size] using Nat.add_lt_add_left h n
  · intro j hj x
    exact d3r1_prune_val false GateOp.eval (List.ofFn x) n (by simp) C.gates κ hκ hclosed (n+j)
      (Or.inr (by simpa using hmκ j hj))

private def appendOr (n : ℕ) (C : Circuit) (i : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or,[C.output,i]⟩],n+C.size⟩

private theorem appendWires {n : ℕ} (C : Circuit) (i : ℕ) (x : Fin n → Bool) :
    ((appendOr n C i).wires (List.ofFn x)) =
        C.wires (List.ofFn x) ++ [C.eval (List.ofFn x) ||
          (C.wires (List.ofFn x)).getD i false] := by
  simp [appendOr,Circuit.wires,Circuit.eval,List.foldl_append,GateOp.eval]

private theorem collapse (n : ℕ) (L : List ℕ) (B : Circuit) (hb : FanInTwo B)
    (hL : ∀ i ∈ L, i < n+B.size) :
    ∃ C : Circuit, FanInTwo C ∧ C.size = B.size + L.length ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        B.eval (List.ofFn x) = true ∨ ∃ i ∈ L, (B.wires (List.ofFn x)).getD i false = true := by
  induction L generalizing B with
  | nil => exact ⟨B,hb,by simp,by simp⟩
  | cons a l ih =>
    let B' := appendOr n B a
    have hsize : B'.size = B.size+1 := by simp [B',appendOr,Circuit.size]
    have hf : FanInTwo B' := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hb _ hg
      · simp only [List.mem_singleton] at hg
        subst g
        simp
    have hvalid (i) (hi : i ∈ l) : i < n+B'.size := by
      have h := hL i (List.mem_cons_of_mem _ hi)
      omega
    obtain ⟨C,hC,hcs,hout⟩ := ih B' hf hvalid
    refine ⟨C,hC,by simp [hcs,hsize]; omega,?_⟩
    intro x
    rw [hout]
    have hlen : (B.wires (List.ofFn x)).length = n+B.size := by
      rw [LowMergeProof.wires_eq,LowMergeProof.fold_length]
      simp [Circuit.size]
    have houtB : B'.eval (List.ofFn x) = (B.eval (List.ofFn x) ||
        (B.wires (List.ofFn x)).getD a false) := by
      simp only [B',Circuit.eval,appendWires]
      change (_ ++ [_]).getD (n+B.size) false = _
      rw [← hlen, List.getD_append_right _ _ _ _ le_rfl]
      simp
    have hp (i) (hi : i ∈ l) :
        (B'.wires (List.ofFn x)).getD i false = (B.wires (List.ofFn x)).getD i false := by
      dsimp only [B']
      rw [appendWires, List.getD_append _ _ _ _ (by rw [hlen]; exact hL i (List.mem_cons_of_mem _ hi))]
    rw [houtB, Bool.or_eq_true]
    constructor
    · rintro ((h | h) | ⟨i,hi,h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a,List.mem_cons_self,h⟩
      · exact Or.inr ⟨i,List.mem_cons_of_mem _ hi,(hp i hi).symm ▸ h⟩
    · rintro (h | ⟨i,hi,h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨i,hi,(hp i hi).symm ▸ h⟩

/-- Combining a nonempty set of outputs of a single circuit costs exactly one OR per
additional output, regardless of the sharing among those outputs. -/
theorem bundle {n : ℕ} (B : Circuit) (hb : FanInTwo B)
    (M : Finset ℕ) (hm : M.Nonempty) (r : ℕ → ℕ) (hr : ∀ j ∈ M, r j < n+B.size) :
    HasCircuitSize n (fun x => decide (∃ j ∈ M, (B.wires (List.ofFn x)).getD (r j) false = true))
      (B.size+M.card-1) := by
  classical
  obtain ⟨a,ha⟩ := hm
  let Z : Circuit := ⟨B.gates,r a⟩
  let L := ((M.erase a).toList).map r
  have hl (i) (hi : i ∈ L) : i < n+Z.size := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact hr _ (Finset.mem_of_mem_erase (Finset.mem_toList.mp hj))
  obtain ⟨C,hC,hs,he⟩ := collapse n L Z hb hl
  refine ⟨C,hC,?_,?_⟩
  · have hlen : L.length = (M.erase a).card := by simp [L]
    have hcard := Finset.card_erase_add_one ha
    change C.size ≤ Z.size + M.card - 1
    omega
  · intro x
    rw [Bool.eq_iff_iff, he, decide_eq_true_eq]
    constructor
    · rintro (ha' | ⟨i,hi,hx⟩)
      · exact ⟨a,ha,ha'⟩
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
        exact ⟨j,Finset.mem_of_mem_erase (Finset.mem_toList.mp hj),hx⟩
    · rintro ⟨j,hj,hx⟩
      by_cases eq : j = a
      · subst j
        exact Or.inl hx
      · exact Or.inr ⟨r j,List.mem_map.mpr ⟨j,Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨eq,hj⟩),rfl⟩,hx⟩

/-- Any graph satisfying the standard edge-plus-cover circuit lower bound satisfies the
core charging inequality, even for arbitrary families of implicant gates and arbitrary
sharing. The residual cover need not be a minimum cover. -/
theorem fromSizeLower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (M : Finset ℕ) (T T' : Finset (Fin n)) (hAO : IsAO2 n C)
    (hM : ∀ j ∈ M, j < C.size ∧ BelowF G C j)
    (lower : ∀ s, HasCircuitSize n (graphFun G ∅) s → G.edgeFinset.card + T.card ≤ s+1)
    (hT : IsMinCover G T)
    (resCover : (G.deleteEdges (↑(M.biUnion (gammaE G C)) : Set (Sym2 (Fin n)))).IsVertexCover ↑T') :
    (M.biUnion (gammaE G C)).card + T.card ≤ (M.biUnion (coneSet n C)).card + M.card + T'.card := by
  classical
  let D := M.biUnion (gammaE G C)
  let U := M.biUnion (coneSet n C)
  let R := G.deleteEdges (D : Set (Sym2 (Fin n)))
  let : DecidableRel R.Adj := fun u v => inferInstanceAs
    (Decidable ((G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v))
  by_cases hm : M.Nonempty
  · obtain ⟨B,r,hs,hf,hr,he⟩ := compressCones C M (fun j hj => (hM j hj).1) hAO
    let J : (Fin n → Bool) → Bool := fun x => decide (∃ j ∈ M, gateVal n C j x = true)
    have hJ : HasCircuitSize n J (U.card + M.card - 1) := by
      have hb := bundle B hf M hm r hr
      have ident : (fun x : Fin n → Bool =>
          decide (∃ j ∈ M, (B.wires (List.ofFn x)).getD (r j) false = true)) = J := by
        funext x
        rw [Bool.eq_iff_iff]
        simp only [J,decide_eq_true_eq]
        constructor <;> rintro ⟨j,hj,h⟩ <;> refine ⟨j,hj,?_⟩
        · rwa [← he j hj x]
        · rwa [he j hj x]
      rwa [ident,hs] at hb
    have reconstruct : graphFun G ∅ = fun x => graphFun R ∅ x || J x := by
      funext x
      rw [Bool.eq_iff_iff,Bool.or_eq_true]
      simpa only [J,decide_eq_true_eq] using reassemble G C M hAO.1 (fun j hj => (hM j hj).2) x
    have sub : D ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨j,_,hej⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp hej).1
    have hc : R.edgeFinset.card + D.card = G.edgeFinset.card := by
      rw [show R.edgeFinset = G.edgeFinset \ D from G.edgeFinset_deleteEdges D]
      exact Finset.card_sdiff_add_card_eq_card sub
    have hmpos : 0 < M.card := Finset.card_pos.mpr hm
    change D.card + T.card ≤ U.card + M.card + T'.card
    by_cases hR : ∃ i j, R.Adj i j
    · obtain ⟨K,hK,_,hfun,hcost⟩ := CoverCircuit.graph_upper n R T' hR (fun i j hij => resCover hij)
      have hk : HasCircuitSize n (graphFun R ∅) K.size := by
        refine ⟨K,hK,le_rfl,?_⟩
        intro x
        have h := congrFun hfun x
        simpa [graphFun,circuitFun] using h
      have h := Gap548Circuit.orSize hk hJ
      rw [← reconstruct] at h
      have hbound := lower _ h
      omega
    · have hfR (x : Fin n → Bool) : graphFun R ∅ x = false := by
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
        apply decide_eq_false
        rintro ⟨a,b,hab,_,_⟩
        exact hR ⟨a,b,hab⟩
      have eq := reconstruct
      simp only [hfR,Bool.false_or] at eq
      change graphFun G ∅ = J at eq
      rw [eq] at lower
      have hbound := lower _ hJ
      omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hm
    subst M
    simp at resCover ⊢
    exact hT.2 T' resCover

/-- The full posted bound holds on every forest, with any amount of sharing of core cones. -/
theorem forests {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (acyclic : G.IsAcyclic)
    (C : Circuit) (T T' : Finset (Fin n)) (hAO : IsAO2 n C) (hT : IsMinCover G T)
    (hR : IsMinCover (G.deleteEdges
        (↑((maximalCores G C).biUnion (gammaE G C)) : Set (Sym2 (Fin n)))) T') :
    let M := maximalCores G C
    (M.biUnion (gammaE G C)).card + T.card ≤ (M.biUnion (coneSet n C)).card + M.card + T'.card := by
  apply fromSizeLower G C _ T T' hAO ?_ ?_ hT hR.1
  · intro j hj
    have h : IsMaximalCore G C j := (Finset.mem_filter.mp hj).2
    exact ⟨h.1.1,h.1.2.1.1⟩
  · intro s hs
    by_cases he : ∃ i j, G.Adj i j
    · apply Helpers.Forest.forest_bound n T.card s G acyclic he (fun A ha => hT.2 A ha)
      have funEq : graphFun G ∅ = (fun x => decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) := by
        funext x
        simp [graphFun]
      simpa only [← funEq] using hs
    · have h0 : G = ⊥ := by
        ext i j
        simp_all
      have ht0 : T.card = 0 := by
        have hmin := hT.2 ∅ (by rw [h0]; simp [SimpleGraph.IsVertexCover])
        simpa using hmin
      rw [SimpleGraph.edgeFinset_eq_empty.mpr h0,ht0]
      simp

/-- The posted bound also holds for every cycle of length at least five. The labeling in
cyclic order matches the modulo-`n` edge function used by the repository's exact size theorem. -/
theorem cycles {n : ℕ} (hn : 5 ≤ n) (e : Fin n ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (cyc : ∀ u v, G.Adj u v ↔ ((e u).val+1)%n = (e v).val ∨ ((e v).val+1)%n = (e u).val)
    (C : Circuit) (T T' : Finset (Fin n)) (hAO : IsAO2 n C) (hT : IsMinCover G T)
    (hR : IsMinCover (G.deleteEdges
        (↑((maximalCores G C).biUnion (gammaE G C)) : Set (Sym2 (Fin n)))) T') :
    let M := maximalCores G C
    (M.biUnion (gammaE G C)).card + T.card ≤ (M.biUnion (coneSet n C)).card + M.card + T'.card := by
  apply fromSizeLower G C _ T T' hAO ?_ ?_ hT hR.1
  · intro j hj
    have h : IsMaximalCore G C j := (Finset.mem_filter.mp hj).2
    exact ⟨h.1.1,h.1.2.1.1⟩
  · intro s hs
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
    have coverSize := (hT.2 A cover).trans cardA
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
    have hrel := Gap548Circuit.relabel_size e (graphFun G ∅) s hs
    rw [agrees] at hrel
    have exactSize := (PEqualNP.MetaComplexity.L106 n s hn).mp hrel
    omega

/-- A strict violation yields an actual circuit below the standard edge-plus-cover size. -/
theorem refutationCostsLess {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T T' : Finset (Fin n)) (hAO : IsAO2 n C) (hT : IsMinCover G T)
    (hR : IsMinCover (G.deleteEdges
        (↑((maximalCores G C).biUnion (gammaE G C)) : Set (Sym2 (Fin n)))) T')
    (violates : let M := maximalCores G C
      (M.biUnion (coneSet n C)).card + M.card + T'.card <
      (M.biUnion (gammaE G C)).card + T.card) :
    ∃ (B : Circuit), FanInTwo B ∧ circuitFun n B = graphFun G ∅ ∧
      B.size + 1 < G.edgeFinset.card + T.card := by
  by_contra! h
  have lower (s) (hs : HasCircuitSize n (graphFun G ∅) s) :
      G.edgeFinset.card + T.card ≤ s+1 := by
    obtain ⟨B,hB,hs,he⟩ := hs
    have hfun : circuitFun n B = graphFun G ∅ := funext he
    have := h B hB hfun
    omega
  have bound := fromSizeLower G C (maximalCores G C) T T' hAO (fun j hj => by
    have hm : IsMaximalCore G C j := (Finset.mem_filter.mp hj).2
    exact ⟨hm.1.1,hm.1.2.1.1⟩) lower hT hR.1
  exact (Nat.not_lt_of_ge bound) violates

end CoreResidual2962
