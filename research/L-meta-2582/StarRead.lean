import StarProgram
import StarVectors
import FanoReadBudget

namespace PlaneStarRead
open PEqualNP.ReadK PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PlaneStar PlaneStarVectors

private def comb (S : List ℕ) (k : ℕ) (m : Bool) (A B : Vectors) :=
  PlaneStarVectors.op S k (Tree.op m) [A,B]

private def calcTree {n : ℕ} (S : List ℕ) (k : ℕ) (t : Tree n) : Vectors :=
  t.interpret (comb S k) (fun i => leafVectors S k i.val)

private theorem calc_correct {n : ℕ} (S : List ℕ) (k : ℕ) (t : Tree n) :
    (readVectors t.circuit n S k).getD t.circuit.output [] = calcTree S k t := by
  let alg (g : Gate) (xs : List Vectors) := PlaneStarVectors.op S k g.op (g.inputs.map fun i => xs.getD i [])
  let xs := (List.range n).map (leafVectors S k)
  have len : xs.length = n := by simp [xs]
  have h := Tree.run_compile t alg [] (comb S k) (by intros; rfl) xs
    (fun i => leafVectors S k i.val) (by omega) (by
      intro i
      have hi : i.val < xs.length := by simpa only [len] using i.isLt
      rw [List.getD_eq_getElem _ _ hi]
      simp [xs])
  rw [len] at h
  exact h

private theorem join_mem {n : ℕ} (S : List ℕ) (k : ℕ) (ts : List (Tree n))
    (ne : ts ≠ []) (t : Tree n) (ht : t ∈ ts) {v : List ℕ} (hv : v ∈ calcTree S k t) :
    v ∈ calcTree S k (Tree.join ts ne) := by
  have step (ls : List (Tree n)) (a : Tree n)
      (h : v ∈ calcTree S k a ∨ ∃ b ∈ ls, v ∈ calcTree S k b) :
      v ∈ calcTree S k (ls.foldl (Tree.fork false) a) := by
    induction ls generalizing a with
    | nil => simpa using h
    | cons x ls ih =>
      apply ih
      rcases h with ha | ⟨b,hb,hv⟩
      · exact Or.inl ((choice S k _ _ v).mpr (Or.inl ha))
      · rcases List.mem_cons.mp hb with eq | inRest
        · subst b; exact Or.inl ((choice S k _ _ v).mpr (Or.inr hv))
        · exact Or.inr ⟨b,inRest,hv⟩
  cases ts with
  | nil => contradiction
  | cons a ls =>
    apply step
    rcases List.mem_cons.mp ht with ht|ht
    · exact Or.inl (ht ▸ hv)
    · exact Or.inr ⟨t,ht,hv⟩

theorem edgeRead {N k : ℕ} (hk : 1 ≤ k) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hn : ∀ l, points I l ≠ []) (pos : 0 < N) {p l : Fin N} (inc : I p l) :
    readsAtMost (plane I hn pos).circuit (N+N) (setList {Fin.castAdd N p, Fin.natAdd N l}) k = true := by
  let S := setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset _)
  have listInside (a : Fin (N+N)) (ha : a ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset _)) :
      a.val ∈ S := by
    apply List.mem_map.mpr
    exact ⟨a,List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true ha⟩,rfl⟩
  have pi := listInside (Fin.castAdd N p) (by simp)
  have li := listInside (Fin.natAdd N l) (by simp)
  let v := capAdd k (indicator S (N+l.val)) (indicator S p.val)
  have vmem : v ∈ calcTree S k (plane I hn pos) := by
    apply join_mem S k _ _ (star I hn l) (List.mem_ofFn.mpr ⟨l,rfl⟩)
    apply edge
    · exact leaf S k _ li
    · apply join_mem S k _ _ (Tree.leaf (Fin.castAdd N p)) (List.mem_map.mpr ⟨p,by simpa [points] using inc,rfl⟩)
      exact leaf S k _ pi
  unfold readsAtMost
  rw [calc_correct, List.any_eq_true]
  refine ⟨v,vmem,List.all_eq_true.mpr ?_⟩
  intro a ha
  apply decide_eq_true
  exact (edge_entries S k (N+l.val) p.val (by have := p.isLt; omega) a ha).trans hk

theorem largeBudget {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (pos : 0 < N) (deg : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1)
    (C : Circuit) (budget : N*(q+2) ≤ C.size+1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N+N) D ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = decide
        (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (N+N) D 2 := by
  have sizes (l : Fin N) : (points I l).length = q+1 := by simpa [points] using deg l
  have hn (l : Fin N) : points I l ≠ [] := by intro e; have h := sizes l; rw [e] at h; simp at h
  let D := (plane I hn pos).circuit
  have sizeD := plane_count I hn pos sizes
  have exactD (z : Fin (N+N) → Bool) : circuitFun (N+N) D z = decide
        (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
    change (plane I hn pos).circuit.eval (List.ofFn z) = _
    rw [Tree.eval_circuit]
    apply Bool.eq_iff_iff.mpr
    rw [plane_value,decide_eq_true_eq]
  refine ⟨D,Tree.ao _,exactD,?_,PlaneReadBudget.readFromEdges I exactD (fun _ _ hi => edgeRead (by decide) I hn pos hi)⟩
  dsimp [D]
  omega

end PlaneStarRead
