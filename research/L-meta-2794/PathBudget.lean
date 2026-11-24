import FormulaPartition
import RankSamples
import UnfoldCircuit

namespace PlanePathBudget

open PlaneRankSamples PlaneFormula

-- The separating assignments force one rank-one summand per formula leaf.
theorem formulaBudget {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (rows : ∀ p, (Finset.univ.filter (I p)).card = q+1) (T : PlaneFormula.Tree (Fin (N+N)))
    (on : ∀ e : Edge I, T.eval (raw (pos I e)) = true)
    (off : ∀ f : Edge I, T.eval (raw (neg I f)) = false) :
    N*(q+1) ≤ N+N+T.leaves := by
  rw [←edgeCard I rows]
  apply formulaEdgeBound (fun e : Edge I => e.val.1) (fun e => e.val.2) ?_
    (fun e => raw (pos I e)) (fun f => raw (neg I f)) (separated I) T on off
  exact fun a b h => Subtype.ext h

-- Paths count only internal gate occurrences; any reuse of primary inputs is allowed.
theorem programBudget {q N cap m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (rows : ∀ p, (Finset.univ.filter (I p)).card=q+1) (W : ℕ → Set (Input N))
    (input : ∀ a : Fin (N+N), ∀ z, raw z a=true ↔ z ∈ W a.val)
    (ops : PlaneUnfold.Steps (N+N)) (program : PlaneUnfold.realizes W m ops) (ho : o<N+N+m)
    (paths : ∀ i < m, PlaneUnfold.pathCount ops (N+N+m) o i ≤ cap)
    (on : ∀ e : Edge I, pos I e ∈ W o) (off : ∀ f : Edge I, neg I f ∉ W o) :
    N*(q+1) ≤ N+N+cap*m+1 := by
  obtain ⟨T,size,sem⟩ := PlaneUnfold.toFormula W raw input ops program ho paths
  have positive := fun e : Edge I => (sem _).mpr (on e)
  have negative (f : Edge I) : T.eval (raw (neg I f)) = false := by
    cases h : T.eval (raw (neg I f)) with
    | false => rfl
    | true => exact False.elim (off f ((sem _).mp h))
  have h := formulaBudget I rows T positive negative
  omega

theorem goalOf99 {q N m : ℕ} (hq : 100<q) (nontrivial : 2≤N)
    (h : N*(q+1) ≤ N+N+99*m+1) : N*q≤100*m := by
  rw [Nat.mul_add, Nat.mul_one] at h
  have low := Nat.mul_le_mul_left N (show 101 ≤ q by omega)
  omega

end PlanePathBudget
