import BoundedPaths
import FullRankFactor
import PlaneKernel

namespace PlanePathBudget

open PlaneRankSamples PlaneFormula

-- Edge columns alone give full rank. No samples with q+1 activated lines are needed.
theorem exactFormula {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N=q^2+q+1) (rows : ∀ p, (Finset.univ.filter (I p)).card=q+1)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (T : PlaneFormula.Tree (Fin (N+N))) (on : ∀ e : Edge I, T.eval (raw (pos I e))=true)
    (off : ∀ f : Edge I, T.eval (raw (neg I f))=false) : N*(q+1)≤T.leaves := by
  classical
  let R (e f : Edge I) := e.val.1=f.val.1 ∨ e.val.2=f.val.2
  have part := formulaPartition R (fun e => raw (pos I e)) (fun e => raw (neg I e))
    (separated I) T Set.univ Set.univ (fun e _ => on e) (fun f _ => off f)
  have decomp : Factored T.leaves (fun e f => if R e f then 1 else 0) := by
    obtain ⟨A,B,h⟩ := part
    exact ⟨A,B,fun e f => by simpa only [mask,Set.mem_univ,true_and,ite_true] using h e f⟩
  rw [←edgeCard I rows]
  exact card_le_factors R decomp (PlaneKernel.noKernel I hq hN rows cols unique)

theorem pathMass {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l}=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l=true)),y) ∉ W o)
    (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    : N*(q+1) ≤ (∑ i ∈ Finset.range m, PlaneUnfold.pathCount ops (N+N+m) o i)+1 := by
  have cols (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card=q+1 := by
    simpa only [Fintype.card_subtype] using degree l
  have rows := RectangleCost.Geometry.lines_through q N I (by omega) hN cols unique
  obtain ⟨T,cost,sem⟩ := PlaneUnfold.toFormulaTotal W raw (rawInput W bits) ops law ho
  refine (exactFormula I (by omega) hN rows cols unique T ?_ ?_).trans cost
  · exact fun e => (sem _).mpr (yes _ _ e.property)
  · intro f
    have h := reject I (W o) rows unique (fun _ _ hp hl =>
      SparsePlaneIncidence.wireMonotone W bits gates o ho ⟨hp,hl⟩) no f
    cases eq : T.eval (raw (neg I f)) with
    | false => rfl
    | true => exact False.elim (h ((sem _).mp eq))

theorem exactProgram {q N m o cap : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l}=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l=true)),y) ∉ W o)
    (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    (paths : ∀ i < m, PlaneUnfold.pathCount ops (N+N+m) o i ≤ cap) :
    N*(q+1) ≤ cap*m+1 := by
  have mass := pathMass I hq hN degree unique W ho bits gates yes no ops law
  have counted := Finset.sum_le_sum (s := Finset.range m)
    (fun i hi => paths i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at counted
  change (∑ i ∈ Finset.range m, PlaneUnfold.pathCount ops (N+N+m) o i) ≤ m*cap at counted
  exact mass.trans (Nat.add_le_add_right (by simpa only [Nat.mul_comm m cap] using counted) 1)

theorem bounded100 {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l}=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l=true)),y) ∉ W o)
    (bounded : ∃ ops : PlaneUnfold.Steps (N+N), PlaneUnfold.realizes W m ops ∧
      ∀ i < m, PlaneUnfold.pathCount ops (N+N+m) o i ≤ 100) : N*q≤100*m := by
  obtain ⟨ops,law,paths⟩ := bounded
  have bound := exactProgram I hq hN degree unique W ho bits gates yes no ops law paths
  rw [Nat.mul_add,Nat.mul_one] at bound
  omega

theorem boundedAverage100 {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l}=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l=true)),y) ∉ W o)
    (bounded : ∃ ops : PlaneUnfold.Steps (N+N), PlaneUnfold.realizes W m ops ∧
      (∑ i ∈ Finset.range m, PlaneUnfold.pathCount ops (N+N+m) o i) ≤ 100*m) : N*q≤100*m := by
  obtain ⟨ops,law,paths⟩ := bounded
  have bound := pathMass I hq hN degree unique W ho bits gates yes no ops law
  rw [Nat.mul_add,Nat.mul_one] at bound
  omega

end PlanePathBudget
