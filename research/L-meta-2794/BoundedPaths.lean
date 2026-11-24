import PathBudget
import PlaneGeometry
import SparseExactness

namespace PlanePathBudget

open PlaneRankSamples

theorem rawInput {N : ℕ} (W : ℕ → Set (Input N))
    (bits : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) :
    ∀ a : Fin (N+N), ∀ z, raw z a=true ↔ z ∈ W a.val := by
  intro a
  induction a using Fin.addCases with
  | left p =>
    intro z
    simp only [raw, Fin.addCases_left, Fin.val_castAdd, (bits p).1, Set.mem_ofPred_eq]
  | right l =>
    intro z
    simp only [raw, Fin.addCases_right, Fin.val_natAdd, (bits l).2, Set.mem_ofPred_eq]

-- The tests in the desk statement already provide sufficient samples for the
-- formula lower bound. The only extra condition for the gate bound is the
-- number of times an internal gate occurs in the expanded output formula.
theorem planeProgram {q N m o cap : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o)
    (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    (paths : ∀ i < m, PlaneUnfold.pathCount ops (N+N+m) o i ≤ cap) :
    N*(q+1) ≤ N+N+cap*m+1 := by
  have rows := RectangleCost.Geometry.lines_through q N I (by omega) hN
    (fun l => by simpa only [Fintype.card_subtype] using degree l) unique
  refine programBudget I rows W (rawInput W bits) ops law ho paths ?_ ?_
  · exact fun e => yes _ _ e.property
  · apply reject I (W o) rows unique
    · intro u v hp hl
      exact SparsePlaneIncidence.wireMonotone W bits gates o ho ⟨hp,hl⟩
    · exact no

theorem bounded99 {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1)
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o)
    (bounded : ∃ ops : PlaneUnfold.Steps (N+N), PlaneUnfold.realizes W m ops ∧
      ∀ i < m, PlaneUnfold.pathCount ops (N+N+m) o i ≤ 99) : N*q ≤ 100*m := by
  obtain ⟨ops,law,paths⟩ := bounded
  exact goalOf99 hq (by nlinarith [Nat.zero_le (q^2)]) (planeProgram I hq hN degree unique W ho bits gates yes no ops law paths)

end PlanePathBudget
