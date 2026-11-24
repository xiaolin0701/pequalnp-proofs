import PlaneStarFormula
import PlaneCover

namespace PlaneCover3364

open PlaneRankSamples

theorem starPathMass {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l}=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l=true)),y) ∉ W o)
    (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops) :
    N*(q+1)+N ≤ pathTotal ops m o+1 := by
  have cols (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card=q+1 := by
    simpa only [Fintype.card_subtype] using degree l
  have rows := RectangleCost.Geometry.lines_through q N I (by omega) hN cols unique
  obtain ⟨T,cost,sem⟩ := PlaneUnfold.toFormulaTotal W raw (PlanePathBudget.rawInput W bits) ops law ho
  refine (PlaneStarFormula.leaves I (by omega) hN rows cols T ?_ ?_).trans cost
  · exact fun e => (sem _).mpr (yes _ _ e.property)
  · intro f
    have h := reject I (W o) rows unique (fun _ _ hp hl =>
      SparsePlaneIncidence.wireMonotone W bits gates o ho ⟨hp,hl⟩) no f
    cases eq : T.eval (raw (neg I f)) with
    | false => rfl
    | true => exact False.elim (h ((sem _).mp eq))

/-- The rectangle conclusion holds whenever the total number of gate occurrences
    is below 100m + N, with any additional integral slack allowed by the order. -/
theorem starPathCover {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N=q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l}=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set (Input N)) (ho : o < N+N+m)
    (bits : ∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true})
    (gates : NoTwins.steps (N+N) m W)
    (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l=true)),y) ∉ W o)
    (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    (limit : pathTotal ops m o < 100*m+N+(N*(q+1)-1)%100) : Cover I m := by
  have mass := starPathMass I hq hN degree unique W ho bits gates yes no ops law
  apply (RectangleCost.budget_iff I hq hN degree unique).mpr
  omega

variable {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
  (hq : 100 < q) (hN : N=q^2+q+1) (cols : ∀ l, Fintype.card {p // I p l}=q+1)
  (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
  (E : Finset ℕ) (W : ℕ → Set (Input N)) (ho : o < N+N+m)
  (bits : ∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true})
  (gates : ∀ i < m, ∃ a < N+N+i, ∃ b < N+N+i,
    W (N+N+i)=W a ∪ W b ∨ W (N+N+i)=W a ∨ W (N+N+i)=∅ ∨
    W (N+N+i)=W a ∩ W b ∧
      (i∈E ∨ ∃ (A B : Set (Fin N → Bool)), W a=A ×ˢ Set.univ ∧ W b=Set.univ ×ˢ B))
  (yes : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
  (no : ∀ y : Fin N → Bool, Fintype.card {l // y l=true} ≤ q →
    ((fun p => decide (¬∃ l, I p l ∧ y l=true)),y) ∉ W o)

include hq hN cols unique E W ho bits gates yes no in
theorem markedStarPathMass (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops) :
    N*(q+2) ≤ 1+pathTotal ops m o := by
  have h := starPathMass I hq hN cols unique W ho bits (gateRules E W gates) yes no ops law
  rw [show N*(q+2)=N*(q+1)+N by ring, Nat.add_comm 1]
  exact h

include hq hN cols unique E W ho bits gates yes no in
/-- The posted gate hypotheses supply an operation assignment attaining this lower bound. -/
theorem hasStarPathMass : ∃ ops : PlaneUnfold.Steps (N+N), PlaneUnfold.realizes W m ops ∧
    N*(q+2) ≤ 1+pathTotal ops m o := by
  obtain ⟨ops,law⟩ := PlaneUnfold.chooseSteps W (gateRules E W gates)
  exact ⟨ops,law,markedStarPathMass I hq hN cols unique E W ho bits gates yes no ops law⟩

include hq hN cols unique E W ho bits gates yes no in
/-- For every order, the average of 100 allows N-1 additional occurrences. -/
theorem markedStarCover (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    (limit : pathTotal ops m o ≤ 100*m+N-1) : Cover I m := by
  apply starPathCover I hq hN cols unique W ho bits (gateRules E W gates) yes no ops law
  have hn : 0<N := by omega
  omega

include hq hN cols unique E W ho bits gates yes no in
theorem allAverage100 (bounded : ∃ ops : PlaneUnfold.Steps (N+N), PlaneUnfold.realizes W m ops ∧
    pathTotal ops m o ≤ 100*m) : Cover I m := by
  obtain ⟨ops,law,limit⟩ := bounded
  apply markedStarCover I hq hN cols unique E W ho bits gates yes no ops law
  have hn : 0<N := by omega
  omega

end PlaneCover3364
