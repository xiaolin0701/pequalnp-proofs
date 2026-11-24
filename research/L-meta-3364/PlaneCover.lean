import RectangleCost
import OutputBudget
import ExactPathBudget

namespace PlaneCover3364

open PlaneRankSamples

/-- Exactly the three conclusions of L-meta-3364. -/
abbrev Cover {N : ℕ} (I : Fin N → Fin N → Prop) (m : ℕ) : Prop :=
  ∃ A B : Fin m → Finset (Fin N),
    (∀ i p, p ∈ A i → ∀ l, l ∈ B i → I p l) ∧
    (∀ p l, I p l → ∃ i, p ∈ A i ∧ l ∈ B i) ∧
    (∑ i, ((A i).card + (B i).card)) ≤ 100*m+N

/-- Sum of gate occurrences when the chosen output is unfolded. -/
abbrev pathTotal {n : ℕ} (ops : PlaneUnfold.Steps n) (m o : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, PlaneUnfold.pathCount ops (n+m) o i

/-- This is the largest additive slack that rounding to a multiple of 100 allows. -/
theorem roundBudget {edges paths m : ℕ} (mass : edges ≤ paths+1)
    (limit : paths < 100*m + (edges-1)%100) : edges ≤ 100*m := by
  omega

/-- Orders for which the weaker assumption `paths ≤ 100*m` can lose one edge. -/
theorem endpointResidues (q : ℕ) :
    ((q^2+q+1)*(q+1)-1)%100 = 0 ↔ q%50 = 0 ∨ q%50 = 6 ∨ q%50 = 42 := by
  have expand : (q^2+q+1)*(q+1) = q*(q*q+2*q+2)+1 := by ring
  rw [expand,Nat.add_sub_cancel]
  have modular :
      q*(q*q+2*q+2) % 100 = (q%100)*((q%100)*(q%100)+2*(q%100)+2) % 100 := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  rw [modular]
  have reduce : q%50 = (q%100)%50 := by omega
  rw [reduce]
  generalize eqr : q%100 = r
  have hr : r < 100 := eqr ▸ Nat.mod_lt q (by decide)
  interval_cases r <;> decide

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

include gates in
theorem gateRules : NoTwins.steps (N+N) m W := by
  intro i hi
  obtain ⟨a,ha,b,hb,h⟩ := gates i hi
  exact ⟨a,ha,b,hb,h.imp_right (Or.imp_right (Or.imp_right And.left))⟩

include hq hN cols unique E W ho bits gates yes no in
theorem through298 (order : q ≤ 298) : Cover I m := by
  have rules := gateRules E W gates
  have large : 100 ≤ N := by nlinarith [Nat.zero_le (q^2)]
  have ex := RectangleCost.planeExchange I hq hN cols unique W ho bits rules yes no
  have h := PlaneOutputBudget.exchangeBound (n:=N+N) (m:=m) (o:=o) (by omega) W rules ho ex
  apply (RectangleCost.budget_iff I hq hN cols unique).mpr
  have sq := Nat.mul_le_mul_left N (show q+1 ≤ 299 by omega)
  omega

include hq hN cols unique E W ho bits gates yes no in
theorem pathBudget (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    (limit : pathTotal ops m o < 100*m + (N*(q+1)-1)%100) : Cover I m := by
  have mass := PlanePathBudget.pathMass I hq hN cols unique W ho bits
    (gateRules E W gates) yes no ops law
  exact (RectangleCost.budget_iff I hq hN cols unique).mpr (roundBudget mass limit)

include hq hN cols unique E W ho bits gates yes no in
theorem belowAverage100 (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    (limit : pathTotal ops m o ≤ 100*m-1) : Cover I m := by
  apply pathBudget I hq hN cols unique E W ho bits gates yes no ops law
  have mass := PlanePathBudget.pathMass I hq hN cols unique W ho bits
    (gateRules E W gates) yes no ops law
  change N*(q+1) ≤ pathTotal ops m o+1 at mass
  have size : 1 < N*(q+1) := by nlinarith [Nat.zero_le (q^2),Nat.le_mul_of_pos_right N (by omega : 0<q+1)]
  omega

include hq hN cols unique E W ho bits gates yes no in
theorem average100 (ops : PlaneUnfold.Steps (N+N)) (law : PlaneUnfold.realizes W m ops)
    (limit : pathTotal ops m o ≤ 100*m)
    (residue : q%50 ≠ 0 ∧ q%50 ≠ 6 ∧ q%50 ≠ 42) : Cover I m := by
  apply pathBudget I hq hN cols unique E W ho bits gates yes no ops law
  have h := endpointResidues q
  rw [← hN] at h
  omega

end PlaneCover3364
