import PlaneCover
import FixedInput
import PinnedExchange
import PinIndices

namespace PlaneCover3364

open PlaneRankSamples

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
/-- Fixing a twice-read raw coordinate saves two gates and preserves all
    the pairwise exchange witnesses on the remaining coordinates. -/
theorem threeTimes : 3*N ≤ m := by
  have rules := gateRules E W gates
  have large : 3 ≤ N+N := by omega
  have ex := RectangleCost.planeExchange I hq hN cols unique W ho bits rules yes no
  have h := PlaneFixedInput.sharpen large W rules ho ex (fun a ha =>
    PlanePin.pinReadyFrom large ha W (RectangleCost.pinnedExchange I hq hN cols unique W ho bits rules yes no a ha))
  omega

include hq hN cols unique E W ho bits gates yes no in
theorem through299 (order : q ≤ 299) : Cover I m := by
  have size := threeTimes I hq hN cols unique E W ho bits gates yes no
  have bound := Nat.mul_le_mul_left N (show q+1 ≤ 300 by omega)
  apply (RectangleCost.budget_iff I hq hN cols unique).mpr
  omega

end PlaneCover3364
