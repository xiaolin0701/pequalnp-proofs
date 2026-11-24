import ConeBound
import LiveCone
import PlaneGeometry

namespace PlaneOutputBudget

theorem exchangeBound {Z : Type} {n m o : ℕ} (hn : 2 ≤ n) (W : ℕ → Set Z)
    (rules : ∀ i < m, ∃ a < n+i, ∃ b < n+i,
      W (n+i) = W a ∪ W b ∨ W (n+i) = W a ∨ W (n+i) = ∅ ∨ W (n+i) = W a ∩ W b)
    (out : o < n+m) (ex : PlanePrivate.Exchange n o W) : 3*n ≤ 2*m+2 := by
  classical
  have other (a : ℕ) : ∃ b < n, a ≠ b := by
    by_cases a=0
    · exact ⟨1,by omega,by omega⟩
    · exact ⟨0,by omega,by omega⟩
  have go : n ≤ o := by
    by_contra! raw
    obtain ⟨a,ha,ne⟩ := other o
    obtain ⟨x,hx,_,_,no,_,_⟩ := ex a ha o raw ne.symm
    exact no hx
  obtain ⟨P,early,slots,order,rising⟩ := PlaneCone.chooseParents W rules
  obtain ⟨G,atOut,cost,bounds,top,next,first⟩ := PlaneCone.cone P early go out
  have used (w : ℕ) (hw : w ∈ Finset.range n ∪ G) (hne : w≠o) :
      (PrivateFanout2794.children G P w).Nonempty := by
    have found : ∃ g ∈ G, w ∈ P g := by
      rcases Finset.mem_union.mp hw with raw|gate
      · have lo := Finset.mem_range.mp raw
        obtain ⟨b,hb,ne⟩ := other w
        obtain ⟨x,hx,y,hy,_,_,stable⟩ := ex w lo b hb ne
        exact first w lo (PlaneCone.essential W P early order out x y hx hy stable)
      · exact next w gate hne
    obtain ⟨g,hg,hread⟩ := found
    exact ⟨g,Finset.mem_filter.mpr ⟨hg,hread⟩⟩
  have bound := PlanePrivate.coneLong top atOut bounds (fun g _ => slots g) used
    (fun g hg => order g (bounds g hg).1 ((bounds g hg).2.trans_lt out))
    (fun g _ => rising g) ex
  omega

theorem through299 {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (limit : q ≤ 299) (hN : N=q^2+q+1)
    (cols : ∀ l, Fintype.card {p // I p l} = q+1) (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (ho : o<N+N+m)
    (bits : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
    (rules : NoTwins.steps (N+N) m W)
    (pos : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (neg : ∀ y : Fin N → Bool, Fintype.card {l // y l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o) : N*q ≤ 100*m := by
  have big : 100 ≤ N := by nlinarith [Nat.zero_le (q^2)]
  have h := exchangeBound (n:=N+N) (m:=m) (o:=o) (by omega) W rules ho
    (RectangleCost.planeExchange I hq hN cols unique W ho bits rules pos neg)
  have mul := Nat.mul_le_mul_left N limit
  omega

end PlaneOutputBudget
