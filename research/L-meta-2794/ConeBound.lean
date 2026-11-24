import PrivateInputs
import PrivateFanout

namespace PlanePrivate

open PrivateFanout2794

-- Apply the semantic obstruction to the finite output cone and count its gates.
theorem coneBound {Z : Type} {n o : ℕ} {G : Finset ℕ} {P : ℕ → Finset ℕ} {W : ℕ → Set Z}
    (top : ∀ g ∈ G, ∀ t ∈ P g, t<g ∧ (t<n ∨ t∈G))
    (atOut : o∈G) (bounds : ∀ g∈G, n≤g ∧ g≤o) (slots : ∀ g∈G, (P g).card ≤ 2)
    (used : ∀ w ∈ Finset.range n ∪ G, w ≠ o → (children G P w).Nonempty)
    (order : Forward G P W) (rising : Rising G P W) (ex : Exchange n o W) :
    6*n ≤ 5*G.card+4 := by
  classical
  let c (a : ℕ) := if h : (children G P a).Nonempty then h.choose else 0
  have mark (a : ℕ) (h : (children G P a).card=1) : c a ∈ children G P a := by
    have hne := Finset.card_pos.mp (show 0 < (children G P a).card by omega)
    simpa only [c,dite_eq_left hne] using hne.choose_spec
  have pick (a : ℕ) (h : (children G P a).card=1) {g : ℕ} (found : g ∈ children G P a) :
      UsesOnly G P a g := by
    intro k hk ak
    exact Finset.card_le_one.mp h.le k (Finset.mem_filter.mpr ⟨hk,ak⟩) g found
  have disj : Disjoint (Finset.range n) G := by
    apply Finset.disjoint_left.mpr
    intro w hw hg
    exact (Nat.not_lt_of_le (bounds w hg).1) (Finset.mem_range.mp hw)
  have sz := fanoutBound (Finset.range n) G P o disj atOut slots
    (fun g hg t ht => (top g hg t ht).1) used c (fun a _ h => mark a h) (by
      intro a ha b hb sah sbh eq
      by_contra ne
      obtain ⟨gc,bc⟩ := Finset.mem_filter.mp (mark b sbh)
      exact distinctUsers top atOut (bounds o atOut).1 order rising ex (Finset.mem_range.mp ha)
        (Finset.mem_range.mp hb) ne (pick a sah (mark a sah)) gc bc eq) (by
      intro a ha b hb ne sah sbh smh read
      obtain ⟨gc,bc⟩ := Finset.mem_filter.mp (mark b sbh)
      exact noSuccessive top atOut (bounds o atOut).1 (fun g hg => (bounds g hg).2) order rising ex
        (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) ne (pick a sah (mark a sah))
        (pick (c a) smh (Finset.mem_filter.mpr ⟨gc,read⟩)) gc bc read)
  simpa only [Finset.card_range] using sz

end PlanePrivate

namespace PlanePrivate

open PrivateFanout2794

-- Apply the semantic obstruction to the finite output cone and count its gates.
theorem coneStrong {Z : Type} {n o : ℕ} {G : Finset ℕ} {P : ℕ → Finset ℕ} {W : ℕ → Set Z}
    (top : ∀ g ∈ G, ∀ t ∈ P g, t<g ∧ (t<n ∨ t∈G))
    (atOut : o∈G) (bounds : ∀ g∈G, n≤g ∧ g≤o) (slots : ∀ g∈G, (P g).card ≤ 2)
    (used : ∀ w ∈ Finset.range n ∪ G, w ≠ o → (children G P w).Nonempty)
    (order : Forward G P W) (rising : Rising G P W) (ex : Exchange n o W) :
    4*n ≤ 3*G.card+2 := by
  classical
  let c (a : ℕ) := if h : (children G P a).Nonempty then h.choose else 0
  have mark (a : ℕ) (h : (children G P a).card=1) : c a ∈ children G P a := by
    have hne := Finset.card_pos.mp (show 0 < (children G P a).card by omega)
    simpa only [c,dite_eq_left hne] using hne.choose_spec
  have pick (a : ℕ) (h : (children G P a).card=1) {g : ℕ} (found : g ∈ children G P a) :
      UsesOnly G P a g := by
    intro k hk ak
    exact Finset.card_le_one.mp h.le k (Finset.mem_filter.mpr ⟨hk,ak⟩) g found
  have disj : Disjoint (Finset.range n) G := by
    apply Finset.disjoint_left.mpr
    intro w hw hg
    exact (Nat.not_lt_of_le (bounds w hg).1) (Finset.mem_range.mp hw)
  have sz := fanoutStrong (Finset.range n) G P o disj atOut slots
    (fun g hg t ht => (top g hg t ht).1) used c (fun a _ h => mark a h) (by
      intro a ha b hb g hg ne sap bg
      exact distinctUsers top atOut (bounds o atOut).1 order rising ex (Finset.mem_range.mp ha)
        (Finset.mem_range.mp hb) ne (pick a sap (mark a sap)) hg bg) (by
      intro a ha b hb g hg ne sap sup ug bg
      exact noSuccessive top atOut (bounds o atOut).1 (fun i hi => (bounds i hi).2) order rising ex
        (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) ne (pick a sap (mark a sap))
        (pick (c a) sup (Finset.mem_filter.mpr ⟨hg,ug⟩)) hg bg ug)
  simpa only [Finset.card_range] using sz

end PlanePrivate

namespace PlanePrivate

open PrivateFanout2794

-- Apply the semantic obstruction to the finite output cone and count its gates.
theorem coneLong {Z : Type} {n o : ℕ} {G : Finset ℕ} {P : ℕ → Finset ℕ} {W : ℕ → Set Z}
    (top : ∀ g ∈ G, ∀ t ∈ P g, t<g ∧ (t<n ∨ t∈G))
    (atOut : o∈G) (bounds : ∀ g∈G, n≤g ∧ g≤o) (slots : ∀ g∈G, (P g).card ≤ 2)
    (used : ∀ w ∈ Finset.range n ∪ G, w ≠ o → (children G P w).Nonempty)
    (order : Forward G P W) (rising : Rising G P W) (ex : Exchange n o W) :
    3*n ≤ 2*G.card+2 := by
  classical
  let c (a : ℕ) := if h : (children G P a).Nonempty then h.choose else 0
  have mark (a : ℕ) (h : (children G P a).card=1) : c a ∈ children G P a := by
    have hne := Finset.card_pos.mp (show 0 < (children G P a).card by omega)
    simpa only [c,dite_eq_left hne] using hne.choose_spec
  have pick (a : ℕ) (h : (children G P a).card=1) {g : ℕ} (found : g ∈ children G P a) :
      UsesOnly G P a g := by
    intro k hk ak
    exact Finset.card_le_one.mp h.le k (Finset.mem_filter.mpr ⟨hk,ak⟩) g found
  have disj : Disjoint (Finset.range n) G := by
    apply Finset.disjoint_left.mpr
    intro w hw hg
    exact (Nat.not_lt_of_le (bounds w hg).1) (Finset.mem_range.mp hw)
  have sz := fanoutLong (Finset.range n) G P o disj atOut slots used c (fun a _ h => mark a h) (by
      intro a ha b hb g hg ne sap bg
      exact distinctUsers top atOut (bounds o atOut).1 order rising ex (Finset.mem_range.mp ha)
        (Finset.mem_range.mp hb) ne (pick a sap (mark a sap)) hg bg) (by
      intro a ha sap w v trace rwv b hb
      have later (i j : ℕ) (h : soleStep G P i j) : i < j ∧ UsesOnly G P i j := by
        obtain ⟨hg,access⟩ := Finset.mem_filter.mp h.1
        exact ⟨(top j hg i access).1,pick i h.2 h.1⟩
      obtain ⟨gc,ac⟩ := Finset.mem_filter.mp (mark a sap)
      exact noRawAfterChain top atOut (fun j hj => (bounds j hj).2) order rising ex
        (Finset.mem_range.mp ha) (top (c a) gc a ac).1 (pick a sap (mark a sap))
        (soleStep G P) later trace rwv (Finset.mem_filter.mp rwv.1).1 b (Finset.mem_range.mp hb))
  simpa only [Finset.card_range] using sz

end PlanePrivate
