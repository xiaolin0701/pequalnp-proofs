import Mathlib

namespace PlaneSignalCompression

abbrev Steps {Z : Type} (n m : ℕ) (W : ℕ → Set Z) :=
  ∀ g < m, ∃ a < n+g, ∃ b < n+g,
    W (n+g) = W a ∪ W b ∨ W (n+g) = W a ∨ W (n+g) = ∅ ∨ W (n+g) = W a ∩ W b

def Fresh {Z : Type} (W : ℕ → Set Z) (i : ℕ) : Prop :=
  W i ≠ ∅ ∧ ∀ j < i, W i ≠ W j

noncomputable def kept {Z : Type} (n m : ℕ) (W : ℕ → Set Z) : Finset ℕ := by
  classical
  exact (Finset.range m).filter (fun i => Fresh W (n+i))

/-- Gates that first introduce a nonempty signal suffice. The raw inputs may
    include a wire fixed to false, and the new input list may omit that wire. -/
theorem compact {Z : Type} {n r m : ℕ} (W U : ℕ → Set Z)
    (inputs : ∀ i < n, W i=∅ ∨ ∃ j < r, W i=U j)
    (gates : Steps n m W) :
    ∃ V : ℕ → Set Z, (∀ j < r, V j=U j) ∧ Steps r (kept n m W).card V ∧
      ∀ i < n+m, W i=∅ ∨ ∃ j < r+(kept n m W).card, W i=V j := by
  classical
  induction m with
  | zero => simpa [kept,Steps] using
      (show ∃ V : ℕ → Set Z, (∀ j < r, V j=U j) ∧ ∀ i < n, W i=∅ ∨ ∃ j < r, W i=V j
        from ⟨U,fun _ _ => rfl,inputs⟩)
  | succ m ih =>
    obtain ⟨V,raw,run,covered⟩ := ih (fun g hg => gates g (by omega))
    let k := (kept n m W).card
    have old (i : ℕ) (hi : i<n+m) : W i=∅ ∨ ∃ j < r+k, W i=V j := covered i hi
    by_cases fresh : Fresh W (n+m)
    · have nc : (kept n (m+1) W).card=k+1 := by
        have h : m∉kept n m W := by simp [kept]
        simp [kept,Finset.range_add_one,Finset.filter_insert,fresh,k] at h ⊢
      obtain ⟨a,ha,b,hb,h⟩ := gates m (by omega)
      have binary : W (n+m)=W a ∪ W b ∨ W (n+m)=W a ∩ W b := by
        rcases h with h|h|h|h
        · exact Or.inl h
        · exact False.elim (fresh.2 a ha h)
        · exact False.elim (fresh.1 h)
        · exact Or.inr h
      have nonA : W a≠∅ := by
        intro e
        rcases binary with h|h
        · exact fresh.2 b hb (by simpa [e] using h)
        · exact fresh.1 (by simpa [e] using h)
      have nonB : W b≠∅ := by
        intro e
        rcases binary with h|h
        · exact fresh.2 a ha (by simpa [e] using h)
        · exact fresh.1 (by simpa [e] using h)
      obtain ⟨a',ha',ea⟩ := (old a ha).resolve_left nonA
      obtain ⟨b',hb',eb⟩ := (old b hb).resolve_left nonB
      let V' : ℕ → Set Z := Function.update V (r+k) (W (n+m))
      have before (j : ℕ) (hj : j<r+k) : V' j=V j := Function.update_of_ne (by omega) _ _
      have now : V' (r+k)=W (n+m) := Function.update_self _ _ _
      rw [nc]
      refine ⟨V',fun j hj => (before j (by omega)).trans (raw j hj),?_,?_⟩
      · intro g hg
        by_cases hg' : g<k
        · obtain ⟨x,hx,y,hy,sg⟩ := run g hg'
          refine ⟨x,hx,y,hy,?_⟩
          rw [before _ (show r+g<r+k by omega), before _ (show x<r+k by omega),
            before _ (show y<r+k by omega)]
          exact sg
        · have eq : g=k := by omega
          subst g
          refine ⟨a',ha',b',hb',?_⟩
          rw [now,before _ ha',before _ hb',←ea,←eb]
          exact binary.imp_right (fun h => Or.inr (Or.inr h))
      · intro i hi
        by_cases ho : i<n+m
        · rcases old i ho with h|⟨j,hj,h⟩
          · exact Or.inl h
          · exact Or.inr ⟨j,by omega,h.trans (before j hj).symm⟩
        · have eq : i=n+m := by omega
          exact Or.inr ⟨r+k,by omega,eq ▸ now.symm⟩
    · have nc : (kept n (m+1) W).card=k := by
        simp [kept,Finset.range_add_one,Finset.filter_insert,fresh,k]
      rw [nc]
      refine ⟨V,raw,run,fun i hi => ?_⟩
      by_cases ho : i<n+m
      · exact old i ho
      · have eq : i=n+m := by omega
        subst i
        by_cases zero : W (n+m)=∅
        · exact Or.inl zero
        · obtain ⟨t,ht,e⟩ : ∃ t < n+m, W (n+m)=W t := by
            by_contra! hn
            exact fresh ⟨zero,hn⟩
          rw [e]
          exact old t ht

theorem kept_le {Z : Type} {n m : ℕ} (W : ℕ → Set Z) : (kept n m W).card ≤ m := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem dropTwo {Z : Type} {n m a b : ℕ} (W : ℕ → Set Z)
    (ha : a < m) (hb : b < m) (ne : a≠b) (da : ¬Fresh W (n+a)) (db : ¬Fresh W (n+b)) :
    (kept n m W).card+2 ≤ m := by
  classical
  have sub : insert a (insert b (kept n m W)) ⊆ Finset.range m := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl|hg
    · exact Finset.mem_range.mpr ha
    rcases Finset.mem_insert.mp hg with rfl|hg
    · exact Finset.mem_range.mpr hb
    exact (Finset.mem_filter.mp hg).1
  simpa [kept,ne,da,db,Nat.add_assoc] using Finset.card_le_card sub

end PlaneSignalCompression
