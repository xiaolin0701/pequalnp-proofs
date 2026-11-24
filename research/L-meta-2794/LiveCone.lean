import Mathlib

namespace PlaneCone

variable {Z : Type} (W : ℕ → Set Z)

-- Choose only operands actually read by the operation. The copy and empty
-- cases have one and zero parents respectively, including at repeated operands.
theorem chooseParents {n m : ℕ}
    (gates : ∀ i < m, ∃ a < n+i, ∃ b < n+i,
      W (n+i) = W a ∪ W b ∨ W (n+i) = W a ∨ W (n+i) = ∅ ∨ W (n+i) = W a ∩ W b) :
    ∃ P : ℕ → Finset ℕ,
      (∀ g, ∀ t ∈ P g, n ≤ g ∧ g < n+m ∧ t < g) ∧ (∀ g, (P g).card ≤ 2) ∧
      (∀ g, n ≤ g → g < n+m → ∀ x y, (∀ t ∈ P g, x ∈ W t → y ∈ W t) → x ∈ W g → y ∈ W g) ∧
      (∀ g, ∀ t ∈ P g, ∀ x y, x ∉ W t → y ∈ W t → x ∈ W g → y ∈ W g) := by
  classical
  have make (g : ℕ) : ∃ T : Finset ℕ,
      (∀ t ∈ T, n ≤ g ∧ g < n+m ∧ t < g) ∧ T.card ≤ 2 ∧
      (n ≤ g → g < n+m → ∀ x y, (∀ t ∈ T, x ∈ W t → y ∈ W t) → x ∈ W g → y ∈ W g) ∧
      (∀ t ∈ T, ∀ x y, x ∉ W t → y ∈ W t → x ∈ W g → y ∈ W g) := by
    by_cases live : n ≤ g ∧ g < n+m
    · obtain ⟨a,ha,b,hb,law⟩ := gates (g-n) (by omega)
      have idx : n+(g-n)=g := by omega
      rw [idx] at ha hb law
      rcases law with law|law|law|law
      · refine ⟨{a,b},?_,Finset.card_le_two,?_,?_⟩
        · simpa [live] using And.intro ha hb
        · intro _ _ x y h; rw [law]; exact Or.imp (h a (by simp)) (h b (by simp))
        · intro t ht x y _ hy _
          rcases Finset.mem_insert.mp ht with rfl|ht
          · exact law ▸ Or.inl hy
          · exact law ▸ Or.inr (Finset.mem_singleton.mp ht ▸ hy)
      · refine ⟨{a},by simpa [live],by simp,?_,?_⟩
        · intro _ _ x y h; simpa only [law] using h a (by simp)
        · intro t ht x y _ hy _; rwa [law,← Finset.mem_singleton.mp ht]
      · refine ⟨∅,by simp,by simp,?_,by simp⟩
        simp [law]
      · refine ⟨{a,b},?_,Finset.card_le_two,?_,?_⟩
        · simpa [live] using And.intro ha hb
        · intro _ _ x y h; rw [law]; exact fun ⟨hx,hy⟩ => ⟨h a (by simp) hx,h b (by simp) hy⟩
        · intro t ht x y hx _ hg
          rw [law] at hg
          rcases Finset.mem_insert.mp ht with rfl|ht
          · exact False.elim (hx hg.1)
          · exact False.elim (hx (Finset.mem_singleton.mp ht ▸ hg.2))
    · exact ⟨∅,by simp,by simp,by intro lo hi; exact False.elim (live ⟨lo,hi⟩),by simp⟩
  choose P hP using make
  exact ⟨P,fun g => (hP g).1,fun g => (hP g).2.1,fun g => (hP g).2.2.1,fun g => (hP g).2.2.2⟩

def path (P : ℕ → Finset ℕ) (a b : ℕ) := Relation.ReflTransGen (fun t g => t ∈ P g) a b

theorem cone {n m o : ℕ} (P : ℕ → Finset ℕ)
    (earlier : ∀ g, ∀ t ∈ P g, n ≤ g ∧ g < n+m ∧ t < g) (ho : n ≤ o) (endBound : o < n+m) :
    ∃ G : Finset ℕ, o ∈ G ∧ G.card ≤ m ∧ (∀ g ∈ G, n ≤ g ∧ g ≤ o) ∧
      (∀ g ∈ G, ∀ t ∈ P g, t < g ∧ (t<n ∨ t∈G)) ∧
      (∀ g ∈ G, g ≠ o → ∃ h ∈ G, g ∈ P h) ∧
      (∀ t < n, path P t o → ∃ h ∈ G, t ∈ P h) := by
  classical
  let G := (Finset.Ico n (n+m)).filter (fun g => path P g o)
  have bounded {a b : ℕ} (h : path P a b) : a ≤ b := by
    induction h with
    | refl => exact le_rfl
    | tail hab e ih => exact ih.trans (earlier _ _ e).2.2.le
  have member {a : ℕ} : a ∈ G ↔ n ≤ a ∧ a < n+m ∧ path P a o := by
    simp [G,and_assoc]
  have next {a : ℕ} (p : path P a o) (h : a ≠ o) : ∃ b ∈ G, a ∈ P b := by
    obtain eq|⟨b,read,up⟩ := p.cases_head
    · contradiction
    · exact ⟨b,member.mpr ⟨(earlier _ _ read).1,(earlier _ _ read).2.1,up⟩,read⟩
  refine ⟨G,member.mpr ⟨ho,endBound,.refl⟩,?_,?_,?_,?_,?_⟩
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · intro g hg; exact ⟨(member.mp hg).1,bounded (member.mp hg).2.2⟩
  · intro g hg t read
    refine ⟨(earlier _ _ read).2.2,?_⟩
    by_cases h : t < n
    · exact Or.inl h
    · exact Or.inr (member.mpr ⟨by omega,(earlier _ _ read).2.2.trans (member.mp hg).2.1,
          Relation.ReflTransGen.head read (member.mp hg).2.2⟩)
  · intro g hg ne; exact next (member.mp hg).2.2 ne
  · intro t ht pt; exact next pt (by omega)

-- Each essential raw wire has a directed path to the differing output.
theorem essential {n m o a : ℕ} (P : ℕ → Finset ℕ)
    (early : ∀ g, ∀ t ∈ P g, n ≤ g ∧ g < n+m ∧ t < g)
    (order : ∀ g, n ≤ g → g < n+m → ∀ x y, (∀ t ∈ P g, x ∈ W t → y ∈ W t) → x ∈ W g → y ∈ W g)
    (endBound : o < n+m) (x y : Z) (old : x ∈ W o) (newer : y ∉ W o)
    (stable : ∀ t < n, t ≠ a → x ∈ W t → y ∈ W t) : path P a o := by
  have trace (g : ℕ) (hg : g < n+m) (yes : x ∈ W g) (no : y ∉ W g) : path P a g := by
    induction g using Nat.strong_induction_on with
    | ind g ih =>
      by_cases raw : g < n
      · by_cases e : g=a
        · subst g; exact .refl
        · exact False.elim (no (stable g raw e yes))
      · have lose : ∃ t ∈ P g, x ∈ W t ∧ y ∉ W t := by
          by_contra! h
          exact no (order g (by omega) hg x y h yes)
        obtain ⟨t,read,yt,nt⟩ := lose
        have lt := (early g t read).2.2
        exact Relation.ReflTransGen.tail (ih t lt (lt.trans hg) yt nt) read
  exact trace o endBound old newer

end PlaneCone
