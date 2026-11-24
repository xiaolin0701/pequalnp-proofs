import PEqualNP.Defs

namespace HeawoodNormalization

def build (s l : List ℕ) := ∀ i : Fin l.length,
  ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val, l.get i = (a &&& b) ∨ l.get i = (a ||| b)

def generated (s : List ℕ) (w : ℕ) := ∃ a ∈ s, ∃ b ∈ s, w = (a &&& b) ∨ w = (a ||| b)

theorem build_snoc (s l : List ℕ) (w : ℕ) :
    build s (l ++ [w]) ↔ build s l ∧ generated (s ++ l) w := by
  constructor
  · intro h
    constructor
    · intro i
      have hh := h ⟨i.val,by simp⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,List.take_append_of_le_length i.isLt.le] using hh
    · have hh := h ⟨l.length,by simp⟩
      simpa [generated,List.get_eq_getElem] using hh
  · rintro ⟨h,hw⟩ i
    by_cases hi : i.val < l.length
    · have hh := h ⟨i.val,hi⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left hi,List.take_append_of_le_length hi.le] using hh
    · have hi' := i.isLt
      simp only [List.length_append,List.length_singleton] at hi'
      have e : i.val = l.length := by omega
      rw [List.get_eq_getElem,List.getElem_append_right (by omega),List.take_append_of_le_length (by omega)]
      simpa [e,generated] using hw

theorem compact (s l : List ℕ) (h : build s l) :
    ∃ k : List ℕ, k.length ≤ l.length ∧ k.Nodup ∧ (∀ w ∈ k, w ∉ s) ∧ build s k ∧
      ∀ w ∈ s ++ l, w ∈ s ++ k := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[],by simp,by simp,by simp,h,fun _ hh => hh⟩
  | append_singleton l w ih =>
    obtain ⟨hl,hw⟩ := (build_snoc s l w).mp h
    obtain ⟨k,hk,hn,hs,hwf,hcover⟩ := ih hl
    have old : ∀ z ∈ s ++ (l ++ [w]), z ∈ s ++ k ∨ z = w := by
      intro z hz
      rcases List.mem_append.mp (List.append_assoc s l [w] ▸ hz : z ∈ (s ++ l) ++ [w]) with h | h
      · exact Or.inl (hcover _ h)
      · exact Or.inr (by simpa using h)
    by_cases seen : w ∈ s ++ k
    · refine ⟨k,by simp; omega,hn,hs,hwf,?_⟩
      intro z hz
      rcases old z hz with hh | rfl
      · exact hh
      · exact seen
    · have nws : w ∉ s := fun he => seen (List.mem_append_left _ he)
      have nwk : w ∉ k := fun he => seen (List.mem_append_right _ he)
      refine ⟨k ++ [w],by simp; omega,?_,?_,?_,?_⟩
      · simp [List.nodup_append,hn]
        rintro a ha rfl
        exact nwk ha
      · intro z hz
        rcases List.mem_append.mp hz with hh | hh
        · exact hs z hh
        · simpa only [List.mem_singleton.mp hh] using nws
      · apply (build_snoc s k w).mpr
        obtain ⟨a,ha,b,hb,hop⟩ := hw
        exact ⟨hwf,a,hcover _ ha,b,hcover _ hb,hop⟩
      · intro z hz
        rw [← List.append_assoc]
        rcases old z hz with hh | rfl
        · exact List.mem_append_left _ hh
        · simp

theorem normalization : ∀ (S L : List ℕ) (z : ℕ), z ∉ S → z ∈ L →
    (∀ i : Fin L.length,
      ∃ a ∈ S ++ L.take i.val, ∃ b ∈ S ++ L.take i.val,
        L.get i = (a &&& b) ∨ L.get i = (a ||| b)) →
    ∃ K : List ℕ, K.length ≤ L.length ∧ K.Nodup ∧ (∀ w ∈ K, w ∉ S) ∧ z ∈ K ∧
      ∀ i : Fin K.length,
        ∃ a ∈ S ++ K.take i.val, ∃ b ∈ S ++ K.take i.val,
          K.get i = (a &&& b) ∨ K.get i = (a ||| b) := by
  intro S L z hzS hzL h
  obtain ⟨K,hlen,hn,hS,hg,cover⟩ := compact S L h
  exact ⟨K,hlen,hn,hS,(List.mem_append.mp (cover z (List.mem_append_right _ hzL))).resolve_left hzS,hg⟩

end HeawoodNormalization
