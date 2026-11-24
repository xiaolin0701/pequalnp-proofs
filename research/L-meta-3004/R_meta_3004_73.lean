import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3004_73
    (normalize : ∀ (S L : List ℕ) (z : ℕ), z ∉ S → z ∈ L →
    (∀ i : Fin L.length,
      ∃ a ∈ S ++ L.take i.val, ∃ b ∈ S ++ L.take i.val,
        L.get i = (a &&& b) ∨ L.get i = (a ||| b)) →
    ∃ K : List ℕ, K.length ≤ L.length ∧ K.Nodup ∧ (∀ w ∈ K, w ∉ S) ∧ z ∈ K ∧
      ∀ i : Fin K.length,
        ∃ a ∈ S ++ K.take i.val, ∃ b ∈ S ++ K.take i.val,
          K.get i = (a &&& b) ∨ K.get i = (a ||| b))
    (residual : let B : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752] ++ [191866593364673099, 193001360500003407, 7]
    ∃ R : List ℕ, R.length ≤ 22 ∧
      (∃ r ∈ B ++ R, (r ||| 7) = 2097151) ∧
      ∀ i : Fin R.length,
        ∃ a ∈ B ++ R.take i.val, ∃ b ∈ B ++ R.take i.val,
          R.get i = (a &&& b) ∨ R.get i = (a ||| b)) :
  have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (26 : ℕ) ∧ x2.Nodup ∧ (∀ x3 ∈ x2, x3 ∉ x1) ∧ (2097151 : ℕ) ∈ x2 ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  let S : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let P : List ℕ := [191866593364673099, 193001360500003407, 7]
  let build := fun (s l : List ℕ) => ∀ i : Fin l.length,
    ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val, l.get i = (a &&& b) ∨ l.get i = (a ||| b)
  have appendBuild (s l t : List ℕ) (hl : build s l) (ht : build (s ++ l) t) : build s (l ++ t) := by
    intro i
    by_cases e : i.val < l.length
    · have h := hl ⟨i.val,e⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left e,List.take_append_of_le_length e.le] using h
    · have hi : i.val < l.length + t.length := by simpa using i.isLt
      have h := ht ⟨i.val-l.length,by omega⟩
      simpa only [List.get_eq_getElem,List.getElem_append_right (show l.length ≤ i.val by omega),
        List.take_append,List.take_of_length_le (show l.length ≤ i.val by omega),List.append_assoc] using h
  have hp : build S P := by
    intro i
    change Fin 3 at i
    fin_cases i
    · exact ⟨189297016294081033, by decide, 155696362464477250, by decide, Or.inr (by decide)⟩
    · exact ⟨191866593364673099, by decide, 183565875465490436, by decide, Or.inr (by decide)⟩
    · exact ⟨95229015649943559, by decide, 193001360500003407, by decide, Or.inl (by decide)⟩
  obtain ⟨R,hlen,⟨r,hr,hrz⟩,hb⟩ := residual
  have hR : build S (P ++ R) := appendBuild S P R hp hb
  have hlast : build (S ++ (P ++ R)) [2097151] := by
    intro i
    change Fin 1 at i
    have e : i = 0 := Fin.eq_zero i
    subst i
    refine ⟨r,?_,7,?_,Or.inr hrz.symm⟩
    · change r ∈ (S ++ (P ++ R)) ++ []
      simpa only [List.append_nil, List.append_assoc] using hr
    · apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_append_left
      decide
  let L := (P ++ R) ++ [2097151]
  have raw : build S L := appendBuild S _ _ hR hlast
  obtain ⟨K,hK,hn,hs,hz,hwell⟩ := normalize S L 2097151 (by decide) (by simp [L]) raw
  refine ⟨K,?_,hn,hs,hz,hwell⟩
  have hlenL : L.length = 3 + R.length + 1 := by simp [L,P]; omega
  omega
