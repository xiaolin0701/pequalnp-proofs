import PEqualNP.Defs

-- Every fan-in-two monotone output is monotone on a support of at most m+1 primary wires.
theorem MonotoneSupport : ∀ (Z : Type) (n m o : ℕ) (W : ℕ → Set Z), o < n+m →
      (∀ g < m, ∃ a < n+g, ∃ b < n+g,
        W (n+g) = W a ∪ W b ∨ W (n+g) = W a ∨ W (n+g) = ∅ ∨ W (n+g) = W a ∩ W b) →
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ m+1 ∧
        ∀ x y, (∀ v ∈ S, x ∈ W v → y ∈ W v) → x ∈ W o → y ∈ W o := by
  intro Z n m o W ho gates
  classical
  have reach (k : ℕ) (hk : k ≤ m) (T : Finset ℕ) (ht : ∀ u ∈ T, u < n+k) :
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ T.card+k ∧
        ∀ x y, (∀ v ∈ S, x ∈ W v → y ∈ W v) → ∀ u ∈ T, x ∈ W u → y ∈ W u := by
    induction k generalizing T with
    | zero =>
      exact ⟨T, fun u hu => Finset.mem_range.mpr (by simpa using ht u hu), by simp, fun _ _ h => h⟩
    | succ k ih =>
      let w := n+k
      by_cases hwat : w ∈ T
      · obtain ⟨a,ha,b,hb,law⟩ := gates k (by omega)
        let U := insert a (insert b (T.erase w))
        have hU : ∀ u ∈ U, u < n+k := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl|hu
          · exact ha
          rcases Finset.mem_insert.mp hu with rfl|hu
          · exact hb
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hu
          have := ht u hm
          change u ≠ n+k at hne
          omega
        obtain ⟨S, hs, hc, hdep⟩ := ih (by omega) U hU
        have c1 := Finset.card_insert_le a (insert b (T.erase w))
        have c2 := Finset.card_insert_le b (T.erase w)
        rw [Finset.card_erase_of_mem hwat] at c2
        have := Finset.card_pos.mpr ⟨w,hwat⟩
        have uc : U.card ≤ T.card+1 := by dsimp [U]; omega
        refine ⟨S,hs,by omega,?_⟩
        intro x y hxy u hu
        by_cases eq : u = w
        · subst u
          have pa := hdep x y hxy a (by simp [U])
          have pb := hdep x y hxy b (by simp [U])
          change x ∈ W (n+k) → y ∈ W (n+k)
          rcases law with h | h | h | h <;> rw [h]
          · exact Or.imp pa pb
          · exact pa
          · exact id
          · exact And.imp pa pb
        · exact hdep x y hxy u (by simp [U,eq,hu])
      · have ht' : ∀ u ∈ T, u < n+k := by
          intro u hu
          have hne : u ≠ w := fun e => hwat (e ▸ hu)
          have := ht u hu
          change u ≠ n+k at hne
          omega
        obtain ⟨S,hs,hc,hdep⟩ := ih (by omega) T ht'
        exact ⟨S,hs,by omega,hdep⟩
  obtain ⟨S,hs,hc,hdep⟩ := reach m le_rfl {o} (by simpa using ho)
  exact ⟨S,hs,by simpa [Nat.add_comm] using hc,fun x y h => hdep x y h o (by simp)⟩
