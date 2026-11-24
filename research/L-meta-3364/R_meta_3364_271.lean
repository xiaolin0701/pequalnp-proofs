import PEqualNP.Defs

-- All primary coordinates influence the output, so a binary circuit uses at least 2N−1 gates.
-- Through order 198 this pays for the N column stars. Above that order only the gate bound remains.
theorem PEqualNP.Outside.R_meta_3364_271
    (support : ∀ (Z : Type) (n m o : ℕ) (W : ℕ → Set Z), o < n+m →
      (∀ g < m, ∃ a < n+g, ∃ b < n+g,
        W (n+g) = W a ∪ W b ∨ W (n+g) = W a ∨ W (n+g) = ∅ ∨ W (n+g) = W a ∩ W b) →
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ m+1 ∧
        ∀ x y, (∀ v ∈ S, x ∈ W v → y ∈ W v) → x ∈ W o → y ∈ W o)
    (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      199 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (m o : ℕ) (E : Finset ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
      let n := N+N
      let one := fun (a b : Fin N) => decide (b = a)
      o < n+m →
      (∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) →
      (∀ i < m, ∃ a < n+i, ∃ b < n+i, let g := W (n+i)
        g = W a ∪ W b ∨ g = W a ∨ g = ∅ ∨ g = W a ∩ W b ∧
        (i ∈ E ∨ ∃ (S T : Set (Fin N → Bool)), W a = S ×ˢ Set.univ ∧ W b = Set.univ ×ˢ T)) →
      (∀ p l, I p l → (one p,one l) ∈ W o) →
      (∀ y : Fin N → Bool, Fintype.card {l : Fin N // y l = true} ≤ q →
        ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o) →
      100*E.card < N*q → N*(q+1) ≤ 100*m) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  intro q N I inst hq hn degrees uniq m o E W ho inputs gates pos neg marks
  classical
  have bound : N*(q+1) ≤ 100*m := by
    by_cases largeq : 199 ≤ q
    · exact large q N I largeq hn degrees uniq m o E W ho inputs gates pos neg marks
    obtain ⟨S,hs,hcard,dep⟩ := support _ (N+N) m o W ho (by
      intro g hg
      obtain ⟨a,ha,b,hb,h⟩ := gates g hg
      exact ⟨a,ha,b,hb,h.imp_right (Or.imp_right (Or.imp_right And.left))⟩)
    let one := fun (a b : Fin N) => decide (b = a)
    have need (p l : Fin N) (inc : I p l) : p.val ∈ S ∧ N+l.val ∈ S := by
      let z := (one p, one l)
      have hz : z ∈ W o := pos p l inc
      constructor
      · by_contra missing
        let y := one l
        let x := fun a : Fin N => decide (¬∃ b, I a b ∧ y b = true)
        have hy : Fintype.card {b : Fin N // y b = true} ≤ q := by
          simp [y,one]; omega
        apply neg y hy (dep z (x,y) ?_ hz)
        intro v hv hx
        by_cases hsmall : v < N
        · let a : Fin N := ⟨v,hsmall⟩
          rw [(show v = a.val from rfl),(inputs a).1] at hx
          exact False.elim (missing ((congrArg Fin.val (of_decide_eq_true (show decide (a=p)=true from hx))) ▸ hv))
        · let a : Fin N := ⟨v-N,by have := Finset.mem_range.mp (hs hv); omega⟩
          have e : v=N+a.val := by dsimp [a]; omega
          rw [e,(inputs a).2] at hx ⊢
          exact hx
      · by_contra missing
        let y := fun _ : Fin N => false
        let x := fun a : Fin N => decide (¬∃ b, I a b ∧ y b = true)
        have hy : Fintype.card {b : Fin N // y b = true} ≤ q := by simp [y]
        apply neg y hy (dep z (x,y) ?_ hz)
        intro v hv hx
        by_cases hsmall : v < N
        · let a : Fin N := ⟨v,hsmall⟩
          rw [(show v = a.val from rfl),(inputs a).1]
          change decide (¬∃ b, I a b ∧ y b = true) = true
          simp [y]
        · let b : Fin N := ⟨v-N,by have := Finset.mem_range.mp (hs hv); omega⟩
          have e : v=N+b.val := by dsimp [b]; omega
          rw [e,(inputs b).2] at hx
          have eq := of_decide_eq_true (show decide (b=l)=true from hx)
          exact False.elim (missing ((e.trans (congrArg (fun i : Fin N => N+i.val) eq)) ▸ hv))
    have allBits : Finset.range (N+N) ⊆ S := by
      intro v hv
      have hlt := Finset.mem_range.mp hv
      by_cases hsmall : v < N
      · let p : Fin N := ⟨v,hsmall⟩
        have hn2 : 2 ≤ N := by nlinarith [Nat.zero_le (q^2)]
        let r : Fin N := if p.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
        have ne : p ≠ r := by
          intro e
          have eq := congrArg Fin.val e
          unfold r at eq
          split at eq
          · change p.val = 1 at eq; omega
          · change p.val = 0 at eq; contradiction
        obtain ⟨l,h,_⟩ := uniq p r ne
        exact (need p l h.1).1
      · let l : Fin N := ⟨v-N,by omega⟩
        have nonempty : Nonempty {p : Fin N // I p l} := Fintype.card_pos_iff.mp (by rw [degrees]; omega)
        obtain ⟨⟨p,h⟩⟩ := nonempty
        have eq : N+l.val = v := by dsimp [l]; omega
        exact eq ▸ (need p l h).2
    have hc := Finset.card_le_card allBits
    rw [Finset.card_range] at hc
    have hmul := Nat.mul_le_mul_left N (show q+1 ≤ 199 by omega)
    have hn100 : 100 ≤ N := by nlinarith [Nat.zero_le (q^2)]
    omega
  have enough : N ≤ m := by
    have h100 : 100 * N ≤ N * (q+1) := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left N (show 100 ≤ q+1 by omega)
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le enough
  let A : Fin (N+k) → Finset (Fin N) := Fin.addCases
    (fun l => Finset.univ.filter (fun p => I p l)) (fun _ => ∅)
  let B : Fin (N+k) → Finset (Fin N) := Fin.addCases (fun l => {l}) (fun _ => ∅)
  refine ⟨A,B,?_,?_,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left l => simp [A,B]
    | right t => simp [A,B]
  · intro p l hl
    exact ⟨Fin.castAdd k l, by simpa [A] using hl, by simp [B]⟩
  · rw [Fin.sum_univ_add]
    simpa [A,B, ← Fintype.card_subtype, degrees, Nat.mul_add] using (show N*(q+1)+N ≤ 100*(N+k)+N by omega)
