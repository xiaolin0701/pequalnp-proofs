import FirstGateBound

namespace Meta2796

open PEqualNP.CircuitLowerBounds
open scoped Classical

noncomputable def edgeFunction {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

def ExclusiveNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i b, i ≠ b → ∃ c, c ≠ b ∧ G.Adj i c ∧ ¬ G.Adj b c

theorem fixed_bit_sensitive {n : ℕ} {G : SimpleGraph (Fin n)}
    (hex : ExclusiveNeighbors G) {i b : Fin n} (hib : i ≠ b) (bit : Bool) :
    ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ x b = bit ∧ y b = bit ∧ edgeFunction G x ≠ edgeFunction G y := by
  classical
  obtain ⟨c, hcb, hic, hbc⟩ := hex i b hib
  let x := fun j : Fin n => decide (j = c ∨ j = b ∧ bit = true)
  let y := Function.update x i true
  have hb : x b = bit := by cases bit <;> simp [x, Ne.symm hcb]
  have hz : edgeFunction G x = false := by
    apply decide_eq_false
    rintro ⟨u,v,huv,hu,hv⟩
    rcases of_decide_eq_true hu with h | ⟨h,_⟩ <;>
      rcases of_decide_eq_true hv with k | ⟨k,_⟩ <;> subst u <;> subst v
    · exact G.loopless.irrefl _ huv
    · exact hbc huv.symm
    · exact hbc huv
    · exact G.loopless.irrefl _ huv
  have ho : edgeFunction G y = true := by
    apply decide_eq_true
    refine ⟨i, c, hic, by simp [y], ?_⟩
    simp [y, x, Ne.symm hic.ne]
  exact ⟨x,y,(fun j hj => (Function.update_of_ne hj true x).symm),hb,
    (Function.update_of_ne hib.symm true x).trans hb, by rw [hz,ho]; decide⟩

theorem graph_pair_sensitive {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : ExclusiveNeighbors G) : PairSensitive (edgeFunction G) := by
  intro a b hab op hop i
  rcases hop with rfl | rfl
  · by_cases hbi : i = b
    · obtain ⟨x,y,heq,hx,hy,hne⟩ := fixed_bit_sensitive h (hbi ▸ hab.symm) false
      exact ⟨x,y,heq,by simp [GateOp.eval,hx,hy],hne⟩
    · obtain ⟨x,y,heq,hx,hy,hne⟩ := fixed_bit_sensitive h hbi false
      exact ⟨x,y,heq,by simp [GateOp.eval,hx,hy],hne⟩
  · by_cases hbi : i = b
    · obtain ⟨x,y,heq,hx,hy,hne⟩ := fixed_bit_sensitive h (hbi ▸ hab.symm) true
      exact ⟨x,y,heq,by simp [GateOp.eval,hx,hy],hne⟩
    · obtain ⟨x,y,heq,hx,hy,hne⟩ := fixed_bit_sensitive h hbi true
      exact ⟨x,y,heq,by simp [GateOp.eval,hx,hy],hne⟩

theorem graph_sensitive {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (h : ExclusiveNeighbors G) (i : Fin n) : Sensitive (edgeFunction G) i := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have hab : a ≠ b := by intro e; have := congrArg Fin.val e; simp [a,b] at this
  obtain ⟨x,y,hxy,_,hf⟩ := graph_pair_sensitive h a b hab .and (Or.inl rfl) i
  exact ⟨x,y,hxy,hf⟩

end Meta2796
