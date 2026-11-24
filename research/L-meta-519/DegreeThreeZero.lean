import PEqualNP.MetaComplexity.Helpers.ReadersPat
import PEqualNP.MetaComplexity.Helpers.LocRes

namespace DegreeThreeZero

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Forest PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.Loc.Res SimpleGraph

/-- A constant-status reader and two more direct readers save four gates. -/
theorem threeReaders {n : ℕ} {f : (Fin (n+1) → Bool) → Bool}
    {gs : List Gate} {o : ℕ} (L : Least (n+1) f gs o) (v : Fin (n+1)) (b : Bool)
    (hnc : ∃ x y, f (Function.update x v b) ≠ f (Function.update y v b))
    {p q r : ℕ} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : Reads gs p v) (hq : Reads gs q v) (hr : Reads gs r v)
    (hc : IsC n gs v b (n+1+p)) : Drop f v b 4 gs.length := by
  have hn : ∃ x y, f x ≠ f y := by
    obtain ⟨x,y,h⟩ := hnc
    exact ⟨_,_,h⟩
  obtain ⟨j, hpj, hread, hrc⟩ := L.next v b hnc p (reads_len hp) hc
  have hqj : q ≠ j := by
    rintro rfl
    exact L.no_tri hn p q v hp hq hread
  have hrj : r ≠ j := by
    rintro rfl
    exact L.no_tri hn p r v hp hr hread
  exact L.save4 v b hnc p q r j hpq hpr (by omega) hqr hqj hrj
    (rc_input b hp) (rc_input b hq) (rc_input b hr) hrc

/-- Three incident edges and a cover repair with one vertex bound the zero-branch cost. -/
theorem potential_drop {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (v a b c : Fin n) (hv : ∀ j, G.Adj v j → j = a ∨ j = b ∨ j = c) :
    Phi1 G A ≤ Phi1 (delV G {v}) A + 4 := by
  classical
  have he := edges_le G {v} {s(v,a),s(v,b),s(v,c)} (by
    intro i j hij hi
    obtain rfl := Finset.mem_singleton.mp hi
    rcases hv j hij with rfl | rfl | rfl <;> simp)
  have ht := tau_delV G {v} {v} (fun i j _ hi => Or.inl hi)
  have hcard : ({s(v,a),s(v,b),s(v,c)} : Finset _).card ≤ 3 := Finset.card_le_three
  rw [Finset.card_singleton] at ht
  unfold Phi1
  omega

/-- In the degree-three induction, a four-gate zero drop immediately pays the step. -/
theorem closes_zero {n s : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (v a b c : Fin n) (hv : ∀ j, G.Adj v j → j = a ∨ j = b ∨ j = c) (hfree : v ∉ A)
    (hdrop : Drop (F G A) v false 4 s)
    (ih : BoundOf (HasCircuitSize n) (delV G {v}) A) : Phi1 G A ≤ s + 1 := by
  obtain ⟨t, ht, hs⟩ := hdrop
  have hf : (fun x => F G A (Function.update x v false)) = F (delV G {v}) A :=
    funext (fun x => ToolRes0_proof n G A v x hfree)
  rw [hf] at hs
  have h1 := ih t hs
  have h2 := potential_drop G A v a b c hv
  omega

end DegreeThreeZero
