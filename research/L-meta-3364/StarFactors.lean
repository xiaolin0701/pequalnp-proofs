import LeafProtocol
import StarRank
import StarCount

namespace PlaneStarFactors

open PlaneLeafProtocol

open scoped Classical in
theorem localBound {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {k d : ℕ} (a : Tiles V E k) (star : V → Finset E) (win : E → E → Fin k)
    (tile : ∀ e f i, (e∈a.row i ∧ f∈a.col i) ↔ i=win e f)
    (belongs : ∀ e, e∈star (a.color (win e e)))
    (shared : ∀ v e f, e∈star v → f∈star v → e≠f → a.color (win e f)=v)
    (regular : ∀ v, (star v).card=d) (two : 2≤d) (v : V) :
    (star v).card - (Finset.univ.filter (fun e => a.color (win e e)=v)).card +
      (if (Finset.univ.filter (fun e => a.color (win e e)=v)).Nonempty then 1 else 0) ≤
        (Finset.univ.filter (fun k => a.color k=v)).card := by
  classical
  let own := fun e => a.color (win e e)
  let S := star v
  let O := Finset.univ.filter (fun e => own e=v)
  let M := Finset.univ.filter (fun e : S => own e.val≠v)
  let K := {i : Fin k // a.color i=v}
  let left (i : K) (e : S) : ℚ := if e.val ∈ a.row i.val then 1 else 0
  let right (i : K) (f : S) : ℚ := if f.val ∈ a.col i.val then 1 else 0
  have decomp (e f : S) : (∑ i : K, left i e * right i f) =
      if e=f ∧ e∈M then 0 else 1 := by
    have one (i : K) : left i e * right i f = if i.val=win e.val f.val then 1 else 0 := by
      simp only [← tile]
      by_cases hr : e.val∈a.row i.val <;> by_cases hc : f.val∈a.col i.val <;> simp [left,right,hr,hc]
    rw [Finset.sum_congr rfl (fun i _ => one i)]
    have sum : (∑ i : K, if i.val=win e.val f.val then (1:ℚ) else 0) =
        if a.color (win e.val f.val)=v then 1 else 0 := by
      by_cases h : a.color (win e.val f.val)=v
      · let j : K := ⟨win e.val f.val,h⟩
        have eq (i : K) : i.val=win e.val f.val ↔ i=j := ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
        simp [eq,h]
      · have ne (i : K) : i.val≠win e.val f.val := fun h' => h (h' ▸ i.property)
        simp [ne,h]
    rw [sum]
    by_cases he : e=f
    · subst f
      by_cases owned : own e.val=v <;> simp [own] at owned <;> simp [M,own,owned]
    · have neq : e.val≠f.val := fun h => he (Subtype.ext h)
      simp [he,shared v e.val f.val e.property f.property neq]
  have dim : 2≤Fintype.card S := by simpa [S,regular] using two
  have bound := PlaneStarRank.factorBound M dim left right decomp
  have ownMem (x : E) (hx : own x=v) : x∈S := by
    change x∈star v
    rw [← hx]
    exact belongs x
  have subtypeOwn : Fintype.card {e : S // own e.val=v}=O.card := by
    let iso : {e : S // own e.val=v} ≃ {e : E // own e=v} :=
      { toFun := fun e => ⟨e.val.val,e.property⟩
        invFun := fun e => ⟨⟨e.val,ownMem e.val e.property⟩,e.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr iso,Fintype.card_subtype]
  have missing : M.card=S.card-O.card := by
    change (Finset.univ.filter (fun e : S => ¬own e.val=v)).card=_
    rw [←Fintype.card_subtype,Fintype.card_subtype_compl,subtypeOwn,Fintype.card_coe]
  have active : M=Finset.univ ↔ ¬O.Nonempty := by
    constructor
    · intro full ⟨e,he⟩
      have hv := (Finset.mem_filter.mp he).2
      let x : S := ⟨e,ownMem e hv⟩
      have hx : x∈M := full ▸ Finset.mem_univ _
      exact (Finset.mem_filter.mp hx).2 hv
    · intro empty
      apply Finset.eq_univ_of_forall
      intro x
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun h => empty ⟨x.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩⟩
  rw [missing] at bound
  change S.card-O.card + (if O.Nonempty then 1 else 0) ≤ _
  rw [Fintype.card_subtype] at bound
  by_cases h : O.Nonempty
  · rw [ite_eq_left h]
    rw [ite_eq_right (fun full => (active.mp full) h)] at bound
    exact bound
  · rw [ite_eq_right h]
    rw [ite_eq_left (active.mpr h)] at bound
    exact bound

open scoped Classical in
theorem count {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {k N d : ℕ} (a : Tiles V E k) (star : V → Finset E) (win : E → E → Fin k)
    (tile : ∀ e f i, (e∈a.row i ∧ f∈a.col i) ↔ i=win e f)
    (belongs : ∀ e, e∈star (a.color (win e e)))
    (shared : ∀ v e f, e∈star v → f∈star v → e≠f → a.color (win e f)=v)
    (regular : ∀ v, (star v).card=d) (vertices : Fintype.card V=2*N)
    (edges : Fintype.card E=N*d) (two : 2≤d) : N*d+N ≤ k := by
  classical
  apply (show N*d+N ≤ Fintype.card (Fin k) → N*d+N ≤ k by simp)
  exact PetersenStarCount.total N d _ a.color star regular belongs vertices edges (by omega)
    (localBound a star win tile belongs shared regular two)

end PlaneStarFactors
