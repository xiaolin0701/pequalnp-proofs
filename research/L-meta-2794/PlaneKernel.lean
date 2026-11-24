import Mathlib

namespace PlaneKernel

abbrev Edge {N : ℕ} (I : Fin N → Fin N → Prop) := {e : Fin N × Fin N // I e.1 e.2}

-- A linear combination of overlaps on the incidence edges has trivial kernel.
theorem noKernel {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (plane : N=q^2+q+1)
    (rows : ∀ p, (Finset.univ.filter (I p)).card=q+1)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (unique : ∀ p r, p≠r → ∃! l, I p l ∧ I r l) (z : Edge I → ℚ)
    (zero : ∀ e : Edge I, (∑ f : Edge I, if e.val.1=f.val.1 ∨ e.val.2=f.val.2 then z f else 0)=0) :
    ∀ e, z e=0 := by
  classical
  let A (p : Fin N) := ∑ f : Edge I, if p=f.val.1 then z f else 0
  let B (l : Fin N) := ∑ f : Edge I, if l=f.val.2 then z f else 0
  have law (e : Edge I) : z e = A e.val.1 + B e.val.2 := by
    have overlap : (∑ f : Edge I, if e.val.1=f.val.1 ∨ e.val.2=f.val.2 then z f else 0) =
        A e.val.1+B e.val.2-z e := by
      unfold A B
      rw [←Finset.sum_add_distrib]
      have self : z e = ∑ f : Edge I, if e=f then z f else 0 := by simp
      conv_rhs => rw [self,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro f _
      by_cases ep : e.val.1=f.val.1 <;> by_cases el : e.val.2=f.val.2
      · have ef : e=f := Subtype.ext (Prod.ext ep el); simp [ef]
      · have ef : e≠f := fun h => el (h ▸ rfl); simp [ep,el,ef]
      · have ef : e≠f := fun h => ep (h ▸ rfl); simp [ep,el,ef]
      · have ef : e≠f := fun h => ep (h ▸ rfl); simp [ep,el,ef]
    linarith [zero e,overlap]
  let val (p l : Fin N) : ℚ := if h : I p l then z ⟨(p,l),h⟩ else 0
  have sumGrid (F : Edge I → ℚ) : (∑ f, F f) = ∑ p, ∑ l, if h : I p l then F ⟨(p,l),h⟩ else 0 := by
    let v (u : Fin N × Fin N) : ℚ := if h : I u.1 u.2 then F ⟨u,h⟩ else 0
    let S := Finset.univ.filter (fun u : Fin N × Fin N => I u.1 u.2)
    have lift := Finset.sum_subtype (F := (inferInstance : Fintype (Edge I))) S (fun u => show u∈S ↔ I u.1 u.2 by simp [S]) v
    have hsame : (∑ f : Edge I, v f.val) = ∑ f, F f := by apply Finset.sum_congr rfl; intro f _; simp [v,f.property]
    rw [hsame] at lift
    have ext : (∑ u : Fin N × Fin N, v u) = ∑ u∈S, v u := by
      rw [←Fintype.sum_extend_by_zero S v]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : I u.1 u.2 <;> simp [S,v,h]
    rw [←lift,←ext,Fintype.sum_prod_type]
  have rowSum (p : Fin N) : A p = ∑ l, val p l := by
    unfold A
    rw [sumGrid]
    calc
      _ = ∑ t : Fin N, if p=t then ∑ l, val t l else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases eq : p=t
        · simp [eq,val]
        · simp [eq]
      _ = _ := by simp
  have colSum (l : Fin N) : B l = ∑ p, val p l := by
    unfold B
    rw [sumGrid,Finset.sum_comm]
    calc
      _ = ∑ t : Fin N, if l=t then ∑ p, val p t else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases eq : l=t
        · simp [eq,val]
        · simp [eq]
      _ = _ := by simp
  have rule (p l : Fin N) : val p l = if I p l then A p+B l else 0 := by
    by_cases h : I p l
    · simpa [val,h] using law ⟨(p,l),h⟩
    · simp [val,h]
  have point (p : Fin N) : (q:ℚ)*A p = -(∑ l, if I p l then B l else 0) := by
    have h := rowSum p
    simp_rw [rule] at h
    rw [Finset.sum_ite] at h ⊢
    simp [Finset.sum_add_distrib, rows] at h ⊢
    linarith
  have line (l : Fin N) : (q:ℚ)*B l = -(∑ p, if I p l then A p else 0) := by
    have h := colSum l
    simp_rw [rule] at h
    rw [Finset.sum_ite] at h ⊢
    simp [Finset.sum_add_distrib, cols] at h ⊢
    linarith
  have common (p r : Fin N) :
      (∑ l : Fin N, if I p l ∧ I r l then A r else 0) = (if r=p then (q:ℚ)*A p else 0) + A r := by
    rw [Finset.sum_ite]
    by_cases eq : r=p
    · subst r
      simp [rows,add_mul]
    · obtain ⟨k,hk,only⟩ := unique p r (Ne.symm eq)
      have s : (Finset.univ.filter (fun l => I p l ∧ I r l)) = {k} := by
        ext l
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
        exact ⟨only l,fun e => e ▸ hk⟩
      simp [s,eq]
  have both (p : Fin N) : (q:ℚ)*q*A p = (q:ℚ)*A p+∑ r,A r := by
    calc
      _ = -(∑ l, if I p l then (q:ℚ)*B l else 0) := by
        rw [mul_assoc,point,mul_neg,Finset.mul_sum]
        simp only [mul_ite,mul_zero]
      _ = ∑ l, ∑ r, if I p l ∧ I r l then A r else 0 := by
        simp_rw [line]
        rw [←Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro l _
        by_cases inc : I p l <;> simp [inc]
      _ = _ := by rw [Finset.sum_comm]; simp_rw [common]; simp [Finset.sum_add_distrib]
  let c : ℚ := (∑ r,A r) / ((q:ℚ)*q-q)
  have qpos : (2:ℚ) ≤ q := by exact_mod_cast hq
  have denom : (q:ℚ)*q-q ≠ 0 := by nlinarith
  have constant (p : Fin N) : A p=c := by
    apply (eq_div_iff denom).mpr
    nlinarith [both p]
  have nonempty : 0<N := by omega
  let p : Fin N := ⟨0,nonempty⟩
  have h := both p
  simp_rw [constant] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hN : (N:ℚ)=(q:ℚ)^2+q+1 := by exact_mod_cast plane
  have prod : ((2:ℚ)*q+1)*c=0 := by rw [hN] at h; linear_combination -h
  have cz : c=0 := (mul_eq_zero.mp prod).resolve_left (by positivity)
  have bz (l : Fin N) : B l=0 := by
    have h := line l
    simp_rw [constant,cz] at h
    simp at h
    exact h.resolve_left (by positivity)
  intro e
  rw [law,constant,cz,bz,add_zero]

end PlaneKernel
