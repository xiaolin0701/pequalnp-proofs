import Mathlib
import PEqualNP.Outside.L_gct_222

namespace SymmetricLevel231

/-- A symmetric rank-one direction cannot lie entirely on the permanent level. -/
theorem noOuterSquare (v : Fin 4 → ℂ)
    (h : ∀ t : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+t*v i*v j)=24) :
    v=0 := by
  let a := v 0
  let b := v 1
  let c := v 2
  let d := v 3
  let e₁ := a+b+c+d
  let e₂ := a*b+a*c+a*d+b*c+b*d+c*d
  let e₃ := a*b*c+a*b*d+a*c*d+b*c*d
  let e₄ := a*b*c*d
  have coefficients (t : ℂ) :
      6*t*e₁^2+4*t^2*e₂^2+6*t^3*e₃^2+24*t^4*e₄^2=0 := by
    have ht := h t
    rw [PEqualNP.Outside.L_gct_222.perm4] at ht
    simp only [Matrix.of_apply] at ht
    dsimp [e₁,e₂,e₃,e₄,a,b,c,d]
    linear_combination ht
  have fromSquare (x : ℂ) (zero : x^2=0) : x=0 := by
    by_contra nz
    exact (pow_ne_zero _ nz) zero
  have h1 : e₁=0 := fromSquare _ (by linear_combination (1/9)*(coefficients (1)) + (-1/9)*(coefficients (-1)) + (-1/72)*(coefficients (2)) + (1/72)*(coefficients (-2)))
  have h2 : e₂=0 := fromSquare _ (by linear_combination (1/6)*(coefficients (1)) + (1/6)*(coefficients (-1)) + (-1/96)*(coefficients (2)) + (-1/96)*(coefficients (-2)))
  have h3 : e₃=0 := fromSquare _ (by linear_combination (-1/36)*(coefficients (1)) + (1/36)*(coefficients (-1)) + (1/72)*(coefficients (2)) + (-1/72)*(coefficients (-2)))
  have h4 : e₄=0 := fromSquare _ (by linear_combination (-1/144)*(coefficients (1)) + (-1/144)*(coefficients (-1)) + (1/576)*(coefficients (2)) + (1/576)*(coefficients (-2)))
  have polynomial (x : ℂ) : x^4=(x-a)*(x-b)*(x-c)*(x-d) := by
    calc
      _ = x^4-e₁*x^3+e₂*x^2-e₃*x+e₄ := by rw [h1,h2,h3,h4]; ring
      _ = _ := by dsimp [e₁,e₂,e₃,e₄]; ring
  funext i
  by_contra nz
  apply (pow_ne_zero 4 nz)
  rw [polynomial]
  fin_cases i <;> simp [a,b,c,d]

/-- Symmetry makes the two factors proportional, so the same obstruction holds
for an arbitrary outer product. -/
theorem noSymmetricOuter (v w : Fin 4 → ℂ) (sym : ∀ i j, v i*w j=v j*w i)
    (h : ∀ t : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+t*v i*w j)=24) :
    v=0 ∨ w=0 := by
  by_cases hv : v=0
  · exact Or.inl hv
  · obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by
      by_contra! z
      exact hv (funext z)
    let k := w i/v i
    have hw (j) : w j=k*v j := by
      dsimp [k]
      field_simp [hi]
      linear_combination sym i j
    by_cases hk : k=0
    · exact Or.inr (funext fun j => by simpa [hk] using hw j)
    · apply False.elim
      apply hv
      apply noOuterSquare
      intro t
      have eq : (Matrix.of fun (l j : Fin 4) => 1+(t/k)*v l*w j)=
          Matrix.of (fun (l j : Fin 4) => 1+t*v l*v j) := by
        ext l j
        simp only [Matrix.of_apply, hw j]
        field_simp [hk]
      rw [←eq]
      exact h _

/-- Every nonzero symmetric matrix whose whole line stays on the level has
ordinary matrix rank at least two. -/
theorem rankAtLeastTwo (A : Matrix (Fin 4) (Fin 4) ℂ) (nonzero : A≠0)
    (symmetric : ∀ i j, A i j=A j i)
    (level : ∀ t : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+t*A i j)=24) :
    2≤A.rank := by
  by_contra! small
  obtain ⟨p,q,nz⟩ : ∃ p q, A p q≠0 := by
    by_contra! zero
    exact nonzero (Matrix.ext zero)
  have minors (i j : Fin 4) : A p q*A i j=A p j*A i q := by
    let B := A.submatrix (![p,i] : Fin 2 → Fin 4) (![q,j] : Fin 2 → Fin 4)
    have hB : B.rank ≤ A.rank := A.rank_submatrix_le _ _
    have vanish : B.det=0 := by
      by_contra hn
      have deg := Matrix.rank_of_det_ne_zero hn
      simp only [Fintype.card_fin] at deg
      omega
    change (A.submatrix _ _).det=0 at vanish
    rw [Matrix.det_fin_two] at vanish
    exact sub_eq_zero.mp vanish
  let v := fun i => A i q
  let w := fun j => A p j / A p q
  have factor (i j) : A i j=v i*w j := by
    dsimp [v,w]
    field_simp [nz]
    linear_combination minors i j
  have one := noSymmetricOuter v w (fun i j => (factor i j).symm.trans ((symmetric i j).trans (factor j i))) (by
    intro t
    have eq : (Matrix.of fun (i j : Fin 4) => 1+t*v i*w j)=
        Matrix.of (fun (i j : Fin 4) => 1+t*A i j) := by
      ext i j
      simp only [Matrix.of_apply,factor i j,mul_assoc]
    rw [eq]
    exact level _)
  rcases one with z|z
  · exact nz (congrFun z p)
  · have h := congrFun z q
    change A p q/A p q=0 at h
    rw [div_self nz] at h
    exact one_ne_zero h

end SymmetricLevel231

