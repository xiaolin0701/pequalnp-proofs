import Mathlib
import PEqualNP.Outside.L_gct_222

namespace SymmetricHook231

noncomputable section

/-- All ten coordinates of a symmetric four by four matrix. -/
def mat (u x y z a b c d e f : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![u,x,y,z], ![x,a,b,c], ![y,b,d,e], ![z,c,e,f]]

def base (u a b c d e f : ℂ) :=
  u*(a*d*f+a*e^2+b^2*f+2*b*c*e+c^2*d)

def quad (g i j k l m x y z : ℂ) :=
  g*x^2+i*y^2+j*z^2+2*k*x*y+2*l*x*z+2*m*y*z

private theorem expand (u x y z a b c d e f : ℂ) :
    Matrix.permanent (mat u x y z a b c d e f) =
      base u a b c d e f + quad (d*f+e^2) (a*f+c^2) (a*d+b^2)
        (b*f+c*e) (b*e+c*d) (a*e+b*c) x y z := by
  rw [PEqualNP.Outside.L_gct_222.perm4]
  simp [mat,base,quad]
  ring

/-- A quadratic form constant on an affine plane with nonzero coordinate sum
has all six symmetric coefficients equal. -/
private theorem quadratic (C s g i j k l m : ℂ) (nz : s≠0)
    (h : ∀ x y, C+quad g i j k l m x y (s-x-y)=24) :
    g=i ∧ g=j ∧ g=k ∧ g=l ∧ g=m := by
  have cancel (w : ℂ) (eq : s^2*w=0) : w=0 := (mul_eq_zero.mp eq).resolve_left (pow_ne_zero _ nz)
  have h1 := h s 0
  have h2 := h 0 s
  have h3 := h 0 0
  have h12 := h (s/2) (s/2)
  have h13 := h (s/2) 0
  have h23 := h 0 (s/2)
  unfold quad at h1 h2 h3 h12 h13 h23
  have gi : g=i := sub_eq_zero.mp (cancel _ (by linear_combination h1-h2))
  have gj : g=j := sub_eq_zero.mp (cancel _ (by linear_combination h1-h3))
  subst i
  subst j
  exact ⟨rfl,rfl,sub_eq_zero.mp (cancel _ (by linear_combination 2*h1-2*h12)),
    sub_eq_zero.mp (cancel _ (by linear_combination 2*h1-2*h13)),
    sub_eq_zero.mp (cancel _ (by linear_combination 2*h1-2*h23))⟩

/-- Extract the linear coefficient from the cofactor equation. -/
private theorem first (r u v : ℂ) (h : ∀ t : ℂ, 3+t*r≠0 → t*u+t^2*v=0) : u=0 := by
  have all (t : ℂ) : (3+t*r)*(t*u+t^2*v)=0 := by
    by_cases nz : 3+t*r=0
    · rw [nz,zero_mul]
    · rw [h t nz,mul_zero]
  linear_combination all 1 - (1/2)*all 2 + (1/9)*all 3

/-- The hook's coordinates are arbitrary subject to x+y+z=0. Adding any
independent symmetric direction would preserve all these translated planes. -/
theorem noExtension (u v w z a b c d e f : ℂ)
    (h : ∀ t x y : ℂ, Matrix.permanent
      (mat (1+t*u) x y (3+t*(v+w+z)-x-y) (1+t*a) (1+t*b) (1+t*c)
        (1+t*d) (1+t*e) (1+t*f))=24) :
    u=0 ∧ v+w+z=0 ∧ a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 ∧ f=0 := by
  let r := v+w+z
  have hh := fun t x y => (expand _ _ _ _ _ _ _ _ _ _).symm.trans (h t x y)
  have same (t : ℂ) (nz : 3+t*r≠0) := quadratic _ _ _ _ _ _ _ _ nz (hh t)
  have h1 : -a - 2*c + d + 2*e=0 := by
    apply first r _ (-a*f - c^2 + d*f + e^2)
    intro t ht
    linear_combination (same t ht).1
  have h2 : -a - 2*b + 2*e + f=0 := by
    apply first r _ (-a*d - b^2 + d*f + e^2)
    intro t ht
    linear_combination (same t ht).2.1
  have h3 : -b - c + d + e=0 := by
    apply first r _ (-b*f - c*e + d*f + e^2)
    intro t ht
    linear_combination (same t ht).2.2.1
  have h4 : -b - c + e + f=0 := by
    apply first r _ (-b*e - c*d + d*f + e^2)
    intro t ht
    linear_combination (same t ht).2.2.2.1
  have h5 : -a - b - c + d + e + f=0 := by
    apply first r _ (-a*e - b*c + d*f + e^2)
    intro t ht
    linear_combination (same t ht).2.2.2.2
  have h_b : b=a := by linear_combination (1/2)*h1 + (-1)*h3 + (-1/2)*h4 + (1/2)*h5
  have h_c : c=a := by linear_combination (1/2)*h2 + (-1/2)*h3 + (-1)*h4 + (1/2)*h5
  have h_d : d=a := by linear_combination (-1)*h4 + (1)*h5
  have h_e : e=a := by linear_combination (1/2)*h1 + (1/2)*h2 + (-1/2)*h3 + (-1/2)*h4
  have h_f : f=a := by linear_combination (-1)*h3 + (1)*h5
  subst b
  subst c
  subst d
  subst e
  subst f
  have bottom : a=0 := by
    by_contra nonzero
    have vanish : 1+(-a⁻¹)*a=0 := by rw [neg_mul,inv_mul_cancel₀ nonzero]; norm_num
    have test := hh (-a⁻¹) 0 0
    simp only [vanish] at test
    norm_num [base,quad] at test
  subst a
  have line (t : ℂ) : 6*(1+t*u)+2*(3+t*r)^2=24 := by
    have test := hh t 0 0
    dsimp [base,quad] at test
    dsimp [r]
    linear_combination test
  have hR : r^2=0 := by linear_combination (1/4)*(line 1)+(1/4)*(line (-1))
  have rzero : r=0 := by
    by_contra nz
    exact (pow_ne_zero _ nz) hR
  have corner : u=0 := by
    have one := line 1
    rw [rzero] at one
    linear_combination (1/6)*one
  exact ⟨corner,rzero,rfl,rfl,rfl,rfl,rfl,rfl⟩

abbrev Ambient := Fin 4 × Fin 4 → ℂ

def direction (u x y z a b c d e f : ℂ) : Ambient :=
  fun ij => mat u x y z a b c d e f ij.1 ij.2

/-- Pick the centre of the symmetric hook at coordinate 0. -/
def hook (x y : ℂ) : Ambient := direction 0 x y (-x-y) 0 0 0 0 0 0

def hookMap : (ℂ × ℂ) →ₗ[ℂ] Ambient where
  toFun v := hook v.1 v.2
  map_add' u v := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [hook,direction,mat] <;> ring
  map_smul' c u := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [hook,direction,mat] <;> ring

theorem hookDimension : Module.finrank ℂ (LinearMap.range hookMap)=2 := by
  have inj : Function.Injective hookMap := by
    intro v w eq
    exact Prod.ext (congrFun eq (0,1)) (congrFun eq (0,2))
  have dim := (LinearEquiv.ofInjective hookMap inj).finrank_eq
  simpa using dim.symm

theorem hookLevel (x y : ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+hook x y (i,j))=24 := by
  have rep : (Matrix.of fun (i j : Fin 4) => 1+hook x y (i,j))=
      mat 1 (1+x) (1+y) (1-x-y) 1 1 1 1 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hook,direction,mat] <;> ring
  rw [rep,expand]
  dsimp [base,quad]
  ring

private theorem constraint (L : Submodule ℂ Ambient) (allHook : ∀ x y, hook x y∈L)
    (level : ∀ t∈L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+t (i,j))=24)
    (u v w z a b c d e f : ℂ) (dir : direction u v w z a b c d e f∈L) :
    u=0 ∧ v+w+z=0 ∧ a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 ∧ f=0 := by
  apply noExtension
  intro t x y
  let h := hook (x-1-t*v) (y-1-t*w)
  let D := direction u v w z a b c d e f
  have member : t • D+h ∈ L := L.add_mem (L.smul_mem t dir) (allHook _ _)
  have rep : (Matrix.of fun (i j : Fin 4) => 1+(t • D+h) (i,j)) =
      mat (1+t*u) x y (3+t*(v+w+z)-x-y) (1+t*a) (1+t*b) (1+t*c)
        (1+t*d) (1+t*e) (1+t*f) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h,D,hook,direction,mat] <;> ring
  exact rep ▸ level _ member

/-- The canonical two-dimensional hook is maximal among complex linear subspaces
of symmetric matrices on the level 24 through the all-ones matrix. -/
theorem maximal (L : Submodule ℂ Ambient) (allHook : ∀ x y, hook x y∈L)
    (symmetric : ∀ t∈L, ∀ i j : Fin 4, t (i,j)=t (j,i))
    (level : ∀ t∈L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+t (i,j))=24) :
    L = LinearMap.range hookMap := by
  apply le_antisymm
  · intro t ht
    have eq : t = direction (t (0,0)) (t (0,1)) (t (0,2)) (t (0,3)) (t (1,1))
        (t (1,2)) (t (1,3)) (t (2,2)) (t (2,3)) (t (3,3)) := by
      funext ⟨i,j⟩
      fin_cases i <;> fin_cases j <;> first | rfl | exact symmetric t ht _ _
    obtain ⟨corner,sum,aa,bb,cc,dd,ee,ff⟩ := constraint L allHook level _ _ _ _ _ _ _ _ _ _ (eq ▸ ht)
    refine ⟨(t (0,1),t (0,2)),?_⟩
    change hook _ _ = t
    have last : t (0,3) = -t (0,1)-t (0,2) := by linear_combination sum
    conv_rhs => rw [eq]
    rw [corner,last,aa,bb,cc,dd,ee,ff]
    rfl
  · rintro _ ⟨v,rfl⟩
    exact allHook _ _

theorem dimensionThroughHook (L : Submodule ℂ Ambient) (allHook : ∀ x y, hook x y∈L)
    (symmetric : ∀ t∈L, ∀ i j : Fin 4, t (i,j)=t (j,i))
    (level : ∀ t∈L, Matrix.permanent (Matrix.of fun (i j : Fin 4) => 1+t (i,j))=24) :
    Module.finrank ℂ L=2 := by
  rw [maximal L allHook symmetric level,hookDimension]

end

end SymmetricHook231
