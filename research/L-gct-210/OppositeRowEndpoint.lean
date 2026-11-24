import Mathlib

namespace LevelSpaceFive.OppositeRow

def e2 (a b c d e : ℂ) : ℂ :=
  a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e

def e3 (a b c d e : ℂ) : ℂ :=
  a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e +
  b*c*d + b*c*e + b*d*e + c*d*e

def f (a b c : ℂ) : ℂ := 3*a*b*c + a*b + a*c + b*c

private lemma cancel_shared {a x y z : ℂ} (ha : a ≠ 0)
    (hy : f a x y = 0) (hz : f a x z = 0) : y = z := by
  unfold f at hy hz
  have eq : ((3*a+1)*x+a)*(y-z) = 0 := by linear_combination hy - hz
  rcases mul_eq_zero.mp eq with hx | h
  · have hax : a*x = 0 := by linear_combination hy - y*hx
    have : x = 0 := (mul_eq_zero.mp hax).resolve_left ha
    simp [this] at hx
    contradiction
  · exact sub_eq_zero.mp h

theorem singleton_partition (a b c d e : ℂ)
    (h1 : a+b+c+d+e = 5) (h2 : e2 a b c d e = -20) (h3 : e3 a b c d e = 20)
    (hbc : f a b c = 0) (hbd : f a b d = 0) (hbe : f a b e = 0)
    (hcd : f a c d = 0) (hce : f a c e = 0) (hde : f a d e = 0) : False := by
  unfold e2 at h2
  unfold e3 at h3
  by_cases ha : a = 0
  · subst a
    simp only [f, mul_zero, zero_mul, zero_add, add_zero] at hbc hbd hbe hcd hce hde
    simp [hbc, hbd, hbe, hcd, hce, hde] at h2
  · have hcb : f a c b = 0 := by simpa [f, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hbc
    have h₁ := cancel_shared ha hbc hbd
    have h₂ := cancel_shared ha hbc hbe
    have h₃ := cancel_shared ha hcb hcd
    subst d
    subst e
    subst b
    have ha' : a = 5-4*c := by linear_combination h1
    rw [ha'] at h2 h3
    have quad : c^2 - 2*c - 2 = 0 := by linear_combination -(1/10)*h2
    have hc : c = -2/3 := by linear_combination -(1/60)*(h3 + (20*c+10)*quad)
    rw [hc] at quad
    norm_num at quad

theorem pair_partition (a b c d e : ℂ)
    (h1 : a+b+c+d+e = 5) (h2 : e2 a b c d e = -20) (h3 : e3 a b c d e = 20)
    (h₁ : f a b c = 0) (h₂ : f a b d = 0) (h₃ : f a b e = 0)
    (h₄ : f c d e = 0) : False := by
  unfold f at h₁ h₂ h₃ h₄
  unfold e2 at h2
  unfold e3 at h3
  by_cases hs : 3*a*b+a+b = 0
  · have hab : a*b = 0 := by linear_combination h₁ - c*hs
    have hsum : a+b = 0 := by linear_combination hs - 3*hab
    have za : a = 0 := by
      rcases mul_eq_zero.mp hab with h | h
      · exact h
      · simpa [h] using hsum
    subst a
    have zb : b = 0 := by simpa using hsum
    subst b
    have hz : (40 : ℂ) = 0 := by linear_combination h₄ - h2 - 3*h3
    norm_num at hz
  · have hcd : (3*a*b+a+b)*(c-d) = 0 := by linear_combination h₁-h₂
    have hce : (3*a*b+a+b)*(c-e) = 0 := by linear_combination h₁-h₃
    have heqd := sub_eq_zero.mp ((mul_eq_zero.mp hcd).resolve_left hs)
    have heqe := sub_eq_zero.mp ((mul_eq_zero.mp hce).resolve_left hs)
    subst d
    subst e
    have hprod : c^2*(c+1) = 0 := by linear_combination (1/3)*h₄
    rcases mul_eq_zero.mp hprod with h | h
    · have hc : c = 0 := by simpa using h
      rw [hc] at h3
      norm_num at h3
    · have hc : c = -1 := by linear_combination h
      rw [hc] at h1 h2 h₁
      have hz : (10 : ℂ) = 0 := by linear_combination -h₁ - 2*h2 - 7*h1
      norm_num at hz

end LevelSpaceFive.OppositeRow
