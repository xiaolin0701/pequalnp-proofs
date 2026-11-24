import Mathlib

namespace LevelSpaceFive.TwoRowJoint

variable {U V : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

/-- A bilinear pairing vanishing on a mixed hyperplane whose two marginal
functionals are nonzero vanishes on the whole product. -/
theorem bilinear_zero_of_joint_hyperplane
    (f : U →ₗ[ℂ] ℂ) (g : V →ₗ[ℂ] ℂ) (B : U →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (u₁ : U) (v₁ : V) (hu₁ : f u₁ = 1) (hv₁ : g v₁ = 1)
    (h : ∀ u v, f u = g v → B u v = 0) (u : U) (v : V) : B u v = 0 := by
  have matching (x : U) (y : V) (hx : f x ≠ 0) (hy : g y ≠ 0) : B x y = 0 := by
    have heq : f ((g y) • x) = g ((f x) • y) := by simp [mul_comm]
    have hxy := h ((g y) • x) ((f x) • y) heq
    simpa [hx, hy] using hxy
  have left (x : U) (y : V) (hy : g y ≠ 0) : B x y = 0 := by
    by_cases hx : f x = 0
    · have hsum : f (x + u₁) ≠ 0 := by simp [hx, hu₁]
      have hbase : f u₁ ≠ 0 := by simp [hu₁]
      simpa [matching u₁ y hbase hy] using matching (x + u₁) y hsum hy
    · exact matching x y hx hy
  by_cases hv : g v = 0
  · have hsum : g (v + v₁) ≠ 0 := by simp [hv, hv₁]
    have hbase : g v₁ ≠ 0 := by simp [hv₁]
    simpa [left u v₁ hbase] using left u (v + v₁) hsum
  · exact left u v hv

end LevelSpaceFive.TwoRowJoint
