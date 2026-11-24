import Mathlib

namespace LevelSpaceFive.RepeatedThreeTwo

/-- The last sparse case of the three pure row differences argument.
The first two equations are the two mixed linear restrictions on the remaining
four-row direction. The last one comes from the two repeated-column quadrics. -/
theorem sparse_endpoint_impossible (w t s : ℂ)
    (hw : w ^ 2 + w + 1 = 0)
    (h₁ : (4 - 4 * w) * t = 4 * w / 9)
    (h₂ : -4 * w * t + 3 * s = -4 * w - 2)
    (hq : 12 * t ^ 2 + 2 * (4 + 4 * w) * t * s = -4 * w / 9) :
    False := by
  have ht : t = (w - 1) / 27 := by
    linear_combination ((w + 2) / 12) * h₁ + (t / 3 + 1 / 27) * hw
  rw [ht] at h₂
  have hs : s = -(116 * w + 58) / 81 := by
    linear_combination (1 / 3) * h₂ + (4 / 81) * hw
  rw [ht, hs] at hq
  have hz : 752 * w / 729 = 0 := by
    linear_combination hq - ((500 - 928 * w) / 2187) * hw
  have hw0 : w = 0 := by linear_combination (729 / 752) * hz
  rw [hw0] at hw
  norm_num at hw

end LevelSpaceFive.RepeatedThreeTwo
