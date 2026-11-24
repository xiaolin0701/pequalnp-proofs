import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Basic

namespace PetersenExceptional

abbrev Mask := Fin 256

def has (x : Mask) (vertex : Nat) : Bool := x.val.testBit (vertex-1)

def edgeAtZero (x : Mask) : Bool :=
  ([(1,2),(2,3),(3,4),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (ℕ × ℕ)).any
    fun e => has x e.1 && has x e.2

def reachesZero (x : Mask) : Bool := (has x 1 || has x 4 || has x 5)

def sensitive (x : Mask) : Bool := !edgeAtZero x && reachesZero x

def above (x y : Mask) : Bool := x.val &&& y.val == x.val

def addNeighbor (x : Mask) (k : Nat) : Mask := ⟨(x.val ||| 2^(k-1)) % 256, by omega⟩

-- The exceptional mask 100 consists of vertices 3, 6 and 7 in the original numbering.
set_option maxHeartbeats 0 in
theorem classify : ∀ x : Mask, edgeAtZero x = false → x ≠ 100 →
  [1,4,5].any (fun k => above x (addNeighbor x k) && sensitive (addNeighbor x k)) = true := by
  decide +kernel

theorem absorber_vanishes (h k : Mask → Bool) (tail : Mask → Bool → Bool → Bool)
    (monotone_h : ∀ x y, above x y = true → h x = true → h y = true)
    (monotone_tail : ∀ x a b, tail x a false = true → tail x a b = true)
    (pin_false : ∀ x, tail x (h x) (k x) = edgeAtZero x)
    (pin_true : ∀ x, tail x true false = (edgeAtZero x || reachesZero x)) :
    ∀ x, edgeAtZero x = false → x ≠ 100 → h x = false := by
  intro x hfalse hx
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp (classify x hfalse hx)
  let y := addNeighbor x j
  have hh : above x y = true ∧ sensitive y = true := by simpa only [Bool.and_eq_true] using hj
  obtain ⟨hle, hs⟩ := hh
  change (!edgeAtZero y && reachesZero y) = true at hs
  have hh : (!edgeAtZero y) = true ∧ reachesZero y = true := by simpa only [Bool.and_eq_true] using hs
  obtain ⟨h0,h1⟩ := hh
  have hy : edgeAtZero y = false := by simpa using h0
  have ht : tail y true false = true := by rw [pin_true, h1]; simp
  cases hval : h x with
  | false => rfl
  | true =>
    have hv := monotone_h x y hle hval
    have he := pin_false y
    rw [hv,hy] at he
    have contra := monotone_tail y true (k y) ht
    simp [he] at contra

end PetersenExceptional
