import PEqualNP.MetaComplexity.L649
import PEqualNP.MetaComplexity.Helpers.LineDegTest
import PinCircuit
import PinnedNonedge

namespace Meta606RangeTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PinCircuit

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def onPoints (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun x => z (Fin.castAdd N x) = true

def onLines (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun y => z (Fin.natAdd N y) = true

def pointPin (p l x : Fin N) : Option Bool :=
  if x = p then some true else if I x l then some false else none

def linePin (p l y : Fin N) : Option Bool :=
  if y = l then some true else if I p y then some false else none

def encoding (p l : Fin N) (i : ℕ) : Option Bool :=
  if h : i < N+N then Fin.addCases (pointPin I p l) (linePin I p l) ⟨i,h⟩ else none

private theorem point_value (p l x : Fin N) (z : Fin (N+N) → Bool) :
    pinInput (encoding I p l) z (Fin.castAdd N x) =
      (pointPin I p l x).getD (z (Fin.castAdd N x)) := by
  unfold pinInput encoding
  rw [dif_pos (Fin.castAdd N x).isLt]
  change (Fin.addCases (motive := fun _ : Fin (N+N) => Option Bool) (pointPin I p l) (linePin I p l) (Fin.castAdd N x)).getD _ = _
  rw [Fin.addCases_left]

private theorem line_value (p l y : Fin N) (z : Fin (N+N) → Bool) :
    pinInput (encoding I p l) z (Fin.natAdd N y) =
      (linePin I p l y).getD (z (Fin.natAdd N y)) := by
  unfold pinInput encoding
  rw [dif_pos (Fin.natAdd N y).isLt]
  change (Fin.addCases (motive := fun _ : Fin (N+N) => Option Bool) (pointPin I p l) (linePin I p l) (Fin.natAdd N y)).getD _ = _
  rw [Fin.addCases_right]

private theorem points_eq (p l : Fin N) (z : Fin (N+N) → Bool) :
    onPoints (pinInput (encoding I p l) z) = pinPoints I p l (onPoints z) := by
  ext x
  simp only [onPoints, Finset.mem_filter, Finset.mem_univ, true_and, pinPoints,
    Finset.mem_insert, point_value]
  by_cases hp : x = p <;> by_cases hxl : I x l <;> simp [pointPin, hp, hxl]

private theorem lines_eq (p l : Fin N) (z : Fin (N+N) → Bool) :
    onLines (pinInput (encoding I p l) z) = pinLines I p l (onLines z) := by
  ext y
  simp only [onLines, Finset.mem_filter, Finset.mem_univ, true_and, pinLines,
    Finset.mem_insert, line_value]
  by_cases hl : y = l <;> by_cases hpy : I p y <;> simp [linePin, hl, hpy]

theorem bounded_unsafe_factor (hrect : NoRectangle I) (D : Circuit)
    (hm : Monotone2 D) (hd : HasLineDegree (N+N) (Finset.Ico N (N+N)) D 2)
    (A : Finset (Fin N) → Finset (Fin N) → Prop)
    (hmono : ∀ X X' Y Y', X ⊆ X' → Y ⊆ Y' → A X Y → A X' Y')
    (hout : ∀ z : Fin (N+N) → Bool,
      (A (onPoints z) (onLines z) ∧ circuitFun (N+N) D z = true) ↔
      hit I (onPoints z) (onLines z))
    (p l : Fin N) (hne : ¬ I p l) (haccept : A {p} {l}) :
    (incidences I).card ≤ 48*(D.size+2) + 6*N := by
  classical
  let pin := encoding I p l
  let C := restrict (N+N) pin D
  let R := residual I p l
  letI : DecidableRel R := fun x y => inferInstanceAs (Decidable (I x y ∧ ¬ I x l ∧ ¬ I p y))
  have hr : NoRectangle R := by
    intro u u' v v' hp' hl' he
    exact hrect u u' v v' hp' hl' ⟨he.1.1, he.2.1.1, he.2.2.1.1, he.2.2.2.1⟩
  have heq : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ u v : Fin N, R u v ∧ z (Fin.castAdd N u) = true ∧ z (Fin.natAdd N v) = true := by
    intro z
    have hp' : A (onPoints (pinInput pin z)) (onLines (pinInput pin z)) := by
      rw [points_eq, lines_eq]
      apply hmono _ _ _ _ _ _ haccept
      · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
      · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    have hcalc : circuitFun (N+N) C z = circuitFun (N+N) D (pinInput pin z) :=
      restrict_eval (N+N) pin D z
    have hwith : circuitFun (N+N) D (pinInput pin z) = true ↔
        A (onPoints (pinInput pin z)) (onLines (pinInput pin z)) ∧
        circuitFun (N+N) D (pinInput pin z) = true := ⟨fun h => ⟨hp',h⟩, And.right⟩
    rw [hcalc, hwith, hout, points_eq, lines_eq, hit_after_pins I p l hne]
    simp only [hit, onPoints, onLines, Finset.mem_filter, Finset.mem_univ, true_and, R]
    aesop
  have hrbound := PEqualNP.MetaComplexity.L649 N R C hr (restrict_mono _ _ _ hm)
    (le_trans (restrict_degree _ _ _ _) hd) heq
  have hcount : (incidences R).card ≤ 48*C.size+2*N := hrbound
  have hsize : C.size = D.size+2 := restrict_size _ _ _
  have hloss := loss_bound I hrect p l
  change (incidences I).card ≤ (incidences R).card+4*N at hloss
  omega


def assignment {N : ℕ} (X Y : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun x => decide (x ∈ X)) (fun y => decide (y ∈ Y))

private theorem assignment_sets (z : Fin (N+N) → Bool) : assignment (onPoints z) (onLines z) = z := by
  funext i
  induction i using Fin.addCases with
  | left u => simp [assignment, onPoints]
  | right v => rw [assignment, Fin.addCases_right]; simp [onLines]

theorem actual_circuit_factors (hrect : NoRectangle I) (A B : Circuit)
    (ha : Monotone2 A) (hb : Monotone2 B)
    (hdeg : HasLineDegree (N+N) (Finset.Ico N (N+N)) B 2)
    (hout : ∀ z : Fin (N+N) → Bool,
      (circuitFun (N+N) A z = true ∧ circuitFun (N+N) B z = true) ↔
      hit I (onPoints z) (onLines z))
    (p l : Fin N) (hne : ¬ I p l)
    (haccept : circuitFun (N+N) A (assignment {p} {l}) = true) :
    (incidences I).card ≤ 48*(B.size+2)+6*N := by
  let f := fun X Y : Finset (Fin N) => circuitFun (N+N) A (assignment X Y) = true
  apply bounded_unsafe_factor I hrect B hb hdeg f _ _ p l hne haccept
  · intro X X' Y Y' hx hy hf
    have hmono : ∀ g ∈ A.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      simpa using (ha g hg).1
    apply LineDegTest.W_mono A.gates hmono (List.ofFn (assignment X Y)) (List.ofFn (assignment X' Y')) (by simp) _ A.output hf
    intro i hi
    rw [LineDegTest.ofFn_getD] at hi ⊢
    by_cases h : i < N+N
    · rw [dif_pos h] at hi ⊢
      generalize he : (⟨i,h⟩ : Fin (N+N)) = k at hi ⊢
      induction k using Fin.addCases with
      | left u =>
        simpa [assignment] using hx (by simpa [assignment] using hi : u ∈ X)
      | right v =>
        rw [assignment, Fin.addCases_right] at hi ⊢
        simpa using hy (by simpa using hi : v ∈ Y)
    · simp [h] at hi
  · intro z
    simpa [f, assignment_sets] using hout z

end Meta606RangeTwo
