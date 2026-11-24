import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]


def block (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

lemma one_outside : ∀ t : Fin 13, t ≠ 0 → 0 ∉ block t ∨ 1 ∉ block t := by
  decide

lemma primary (gs : List Gate) (o : Nat) (ho : o < 13) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs,o⟩ (List.ofFn x) = x ⟨o,ho⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD o false = _
  rw [getD_wiresFrom_lt _ _ _ (by simpa)]
  rw [List.getD_eq_getElem _ _ (by simpa)]
  exact List.getElem_ofFn (by simpa using ho)

end PEqualNP.Outside.L_meta_1570_aux
open PEqualNP.Outside.L_meta_1570_aux
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gs o _ _ correct
  have eqL : L = block := funext hL
  subst L
  have in0 : (0 : Fin 13) ∈ block 0 := by decide
  have in1 : (1 : Fin 13) ∈ block 0 := by decide
  let single (i v : Fin 13) := decide (v = i)
  have at0 : Circuit.eval ⟨gs,o 0⟩ (List.ofFn (single 0)) = true := by
    rw [correct 0 _ (Or.inl (by simp [single]))]
    exact decide_eq_true ⟨0, in0, by simp [single]⟩
  have at1 : Circuit.eval ⟨gs,o 0⟩ (List.ofFn (single 1)) = true := by
    rw [correct 0 _ (Or.inr (Or.inl (by simp [single])))]
    exact decide_eq_true ⟨1, in1, by simp [single]⟩
  refine ⟨?_, ?_, at0, at1, ?_, ?_⟩
  · by_contra! small
    rw [primary _ _ small] at at0 at1
    simp only [single, decide_eq_true_eq] at at0 at1
    have h := at0.symm.trans at1
    exact (by decide : (0 : Fin 13) ≠ 1) h
  · by_contra! large
    change (wiresFrom gs (List.ofFn (single 0))).getD (o 0) false = true at at0
    rw [List.getD_eq_default] at at0
    · contradiction
    · simpa [length_wiresFrom] using large
  · rw [correct 0 _ (Or.inr (Or.inr (fun p hp => decide_eq_true hp)))]
    simp
  · intro t ht
    rcases one_outside t ht with h | h
    · rw [correct 0 _ (Or.inl (decide_eq_true h))]
      exact decide_eq_true ⟨0,in0,decide_eq_true h⟩
    · rw [correct 0 _ (Or.inr (Or.inl (decide_eq_true h)))]
      exact decide_eq_true ⟨1,in1,decide_eq_true h⟩
