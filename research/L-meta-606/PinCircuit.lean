import PEqualNP.Defs.LineDegree
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD

namespace Meta606RangeTwo.PinCircuit

open PEqualNP.CircuitLowerBounds

def idx (n : ℕ) (pin : ℕ → Option Bool) (i : ℕ) : ℕ :=
  if i < n then match pin i with | none => i | some false => n | some true => n+1
  else i+2

def copyGate (n : ℕ) (pin : ℕ → Option Bool) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (idx n pin)⟩

def restrict (n : ℕ) (pin : ℕ → Option Bool) (D : Circuit) : Circuit :=
  ⟨[{op := .or, inputs := []}, {op := .and, inputs := []}] ++ D.gates.map (copyGate n pin),
    idx n pin D.output⟩

theorem restrict_size (n : ℕ) (pin : ℕ → Option Bool) (D : Circuit) :
    (restrict n pin D).size = D.size + 2 := by simp [Circuit.size, restrict] <;> omega

theorem restrict_mono (n : ℕ) (pin : ℕ → Option Bool) (D : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 D) :
    PEqualNP.MetaComplexity.Monotone2 (restrict n pin D) := by
  intro g hg
  simp only [restrict, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_map] at hg
  rcases hg with rfl | rfl | ⟨g, hg, rfl⟩
  · simp
  · simp
  · simpa [copyGate] using hm g hg

private theorem cons_end_get {α : Type*} (s : List α) (u z : α) (i : ℕ) :
    (s ++ [u]).getD i z = if i = s.length then u else s.getD i z := by
  by_cases he : i = s.length
  · subst i
    simp [List.getD_append_right]
  by_cases hl : i < s.length
  · rw [if_neg he, List.getD_append s [u] z i hl]
  · have hgt : s.length < i := by omega
    rw [if_neg he, List.getD_eq_default (s++[u]) z (by simp; omega), List.getD_eq_default s z (by omega)]

private theorem bridge {α : Type*} (rel : α → α → Prop) (n : ℕ) (pin : ℕ → Option Bool)
    (s d : List α) (x y bad : α) (hbase : n ≤ s.length) (hlen : d.length = s.length+2)
    (hold : ∀ i, rel (d.getD (idx n pin i) bad) (s.getD i bad)) (hxy : rel y x) :
    ∀ i, rel ((d++[y]).getD (idx n pin i) bad) ((s++[x]).getD i bad) := by
  intro i
  have hiff : idx n pin i = d.length ↔ i = s.length := by
    by_cases hi : i < n
    · have hi' : i ≠ s.length := by omega
      unfold idx
      rw [if_pos hi]
      cases h : pin i with
      | none => simp; omega
      | some b => cases b <;> simp <;> omega
    · simp [idx, hi, hlen]
  rw [cons_end_get, cons_end_get]
  by_cases he : i = s.length
  · rw [if_pos he, if_pos (hiff.mpr he)]
    exact hxy
  · rw [if_neg he, if_neg (fun h => he (hiff.mp h))]
    exact hold i

private def evstep (s : List Bool) (g : Gate) : List Bool :=
  s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]

private theorem fold_ev (n : ℕ) (pin : ℕ → Option Bool) (gs : List Gate)
    (s d : List Bool) (hn : n ≤ s.length) (hlen : d.length = s.length+2)
    (h : ∀ i, d.getD (idx n pin i) false = s.getD i false) :
    ∀ i, ((gs.map (copyGate n pin)).foldl evstep d).getD (idx n pin i) false =
      (gs.foldl evstep s).getD i false := by
  induction gs generalizing s d with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [evstep]; omega
    · simp [evstep, hlen] <;> omega
    · apply bridge Eq n pin s d _ _ false hn hlen h
      simp only [copyGate, List.map_map, Function.comp_def, h]

def pinInput (pin : ℕ → Option Bool) {n : ℕ} (x : Fin n → Bool) (i : Fin n) :=
  (pin i.val).getD (x i)

theorem restrict_eval (n : ℕ) (pin : ℕ → Option Bool) (D : Circuit) (x : Fin n → Bool) :
    (restrict n pin D).eval (List.ofFn x) = D.eval (List.ofFn (pinInput pin x)) := by
  change (((D.gates.map (copyGate n pin)).foldl evstep
    ((List.ofFn x ++ [false]) ++ [true])).getD (idx n pin D.output) false) = _
  change _ = (D.gates.foldl evstep (List.ofFn (pinInput pin x))).getD D.output false
  apply fold_ev
  · simp
  · simp <;> omega
  intro i
  by_cases hi : i < n
  · rw [cons_end_get, cons_end_get]
    have hlen : (List.ofFn x).length = n := by simp
    simp only [List.length_append, List.length_singleton, hlen, idx, if_pos hi]
    have hn1 : i ≠ n+1 := by omega
    cases hp : pin i with
    | none => simp [hp, hi, hi.ne, hn1, pinInput]
    | some b => cases b <;> simp [hp, hi, pinInput]
  · rw [List.getD_eq_default, List.getD_eq_default]
    · simpa using Nat.le_of_not_gt hi
    · simp [idx, hi] <;> omega


private def dgstep (s : List ℕ) (g : Gate) : List ℕ := s ++ [g.lineDegree s]

private theorem map_sum_le (s : List ℕ) (f g : ℕ → ℕ) (h : ∀ i, f i ≤ g i) :
    (s.map f).sum ≤ (s.map g).sum := by
  induction s with
  | nil => simp
  | cons i s ih => simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add (h i) ih

private theorem map_max_le (s : List ℕ) (f g : ℕ → ℕ) (h : ∀ i, f i ≤ g i) :
    (s.map f).foldr max 0 ≤ (s.map g).foldr max 0 := by
  induction s with
  | nil => simp
  | cons i s ih => simpa only [List.map_cons, List.foldr_cons] using max_le_max (h i) ih

private theorem fold_dg (n : ℕ) (pin : ℕ → Option Bool) (gs : List Gate)
    (s d : List ℕ) (hn : n ≤ s.length) (hlen : d.length = s.length+2)
    (h : ∀ i, d.getD (idx n pin i) 0 ≤ s.getD i 0) :
    ∀ i, ((gs.map (copyGate n pin)).foldl dgstep d).getD (idx n pin i) 0 ≤
      (gs.foldl dgstep s).getD i 0 := by
  induction gs generalizing s d with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [dgstep]; omega
    · simp [dgstep, hlen]
    · apply bridge (· ≤ ·) n pin s d _ _ 0 hn hlen h
      simp only [copyGate, Gate.lineDegree, List.map_map, Function.comp_def]
      by_cases hgate : g.op = GateOp.and
      · simpa only [hgate, if_true] using map_sum_le g.inputs _ _ h
      · simpa only [hgate, if_false] using map_max_le g.inputs _ _ h

theorem restrict_degree (n : ℕ) (pin : ℕ → Option Bool) (D : Circuit) (marked : Finset ℕ) :
    (restrict n pin D).lineDeg n marked ≤ D.lineDeg n marked := by
  let s := (List.range n).map fun i => if i ∈ marked then 1 else 0
  change (((D.gates.map (copyGate n pin)).foldl dgstep ((s ++ [0]) ++ [0])).getD
    (idx n pin D.output) 0) ≤ (D.gates.foldl dgstep s).getD D.output 0
  apply fold_dg
  · simp [s]
  · simp [s]
  intro i
  have hlen : s.length = n := by simp [s]
  rw [cons_end_get, cons_end_get]
  simp only [List.length_append, List.length_singleton, hlen]
  by_cases hi : i < n
  · have hn1 : i ≠ n+1 := by omega
    simp only [idx, if_pos hi]
    cases hp : pin i with
    | none => simp [hi.ne, hn1]
    | some b => cases b <;> simp
  · have hn0 : i+2 ≠ n := by omega
    have hn1 : i+2 ≠ n+1 := by omega
    simp only [idx, if_neg hi, if_neg hn0, if_neg hn1]
    rw [List.getD_eq_default s 0 (by omega)]
    exact Nat.zero_le _

end Meta606RangeTwo.PinCircuit
