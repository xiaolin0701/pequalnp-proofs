import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1557_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

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

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp


private def value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  Circuit.eval ⟨gs,w⟩ (List.ofFn x)

private lemma input_eq {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    value gs x i = x i := by
  change (wiresFrom gs (List.ofFn x)).getD i false = _
  rw [getD_wiresFrom_lt _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma or_iff {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length)
    (hop : (gs.get i).op = GateOp.or) :
    value gs x (n + i.val) = true ↔
      ∃ w ∈ (gs.get i).inputs, w < n + i.val ∧ value gs x w = true := by
  have h := getD_wiresFrom_gate gs (List.ofFn x) i.val i.isLt
  rw [List.length_ofFn] at h
  change (wiresFrom gs (List.ofFn x)).getD (n + i.val) false = true ↔ _
  rw [h]
  change (gs.get i).op.eval _ = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨w,hw,hval⟩,rfl⟩
    by_cases hlt : w < n + i.val
    · exact ⟨w,hw,hlt,by simpa [hlt, value, Circuit.eval, Circuit.wires, wiresFrom] using hval⟩
    · simp [hlt] at hval
  · rintro ⟨w,hw,hlt,hval⟩
    exact ⟨true,⟨w,hw,by simpa [hlt, value, Circuit.eval, Circuit.wires, wiresFrom] using hval⟩,rfl⟩

theorem and_of_tests (n : ℕ) (gs : List Gate) (g : Fin gs.length) (x y z : Fin n → Bool)
    (hops : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or)
    (hcover : ∀ i, x i = true → y i = true ∨ z i = true)
    (hx : Circuit.eval ⟨gs,n + g.val⟩ (List.ofFn x) = true)
    (hy : Circuit.eval ⟨gs,n + g.val⟩ (List.ofFn y) = false)
    (hz : Circuit.eval ⟨gs,n + g.val⟩ (List.ofFn z) = false) :
    ∃ a : Fin gs.length, (gs.get a).op = GateOp.and ∧
      ∀ T : Finset (Fin gs.length), g ∈ T →
        (∀ i ∈ T, ∀ j : Fin gs.length, n + j.val ∈ (gs.get i).inputs → j < i → j ∈ T) → a ∈ T := by
  classical
  let needed (i : Fin gs.length) : Prop := ∀ T : Finset (Fin gs.length), g ∈ T →
    (∀ a ∈ T, ∀ j : Fin gs.length, n + j.val ∈ (gs.get a).inputs → j < a → j ∈ T) → i ∈ T
  have root : needed g := fun _ h _ => h
  have earlier {i j : Fin gs.length} (hi : needed i) (hw : n + j.val ∈ (gs.get i).inputs)
      (hji : j < i) : needed j := by
    intro T hg hc
    exact hc i (hi T hg hc) j hw hji
  by_contra hnone
  have allOr (i : Fin gs.length) (hi : needed i) : (gs.get i).op = GateOp.or := by
    rcases hops _ (List.get_mem _ _) with h | h
    · exact (hnone ⟨i,h,hi⟩).elim
    · exact h
  have propagate (a : ℕ) (ha : a < gs.length) (hneed : needed ⟨a,ha⟩)
      (hax : value gs x (n+a) = true) :
      value gs y (n+a) = true ∨ value gs z (n+a) = true := by
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      let i : Fin gs.length := ⟨a,ha⟩
      have ho := allOr i hneed
      obtain ⟨w,hw,hlt,hxw⟩ := (or_iff gs x i ho).mp hax
      have child : value gs y w = true ∨ value gs z w = true := by
        by_cases hp : w < n
        · let v : Fin n := ⟨w,hp⟩
          have h := hcover v ((input_eq gs x v).symm.trans hxw)
          simpa only [← input_eq gs y v, ← input_eq gs z v] using h
        · let j : Fin gs.length := ⟨w-n, by dsimp [i] at hlt; omega⟩
          have hwj : n + j.val=w := by dsimp [j]; omega
          have hji : j < i := by change w-n < a; change w < n+a at hlt; omega
          have hnj := earlier hneed (hwj ▸ hw) hji
          simpa only [hwj] using ih j.val hji j.isLt hnj (hwj ▸ hxw)
      rcases child with h | h
      · exact Or.inl ((or_iff gs y i ho).mpr ⟨w,hw,hlt,h⟩)
      · exact Or.inr ((or_iff gs z i ho).mpr ⟨w,hw,hlt,h⟩)
  rcases propagate g.val g.isLt root hx with h | h
  · exact Bool.noConfusion (hy.symm.trans h)
  · exact Bool.noConfusion (hz.symm.trans h)

end PEqualNP.Outside.L_meta_1557_aux

theorem PEqualNP.Outside.L_meta_1557 : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (B : Fin n → Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : Fin gates.length) (q q' : Fin n),
    L ∩ M = {m} → (∀ r ∈ L, B r ∩ L = ∅) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    q ∈ L → q' ∈ L → q ≠ q' →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q ∨ v ∈ B q))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q' ∨ v ∈ B q'))) = true →
    ∃ a : Fin gates.length, (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ∀ T : Finset (Fin gates.length), g ∈ T →
        (∀ i ∈ T, ∀ g' : Fin gates.length, n + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → a ∈ T := by
  intro n L M m B gates g q q' hLM hB hops hq hq' hne hLfalse hMfalse hqtrue hq'true
  classical
  have use_test (r : Fin n) (hr : r ∈ L) (hrm : r ≠ m)
      (ht : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩
        (List.ofFn (fun v : Fin n => decide (v = r ∨ v ∈ B r))) = true) :
      ∃ a : Fin gates.length, (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), g ∈ T →
          (∀ i ∈ T, ∀ g' : Fin gates.length, n + (g' : ℕ) ∈ (gates.get i).inputs →
            g' < i → g' ∈ T) → a ∈ T := by
    apply L_meta_1557_aux.and_of_tests n gates g
      (fun v => decide (v = r ∨ v ∈ B r)) (fun v => decide (v ∉ L)) (fun v => decide (v ∉ M))
      (fun h hh => (hops h hh).1) _ ht hLfalse hMfalse
    intro i hi
    simp only [decide_eq_true_eq] at hi ⊢
    by_cases hiL : i ∈ L
    · right
      intro hiM
      have him : i ∈ L ∩ M := Finset.mem_inter.mpr ⟨hiL, hiM⟩
      rw [hLM, Finset.mem_singleton] at him
      rcases hi with hir | hiB
      · exact hrm (hir.symm.trans him)
      · have bad : i ∈ B r ∩ L := Finset.mem_inter.mpr ⟨hiB, hiL⟩
        simpa [hB r hr] using bad
    · exact Or.inl hiL
  by_cases h : q = m
  · apply use_test q' hq' _ hq'true
    exact fun h' => hne (h.trans h'.symm)
  · exact use_test q hq h hqtrue
