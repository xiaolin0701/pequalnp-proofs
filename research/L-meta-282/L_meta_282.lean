import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

-- Wire evaluation follows the circuit semantics lemmas in L-meta-718.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial gs w
  rw [ht]; simp [hl]

theorem initial_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, initial_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact initial_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [initial_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]


def selectWire (bit : Bool) : List ℕ → Option ℕ
  | [] => none
  | [a] => some a
  | a :: b :: _ => some (if bit then b else a)

def sideValue (bit : Bool) (xs : List ℕ) (read : ℕ → Bool) : Bool :=
  ((selectWire bit xs).map read).getD true

lemma sideExists (xs : List ℕ) (read : ℕ → Bool) (h : xs.length ≤ 2) :
    ∃ b, sideValue b xs read = (xs.map read).all id := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩
  · exact ⟨false, rfl⟩
  · exact ⟨false, by simp [sideValue, selectWire]⟩
  · refine ⟨read a, ?_⟩
    cases ha : read a <;> cases hb : read b <;> simp [sideValue, selectWire, ha, hb]
  · simp at h

-- A choice of one operand per AND must agree with the actual gate value on this input.
def Valid {n : ℕ} (C : Circuit) (tag : ℕ → Fin 3) (x : Fin n → Bool)
    (bits : Fin 3 → Bool) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
    sideValue (bits (tag j)) g.inputs (operand C x (n+j)) = val C x (n+j)

-- A shared choice preserves falsity on the union of two inputs.
lemma joinFalse {n : ℕ} (C : Circuit) (tag : ℕ → Fin 3) (x y : Fin n → Bool)
    (bits : Fin 3 → Bool) (mx : Valid C tag x bits) (my : Valid C tag y bits)
    (hm : Monotone2 C) (w : ℕ) : val C x w = false → val C y w = false →
      val C (fun i => x i || y i) w = false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx hy
    by_cases input : w < n
    · let a : Fin n := ⟨w, input⟩
      change val C (fun i => x i || y i) a.val = false
      rw [val_input]
      exact Bool.or_eq_false_iff.mpr ⟨(val_input C x a).symm.trans hx,
        (val_input C y a).symm.trans hy⟩
    by_cases bound : w < n + C.gates.length
    · let j := w - n
      have jw : w = n + j := by dsimp [j]; omega
      have hj : j < C.gates.length := by dsimp [j]; omega
      let g := C.gates[j]
      have hg : C.gates[j]? = some g := List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
      have ⟨hop, hlen⟩ := hm g (List.getElem_mem hj)
      change g.op = GateOp.and ∨ g.op = GateOp.or at hop
      have prop (i : ℕ) : operand C x (n+j) i = false →
          operand C y (n+j) i = false → operand C (fun a => x a || y a) (n+j) i = false := by
        by_cases hi : i < w
        · simpa only [← jw, operand, ite_eq_left hi] using ih i hi
        · simp [← jw, operand, hi]
      rw [jw] at hx hy ⊢
      rw [val_gate C _ hg]
      rcases hop with ha | ho
      · have ax := (mx j g hg ha).trans hx
        have ay := (my j g hg ha).trans hy
        rw [ha]
        let r := operand C (fun i => x i || y i) (n+j)
        change (g.inputs.map r).all id = false
        rcases he : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩
        · simp [sideValue,he,selectWire] at ax
        · simpa [r] using prop a (by simpa [sideValue,he,selectWire] using ax)
            (by simpa [sideValue,he,selectWire] using ay)
        · cases hbit : bits (tag j)
          · have hz := prop a (by simpa [sideValue,he,selectWire,hbit] using ax)
                (by simpa [sideValue,he,selectWire,hbit] using ay)
            simp [r,hz]
          · have hz := prop b (by simpa [sideValue,he,selectWire,hbit] using ax)
                (by simpa [sideValue,he,selectWire,hbit] using ay)
            simp [r,hz]
        · simp [he] at hlen
      · rw [val_gate C _ hg, ho] at hx hy
        rw [ho]
        simp only [GateOp.eval, List.any_eq_false, List.mem_map, Bool.not_eq_true,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hx hy ⊢
        exact fun i hi => prop i (hx i hi) (hy i hi)
    · exact val_beyond C _ (by omega)

lemma existsValid {n : ℕ} (C : Circuit) (A : Finset ℕ) (tag : ℕ → Fin 3)
    (bound : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (inj : Set.InjOn tag (A : Set ℕ)) (hm : Monotone2 C) (x : Fin n → Bool) :
    ∃ bits, Valid C tag x bits := by
  classical
  have one (j : ℕ) : ∃ b : Bool, ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
      sideValue b g.inputs (operand C x (n+j)) = val C x (n+j) := by
    cases hg : C.gates[j]? with
    | none => exact ⟨false, by simp⟩
    | some g =>
      have ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hg
      have hlen := (hm _ (he ▸ List.getElem_mem hj)).2
      obtain ⟨b,hb⟩ := sideExists g.inputs (operand C x (n+j)) hlen
      refine ⟨b, ?_⟩
      intro k hk ha
      cases hk
      simpa [val_gate C x hg, ha, GateOp.eval, id] using hb
  choose f hf using one
  let F : Fin 3 → Bool := fun c =>
    if h : ∃ j ∈ A, tag j = c then f h.choose else false
  refine ⟨F, ?_⟩
  intro j g h ha
  have hjA := bound j g h ha
  have hx : ∃ k ∈ A, tag k = tag j := ⟨j,hjA,rfl⟩
  have same : hx.choose = j := inj hx.choose_spec.1 hjA hx.choose_spec.2
  simpa [F, hx, same] using hf j g h ha

lemma anyJoin (xs : List ℕ) (a b : ℕ → Bool) :
    xs.any (fun i => a i || b i) = (xs.any a || xs.any b) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [ih, Bool.or_assoc, Bool.or_left_comm]

-- Before the first AND every wire preserves unions.
lemma beforeJoin {n : ℕ} (C : Circuit) (hm : Monotone2 C) (j : ℕ)
    (prior : ∀ k < j, ∀ g, C.gates[k]? = some g → g.op ≠ GateOp.and)
    (x y : Fin n → Bool) (w : ℕ) (hw : w < n+j) :
    val C (fun i => x i || y i) w = (val C x w || val C y w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w < n
    · let v : Fin n := ⟨w,h⟩
      change val C _ v.val = (val C _ v.val || val C _ v.val)
      simp only [val_input]
    by_cases bound : w < n + C.gates.length
    · let k := w - n
      have wk : w = n+k := by dsimp [k]; omega
      have hk : k < C.gates.length := by dsimp [k]; omega
      let g := C.gates[k]
      have hg : C.gates[k]? = some g := List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
      have op := (hm g (List.getElem_mem hk)).1
      change g.op = GateOp.and ∨ g.op = GateOp.or at op
      have ho := op.resolve_left (prior k (by omega) g hg)
      have hop : operand C (fun i => x i || y i) (n+k) = fun v =>
          operand C x (n+k) v || operand C y (n+k) v := by
        funext i
        by_cases hi : i < w
        · simpa only [← wk, operand, ite_eq_left hi] using ih i hi (by omega)
        · simp [← wk, operand, hi]
      rw [wk, val_gate C _ hg, val_gate C _ hg, val_gate C _ hg, ho, hop]
      simpa only [GateOp.eval, List.any_map, Function.id_comp] using
        anyJoin g.inputs (operand C x (n+k)) (operand C y (n+k))
    · simp [val_beyond C _ (show n + C.gates.length ≤ w by omega)]

lemma selectAnd (xs : List ℕ) (read : ℕ → Bool) (hlen : xs.length ≤ 2) :
    (xs.map read).all id = (sideValue false xs read && sideValue true xs read) := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨d,t⟩⟩⟩
  · rfl
  · simp [sideValue,selectWire]
  · simp [sideValue,selectWire]
  · simp at hlen

lemma forceOpposite {n : ℕ} (C : Circuit) (A : Finset ℕ) (tag : ℕ → Fin 3)
    (bound : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (inj : Set.InjOn tag (A : Set ℕ)) (hm : Monotone2 C) (x : Fin n → Bool)
    (bits : Fin 3 → Bool) (hb : Valid C tag x bits)
    (unique : ∀ c, Valid C tag x c → c = bits) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (ha : g.op = GateOp.and) :
    sideValue false g.inputs (operand C x (n+j)) = bits (tag j) ∧
      sideValue true g.inputs (operand C x (n+j)) = !(bits (tag j)) := by
  have other : sideValue (!(bits (tag j))) g.inputs (operand C x (n+j)) ≠ val C x (n+j) := by
    intro h
    let c := Function.update bits (tag j) (!(bits (tag j)))
    have hc : Valid C tag x c := by
      intro k u hu ha'
      by_cases hk : tag k = tag j
      · have eq := inj (bound k u hu ha') (bound j g hg ha) hk
        subst k
        have equ : u = g := Option.some.inj (hu.symm.trans hg)
        subst u
        simpa [c] using h
      · simpa [c, Function.update_of_ne hk] using hb k u hu ha'
    have bad := congrFun (unique c hc) (tag j)
    simp [c] at bad
  have same := hb j g hg ha
  have hlen : g.inputs.length ≤ 2 := (hm g (List.mem_of_getElem? hg)).2
  rw [val_gate C x hg, ha] at same other
  change _ = (g.inputs.map _).all id at same
  change _ ≠ (g.inputs.map _).all id at other
  rw [selectAnd _ _ hlen] at same other
  cases hbit : bits (tag j) <;>
    cases h0 : sideValue false g.inputs (operand C x (n+j)) <;>
    cases h1 : sideValue true g.inputs (operand C x (n+j)) <;> simp_all


-- These eight nonedges pair one vertex of each triangle, omitting the connecting edge.
def leftVertex : Fin 8 → Fin 6 := fun i => ⟨i.val / 3, by omega⟩
def rightVertex : Fin 8 → Fin 6 := fun i => ⟨if i.val < 6 then 3 + i.val % 3 else i.val - 2, by split <;> omega⟩

def hits (bare : Fin 6 → Bool) (i : Fin 8) : Bool :=
  bare (leftVertex i) || bare (rightVertex i)

set_option maxHeartbeats 4000000 in
lemma firstGateCannotSplit : ∀ a b : Fin 6 → Bool,
    (∀ i, hits a i = !(hits b i)) →
      (Finset.univ.filter (fun i => hits a i = true)).card ≠ 4 := by
  decide +kernel

-- Eight pairwise incompatible rows use all eight choices, once each.
lemma uniqueCodes (ok : Fin 8 → (Fin 3 → Bool) → Prop)
    (existsCode : ∀ i, ∃ c, ok i c)
    (separates : ∀ i j c, ok i c → ok j c → i = j) :
    ∃ e : Fin 8 ≃ (Fin 3 → Bool), ∀ i c, ok i c ↔ e i = c := by
  choose f hf using existsCode
  have inj : Function.Injective f := by
    intro i j e
    exact separates i j (f j) (e ▸ hf i) (hf j)
  have bij := (Fintype.bijective_iff_injective_and_card f).2 ⟨inj, by decide⟩
  refine ⟨Equiv.ofBijective f bij, fun i c => ?_⟩
  change ok i c ↔ f i = c
  constructor
  · intro h
    obtain ⟨j, rfl⟩ := bij.surjective c
    rw [separates i j (f j) h (hf j)]
  · rintro rfl
    exact hf i

def point (v : Fin 6) : Fin 6 → Bool := fun i => decide (i = v)

def row (i : Fin 8) : Fin 6 → Bool :=
  fun v => point (leftVertex i) v || point (rightVertex i) v

abbrev EdgeOn (x : Fin 6 → Bool) : Prop :=
  ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] :
    List (ℕ × ℕ)) ∧ x u = true ∧ x v = true

lemma rowIndependent : ∀ i, ¬ EdgeOn (row i) := by decide +kernel

lemma rowsConflict : ∀ i j, i ≠ j → EdgeOn (fun v => row i v || row j v) := by decide +kernel

lemma lowerBound (C : Circuit) (hm : Monotone2 C) (A : Finset ℕ) (hcard : A.card ≤ 3)
    (bound : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (model : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔ EdgeOn x) : False := by
  classical
  obtain ⟨emb : A ↪ Fin 3⟩ := Function.Embedding.nonempty_of_card_le (α := ↥A) (β := Fin 3) (by simpa using hcard)
  let tag : ℕ → Fin 3 := fun j => if h : j ∈ A then emb ⟨j,h⟩ else 0
  have inj : Set.InjOn tag (A : Set ℕ) := by
    intro i hi j hj e
    change i ∈ A at hi
    change j ∈ A at hj
    have eq : emb ⟨i,hi⟩ = emb ⟨j,hj⟩ := by simpa only [tag, dite_eq_left hi, dite_eq_left hj] using e
    exact congrArg Subtype.val (emb.injective eq)
  have zero (i) : val C (row i) C.output = false :=
    Bool.eq_false_iff.mpr (fun h => rowIndependent i ((model _).1 h))
  have separate (i j) (c) (hi : Valid C tag (row i) c) (hj : Valid C tag (row j) c) : i = j := by
    by_contra ne
    have no := joinFalse C tag _ _ c hi hj hm C.output (zero i) (zero j)
    have yes := (model _).2 (rowsConflict i j ne)
    change val C _ C.output = true at yes
    exact Bool.false_ne_true (no.symm.trans yes)
  obtain ⟨e, he⟩ := uniqueCodes (fun i => Valid C tag (row i))
    (fun i => existsValid C A tag bound inj hm (row i)) separate
  have has : ∃ j : ℕ, ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and := by
    by_contra h
    have anyCode (i : Fin 8) : Valid C tag (row i) (fun _ => false) :=
      fun j g hg ha => (h ⟨j,g,hg,ha⟩).elim
    exact (by decide : (0 : Fin 8) ≠ 1) (separate _ _ _ (anyCode 0) (anyCode 1))
  let j := Nat.find has
  obtain ⟨g,hg,ha⟩ := Nat.find_spec has
  have prior (k) (hk : k < j) (u : Gate) (hu : C.gates[k]? = some u) : u.op ≠ GateOp.and :=
    fun hop => Nat.find_min has hk ⟨u,hu,hop⟩
  let bare (b : Bool) (v : Fin 6) := sideValue b g.inputs (operand C (point v) (6+j))
  have hit (b) (i) : hits (bare b) i =
      sideValue b g.inputs (operand C (row i) (6+j)) := by
    cases hsel : selectWire b g.inputs with
    | none => simp [hits,bare,sideValue,hsel]
    | some w =>
      by_cases hw : w < 6+j
      · simp only [hits, bare, sideValue, hsel, Option.map_some, Option.getD_some, operand,
          ite_eq_left hw]
        exact (beforeJoin C hm j prior _ _ w hw).symm
      · simp [hits,bare,sideValue,hsel,operand,hw]
  have both (i) :
      hits (bare false) i = e i (tag j) ∧ hits (bare true) i = !(e i (tag j)) := by
    rw [hit,hit]
    exact forceOpposite C A tag bound inj hm (row i) (e i) ((he i _).2 rfl)
      (fun c h => ((he i c).1 h).symm) j g hg ha
  have nob := firstGateCannotSplit (bare false) (bare true) (fun i => by rw [(both i).1,(both i).2]; simp)
  apply nob
  calc
    _ = (Finset.univ.filter (fun c : Fin 3 → Bool => c (tag j) = true)).card :=
      Finset.card_equiv e (fun i => by simp [(both i).1])
    _ = 4 := (by decide +kernel : ∀ t : Fin 3,
      (Finset.univ.filter (fun c : Fin 3 → Bool => c t = true)).card = 4) (tag j)

end PEqualNP.Outside.L_meta_282

theorem PEqualNP.Outside.L_meta_282 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨hm, A, hcard, bound⟩, model⟩
  exact PEqualNP.Outside.L_meta_282.lowerBound C hm A hcard bound model
