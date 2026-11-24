import PEqualNP.Defs

namespace Meta3156Edges
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fold monotonicity from the project helper LowMergeWires.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem isNot_iff (g : Gate) : isNot g = true ↔ g.op = .not := by
  rcases g with ⟨op,ins⟩; cases op <;> simp [isNot]

theorem leInputs {n} (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    LeL (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt),List.getElem_ofFn] at hi ⊢
    exact h ⟨i,hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

theorem leSnoc {a b : List Bool} (hl : a.length = b.length) (h : LeL a b)
    {u v : Bool} (hz : u = true → v = true) : LeL (a++[u]) (b++[v]) := by
  intro i hi
  by_cases lt : i < a.length
  · rw [List.getD_append _ _ _ _ lt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    rw [← hl]
    cases j : i-a.length with
    | zero => simp [j] at hi; simpa using hz hi
    | succ k => simp [j] at hi


-- Locate the failed cofactor on a minimal positive assignment.
def edgeCodes : List Nat := [1,12,23,34,40,5,16,27,38,57,68,85]
def lhs (e : Nat) := Fin.ofNat 9 (e / 10)
def rhs (e : Nat) := Fin.ofNat 9 (e % 10)
def pair (e : Nat) (i : Fin 9) : Bool := decide (i = lhs e ∨ i = rhs e)
def edge (x : Fin 9 → Bool) := edgeCodes.any fun e => x (lhs e) && x (rhs e)

theorem ao (pre post : List Gate) (q : Gate) (out : Nat)
    (hf : FanInTwo ⟨pre ++ q :: post, out⟩)
    (hn : ∀ g ∈ pre ++ post, g.op ≠ .not) {g : Gate} (hg : g ∈ pre ++ post) :
    g.op = .and ∨ g.op = .or := by
  have mem : g ∈ pre ++ q :: post := by
    rcases List.mem_append.mp hg with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have legal := (hf g mem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
  exact legal.elim Or.inl (fun h => h.elim Or.inr (fun no => False.elim (hn g hg no)))

theorem forced_le (pre post : List Gate) (q : Gate) (out : Nat)
    (hf : FanInTwo ⟨pre ++ q :: post, out⟩)
    (hn : ∀ g ∈ pre ++ post, g.op ≠ .not) (x : Fin 9 → Bool) :
    circuitFun 9 ⟨pre ++ ⟨.or,[]⟩ :: post, out⟩ x = true →
    circuitFun 9 ⟨pre ++ q :: post, out⟩ x = true := by
  let w := pre.foldl step (List.ofFn x)
  change ((pre ++ ⟨.or,[]⟩ :: post).foldl step (List.ofFn x)).getD out false = true → _
  change _ → ((pre ++ q :: post).foldl step (List.ofFn x)).getD out false = true
  simp only [List.foldl_append,List.foldl_cons]
  apply fold_mono post (fun g h => ao pre post q out hf hn (List.mem_append_right _ h))
        (step w ⟨.or,[]⟩) (step w q) (by simp [step])
        (leSnoc rfl (fun _ => id) (by simp [GateOp.eval])) out

theorem forced_monotone (pre post : List Gate) (q : Gate) (out : Nat)
    (hf : FanInTwo ⟨pre ++ q :: post, out⟩)
    (hn : ∀ g ∈ pre ++ post, g.op ≠ .not) (x y : Fin 9 → Bool)
    (xy : ∀ i, x i = true → y i = true) :
    circuitFun 9 ⟨pre ++ ⟨.or,[]⟩ :: post, out⟩ x = true →
    circuitFun 9 ⟨pre ++ ⟨.or,[]⟩ :: post, out⟩ y = true := by
  apply fold_mono (pre ++ ⟨.or,[]⟩ :: post) _ _ _ (by simp) (leInputs x y xy) out
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ao pre post q out hf hn (List.mem_append_left _ h)
  · rcases List.mem_cons.mp h with h | h
    · subst g; exact .inr rfl
    · exact ao pre post q out hf hn (List.mem_append_right _ h)

theorem missed_edge (d : (Fin 9 → Bool) → Bool) (v : Fin 9)
    (low : ∀ x, d x = true → edge x = true)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → d x = true → d y = true)
    (diff : (fun y : Fin 8 → Bool => d (v.insertNth false y)) ≠
      (fun y : Fin 8 → Bool => edge (v.insertNth false y))) :
    ∃ e ∈ edgeCodes, lhs e ≠ v ∧ rhs e ≠ v ∧ d (pair e) = false := by
  classical
  have ex : ∃ y : Fin 8 → Bool, d (v.insertNth false y) ≠ edge (v.insertNth false y) := by
    by_contra! all
    exact diff (funext all)
  obtain ⟨y,hy⟩ := ex
  let x : Fin 9 → Bool := v.insertNth false y
  have hd : d x = false := by
    cases h : d x with
    | false => rfl
    | true => exact False.elim (hy (h.trans (low x h).symm))
  have yes : edge x = true := by
    cases h : edge x with
    | false => exact False.elim (hy (hd.trans h.symm))
    | true => rfl
  obtain ⟨e,he,hh⟩ := List.any_eq_true.mp yes
  change (x (lhs e) && x (rhs e)) = true at hh
  rw [Bool.and_eq_true] at hh
  obtain ⟨hl,hr⟩ := hh
  have hv : x v = false := Fin.insertNth_apply_same ..
  refine ⟨e,he,(fun eq => ?_),(fun eq => ?_),?_⟩
  · rw [eq,hv] at hl; contradiction
  · rw [eq,hv] at hr; contradiction
  · cases h : d (pair e) with
    | false => rfl
    | true =>
      have contra := mono (pair e) x (by
        intro i hi
        change decide (i = lhs e ∨ i = rhs e) = true at hi
        rcases of_decide_eq_true hi with rfl | rfl <;> assumption) h
      rw [hd] at contra
      contradiction


theorem cofactor_diff_iff_edge (d : (Fin 9 → Bool) → Bool) (v : Fin 9)
    (low : ∀ x, d x = true → edge x = true)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → d x = true → d y = true) :
    (fun y : Fin 8 → Bool => d (v.insertNth false y)) ≠
      (fun y : Fin 8 → Bool => edge (v.insertNth false y)) ↔
      ∃ e ∈ edgeCodes, lhs e ≠ v ∧ rhs e ≠ v ∧ d (pair e) = false := by
  refine ⟨missed_edge d v low mono,?_⟩
  rintro ⟨e,hm,hl,hr,hd⟩ eq
  have off : pair e v = false := by simp [pair,Ne.symm hl,Ne.symm hr]
  have ins : v.insertNth false (v.removeNth (pair e)) = pair e := by
    rw [← off]
    exact Fin.insertNth_self_removeNth v (pair e)
  have h := congrFun eq (v.removeNth (pair e))
  simp only [ins] at h
  have he : edge (pair e) = true := List.any_eq_true.mpr ⟨e,hm,by simp [pair]⟩
  rw [hd,he] at h
  contradiction

theorem has_three_witnesses (pre post : List Gate) (q : Gate) (out : Nat)
    (hf : FanInTwo ⟨pre ++ q :: post, out⟩)
    (hn : ∀ g ∈ pre ++ post, g.op ≠ .not)
    (he : circuitFun 9 ⟨pre ++ q :: post, out⟩ = edge)
    (diff : ∀ v : Fin 9, v = 4 ∨ v = 6 ∨ v = 7 →
     (fun y : Fin 8 → Bool => circuitFun 9 ⟨pre ++ ⟨.or,[]⟩ :: post,out⟩ (v.insertNth false y)) ≠
       (fun y : Fin 8 → Bool => edge (v.insertNth false y))) :
    ∀ v : Fin 9, v = 4 ∨ v = 6 ∨ v = 7 →
      ∃ e ∈ edgeCodes, lhs e ≠ v ∧ rhs e ≠ v ∧
        circuitFun 9 ⟨pre ++ ⟨.or,[]⟩ :: post, out⟩ (pair e) = false := by
  intro v hv
  apply missed_edge _ v _ (forced_monotone pre post q out hf hn) (diff v hv)
  intro x h
  rw [← he]
  exact forced_le pre post q out hf hn x h


-- A missed edge by itself witnesses that the inverter output is true.
theorem gate_on_missed (pre post : List Gate) (q : Gate) (out : Nat)
    (he : circuitFun 9 ⟨pre ++ q :: post, out⟩ = edge) (e : Nat) (hm : e ∈ edgeCodes)
    (miss : circuitFun 9 ⟨pre ++ ⟨.or,[]⟩ :: post,out⟩ (pair e) = false) :
    let w := pre.foldl step (List.ofFn (pair e))
    q.op.eval (q.inputs.map fun i => w.getD i false) = true := by
  let w := pre.foldl step (List.ofFn (pair e))
  let b := q.op.eval (q.inputs.map fun i => w.getD i false)
  change b = true
  by_contra h
  have hz : b = false := by cases hbit : b <;> simp_all
  have positive : edge (pair e) = true := by
    apply List.any_eq_true.mpr
    exact ⟨e,hm,by simp [pair]⟩
  have htrue := (congrFun he (pair e)).trans positive
  change ((pre ++ q :: post).foldl step (List.ofFn (pair e))).getD out false = true at htrue
  change ((pre ++ ⟨.or,[]⟩ :: post).foldl step (List.ofFn (pair e))).getD out false = false at miss
  simp only [List.foldl_append, List.foldl_cons] at htrue miss
  change (post.foldl step (w ++ [b])).getD out false = true at htrue
  change (post.foldl step (w ++ [false])).getD out false = false at miss
  rw [hz,miss] at htrue
  contradiction

theorem sparse_child : ∀ (pre post : List Gate) (q : Gate) (o : ℕ),
      let C : Circuit := ⟨pre ++ q :: post, o⟩
      let D : Circuit := ⟨pre ++ ⟨.or, []⟩ :: post, o⟩
      let f := fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))
      FanInTwo C → (∀ g ∈ pre ++ post, g.op ≠ .not) → circuitFun 9 C = f →
      ∀ (v : Fin 9),
        (fun y : Fin 8 → Bool => circuitFun 9 D (v.insertNth false y)) ≠
        (fun y : Fin 8 → Bool => f (v.insertNth false y)) →
        ∃ i j : Fin 9, i ≠ v ∧ j ≠ v ∧
          let x := fun u : Fin 9 => decide (u = i ∨ u = j)
          f x = true ∧ circuitFun 9 D x = false ∧
            let w := (⟨pre,o⟩ : Circuit).wires (List.ofFn x)
            q.op.eval (q.inputs.map (fun k => w.getD k false)) = true := by
  dsimp only
  intro pre post q o hf hn he v hd
  have hfun : circuitFun 9 ⟨pre ++ q :: post,o⟩ = edge := he
  obtain ⟨e,mem,hl,hr,missing⟩ := missed_edge _ v
    (fun x h => (congrFun hfun x) ▸ forced_le pre post q o hf hn x h)
    (forced_monotone pre post q o hf hn) hd
  refine ⟨lhs e,rhs e,hl,hr,?_,missing,?_⟩
  · apply List.any_eq_true.mpr
    exact ⟨e,mem,by simp [lhs,rhs]⟩
  · exact gate_on_missed pre post q o hfun e mem missing
end Meta3156Edges
