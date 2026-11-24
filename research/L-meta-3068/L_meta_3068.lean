import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3068_aux

-- Basic circuit semantics and constant propagation from the project proof of L_meta_720.
open PEqualNP.MetaComplexity
namespace PEqualNP.MetaComplexity.Helpers
open PEqualNP.CircuitLowerBounds
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

end PEqualNP.MetaComplexity.Helpers

namespace Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem unread_agree (S : ℕ → Prop) (gs : List Gate)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ S i) :
    ∀ u v : List Bool, u.length = v.length →
      (∀ i, ¬ S i → u.getD i false = v.getD i false) →
      ∀ i, ¬ S i → (wiresFrom gs u).getD i false = (wiresFrom gs v).getD i false := by
  induction gs with
  | nil => intro u v _ h; exact h
  | cons g gs ih =>
    intro u v hl h i hi
    have same : g.op.eval (g.inputs.map fun a => u.getD a false) =
        g.op.eval (g.inputs.map fun a => v.getD a false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h a (avoid g List.mem_cons_self a ha)
    apply ih (fun g' hg' => avoid g' (List.mem_cons_of_mem _ hg'))
      (u ++ [g.op.eval (g.inputs.map fun a => u.getD a false)])
      (v ++ [g.op.eval (g.inputs.map fun a => v.getD a false)]) (by simp [hl]) _ i hi
    intro k hk
    by_cases hku : k < u.length
    · rw [List.getD_append _ _ _ _ hku, List.getD_append _ _ _ _ (by omega)]
      exact h k hk
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      rw [same, hl]

theorem compressTail {T : Type*} (n : ℕ) (gs : List Gate) (out : ℕ) (M : List Stat)
    (u v : List Bool) (wz z : T → List Bool)
    (hok : ∀ g ∈ gs, Ok g) (hu : u.length = M.length) (hv : v.length = M.length)
    (hw : ∀ t, (wz t).length = n) (hz : ∀ t, (z t).length = M.length)
    (hvalid : ∀ k, (M.getD k (Sum.inl false)).Valid n)
    (hagree : ∀ k i, M.getD k (Sum.inl false) = Sum.inr i → u.getD k false = v.getD k false)
    (hmap : ∀ t k, (M.getD k (Sum.inl false)).val (wz t) = (z t).getD k false)
    (hprobe : (wiresFrom gs u).getD out false ≠ (wiresFrom gs v).getD out false)
    (hnc : ∃ a b, (wiresFrom gs (z a)).getD out false ≠ (wiresFrom gs (z b)).getD out false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size+1 ≤ gs.length ∧
      ∀ t, D.eval (wz t) = (wiresFrom gs (z t)).getD out false := by
  classical
  let gs' := gs.map normGate
  let acc := elim n gs' (M,[])
  have hn : ∀ g ∈ gs', NOk g := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok _ (hok _ hg₀)
  have hval (t : T) : (acc.1.getD out (Sum.inl false)).val (wiresFrom acc.2 (wz t)) =
      (wiresFrom gs (z t)).getD out false := by
    have hi : Inv n (wz t) (z t) (M,[]) := ⟨(hz t).symm, fun k => ⟨hvalid k,hmap t k⟩⟩
    have h := ((inv_elim n (wz t) (hw t) gs' (z t) _ (fun g hg => (hn g hg).1) hi).2 out).2
    simpa only [acc, gs', wiresFrom_norm] using h
  cases hout : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨a,b,hab⟩ := hnc
    exact (hab (by rw [← hval a, ← hval b, hout]; rfl)).elim
  | inr o =>
    let S := fun k => k < M.length ∧ ∃ b, M.getD k (Sum.inl false) = Sum.inl b
    have notout : ¬ S out := by
      rintro ⟨ho, b, hb⟩
      have he := elim_getD n out (Sum.inl false) gs' (M,[]) ho
      change acc.1.getD out (Sum.inl false) = M.getD out (Sum.inl false) at he
      rw [hout,hb] at he
      contradiction
    have hit : ∃ k, S k ∧ ∃ g ∈ gs', k ∈ g.inputs := by
      by_contra nohit
      apply hprobe
      have eqs := unread_agree S gs' (fun g hg i hi hS => nohit ⟨i,hS,g,hg,hi⟩) u v
        (hu.trans hv.symm) (fun i hi => by
          by_cases h : i < M.length
          · cases hs : M.getD i (Sum.inl false) with
            | inl b => exact (hi ⟨h,b,hs⟩).elim
            | inr j => exact hagree i j hs
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]) out notout
      simpa only [gs', wiresFrom_norm] using eqs
    obtain ⟨k,⟨hk,hconst⟩,hread⟩ := hit
    have hlen := elim_len_lt n k gs' (M,[]) hn hk hconst hread
    refine ⟨⟨acc.2,o⟩, elim_ok n gs' (M,[]) (by simp), ?_, ?_⟩
    · simpa only [Circuit.size, acc, gs', List.length_nil, Nat.zero_add, List.length_map] using hlen
    · intro t
      have h := hval t
      rw [hout] at h
      exact h

end Compression


namespace PinFour
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

def m : List Stat := [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
  Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 5]

def old (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
def pin (y : Fin 8 → Bool) := Fin.insertNth (α := fun _ => Bool) (4 : Fin 9) false y
def a (j : Fin 9) := decide (j = 0 ∨ j = 6)
def b (j : Fin 9) := decide (j = 0 ∨ j = 4 ∨ j = 6)

theorem valid (k : ℕ) : (m.getD k (Sum.inl false)).Valid 8 := by
  by_cases hk : k < 10
  · interval_cases k <;> first | exact True.intro | exact (by decide : 0 < 8) | exact (by decide : 1 < 8) | exact (by decide : 2 < 8) | exact (by decide : 3 < 8) | exact (by decide : 4 < 8) | exact (by decide : 5 < 8) | exact (by decide : 6 < 8) | exact (by decide : 7 < 8)
  · rw [List.getD_eq_default _ _ (by change 10 ≤ k; omega)]
    trivial

theorem agrees (k i : ℕ) (h : m.getD k (Sum.inl false) = Sum.inr i) :
    (old a).getD k false = (old b).getD k false := by
  by_cases hk : k < 10
  · interval_cases k <;> first | decide | contradiction
  · rw [List.getD_eq_default _ _ (by change 10 ≤ k; omega)] at h
    contradiction

theorem maps (y : Fin 8 → Bool) (k : ℕ) :
    (m.getD k (Sum.inl false)).val (List.ofFn y) = (old (pin y)).getD k false := by
  by_cases hk : k < 10
  · interval_cases k <;> rfl
  · rw [List.getD_eq_default _ _ (by change 10 ≤ k; omega),
        List.getD_eq_default _ _ (by change 10 ≤ k; omega)]
    rfl

theorem pin_four : ∀ (C : Circuit), FanInTwo C →
      let f := fun x : Fin 9 → Bool => C.eval (List.ofFn x ++ [x 4 || x 6])
      f (fun j => decide (j = 0 ∨ j = 6)) ≠ f (fun j => decide (j = 0 ∨ j = 4 ∨ j = 6)) →
      f ((4 : Fin 9).insertNth false (fun _ : Fin 8 => false)) ≠
        f ((4 : Fin 9).insertNth false (fun _ : Fin 8 => true)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
        ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f ((4 : Fin 9).insertNth false y) := by
  intro C hf
  dsimp only
  intro hprobe hnc
  apply Compression.compressTail 8 C.gates C.output m (old a) (old b)
    (fun y : Fin 8 → Bool => List.ofFn y) (fun y => old (pin y))
    hf (by rfl) (by rfl) (by simp) (by simp [old,m]) valid agrees maps hprobe
  exact ⟨fun _ => false, fun _ => true, hnc⟩

end PinFour

namespace Base1007
abbrev B:=BitVec 252
abbrev Sig:=B × B
def top : B:=BitVec.allOnes 252
def zero : Sig:=(0,0)
def one : Sig:=(top,top)
def target : Sig:=(top,0)
def neg (a : Sig) : Sig:=(~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1|||b.1,a.2|||b.2) else (a.1&&&b.1,a.2&&&b.2)
def proper (a : Sig) : Prop:=a ≠ zero/\a ≠ one
def raw0 : Sig:=(0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def raw1 : Sig:=(0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def raw2 : Sig:=(0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230)
def raw3 : Sig:=(0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def raw4 : Sig:=(0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def raw5 : Sig:=(0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def raw6 : Sig:=(0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def raw7 : Sig:=(0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)
def raw : List Sig:=[raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]
inductive Live : Nat->Nat->Finset Sig->Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))
namespace Theta
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
inductive Run {α : Type} (inv : α->α) (meet join : α->α->α) (y : α) : ℕ->List α->Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs->Run inv meet join y s xs->Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)
theorem kept_map {α β : Type} (e : α->β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e=kept b (e x) (xs.map e):= by cases b <;> simp [kept]
lemma Run.map {α β : Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
    {inv' : β->β} {meet' join' : β->β->β}
    (hi : ∀ a,e (inv a)=inv' (e a)) (hm : ∀ a b,e (meet a b)=meet' (e a) (e b))
    (hj : ∀ a b,e (join a b)=join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e):= by
  induction h with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e):= by
      cases neg <;> simp [kept_map,hi]
    rw [e1] at ih; exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)):= by
      cases conj <;> simp [kept_map,hm,hj]
    rw [e1] at ih; exact Run.two conj ka kb ih
theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) : xs.length ≤ s+1:= by
  induction h with
  | done=>simp
  | perm hp _ ih=>rwa [←hp.length_eq]
  | one _ save _ ih=>cases save <;> simp_all [kept] <;> omega
  | two _ ka kb _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
abbrev NatRun (m : Nat):=Run (·^^^m) (·&&&·) (·|||·)
lemma q29 {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i=m.testBit j) (hw : ∀ w ∈ xs,w.testBit i=w.testBit j) :
    y.testBit i=y.testBit j:= by
  induction h with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | one neg save _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)
def lo (k : Nat):=2^k - 1
def mask (k : Nat):=lo (k+k)
def goal (k : Nat):=lo k<<<k
def se : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def q7 : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def qe : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000
lemma yx : se=lo 232:= by decide +kernel
lemma vb : q7=mask 232:= by decide +kernel
lemma vc : qe=goal 232:= by decide +kernel
lemma u4 (k i : Nat) : (lo k).testBit i=decide (i<k):= by
  simp [lo,Nat.testBit_two_pow_sub_one]
lemma zn (k i : Nat) : (mask k).testBit i=decide (i<k+k):= by
  simp [mask,u4]
lemma xo (k i : Nat) :
    (goal k).testBit i=(decide (k ≤ i)&&decide (i - k<k)):= by
  simp [goal,Nat.testBit_shiftLeft,u4]
def vd (w : Nat) : Nat:=w^^^(w>>>232)
def s9 : List Nat->Nat | []=>0 | a :: t=>vd a|||s9 t
lemma q11 (i : Nat) (ws : List Nat) : (s9 ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i ≠ a.testBit (232+i):= by
  induction ws with
  | nil=>simp [s9]
  | cons a t ih =>
    simp only [s9,Nat.testBit_or,Bool.or_eq_true,ih,vd,Nat.testBit_xor,Nat.testBit_shiftRight,List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
lemma vl {s ws} (h : NatRun q7 qe s ws) :
    (s9 ws&&&se)=se:= by
  rw [vb,vc] at h; rw [yx]
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hm : (mask 232).testBit i=(mask 232).testBit (232+i):= by
      simp [zn,show i<464 by omega,show 232+i<464 by omega]
    have hy : (goal 232).testBit i ≠ (goal 232).testBit (232+i):= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (s9 ws).testBit i=true:= by
      apply (q11 i ws).2; by_contra! hh; exact hy (q29 h i (232+i) hm hh)
    simp [hc]
  · simp [u4,hi]
lemma q34 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1) (i j : Nat)
    (hw : ∀ a ∈ ws,a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j:= by
  induction h with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (hp.length_eq.trans hl) (fun a ha=>hw a (hp.mem_iff.1 ha))
  | one _ save h _=>have hh:=run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had; simp only [kept,Bool.false_eq_true,ite_false,List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true,Bool.false_eq_true,ite_false,Nat.testBit_or,Nat.testBit_and] <;> grind
    · exact hw _ (by simp [ht])
def sq (w : Nat) : Nat:=(w>>>232)&&&(w^^^se)
def rd : List Nat->Nat | []=>0 | a :: t=>sq a|||rd t
lemma zu (i : Nat) (hi : i<232) (ws : List Nat) : (rd ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i=false/\a.testBit (232+i)=true:= by
  induction ws with
  | nil=>simp [rd]
  | cons a t ih=>simp [rd,sq,yx,u4,hi,ih,and_comm]
lemma rl {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    (rd ws&&&se)=se:= by
  rw [vb,vc] at h; rw [yx]
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hy : ¬ (goal 232).testBit (232+i) ≤ (goal 232).testBit i:= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (rd ws).testBit i=true:= by
      apply (zu i hi ws).2; by_contra! hh; apply hy
      apply q34 h hl; intro a ha; specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
    simp [hc]
  · simp [u4,hi]
lemma y1 {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):= by cases b <;> simpa [kept] using p
def vy (s : Nat) (ws : List Nat) (f : Bool->List Nat->Bool) : Bool :=
  let len:=ws.length
  let slack:=s+2 - len
  let t0:=decide (len=s+2)
  let t1:=decide (len=s+1)
  let t2:=decide (len=s)
  ws.any fun a =>
    let ra:=ws.erase a
    let da:=vd a
    let dau:=sq a
    (slack ≥ 1 &&
      (let cra:=if t1&&slack==1 then 0 else s9 ra
       let crau:=if t1||t2 then rd ra else 0
       [false,true].any fun neg =>
        let w:=if neg then a^^^q7 else a
        (((if t1 then sq w|||crau else vd w|||cra)&&&se==se)&&f t1 (w :: ra)) ||
        (slack ≥ 2 &&
          ((if t2 then sq w|||(dau|||crau) else vd w|||(da|||cra))&&&se==se) &&
          f t2 (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b &&
      (let r:=ra.erase b
       let db:=vd b
       let dbu:=sq b
       let cr:=if t0 then 0 else s9 r
       let cru:=if t0||t1||t2 then rd r else 0
       [false,true].any fun conj =>
        let w:=if conj then a&&&b else a|||b
        let dw:=if t0 then 0 else vd w
        let dwu:=if t0||t1||t2 then sq w else 0
        (((if t0 then dwu|||cru else dw|||cr)&&&se==se)&&f t0 (w :: r)) ||
        (slack ≥ 1 &&
          ((((if t1 then dwu|||(dau|||cru) else dw|||(da|||cr))&&&se==se)&&f t1 (w :: a :: r)) ||
           (((if t1 then dwu|||(dbu|||cru) else dw|||(db|||cr))&&&se==se)&&f t1 (w :: b :: r)))) ||
        (slack ≥ 2 &&
          ((if t2 then dwu|||(dau|||(dbu|||cru)) else dw|||(da|||(db|||cr)))&&&se==se) &&
          f t2 (w :: a :: b :: r)))
lemma q08 {a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun q7 qe s ((if neg then a^^^q7 else a) :: kept save a rest))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a):=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length:= by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩; rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have hrun:=Run.perm ((y1 pr save a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases save with
  | false =>
    simp only [kept,Bool.false_eq_true,ite_false] at ht hrun hcov
    have hlen : ((if neg then a^^^q7 else a) :: ws.erase a).length=ws.length:= by
      simp [List.length_erase_of_mem ha]; omega
    rw [hlen] at ht
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h1,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [hcov,ht]
  | true =>
    simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2-ws.length:= by omega
    have hlen : ((if neg then a^^^q7 else a) :: a :: ws.erase a).length=ws.length+1:= by
      simp [List.length_erase_of_mem ha]; omega
    have hlen_eq : decide (((if neg then a^^^q7 else a) :: a :: ws.erase a).length=s+1)=decide (ws.length=s):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
    rw [hlen_eq] at ht
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · have h1 : ws.length ≠ s+1:= by omega
      simp only [h1,h2,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma u9 {a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hlenr : ((ws.erase a).erase b).length=ws.length - 2:= by
    have:=pr.length_eq; omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩; rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have hrun:=Run.perm ((y1 (y1 pr kb b) ka a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases ka <;> cases kb
  · simp only [kept,Bool.false_eq_true,ite_false] at ht hh hrun hcov
    have hlen : ((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=ws.length - 1:= by
      simp [hlenr]; omega
    have hle : decide (((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s+2):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    by_cases h0 : ws.length=s+2
    · have hcu:=rl hrun (by omega)
      simp only [h0,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,decide_false,s9] at ht hcov ⊢
      simp [hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: b :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr]; omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr]; omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=ws.length+1:= by
      simp [hlenr]; omega
    have hle : decide (((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s):= by
      rw [hlen]; exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h2,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma q07 {a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  rcases le_total a b with hab | hba
  · exact u9 hab p h f hf
  · apply u9 (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a&&&b else a|||b)=(if conj then b&&&a else b|||a):= by
      cases conj <;> simp [Nat.and_comm,Nat.or_comm]
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
lemma q1f {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t=0->ws=[y]:= by
  induction h with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one=>simp
  | two=>simp
lemma y0 {t ws} (h : NatRun q7 qe t ws) :
    ∀ s,t=s+1->∀ zs,ws.Perm zs->∀ f : Bool->List Nat->Bool,
      (∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true)->vy s zs f=true:= by
  induction h with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | one _ _ h _=>intro s he zs p f hf; cases he; exact q08 p h f hf
  | two _ _ _ h _=>intro s he zs p f hf; cases he; exact q07 p h f hf
def xs517 : List ℕ:=[0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517,0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827,0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248,0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0,0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418,0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800,0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688]
lemma yn : ∀ zs ∈ xs517.sublists,zs ≠ xs517 →
    (s9 zs&&&se) ≠ se:= by decide +kernel
def r2 (tag d w : Nat) : Nat:=((w&&&tag)<<<d)|||((w>>>d)&&&tag)
lemma q3l (tag d i w : Nat) (h : (tag&&&(tag<<<d))=0) :
    (r2 tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag<<<d).testBit i then w.testBit (i-d) else false):= by
  have ht:=congrArg (fun v : Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [r2,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at*<;> grind
lemma yw (tag d : Nat) (h : (tag&&&(tag<<<d))=0) (a b : Nat) :
    r2 tag d (a&&&b)=(r2 tag d a&&&r2 tag d b) ∧
    r2 tag d (a|||b)=(r2 tag d a|||r2 tag d b) ∧
    r2 tag d (a^^^b)=(r2 tag d a^^^r2 tag d b):= by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,q3l tag d i _ h] <;>
    split_ifs <;> simp
lemma q0b {s ws} (h : NatRun q7 qe s ws) (tag d : Nat)
    (hz : (tag&&&(tag<<<d))=0) (hm : r2 tag d q7=q7)
    (hy : r2 tag d qe=qe) :
    NatRun q7 qe s (ws.map (r2 tag d)):= by
  rw [← hy]
  exact Run.map _ (fun a=>(yw tag d hz a q7).2.2.trans (by rw [hm]))
    (fun a b=>(yw tag d hz a b).1) (fun a b=>(yw tag d hz a b).2.1) h
def q3e : Nat:=0x3ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff
def q3d : Nat:=0xfffffffffffffffffffffffffffff00000000000000000000000000000fffffffffffffffffffffffffffff
def q38 (xs : List Nat):=xs.map (r2 q3e 58)
def q37 (xs : List Nat):=xs.map (r2 q3d 116)
lemma q3j {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q38 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
lemma q3i {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q37 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
def vf (a b c d e f : Bool) : Nat :=
  let x:=b.toNat+c.toNat; let y:=(!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)
lemma q0q : ∀ a b c d e f g h i j l m : Bool,
    vf (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q1g : ∀ a b c d e f g h i j l m : Bool,
    vf (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q05 {l r : List Nat} (h : l.Perm r) : l.sum=r.sum:= by
  induction h with
  | nil=>rfl
  | cons _ _ ih=>simp [ih]
  | swap=>simp; omega
  | trans _ _ ih1 ih2=>exact ih1.trans ih2
lemma q01 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (v : Nat->Nat) (hand : ∀ a b,v (a&&&b) ≤ v a+v b)
    (hor : ∀ a b,v (a|||b) ≤ v a+v b) : v y ≤ (ws.map v).sum:= by
  induction h with
  | done=>simp
  | perm p _ ih=>rw [← q05 (p.map v)]; exact ih (p.length_eq.trans hl)
  | one _ save h _=>have hh:=run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc,← hand]; exact ih' | grw [← Nat.add_assoc,← hor]; exact ih'
def yz (a b c d e f v : Nat) : Nat :=
  if v.testBit a then
    if v.testBit d then (!v.testBit e).toNat+(!v.testBit f).toNat
    else
      let x:=(v.testBit b).toNat+(v.testBit c).toNat
      let y:=(!v.testBit e).toNat+(!v.testBit f).toNat
      max x (max y (x+y - 1))
  else
    if v.testBit d then 0
    else (v.testBit b).toNat+(v.testBit c).toNat
lemma q0e (a b c d e f v : Nat) :
    yz a b c d e f v=vf (v.testBit a) (v.testBit b) (v.testBit c)
      (v.testBit d) (v.testBit e) (v.testBit f):= by
  unfold yz vf
  cases v.testBit a <;> cases v.testBit d <;> rfl
lemma q0f {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (a b c d e f : Nat) : yz a b c d e f y ≤ (ws.map (yz a b c d e f)).sum:= by
  apply q01 h hl
  · intro v w; simp only [q0e,Nat.testBit_and]; exact q0q _ _ _ _ _ _ _ _ _ _ _ _
  · intro v w; simp only [q0e,Nat.testBit_or]; exact q1g _ _ _ _ _ _ _ _ _ _ _ _
def q26 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(462,447,452,215,221,207),(453,441,440,220,193,181),(445,410,360,199,216,201),(460,410,440,178,229,217),(459,461,454,220,89,205),(370,438,302,215,216,211),(457,410,418,199,207,201),(403,428,450,207,201,220),(457,429,450,218,207,201),(456,452,454,219,201,199)]
lemma zy : q26.all (fun t =>
    yz t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 qe==3)=true:= by decide +kernel
def yh (a b c d e f : Nat) : Nat->List Nat->Bool
  | acc,[]=>decide (acc<3)
  | acc,w :: t =>
    let acc':=acc+yz a b c d e f w
    if acc' ≥ 3 then false else yh a b c d e f acc' t
lemma zo (a b c d e f : Nat) (ws : List Nat) (acc : Nat)
    (h : yh a b c d e f acc ws=true) : acc+(ws.map (yz a b c d e f)).sum<3:= by
  induction ws generalizing acc with
  | nil=>simpa [yh] using h
  | cons w t ih =>
    simp only [yh] at h
    split at h
    · contradiction
    · have ih':=ih _ h
      simp only [List.map_cons,List.sum_cons]
      omega
def q0x (ws : List Nat) : Bool :=
  q26.any (fun t=>yh t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 0 ws)
lemma q1n {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    q0x ws=false:= by
  rw [Bool.eq_false_iff]; intro hk
  obtain ⟨t,ht,hlt⟩:=List.any_eq_true.mp hk
  have hg:=beq_iff_eq.mp (List.all_eq_true.mp zy t ht)
  have hb:=q0f h hl t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2
  have hs:=zo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 ws 0 hlt
  rw [hg] at hb; omega
def span (f : Nat->Bool) : Nat->Nat->Bool
  | 0,_=>true
  | n+1,i=>f i&&span f n (i+1)
theorem span_ok {f n o} (h : span f n o=true) : ∀ i,o ≤ i->i<o+n->f i=true:= by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem span_join {f a o b} (ha : span f a o=true) (hb : span f b (o+a)=true) :
    span f (a+b) o=true:= by
  induction a generalizing o with
  | zero=>simpa using hb
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at ha; rw [Nat.succ_add,span,Bool.and_eq_true]
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩
lemma q10 {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r):= by
  induction t,hle using Nat.le_induction with
  | base=>exact h
  | succ _ _ ih=>exact Run.one false false ih
def q36 : Nat->Nat
  | 0=>0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517
  | 1=>0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827
  | 2=>0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248
  | 3=>0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0
  | 4=>0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418
  | 5=>0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800
  | 6=>0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688
  | 7=>0
  | 8=>q7
  | 9=>0x6f27d5b39727ae1b49f56d29a9e3808d7be5d22ba78c2bdef96c46fbe3004202ba9605a60011c4cfa98141800adbd4521ba18002a2b30446eae0
  | _=>0xff28d8b3df67b7254ff5613bb923c9858b85d6afa3524efe7b0f67d3e780c202bad625b22001c441b981418808fbd4560ba1020282330546c2e0
def q24 : Nat->Nat
  | 0=>0x2e0060280e268192c8192a0162b81918806200192a019000081000503005188191880917801268a50013001001001280180a1481912811230110080214811218110300219811200110280616805020051e015000ec018011c8151481a16819178151a8150300a1981503006188150000017809030121680902812000ac01802148150000c10009118191281501006118150200a0b80910011030160f0150200602811098010d001028050a8050b811030150a8090280d098090300d08805028090780503011068050200d0580502009
  | 1=>0xb80e01806419520b952099521f152549510004c1d812531e91f00e520163d00d33951231511d8160027c00801000044e01601805268052a005380a51881610012421b2498fa3601206816188121f0c6068c62b0121e15129012380c50022801002440c5001482481242812030010b8120011829016308161f016078163e81a01809338c5001e802002188053081a1f01a178050581a0e81a0881a0d01a38019001bc0100536819001b0028011e0193481920002338190003432819320060280a3101900184020012f819168062e819
  | 2=>0x378a62080a1f00a1b80a0b80a0780a0d00a0d80a0c00a7ca290e80a0800a0700a7a80900074368096a132338097800914806230090b8a60d0a6260a61f0a6748a500068368a5730a50005c001703d0a514801708a5000f8002e8440a50030414809378c637812378161e0056b8051780a3781a1180519809200093200514805378013b00e2b00e2980e590ad1f80e530ad612e93d80e581b21a00e3c80e1100e613052600e0300e5d9b25eae95e9293600e5dae90d00e0200e0c00e580ad0900e0d80e0800e0600e591292900e582bd
  | _=>0x5e9327780e001f4000185200a9e8fa000540001412802000102b0023b002290026a802378021d80a0b80214802110029fc691f0029ec6906802090020c0020800207002060022a00652006591be6a80e6900e3780e6800e1d806002701a806260064f80a1780606806100060a806360060b80692006030090880642806078060e806730054f81a450053d0058d005028021680a1880a778124180a0680a148126e812260121000a778163600a14816360a6260163d8a63b00a2b00a2900a2880a0980a290a61480a
def zf : Nat->Nat->Nat
  | 0,_=>0
  | fuel+1,i =>
    if i<11 then q36 i
    else
      let k:=i - 11
      let c:=(q24 (k/83)>>>(20*(k % 83)))&&&1048575
      let op:=c&&&3
      let a:=(c>>>2)&&&511
      if op=0 then zf fuel a^^^q7
      else let b:=c>>>11; if op=1 then zf fuel a&&&zf fuel b else zf fuel a|||zf fuel b
def q2a : Nat->Nat
  | 0=>0x181dc00005ff70000179dc00005ef70000175dc00005cf70000171dc00005bf7000016ddc00005af70000169dc00005977000022fec000085fb004b86de40000857b0000211ec000081fb0050205e80000817b0000203ec0144807a0000201ec00007d7b00001fbec00007e7b00001f7ec00007cfb00001f1ec008b977c3d91c83f0014493fc0000295f80000a4fe000028ff80000a37e0000289f80000a07e0000285f80000a0fe000027ff800009efe0000279f800009dfe0000275f800009cfe0000001fc0000907d00001efec00007afb00001e9ec000079fb00001e5ec0146787a00001e1ec00006efe00001b5f400006cfd000015fec0000577b000015bec0000567b0030cabcc01332af3000a8abcc00b32af30029cabcc00b12af3002f8abcc00bc2af300518abe801442afa00500abe800002afb0000157ec0000527b0000147ec00c34ff5004cd3fd4002a4ff5002cd3fd400a74ff5002c53fd400be4ff5002f13fd454554ff10000139f400004d770000125f8000048fe0030c65d801331976000a865d800b319760029c65d800b119760031865d800be1976002f065d80110197a0042065e80102197a0040065e800fa197a004b865f00128197c0049c65f00000197e003c065e8545519720015465e8549f19740027c65f0aa9f1978000011fec000046fe0000115f800003efe0011ceff40000393f00000defc0000363f00000d6fc000034bf00000cefc0000323f00000c2fc00002fbf00000b8fc00002dbf00154b6ec00002cbf000c8b2f8014d2b9f00194ae7c005d2b9f0020cae7c014b2baf00240aebc002a2bb70033caedc010a2bbb0049caef4014a2bbe00000aefc00552bbb0027caef400322bbe000009fdc013e1fee002947f9c00001f5f000a8775c00001ddf328d8306c00be0c5700440316c011888cb00435b92c00c84bc70053d2d3801375355004f94d58012b515525cf8498801538c630030db98c013754e500001519c01509bf10051657c401509f720054e8dc8004785f9002f8ae5c01102b9b
  | 1=>0x45fc014b086f000c021bc002a08770000021fc0055087b0027c21f40032087e0000041fc014b0f6f000b83dbc002a0f77003e83dec00000f7f001543dec00320f7e0054436fc014d0ddf00104377c014b0def000a837dc00bc0df70010437f400000dff0015437ec009f0dfd000c837f800000eff0000039fc00000d7f0000033fc00000bff000002bfc000009ff0000023fc000007ff000001bfc002a04770000011fc0055047b000c811fa9b4b154700536973c014d6e4f0052db73c00dc6dcfa6d2cab2e9b4b194e005351d3c014d43cf005350b3c005d42cf0030e1b5c014d155700434555c01336dd7000a9b75e9a2a2ad3000b1455c00b05157000a9455e9a2a4fd5002c13d5c002a4f57000a9295e9a2a19560052d073c008e41cf000a9075c007b40cf0052d033c002a40d70029d035c014b156700450559c01131567004cdb99c002a6e67a58a8ab8c00b054e7000a9539c002a4ae7a58a86598002a4767002cd1d9c002a4467000a90f9c002a42e7002c50b9c00c345f3000b28bcc014558730030c49cc00c31b730030e5dd4004b95f50012e7dd80000aa7700002a7dc000061f70000017dc00009b77000026bdc00009a770051a67d8000099f70000265dc000087770000219dc000083770000209dc0153787300001dfdc0000777700001dbdc000076770051455cc011615730044055cc010915730041c55cc010215730040055cc00fa1573004c455d4012e1575004ac55d4012815750049c55d4013e15760052055d8014615760051055d8014015760000055dc00f21573003c055cc000075f700001d3dc0000747700001cbdc000071f700001c1dc00c3387300001a1dc000067f7000019ddc010959f30052167d8000059f7000019bdc012b5df50000199dc010253f30007d4fd4014053f6000014fdc000065f70000195dc000064f7004acbbd4013e2ef60000191dc00000577000018fdc010058f30049d63d4014458f60000163dc00006377000018bdc000062770000183dc01105f73004a17dd400005f77
  | 2=>0x1a5fc000068ff000009dfc00002d7f000a8abcc002a2af700024abec00472afb00000abec01382afb00098abec00412afb000d0abec00022afb00280abec00362afb00000abfc002a2afb001c0abec005a2afb00154abec000050ff000a93fd4002a4ff70000137fc00554dfb0000133fc00004c7f000a85ddc0047177f000005dfc0055177b0000127fc002a1977000a865d80009197e0011c65f8014b197e0011065f8008b197e0046c65f80000197f0009865f80058197e0010465f80034197e0000865f80000197e0028065f80119197e0019465f80036197e0000c65f8002a197e0013465f80070197e0015465ec0055197a0015465f8009f197e0027c65f00099197e000b865f80093197e000c865f8002a18770011c61fc0000187f0015461ec009f187d000c861f80000467f000010bfc0000427f000a843dc000010ff0015443ec003210fe0000107fc0000417f0000103fc0000407f00000fffc00003e7f00000f5fc00323d7e00000f3fc00003c7f00000effc00003b7f00000ebfc00003a7f00000e7fc014d03df0052c0fbc002a03f7000000ffc005503fb0027c0ff4003203fe00000aefc00412bbf00000affc00002b7f00154adec00002a7f00000a5fc0032297e00000a3fc003228fe00000a1fc0000267f000a895dc0000257f0000093fc0000247f000a88ddc0000237f000008bfc000021ff0000085fc0000207f005447efc00781fbf005347f7c00811fdf001ec7fbc014b1fef0007c7fbc002a1ff70029c7fdc01021ffb0007c7ff401401ffe000007ffc00551ffb0027c7ff400321ffe0000073fc00001c7f000006ffc00001aff0000067fc003219fe00534317c00650c5f00174317c00210c5f000a831dc00b10c770040031ec01440c7e0000031fc00550c7b000c831f800530c3f0000063fc000017ff000005bfc002a15f70000057fc000014ff0000051fc000013ff000004bfc0151093f00534257c0065095f0052c25bc002a09770019425ec0000097f0015425ec009f097d000c825f8000011ff
  | _=>0x7f0000055dc000023ff0000001fc0000137f0000083fc00001a7f0000005fc0000507f000006dfc000001ff0000055fc0000387f00000abec00002aff000005dfc0000197f0000065f80000187f0000043fc000003ff000007ffc00000c7f0000025fc0000087f000003dfc00000dff00536973c014d15570052c559c002c25f70000187dc004b58770000267dc00091577000b055dc004b15770054455dc007b15770053455dc004715770052c55dc004415770022c55dc011b15770050c55dc000115770000055dc00b01577003c455dc002615770007c55dc00411577000d055dc000215770028055dc002415770045455dc006515770043c55dc00361577000e855dc010515770000c55dc002a1577000a9c9dc002a6f770030c9bdc002a26f7004cce1dc002a3877000a9a5dc00b06177000a985dc000059f7002c177dc002a5df7000014fdc002c2ef7002c0bbdc002a2ef700308bbdc000058f7000017ddc00005e770012c6dec00261b7b001946dec0000817b0000201ec00007d7b0011c89f8004745fe000028df800448dfe0000289f80000a07e0000013fc0000a97f0000155fc0000a77f00000d5fc0000347f0000299fc000023ff0000287fc0000007f00000bdfc00009c7f0000261fc0000337f000025ffc000078ff000004dfc0000977f000025bfc0000307f0000259fc00002c7f0000255fc007b20ff0000083fc000094ff0000251fc00001a7f000024ffc0000937f0000249fc000091ff0000245fc000090ff0000005fc00008fff000023dfc00008eff0000239fc0047507e0000141fc00008d7f000007bfc00006c7f0000233fc00008aff0000225fc000087ff000006dfc00001d7f000020bfc0000817f0000201fc00007fff00001fdfc00007d7f0000007fc0047787b00001e1ec0000787f0000055fc0000737f00001c9fc000070ff00001bffc00006f7f00001b7fc00006bff00001adfc00006aff00001a9fc000069ff00098e1ec0065387b00098e1f40146387e00000e1fc004d387b
def xl (code k : Nat) (acc : List Nat) : List Nat :=
  if (code>>>k)&&&1==1 then q36 k :: acc else acc
def z0 (e : Nat) (acc : List Nat) : List Nat :=
  if e==0 then acc else zf 4 (e - 1) :: acc
def q3k (i : Nat) : List Nat :=
  if i<6 then []
  else
    let j:=i - 6
    let code:=(q2a (j/176)>>>(34*(j % 176)))&&&0x3ffffffff
    let acc:=z0 ((code>>>25)&&&511) (z0 ((code>>>16)&&&511) (z0 ((code>>>7)&&&511) []))
    xl code 0 (xl code 1 (xl code 2 (xl code 3 (xl code 4 (xl code 5 (xl code 6 acc))))))
def q25 : Nat->Nat
  | 0=>1 | 1=>1 | 2=>1 | 3=>1 | 4=>1 | 5=>1
  | 6=>19 | 7=>292 | 8=>365 | 9=>26 | 10=>1 | _=>0
def q3t : Nat->Nat
  | 0=>0 | 1=>1 | 2=>2 | 3=>3 | 4=>4 | 5=>5
  | 6=>6 | 7=>25 | 8=>317 | 9=>682 | 10=>708 | _=>0
def vj (s i : Nat) : List Nat:=q3k (q3t s+i)
def sg (salt : Nat) : List Nat->Nat
  | []=>0
  | w :: t=>let x:=(w % 1048573+317+salt) % 1048573; (x*x*x) % 1048573+sg salt t
def q18 : Nat->Nat
  | 6=>0x2d510a29c920dd8c26046a45edcab10e217235801e802cc829b
  | 7=>0xba020271000f0d789715b90b1b40d05ca2d4a2b20600798bac5c7e51085e9a4554cdd8e3980600005246e24e7704c2f50005cd6d23c0e8ee0943e87206f17bbbe2205918c9ad6d8c4dd10000ca1d4a0086754ac52a4592ac768220bc3fc1f922c761b4a30630003be5e00833f0d0d88b41f41811e4783cf36e2dc004002e0fbd5d8007d4b20a617c1680000029e1429da3348d12e9adfc1e03a65ca0c0b8279042040b6832081c4a94630e90120006c8e7618c585e8478000000e0b5e3abee6724d0dc28a4f63f1783c6676dd56abce0000e08019e42acc8c20d74cc7606228d6fa4e030800778001c584c7764b0a4ac49105d1a648c4486522847d50cc6e20a0c4d4e35f0901710e0cf40515302009b2095a0370e248f4c04163a3ab0e2840000aa000b85763445f112a350607800000029000006d184643c45988fb302401912822c64a9d0e0251912f598a0f42b8671a88181a41b0d04218a2434643e58a8f31b8394262fda061372b12394e130690d75503ca3d8870b697b212c6a301b50092181d0146e85e85835b2103bcf84497750e5ff1886ee6a8460501e2ebd824067cd205840001d91dcb18003c8b01d480c8280d067c358d0e1c820064b038188b0c722360a82b46ecd1d3fb780008508e3d453439e0ab8c320211da96c49235238a77476931a93a75666c63f3553f2880e4054184a210f404408b042709674c3e1af888398a483c3b7302460aa0ba8f06319693b13a3a09d00888a0a912af60582b10c1d65990a588472078ca40e9987a0801342287b47757e41d838d2941b3c228ff1c54020aac9092059006afd1a425090c482c4850b8cf9379f87621756ebdc27d118652a69049007e8914bf0f0b012a684ab49f802050ea22623a
  | 8=>0x138c54934604ac03d9da53893a963200001f918326961401461089814d14c94c238451f64d35929b4ffaf00002f2588000001a6d1c3b8e552048160000c7da4508a12ea26db16296bd4174c85145c2c45633c2b20c82402f83540b8c291ccda0a2c69e6c9eca21c2a0b32380b2a0ac60a180095d0bdd04b246a3d513ace3aa972874da6d12706ca58000a1009a100ee43944337528b29fa491af5485ec98a38a278ca0421a2b04903aa0829c0915225ecb49060815d8002cecf16671685a93052a10eaaae5249586bf0f0aeca69a030a2190e0e420b1707a822828a486a0ae27e4f50b56214a3320d56cc656d4d911c53d81c0725307c8d2be5faaad16f4d8a258091347291cdca1ed5dec5685f09208d2be2b0f502b18c1101fd8bd580c6170a10af63b6318d13b231385cca428188a62b26c28e949168927081b0890e0aba9e0040269400f2c59014d6670b590016363c59c58138de07c8391f105e2808a0c869d46aed6a82117f42080ed12ba0f4b08151da27cb0f180e20dc9fc0023e5a74085eeb944fafa110bfa19830b40f68686160013b2a22082398f4d442f04a620c4000002211d407031a26c888514480034f1ec65800402a400009c1dd13a932c83919f0c00c2376858002822bc3b9462330991510e6a11296a7530cb8219c518464554899170005ac7f05a12d2600002d1fe000000ac43043324a781ff1c1670760b312c69b2299d1e869c551c62a085d028515a82d93ea730a41d9582a81a063800064be426b5cda8b35174b0a59ccc19eb0245b5245d516d8cf57e4544e80150494c2cf8955b0486364e79f2176764c5478cc4ba000900101ed355380392a1d0c118ee1e423a000d31ba36028c1d118b2471a0c4a48007988d1162e80315e2742680a1598944bc9701e1a83102201b47e05816d544fc03083d4a2082920003001556e38c3f44a4407c0b76562d488805032b9427aaa016464000c1819282a82a618a37e140351d5b805d33781b1956d8ad29e01d930119822ac0560012e9fb018131e24d99695c1669c70006f92a2f4950b72cc325400c21231616587088b0ae90ab9002000855500f60005c2a99970ac8911b97e567000260a0514712600cc4367782c01f106669099ad2f73c6dc179d7f360515401b83e8990e65933865e276a50ac4592ae0cc5c09959456c2e2ea5d640f052e4008538372c1ca41de619665ae3b03b725475bc0369359ab3324d26b08f0005715f1e84df000cf83393c7b87923c256875510243753e0a908db9dac89d023a20b44cc289be83c53bec083f3780ccda9df0013f63a4a274ca400001181acf03821d7b6c547d43c
  | 9=>0xa197f9864cac828bcc96272d000622a0801403cb48d000b1ebd4114d11504f80408a7451700016502d6981bb801d1148e240e1f1b0344d9ea8d30f4e10
  | _=>0
def q17 : Nat->Nat
  | 6=>0x6d235ea20
  | 7=>0x234342c80020021d2500aec0506cac86608011a05070243405480089c0601bd838e5329f00e0429190060a0788c0230151a47435248086e14000c806004980012037e2603c050381010011a978040100000c03a0388c0e461502408295081442751882c1a0000038001c00000240503018180003014000d098080233
  | 8=>0x20e334d381e85e0400d6900336c4f00e1846c1e225571d8f3650040e03b0143103c0112c380e421004c3088010408f0104101c02228630140e03c0f00c2b18c01018020f002008e13181403001164360218b004672203d074b7000000904100c3117008118960500812827084700004a000b30d4020ac01000b606003004170041a01c0810c5c00827034690d80d04c1206c000100700431038000182b02801040000640515c37008013400f0180102c330140d02c0000816078000100b000ad000000000102c20010040004800016
  | 9=>0xd16e05d801451001402c9040
  | _=>0
def q16 (s : Nat) (zs : List Nat) : Nat :=
  match s with
  | 6 =>
    let h:=sg 11 zs % 1048573
    let d:=(q17 6>>>(5*(h % 7)))&&&31
    let slot:=((h*1001) % 1048573+d) % 29
    (q18 6>>>(7*slot))&&&127
  | 7 =>
    let h:=sg 0 zs % 1048573
    let d:=(q17 7>>>(9*(h % 110)))&&&511
    let slot:=((h*17) % 1048573+d) % 463
    (q18 7>>>(11*slot))&&&2047
  | 8 =>
    let h:=sg 1 zs % 1048573
    let d:=(q17 8>>>(10*(h % 166)))&&&1023
    let slot:=((h*1) % 1048573+d) % 695
    (q18 8>>>(11*slot))&&&2047
  | 9 =>
    let h:=sg 13 zs % 1048573
    let d:=(q17 9>>>(6*(h % 16)))&&&63
    let slot:=((h*31) % 1048573+d) % 71
    (q18 9>>>(7*slot))&&&127
  | _=>0
def yd (g : Nat) (ws : List Nat) :=
  if g=0 then ws else if g=1 then q38 ws else if g=2 then q37 ws else q38 (q37 ws)
lemma q0v (g : Nat) {s ws} (h : NatRun q7 qe s ws) :
    NatRun q7 qe s (yd g ws):= by
  unfold yd; split
  · exact h
  · split
    · exact q3j h
    · split
      · exact q3i h
      · exact q3j (q3i h)
def qh : Nat->Nat->Bool
  | 0,i=>!(vj 0 i==[qe])
  | s+1,i =>
    let ws:=vj (s+1) i
    !(vy s ws fun tight zs =>
      !(tight&&q0x zs) &&
      (let v:=q16 s zs; !(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4)))))
lemma zc {s i} (hb : qh s i=true)
    (h : NatRun q7 qe s (vj s i)) :
    ∃ q<s,∃ j<q25 q,NatRun q7 qe q (vj q j):= by
  cases s with
  | zero=>simp [qh,q1f h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tight : Bool) (zs : List Nat):=!(tight&&q0x zs) &&
      (let v:=q16 s zs; !(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4))))
    have hF (zs) (hz : NatRun q7 qe s zs) : F (decide (zs.length=s+1)) zs=true:= by
      simp only [F,Bool.and_eq_true,Bool.not_eq_true']
      constructor
      · by_cases hl : zs.length=s+1
        · simp [hl,q1n hz hl]
        · simp [hl]
      · simp only [Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj; by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (q0v _ hz))
    have hN:=y0 h s rfl _ (List.Perm.refl _) F hF
    change !(vy _ _ F)=true at hb; rw [hN] at hb; contradiction
lemma q0k {cap : Nat}
    (hc : ∀ s ≤ cap,∀ i<q25 s,qh s i=true) :
    ∀ s ≤ cap,∀ i<q25 s,¬ NatRun q7 qe s (vj s i):= by
  intro s; induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩:=zc (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h
set_option maxHeartbeats 0 in
lemma q3h :
    qh 0 0=true/\qh 1 0=true/\qh 2 0=true ∧
    qh 3 0=true/\qh 4 0=true/\qh 5 0=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma z6 : span (qh 6) 19 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3s : span (qh 7) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3r : span (qh 7) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3q : span (qh 7) 92 200=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3p : span (qh 8) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3o : span (qh 8) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3n : span (qh 8) 100 200=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3m : span (qh 8) 65 300=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma z9 : span (qh 9) 26 0=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma q3z : span (qh 10) 1 0=true:= by decide +kernel
lemma z7 : span (qh 7) 292 0=true:=(@span_join (qh 7) 100 0 192 q3s (@span_join (qh 7) 100 100 92 q3r q3q))
lemma z8 : span (qh 8) 365 0=true:=(@span_join (qh 8) 200 0 165 (@span_join (qh 8) 100 0 100 q3p q3o) (@span_join (qh 8) 100 200 65 q3n q3m))
lemma q2x (s : Nat) (hs : s ≤ 10) : ∀ i<q25 s,qh s i=true:= by
  interval_cases s
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.2.1
  · intro i hi; simp only [q25] at hi; have h0 : i=0:=(by omega); subst h0; exact q3h.2.2.2.2.2
  · exact fun i hi=>span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok q3z i (Nat.zero_le i) hi
theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False:= by
  rw [← vb,← vc] at h
  have h10 : NatRun q7 qe 10 xs517:=q10 h hs
  have p : xs517.Perm (vj 10 0):= by decide +kernel
  exact q0k q2x 10 (by decide) 0 (by decide) (Run.perm p h10)
theorem noSub {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs517)
    (h : NatRun (mask 232) (goal 232) s ws) : False:= by
  by_cases eq : ws=xs517
  · subst ws; exact noRunFull _ hs h
  · rw [← vb,← vc] at h
    exact yn _ (List.mem_sublists.2 hsub) eq (vl h)
end Theta
abbrev q0:=Nat × Nat
def rx : Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def rm (x : Nat) : Nat:=x^^^rx
def rv : q0:=(0,0)
def v5 : q0:=(rx,rx)
def qc : q0:=(rx,0)
def qx (a : q0) : q0:=(rm a.1,rm a.2)
def qn (isOr : Bool) (a b : q0) : q0 :=
  if isOr then (a.1|||b.1,a.2|||b.2) else (a.1&&&b.1,a.2&&&b.2)
def qr (x : Nat) : Prop:=∀ j,252 ≤ j->x.testBit j=false
def qb (a : q0) : Prop:=qr a.1/\qr a.2
def qd (a : q0) : Prop:=qb a/\a ≠ rv/\a ≠ v5
def x3 : q0:=(0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def q1d : q0:=(0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def q1c : q0:=(0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230)
def yv : q0:=(0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def q1b : q0:=(0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def yu : q0:=(0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def yt : q0:=(0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def q1a : q0:=(0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)
def rj : List q0:=[x3,q1d,q1c,yv,q1b,yu,yt,q1a]
lemma y6 : rx=2 ^ 252 - 1:= by
  have h1 : rx=2 ^ 126*2 ^ 126 - 1:= by decide
  rw [h1,← Nat.pow_add]
lemma qg (j : Nat) : rx.testBit j=decide (j<252):= by
  rw [y6]; exact Nat.testBit_two_pow_sub_one 252 j
lemma uw {x : Nat} (hx : qr x) (j : Nat) :
    (rm x).testBit j=if j<252 then !(x.testBit j) else false:= by
  simp only [rm,Nat.testBit_xor,qg]
  by_cases hj : j<252
  · simp [hj]
  · simp [hj,hx j (by omega)]
lemma q5 (x : Nat) {j : Nat} (hj : j<252) :
    (rm x).testBit j=!(x.testBit j):= by
  simp [rm,Nat.testBit_xor,qg,hj]
lemma sc : qr 0:=fun _ _=>Nat.zero_testBit _
lemma vh : qr rx:=fun j hj=>by
  rw [qg]; simp [show ¬ j<252 by omega]
lemma xm {x : Nat} (hx : qr x) : qr (rm x):=fun j hj=>by
  rw [uw hx]; simp [show ¬ j<252 by omega]
lemma s4 {x y : Nat} (hx : qr x) : qr (x&&&y):=fun j hj=>by
  rw [Nat.testBit_and,hx j hj]; rfl
lemma uz {x y : Nat} (hx : qr x) (hy : qr y) : qr (x|||y):=fun j hj=>by
  rw [Nat.testBit_or,hx j hj,hy j hj]; rfl
lemma q0s {x y : Nat} (hx : qr x) (hy : qr y) : qr (x^^^y):=fun j hj=>by
  rw [Nat.testBit_xor,hx j hj,hy j hj]; rfl
lemma uj {x : Nat} (h : x ≤ rx) : qr x:=fun j hj=>by
  have hlt : x<2 ^ 252:= by
    have hp : 0<2 ^ 252:=Nat.pow_pos (by omega)
    rw [y6] at h; omega
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hj))
lemma vg : qb rv:=⟨sc,sc⟩
lemma q0r : qb v5:=⟨vh,vh⟩
lemma z3 : qb qc:=⟨vh,sc⟩
lemma ye {a : q0} (ha : qb a) : qb (qx a) :=
  ⟨xm ha.1,xm ha.2⟩
lemma x9 (d : Bool) {a b : q0} (ha : qb a) (hb : qb b) :
    qb (qn d a b):= by
  cases d
  · exact ⟨s4 ha.1,s4 ha.2⟩
  · exact ⟨uz ha.1 hb.1,uz ha.2 hb.2⟩
lemma s0 (d : Bool) (a b : q0) : qn d a b=qn d b a:= by
  cases d <;> simp [qn,Nat.and_comm,Nat.or_comm]
lemma so {a : q0} (ha : qb a) :
    qn false a v5=a/\qn true a rv=a ∧
    qn false a rv=rv/\qn true a v5=v5 ∧
    qn false a a=a/\qn true a a=a:= by
  obtain ⟨p,n⟩:=a
  have hp1 : p&&&rx=p:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_and,qg]; by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn1 : n&&&rx=n:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_and,qg]; by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.2 j (by omega)]
  have hp2 : p|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg]; by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn2 : n|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg]; by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.2 j (by omega)]
  simp [qn,v5,rv,hp1,hn1,hp2,hn2]
lemma v6 : qx rv=v5/\qx v5=rv:= by
  constructor
  · simp [qx,rv,v5,rm]
  · simp [qx,rv,v5,rm]
def y7 (a : Sig) : q0:=(a.1.toNat,a.2.toNat)
lemma xb (x : B) : qr x.toNat:=fun j hj=>by
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hj))
lemma q1h (a : Sig) : qb (y7 a):=⟨xb a.1,xb a.2⟩
lemma xn : Function.Injective y7:= by
  intro a b h
  have h1 : a.1.toNat=b.1.toNat:=congrArg Prod.fst h
  have h2 : a.2.toNat=b.2.toNat:=congrArg Prod.snd h
  exact Prod.ext (BitVec.eq_of_toNat_eq h1) (BitVec.eq_of_toNat_eq h2)
lemma q28 : y7 zero=rv:=rfl
lemma q2y : y7 one=v5:= by
  apply Prod.ext <;> exact (by decide : (BitVec.allOnes 252).toNat=rx)
lemma q0t : y7 target=qc:= by
  apply Prod.ext
  · exact (by decide : (BitVec.allOnes 252).toNat=rx)
  · rfl
lemma q13 (a : Sig) : y7 (neg a)=qx (y7 a):= by
  have hnot (x : B) : (~~~x).toNat=rm x.toNat:= by
    apply Nat.eq_of_testBit_eq; intro j
    rw [BitVec.testBit_toNat,BitVec.getLsbD_not,uw (xb x)]
    by_cases hj : j<252
    · simp [hj,BitVec.testBit_toNat]
    · simp [hj]
  exact Prod.ext (hnot a.1) (hnot a.2)
lemma q14 (d : Bool) (a b : Sig) : y7 (bin d a b)=qn d (y7 a) (y7 b):= by
  cases d <;> simp [bin,qn,y7]
lemma xc {a : Sig} (ha : proper a) : qd (y7 a):= by
  refine ⟨q1h a,fun h=>ha.1 (xn (h.trans q28.symm)),
    fun h=>ha.2 (xn (h.trans q2y.symm))⟩
inductive qy : Nat->Nat->Finset q0->Prop
  | stop : qy 0 0 {qc}
  | unary {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) :
      qy (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) :
      qy (k+1) t (insert a (insert b U))
lemma z5 {k t : Nat} {S : Finset Sig} (h : Live k t S) :
    qy k t (S.image y7):= by
  induction h with
  | stop=>simpa [q0t] using qy.stop
  | @unary k t U a ha hf _ ih =>
    simp only [Finset.image_insert,q13] at ih ⊢
    have hf' : qx (y7 a) ∉ insert (y7 a) (U.image y7):= by
      rw [← Finset.image_insert,← q13]
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.unary (xc ha) hf' ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    simp only [Finset.image_insert,q14] at ih ⊢
    have hf' : qn d (y7 a) (y7 b) ∉ insert (y7 a) (insert (y7 b) (U.image y7)):= by
      rw [← Finset.image_insert,← Finset.image_insert,← q14]
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.binary (xc ha) (xc hb) (fun e=>hab (xn e)) hf' ih
lemma q00 {a : Sig} (ha : a ∈ raw) : y7 a ∈ rj:= by
  have h : raw.map y7=rj:= by decide +kernel
  rw [← h]; exact List.mem_map_of_mem ha
def r9 (d : Bool) (a : q0) : Nat :=
  if d then a.1^^^a.2 else a.1&&&rm a.2
def q9 (d : Bool) : List q0->Nat
  | []=>0
  | a :: l=>r9 d a|||q9 d l
def rg (a b : q0) : Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2
lemma rf (a b : q0) : rg a b=true ↔ a=b:= by
  cases a; cases b; simp only [rg,Bool.and_eq_true,Nat.beq_eq,Prod.mk.injEq]
def up (x : q0) : List q0->Bool
  | []=>false
  | y :: ys=>rg x y||up x ys
lemma y5 (x : q0) (l : List q0) : up x l=true ↔ x ∈ l:= by
  induction l with
  | nil=>simp [up]
  | cons y ys ih=>simp [up,rf,ih]
def v4 : List q0->Bool
  | []=>true
  | x :: xs=>!up x xs&&v4 xs
lemma ve {l : List q0} (h : v4 l=true) : l.Nodup:= by
  induction l with
  | nil=>exact List.nodup_nil
  | cons x xs ih =>
    simp only [v4,Bool.and_eq_true,Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨fun hm=>by rw [(y5 x xs).mpr hm] at h; exact Bool.false_ne_true h.1.symm,ih h.2⟩
def sn (x : q0) : List q0->Option (List q0)
  | []=>none
  | y :: ys=>if rg x y then some ys else
    match sn x ys with | none=>none | some r=>some (y :: r)
lemma yq {x : q0} {ys r : List q0} (h : sn x ys=some r) :
    ys.Perm (x :: r):= by
  induction ys generalizing r with
  | nil=>simp [sn] at h
  | cons y ys ih =>
    simp only [sn] at h
    cases he : rg x y
    · rw [he] at h
      cases hr : sn x ys with
      | none=>rw [hr] at h; contradiction
      | some r' =>
        rw [hr] at h; injection h with h; subst h
        exact ((ih hr).cons y).trans (List.Perm.swap _ _ _)
    · rw [he] at h; injection h with h; subst h
      rw [(rf x y).mp he]
def vp : List q0->List q0->Bool
  | [],[]=>true
  | x :: xs,ys=>match sn x ys with | none=>false | some ys'=>vp xs ys'
  | _,_=>false
lemma yp {xs ys : List q0} (h : vp xs ys=true) : xs.Perm ys:= by
  induction xs generalizing ys with
  | nil=>cases ys with | nil=>exact List.Perm.nil | cons _ _=>simp [vp] at h
  | cons x xs ih =>
    simp only [vp] at h
    cases he : sn x ys with
    | none=>rw [he] at h; contradiction
    | some ys'=>rw [he] at h; exact ((ih h).cons x).trans (yq he).symm
def qw (del v : List q0) : List q0:=v.filter (fun x=>!(del.contains x))
def vs (a : q0) : List q0->List q0
  | []=>[]
  | x :: xs=>if rg a x then vs a xs else x :: vs a xs
def ug (a b : q0) : List q0->List q0
  | []=>[]
  | x :: xs=>if rg a x||rg b x then ug a b xs else x :: ug a b xs
lemma q0h (a : q0) (v : List q0) : vs a v=qw [a] v:= by
  induction v with
  | nil=>rfl
  | cons x xs ih =>
    simp only [vs,qw,List.filter_cons,List.contains_eq_mem,List.mem_singleton] at ih ⊢
    by_cases h : a=x
    · subst h; rw [(rf a a).mpr rfl]; simp [ih]
    · have hf : rg a x=false:= by cases he : rg a x; rfl; exact (h ((rf a x).mp he)).elim
      have hne : decide (x=a)=false:=decide_eq_false (Ne.symm h)
      rw [hf,hne]; simp [ih]
lemma q0g (a b : q0) (v : List q0) : ug a b v=qw [a,b] v:= by
  induction v with
  | nil=>rfl
  | cons x xs ih =>
    simp only [ug,qw,List.filter_cons,List.contains_eq_mem,List.mem_cons,List.not_mem_nil,or_false] at ih ⊢
    by_cases h : a=x\/b=x
    · have ht : (rg a x||rg b x)=true:= by
        rcases h with rfl | rfl <;> simp [(rf _ _).mpr rfl]
      have hm : decide (x=a\/x=b)=true:=decide_eq_true (by rcases h with rfl | rfl <;> simp)
      rw [ht,hm]; simp [ih]
    · have ha : a ≠ x:=fun e=>h (Or.inl e)
      have hb : b ≠ x:=fun e=>h (Or.inr e)
      have hfa : rg a x=false:= by cases he : rg a x; rfl; exact (ha ((rf a x).mp he)).elim
      have hfb : rg b x=false:= by cases he : rg b x; rfl; exact (hb ((rf b x).mp he)).elim
      have hm : decide (x=a\/x=b)=false:=decide_eq_false (by rintro (rfl | rfl); exact ha rfl; exact hb rfl)
      rw [hfa,hfb,hm]; simp [ih]
abbrev y3:=Nat × Nat × Nat
def r0 (z : Nat) (c : y3) : y3 :=
  let nz:=rm z
  (z|||c.1,(z&&&rm c.1)|||(c.2.1&&&nz),
   (z&&&c.2.1)|||(c.2.2&&&nz))
def qz (d : Bool) : List q0->y3
  | []=>(0,0,0)
  | a :: l=>r0 (r9 d a) (qz d l)
def q0a (z : Nat) (c : Nat × Nat) : Nat × Nat :=
  (z|||c.1,(z&&&rm c.1)|||(c.2&&&rm z))
def zi : List q0->Nat × Nat
  | []=>(0,0)
  | a :: l=>q0a (r9 false a) (zi l)
lemma q2c (v : List q0) :
    (zi v).1=(qz false v).1/\(zi v).2=(qz false v).2.1:= by
  induction v with
  | nil=>exact ⟨rfl,rfl⟩
  | cons a l ih=>simp only [zi,qz,q0a,r0,ih.1,ih.2,and_self]
def vr (c : y3) (a : Nat) : Nat:=c.1&&&rm (c.2.1&&&a)
def uc (c : y3) (a b : Nat) : Nat :=
  c.1&&&rm ((c.2.1&&&(a|||b))|||(c.2.2&&&(a&&&b)))
def sv (c : y3) : Prop:=qr c.1/\qr c.2.1/\qr c.2.2
lemma rq (d : Bool) {a : q0} (ha : qb a) : qr (r9 d a):= by
  cases d
  · exact s4 ha.1
  · exact q0s ha.1 ha.2
lemma zl {z : Nat} {c : y3} (hz : qr z) (hc : sv c) :
    sv (r0 z c) :=
  ⟨uz hz hc.1,uz (s4 hz) (s4 hc.2.1),
   uz (s4 hz) (s4 hc.2.2)⟩
lemma ru (d : Bool) {v : List q0} (hv : ∀ a ∈ v,qb a) :
    sv (qz d v):= by
  induction v with
  | nil=>exact ⟨sc,sc,sc⟩
  | cons a l ih =>
    exact zl (rq d (hv a List.mem_cons_self))
      (ih fun b hb=>hv b (List.mem_cons_of_mem _ hb))
lemma q33 {c : y3} {a : Nat} (hc : sv c) (ha : qr a) :
    vr (r0 a c) a=c.1:= by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i<252
  · simp only [vr,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [vr,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hc.1 i hge]
lemma q32 {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    uc (r0 a (r0 b c)) a b=c.1:= by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i<252
  · simp only [uc,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [uc,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.1 i hge]
lemma zq {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    r0 a (r0 b c)=r0 b (r0 a c):= by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [r0,Nat.testBit_or]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> (apply Nat.eq_of_testBit_eq; intro i; by_cases hi : i<252)
    · simp only [r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
        cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
    · have hge : 252 ≤ i:= by omega
      simp [r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.2.1 i hge]
    · simp only [r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
        cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
    · have hge : 252 ≤ i:= by omega
      simp [r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.2.2 i hge]
lemma q0i (d : Bool) {l r : List q0} (h : l.Perm r) (hl : ∀ a ∈ l,qb a) :
    qz d l=qz d r:= by
  induction h with
  | nil=>rfl
  | cons a _ ih =>
    exact congrArg (r0 (r9 d a)) (ih fun x hx=>hl x (List.mem_cons_of_mem _ hx))
  | @swap a b t =>
    exact zq (ru d fun x hx=>hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      (rq d (hl b (List.mem_cons_self)))
      (rq d (hl a (List.mem_cons_of_mem _ List.mem_cons_self)))
  | trans p _ h1 h2=>exact (h1 hl).trans (h2 fun x hx=>hl x (p.mem_iff.mpr hx))
lemma zj (d : Bool) (v : List q0) : (qz d v).1=q9 d v:= by
  induction v with
  | nil=>rfl
  | cons a v ih=>change r9 d a|||(qz d v).1=r9 d a|||q9 d v; rw [ih]
lemma vq : qd qc:=⟨z3,by decide,by decide⟩
lemma qv {k t S} (h : qy k t S) : ∀ a ∈ S,qd a:= by
  induction h with
  | stop=>simpa using vq
  | unary ha _ _ ih=>simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩
lemma xg {k t S} (h : qy k t S) : t ≤ k/\S.card+t ≤ k+1:= by
  induction h with
  | stop=>simp
  | @unary k t U a _ hf _ ih =>
    have hu : qx a ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : qn d a b ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
lemma q1i (t : Nat) (a : q0) (i : Nat) (hi : i<252)
    (h : (r9 (decide (0<t)) (qx a)).testBit i=true) :
    (r9 true a).testBit i=true:= by
  cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> cases ht : decide (0<t) <;>
    simp only [r9,qx,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_and,
      q5 _ hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
lemma q0u (t d : Bool) (a b : q0) (i : Nat) (hi : i<252)
    (h : (r9 t (qn d a b)).testBit i=true) :
    (r9 t a).testBit i=true\/(r9 t b).testBit i=true:= by
  cases t <;> cases d <;>
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;>
    cases hu : b.1.testBit i <;> cases hv : b.2.testBit i <;>
    simp only [r9,qn,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_or,
      Nat.testBit_and,q5 _ hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
lemma yj (t : Nat) (a : q0) (i : Nat) (hi : i<252)
    (h : (r9 (decide (0<t)) a).testBit i=true) : (r9 true a).testBit i=true:= by
  cases ht : decide (0<t) <;> cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;>
    simp only [r9,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_and,
      q5 _ hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
lemma zh {k t S} (h : qy k t S) (i : Nat) (hi : i<252) :
    ∃ a ∈ S,(r9 (decide (0<t)) a).testBit i=true:= by
  induction h with
  | stop =>
    refine ⟨qc,by simp,?_⟩
    simp [r9,qc,Nat.testBit_and,q5 _ hi,qg,hi]
  | unary _ _ _ ih =>
    obtain ⟨x,hx,h⟩:=ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,q1i _ _ _ hi h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,yj _ _ _ hi h⟩
  | binary _ _ _ _ _ ih =>
    obtain ⟨x,hx,h⟩:=ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases q0u _ _ _ _ _ hi h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
lemma ss (d : Bool) (v : List q0) (i : Nat) :
    (q9 d v).testBit i=true ↔ ∃ a ∈ v,(r9 d a).testBit i=true:= by
  induction v with
  | nil=>simp [q9]
  | cons a v ih =>
    simp only [q9,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h | ⟨b,hb,h⟩)
      · exact ⟨a,Or.inl rfl,h⟩
      · exact ⟨b,Or.inr hb,h⟩
    · rintro ⟨b,rfl | hb,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,hb,h⟩
lemma q09 {k t S} {v : List q0} (h : qy k t S) (he : v.toFinset=S) :
    q9 (decide (0<t)) v=rx:= by
  apply Nat.eq_of_testBit_eq; intro i
  rw [qg]
  by_cases hi : i<252
  · obtain ⟨a,hm,ha⟩:=zh h i hi
    have hmem : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ hm)
    simp only [hi,decide_true]
    exact (ss _ _ _).2 ⟨a,hmem,ha⟩
  · simp only [hi,decide_false]
    rw [Bool.eq_false_iff]; intro ht
    obtain ⟨a,ha,hbit⟩:=(ss _ _ _).1 ht
    have hv : qb a:=(qv h a (he ▸ List.mem_toFinset.mpr ha)).1
    have hf:=rq (decide (0<t)) hv i (by omega)
    rw [hf] at hbit; contradiction
lemma zm (d : Bool) (l r : List q0) :
    q9 d (l++r)=q9 d l|||q9 d r:= by
  induction l with
  | nil=>simp [q9]
  | cons a l ih=>simp [q9,ih,Nat.or_assoc]
def s8 (U : Finset q0) (del : List q0) : List q0 :=
  del.filter (fun a=>decide (a ∈ U))
lemma vz {v del : List q0} {U : Finset q0}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset=del.toFinset ∪ U) :
    (s8 U del++qw del v).Nodup/\(s8 U del++qw del v).toFinset=U:= by
  have memv (x : q0) : x ∈ v ↔ x ∈ del\/x ∈ U:= by
    rw [← List.mem_toFinset,he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq; subst b
    simp [s8] at ha; simp [qw] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,s8,qw,
      decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all
lemma u0 (del v : List q0) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del,x ∈ v) : v.Perm (del++qw del v):= by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e; subst b
    simp [qw] at hb; exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,qw,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma q2b (d : Bool) {v : List q0} {a : q0} (hv : v.Nodup) (hval : ∀ x ∈ v,qb x)
    (ha : a ∈ v) :
    v.length - 1=(qw [a] v).length ∧
      vr (qz d v) (r9 d a)=q9 d (qw [a] v):= by
  have p:=u0 [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l:=p.length_eq; simp at l; omega
  · rw [q0i d p hval]
    have hvd : ∀ x ∈ qw [a] v,qb x:=fun x hx =>
      hval x (p.mem_iff.mpr (List.mem_append_right _ hx))
    exact (q33 (ru d hvd) (rq d (hval a ha))).trans (zj _ _)
lemma q27 (d : Bool) {v : List q0} {a b : q0} (hv : v.Nodup)
    (hval : ∀ x ∈ v,qb x) (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2=(qw [a,b] v).length ∧
      uc (qz d v) (r9 d a) (r9 d b)=q9 d (qw [a,b] v):= by
  have p:=u0 [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l:=p.length_eq; simp at l; omega
  · rw [q0i d p hval]
    have hvd : ∀ x ∈ qw [a,b] v,qb x:=fun x hx =>
      hval x (p.mem_iff.mpr (List.mem_append_right _ hx))
    exact (q32 (ru d hvd) (rq d (hval a ha))
      (rq d (hval b hb))).trans (zj _ _)
lemma q19 : rj.Nodup:= by decide +kernel
lemma rh : ∀ a ∈ rj,qb a:= by
  have hle : rj.all (fun a=>decide (a.1 ≤ rx/\a.2 ≤ rx))=true:= by decide +kernel
  intro a ha
  have h:=of_decide_eq_true (List.all_eq_true.mp hle a ha)
  exact ⟨uj h.1,uj h.2⟩
lemma q0d : rj.all (fun a=>q9 true (rj.erase a)!=rx)=true:= by
  decide +kernel
lemma q1l {k t S} (l : qy k t S) (hs : ∀ a ∈ S,a ∈ rj) : rj.toFinset=S:= by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr=>?_,hs a⟩
  by_contra hn
  have fail:=List.all_eq_true.mp q0d a hr
  have cov : q9 true (rj.erase a)=rx:= by
    apply Nat.eq_of_testBit_eq; intro i; rw [qg]
    by_cases hi : i<252
    · obtain ⟨b,hb,h⟩:=zh l i hi
      have ba : b ≠ a:=fun he=>hn (he ▸ hb)
      have hm:=(List.mem_erase_of_ne ba).mpr (hs _ hb)
      simp only [hi,decide_true]
      exact (ss true _ _).mpr ⟨b,hm,yj _ _ _ hi h⟩
    · simp only [hi,decide_false]
      rw [Bool.eq_false_iff]; intro ht
      obtain ⟨b,hb,hbit⟩:=(ss true _ _).mp ht
      have hbv:=rh b (List.mem_of_mem_erase hb)
      have hf:=rq true hbv i (by omega)
      rw [hf] at hbit; contradiction
  simp [cov] at fail
def q0w : Nat:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cb70ca41b4174c6b5c8dc87531b7a7a7a5074cd8a3e7ab966b5620c41cd99c659b5a7f5391beb8f399eb78a62dc8d4ea48db9593e7aec79a7c8b9b766e71b7a74f5ecdcc88f3e1b4141418a74b9505341cd0cec62667ab940f59beca7c6921beb87925db75062c89689e796cd9b5341b579a7dccdb7cddca741e29253e7a49bb5a77a7a7a50e20c8aec7a66b953f0cd410ccc928f531b39f5a7e359f5f4b78af0a49fdbdc9f668fec7a3ee41be766b7b9c8a77ae2393ea4e759eca74141418ae26650b5410ccd3ef0b97a66fa39873e1b92c6a7e39bc6f9b750f0e760f2c8600c87b54153e41ba40c
def q1k : Nat:=0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a51d000e00000eafaf3ca338a54e90779706a54e970505a39003060202a3970b06071d90030e0b653805a53c054e074e0b03af363c38e807a5a5a51d000e00000eafaf51e84ea538361a0306a538030505e83697066c6ce8030b06071d36970e0b654e05a551053807380b97af90514ea307a5a5a51d00af0000af0e0e774ee8a5a3363c0307a5a3030b0b4e36970744444e030507061d3697af0558e80ba5770ba306a305970e9077e83806a5a5a51d00af0000af0e0e1a38a3a5e890519707a5e8970b0b389003072c2c38970507061d9003af0558a30ba51a0be806e805030e361aa34e06a5a5a5
def v9 : Nat:=0x9a999e949592935d4f4e626355565354e3dedfdcdd5c5b79eb747877e9eae7e88972736a696f676e6b6d71706c68664029a6a5a43a39181110150e14121317160f0d0cb8b73e3f2728201f241c23212226251e1d1bcac9c83837989796f991908ffbfaa1a09ff7f8f5f69d9c9b6160525150db5a594d46454a494744484c4b434241e4e1e05f5ee2d9dad1d0d6d4d2cfd3d8d7ced5cd5857f0f18e8d7675f4e6e588876564eeefeced8c8b8af3f2867e7d83827f818584807c7b7accb5b63d1a19c7c6a3a2360504090806070b0a03020100cbb3b4abaab0aeacadb2b1a9a8afa73c3bc5bdbcc2c0bebfc4c3bbc1bab92f2e3332303135342d2c2b2a
def v8 : Nat:=0xa18c3d5f5e3c3bcce4cb8d8e9fa08a8b4063623f3e6061f3cac59d865c5b38373658572d302f2c323134332e2b352af4f2e3c8c9c6c7e2bbbebdbac0bfc3c2bcc4c1b99e8987889b9c7c7f7e7b828184837d85807a5d3a39595afbeeefb8e1b3b49a789875765655282752191af0f1faecedb7b5b6e0a9acabaeada8b1b0aab2afa779997796972954531e212023221d25241f261c1b5051eae9e5e6f8f7a6dfdea2a3dad9959473729164654f184d03060508070a0904010b0200ebe8e7f9f6f5a5a4dddcdbced2d1d4d3d7d6d0d8d5cfcd749392686b6a6e6d706f69716c67668f904e0f12111413161510170e0d0c43474649484b4a454c424441
def sw (key j : Nat) : Nat:=(key>>>(8*j))&&&255
def u7 (f : Nat->Nat) (x : Nat) : Nat->Nat->Nat
  | 0,acc=>acc
  | j+1,acc =>
    u7 f x j ((acc<<<1)|||(if x.testBit (f j) then 1 else 0))
def qu (f : Nat->Nat) (x : Nat) : Nat :=
  if x=0 then 0 else u7 f x 252 0
lemma u3 (f : Nat->Nat) (x : Nat) :
    ∀ (n acc k : Nat),(u7 f x n acc).testBit k =
      if k<n then x.testBit (f k) else acc.testBit (k - n)
  | 0,acc,k=>by simp [u7]
  | n+1,acc,k=>by
    rw [u7,u3]
    by_cases hk : k<n
    · simp [hk,show k<n+1 by omega]
    · by_cases heq : k=n
      · subst heq
        simp only [Nat.lt_irrefl,ite_false,Nat.lt_succ_self,ite_true,Nat.sub_self,
          Nat.testBit_or,Nat.testBit_shiftLeft,not_le.mpr Nat.zero_lt_one,
          decide_false,Bool.false_and,Bool.false_or]
        cases x.testBit (f k) <;> rfl
      · have h1 : ¬ k<n+1:= by omega
        have hsub : k - n=(k - (n+1))+1:= by omega
        simp only [hk,h1,ite_false,hsub,Nat.testBit_or,Nat.testBit_shiftLeft]
        have hbit : (if x.testBit (f n)=true then (1 : Nat) else 0).testBit (k - (n+1)+1)=false:= by
          cases x.testBit (f n) <;> simp [Nat.testBit_succ]
        rw [hbit,Bool.or_false]
        simp [show 1 ≤ k - (n+1)+1 by omega]
lemma ql (f : Nat->Nat) (x k : Nat) :
    (qu f x).testBit k=if k<252 then x.testBit (f k) else false:= by
  by_cases hx : x=0
  · subst hx; simp [qu]
  · rw [qu,ite_eq_right hx,u3]; simp
lemma r7 (f : Nat->Nat) (x : Nat) : qr (qu f x):=fun j hj=>by
  rw [ql]; simp [show ¬ j<252 by omega]
lemma sd (f : Nat->Nat) (a b : Nat) :
    qu f (a&&&b)=qu f a&&&qu f b:= by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and,ql]; split_ifs <;> simp
lemma sm (f : Nat->Nat) (a b : Nat) :
    qu f (a|||b)=qu f a|||qu f b:= by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_or,ql]; split_ifs <;> simp
lemma ry (f : Nat->Nat) (hf : ∀ j<252,f j<252) (a : Nat) :
    qu f (rm a)=rm (qu f a):= by
  apply Nat.eq_of_testBit_eq; intro j
  rw [ql,uw (r7 f a),ql]
  by_cases hj : j<252
  · simp [hj,q5 a (hf j hj)]
  · simp [hj]
lemma rr (f : Nat->Nat) : qu f 0=0:= by
  apply Nat.eq_of_testBit_eq; intro j; rw [ql]; split_ifs <;> simp
lemma sh (f : Nat->Nat) (hf : ∀ j<252,f j<252) : qu f rx=rx:= by
  apply Nat.eq_of_testBit_eq; intro j; rw [ql]
  by_cases hj : j<252
  · simp [hj,qg,hf j hj]
  · simp [hj,qg]
lemma ul (f : Nat->Nat) (hf : ∀ j<252,f j<252/\f (f j)=j)
    {a : Nat} (ha : qr a) : qu f (qu f a)=a:= by
  apply Nat.eq_of_testBit_eq; intro j
  rw [ql]
  by_cases hj : j<252
  · have hfj:=hf j hj
    rw [ite_eq_left hj,ql,ite_eq_left hfj.1,hfj.2]
  · rw [ite_eq_right hj]; exact (ha j (by omega)).symm
lemma vx : ∀ j : Fin 252,sw v9 j.val<252/\sw v9 (sw v9 j.val)=j.val:= by
  decide +kernel
lemma vw : ∀ j : Fin 252,sw v8 j.val<252/\sw v8 (sw v8 j.val)=j.val:= by
  decide +kernel
lemma q15 : ∀ j : Fin 252,sw q0w j.val<252:= by decide +kernel
lemma q31 : ∀ j : Fin 252,sw q1k j.val<252:= by decide +kernel
def q3g (a : q0) : q0:=(qu (sw v9) a.1,qu (sw v9) a.2)
def q3f (a : q0) : q0:=(qu (sw v8) a.1,qu (sw v8) a.2)
def qj (isB : Bool) (a : q0) : q0:=if isB then q3f a else q3g a
def q1 : List Bool->q0->q0
  | [],a=>a
  | b :: t,a=>q1 t (qj b a)
def uu : Fin 8->List Bool :=
  ![[],[false],[false,true,false,true],[true,false,true],
    [true],[true,false],[false,true,false],[false,true]]
def r1 (g : Fin 8) (a : q0) : q0:=q1 (uu g) a
def zk (g : Fin 8) (a : q0) : q0:=q1 (uu g).reverse a
lemma uy (b : Bool) (a : q0) : qb (qj b a):= by
  cases b
  · exact ⟨r7 (sw v9) a.1,r7 (sw v9) a.2⟩
  · exact ⟨r7 (sw v8) a.1,r7 (sw v8) a.2⟩
lemma q0o (b : Bool) (a : q0) : qj b (qx a)=qx (qj b a):= by
  cases b
  · exact Prod.ext (ry (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1) a.1)
      (ry (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1) a.2)
  · exact Prod.ext (ry (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1) a.1)
      (ry (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1) a.2)
lemma q0p (b d : Bool) (x y : q0) :
    qj b (qn d x y)=qn d (qj b x) (qj b y):= by
  cases b <;> cases d
  · exact Prod.ext (sd (sw v9) x.1 y.1) (sd (sw v9) x.2 y.2)
  · exact Prod.ext (sm (sw v9) x.1 y.1) (sm (sw v9) x.2 y.2)
  · exact Prod.ext (sd (sw v8) x.1 y.1) (sd (sw v8) x.2 y.2)
  · exact Prod.ext (sm (sw v8) x.1 y.1) (sm (sw v8) x.2 y.2)
lemma zx (b : Bool) : qj b rv=rv:= by
  cases b
  · exact Prod.ext (rr (sw v9)) (rr (sw v9))
  · exact Prod.ext (rr (sw v8)) (rr (sw v8))
lemma q0n (b : Bool) : qj b v5=v5:= by
  cases b
  · have hA:=sh (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1)
    simp only [qj,q3g,v5,Bool.false_eq_true,ite_false,hA]
  · have hB:=sh (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1)
    simp only [qj,q3f,v5,ite_true,hB]
lemma z2 (b : Bool) : qj b qc=qc:= by
  cases b
  · have hA:=sh (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1)
    simp only [qj,q3g,qc,Bool.false_eq_true,ite_false,hA,rr]
  · have hB:=sh (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1)
    simp only [qj,q3f,qc,ite_true,hB,rr]
lemma vv (b : Bool) {a : q0} (ha : qb a) :
    qj b (qj b a)=a:= by
  cases b
  · exact Prod.ext (ul (sw v9) (fun j hj=>vx ⟨j,hj⟩) ha.1)
      (ul (sw v9) (fun j hj=>vx ⟨j,hj⟩) ha.2)
  · exact Prod.ext (ul (sw v8) (fun j hj=>vw ⟨j,hj⟩) ha.1)
      (ul (sw v8) (fun j hj=>vw ⟨j,hj⟩) ha.2)
lemma ze (w : List Bool) {a : q0} (ha : qb a) : qb (q1 w a):= by
  induction w generalizing a with
  | nil=>exact ha
  | cons b t ih=>exact ih (uy b a)
lemma us (w : List Bool) (a : q0) : q1 w (qx a)=qx (q1 w a):= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0o,ih,q1]
lemma su (w : List Bool) (d : Bool) (x y : q0) :
    q1 w (qn d x y)=qn d (q1 w x) (q1 w y):= by
  induction w generalizing x y with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0p,ih,q1,q1]
lemma xw (w : List Bool) : q1 w rv=rv:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,zx,ih]
lemma q0l (w : List Bool) : q1 w v5=v5:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0n,ih]
lemma vu (w : List Bool) : q1 w qc=qc:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,z2,ih]
lemma z1 (w1 w2 : List Bool) (a : q0) :
    q1 (w1++w2) a=q1 w2 (q1 w1 a):= by
  induction w1 generalizing a with
  | nil=>rfl
  | cons b t ih=>exact ih (qj b a)
lemma ut (w : List Bool) {a : q0} (ha : qb a) :
    q1 w.reverse (q1 w a)=a:= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih =>
    rw [List.reverse_cons,z1]
    simp only [q1]
    rw [ih (uy b a),vv b ha]
lemma sf (w : List Bool) {a b : q0} (ha : qb a) (hb : qb b)
    (he : q1 w a=q1 w b) : a=b:= by
  have h:=congrArg (q1 w.reverse) he
  rwa [ut w ha,ut w hb] at h
lemma ui (w : List Bool) {a : q0} (h : qd a) :
    qd (q1 w a):= by
  refine ⟨ze w h.1,?_,?_⟩
  · intro h0; exact h.2.1 (sf w h.1 vg (h0.trans (xw w).symm))
  · intro h1; exact h.2.2 (sf w h.1 q0r (h1.trans (q0l w).symm))
def si : Nat->q0
  | 0=>x3 | 1=>q1d | 2=>q1c | 3=>yv
  | 4=>q1b | 5=>yu | 6=>yt | 7=>q1a | _=>rv
lemma y4 (j : Nat) : qb (si j):= by
  match j with
  | 0=>exact rh x3 (by simp [rj])
  | 1=>exact rh q1d (by simp [rj])
  | 2=>exact rh q1c (by simp [rj])
  | 3=>exact rh yv (by simp [rj])
  | 4=>exact rh q1b (by simp [rj])
  | 5=>exact rh yu (by simp [rj])
  | 6=>exact rh yt (by simp [rj])
  | 7=>exact rh q1a (by simp [rj])
  | _+8=>exact vg
def u8 (isB : Bool) (j : Nat) : Nat :=
  ((if isB then 0x43076215 else 0x25613740)>>>(4*j))&&&7
def vo : List Bool->Nat->Nat
  | [],j=>j
  | b :: t,j=>vo t (u8 b j)
set_option maxRecDepth 10000 in
lemma x8 : ∀ (b : Bool) (j : Fin 8),
    qj b (si j.val)=si (u8 b j.val):= by decide +kernel
lemma q06 (b : Bool) (j : Nat) : u8 b j<8:= by
  have h : u8 b j ≤ 7:=Nat.and_le_right
  omega
lemma s3 (w : List Bool) : ∀ (j : Nat),j<8 →
    q1 w (si j)=si (vo w j):= by
  induction w with
  | nil=>intro j _; rfl
  | cons b t ih =>
    intro j hj
    rw [q1,x8 b ⟨j,hj⟩,vo]
    exact ih (u8 b j) (q06 b j)
def qf : List q0:=[x3,yv,yu,yt]
def qa (a : q0) : Bool :=
  rg a x3||rg a yv||rg a yu||rg a yt
lemma ri (a : q0) : qa a=true ↔ a ∈ qf:= by
  simp only [qa,qf,Bool.or_eq_true,rf,List.mem_cons,List.not_mem_nil,or_false]
  tauto
def s5 : Fin 4->q0:=![x3,yv,yu,yt]
def sp : Fin 4->Fin 8:=![0,2,4,6]
lemma yr : ∀ a ∈ qf,qb a:=fun a ha =>
  rh a (by simp only [qf,rj,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢; tauto)
lemma sy (b : Bool) (l : List Nat) (hl : ∀ j ∈ l,j<8)
    (hp : (l.map (u8 b)).Perm l) :
    ((l.map si).map (qj b)).Perm (l.map si):= by
  have heq : (l.map si).map (qj b)=(l.map (u8 b)).map si:= by
    rw [List.map_map,List.map_map]
    exact List.map_congr_left fun j hj=>x8 b ⟨j,hl j hj⟩
  rw [heq]; exact hp.map si
lemma yb (b : Bool) : (qf.map (qj b)).Perm qf:= by
  change (([0,3,5,6].map si).map (qj b)).Perm ([0,3,5,6].map si)
  exact sy b [0,3,5,6] (by decide) (by cases b <;> decide)
lemma x0 (b : Bool) {a : q0} (ha : qb a) :
    qj b a ∈ qf ↔ a ∈ qf:= by
  have hp:=yb b
  rw [← hp.mem_iff]
  constructor
  · intro hm; obtain ⟨x,hx,he⟩:=List.mem_map.mp hm
    have hinv : x=a:= by
      have h:=congrArg (qj b) he
      rwa [vv b (yr x hx),vv b ha] at h
    exact hinv ▸ hx
  · exact List.mem_map_of_mem
lemma s1 (w : List Bool) {a : q0} (ha : qb a) :
    q1 w a ∈ qf ↔ a ∈ qf:= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih=>rw [q1,ih (uy b a),x0 b ha]
lemma q0m (b : Bool) : (rj.map (qj b)).Perm rj:= by
  change (([0,1,2,3,4,5,6,7].map si).map (qj b)).Perm ([0,1,2,3,4,5,6,7].map si)
  exact sy b [0,1,2,3,4,5,6,7] (by decide) (by cases b <;> decide)
lemma y2 (w : List Bool) : (rj.map (q1 w)).Perm rj:= by
  induction w with
  | nil=>simp [q1]
  | cons b t ih =>
    have hs:=q0m b
    have hm : rj.map (q1 (b :: t))=(rj.map (qj b)).map (q1 t):= by
      rw [List.map_map]; rfl
    rw [hm]; exact (hs.map (q1 t)).trans ih
def xt (a : q0) : q0:=(qu (sw q0w) a.1,qu (sw q1k) a.2)
def q3 (i : Fin 4) (a : q0) : q0:=xt (r1 (sp i) a)
lemma re (i : Fin 4) (a : q0) : qb (q3 i a) :=
  ⟨r7 (sw q0w) (r1 (sp i) a).1,
   r7 (sw q1k) (r1 (sp i) a).2⟩
lemma uo (i : Fin 4) (a : q0) : q3 i (qx a)=qx (q3 i a):= by
  rw [q3,q3,r1,r1,us]
  exact Prod.ext (ry (sw q0w) (fun j hj=>q15 ⟨j,hj⟩) _)
    (ry (sw q1k) (fun j hj=>q31 ⟨j,hj⟩) _)
lemma vn (i : Fin 4) (d : Bool) (a b : q0) :
    q3 i (qn d a b)=qn d (q3 i a) (q3 i b):= by
  rw [q3,q3,q3,r1,r1,r1,su]
  cases d
  · exact Prod.ext (sd (sw q0w) _ _) (sd (sw q1k) _ _)
  · exact Prod.ext (sm (sw q0w) _ _) (sm (sw q1k) _ _)
lemma zp : xt qc=qc:= by
  have hP:=sh (sw q0w) (fun j hj=>q15 ⟨j,hj⟩)
  simp only [xt,qc,hP,rr]
lemma vm (i : Fin 4) : q3 i qc=qc:= by
  rw [q3,r1,vu,zp]
set_option maxRecDepth 10000 in
lemma yo : xt x3=rv:= by decide +kernel
lemma zd (i : Fin 4) : r1 (sp i) (s5 i)=x3:= by
  fin_cases i
  · exact s3 _ 0 (by omega)
  · exact s3 _ 3 (by omega)
  · exact s3 _ 5 (by omega)
  · exact s3 _ 6 (by omega)
lemma r8 (i : Fin 4) : q3 i (s5 i)=rv:= by
  rw [q3,zd i,yo]
def r4 (a : q0) : Nat :=
  ((a.1&&&Theta.lo 232)<<<232)|||(a.2&&&Theta.lo 232)
lemma uv (a : q0) (j : Nat) :
    (r4 a).testBit j =
      if j<232 then a.2.testBit j else if j<464 then a.1.testBit (j - 232) else false:= by
  simp only [r4,Theta.lo,Nat.testBit_or,Nat.testBit_and,
    Nat.testBit_two_pow_sub_one,Nat.testBit_shiftLeft]
  by_cases hj : j<232
  · simp [hj,show ¬ 232 ≤ j by omega]
  · by_cases hk : j<464
    · simp [hj,hk,show 232 ≤ j by omega,show j - 232<232 by omega]
    · simp [hj,hk,show 232 ≤ j by omega,show ¬ j - 232<232 by omega]
lemma xy : r4 qc=Theta.goal 232:= by decide +kernel
lemma z4 (a : q0) :
    r4 (qx a)=r4 a^^^Theta.mask 232:= by
  have hmask (j : Nat) : (Theta.mask 232).testBit j=decide (j<464):= by
    simp only [Theta.mask,Theta.lo,Nat.testBit_two_pow_sub_one]
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor,hmask,uv,uv]
  by_cases hl : j<232
  · simp [hl,qx,q5 _ (show j<252 by omega),show j<464 by omega]
  · by_cases hh : j<464
    · simp [hl,hh,qx,q5 _ (show j - 232<252 by omega)]
    · simp [hl,hh]
lemma x2 (d : Bool) (a b : q0) :
    r4 (qn d a b)=if d then r4 a|||r4 b else r4 a&&&r4 b:= by
  apply Nat.eq_of_testBit_eq; intro j
  cases d <;> simp only [qn,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_or,
    Nat.testBit_and,uv] <;> split_ifs <;> rfl
lemma q1m {k t S} (h : qy k t S) (v : List q0) (hv : v.Nodup)
    (he : v.toFinset=S) :
    Theta.Run qx (qn false) (qn true) qc k v:= by
  induction h generalizing v with
  | stop =>
    have hp : ([qc] : List q0).Perm v :=
      List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])
    exact Theta.Run.perm hp Theta.Run.done
  | @unary k t U a _ hf _ ih =>
    let rest:=qw [a] v
    have ham : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn,eq⟩:=vz (del:=[a]) hv (by simp) (by simpa using he)
    let save:=decide (a ∈ U)
    have hkeep : Theta.kept save a rest=s8 U [a]++rest:= by
      by_cases hm : a ∈ U <;> simp [save,Theta.kept,s8,hm]
    rw [← hkeep] at hn eq
    have hs : (qx a :: Theta.kept save a rest).toFinset=insert (qx a) U:= by
      rw [List.toFinset_cons,eq]
    have hnd : (qx a :: Theta.kept save a rest).Nodup:= by
      refine List.nodup_cons.mpr ⟨fun hz=>hf (Finset.mem_insert_of_mem ?_),hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p:=u0 [a] v hv (by simp) (by simpa using ham)
    exact Theta.Run.perm p.symm (Theta.Run.one true save (ih _ hnd hs))
  | @binary k t U a b d _ _ hab hf _ ih =>
    let rest:=qw [a,b] v
    have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn,eq⟩:=vz (del:=[a,b]) hv (by simp [hab]) (by simpa using he)
    let sa:=decide (a ∈ U); let sb:=decide (b ∈ U)
    have hkeep : Theta.kept sa a (Theta.kept sb b rest)=s8 U [a,b]++rest:= by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;> simp [sa,sb,Theta.kept,s8,ham,hbm]
    rw [← hkeep] at hn eq
    have hs : (qn d a b :: Theta.kept sa a (Theta.kept sb b rest)).toFinset=insert (qn d a b) U:= by
      rw [List.toFinset_cons,eq]
    have hnd : (qn d a b :: Theta.kept sa a (Theta.kept sb b rest)).Nodup:= by
      refine List.nodup_cons.mpr ⟨fun hz=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)),hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p:=u0 [a,b] v hv (by simp [hab]) (by simpa using And.intro ah bh)
    have hdone:=ih _ hnd hs
    cases d
    · exact Theta.Run.perm p.symm (Theta.Run.two true sa sb hdone)
    · exact Theta.Run.perm p.symm (Theta.Run.two false sa sb hdone)
def vi : List q0:=[q1c,q1a,yv,q1d,yu,yt,q1b]
def rc : List q0:=vi.map xt
lemma yg : vi.toFinset=rj.toFinset.erase x3:= by decide +kernel
lemma x4 (i : Fin 4) : s5 i ∈ rj.toFinset:= by
  fin_cases i <;> decide +kernel
set_option maxRecDepth 10000 in
lemma uk : rc.map r4=Theta.xs517:= by decide +kernel
lemma xx : Theta.xs517.Nodup:= by decide +kernel
lemma y8 : rc.Nodup:= by
  have h:=xx; rw [← uk] at h; exact List.Nodup.of_map _ h
lemma q04 (i : Fin 4) :
    rj.toFinset.image (q3 i)=insert rv rc.toFinset:= by
  have hact : rj.toFinset.image (r1 (sp i))=rj.toFinset:= by
    ext x; simp only [Finset.mem_image,List.mem_toFinset]
    have hp:=y2 (uu (sp i))
    rw [← hp.mem_iff,List.mem_map]; rfl
  have hcomp : rj.toFinset.image (q3 i)=rj.toFinset.image xt:= by
    calc rj.toFinset.image (q3 i)
        = (rj.toFinset.image (r1 (sp i))).image xt:= by
          rw [Finset.image_image]; rfl
      _=rj.toFinset.image xt:= by rw [hact]
  have hm : rc.toFinset=vi.toFinset.image xt:= by
    ext a; simp [rc,Finset.mem_image,List.mem_map]
  have h0 : x3 ∈ rj.toFinset:=x4 0
  rw [hcomp,hm,yg,← yo,← Finset.image_insert,Finset.insert_erase h0]
def qm (w : List q0) (v : q0) : Prop:=v ∈ w\/¬ qd v
lemma s2 {w : List q0} {a : q0} (haV : qb a) (h : qm w a) :
    a=rv\/a=v5\/(a ∈ w/\qd a):= by
  by_cases hz : a=rv
  · exact Or.inl hz
  by_cases ho : a=v5
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x=>x ⟨haV,hz,ho⟩),haV,hz,ho⟩)
def yc (w : List q0) (z : q0) : Prop :=
  (∃ a ∈ w,qd a/\z=qx a) ∨
  (∃ d a b,a ∈ w/\b ∈ w/\qd a/\qd b/\a ≠ b/\z=qn d a b)
lemma q35 {w a b} (d : Bool) (haV : qb a) (hbV : qb b)
    (ha : qm w a) (hb : qm w b) :
    qm w (qn d a b)\/yc w (qn d a b):= by
  have rz : qm w rv:=Or.inr (fun h=>h.2.1 rfl)
  have ro : qm w v5:=Or.inr (fun h=>h.2.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=so haV
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=so hbV
  rcases s2 haV ha with rfl | rfl | ⟨ham,hap⟩
  · rw [s0]; cases d <;> simp_all
  · rw [s0]; cases d <;> simp_all
  rcases s2 hbV hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
lemma q30 (w : List q0) (a : q0) (haV : qb a) (ha : a ∈ w) :
    qm w (qx a)\/yc w (qx a):= by
  rcases s2 haV (Or.inl ha : qm w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh=>hh.2.2 v6.1))
  · exact Or.inl (Or.inr (fun hh=>hh.2.1 v6.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma q1j {w : List q0} {z : q0} {k t S} (h : qy k t S)
    (hz : qm w z\/yc w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1/\qy k' t' S'/\∀ a ∈ S',a ∈ w:= by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w\/a=z:= by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=qv h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (qx a)
        have ht : qy k t (insert (qx a) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:= by
          intro v hv; obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hmv
        have hf : qx a ∉ insert a U:= by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (qn d a b)
        have ht : qy k t (insert (qn d a b) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:= by
          intro v hv; obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv; simpa [hne] using sub v hmv
        have hf : qn d a b ∉ insert a (insert b U):= by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha; have hn : a ≠ z:=fun hh=>hm (hh ▸ ha); simpa [hn] using sub a ha
def qp (i : Fin 4) (k : Nat) (S : Finset q0) : Prop :=
  ∃ m ≤ k,∃ t T,qy m t T/\T ⊆ S.image (q3 i)
lemma v2 (i : Fin 4) : ¬ qp i 10 rj.toFinset:= by
  rintro ⟨m,hm,t,T,h,hs⟩
  rw [q04] at hs
  have ht : ∀ a ∈ T,a ∈ rc:= by
    intro a ha
    rcases Finset.mem_insert.mp (hs ha) with eq | hmem
    · exact False.elim ((qv h _ ha).2.1 eq)
    · exact List.mem_toFinset.mp hmem
  let v:=rc.filter (fun a=>decide (a ∈ T))
  have he : v.toFinset=T:= by
    ext a; simp only [v,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha=>⟨ht _ ha,ha⟩⟩
  have hh:=q1m h v (y8.filter _) he
  have hr:=Theta.Run.map (inv':=(·^^^Theta.mask 232))
    (meet':=(·&&&·)) (join':=(·|||·)) r4 z4
    (fun a b=>x2 false a b) (fun a b=>x2 true a b) hh
  rw [xy] at hr
  apply Theta.noSub hm _ hr
  have sub:=List.Sublist.map r4
    (List.filter_sublist (l:=rc) (p:=fun a=>decide (a ∈ T)))
  rwa [uk] at sub
lemma za {i : Fin 4} {k k' : Nat} {S : Finset q0}
    (h : qp i k S) (hk : k ≤ k') : qp i k' S:= by
  obtain ⟨m,hm,t,T,hl,hs⟩:=h; exact ⟨m,hm.trans hk,t,T,hl,hs⟩
lemma x5 {i : Fin 4} {q : Nat} {S S' : Finset q0} {g : q0}
    (hs : S' ⊆ insert g S)
    (hr : qm (S.image (q3 i)).toList (q3 i g) ∨
      yc (S.image (q3 i)).toList (q3 i g))
    (h : qp i q S') : qp i (q+1) S:= by
  obtain ⟨m,hm,t,T,hl,ht⟩:=h
  have sub : ∀ a ∈ T,a ∈ (S.image (q3 i)).toList++[q3 i g]:= by
    intro a ha; obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m',t',T',hm',h',hT'⟩:=q1j hl hr sub
  exact ⟨m',by omega,t',T',h',fun a ha=>Finset.mem_toList.mp (hT' _ ha)⟩
lemma x6 {i : Fin 4} {q : Nat} {S S' : Finset q0} {g : q0}
    (hs : S' ⊆ insert g S)
    (hr : qm (S.image (q3 i)).toList (q3 i g))
    (h : qp i q S') : qp i q S:= by
  obtain ⟨m,hm,t,T,hl,ht⟩:=h
  refine ⟨m,hm,t,T,hl,?_⟩
  intro a ha; obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp=>hp (qv hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma va {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (h : qp i q (insert (qx a) U)) : qp i (q+1) (insert a U):= by
  apply x5 (g:=qx a) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rw [uo]
  exact q30 _ _ (re i a) (by simp)
lemma un {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : qp i q (insert (qn d a b) U)) : qp i (q+1) (insert a (insert b U)):= by
  apply x5 (g:=qn d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rw [vn]
  exact q35 _ (re i a) (re i b) (Or.inl (by simp)) (Or.inl (by simp))
lemma xj {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qx a) U)) :
    qp i q (insert a U):= by
  apply x6 (g:=qx a) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · exact Or.inr (fun hp=>hp.2.2 (by rw [uo,hz,v6.1]))
  · exact Or.inr (fun hp=>hp.2.1 (by rw [uo,ho,v6.2]))
  · simp at hm
lemma rn {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  apply x6 (g:=qn d a b) (by simp [Finset.insert_subset_iff]; exact fun _ h=>by simp [h]) _ h
  rw [vn,s0]
  have hbv:=re i b
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp=>hp.2.1 (so hbv).2.2.1)
    · rw [(so hbv).2.1]; exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(so hbv).1]; exact Or.inl (by simp)
    · exact Or.inr (fun hp=>hp.2.2 (so hbv).2.2.2.1)
  · simp at hm
lemma uq {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (hb : ¬ qd (q3 i b)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  rw [s0] at h; rw [Finset.insert_comm]; exact rn hb h
lemma ud {k t : Nat} {S : Finset q0} (h : qy k t S) (i : Fin 4) :
    qp i k S:= by
  induction h with
  | stop=>refine ⟨0,Nat.le_refl _,0,{qc},qy.stop,?_⟩; simp [vm]
  | unary _ _ _ ih=>exact va ih
  | binary _ _ _ _ _ ih=>exact un ih
lemma ue {k t : Nat} {S : Finset q0} (h : qy k t S)
    (i : Fin 4) (a : q0) (ha : a ∈ S) (hc : ¬ qd (q3 i a)) :
    ∃ q<k,qp i q S:= by
  induction h with
  | stop =>
    have ht : a=qc:=Finset.mem_singleton.mp ha
    exact (hc (by rw [ht,vm]; exact vq)).elim
  | @unary k t U b _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k,by omega,xj hc (ud tail i)⟩
    · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem ha); exact ⟨q+1,by omega,va h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k,by omega,rn hc (ud tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k,by omega,uq hc (ud tail i)⟩
      · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem hU); exact ⟨q+1,by omega,un h⟩
def r3 (k : Nat) (S : Finset q0) : Prop :=
  ∀ i q,q+(if s5 i ∈ S then 1 else 0)<k->¬ qp i q S
lemma xf {k : Nat} (hk : k ≤ 12) : r3 k rj.toFinset:= by
  intro i q hq h; rw [ite_eq_left (x4 i)] at hq
  exact v2 i (za h (by omega))
lemma xu (a : q0) : a ∈ qf ↔ ∃ i,s5 i=a:= by
  rw [← List.mem_ofFn]; rfl
lemma q0j {k : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) : r3 k (insert (qx a) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a U
  · by_cases ht : s5 i ∈ insert (qx a) U
    · rw [ite_eq_left ht] at hq; exact h i (q+1) (by simp [hp]; omega) (va hf)
    · rw [ite_eq_right ht] at hq
      have he : s5 i=a :=
        (Finset.mem_insert.mp hp).resolve_right (fun hm=>ht (Finset.mem_insert_of_mem hm))
      have hz : ¬ qd (q3 i a):= by rw [← he,r8]; exact fun hz=>hz.2.1 rfl
      exact h i q (by simp [hp]; omega) (xj hz hf)
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (va hf)
lemma zv {k : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) : r3 k (insert (qn d a b) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a (insert b U)
  · by_cases ht : s5 i ∈ insert (qn d a b) U
    · rw [ite_eq_left ht] at hq; exact h i (q+1) (by simp [hp]; omega) (un hf)
    · rw [ite_eq_right ht] at hq
      rcases Finset.mem_insert.mp hp with ha | hb
      · have hz : ¬ qd (q3 i a):= by rw [← ha,r8]; exact fun hz=>hz.2.1 rfl
        exact h i q (by simp [hp]; omega) (rn hz hf)
      · rcases Finset.mem_insert.mp hb with hb | hU
        · have hz : ¬ qd (q3 i b):= by rw [← hb,r8]; exact fun hz=>hz.2.1 rfl
          exact h i q (by simp [hp]; omega) (uq hz hf)
        · exact (ht (Finset.mem_insert_of_mem hU)).elim
  · exact h i (q+1) (by simp [hp]; split at hq <;> omega) (un hf)
lemma xz {k t : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) (tail : qy k t (insert (qx a) U)) :
    a ∉ qf:= by
  intro hm; obtain ⟨i,rfl⟩:=(xu _).mp hm
  have hz : ¬ qd (q3 i (s5 i)):= by rw [r8]; exact fun hz=>hz.2.1 rfl
  have ho : ¬ qd (q3 i (qx (s5 i))):= by
    rw [uo,r8,v6.1]; exact fun hp=>hp.2.2 rfl
  obtain ⟨q,hq,hf⟩:=ue tail i (qx (s5 i)) (Finset.mem_insert_self _ _) ho
  exact h i q (by simp; omega) (xj hz hf)
lemma xp {k t : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) (tail : qy k t (insert (qn d a b) U)) :
    (a ∈ qf->d=true/\a ∉ U)/\(b ∈ qf->d=true/\b ∉ U):= by
  have leftSide {a b : q0} (h : r3 (k+1) (insert a (insert b U)))
      (tail : qy k t (insert (qn d a b) U)) (hm : a ∈ qf) : d=true/\a ∉ U:= by
    obtain ⟨i,rfl⟩:=(xu _).mp hm
    have hz : ¬ qd (q3 i (s5 i)):= by rw [r8]; exact fun hz=>hz.2.1 rfl
    constructor
    · cases d
      · exfalso
        have ho : ¬ qd (q3 i (qn false (s5 i) b)):= by
          rw [vn,r8,s0,(so (re i b)).2.2.1]
          exact fun hp=>hp.2.1 rfl
        obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_self _ _) ho
        exact h i q (by simp; omega) (rn hz hf)
      · rfl
    · intro hU
      obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_of_mem hU) hz
      exact h i q (by simp; omega) (rn hz hf)
  refine ⟨leftSide h tail,?_⟩
  apply leftSide (a:=b) (b:=a)
  · rwa [Finset.insert_comm]
  · rwa [s0]
inductive q2 : Nat->Nat->Finset q0->Prop
  | stop : q2 0 0 {qc}
  | unary {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf)
      (tail : q2 k t (insert (qx a) U)) :
      q2 (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf->d=true/\a ∉ U)
      (hrb : b ∈ qf->d=true/\b ∉ U)
      (tail : q2 k t (insert (qn d a b) U)) :
      q2 (k+1) t (insert a (insert b U))
lemma q2.nlive {k t S} (h : q2 k t S) : qy k t S:= by
  induction h with
  | stop=>exact qy.stop
  | unary ha hf _ _ ih=>exact qy.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih=>exact qy.binary ha hb hab hf ih
lemma yl {k t S} (h : qy k t S) (hb : r3 k S) : q2 k t S:= by
  induction h with
  | stop=>exact q2.stop
  | unary ha hf tail ih =>
    exact q2.unary ha hf (xz hb tail) (ih (q0j hb))
  | binary ha hg hab hf tail ih =>
    obtain ⟨h1,h2⟩:=xp hb tail
    exact q2.binary ha hg hab hf h1 h2 (ih (zv hb))
lemma xe (w : List Bool) {k t : Nat} {S : Finset q0}
    (h : q2 k t S) : q2 k t (S.image (q1 w)):= by
  induction h with
  | stop=>simpa [vu] using q2.stop
  | @unary k t U a ha hf hr tail ih =>
    have hU : ∀ x ∈ U,qb x:=fun x hx =>
      (qv tail.nlive x (Finset.mem_insert_of_mem hx)).1
    simp only [Finset.image_insert,us] at ih ⊢
    have hne : qx (q1 w a) ∉ insert (q1 w a) (U.image (q1 w)):= by
      rw [← Finset.image_insert,← us]
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have hyV : qb y:= by
        rcases Finset.mem_insert.mp hy with rfl | hu
        · exact ha.1
        · exact hU y hu
      exact hf (sf w hyV (ye ha.1) he ▸ hy)
    exact q2.unary (ui w ha) hne
      (fun hm=>hr ((s1 w ha.1).mp hm)) ih
  | @binary k t U a b d ha hb hab hf hra hrb tail ih =>
    have hU : ∀ x ∈ U,qb x:=fun x hx =>
      (qv tail.nlive x (Finset.mem_insert_of_mem hx)).1
    simp only [Finset.image_insert,su] at ih ⊢
    have hne : qn d (q1 w a) (q1 w b) ∉
        insert (q1 w a) (insert (q1 w b) (U.image (q1 w))):= by
      rw [← Finset.image_insert,← Finset.image_insert,← su]
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have hyV : qb y:= by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ha.1
        rcases Finset.mem_insert.mp hy with rfl | hu
        · exact hb.1
        · exact hU y hu
      exact hf (sf w hyV (x9 d ha.1 hb.1) he ▸ hy)
    have hm (v : q0) (hvV : qb v) (hv : v ∉ U) : q1 w v ∉ U.image (q1 w):= by
      intro hx; obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hv (sf w (hU y hy) hvV he ▸ hy)
    refine q2.binary (ui w ha) (ui w hb)
      (fun e=>hab (sf w ha.1 hb.1 e)) hne ?_ ?_ ih
    · intro hx; obtain ⟨h1,h2⟩:=hra ((s1 w ha.1).mp hx)
      exact ⟨h1,hm _ ha.1 h2⟩
    · intro hx; obtain ⟨h1,h2⟩:=hrb ((s1 w hb.1).mp hx)
      exact ⟨h1,hm _ hb.1 h2⟩
lemma sj (t : Nat) : (!Nat.beq t 0)=decide (0<t):= by cases t <;> rfl
def rs (v : List q0) (g : q0) : Bool :=
  !(up g v)&&!(Nat.beq g.1 0&&Nat.beq g.2 0)&&!(Nat.beq g.1 rx&&Nat.beq g.2 rx)
lemma xi {v : List q0} {g : q0} (hg : g ∉ v) (hp : qd g) :
    rs v g=true:= by
  have hm : up g v=false:= by
    cases e : up g v; rfl; exact (hg ((y5 g v).mp e)).elim
  have h0 : (Nat.beq g.1 0&&Nat.beq g.2 0)=false:= by
    cases e : (Nat.beq g.1 0&&Nat.beq g.2 0); rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e; exact (hp.2.1 (Prod.ext e.1 e.2)).elim
  have h1 : (Nat.beq g.1 rx&&Nat.beq g.2 rx)=false:= by
    cases e : (Nat.beq g.1 rx&&Nat.beq g.2 rx); rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e; exact (hp.2.2 (Prod.ext e.1 e.2)).elim
  simp [rs,hm,h0,h1]
def v7 (k t : Nat) (r : List q0->Bool) (v rest : List q0) (n : Nat) (c : Nat)
    (g : q0) (keep : List (List q0)) : Bool :=
  let d:=!Nat.beq t 0
  let base:=r9 d g|||c
  if Nat.beq n (k - t) then
    Nat.beq base rx&&rs v g&&r (g :: rest)
  else keep.any (fun h=>Nat.ble (n+h.length) (k - t) &&
    Nat.beq (base|||q9 d h) rx&&rs v g&&r (g :: (h++rest)))
def q12 (k t len : Nat) (r : List q0->Bool) (v : List q0) (c : y3) (a : q0) : Bool :=
  !(qa a) &&
    v7 k t r v (vs a v) (len - 1) (vr c (r9 (!Nat.beq t 0) a))
      (qx a) [[],[a]]
def yf (k t len : Nat) (r : List q0->Bool) (v : List q0) : Bool :=
  let c:=qz (!Nat.beq t 0) v
  v.any (q12 k t len r v c)
def sr (a b : q0) (spa spb : Bool) : List (List q0) :=
  if spa then (if spb then [[]] else [[],[b]])
  else (if spb then [[],[a]] else [[],[a],[b],[a,b]])
def xk (r : List q0->Bool) (v : List q0)
    (a b : q0) (ua ub na1 nb1 : Nat) (spa spb : Bool) : Bool :=
  (Nat.beq (ua&&&nb1) 0&&Nat.beq (ub&&&na1) 0&&!spa&&!spb &&
    (let g:=(a.1&&&b.1,a.2&&&b.2); rs v g&&r (g :: ug a b v))) ||
  (Nat.beq (ua&&&b.2) 0&&Nat.beq (ub&&&a.2) 0 &&
    (let g:=(a.1|||b.1,a.2|||b.2); rs v g&&r (g :: ug a b v)))
def u5 (k t len : Nat) (r : List q0->Bool) (v : List q0) (c : y3)
    (a b : q0) (sa sb : Nat) (spa spb : Bool) : Bool :=
  let rest:=ug a b v
  let m:=uc c sa sb
  (!spa&&!spb &&
    v7 k t r v rest (len - 2) m (a.1&&&b.1,a.2&&&b.2) [[],[a],[b],[a,b]]) ||
    v7 k t r v rest (len - 2) m (a.1|||b.1,a.2|||b.2) (sr a b spa spb)
def v1 {α : Type} (p : α->α->Bool) : List α->Bool
  | []=>false
  | a :: t=>t.any (p a)||v1 p t
lemma u6 {α : Type} (p : α->α->Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b=true) (hba : p b a=true) : v1 p v=true:= by
  induction v with
  | nil=>simp at ha
  | cons h v ih =>
    simp only [v1,Bool.or_eq_true]
    by_cases eqA : a=h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b,(List.mem_cons.mp hb).resolve_left (Ne.symm hne),hab⟩)
    · have ha':=(List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b=h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a,ha',hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
def vt (k t len : Nat) (r : List q0->Bool) (v : List q0) : Bool :=
  if Nat.beq t 0&&Nat.beq len (k+2) then
    let u:=(zi v).2
    let acts:=v.map (fun a=>(a,u&&&r9 false a,rm a.1,qa a))
    v1 (fun x y=>xk r v x.1 y.1 x.2.1 y.2.1 x.2.2.1 y.2.2.1 x.2.2.2 y.2.2.2) acts
  else
    let d:=!Nat.beq t 0
    let c:=qz d v
    let items:=v.map (fun a=>(a,r9 d a,qa a))
    v1 (fun x y=>u5 k t len r v c x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2) items
def u1 : List q0->Bool
  | [a]=>rg a qc
  | _=>false
def v0 (k t : Nat) (v : List q0) (u b : List q0->Bool) : Bool :=
  let len:=v.length
  if Nat.blt (k+1) t||Nat.blt (k+2 - t) len then false else
    u1 v||(!Nat.beq t 0&&yf k (t - 1) len u v)||vt k t len b v
def xd : Nat->Nat->List q0->Bool
  | 0,_,v=>u1 v
  | k+1,t,v=>v0 k t v (xd k (t - 1)) (xd k t)
lemma xh {k t m : Nat} {v rest h : List q0} {g : q0} {opts : List (List q0)}
    {S : Finset q0} {r : List q0->Bool} (l : qy m t S)
    (hle : m ≤ k) (hp : qd g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g :: (h++rest)).Nodup) (he : (g :: (h++rest)).toFinset=S)
    (hr : r (g :: (h++rest))=true) :
    v7 k t r v rest rest.length (q9 (decide (0<t)) rest) g opts=true:= by
  obtain ⟨ht,hc⟩:=xg l
  rw [← he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length ≤ k - t:= by omega
  have cv:=q09 l he
  rw [q9,zm] at cv
  have cov : (r9 (decide (0<t)) g|||q9 (decide (0<t)) rest)|||q9 (decide (0<t)) h=rx:= by
    rw [← cv]; ac_rfl
  have hav:=xi ha hp
  by_cases tight : rest.length=k - t
  · have hz : h.length=0:= by omega
    have hem : h=[]:=List.length_eq_zero_iff.mp hz
    subst h
    have ok : r9 (decide (0<t)) g|||q9 (decide (0<t)) rest=rx:= by
      simpa [q9] using cov
    simp only [v7,sj,tight,Nat.beq_refl,ite_true,ok,hav,Bool.and_true,Bool.true_and]
    simpa using hr
  · have hnt : Nat.beq rest.length (k - t)=false:= by
      cases e : Nat.beq rest.length (k - t); rfl; exact (tight (Nat.beq_eq.mp e)).elim
    simp only [v7,sj,hnt,Bool.false_eq_true,ite_false,List.any_eq_true,
      Bool.and_eq_true,Nat.ble_eq,Nat.beq_eq,hav,and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩
lemma x1 {c : y3} {a b : q0} (hc : sv c)
    (op : Bool) (h : r9 false (qn op a b)|||uc c (r9 false a) (r9 false b)=rx) :
    ((c.2.1&&&r9 false a)&&&(if op then b.2 else rm b.1)) |||
    ((c.2.1&&&r9 false b)&&&(if op then a.2 else rm a.1))=0:= by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i<252
  · have hh:=congrArg (fun z : Nat=>z.testBit i) h
    clear h
    cases op <;> simp only [r9,qn,ite_false,ite_true,uc,qg,
      Nat.testBit_and,Nat.testBit_or,q5 _ hi,Nat.zero_testBit,
      Bool.false_eq_true,hi,decide_true] at hh ⊢ <;>
      cases ax : a.1.testBit i <;> cases ay : a.2.testBit i <;>
      cases bx : b.1.testBit i <;> cases byy : b.2.testBit i <;>
      cases um : c.2.1.testBit i <;> simp [ax,ay,bx,byy,um] at hh ⊢
  · have hge : 252 ≤ i:= by omega
    simp [Nat.testBit_or,Nat.testBit_and,hc.2.1 i hge]
lemma q1e {k r v c a b} (hc : sv c)
    (hlen : v.length - 2=k)
    (h : u5 k 0 v.length r v c a b (r9 false a) (r9 false b) (qa a) (qa b)=true) :
    xk r v a b (c.2.1&&&r9 false a) (c.2.1&&&r9 false b) (rm a.1) (rm b.1)
      (qa a) (qa b)=true:= by
  have heq : Nat.beq (v.length - 2) (k - 0)=true:=Nat.beq_eq.mpr (by omega)
  simp only [u5,v7,heq,ite_true,Bool.or_eq_true,Bool.and_eq_true,
    Nat.beq_eq] at h
  simp only [xk,Bool.or_eq_true,Bool.and_eq_true,Nat.beq_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hcov,hav⟩,hr⟩ | ⟨⟨hcov,hav⟩,hr⟩
  · have h0:=x1 hc false hcov
    have h1 : (c.2.1&&&r9 false a)&&&rm b.1=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&rm a.1=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.2
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · have h0:=x1 hc true hcov
    have h1 : (c.2.1&&&r9 false a)&&&b.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&a.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢; exact hi.2
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩
lemma zz {m t k : Nat} {U : Finset q0} {a : q0} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a U) (hle : m ≤ k)
    (fresh : qx a ∉ insert a U) (ha : a ∉ qf) (l : q2 m t (insert (qx a) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qx a) U->r v=true) :
    yf k t v.length r v=true:= by
  let h:=s8 U [a]; let rest:=qw [a] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩:=vz (del:=[a]) (U:=U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn; change (h++rest).toFinset=U at eq
  have nn : qx a ∉ v:=fun hm=>fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : qx a ∉ U:=fun hm=>fresh (Finset.mem_insert_of_mem hm)
  have hnd : (qx a :: (h++rest)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm=>nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (qx a :: (h++rest)).toFinset=insert (qx a) U:= by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]]:= by by_cases hm : a ∈ U <;> simp [h,s8,hm]
  apply List.any_eq_true.mpr; refine ⟨a,ah,?_⟩
  unfold q12; rw [sj,q0h]
  obtain ⟨hlen,hmask⟩:=q2b (decide (0<t)) hv hval ah
  rw [hlen,hmask]; apply Bool.and_eq_true_iff.mpr
  have hna : qa a=false:= by cases es : qa a; rfl; exact (ha ((ri a).mp es)).elim
  exact ⟨by simp [hna],
    xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
lemma yi {m t k : Nat} {U : Finset q0} {a b : q0} {d : Bool} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a (insert b U)) (hle : m ≤ k)
    (hab : a ≠ b) (fresh : qn d a b ∉ insert a (insert b U))
    (hra : a ∈ qf->d=true/\a ∉ U) (hrb : b ∈ qf->d=true/\b ∉ U)
    (l : q2 m t (insert (qn d a b) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qn d a b) U->r v=true) :
    u5 k t v.length r v (qz (decide (0<t)) v) a b
      (r9 (decide (0<t)) a) (r9 (decide (0<t)) b) (qa a) (qa b)=true:= by
  let g:=qn d a b; let h:=s8 U [a,b]; let rest:=qw [a,b] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩:=vz (del:=[a,b]) (U:=U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn; change (h++rest).toFinset=U at eq
  have nn : g ∉ v:=fun hm=>fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U:=fun hm=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g :: (h++rest)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm=>nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g :: (h++rest)).toFinset=insert g U:= by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]]:= by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,s8,ha,hb]
  have allow : h ∈ sr a b (qa a) (qa b):= by
    cases esa : qa a <;> cases esb : qa b <;> simp only [sr,ite_true,ite_false,Bool.false_eq_true]
    · exact opts
    · have hnb : b ∉ U:=(hrb ((ri b).mp esb)).2
      by_cases ha : a ∈ U <;> simp [h,s8,ha,hnb]
    · have hna : a ∉ U:=(hra ((ri a).mp esa)).2
      by_cases hb : b ∈ U <;> simp [h,s8,hna,hb]
    · have hna : a ∉ U:=(hra ((ri a).mp esa)).2
      have hnb : b ∉ U:=(hrb ((ri b).mp esb)).2
      simp [h,s8,hna,hnb]
  obtain ⟨hlen,hmask⟩:=q27 (decide (0<t)) hv hval ah bh hab
  unfold u5; dsimp only; rw [q0g,hlen,hmask]
  cases d with
  | false =>
    have na : qa a=false:= by cases es : qa a; rfl; exact (Bool.false_ne_true (hra ((ri a).mp es)).1).elim
    have nb : qa b=false:= by cases es : qa b; rfl; exact (Bool.false_ne_true (hrb ((ri b).mp es)).1).elim
    apply Bool.or_eq_true_iff.mpr; left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr; right
    exact xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)
lemma zw {m t k : Nat} {U : Finset q0} {a b : q0} {d : Bool} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a (insert b U)) (hle : m ≤ k)
    (hab : a ≠ b) (fresh : qn d a b ∉ insert a (insert b U))
    (hra : a ∈ qf->d=true/\a ∉ U) (hrb : b ∈ qf->d=true/\b ∉ U)
    (l : q2 m t (insert (qn d a b) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qn d a b) U->r v=true) :
    vt k t v.length r v=true:= by
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1:=yi hv hval he hle hab fresh hra hrb l ih
  have e' : v.toFinset=insert b (insert a U):= by rwa [Finset.insert_comm b a]
  have hf : qn d b a ∉ insert b (insert a U):= by rwa [s0 d b a,Finset.insert_comm b a]
  have ht : q2 m t (insert (qn d b a) U):= by rwa [s0 d b a]
  have h2:=yi hv hval e' hle hab.symm hf hrb hra ht (by simpa only [s0 d b a] using ih)
  unfold vt; split
  · rename_i cut
    simp only [Bool.and_eq_true,Nat.beq_eq] at cut
    obtain ⟨rfl,hvlen⟩:=cut
    have hlen : v.length - 2=k:= by omega
    have hc:=ru false hval
    have hcov2:=(q2c v).2
    let f:=fun x=>(x,(zi v).2&&&r9 false x,rm x.1,qa x)
    have na : f a ∈ v.map f:=List.mem_map_of_mem ah
    have nb : f b ∈ v.map f:=List.mem_map_of_mem bh
    exact u6 _ na nb (fun e=>hab (congrArg Prod.fst e))
      (by simpa only [f,hcov2] using q1e hc hlen h1)
      (by simpa only [f,hcov2] using q1e hc hlen h2)
  · rw [sj]
    let f:=fun x=>(x,r9 (decide (0<t)) x,qa x)
    have na : f a ∈ v.map f:=List.mem_map_of_mem ah
    have nb : f b ∈ v.map f:=List.mem_map_of_mem bh
    exact u6 _ na nb (fun e=>hab (congrArg Prod.fst e)) h1 h2
lemma xq {m t S : Nat} {s : Finset q0} {v : List q0} {u b : List q0->Bool}
    (h : q2 m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset=s)
    (hu : ∀ w,w.Nodup->∀ l ≤ S,q2 l (t - 1) w.toFinset->u w=true)
    (hb' : ∀ w,w.Nodup->∀ l ≤ S,q2 l t w.toFinset->b w=true) :
    v0 S t v u b=true:= by
  have size:=xg h.nlive
  have hval : ∀ x ∈ v,qb x:=fun x hx =>
    (qv h.nlive x (he ▸ List.mem_toFinset.mpr hx)).1
  rw [← he,List.toFinset_card_of_nodup hv] at size
  have hcond : (Nat.blt (S+1) t||Nat.blt (S+2 - t) v.length)=false:= by
    have h1 : Nat.blt (S+1) t=false:= by cases e : Nat.blt (S+1) t; rfl; have:=Nat.blt_eq.mp e; omega
    have h2 : Nat.blt (S+2 - t) v.length=false:= by cases e : Nat.blt (S+2 - t) v.length; rfl; have:=Nat.blt_eq.mp e; omega
    simp [h1,h2]
  unfold v0; dsimp only; rw [hcond]; simp only [Bool.false_eq_true,ite_false,sj]
  cases h with
  | stop =>
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    rw [List.perm_singleton.mp p]; simp [u1,(rf qc qc).mpr rfl]
  | @unary m t U a _ hf hr tail =>
    apply Bool.or_eq_true_iff.mpr; left
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp,zz hv hval he (by omega) hf hr tail ?_⟩
    intro w hn hs; exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d _ _ hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    apply zw hv hval he (by omega) hab hf hra hrb tail
    intro w hn hs; exact hb' w hn m (by omega) (hs.symm ▸ tail)
lemma y9 {m t : Nat} {S : Finset q0} (h : q2 m t S) (k : Nat)
    (hk : m ≤ k) (v : List q0) (hv : v.Nodup) (hs : v.toFinset=S) : xd k t v=true:= by
  induction k generalizing m t S v with
  | zero =>
    have hm : m=0:= by omega
    subst m; cases h
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    rw [List.perm_singleton.mp p]; simp [xd,u1,(rf qc qc).mpr rfl]
  | succ k ih =>
    rw [xd]
    apply xq h hk hv hs <;> exact fun w hn l hl hh=>ih hh hl w hn rfl
def qs (k t : Nat) (v : List q0) : Prop :=
  ∀ m ≤ k,¬ q2 m t v.toFinset
lemma yy {k t : Nat} {v : List q0} (hv : v.Nodup) (hc : xd k t v=false) :
    qs k t v:= by
  intro m hm h; exact Bool.false_ne_true (hc.symm.trans (y9 h k hm v hv rfl))
lemma xv {k t : Nat} {v : List q0} {u b : List q0->Bool} (hv : v.Nodup)
    (hu : ∀ w,u w=false->qs k (t - 1) w)
    (hb : ∀ w,b w=false->qs k t w)
    (hc : v0 k t v u b=false) : qs (k+1) t v:= by
  intro m hm h
  have hu' : ∀ w,w.Nodup->∀ j ≤ k,q2 j (t - 1) w.toFinset->u w=true:= by
    intro w _ j hj r; cases e : u w; exact (hu _ e j hj r).elim; rfl
  have hb' : ∀ w,w.Nodup->∀ j ≤ k,q2 j t w.toFinset->b w=true:= by
    intro w _ j hj r; cases e : b w; exact (hb _ e j hj r).elim; rfl
  exact Bool.false_ne_true (hc.symm.trans (xq h hm hv rfl hu' hb'))
def q2z (mult : Nat) (a : q0) : Nat :=
  let x:=((a.1 % 1048573)*mult+a.2 % 1048573+317) % 1048573
  (x*x*x) % 1048573
def q0c (mult : Nat) : List q0->Nat
  | []=>0
  | a :: l=>q2z mult a+q0c mult l
def uf (mult : Nat) (v : List q0) : Nat :=
  q0c mult v % 1048573
def q6 : Nat->Nat
  | 0=>0x76543210 | 1=>0x25613740 | 2=>0x45670123 | 3=>0x16520473 | 4=>0x43076215 | 5=>0x13025746 | 6=>0x70345126 | _=>0x20316475
def q2w : Nat->Nat
  | 0=>0x4600408a1100140010c06007841005000400020aa0003e0070160003c0220160e804400054000380070660bc3640400a0bc044330110c8014000c40080782f0090b80140001c0b00242b0050002a0070120002800701a098044000940500680008c0182281001e0800140007c0780680101d0700440106d0400581006506005804009058024010550500580701103012410002040044010090300e40d002008074040050000a00901e0100880100a
  | 1=>0xbc0481821500407814009000820070950008007f01a17c074260090980147b011004564180490085a4021610087643200e040744110020b8094001c40440782e17d0b86e4610120b86c4100121a8044000880006806701e17c02400194190078040210b8624610060000203217d004048001741700780c00a0b85a42f00e0b85840c00e0b85641000e0b85441400e0b81242e0390b80842e0090b84e4180061300842e0110b84a4490060000402b021
  | 2=>0xc60010a9008c44001fc004744003042fc074002fc040068002f4274068002ec01c1f4002e42e0068000d80d8194b5011008038042cd210038002c4210068002bc2b80686101d080024022ad010058a90092a0058a701100001015009008a4450016008a248c016008a04110162780249d0160500140226d01003802265260038850110085442e062230188320622480442e00a0ac1880223d0b80488d009230048002140bc188890110bc02887009
  | 3=>0x418024010aa0082a40240d1240782f036214024023fd1b0068023f50101f8023ed010068f90ba124024363d9008f640005012802408049008f246c0023001083606d0d8564561b1008ec4051b23a8024db016008e8401016008e64031b2008e440336e0b86789217d380024df0120b8018dd0090780480236d050018023650040382e042130108320420ac108920053480142b00a3400144c00a0402a41001d3302e8a7009020c94023250001e00231d
  | 4=>0xd94654400e0206c436005021424140020b86488f0214f8028043252a00293b00a4e8044a701d2a0108363252a02e85f3254d0028040490d80e43604917c0e45f0490486c45f4b54b00080017c0e8028004a401c1547b00a498028010490200e523039034018c000a0800291f00a06c0451d00a1580442600a1c00291900a0011800c01e2300291500a230044920a90c80d82c00a0d40290f00a001060024350000c00242d428078a70124200240403a
  | 5=>0x17d0d58400a020f64013d91240157a00a0617d8002900017e007065000190005ec01c1b40006c2480488901245c0480d0122600281400a0d88543601d0d9704000605b8048020494980496b0120040e4e90123680481023e350048ce0122146c41005254c048970121440486a0120c8048300120115c4000400c40442b0520102255700a0045855500a1500155300a0054255100a0105840c24a538028df0115300280123d2740285c0a91708540d032
  | 6=>0x170039c500e0783649d00e01c585c100e0081f5b100e350038ce00e2180383300e1040383500e0c00381100e0c47645606d6d00085c01d274009b10020345f4da00225c008780020c00095c0496a80e4000343d94241206d04856579006664049230120057495b0060c45f59f006010bf4160124d001892006340018d2006078029050060202a4070213dc018970060601e8840063680188c07a130018320061400182b0060057043100510c01408571
  | 7=>0x7140580027400204014021001c50023da124028005640a8f64490421240740306e7e805807159001f80071b1001640b80620017217e00e00805867016378058dc0166c4058da0167b0058df00933c058ce01625c058900162180588401621419478016788058500110c005970065778038010650d8c98a7052008c980231e29c029d704200008000628214c940074c1380740064c0019600065c008c4800684001cc00901d5d00380726d72003861011
  | 8=>0x4040680d01a0601fa0401a25c0686701a370069b101a0600688601a8f00684907a7f80684901a004b9a3701a000090df01a004068c601a6280698901a8c00680140d8b806a0100560c06a2b01a60c0762901a2e00141c01a7780694401a890068015d17140680c01a8800680c0c53680687801a360068cf01a868069830093380683001a0440682c01a104068003380115c80757100067000414015749f801656c059590164a4048083da004f684e016
  | 9=>0x18468000440183180621685c07a2d01e01d5c8074369ec05a7b00a29c0799f01e9e0078040952a007a75006184079d701e00c228070229c0078022fd9b80780209510c0181040e3680787801e25c07a6701e1840158301e070078b801e7780781601e51007a1a01e014bf97b01a7640683607e0d80685f01a01233804866040259f801a564068002100057086201a940069d701d70c068032fe7e806a0101a0200680207e00a2d80201a
  | _=>0
def qk : Nat->Nat->Nat
  | 8,0=>1343
  | 8,1=>349
  | 8,2=>6
  | 9,0=>602
  | 9,1=>378
  | 9,2=>41
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3y : Nat->Nat->Nat
  | 8,0=>992
  | 8,1=>227
  | 8,2=>2
  | 9,0=>488
  | 9,1=>283
  | 9,2=>35
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3x : Nat->Nat->Nat
  | 8,0=>1335
  | 8,1=>333
  | 8,2=>6
  | 9,0=>602
  | 9,1=>378
  | 9,2=>41
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3w : Nat->Nat->Nat->Nat
  | 8,0,0=>0x132ff0002eff000fbff00029ff00030ff00084ff00081ff00089ff00225bf0010aff000cdff00171ff00083ff00214bf00211bf00135ff002597f0016cff00237bf0021cbf0021abf0012afe00141ff00142ff0022bbf00190ff00018bf00191ff00003ff0019dff000feff00143ff00215bf00212bf00210bf00250bf00129fe0000aff0015dff00100ff0023abf0021ebf0019cff00144ff0006a7f0015eff0013eff00002ff00060ff0016eff0007fff0022cbf00055ff00009ff00011ff00065ff000c8ff0001b7f000b8bf00001ff000d5ff0002fff000d7ff00000ff
  | 8,0,1=>0x1d6ff00131ff000cbff00024ff00153ff00041ff000ceff00025ff0008aff00193ff000ccff0020fbf0010bff00026ff000efff001a2fe00181ff000f0ff000f0fb0017fff00203ff0017eff000f1ff001fbff00226bf0013aff0015aff00066ff0006cff000dcff00114ff00048ff00139ff00161ff0022abf00146ff00136ff00046ff000d0ff00194ff000caff0008cff00045ff000d1ff0008fff0010dff000dbff00149ff00105ff00228bf00160ff0019fff000daff00148ff00195ff00082ff00172ff000c9ff00027ff00088ff00069ff0008bff0004aff00028ff
  | 8,0,2=>0x84009bf8402fbf84011bf001c7ff00062ff001fcff001cbff00057ff001cdff001c9ff00004ff001c6ff0005fff001feff001f0ff00040ff001f2ff0006bff001caff00063ff000bdff0003aff001ffff0003dff001c8ff000beff00113ff0003eff0020ebf00109ff0003bff001d3ff000c1ff00159ff00064ff00044ff000f3ff000b2bf0005cff000c6ff00068ff00130ff00110ff00127fe0002bff00059ff0008eff0010cff000cfff0002cff0008dff00170ff00087ff00223bf0010fff0002dff000c2ff001a4fe0016aff0012fff000c3ff00138ff000c4ff001d4ff
  | 8,0,3=>0x380adf0780abf3500afd0600abf06c0a7f0500adf2e00abf1940aef0480adf62c09fd57c11ef08c6a7f62cd5fd1f86a7f57cd7ef1a8017f1a8097f1a82f7f1a8117f2d944bf1a8995f265b1d708612bf77c9fdf2642fdf26411df8ba12bf2649adf2d801bf2d809bf94612bf6f470f76f42ff76f411f76c42ff76c411f790612bf6c471f784801bf84809bf8482fbf84811bf25d44df1aa103f840999f841b1b72a8acb79ea10bf25c98df78c2fdf78c11df8ba10bf2b0adf72a801bf2a809bf3d210bf2b090f72b02ff72b011f76dc2ff76dc11f790610bf1b4bcfe84001bf
  | 8,0,4=>0xfc1b7f06d5d7f06c2f7f06d007f06e4e3f06e055f35065fd06cd47d35060fd19460ef0a87e7f3516efd06e2c3f19455ef9ac1b7f1953eef350fefd06c145f06cb83f06c657f06c656f3fc1b7f3515efd06c027f06c607f9681b7f06c7f7f06c125f06c557f35144fd03944df07944bf57c0aef06c6a7f06c097f1a8c87f1a8145f1a8b83f1a8657f06d5f6f1a80a7f26465df06e123f2640adf2e212bf26413df2e0999f2e1b1b7051b1d784865bf06c995f8480abf78c65df06e103f78c0adf2e210bf2e009bf1b46efe2e1e39f038acd7078acb784065bf06de35f8400abf
  | 8,0,5=>0x5002df038fedf910b8bf02cedfe078febf2e0149f2e04fb70504fd707802bf4ec60fe950b8bf02d29fe16129fe2e002bf4ec55fe8ecb8bf02c0cfe2e0129f02c55fe93c09bf93809bf350d5fd06cc87f1f81b7f8b009bf5b4d5fb078d5bf070b8bf13ce7f713c2ff713c60f70502fdf05060df0799cbf038d5df3e0b8bf02d28fe1342ff702c60fe2e02fbf2e060bf81c65df93c65bf35009fd8e8d5bf7a4d5df06cd57f06cfe7f07865bf03865df06c1e3f06c0e5f5b460fb06065bf4441b7f5b4fefb05065df2e065bf7ac65df19411ef7ac60df04865df35055fd06c183f
  | 8,0,6=>0x9ecb8bf038a5df0722ebf13495f713cd3f702d68fe13d21f705163df13c75f7050fedf4ed3cfe2e0febf940b8bf94009bf078149f0784fb79f8b8bf038e4df070f8bf02cecfe2e0f9bf25090f74ed5cfe96c0e5f7d04fd79184fb795c149f4ed4dfe9ccb83f03810df02d2efe9a01e3f94cb8bf02d2bfe03802df03860df2e055bf0604fb787cb8bf02c73fe03855df07860bf13ce8f707855bf0484fd7900b8bf05055df9f0b8bf13caff7050e2df9062ebf078f5bf70c90f737cd3f702d66fe978145f8604fb779c4fd7884149f02d20fe9c81e3f13d62f79a8b83f05016df
  | 8,0,7=>0x1a8125f1a8557f6b055fe2a80abf8e210bf1b40cfe840129f1b455fe6f455f777c0adf06212bf6c475f76c455f72d855bf2d80abf049b1d78fe12bf26416df26455df84055bf048acd786e10bf1b473fe25c55df25c0adf06001bf854febf790fedf1a8fe7f04811df1e401bf8b001bf06c017f0a9117f08c1b7f04802df048fedf91018bf01d1efe06002bf060febf8f401bf85409bf854c8bf9415dbf1e409bf8b018bf04813df04860df2e0c8bf2e15dbf4a409fe050e6df134def713ce0f713d17f71354ff705119df13460f7050e9df13455f78b0b8bf7ac11df13c55f7
  | 8,0,8=>0x7807fdf6d87ff78b011bf06c117f4fc11f777811df0487fdf14541f7048b0df14460f79ec18bf048a5df0862ebf14495f7144d3f71454bf714551f704919df06060bf01d2cfe06051b78b418bf94c18bf01d02fe048e6df90e2ebf060f7bf6f071f725071f701d65fe970125f061bbb792051b7880129f01d20fe9c8183f01d2efe9a0183f04816df95418bf01d2afe1612afe01c60fe8f818bf01c08fe060129f8ac11bf01d9dfe060d7bf90c18bf01d1dfe1442ff706055bf0f1117f14455f76b855fe7a8d7df4fc55f701c55fe04855df06144bf62c0afd4446a7f1a87f7f
  | 8,0,9=>0x7082ff770811f714c2ff714c11f790a26bf14c72f789801bf89809bf8982fbf89811bf16028fd28936df0aa5f7f08e5f7f14c2ef76cc28f76cc2ef714c82f79c07e7f27429df06c287f84428bf76828df6c828f769828fe55c28ef06c297f76829df84429bf55c29ef1e402bf1e460bf9f22cbf4fd40f77ac02df57c60ef6e460f76ac60fe8e460bf7a060df62c60fd2496ef72487ff70722cbf818a5df8ba2cbf7ace6df94a2cbf24893f72482ff74fc2ff790e2cbf4fcd3f78b02fbf7ac2fdf0aa5a7f24811f78002fdf8702fbf6fc2ff78dc11bf78011df6d811f78dc7fbf
  | 8,0,10=>0x3b811fb160cdfd6e0cdf70348cef9d47e7f01c8bfe004cdfd06c8b7f2e08bbf0508bdf13c8bf702c8bfe1948bef0488bdf36028fd05c28fd36428fd62028fd9d07e7f8ce26bf14c54f714c8bf727428df27488df27445df2748bdf14c28f720045ef77027df61828fd06c277f76827df84427bf55c27ef06028bf35828fd2fc28fd07828bf03828df13428f74ec28fe35028fd5b428fb1e028fd14428f760c28fd01c28fe2e028bf05028df13c28f702c28fe19428ef04828df11c28fd9e626bf288a3df2742fdf27411df8ba26bf2749edf2a001bf2a009bf94e26bf70870f7
  | 8,0,11=>0x62c27fd2a827bf77c27df2d827bf25c27df8d818bf14452f71a8277f26427df84027bf0488fdf1442ef777011df03827df07827bf35027fd78427df07888bf03888df35088fd06088bf3f1117f06c887f05088df2e088bf3f01b7f5c889fb78488df3f411fb78489df0bc89fb04888df22045ef03445ef08cfc7f03845df07845bf35045fd03845cf24445ef06045bf06c457f05045df2e045bf19445ef04845df0aa617f77045df06027bf79827df360cdfd2208cef22c89fb0608bbf9d1117f3508bfd0788bbf0388bdf4ec8bfe1348bf79b81b7f1448bf7654cdfd6e08bf7
  | 8,0,12=>0x350f0fb9e01b7f5b4f0fb06e0c7f350f0fd350f0f982c0a7f5580aef1a9557f2d8efbf2a8efbf078efbf06d557f3bcf0fb7ecf0fb808f0fb5f4f0fd5f4f0f93c045fb08cf0fb55809ef638f0fb5f42efd004f0fb3c009fb2e0efbf06cef7f160f0fb0bcf0fb5f411fd3c011fb060efbf92cb8bf1344ef7958b8bf4ec4bfe9bc1b7f81827df8b027bf27427df8bc18bf01c4bfe57c27ef84827bf78c27df8d0b8bf13c50f7858b8bf02c4cfe9941b7f19466ef06cd17f050d1df2e0d1bf194d1ef05029df2e029bf19429ef85009bf84409bf964097f1e427bf7ac27df19427ef
  | 8,0,13=>0x26c9cdf1bc2ff71bc11f7914b2bf1bc70f72c801bf2c809bf2c82fbf2c811bf26d10df0aa5d7f08e5d7f1bc2cf761c2cfd6d42bf76d42cf71bc8bf776411df01da4fe68da4fe061d4bf060c3bf9dd117f41c0afb1a9067f84106bf2d906bf848c2bf78cc2df060c2bf89906bf06106bf750c3fb41c11fb024c3fb06cc27f2e0c2bf050c2df2e106bf07906bf06d067f0bcc3fb048c2df9b66b7f2fc25fd92801bf07824bf35024fd2e024bf06c247f06024bf9b47e7f61425fd83c24bf83c25bf69409fe4eda2fe3bda2fe07a02bf038f0df038f0db079fbbf078f0bf078f0bb
  | 8,0,14=>0x497bdf0601abf0611abf060a6bf0483ddf061ffbf8c401bf8c402bf8383abf2e0eabf0517bdf03834df03924df07876bf2e11bbf07820bf07915bf07877bf06c637f05063df2e063bf19463ef06d597f06c647f06c2c7f06e0d7f9f4b8bf079ffbf9f41b7f9f46a7f2d9ffbf9f610bf934f0fb3c027fb5f028fd89827bf26c27df1bc2bf72a027bf28827df05027df2e027bf04827df8b02bbf6c02bf749927fe16127fe2c802bf49860fe0e65d7f60c2cfd88c2fbf1442bf701c2bfe06c2b7f2e02bbf0782bbf13c2bf702c2bfe3502bfd0602bbf26c2fdf26c11df8c8b2bf
  | 8,0,15=>0x6019bf0781fbf2c8b3bf2a0a9bf82cd17f1e47abf06022bf060b5bf04832df04978df2e01dbf2e0bbbf07822bf0787cbf05036df05175df03838df03923df06c407f06df97f1a86b7f2d8b7bf2a8abbf82c277f55827ef2c827bf2a08bbf8382fbf6d02ff71e4bdbf06dcf7f0497adf
  | 8,1,0=>0x2e1b1b7051b1d706c995f06e103f2e1e39f038acd7078acb706de35f1a8995f265b1d71aa103f840999f841b1b72a8acb7000b3bf000a9bf0007abf0006b7f000b7bf000abbf000637f0017adf0020ebf000eabf000b2bf00127fe0010c7f001897d00223bf001a4fe00180fd001ce7d001537f0020fbf001a2fe00181fd000f0fb00226bf0022abf00228bf000277f00225bf00214bf00211bf002597f000d17f00237bf0021cbf0021abf0012afe0022bbf00018bf00215bf00212bf00210bf00250bf00129fe0023abf0021ebf0006a7f0022cbf0001b7f000b8bf00000ff
  | 8,1,1=>0x9a0183f060129f0bcd7eb444183f1a8125f0f18b7d840129f0f0aa3f049b1d7444b63f444975f048acd708c793f08d5d6f00409f98209fdb7b0e2db078149f0784fb771090f396c0e5f7d04fd79184fb795c149f9ccb83f9a01e3f4440e5f0604fb70484fd74441e3f2b8d3f3978145f8604fb779c4fd7884149f9c81e3f9a8b83f2e0149f2e04fb70504fd72e0129f0f01e3f004d5f967009f906c1e3f06c0e5f0bc11eb06c183f670d5f906e4e3f06e055f06cd47d0bc60eb06e2c3f06c145f06cb83f06c656f06c125f06c477d1a8145f1a8b83f06d5f6f06e123f2e0999f
  | 8,1,2=>0x3e82b7b0182b7b9d0d87d5a811eb1f9ce7d309ce7d4cc287d1f8c27d08d536f078243f74409f954c246f034246f60409f9038f0db078f0bb350f0f908df86f3bdf86f08cef6f5f4f0f9818275f8b0273f274275f57c276f848273f78c275f1e4273f62c277d2a8273f77c275f2d8273f25c275f038275f078273f350277d078883f03845cf060273f360287d050d15f2e0d13f194d16f7ac275f194276f264275f840273f784275f798275f360cd7d770275f768275f844273f55c276f1f99a7d16141ed7b0a5db06051b770071f3970125f061bbb792051b7880129f9c8183f
  | 8,1,3=>0x108276f280277d0cc275f07c273f280637d064273f5cc275f2e4273f108636f5d8275f5e4275f558276f2c8273f1f8bd7d0381f9f1341fb74ec1fbe3501fbd5b41fbb08c1f3f050635f2e0633f194636f2a0273f898273f3c0277b7dc276f3bc246f288275f754277d26c275f68c2b7b1f9897d7bc11eb4302b7b
  | 8,2,0=>0x1897d001ce7d
  | 9,0,0=>0x1ffff000efff00024ff000c2ff0002bff000b2bf00110ff0002cff001d4ff000c3ff000cbff00025ff001fbff000f0ff000f0fb00045ff00088ff00028ff0008bff0004aff000d1ff00069ff0008fff00089ff000c9ff00195ff000cdff00172ff0008cff00226bf00136ff0002eff00082ff00029ff0016cff0016eff0022cbf00009ff00065ff0001b7f0007fff00141ff0019dff000d7ff00001ff000feff00190ff00003ff00100ff00191ff00011ff00002ff00055ff000c8ff0015dff0000aff0019cff000d5ff0002fff00060ff00144ff0006a7f00212bf00210bf
  | 9,0,1=>0x2e02fbf2e011bf0fc09ff54809ff0bc09ff18009ff06c65ff05065df2e065bf0fc65ff350d5ff08c65ff08c1b7f5b409ff35009fd1f865ff35011ff00465ff19409ff19460ff0bc65ff19411ff19411ef06c145f06cb83f06c657f06c656f0fc1b7f350d5fd1f81b7f19460ef06c017f06c097f06c2f7f06c117f06c0aff06c0a7f31c0aff0500adf2e00abf1940aff1940aef57c09ff1a8097f84809bf84009bf08c0aff0340aff1f80aff0180aff0040aff0240aff0bc0aff0440aff1a80aff1a80a7f2640adf8400abf00027ff000bdff0003dff0003aff001caff00063ff
  | 9,0,2=>0x8d00ff9ac02ff00c02ff3fd00ff3fcfeff2fcfeff0e4feff08d91ff00411ff08cfeff004feff644feff3f8c8ff5bcfeff9ac2fff160feff3fc01ff08c60ff0bc55ff00801ff00460ff0082fff0bcfeff9ac11ff2fc11ff00811ff3f811ff08c55ff06001bf00455ff3f809ff67001ff08cc8ff024c8ff57409ff17409ff3fc09ff24409ff00809ff5bc09ff06009bf15409ff18011ff2e0149f2e04fb70504fd7070b8bf0389fdf0502fdf05011df8b8b8bf050e2df07801bf07809bf3e0b8bf13490f71342ff713411f713c2ff713c11f7904b8bf13cd3f72e001bf2e009bf
  | 9,0,3=>0xa02eff20828ff0a029ff0bd6cff00c2fff16100ff3fc02ff3fc60ff1e060ff00860ff1f96eff4fc2ff716060ff0a860ff18460ff3e87fff7ac60df1f860ff0bc60ff3e811ff6782fff1f87fff0447fff63011ff60c11ff4f411ff0482fdf04811df8b818bf048a5df1442ff714411f790c18bf14471f70602fbf06011bf99811ff60811ff16011ff44455ff14455f71f855ff47011ff16055ff11c11ff15855ff358d7ff11c60ff0a855ff0a9117f64811ff15411ff4440aff1f40aff0480adf1540aff62c11ff1a8117f84011bf26411df6c411f72b011f700590ff00c01ff
  | 9,0,4=>0x3445ff03445ef1f845ff01845ff00445ff02445ff0bc45ff04445ff08c45ff32445ff1142eff01827ff65427ff33427ff5c827ff23027ff3608bff2208bff22c45ff1f88bff10c11ff08c8bff40c09ff1608bff36011ff6548bff22ccdff5c88bff22c8cff0a88bff9d07e7f7e811ff0048bff22c09ff0bc8bff22c11ff36028ff36028fd22028ff11428ff22c28ff12428ff1f827ff27427df20027ff09c2eff20827ff09c29ff05c28ff05c28fd08c28ff03428ff16028ff16028fd01428ff0a828ff01828ff00428ff02428ff0bc28ff04428ff1f828ff14c28f720028ff
  | 9,0,5=>0x3bc2fff3bc11ff3f827ff09c45ff03827df07827bf5b427ff35027fd22027ff24427ff3e827ff09c28ff06027bf47027ff5bc27ff22c27ff9ac27ff63c27ff17427ff65401ff0044aff09c4aff06c27ff06c277f1080aff05027df2e027bf19427ff19427ef34409ff34427ff02429ff3fc27ff5ac27ff00827ff18027ff5c82fff16069ff09c69ff44427ff2800aff04827df15427ff09c0aff23c11ff23c27ff0142eff03427ff22427ff08c88ff08cfc7f74809ff1f888ff16c11ff00488ff22009ff5c888ff22089ff0bc88ff22011ff22045ff22045ef08c27ff32427ff
  | 9,0,6=>0x2427ff0bc27ff04427ff9ac2bff5502bff2c82fbf1f910ff0a82cff1602bff0142bff0a82bff0182bff0042bff0242bff0bc2bff0442bff1bc2bf75602bff0ac2cff22c2bff93011ff61011ff060c2bf41855ff4180aff5a42fff5a411ff30828ff4182fff41811ff750c2ff308c3ff30801ff30809ff3082fff30811ff3fc24ff3f824ff08ccbff08c25ff08c24ff03424ff00424ff02424ff0bc24ff04424ff22024ff32c24ff09025ff83009ff55809ff55809ef078efbf55465ff06d557f5540aff55401ff55409ff3bc45ff7ecefff3bcf0ff3bcf0fb3bc01ff3bc09ff
  | 9,0,7=>0x10827ff28027ff28024ff55427ff2802bff41827ff3f045ff9d028ff0bc3aff7b82fff82860ff06019bf0443dff0f03dff93411ff08c3aff0e43aff72801ff824feff0781fbf02463ff06c63ff06c637f83409ff9f40aff3bc27ff09c24ff3f027ff10845ff7e827ff10828ff30827ff09c2bff9b827ff28028ff74827ff28045ff40c27ff16828ff00427ff
  | 9,1,0=>0xefff00024ff000c2ff0002bff000b2bf00110ff0002cff001d4ff000c3ff000cbff00025ff001fbff000f0ff000f0fb00045ff00088ff00028ff0008bff0004aff000d1ff00069ff0008fff00089ff000c9ff00195ff000cdff00172ff0008cff00226bf00136ff0002eff00082ff00029ff000d17f0016cff0016eff0022cbf00009ff00065ff0001b7f0007fff00141ff0019dff000d7ff00001ff000feff00190ff00003ff00100ff00191ff00011ff00002ff00055ff000c8ff0015dff0000aff0019cff000d5ff0002fff00060ff00144ff0006a7f00212bf00210bf
  | 9,1,1=>0x6009bf11c09fd2e0149f2e04fb70504fd7070b8bf0389fdf0502fdf05011df8b8b8bf050e2df07801bf07809bf3e0b8bf13490f71342ff713411f713c2ff713c11f7904b8bf13cd3f72e001bf08c1e3f2e009bf2e02fbf2e011bf05065df2e065bf08c1b7f35009fd19411ef06c145f06cb83f06c657f06c656f0fc1b7f350d5fd1f81b7f19460ef06c017f06c097f06c2f7f06c117f06c0a7f0500adf2e00abf1940aef1a8097f84809bf84009bf1a80a7f2640adf8400abf00027ff000277f000bdff00019bf0003dff0003aff001caff0001fbf00063ff000637f001ffff
  | 9,1,2=>0x16028fd1f8287f14c28f7174277f09c4a7f050275f2e0273f194277f194276f344097f344277f008277f180277f09c697f048275f154277f09c0a7f23c277f224277f220457f324277f654277f334277f5c8277f230277f3608b7f360287f360287d274275f200277f09c2e7f208277f09c297f00860fb4fc2ff77ac60df0bc60fb0bc60ef0bc60eb0482fdf04811df8b818bf048a5df1442ff714411f790c18bf14471f70602fbf06011bf14455f716055ef0a9117f5bc11ef0480adf11c0afd1a8117f84011bf26411df6c411f72b011f70e4fefb00460fb0bcfefb06001bf
  | 9,1,3=>0x182b7f0182b7b1f82b7f1bc2bf79b82b7f060c2bf1f8c27f1f8c27d30828fd034247f034246f3f0247f55809ef078efbf06d557f08cef7f08cef6f3bc45ef3bcf0fb3f8277f09c457f03827df07827bf35027fd038275f078273f5b4277f350277d220277f244277f3e8277f09c287f06027bf060273f470277f5bc277f22c277f9ac277f63c277f06c277f1080aef05027df2e027bf19427ef3fc277f5ac277f444277f2800afd04827df034277f08cfc7f74809fd22045ef08c277f03445ef08c457f018277f1f88b7f9d07e7f7e811ef36028fd1f8277f27427df05c28fd
  | 9,1,4=>0x108277f280277f28024fd554277f2802bfd418277f5d811df06019bf0341fbf0781fbf024637f06c637f3f0277f10845ef9b8277f28028fd7e8277f10828ef3bc277f09c247f40c277f16828fb748277f28045fd308277f09c2b7f2c82fbf
  | 9,2,0=>0x182b7b1f8c27d034246f08cef6f038275f078273f350277d060273f050275f2e0273f194276f048275f360287d274275f0bc60eb2e0149f2e04fb70504fd708c1e3f06c145f06cb83f06c656f000277f00019bf0001fbf000637f000b2bf000f0fb00226bf000d17f0022cbf0001b7f0006a7f00212bf00210bf
  | 10,0,0=>0x10827ff28027ff0a82bff5a411ff08c24ff55409ff08c27ff03427ff1f827ff01827ff00427ff02427ff0bc27ff04427ff22027ff09c45ff22c27ff09c28ff1f82fff0082fff16060ff1602fff0a87e7f1f811ff05c11ff16011ff01811ff0bc11ff04811df11c11ff0440aff08c01ff00801ff08cfeff0042fff00411ff08c09ff03409ff00409ff0bc09ff02411ff2e009bf19409ff06c097f0240aff00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,1,0=>0xbc27ff04427ff22027ff09c45ff22c27ff09c28ff004277f024277f0bc277f044277f220277f09c457f22c277f09c287f1f82fff0082fff16060ff1602fff0a87e7f1f811ff05c11ff16011ff01811ff0bc11ff0bc11ef0bc11eb04811df11c11ff0440aff08c01ff00801ff08cfeff0042fff00411ff08c09ff03409ff00409ff00409fd00409f90bc09ff02411ff2e009bf19409ff06c097f0240aff00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,1,1=>0x10827ff28027ff108277f108276f280277f280277d0a82bff5a411ff08c24ff55409ff08c27ff08c277f03427ff034277f1f827ff1f8277f01827ff018277f00427ff02427ff
  | 10,2,0=>0x108277f108276f280277f280277d08c277f034277f1f8277f018277f004277f024277f0bc277f044277f220277f09c457f22c277f09c287f0a87e7f0bc11ef0bc11eb04811df00409fd00409f92e009bf06c097f00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,3,0=>0x108276f280277d0bc11eb00409f900018bf000b8bf0001b7f00000ff
  | 11,0,0=>0x27ff0002fff00011ff00001ff00009ff
  | 11,1,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,2,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,3,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,4,0=>0x277f
  | _,_,_=>0
def q3v : Nat->Nat->Nat->Nat
  | 8,0,0=>0x6c65045bc1b2e0652f0fc1b195bc1b1955d6f06c01195bc1b0bc656f06c65181be3a350d5bd7a4d4357741b350d57d7ac651833c1b050095f06cb8024fc1b194096f0a87e195bc2a1f8d47d06c120457c1b0500a5f0504f02b5c1b2e00a3f2e01402a7cb813c0ab72e00b02af81b1940a6f0506502b3cb81940aaf1a8140297c6a2e00a3f1a865029bc6a050095f1a8b8024fc1b57c096f06c990297cb82640a9f051b102b5cb86c40ab72646502b3c6a264095f265b10275c1b848093f2e0990267cb86c409b7051b10275c1b264095f06e10028fe100500a9f8404f02adcb81b40abe8406502abc6a840093f840990267e106c409b778db70275c1b840093f2e1e30267cb86dc09b7051b70275c1b78c095f1a8990297c996c40ad71aa10028fe102640a9f841b102ade101b40abe
  | 8,0,1=>0x396d27f6c4f19411e7050650473cb8050659f2e04f196dcb802c65be08c1b0517c0e35009dd1356d243cc0b19411ee2e065046bcb835009bd050d4027741219411cf06e050257c1b938093f06cd4025f41b8b0093f06c120257c1b0504f570d41b0517c0b19528ee1f81b0517cb819460af06ce10517c1b13cd3770fc1b0517c0e350d5dd06ce50517c0e3509fdd06c4f0bddc1b13c11770a81b0517c0b19460ee06dec0517c1b050e25f06c140057c1b0502f5f06c140457c1b2e0141f06cb813cdc1b2e00b3e0701b2e0fc4f194e7e71f81b2e0fc1419460cf06e2e2e0fc14194e2cf0fc1b2e0fc1e350d5bd06cf82e0fc4d35090f506c0b0bdf81b02c117e0a81b2e0fc4f19460e706e412e0fc4f194d3e706cb8004fc1b2e02f3f06cb8044fc1b050655f06cb8194fcd45b4d5f9
  | 8,0,2=>0x384d0475cb82b84fb72e04f34edcb813c01b72e04f0bedcb813c11b72e01413e5e6c0504fd70784d242ddf50504fd70504f6bf5c1e13401b70784d026dc1437c4fd70393b27f781e1342fb70784d046dc143484fd70504f38b5c142b84fd70504f34f5c1413c01d70504f0bf5c1413c11d7070232e0fc1e050099f0784f026dc0e13c09d79884d241de3c13490b77884d2435c4d6a090f61358d243d44d56c90e70842a078fc2a1f81e3f0484d0475c1c0a8b83f0a87e2e0fc1213c11d713c2f34fce6413cd3778604f34edde713cd3d713da934fd84f628d3f513d6234f9c2108c1e3f2e0140267cb813c09b70504f0275c351f8145f0a87e0517c2a1f80e5f0dc7e0397cb8048119f06c0e0257c1b078093f06c18024fc2306c656f3516d027e41413c65d708c1b2e0fc1e35009bd
  | 8,0,3=>0xf07e0497c2a1f8477d1a8120297c6a048115f8401202a7c6a840113f840120467c6a264115f840990467c126c40ad71a9b1045de106c411b7265b10475c126c411d78405102adc6a1b4117e2a8ac046dddf2b011d76c46d047d8122b011d708423060fc0b65809fc7d04f0275e4613c09b795c140267e732e0093f2e199026f41813c09b70484f0275e5e050095f8604f026dde713c09d7884140267c4f62809f59a8b8024fcb8048099f960b80527c4f02da0f60780e0067c1e038099f3e0b80527c4d4ec90f62e0e50527c1e0389f9f13c0b0bfd84f02c11f62e0e10527c4f02cd3f62e1ec0527cb8050e29f2e0140067cb80502f9f2e0140467e472e04fb70500b68778b83484fb70500b38b780e13401d70384d0275cf82e04fb70384d2435cb837c4fb70384d27f5c0e1342fd7
  | 8,0,4=>0x38ef1173c0e3bcf0db078ef3c2ec1b558096f06d550517c1b2e1553f06d55195bcef350f0f93bd7d3c3e40e13427d708c0e09f3c1e038279f0784d09edc1e4ec27be078d409ef40e35027dd134d409fd53b35027fc3516d09fe41b050275f0504f09f5c1b2e0273f2e01409e7cb813c27b72e00b09ef81b194276f0506509f3cb819427af038271173c0e03445cf0780d116bcd403445ed0a87e361f45336028f5060170a2f4580bc28ed14c170a3d4d214c28f514c580a3d41c0aa2c3f4fc2f34fcc2a06e2c3f0a87e66df42a1fa065f0a87e8b0fe5c048115f7b4120475c1276011d7880120467e0404811cf049970473c210a8183f0a87e060fc1214411d798c511c5de1714471b7774511c75c5169c71f61458a1c7d45156c71e70a87e0497c311f8125f060120467c3c1f8477d
  | 8,0,5=>0x1e0381f9f0784d07edc1e4ec1fbe078d407ef41e5b41fbb06c1418d7c1b2e0633f06c6518dbc2a1f89b5f9d87e26d7c2a1f9877d9d07e26d7e741f8d87d4cc170a1f4233f0886f82d56025bdf6034456f034f0117ac1455809cf2e156026bcb8554149f2e15513edd550504fd7
  | 8,1,0=>0x38d409d744d35027754ecd409df0d45b427791609109db40e09c454f0504f09d5c4f00427752e01409c7cb813c27372e00b09cf8b8004273d0506509d3cb8194272f004d1025e42f180276b14cd80a1d5eb0bc60cb0093d047a4120bc11cb1442f0478c180bc11ab1445815794581540ae91a82f045ae100bc11ab2642f0472db10bc11e32b02f0478c0217409e906001026e45815409e908c1e0387c230780e0f08c1e4ecf8b80504f9708c1e134dc230784d270502f0472c1e00409b91342f0478c4f004d3f12e001026e4230782f2f2e02f046ac230796d2f06c1413d5c1b13c017506c140057423038d44d06cb80507c1b2e04f3706cb802cf81b2e0013d08cd45b5b41b2e0652f06c01195b41b004656906c01025e41b0bc116b0046502ba46a004097984801026e61000409b9
  | 8,1,1=>0x2800d091b5550042779280060ade506160276d5d82f0472c230341f2f0040918de41e108272f108d409db418280273d0604209cbcb8108272f108f009dac42360286d8984209cbca014427752e0a009cf414280275d2804f09dd4a013427752806509db4a014c2775048a009d749b280275d168d80a1e49d280275d2c82f046ac070182b7a1bc060adcc7e060c23d0780d090bcd4034246d00556027a423078ef2f08cef351b4233bcf06b08c0e09d3c0e13427570780e09c7c1e13427370793b09cf81e350273d
  | 8,2,0=>0x8c1e0383c230784d2708c0e351341b0046569
  | 9,0,0=>0x48580477c1201811df7b0120477c1229411df0482f0477c3c1f8117f048470477c120440adf1a811029fe100440abf2641102b7db10440af71b41102bf82a1f8017f08c2a1f9fc1200411df0a87e025fc7e16009fd048090477c1c2e009bf0380d27f7c140bc09df050090477e2e2e009bf050e20277c232e009bf2e00d026fcf82e009bf1340d243dc0b0bc09fe02c09047f84f0bc09f713c09047de412e009bf13cd3027dcb800409bf2e02f026fcb802411bf2e0140267cb813c09b70504f0275c2306c097f06c0d025fc6502411ef050650277cb819409bf0fc1b025fc1b548097f1f81b025fc6518009ef06c01025fc1b0bc097f06c09045fc1b050095f06cb8024fc1b194097f06c65025bc1b0240a7f0500902b7cb80240abf1940902bbc6a0240a7f2640902b7e100240abf
  | 9,0,1=>0x49760477c1e0341fbf06c0918dfc2a1f82b7f0a86f0afde6e0a82b7f308170a3f56904811df08cfc091fd5555809ef3bc0d117bcb855409bf06d55025fc2303427ef0380d09f7c1e03427bf3500d09ff42a1f8277f0a80609fec0701827fe06c0909dfc1402427df2e00909efc6502427ef1602f09fbc7e16027fd0481109f7c2322027ef03427117bc8809c45ef1f8d809ff41709c28fd160270a3f4d809c28fd14c270a3ddeb16060df16065183bc2a1f81b7f3fc2a1f9fc7e16060fd9ac2a1f9fc580bc60ef0a87e0bdfc2a1f8587d0a87e045fc580bc11ef1f8120477c1805c11bf804120477c5101471f7
  | 9,1,0=>0xa8060aded690bc11eb08c0d091bd5500409f908c0d09dbc0e034275f0780d09cfcd4034277d0a80609dec07018277e0040909fe47e160277d0bc1109fac23220276f03427115bc7e360277d05c270a1f401024277d0040909de414024275f2e00909cfc65024276f1602f09dbc2f044277b0bc1109dbc2f044276b0481109d7c8809c456f160270a1f4d809c287d14c270a1dc580bc60eb0a87e161f4580bc11eb0a806045ec7e0bc11eb1f817045f4020bc11eb0bd3d047ac120bc11cf0482f0472c470bc11eb0bc1102bac010bc11eb08c01027e423034096f00801027e40117409f90042f027e40102411f90bc09047ac1400409dd2e001026f4b800409b92e0140267cb813c09b70504f0275c0119409f906c01025f41b004097906c140257c1b2e0093f06c65025bc010240af9
  | 9,1,1=>0x42280276f108a009df442280276d08c4209dbc42034276f1f8a009df45a018277b1082f09dbc42044276f1088809dbc4209c456f1080109dbc42024276f3bc4209dbc4209c246f1088b09dbc4209c286f2805809df45a044277b2800109df4a0024277d280d809df4a009c287d2802f09df4a0044277d308a009df45a09c2b7b2808809df4a009c457d2808b09df45a09c287b
  | 9,2,0=>0x108a009db40102427790bc1109dac120bc11cb2e001026e41b0040979
  | _,_,_=>0
def q3u : Nat->Nat->Nat
  | 8,0=>0xa87e1602f6d0a87e1602f692e01413c099706c1413c095706cb8050091f06cb813c093706cb802c093e06cb8194092f
  | 8,1=>0x1684228027691080102427692802f04427690500102427592e00102427390046502427690482f044274b0a87e1602f691f8170bc116908c0103409692e01400409992e04f00409b10504f00409d106c14004095906cb8004093906c011940969
  | _,_=>0
def s7 : Nat->Nat->Nat->Nat
  | 8,0,0=>0x37a08b15bc88e1a3ed3bd492da7c6f9001a026dd7196559271fd10eb27250275dc48d1a12d98965b4b2c3cb541e0d65b1ba3fdb2527b4e79589c4693a0c7817f5cf991ef17e422ddfff33fa27d4c2a21901d17115dd07cf82454a242269d193c4af670e820116700e859e5e4129b076924324c58b8dcc84900be7a2916d99fad2436d059697ee64a45da57de3be5dec3abde0b5dda3d977658cf672cf6169fd57f3ead3f84179f3b55e421766a1f2f1ecc714967509b6e264091f9d0dc2a461685b84ba9020dc417a7124979ea5e13214a5203ed2a143e8474586cb3b459129a
  | 8,0,1=>0x1ea6fc84bd41408fa5b10e2950972891c93a527fc2865781656d3955db19b024861db1f4d9a40dd1d1b854600f498520c49be4c745fd0b76b19c1d7f9c9ab0859bd4428692c2c8de349c49a6b279d8e7a2c877795840e1534618999d2708644635223264c958bcceb7bc4a4e8de564c8cdd33971fa585a1b26d93d666f77ec4a4ba3c023f8fc4e6f5be56e921247422ef0b97812636b9045d6387fcb0f19504de5604ee483a41245cfc1a1a09c9a69420ff93b9d4e9154d46f6b20d133ed182b1070c5971a47596f74d51630543b8b0950b5f984bf16249f288929a461a405a
  | 8,0,2=>0x644c000a26983f2831ed96c8c4b3345e3210dca4414ec1f456d29784575400008a4000843df5ba0457d3063e2f73cd515a203608b00aa33b5b9dd91815e8894010d3043541e93b45b390000fb15d1e9e502f40000da620f01298732dfcdf206c60512e3a79d2428eab000104e000244f3d08df9100901a0c45dbd77ee31109d4a216001601685282fa6d0aec51dcabea5054c99a64e3094856f120a03d96a64cec1412302144c955a79c291a2040013344a6966c938999a501b236417169e61b100008eb0ec5b1d443e9b14d4452100008631ff27098304b436d3a139744484f
  | 8,0,3=>0x864dbe18b21bb722b621138d16d423a61bf96e65ca29ce2d903089d60002079331464053058b952bc00000029399195113092856a005400022ac623967cb6301cc23915680007fc5c723c28ee00b260b19232287a0240008d7d2fd39a60f50000000039445c4715d51016c4fc6e05f8168a09b168fcb45a6f668f3b854ec2dbd3d9600dc59413ce772e4682190f01c4085220777329b2877c18400001199765ad91d240b3000055c54bdc1021adaa90224000a3e272087a4d9786050750002135000000061259a27a220846dc4f016b3891966d82117584851010d6af6d64937
  | 8,0,4=>0x1b0da3d1c716f569c1086698114bdd491aed5633ac8d91917dc0100015e003480006bc648936966611c4a05901344761be81c71845d2985354379b046500002497427e6b15d062c46b46909a0a4e3fa19e0557c3dcb778e52ae07645ba53e5a2496d95d9778253b3205929a1fe8b98d290ae07440e90ad5a0139363393faa98791d4061343078b9a04281a78422b5e2664226b21298e45ba623cd570738537960e58c925dc00000000a92b7e7ac715549184643a558e451d1cec0000925bfb6b6d0f70171b2e3d30eeb2f822f982180000001b9a5e1df6100000760fadaaa
  | 8,0,5=>0x4c1980b51e49dc04464840625f21505a2598d6c4014774d3214653e517480517f846aa2080d1e028536723e45e002098c36afc6257f0c00072fe439348c00044b0ea73eea6016544000a20250040e5f3551c55390b059371c5a6a98704e714b9654b6475af967f06615784b71876400064658143bc9fb527286cb090402d4ea50018cc58610001df1384dc0a7330000000126d57e624359bd9b962dc3f98bc4d7958c48fb29813703ccd0bf19ad2098fb53ed6725eb8a064287809d5c97748011945454c4ea210900b04071f040005b25a6ca1ddae92d95f8f857e87909a4000
  | 8,0,6=>0x975479813108377a8a0217de40006cd9aef5a297b985fc000911d9593bdc5f15edda84829c07906bc12100602892c784784c9e47c5ae4490a2a58414f361c920fe4c1866d4d9a4c510547d22a51e25cb100000008f7179f608476f5c852c52844b6915840002f7296a8e129f44af5df45e9c2daa14c0f3555e3636771753557c9f90a653c13b187ee8505c7c260c0000001bad48c96b196e0aa3828cd816d50a015d84ee99094ea558b19096cfc92d8444f21230c5540bc4f7704549aa2cd02a1a404dc18d580006fd4000812d5a99c8425f1069a497d456d17fa4b2a7069541
  | 8,0,7=>0x80fe4190aad3b979087ae17a53ae560c83da07c131048a57b038a8af1e51c45244a2cb2a058570f103290000b32713d90d0001ee9000154988bce7f271472978d8f1200000ef74b40490040000575caf89ebc00088528d76d440003e9cd95000258ba670ab800ac1ce6f04000098590325327312a34a9d1688b8c8024cd91e4662e67ce1b3696dde15b2daa42e056cf6ea902103d5cd52175db40e65b2a9928000a57d0370001f29308dcdf00014b1571e3a1648414501f867a22a63cb0000000216c080768d99b30786d99005a7333e655b095d2e92d64231311c000577da20
  | 8,0,8=>0x64cda10262d8ec07c66649440dbea344ef104a40343c307ac637949f8644f03170c6341b948395b5e7e7044e33f954614576309975070c4b53c634118e03417cf57bb88dc0006c0a7b9a6640008344ca92838d89a1e0b7b7884ba76e944e836fe1799268a131bd8b7c6605ab40cedf5762769722c464825efde4c2c7d0480cc593103453d5048e231932d16b6d1db0619b50cc946915624b846880a60f77f044557f152111cce174a02144278646996ee64b15946081631c212908e14f2705c3d0d0c8b39ba5cb916c63a993857ec2b3c17b21d4ebba21068c93f25790088a27
  | 8,0,9=>0x6784be9030549997c4199a70d2236d3c20886a53917f646c302108110070d590351bcd2c249d441ee92773686ed6d9db913a243c3a104ce873398a38ca4c89158d4a956c5331a004aaa28a61833df63e61ad5d672a89abd62961572214af401b62df026630801de36098846b96f81a717965a295bae4331b05a112ce62d173a450991464691fc60cb9bc45ff0f057da273a52a90a64a98d506911015f7f20ac7b47e9c87d54c68ab8b3e35846dc0090bac79201c47f9a735bf88c2e4ba32f0351127e7547e65d9b7739b996d70f69652d6a7326e00305a585f5b8da9638243b9
  | 8,0,10=>0x71fe86a00000009d760f3110400000005cd65c52cd946539a00014b91078e212d2dad32bc896f3415e92000197b3bda3f9a250344085545700028690001c76a4c030925cd451299a46733c03918a268d9280d7c20ac669196ec0698f45b129d0436b4bbe5693becea93560000691c09c91bc01971955c161443e1244000037540d336d60c934440a320057c160c60d700022c00001bb83a8164183e513ba6fc0425910d935de55118665469a58655920ec0319de249032d87d41a5d1f167049cd23c5c5d6d6dd3387d661780e4d7c77a67ea46346b17f7d0ad31ce0f1a5e46e9
  | 8,0,11=>0x27cd0cf6a2649547656179445f873ad271aa3b04aaa4860418dc5c289219e7800004d0645e9a19ae5c8431903495fa84371eb4a511c698ab222caa1686dd31333a92f67ea50aa644ea336701080000c2f48f1222042680710247fb5a38e99a40e249316a9f11ffd81b00c87089ce593430e44045ff285740346a1658a3b19fbc7091f5cff15384eda90c475127323045d5a80c000005e14e5c2219624b987f62e165e5a59774e23b6165f6977e9dc60a700a22d1c429a78dcf759a56a149089ba512658168327191e5c000553d691078a27931a697730c40001065a8b006d9d4
  | 8,0,12=>0x91253fa0149547228685964adca550a4fd75284aea54fe6e14304091623e8638f25149650c3f12645893040529110515a15afca6e00bd75a3e4886100001df52244db77927139a868122e5a7e16861ab155c55e9a6e40c91f38c550c843e98d656619ea047214c5c856a307f62dcc951368592591f8f5633d22290000af08f3c15f382cebca0edfad2fecbbe66b00440001459212e96738ba6f871adcfb58697390e842e08064000569e0cf2ed87711b14af9a288000201c000a03d1c77d2d70190b4a441c0005f8ee408150cd99399f1e018ac471ca27a7f107d800010e4000
  | 8,0,13=>0x9270fe46e4878d04a876c99500007b30000a2444615d9880b2ac84c036c40007a2c40627bc38769a071e97b68e127004d582d497c6d4ce1c6bd153757ee923003da2e120632b6fc289f58908e37d9e7494c7c7d109f083a6a349b3a14496115289b90825c4987ae8f38565af51a9def929da29d9d6c0003a7677f2d25131219e1e1229c7e194959a665715af75a44af89fc00069f4630000193b3b0cef33cf95e40784f298da4a9521a697b92464e912761f1215dc996955dc40de54979d91f892ee578f27a664082216d8986cf25841045048651f9635c8df25a52d536204e9
  | 8,0,14=>0x1deda62a231e2e139dc6a2ffc10c287e4be961e86107d1d5b56e421f21cd48f228d60972a49fb48a9eba46619b428edf11564620900011e17dc400001c84c20d8c0f90c640411e8603732984993e38ad40001b793a5475f7d0cec429f815e070657359de28f107514e4bc47e474a0426a6edfbb337902d8525788198010a519c9144d061bd72065ff266c9719f64fee9184dfb96a40398aa484d08dc59221bcc11650650242bc0ff529c000154a7d154a4ab09d4506119cc0007f250e68a467005484a646821f018334fc7448653200a54818a068c900025a2982483c827c1a9
  | 8,0,15=>0x8f69498c3d5773e3e25b10f659711e5acd0000fbe2f0e7908e64c517aa58470030ca45e465e34a2e1c3712860153fe26973c4d4741f930e2740000508c5e5574563ca4a5c1288e65a48ba596f653d06b6591687152093f21960d305d433d5964daf69ee24b1eec7798a840000291bc52a640005aa4000000282b4f2624100024a27e44e876f30bc096ac4a77c25a3774043c970119926e8528132fd25d8e247627ea40c436c81f77fbccef494e0171f651e959fe6d179a400046e51740800e4676aa4534ec57291ab8240323e0ff816e9aa12440001fa67c503f5e54416e911
  | 8,0,16=>0x8744f9f0000e5b9ca60673f24bc9000199178f28a11c8d9837491c359c04c9929d09398a65db901fc000541d73327ae1b980c52ac4fca0891524ac18c697097b080215d919042b25bbd68aa636a0e4ecf4d7d71d3c55d530faa14b968695887ee5206fc4da4958d280a5ce96b248c6f85a64f1967b022c301c6d52785a09255c90245b810b2d50a877f44a378314e1e40b938170a423c3e592781d9925194e464c0e248b96810f3f037dee44665f77537ce6d5000a7935a4e818f54dcf0164c95757d1a206542e7160a1217e85f3387e5ae30881009a5810548f90a7c8265319
  | 8,0,17=>0x89cce750a89827a05e2fc40505a9224d59f00010859d695513a68f5c78c5b6f12b8cb84ed48f4518616115c87ef18b03077c646071cc68e9301298f55a5ce5a08c06358d0d724e4a9a967c5c316a515f126d65995b05bd19e6c1411efdd0a6fe8a3f3b8ccd2916400000000b73c453028b7502f93d4d4b33a9ba224b20d99708e0748063e5a47c14979919992a248061e8cb5f4dc52dd94fce6b741ded40000000448056c5ec42246fa5cf55d641629e1c9083dbcbf96a6c8416a0626164b1349687079c74fd3018f340008284d3a1ce4ddd4045409088e54107e156f8806255
  | 8,0,18=>0x30357cf1b36765003a8db31f4b9f46da9925dba83161fd71c6b84ad8396262386ae509064d4b791e9517a725c973f846e19375797a73c799081cea14c44bba4744f1d2ae414d52fe7e91f9a6f971d69d315e9881000151fa3e4342205e011748a7c984c407d403e571419dd0e7e8e0690dc57a928c69895a242321fdc20a9fe49de00017f485e013b4f15c1876040aa4c85eda46a58094fa6471092d14c3f647a2756558f479dc8f0a8e4fa5b7c6c9420d7a17346169151e0b924a4adc359c47174e6077845c88970b4ec18c24b011fb60e12a141bd6cc424c11de29b6936847
  | 8,0,19=>0xa114bb83ae20d52624eb6a7642dc714514633129ae26a676f626e9a64ca59358fb02a90f45b7a63e83a993b6477a1240b92bfe899055c8ec941000d6284ae175e54c7a7a67a4091d81708128714e76619936558707182f92fe09f10da81a619060a96a8843a00cc95907ce70a7c7d5012fc9a23183cff722654e789add2b17e4e67736e2c9886c61d4ada2b92cc04f1461829a2090e739b2671b2205ff988a0f813ab42b93806797235d27660b5e12a2c58f72505cc293544b08184bd11a0558964e4b41539a7b34244de95d2556c133c871a4644b88b4d3e1247e804593a4cd
  | 8,0,20=>0x3b64a6357a2591a0ce7ff21e58d25665a5193468c440383e2594e54574663e267aa2b781c665c5609a8f6585d418f04f66a37d9942c5d5dc1ee42d17e7c012869602f3d1da8382f49f450fd4081f251aa0dcc2212fd0a396f265894d656f444658016fb524720713af339e4cf2410fc1
  | 8,1,0=>0x9546894dc681023ad972543900051c58b6b46a253307ea610cba030009528b992e2096a46d13e90b53928ef4679ef6419bf81f045721a4f2992b948fac10614e783934a85f1eb3a497a8f14cf3c99798c14890918c32934d72c905b6c19a75c954f0006699690d354900041d2474274e1804a410009890ab0923a1048a2f3910b952b5fd6b97fd1f50d928a5aa1108df7d00002dd7ec0124e99495b70003215f149b9998898ab9d00426237f29019399747c99590597f930d5594a92964a3779
  | 8,1,1=>0x9c1739a7700a36147fa8100096079000098d0003fd7038c902f52d2139b95b91289211b94495240009d84e8389819a58696129a799dc1ef20d3f1a7f6d96aa9f90009099f0829441acb4de3ae352a5c8d1445a996386301b194b73171136900caa9461663723a6345903f289a2b4128b38fc4f79914711cc4bf8516016e17299719149f532295e6e94438318412336f197727c50c20320b031ad1ab469929c4e4a5aa697d411d82c9436b61fd00060d4b79818d95712a2a50a0f371812253
  | 8,1,2=>0x39c33e8bc7e0a596a9a0999586196c0db8499d932e19991c27907fa237b99616ec9cc0f14fa3822bb9479a11a140608264943b3e36435318d39084934d18cd751a3100b3d476455791921fa217da2ef7739314c76186395d175f8794a12740552f164d0a76224fe9d100055261f0006cb65175d7b01f13eda520ef8813b60241d4871a0b5205c148151400095a22105d05375b6dc95c6f97419731bf0131644b154374944d3af0001377e18f90000a11842a139a0d528da0d4d94773488fa65e
  | 8,1,3=>0x1e1011581823a4977127658c5e924ba1179d9c7a4d19f22999f6e2a835f996b3d93793161c32619ff24f66f9340217018e92397102a97d157c9329cf16c0001898f62e692aa2d69186779f6d3a13561acf1d009b1e90000000000003b9ac986a92f9107ff3816714c16799639b07532ac7595d97835f07f625f7c17a142971f6f41af2596774d340f0ad33570989138a6c978c6a10f97b124936801b71935f70dab901906b13d14408988726e79190705f62c876a7b00f7bc3090931a983477f
  | 8,1,4=>0xa914975842317dc45f2c378a7810779e14510008cf7ea04f50a6ca69e25ba0114937b90f1d842d6bc8666f72b47f4000a3c77d00062768226c9d75357de694001000000632821a64a292d11514990141013c45e15b197521991128300054768c5a1227159ae16b1a3989f04131b8af7ac46f8b7814201a19655504450abb02b14d8993074f117c26500da897fb1f92411175995881db062ac78e029e2f94ef8a149179932f8b152765c0e464f9240351e73e6a512949b15900c58699f36611c5
  | 8,1,5=>0x941a201710001943703199c82814b90f54329e469a5060498e180a000aa1929000a715916195690da7d993a8a976900953bab1
  | 8,2,0=>0x247118a0000a81690
  | 9,0,0=>0x686077ce767d93cabf5d9c23f9714be5e1a6ad748b8e05fd4cd96193f7db4ae574b78f8c000e3a433c30427e0000000f0df329ef06880a5e6290c000351d6a285102fa8e617723f728903520a26b8bd2345ab27720488000b22ffb2a2afdca0459028b88a63f88315ce42461c304f738c645a43019712462d4d60e97f89dc544f02529fb4f93e44380c19dd816a95079cafb4cda2e1171c77cbd21fa5c980021a32211ccaea5bb2f798384a451f2eb202201c21f2c9514640c5b7e429598a0065926669040c0c96e0c30b49be4353198
  | 9,0,1=>0x46b8dc529895b2a1cac974e10164dc764512b4b7dac7a5102f8958da11dbef06a300c925fb2f01611a106372f91518800134e9b9540bf44c5275100013e6426f4789cb10cd026ab2413104df81c11b48d5ce6e110444931015a52d20c99ca4d6bf9234c549aa83bf1f4902648627f5290e859622491c90d1d4c87061e3800000109a2d500c8e4465f25e324ccfd1466b89ec64b4c8b78425dca1308128582663349215678001c289fc115866e2e2e30941b5c8d1cc2b6d0a73e544ae151b897ccc2afe23cc086301207200a624252493
  | 9,0,2=>0x811b609552bd4734a5c59026311b989e192ebc95178e6d38266c3639cd0d42de21420945ce65197f645b0dd485922c3178b183d15d6b0297325957072ee58f65144538b3c672fc15ed23de19529a2acb58a0deb4965525856d8e110a3b30cb171476bc95bd9128df2721664682f2260494eceb4af85ac80005168a914eae1dbb430d1dc9511fe69792be0ea8a691d764e058470622c205b8b04fce590abc60625814967d9ac462b0b34a08000aaf27544ba6c54fef6f1111da519ea79563b12e402ad992a3ef51b270406480e9b8519f
  | 9,0,3=>0x7f0b3895644b17b5c1cc8bc8197b89bd4da83916a317697fe8e189095a60e325f185c9851fec94005c185ba031c7f4b4a8ef205e514b18d7d2e5b1648644d22c5a5feaeda3e21411ef9499a3e3291e49ba5933045600b171822def07cc87c98a7a74f880c05562378be3ba44ea837710c5306c20f143dc988a8242d028b04d996669945adc55d2abf679a8840b8fb31c59a7c0d43930b7ae045d26e1668a17d9826a694d8000b58000580c624c928578fcb629ca6189730a7e9ed307530cc7864e23c143987c4b0abcc090b771a0910c
  | 9,0,4=>0x8a4801dc8217425dc3a6022000629abe8000f2438cb805b12f492df3ce06ceebc51fc82e3280000d8b2843432292b0a1ea2c246338982ae253131188a43c868d5195c9e440009578d8b34cb42bc171909c5e829310e130a50e27052a8a7d20a29193cc0ec5252edc5613e4ddb05113eb45a542273c3010b2df72b2f684ac24e2045371b23a41731192949d04b0c999927cadd3222d92289931d98d3269207a4fe238c434c1ed762db19398d7ddf12574f0b2a47ae9a117b80686f46bf7140951be30390dc809c2dcde12c0b9ac892107
  | 9,0,5=>0x11511686a2000674bbf00005e27949e159b62140004811e9e13167a2a44440d8c74dad85f1f2818c281c40000597d091c41125d1271c5d45364ea304b6640008c71c4b871b3ad841408000d5a58a928afd081e9f96b48001e132238a8ac45722a693b095c4db2b7275481e87e29e7120ae318d312421e09584726772de30e84eedd56012c852252596a51e5813419368c3c68f3206974499d817b1c72d4b64439e1397cfa0e604f0492dc8d25a021ab6ca97e8a924da5f7bc5ddc245c7a88f661124e1210a6049e223168a8a5e002457
  | 9,0,6=>0x71f25a4e38679335b45856303d4d480024720002c6af5d7129b78369ee50de127180c60d8368611c509da39e5162242f862b2bc85cf878501266a5e84664f8c00057892a55feaa10004590f2edb7918800000127c1ac9ca89425ab4881f3de2af190368001432000457c68553228300038dc3a02d10de0be620220391c3c61c7200083741b067e20a86cb6482320007d4a9585e313c8301dbd93e081010accc00051b7f5b5855f23096988e8d4be499804b27535e0006388d0cd5215900000013d270d11f836e19600067889e4d6c899
  | 9,0,7=>0x4e48755ec307733203482f71c9500b368e92a591908a857887f93b295ee2088c973c89857be9d1664c4d12a218b00034520ae00059dc1ad12200000015e98c0b415fe422d5ce37e34397c5b7282f384194400000035f1be0368dcf2bb42c8af2e44908976527284f7e4a82484a2917908000a42b79269bf6e4811c10bc49e814c27c26d9fa64980018169885b530ac22b391e26a7e2177c3106f9250725bb110f26e220aa04658870f2a6af1c1832777c0a2c54e2f67749ab0138e2578bfa305972bcf4889470e840e626c972531e755
  | 9,0,8=>0x47894b0572c5190cafc5892c796f4b0859644550bc957c00047b30a2085e5600d43914f0c8e7da6418e1e15253118b8d3da407b755981259f22c76fc800151e394000387dc7e7e159bc3c62de60a85080010ef24169f80aa512dc104a2574996d9a5209180b98ab1160ca85f4f26913db065f76d1d5f996259224b9630b6409d25c10bba81d5790935578604d92d5c5b4915050473122936f4a6efbf49fc5ed093109239c6a4b6267f61c9e24b28a730ccb93c346bd1913af6402202d59c8455fce3317524744000f0b58c98f02d5069
  | 9,0,9=>0x6b5383d6532b15fa81840000000b89c499f8b434a3b926222c6b0209a9d6f672922036049ace5570ccaa4a989d9796398e2f08b9726c2e646ae8355cb8258e6cea6f289a54931797acc59de40ba19048c4e22865e0001d910fe7c10003eac4b80003d741057f6259244932505322b
  | 9,1,0=>0x7048287384db307b4bbc35598493580f4d18698393c12d517249c1419a4403a193bb4c96995874629a739b617bc92cb021625539ba9a5769a7da79b831a049dd7fd5c92af4ef66b44902a6ca94990783406db3197268832f8ef32bb99a913578993417925a17a32e1b717ef761529bc87c19191795ff2b9ac181730385c81c314ad99f998131125493d63fb2768f6f16416b70e6619779749ab1721044771bc45d100045195c4b10008948795419cc96a86649d35d92d429ae4032784071000
  | 9,1,1=>0xac90001a11c96e4b2fa3905cb69aa90015978d174840d99139e1714a5b01041789b3fbbbb39b2c2897289c40003ca5273390006f785737c1830001d858a0002139a1b8f3f900014f39f83bab90692597bc3a60001910004597e13917394673887cb0b581953145d90ba9995b27bbc19dbba1b4b000000a5f73ab3727d8a19b95518c3a1c62ca416d125f2d36912e94df8f72dc4d566404934c55f03a0bd6d39133a058b07a959b8d0f1b51051a712a960fb552387d22398b87946eb409b610d2
  | 9,1,2=>0x2995f17b36879997d969f7410004f99ef8ada7f0e91805e49290009c54d94e16f47980006b900072fa8918b3134cb649ad50001b39d1000ae19051014a85095d30d18ba11d7094aa82e8af7a1b0973072439d5cf7527b136136910f301a43a74a313e95f97f18d05bb84b62f76748d2b17270118417371ab5c10f92c3b341a36113fb4b4249b578c4ad192b4ba0ab37549e4908b067a000979202466b19824177867811ade0941896a173f25395159f6514f760176912f2b78dbaef7ea6e95b1
  | 9,1,3=>0x1d7871b214a793902d3db4818d36718b1aa763940c24a7cca4d1517e9aaf8510ad1614018f9b4d56960769819b12166918130f55926947734e7817518b28cc1e7b9182965903031264a5992670c34ab47a3993a47c9af7a59061602aa02093c34243849699acb292c908905e7960009556f96b35898c1921000b4fb97b8124bb796c35e931b0007b9329aaa5d77316b18431189634945217349f71b9bcb3a2b472d74f1a618c969e9ba6849e902980a9d51a90db8fb000193000a49007a09579
  | 9,1,4=>0x9e15476e172c74c000aa499c5b9701a987aaa3f000a111298e924c9f139ab9f000261a800006a96c18140a68626ff40486b88c9719b22774310c1a971317164413e13d14c29890b9681a909096d906a511b5952f56f67b8e109121c47645c630199a819313192d1805a296fc74f9d92526c914741c70d00b1b12f978376517caf4631a9f76ba3ba3717f49186098c321a4fb3e3518f13094c18d97f9a2b809a2384900d4176bb8f3a79059439561bb91f19cf3f71c19d8a018553ab05f2919c1
  | 9,1,5=>0x45482133151f2cdab22420002a19b1a2177a2815a9af12ff099000a9caff0009a98287c21bc22c0c979968abb1a6993b5d9000390a83571719b933b950f4d3411307ae97474a071194d6af74401a1f9479b41a0c8b929b7fa50102738072954939caec4cd61f0007f5aa1b49b112511ca901000581139679a8d3a8b381c4000961b5364c0817732c109a81fac22979c9353371b891e941975727178b469adf92f8bc85946f22210988115f3fcb482f13f13b11765e136da517a97599416a3bc7
  | 9,1,6=>0x603169327a7c1dd14929f000
  | 9,2,0=>0x510c4b77d2e6531161a106ae19cb5c00c99a3a212d38cc6d0d027480576c11d9a5167b51a8436f192d0493310037d620b38a94f2296e484460757991df239391432f208b9276f73f8e5747780b9e2ad968802866330951f2ec4c96614cf068012200
  | 10,0,0=>0x185b51c9196e19726cc15500068d3157c00590423e4006240002c006fc8d39df9368093945f38c34730b515d21000000a9a9705b74b169094271e8f47e137315342e5815e40030ca12dc2c209b167c1b0f801405ca425e1670a33104f2fd71045775fd4a4d8e9509ab3c941724ef665b92ac3f584d11454b57911000003ed91264e400114711ed1a4006eca904d51064ed000b36e994745f12f53931da12f1c2
  | 10,0,1=>0xc93b0b13ac9108ce10cc003644e768210c50c4a4592ec0c
  | 10,1,0=>0x2e67f485a1a2691744917d189085f172cf4506196e4593f6718a8b59e23c8c6179e53c94632565628bcd91c96a82dd9861a9209e91864c1a4f30fd615592432584a65f73ed7f55d74096236453975ce9a0000928c134400a62219f0c3424f987e41144137847a000b70c400410bc8063a0a82c70e2215ca189d02545116d1b1605298a6817e43e9b41113e2b2a6490265a001bf5f954384005ae2028d3131e34
  | 10,1,1=>0x994645f0319f3a8009128b26cfc3fd0b6dc272c5c134dff8e5c965e09525fc0000002c33856113c4193d4b32ed995c41b0d0233148d108c480d4c6f0bf875df138f72f51c006422ae61
  | 10,2,0=>0x9b210fc4b07164c426590048d620c003e5a4012b802927a39084008d88bfc9f488ea44c2d359b9c4e8218c6664007e47e88a5a3d46133404845723e004a9b322270d05423903c552335097e08cc4c8024e006080192a789c06a60b001440139004b2430b34ca436e174d05be19a000000a3
  | 10,3,0=>0x44b89702ca80524cd3172000a1
  | 11,0,0=>0x74005949826181590a6828808d1
  | 11,1,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,2,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,3,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,4,0=>0x320410
  | _,_,_=>0
def s6 : Nat->Nat->Nat->Nat
  | 8,0,0=>0xb43f015e6064040144d0343a0201d0d8240200008800000a500805110010180c0642a080021bc020885a0141802c1200428028ad010191303804842020150000f024010082a064430dc17150220202a05c1c204000e80803000004030284a008031800400882194310180d0200000c34110093b0000ec000080800012074470100c004c1008930243c03002000000000d0000401c030442101c080001d00802
  | 8,0,1=>0x43b244030b42a0040101cbe0284500417000030705869880000001581a0082a08c00004236ac540dc2f034620581c0006515401000040444304c0400004018841b81e0443902412190070044e0580e000c7354150186b06806038a50000400c1d08c0f018010e8000040415800168050c801038000641500c0810006058451e00122801000000481500c000547000029000000000200c480001d1dc0008c04
  | 8,0,2=>0x4522ac05371610000b084162a8120443f000111292f2441a0c00307d280800605c00008b106c0c0140721615004010180a04c1c3840c278be358000300e02c012cc0817c010041a0f00911c4f0102205c4c014001500b0a0000fc06018cb0883e0087c1540500003044680b44800c3e06424058022fdb34711601cdc074210740e4dc130080f004010082a0d0061700604c2b0080105003000100200601002
  | 8,0,3=>0x3ad61084010d80b0103a030002d0063c00d00c0004402128031984d61114018090000607e250254b0981c1440004c0f004050586a014000301a34c1b0ec0a000a21581b02c01400698b0071f99406c030483136c1503493518020681017006000140480000001318010a88e7280a0341a1c90d010910d0bf124000e4020d8890d815008680841d0040201c5a5ac2d03424054aa29078134204540e0cc0005928
  | 8,0,4=>0xda094095502b0282a83088104010006836c0d1ee43390071f40b0e9760040803dfd05515010a96340c46414080bd088a50bc1d2a80401c25005f50049e1f0543e08a0440100002284610000c01c31030000047406816600021440102c77368000a0416702d06d0f0001609959010a3008a70005a31000278010599b064b626802208070000900044669b101401
  | 8,1,0=>0x1305a27c543001002c70455860585502c020380800084028001647200c0505c1211c0a038030ac060000a37c040042e4540200001001a209404000020540c04c1001c770547d0dca80cc14260020902f000020a8050741203410000000e8610001805802000180b000390000844d1800104c0934c091500003438018350002000000000000006b004020381c0201a01c0113c191480101c240440d008031d428
  | 8,1,1=>0x1d3440109c2a018060d4aa2188104425024080a81c01211568ea0700b01c231bc722e0b2030f105417
  | 8,2,0=>0x2a0
  | 9,0,0=>0x6000158ea0020004b8240080900006012e1b41382500a000898840400640082a04a0c81209e0000040a03f0083ec2d009012014000240ba1600183b0bc00402006030008020000900000001001a0300d014006000450040620480e8510000c80005600a0341d82400201c210511820681102c01a004000030060000400c0600e00080102e00c000000082400b0030080180102a0000000d021078010050160040f40300700a048060a201a0080281e
  | 9,0,1=>0x144bc1102e00006c7f0000b402c000040220000900c07000403801010080048110b40140303d0000a4e48000c605c4e8840020680900105e0e00089a0001981c00419e0080a80005e008010a501e0e8e58010d0014d00210000240000f2c82ac9005c002054000973cc21c018300182ac7c80400c0289f83703a0282a8290162681400601a1400280c03804c000640025f0078070260b00c049024004330000201040082d01247c1c00d01200005003
  | 9,0,2=>0xf8073290102681902f28a1f00c00a15e0100082f06014c0703b0020a4520102373005b8012e61dc498b40000a0cb825
  | 9,1,0=>0x28c0a27890020190940c03c0d0008501c362000f00928000ac27c581bc0102c110ac23008001145a000170440c018050040101410164a007c8203416224c81180d02483000000fc2800c050000000875020011bc2c01805000010780a0186e07c000c81e07001044000a44b02000038090cc1a1a8040788212c991a0170000034c0e02823004002100004004044030ec22004230e00001800000010ac0e03414
  | 9,1,1=>0xe2585a0d831208000347a060cb13c0067c052d4311d8210bc12084a0240000001c3596687c0005c340200d94c300080c0000a0344a10ca702402000041c4000200c09ddf05c0e
  | 9,2,0=>0x16502c19604827001e589800894c043a2df1f
  | 10,0,0=>0x58a70d85da24738464c249120001902387a04804d85063cc0a0034408
  | 10,1,0=>0x105ca970402a002eb869d13088088fa20529eb42041904181830ca11e70408007180c4810a31dd4
  | 10,2,0=>0xe410310a49814070431800340400101c6
  | 10,3,0=>0x1c1
  | 11,0,0=>0xf0cd
  | 11,1,0=>0xf4d220
  | 11,2,0=>0xf4d220
  | 11,3,0=>0xf4d220
  | _,_,_=>0
def zg (k t : Nat) (w : List q0) : Nat :=
  match k,t with
  | 8,0 =>
    let h:=uf 65565 w
    let bkt:=h % 625
    let d:=(s6 8 0 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*1) % 1048573+d) % 2624
    (s7 8 0 (slot>>>7)>>>(14*(slot&&&127)))&&&16383
  | 8,1 =>
    let h:=uf 65543 w
    let bkt:=h % 161
    let d:=(s6 8 1 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*17) % 1048573+d) % 674
    (s7 8 1 (slot>>>7)>>>(12*(slot&&&127)))&&&4095
  | 8,2 =>
    let h:=uf 65537 w
    let bkt:=h % 3
    let d:=(s6 8 2 0>>>(4*bkt))&&&15
    let slot:=((h*1) % 1048573+d) % 11
    (s7 8 2 0>>>(6*slot))&&&63
  | 9,0 =>
    let h:=uf 65540 w
    let bkt:=h % 291
    let d:=(s6 9 0 (bkt>>>7)>>>(11*(bkt&&&127)))&&&2047
    let slot:=((h*31) % 1048573+d) % 1220
    (s7 9 0 (slot>>>7)>>>(13*(slot&&&127)))&&&8191
  | 9,1 =>
    let h:=uf 65545 w
    let bkt:=h % 185
    let d:=(s6 9 1 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*17) % 1048573+d) % 776
    (s7 9 1 (slot>>>7)>>>(12*(slot&&&127)))&&&4095
  | 9,2 =>
    let h:=uf 65539 w
    let bkt:=h % 21
    let d:=(s6 9 2 0>>>(7*bkt))&&&127
    let slot:=((h*31) % 1048573+d) % 87
    (s7 9 2 0>>>(9*slot))&&&511
  | 10,0 =>
    let h:=uf 65537 w
    let bkt:=h % 34
    let d:=(s6 10 0 0>>>(7*bkt))&&&127
    let slot:=((h*31) % 1048573+d) % 147
    (s7 10 0 (slot>>>7)>>>(10*(slot&&&127)))&&&1023
  | 10,1 =>
    let h:=uf 65546 w
    let bkt:=h % 45
    let d:=(s6 10 1 0>>>(7*bkt))&&&127
    let slot:=((h*1000) % 1048573+d) % 187
    (s7 10 1 (slot>>>7)>>>(10*(slot&&&127)))&&&1023
  | 10,2 =>
    let h:=uf 65538 w
    let bkt:=h % 22
    let d:=(s6 10 2 0>>>(6*bkt))&&&63
    let slot:=((h*1001) % 1048573+d) % 101
    (s7 10 2 0>>>(9*slot))&&&511
  | 10,3 =>
    let h:=uf 65537 w
    let bkt:=h % 4
    let d:=(s6 10 3 0>>>(3*bkt))&&&7
    let slot:=((h*31) % 1048573+d) % 15
    (s7 10 3 0>>>(7*slot))&&&127
  | 11,0 =>
    let h:=uf 65540 w
    let bkt:=h % 4
    let d:=(s6 11 0 0>>>(4*bkt))&&&15
    let slot:=((h*17) % 1048573+d) % 18
    (s7 11 0 0>>>(6*slot))&&&63
  | 11,1 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 1 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 1 0>>>(6*slot))&&&63
  | 11,2 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 2 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 2 0>>>(6*slot))&&&63
  | 11,3 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 3 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 3 0>>>(6*slot))&&&63
  | 11,4 =>
    let h:=uf 65538 w
    let bkt:=h % 1
    let d:=(s6 11 4 0>>>(1*bkt))&&&1
    let slot:=((h*17) % 1048573+d) % 6
    (s7 11 4 0>>>(4*slot))&&&15
  | _,_=>0
lemma ym : ∀ (g j : Fin 8),
    (q6 g.val>>>(4*j.val))&&&7=vo (uu g) j.val:= by decide +kernel
lemma q03 (j : Nat) (hj : j<8) :
    (q6 0>>>(4*j))&&&7=j:= by
  simpa [uu,vo] using ym 0 ⟨j,hj⟩
lemma xr (g : Fin 8) (j : Nat) (hj : j<8) :
    si ((q6 g.val>>>(4*j))&&&7) =
      r1 g (si ((q6 0>>>(4*j))&&&7)):= by
  rw [q03 j hj]; simp only [r1,s3 _ j hj]
  exact congrArg si (ym g ⟨j,hj⟩)
def u2 (permCode : Nat) : Nat->Nat->q0
  | 0,_=>rv
  | fuel+1,i =>
    if Nat.blt i 8 then si ((permCode>>>(4*i))&&&7)
    else
      let k:=i - 8
      let c:=(q2w (k>>>6)>>>(22*(k&&&63)))&&&0x3fffff
      let op:=c&&&3
      let a:=(c>>>2)&&&1023
      if Nat.beq op 0 then qx (u2 permCode fuel a)
      else
        let x:=u2 permCode fuel a
        let y:=u2 permCode fuel (c>>>12)
        if Nat.beq op 1 then (x.1&&&y.1,x.2&&&y.2) else (x.1|||y.1,x.2|||y.2)
lemma rt : ∀ (fuel i : Nat),qb (u2 (q6 0) fuel i)
  | 0,_=>vg
  | fuel+1,i=>by
    unfold u2
    split
    · exact y4 _
    · dsimp only
      split
      · exact ye (rt fuel _)
      · split
        · exact x9 false (rt fuel _) (rt fuel _)
        · exact x9 true (rt fuel _) (rt fuel _)
lemma rp (g : Fin 8) :
    ∀ (fuel i : Nat),u2 (q6 g.val) fuel i=r1 g (u2 (q6 0) fuel i)
  | 0,_=>(xw _).symm
  | fuel+1,i=>by
    unfold u2
    split
    · rename_i hi; exact xr g i (Nat.blt_eq.mp hi)
    · dsimp only
      split
      · rw [rp g fuel _]; simp only [r1,us]
      · split
        · rw [rp g fuel _,rp g fuel _]
          exact (su (uu g) false _ _).symm
        · rw [rp g fuel _,rp g fuel _]
          exact (su (uu g) true _ _).symm
def r6 (permCode code j : Nat) (acc : List q0) : List q0 :=
  if code.testBit j then si ((permCode>>>(4*j))&&&7) :: acc else acc
def qq (permCode e : Nat) (acc : List q0) : List q0 :=
  if Nat.beq e 0 then acc else u2 permCode 5 (e+7) :: acc
def ur (permCode code : Nat) (acc : List q0) : List q0 :=
  r6 permCode code 0 (r6 permCode code 1 (r6 permCode code 2 (r6 permCode code 3
    (r6 permCode code 4 (r6 permCode code 5 (r6 permCode code 6 (r6 permCode code 7 acc)))))))
lemma qt (code j : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ r6 (q6 0) code j acc,qb x:= by
  unfold r6; split
  · intro x hx; rcases List.mem_cons.mp hx with rfl | ht; exact y4 _; exact ha x ht
  · exact ha
lemma qi (e : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ qq (q6 0) e acc,qb x:= by
  unfold qq; split
  · exact ha
  · intro x hx; rcases List.mem_cons.mp hx with rfl | ht; exact rt 5 _; exact ha x ht
lemma qo (g : Fin 8) (code j : Nat) (hj : j<8) (acc : List q0) :
    (r6 (q6 0) code j acc).map (r1 g) =
      r6 (q6 g.val) code j (acc.map (r1 g)):= by
  unfold r6; split <;> simp [xr g j hj]
lemma sl (g : Fin 8) (e : Nat) (acc : List q0) :
    (qq (q6 0) e acc).map (r1 g) =
      qq (q6 g.val) e (acc.map (r1 g)):= by
  unfold qq; split <;> simp [rp]
lemma ux (code : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ ur (q6 0) code acc,qb x:= by
  unfold ur
  exact qt _ _ (qt _ _ (qt _ _ (qt _ _
    (qt _ _ (qt _ _ (qt _ _ (qt _ _ ha)))))))
lemma uh (g : Fin 8) (code : Nat) (acc : List q0) :
    (ur (q6 0) code acc).map (r1 g) =
      ur (q6 g.val) code (acc.map (r1 g)):= by
  simp only [ur,qo g _ 0 (by omega),qo g _ 1 (by omega),
    qo g _ 2 (by omega),qo g _ 3 (by omega),
    qo g _ 4 (by omega),qo g _ 5 (by omega),
    qo g _ 6 (by omega),qo g _ 7 (by omega)]
def st (permCode k t i : Nat) : List q0 :=
  let c2:=q3y k t
  if Nat.blt i c2 then
    let code:=(q3w k t (i>>>6)>>>(28*(i&&&63)))&&&0xfffffff
    qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
      (ur permCode code []))
  else
    let c3:=q3x k t
    if Nat.blt i c3 then
      let j:=i - c2
      let code:=(q3v k t (j>>>6)>>>(38*(j&&&63)))&&&0x3fffffffff
      qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
        (qq permCode ((code>>>28)&&&1023) (ur permCode code [])))
    else
      let code:=(q3u k t>>>(48*(i - c3)))&&&0xffffffffffff
      qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
        (qq permCode ((code>>>28)&&&1023) (qq permCode ((code>>>38)&&&1023)
          (ur permCode code []))))
def q8 (k t i : Nat) : List q0:=st (q6 0) k t i
lemma sx (k t i : Nat) : ∀ x ∈ q8 k t i,qb x:= by
  unfold q8 st; dsimp only
  split
  · exact qi _ (qi _ (ux _ (by simp)))
  · split
    · exact qi _ (qi _ (qi _ (ux _ (by simp))))
    · exact qi _ (qi _ (qi _ (qi _ (ux _ (by simp)))))
lemma xa (g : Fin 8) (k t i : Nat) :
    (q8 k t i).map (r1 g)=st (q6 g.val) k t i:= by
  unfold q8 st; dsimp only
  split
  · simp only [sl,uh,List.map_nil]
  · split
    · simp only [sl,uh,List.map_nil]
    · simp only [sl,uh,List.map_nil]
def r5 (k t : Nat) (w : List q0) : Bool :=
  let n:=zg k t w
  if Nat.beq n 0 then false
  else
    let m:=n - 1
    let i:=m>>>3
    Nat.blt i (qk k t) &&
      vp w (st (q6 (m&&&7)) k t i)
lemma rk {k t : Nat}
    (h : ∀ i<qk k t,qs k t (q8 k t i)) {w : List q0}
    (hw : r5 k t w=true) : qs k t w:= by
  unfold r5 at hw; dsimp only at hw
  split at hw
  · contradiction
  · simp only [Bool.and_eq_true,Nat.blt_eq] at hw
    obtain ⟨hi,hp⟩:=hw
    have hp':=yp hp
    have hlt : (zg k t w - 1)&&&7<8:= by have : (zg k t w - 1)&&&7 ≤ 7:=Nat.and_le_right; omega
    let g : Fin 8:=⟨(zg k t w - 1)&&&7,hlt⟩
    rw [← xa g k t ((zg k t w - 1)>>>3)] at hp'
    intro m hm hr
    apply h _ hi m hm
    have himg : w.toFinset.image (zk g)=(q8 k t ((zg k t w - 1)>>>3)).toFinset:= by
      ext x
      simp only [Finset.mem_image,List.mem_toFinset,hp'.mem_iff,List.mem_map]
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        have hzv:=sx k t _ z hz
        rwa [zk,r1,ut (uu g) hzv]
      · intro hx
        exact ⟨r1 g x,⟨x,hx,rfl⟩,ut (uu g) (sx k t _ x hx)⟩
    rw [← himg]
    exact xe (uu g).reverse hr
def rb (k t i : Nat) : Bool :=
  let v:=q8 k t i
  v4 v&&!xd k t v
def q4 (k t i : Nat) : Bool :=
  let v:=q8 (k+1) t i
  v4 v &&
    !v0 k t v (fun w=>!r5 k (t - 1) w) (fun w=>!r5 k t w)
def vk (t : Nat) : Bool :=
  !v0 11 t rj (fun w=>!r5 11 (t - 1) w) (fun w=>!r5 11 t w)
lemma ya {k t i : Nat} (h : rb k t i=true) :
    qs k t (q8 k t i):= by
  simp only [rb,Bool.and_eq_true,Bool.not_eq_true'] at h
  exact yy (ve h.1) h.2
lemma sk {k t i : Nat} (ht : t ≤ 5)
    (hp : ∀ t ≤ 5,∀ i<qk k t,qs k t (q8 k t i))
    (h : q4 k t i=true) : qs (k+1) t (q8 (k+1) t i):= by
  simp only [q4,Bool.and_eq_true,Bool.not_eq_true'] at h
  apply xv (ve h.1) _ _ h.2
  · intro w hw; exact rk (hp (t - 1) (by omega)) (by simpa using hw)
  · intro w hw; exact rk (hp t ht) (by simpa using hw)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3c : Theta.span (rb 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2v : Theta.span (rb 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2u : Theta.span (rb 8 0) 250 500=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2t : Theta.span (rb 8 0) 250 750=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1q : Theta.span (rb 8 0) 250 1000=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1p : Theta.span (rb 8 0) 93 1250=true:= by decide +kernel
lemma q2r : Theta.span (rb 8 0) 1343 0=true:=(@Theta.span_join (rb 8 0) 750 0 593 (@Theta.span_join (rb 8 0) 250 0 500 q3c (@Theta.span_join (rb 8 0) 250 250 250 q2v q2u)) (@Theta.span_join (rb 8 0) 250 750 343 q2t (@Theta.span_join (rb 8 0) 250 1000 93 q1q q1p)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3b : Theta.span (rb 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2s : Theta.span (rb 8 1) 99 250=true:= by decide +kernel
lemma q2q : Theta.span (rb 8 1) 349 0=true:=(@Theta.span_join (rb 8 1) 250 0 99 q3b q2s)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2p : Theta.span (rb 8 2) 6 0=true:= by decide +kernel
lemma q2o : Theta.span (rb 8 3) 0 0=true:=rfl
lemma q2n : Theta.span (rb 8 4) 0 0=true:=rfl
lemma q2m : Theta.span (rb 8 5) 0 0=true:=rfl
lemma q1r (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 8 t) : rb 8 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q2r i (Nat.zero_le i) hi
  · exact Theta.span_ok q2q i (Nat.zero_le i) hi
  · exact Theta.span_ok q2p i (Nat.zero_le i) hi
  · exact Theta.span_ok q2o i (Nat.zero_le i) hi
  · exact Theta.span_ok q2n i (Nat.zero_le i) hi
  · exact Theta.span_ok q2m i (Nat.zero_le i) hi
lemma zt (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 8 t) : qs 8 t (q8 8 t i) :=
  ya (q1r t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3a : Theta.span (q4 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2l : Theta.span (q4 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2k : Theta.span (q4 8 0) 102 500=true:= by decide +kernel
lemma q2i : Theta.span (q4 8 0) 602 0=true:=(@Theta.span_join (q4 8 0) 250 0 352 q3a (@Theta.span_join (q4 8 0) 250 250 102 q2l q2k))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q39 : Theta.span (q4 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2j : Theta.span (q4 8 1) 128 250=true:= by decide +kernel
lemma q2h : Theta.span (q4 8 1) 378 0=true:=(@Theta.span_join (q4 8 1) 250 0 128 q39 q2j)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2g : Theta.span (q4 8 2) 41 0=true:= by decide +kernel
lemma q2f : Theta.span (q4 8 3) 0 0=true:=rfl
lemma q2e : Theta.span (q4 8 4) 0 0=true:=rfl
lemma q2d : Theta.span (q4 8 5) 0 0=true:=rfl
lemma q1o (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 9 t) : q4 8 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q2i i (Nat.zero_le i) hi
  · exact Theta.span_ok q2h i (Nat.zero_le i) hi
  · exact Theta.span_ok q2g i (Nat.zero_le i) hi
  · exact Theta.span_ok q2f i (Nat.zero_le i) hi
  · exact Theta.span_ok q2e i (Nat.zero_le i) hi
  · exact Theta.span_ok q2d i (Nat.zero_le i) hi
lemma zr (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 9 t) : qs 9 t (q8 9 t i) :=
  sk ht zt (q1o t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q23 : Theta.span (q4 9 0) 64 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q22 : Theta.span (q4 9 1) 84 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q21 : Theta.span (q4 9 2) 43 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q20 : Theta.span (q4 9 3) 8 0=true:= by decide +kernel
lemma q1z : Theta.span (q4 9 4) 0 0=true:=rfl
lemma q1y : Theta.span (q4 9 5) 0 0=true:=rfl
lemma q0z (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 10 t) : q4 9 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q23 i (Nat.zero_le i) hi
  · exact Theta.span_ok q22 i (Nat.zero_le i) hi
  · exact Theta.span_ok q21 i (Nat.zero_le i) hi
  · exact Theta.span_ok q20 i (Nat.zero_le i) hi
  · exact Theta.span_ok q1z i (Nat.zero_le i) hi
  · exact Theta.span_ok q1y i (Nat.zero_le i) hi
lemma zb (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 10 t) : qs 10 t (q8 10 t i) :=
  sk ht zr (q0z t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1x : Theta.span (q4 10 0) 5 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1w : Theta.span (q4 10 1) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1v : Theta.span (q4 10 2) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1u : Theta.span (q4 10 3) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1t : Theta.span (q4 10 4) 1 0=true:= by decide +kernel
lemma q1s : Theta.span (q4 10 5) 0 0=true:=rfl
lemma q0y (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 11 t) : q4 10 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q1x i (Nat.zero_le i) hi
  · exact Theta.span_ok q1w i (Nat.zero_le i) hi
  · exact Theta.span_ok q1v i (Nat.zero_le i) hi
  · exact Theta.span_ok q1u i (Nat.zero_le i) hi
  · exact Theta.span_ok q1t i (Nat.zero_le i) hi
  · exact Theta.span_ok q1s i (Nat.zero_le i) hi
lemma x7 (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 11 t) : qs 11 t (q8 11 t i) :=
  sk ht zb (q0y t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v3 : vk 0=true/\vk 1=true/\vk 2=true/\vk 3=true/\vk 4=true/\vk 5=true:= by decide +kernel
lemma q02 (t : Nat) (ht : t ≤ 5) : vk t=true:= by
  interval_cases t
  · exact v3.1
  · exact v3.2.1
  · exact v3.2.2.1
  · exact v3.2.2.2.1
  · exact v3.2.2.2.2.1
  · exact v3.2.2.2.2.2
lemma yk (t : Nat) (ht : t ≤ 5) : qs 12 t rj:= by
  have h:=q02 t ht
  simp only [vk,Bool.not_eq_true'] at h
  apply xv q19 _ _ h
  · intro w hw; exact rk (x7 (t - 1) (by omega)) (by simpa using hw)
  · intro w hw; exact rk (x7 t ht) (by simpa using hw)
theorem no_live12 {k t : Nat} {S : Finset Sig} (hk : k ≤ 12) (h : Live k t S)
    (hsub : ∀ a ∈ S,a ∈ raw) : False:= by
  have hn : qy k t (S.image y7):=z5 h
  have hnsub : ∀ a ∈ S.image y7,a ∈ rj:= by
    intro a ha; obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    exact q00 (hsub x hx)
  have eq:=q1l hn hnsub
  rw [← eq] at hn
  have sz:=xg hn
  rw [List.toFinset_card_of_nodup q19] at sz
  have hlen : rj.length=8:=rfl
  have ht : t ≤ 5:= by omega
  exact yk t ht k hk (yl hn (xf hk))
end Base1007
namespace Pos3068
abbrev B := BitVec 252
abbrev Sig := B × B
def top : B := BitVec.allOnes 252
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit position pairs a positive and a negative input row.
def raw0 : Sig := (0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff, 0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def raw1 : Sig := (0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff, 0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def raw2 : Sig := (0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000, 0x288f043070431810c6040140208600486843828c4604588c09191234230)
def raw3 : Sig := (0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000, 0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def raw4 : Sig := (0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000, 0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def raw5 : Sig := (0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000, 0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def raw6 : Sig := (0xfffffe00000000000000003fffffffffffffff0000000000000000000000000, 0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def raw7 : Sig := (0xffffffffffffffffffffffc0000000000000000000000000000000000000000, 0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 252
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 252
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 252)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 252) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 252 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 252)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 252) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 252).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]

def sample (s : Bool) (i : Fin 252) (j : Fin 8) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)

private lemma sample_ok : ∀ (s : Bool) (i : Fin 252), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)


theorem toBase {k t S} (h : Live k t S) : Base1007.Live k t S := by
  induction h with
  | stop => exact .stop
  | unary a b h ih => exact .unary a b ih
  | binary a b ab fresh tail ih => exact .binary a b ab fresh ih

theorem positive : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 edgeF 12 := by
  rintro ⟨C,hfan,hs,he⟩
  obtain ⟨k,t,S,hk,ht,hmem⟩ := extract C.gates raw hfan (circuit_target C hfan he)
  exact Base1007.no_live12 (hk.trans hs) (toBase ht) hmem

end Pos3068

namespace Meta3068OneNot
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

theorem remove_only_not {n : ℕ} (C : Circuit) (f : (Fin n → Bool) → Bool)
    (hf : FanInTwo C) (hc : C.gates.countP isNot ≤ 1)
    (hzero : f (fun _ => false) = false) (hone : f (fun _ => true) = true)
    (hcomp : ∀ x, C.eval (List.ofFn x) = !(f x)) : HasCircuitSize n f C.size := by
  classical
  let z : Fin n → Bool := fun _ => false
  let t : Fin n → Bool := fun _ => true
  have endpoint0 : C.eval (List.ofFn z) = true := by rw [hcomp,hzero]; rfl
  have endpoint1 : C.eval (List.ofFn t) = false := by rw [hcomp,hone]; rfl
  have ao (g : Gate) (hg : g ∈ C.gates) (hn : g.op ≠ .not) :
      g.op = .and ∨ g.op = .or := by
    rcases (hf g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn h)
  by_cases hex : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g,hg,hop⟩ := hex
    obtain ⟨pre,post,heq,_⟩ := List.eq_append_cons_of_mem hg
    have hgnot : isNot g = true := (isNot_iff g).mpr hop
    rw [heq,List.countP_append,List.countP_cons,hgnot] at hc
    simp only [↓reduceIte] at hc
    have hpre (q) (hq : q ∈ pre) : q.op = .and ∨ q.op = .or := by
      apply ao q (by simp [heq,hq])
      intro h; exact (List.countP_eq_zero.mp (show pre.countP isNot = 0 by omega) q hq)
        ((isNot_iff q).mpr h)
    have hpost (q) (hq : q ∈ post) : q.op = .and ∨ q.op = .or := by
      apply ao q (by simp [heq,hq])
      intro h; exact (List.countP_eq_zero.mp (show post.countP isNot = 0 by omega) q hq)
        ((isNot_iff q).mpr h)
    let P := fun x : Fin n → Bool => pre.foldl step (List.ofFn x)
    let r := g.inputs.headD (n+pre.length)
    let H := fun (x : Fin n → Bool) (b : Bool) => (post.foldl step (P x ++ [b])).getD C.output false
    have hgate (x) : g.op.eval (g.inputs.map fun i => (P x).getD i false) =
        !((P x).getD r false) := by
      rw [hop]; dsimp only [r]
      cases e : g.inputs with
      | nil => rw [List.getD_eq_default _ _ (by simp [P,fold_length])]; rfl
      | cons i l => rfl
    have val (x) : C.eval (List.ofFn x) = H x (!((P x).getD r false)) := by
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
      rw [heq,List.foldl_append,List.foldl_cons]
      change (post.foldl step (P x ++ [_])).getD C.output false = _
      rw [hgate]
    have mono (x y : Fin n → Bool) (i j : Bool)
        (xy : ∀ k, x k = true → y k = true) (ij : i = true → j = true) :
        H x i = true → H y j = true := by
      have hl : (P x).length = (P y).length := by simp [P,fold_length]
      have hp : LeL (P x) (P y) := fold_mono pre hpre _ _ (by simp) (leInputs x y xy)
      exact fold_mono post hpost _ _ (by simp [hl]) (leSnoc hl hp ij) C.output
    rw [val] at endpoint0 endpoint1
    have proj (x : Fin n → Bool) (b : Bool) : H x b = b := by
      cases b
      · cases hx : H x false with
        | false => rfl
        | true =>
          have h := mono x t false (!((P t).getD r false)) (by simp [t]) (by simp) hx
          rw [endpoint1] at h
          contradiction
      · exact mono z x _ true (by simp [z]) (by simp) endpoint0
    refine ⟨⟨pre,r⟩,fun q hq => hf q (by simp [heq,hq]),?_,?_⟩
    · simp [Circuit.size,heq]
    · intro x
      have h := hcomp x
      rw [val,proj] at h
      change (P x).getD r false = f x
      simpa only [Bool.not_not] using congrArg Bool.not h
  · have hm (q) (hq : q ∈ C.gates) := ao q hq (fun h => hex ⟨q,hq,h⟩)
    have h := fold_mono C.gates hm (List.ofFn z) (List.ofFn t) (by simp)
      (leInputs z t (by simp [z])) C.output endpoint0
    change C.eval (List.ofFn t) = true at h
    rw [endpoint1] at h
    contradiction

theorem remove_only_not_rec (n : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool) :
    FanInTwo C → C.gates.countP (fun g : Gate =>
      GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ 1 →
    f (fun _ => false) = false → f (fun _ => true) = true →
    (∀ x, C.eval (List.ofFn x) = !(f x)) → HasCircuitSize n f C.size := by
  intro hf hc
  have he : (fun g : Gate =>
      GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) = isNot := by
    funext g
    rcases g with ⟨op,ls⟩
    cases op <;> rfl
  rw [he] at hc
  exact remove_only_not C f hf hc

end Meta3068OneNot

namespace H8Free

-- The live-wire compression argument follows the project proof of L-meta-703.
-- The live-wire reduction and circuit semantics follow the merged L-meta-1429.
-- Each finite search layer below is checked against the next layer of smaller states.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 152 pairs of assignments.
abbrev W := BitVec 304
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 152 := ((x >>> 152) ^^^ x).setWidth 152
def cuts (ws : List W) : BitVec 152 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 152) ++ (0 : BitVec 152)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 152) (w : W) : Prop :=
  w.getLsbD (152+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 152) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 152+i.val < 304 := by omega
  have hi' : i.val < 304 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 152) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 152)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : W) : List W → List W
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List W) := ws.foldr insertW []

theorem insertW_perm (v : W) (ws : List W) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List W) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

def children (k : ℕ) (ws : List W) : List (List W) := (pairs ws).flatMap fun (a,b,r) =>
  (ops a b).flatMap fun z =>
    (keepChoices a b r).filterMap fun kept =>
      if kept.length ≤ k ∧ cuts (z :: kept) = -1 then some (ordered (z :: kept)) else none

def earlier : List W → List W → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: r => if a = b then earlier l r else decide (a.toNat < b.toNat)

def containsKey (q : List W) : BinaryTree (List W) → Bool
  | .nil => false
  | .node a l r => if q = a then true else if earlier q a then containsKey q l else containsKey q r

def everyKey (f : List W → Bool) : BinaryTree (List W) → Bool
  | .nil => true
  | .node a l r => f a && everyKey f l && everyKey f r

theorem every_at {f : List W → Bool} {q : List W} (tr : BinaryTree (List W))
    (ha : everyKey f tr = true) (hm : containsKey q tr = true) : f q = true := by
  induction tr with
  | nil => contradiction
  | node a l r il ir =>
    simp only [everyKey,Bool.and_eq_true] at ha
    simp only [containsKey] at hm
    split at hm
    next e => simpa [e] using ha.1.1
    next e =>
      split at hm
      · exact il ha.1.2 hm
      · exact ir ha.2 hm

def Closed (k : Nat) (tr : BinaryTree (List W)) : Prop :=
  ∀ (g : W), g = goal ∨ g = ~~~goal → ∀ ws : List W,
    ws.Nodup → ws.length ≤ 12 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

def doneTest (s : List W) : Bool := s == [goal] || s == [~~~goal]

theorem closed_nil (tr : BinaryTree (List W)) (hc : everyKey (fun q => !doneTest q) tr = true) :
    Closed 0 tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  have eq := singleton_list hn h
  rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy

def rowOK (k : Nat) (tr : BinaryTree (List W)) (ws : List W) :=
  !doneTest ws && (children k ws).all (fun child => containsKey child tr)

theorem perm_set {u v : List W} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

theorem closed_next (k : Nat) (hk : k < 12) (tr next : BinaryTree (List W))
    (hnext : Closed k next) (hc : everyKey (rowOK k next) tr = true) :
    Closed (k+1) tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  simp only [rowOK,Bool.and_eq_true,List.all_eq_true] at hy
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have hp' := ordered_perm (z :: kept)
      have mem : ordered (z :: kept) ∈ children k ws := by
        apply List.mem_flatMap.mpr
        refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
        exact List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ k by omega,cuts_full hg hraw]⟩
      have sz : (ordered (z :: kept)).length ≤ 12 := by rw [hp'.length_eq]; simp only [List.length_cons]; omega
      apply hnext g hg _ (hp'.nodup_iff.mpr hnd) sz (hy.2 _ mem)
      rwa [perm_set hp']
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def startOK (n : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n+1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BinaryTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 12) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g n ins.toFinset := by
  intro hb
  classical
  obtain ⟨s,hs,hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd := nd.filter (fun u => decide (u ∈ s))
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have size := live_card hl'
  rw [List.toFinset_card_of_nodup (show ws.Nodup from hnd)] at size
  have sub : ws.Sublist ins := List.filter_sublist ..
  have key := List.all_eq_true.mp hi ws (List.mem_sublists.mpr sub)
  have perm := ordered_perm ws
  apply hc g hg (ordered ws) (perm.nodup_iff.mpr hnd) (by rw [perm.length_eq]; exact sub.length_le.trans small) ?_
  · rwa [perm_set perm]
  · simpa [startOK,size,cuts_full hg hl'] using key

open PEqualNP.CircuitLowerBounds

def ins : List W := [0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]

open PEqualNP.CircuitLowerBounds
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 304 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 304)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 304) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 304) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 304) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#304)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
def antiEdge (x : Fin 8 → Bool) : Bool :=
  !((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem probe : ∀ j : Fin 304,
    antiEdge (fun i : Fin 8 => bit j (ins.getD i.val 0)) = bit j goal := by decide +kernel

theorem lower_cost (low : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 10 ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = antiEdge x) : 10 < binaryCost gs := by
  by_contra! bound
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 304) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 8) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [ins]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact probe k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact low t ht (lift bound run)

theorem cost_count (gs : List Gate) :
    binaryCost gs + gs.countP (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨op,ls⟩
    unfold binaryCost at *
    rw [List.filter_cons,List.countP_cons]
    cases op <;> simp [isBinary] <;> omega

theorem core_two (low : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 10 ins.toFinset)
    (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 12)
    (hn : 2 ≤ C.gates.countP (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)) :
    ¬ ∀ y : Fin 8 → Bool, C.eval (List.ofFn y) = antiEdge y := by
  intro h
  have hb := lower_cost low C.gates C.output hf h
  have hc := cost_count C.gates
  change C.gates.length ≤ 12 at hs
  omega


set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def descend (k : Nat) (ws : List W) (f : List W → Bool) : Bool :=
  (pairs ws).any fun (a,b,r) =>
    let c := cuts r
    let ca := sep a ||| c
    let cb := sep b ||| c
    let cab := sep a ||| cb
    let n := r.length
    (ops a b).any fun z =>
      let dz := sep z
      (decide (n ≤ k) && (dz ||| c == -1) && f (z :: r)) ||
      (decide (n+1 ≤ k) && (dz ||| ca == -1) && f (z :: a :: r)) ||
      (decide (n+1 ≤ k) && (dz ||| cb == -1) && f (z :: b :: r)) ||
      (decide (n+2 ≤ k) && (dz ||| cab == -1) && f (z :: a :: b :: r))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem descend_hit {k ws a b r z kept f}
    (hm : (a,b,r) ∈ pairs ws) (hz : z ∈ ops a b)
    (hk : kept ∈ keepChoices a b r) (hl : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (hf : f (z :: kept) = true) : descend k ws f = true := by
  apply List.any_eq_true.mpr ⟨(a,b,r),hm,?_⟩
  apply List.any_eq_true.mpr ⟨z,hz,?_⟩
  simp only [keepChoices,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with eq | eq | eq | eq <;> subst kept
  · change sep z ||| cuts r = -1 at hc
    simp [hl,hc,hf]
  · change sep z ||| (sep a ||| cuts r) = -1 at hc
    change r.length+1 ≤ k at hl
    simp [hl,hc,hf]
  · change sep z ||| (sep b ||| cuts r) = -1 at hc
    change r.length+1 ≤ k at hl
    simp [hl,hc,hf]
  · change sep z ||| (sep a ||| (sep b ||| cuts r)) = -1 at hc
    change r.length+2 ≤ k at hl
    simp [hl,hc,hf]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem descend_sound {k : Nat} {g : W} (hg : g = goal ∨ g = ~~~goal)
    {ws : List W} (hn : ws.Nodup) (h : live basicOps g (k+1) ws.toFinset)
    (f : List W → Bool) (hf : ∀ ys : List W, ys.Nodup → live basicOps g k ys.toFinset → f ys = true) :
    doneTest ws || descend k ws f = true := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq,doneTest]
  · rw [Bool.or_eq_true]
    right
    obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : descend k ws f = true := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      exact descend_hit hmem (List.mem_toFinset.mp hop) hkeep (by omega) (cuts_full hg hraw) (hf _ hnd hraw)
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def ahead : Nat → Nat → List W → Bool
  | 0, _, _ => true
  | _+1, 0, ws => doneTest ws
  | d+1, k+1, ws => doneTest ws || descend k ws (ahead d k)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ahead_sound {g : W} (hg : g = goal ∨ g = ~~~goal) (d k : Nat)
    {ws : List W} (hn : ws.Nodup) (h : live basicOps g k ws.toFinset) : ahead d k ws = true := by
  induction d generalizing k ws with
  | zero => rfl
  | succ d ih =>
    cases k with
    | zero =>
      have eq := singleton_list hn h
      rcases hg with rfl | rfl <;> simp [ahead,eq,doneTest]
    | succ k => exact descend_sound hg hn h _ (fun _ hn' h' => ih _ hn' h')


set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def packBits (f : Fin 304 → Bool) : W :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma packBits_bit (f : Fin 304 → Bool) (j : Fin 304) : (packBits f)[j.val] = f j := by
  rw [← BitVec.getLsbD_eq_getElem]
  simp only [packBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using j.isLt)]
  exact List.getElem_ofFn _
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def freeP (i : Fin 8) : Nat := ![0x97969594939291908f8e8d8c8b8a898887868584838281807f7e7d7c7b7a797877767574737271706f6e6d6c6b6a696867666564636261605f5e5d5c5b5a595857565554535251504f4e4d4c4b4a494847464544434241403f3e3d3c3b3a393837363534333231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100, 0x484647494538353639373331323488898586878384808182211f20221e0b08090a070506717073726d6c6f6e69686b6a656467664c4d4b4e4a3e3d403f3b3a3c434244412e302f2c2d606263615f9497959693555756545c5b5e5d585a598f928e90918a8d8b8c5251534f5028292a2b27131415127c7f7d7e7b1a1b1c1d19030402242526230f0e11100c0d7a7778797674751718160001, 0x48494546474d4e4a4b4c43444142292a2b27281b1c1d191a21221e1f2025262324171816727370716a6b68696e6f6c6d6667646537383935363f403d3e2f302e333431323c3a3b2d2c91928e8f9096979394958c8d8a8b5d5e5b5c5351526162635f6056575455595a58504f8788898586797a77787e7f7b7c7d82838480817576740a0b080910110e0f0100141512130402030705060d0c, 0x979493969562605f6163575554562a2928272b1c1b1a191d7f7c7b7e7d141312150403027071727368696a6b6c6d6e6f646566678e928f91905b5c5d5e5152538d8a8c8b58595a4f5035383739364648454947313334323d3e3f402e2f304b4d4c4a4e424341443a3b3c2c2d8589888786080b0a091f211e22208084838281050706777a79780e0f10110001252423261716187675740c0d, 0x272b2a28294a4e4d4c4b232625244745494846201e22211f191d1c1a1b41444342161817727371705d5e5c5b3f403e3d10110f0e615f6360626e6f6d6c595a58121513143c3b3a0d0c91908f8e9287868985887978777a6a6b696853525137363938350a090b082f302e010096959394978c8b8a8d82818480837e7d7b7c7f7574765654555766676564504f323433310607050203042d2c, 0x8685898788363538373909080b0a45474648491e201f2122818084828332313334060507717072735c5b5d5e3e3d3f400f0e10118f908e919269686a6b5251537877797a2e2f300001605f61636228272a2b29131215146d6c6e6f58595a4c4a4b4d4e242325263b3a3c0c0d9493959697555456571a191c1d1b7c7b7d7e7f0302048a8b8c8d656466674f50414243441617187475762c2d, 0x86878885899091928e8f78797a7793959697947b7d7e7f7c81828380848b8c8d8a74757673727071403f3d3e5e5d5b5c11100e0f39363735386b6a6869302f2e090a080b53515201004e4a4b4c4d2b2729282a262324256f6e6c6d3c3a3b635f616260151214135a59580d0c4945474648444142431d191b1a1c221e201f2118161734323133676664652d2c54565755020403060507504f, 0x2728292b2a5f606263611213141595939497967d7b7c7f7e191a1b1d1c54555756020304707173723d3e403f5b5c5e5d0e0f11104b4a4c4e4d6c6d6f6e3a3b3c23242625585a590c0d3536393738858688878908090a0b68696b6a2e302f8e908f929177787a79515253000146474549483132343380818382841f201e222105060742414443646567662c2d8b8a8d8c7476751618174f50] i

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def co (i : Fin 8) (j : Fin 304) : Fin 304 :=
  let lo := (freeP i >>> (8 * (j.val % 152))) &&& 255
  ⟨(lo + (j.val / 152) * 152) % 304, Nat.mod_lt _ (by decide)⟩
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def sym (i : Fin 8) (w : W) : W := packBits (fun j => w[(co i j).val])
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_bit (i : Fin 8) (w : W) (j : Fin 304) :
    (sym i w)[j.val] = w[(co i j).val] := packBits_bit _ _
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def invSym (i : Fin 8) : Fin 8 := ![0, 1, 2, 3, 4, 7, 6, 5] i
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma inv_co (i : Fin 8) (j : Fin 304) : co i (co (invSym i) j) = j := by
  revert i j
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_injective (i : Fin 8) : Function.Injective (sym i) := by
  intro a b h
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have eq := congrArg (fun w : W => w[(co (invSym i) ⟨j,hj⟩).val]) h
  simpa only [sym_bit, inv_co] using eq
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_and (i : Fin 8) (a b : W) : sym i (a &&& b) = sym i a &&& sym i b := by
  apply BitVec.eq_of_getElem_eq; intro j hj
  rw [sym_bit i _ ⟨j,hj⟩, BitVec.getElem_and, BitVec.getElem_and, sym_bit i a ⟨j,hj⟩, sym_bit i b ⟨j,hj⟩]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_or (i : Fin 8) (a b : W) : sym i (a ||| b) = sym i a ||| sym i b := by
  apply BitVec.eq_of_getElem_eq; intro j hj
  rw [sym_bit i _ ⟨j,hj⟩, BitVec.getElem_or, BitVec.getElem_or, sym_bit i a ⟨j,hj⟩, sym_bit i b ⟨j,hj⟩]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_not (i : Fin 8) (a : W) : sym i (~~~a) = ~~~(sym i a) := by
  apply BitVec.eq_of_getElem_eq; intro j hj
  rw [sym_bit i _ ⟨j,hj⟩, BitVec.getElem_not, BitVec.getElem_not, sym_bit i a ⟨j,hj⟩]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_goal (i : Fin 8) : sym i goal = goal := by revert i; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_basic (i : Fin 8) {a b z : W} (h : z ∈ basicOps a b) :
    sym i z ∈ basicOps (sym i a) (sym i b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp [sym_and, sym_or, sym_not]
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma sym_live (i : Fin 8) {k g s} (hg : g = goal ∨ g = ~~~goal) (h : live basicOps g k s) :
    live basicOps g k (s.image (sym i)) := by
  have hfix : sym i g = g := by rcases hg with rfl|rfl <;> simp [sym_not,sym_goal]
  induction k generalizing s with
  | zero => change s = {g} at h; rw [h]; simp [live,hfix]
  | succ k ih =>
    rcases h with h | ⟨a,ha,b,hb,hab,z,hz,hnew,r,hs,ht⟩
    · exact .inl (ih h)
    · refine .inr ⟨sym i a, Finset.mem_image_of_mem _ ha, sym i b, Finset.mem_image_of_mem _ hb,
        fun eq => hab (sym_injective i eq), sym i z, sym_basic i hz, ?_, r.image (sym i), ?_, ?_⟩
      · intro hz'; obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp hz'; exact hnew ((sym_injective i eq) ▸ hx)
      · simp [hs]
      · simpa using ih ht

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem symOK (i : Fin 8) (k : ℕ) (g : W) (hg : g = goal ∨ g = ~~~goal) (ws : List W)
    (h : live basicOps g k ws.toFinset) : live basicOps g k ((ws.map (sym i)).toFinset) := by
  have eq : (ws.map (sym i)).toFinset = ws.toFinset.image (sym i) := by
    ext w
    simp
  rw [eq]
  exact sym_live i hg h

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def certRow (k : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(doneTest ws || descend k ws (fun zs => !containsKey (ordered zs) tr))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem checkedLayer (k : Nat) (hk : k < 12) (tr next : BinaryTree (List W))
    (hs : Closed k next) (hc : everyKey (certRow k next) tr = true) :
    Closed (k+1) tr := by
  intro g hg ws hn _ hm h
  have ok := every_at tr hc hm
  have impossible := descend_sound hg hn h (fun zs => !containsKey (ordered zs) next) (by
    intro ys hy hr
    cases eq : containsKey (ordered ys) next with
    | false => rfl
    | true =>
      have hp := ordered_perm ys
      have hl := live_card hr
      rw [List.toFinset_card_of_nodup hy] at hl
      have hsize : (ordered ys).length ≤ 12 := by rw [hp.length_eq]; omega
      exact False.elim (hs g hg _ (hp.nodup_iff.mpr hy) hsize eq (by rwa [perm_set hp])))
  simp only [certRow,Bool.not_eq_true'] at ok
  cases hd : doneTest ws <;> cases hh : descend k ws (fun zs => !containsKey (ordered zs) next) <;> simp_all

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem splitCheck {f : List W → Bool} {ws} {l r : BinaryTree (List W)}
    (m : f ws = true) (a : everyKey f l = true) (b : everyKey f r = true) :
    everyKey f (.node ws l r) = true := by simp [everyKey,m,a,b]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem closedEmpty (k : Nat) : Closed k .nil := by
  intro g hg ws hn hl hm
  contradiction

def wa : W := 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07
def wb : W := 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d
def wc : W := 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8
def wd : W := 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240
def we : W := 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402
def wf : W := 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010
def wg : W := 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880
def wh : W := 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000
def wi : W := wa&&&wd
def wj : W := wa|||wd
def wk : W := wa&&&wf
def wl : W := wa&&&~~~wh
def wm : W := wb&&&wc
def wn : W := wb|||wc
def wo : W := wb&&&we
def wp : W := wc&&&wd
def wq : W := wc|||wd
def wr : W := wc|||we
def ws : W := wc&&&wf
def wt : W := wc&&&~~~wh
def wu : W := wd|||we
def wv : W := wd|||wf
def ww : W := wd&&&~~~wg
def wx : W := wd&&&~~~wh
def wy : W := we&&&~~~wf
def wz : W := we&&&~~~wg
def wA : W := we&&&~~~wh
def wB : W := wf&&&~~~wg
def wC : W := wp&&&we
def wD : W := wp|||we
def wE : W := wp&&&~~~we
def wF : W := we&&&~~~wp
def wG : W := wp&&&~~~wd
def wH : W := wd&&&~~~wp
def wI : W := wp&&&wf
def wJ : W := wp|||wf
def wK : W := wp&&&~~~wf
def wL : W := wf&&&~~~wp
def wM : W := wc&&&~~~wp
def wN : W := wp&&&wa
def wO : W := wp|||wa
def wP : W := wp&&&~~~wa
def wQ : W := wa&&&~~~wp
def wR : W := wp&&&wb
def wS : W := wp|||wb
def wT : W := wp&&&~~~wb
def wU : W := wb&&&~~~wp
def wV : W := wp&&&wg
def wW : W := wp|||wg
def wX : W := wp&&&~~~wg
def wY : W := wg&&&~~~wp
def wZ : W := wp&&&wh
def w0 : W := wp|||wh
def w1 : W := wp&&&~~~wh
def w2 : W := wh&&&~~~wp
def w3 : W := we&&&wd
def w4 : W := we&&&~~~wd
def w5 : W := wd&&&~~~we
def w6 : W := we&&&wf
def w7 : W := we|||wf
def w8 : W := wf&&&~~~we
def w9 : W := we&&&wc
def waa : W := we&&&~~~wc
def wab : W := wc&&&~~~we
def wac : W := we|||wa
def wad : W := wa&&&~~~we
def wae : W := we|||wb
def waf : W := we&&&~~~wb
def wag : W := wb&&&~~~we
def wah : W := we&&&wg
def wai : W := we|||wg
def waj : W := wg&&&~~~we
def wak : W := we&&&wh
def wal : W := we|||wh
def wam : W := wh&&&~~~we
def wan : W := wd&&&wf
def wao : W := wd&&&~~~wf
def wap : W := wf&&&~~~wd
def waq : W := wd&&&~~~wa
def war : W := wa&&&~~~wd
def was : W := wd|||wb
def wat : W := wd&&&~~~wb
def wau : W := wb&&&~~~wd
def wav : W := wd&&&wg
def waw : W := wd|||wg
def wax : W := wg&&&~~~wd
def way : W := wd&&&wh
def waz : W := wd|||wh
def waA : W := wh&&&~~~wd
def waB : W := wf|||wc
def waC : W := wf&&&~~~wc
def waD : W := wc&&&~~~wf
def waE : W := wf|||wa
def waF : W := wf&&&~~~wa
def waG : W := wa&&&~~~wf
def waH : W := wf&&&wb
def waI : W := wb&&&~~~wf
def waJ : W := wf&&&wg
def waK : W := wf|||wg
def waL : W := wg&&&~~~wf
def waM : W := wf|||wh
def waN : W := wf&&&~~~wh
def waO : W := wc|||wa
def waP : W := wc&&&~~~wa
def waQ : W := wa&&&~~~wc
def waR : W := wc&&&~~~wb
def waS : W := wb&&&~~~wc
def waT : W := wc&&&wg
def waU : W := wc|||wg
def waV : W := wc&&&~~~wg
def waW : W := wc&&&wh
def waX : W := wc|||wh
def waY : W := wh&&&~~~wc
def waZ : W := wa&&&wb
def wa0 : W := wb&&&~~~wa
def wa1 : W := wa&&&wh
def wa2 : W := wa|||wh
def wa3 : W := wh&&&~~~wa
def wa4 : W := wb|||wg
def wa5 : W := wb&&&~~~wg
def wa6 : W := wg&&&~~~wb
def wa7 : W := wm&&&we
def wa8 : W := wm|||we
def wa9 : W := wm&&&~~~we
def wba : W := we&&&~~~wm
def wbb : W := wm|||wd
def wbc : W := wm&&&~~~wd
def wbd : W := wd&&&~~~wm
def wbe : W := wm&&&wf
def wbf : W := wm|||wf
def wbg : W := wm&&&~~~wf
def wbh : W := wf&&&~~~wm
def wbi : W := wm&&&wa
def wbj : W := wm|||wa
def wbk : W := wm&&&~~~wa
def wbl : W := wa&&&~~~wm
def wbm : W := wm&&&wg
def wbn : W := wm|||wg
def wbo : W := wm&&&~~~wg
def wbp : W := wg&&&~~~wm
def wbq : W := wm&&&wh
def wbr : W := wm|||wh
def wbs : W := wm&&&~~~wh
def wbt : W := wh&&&~~~wm
def wbu : W := wo&&&wd
def wbv : W := wo|||wd
def wbw : W := wo&&&~~~wd
def wbx : W := wd&&&~~~wo
def wby : W := wo&&&wf
def wbz : W := wo|||wf
def wbA : W := wo&&&~~~wf
def wbB : W := wf&&&~~~wo
def wbC : W := wo|||wc
def wbD : W := wo&&&~~~wc
def wbE : W := wc&&&~~~wo
def wbF : W := wo&&&wa
def wbG : W := wo|||wa
def wbH : W := wo&&&~~~wa
def wbI : W := wa&&&~~~wo
def wbJ : W := wo&&&wg
def wbK : W := wo|||wg
def wbL : W := wo&&&~~~wg
def wbM : W := wg&&&~~~wo
def wbN : W := wo&&&wh
def wbO : W := wo|||wh
def wbP : W := wo&&&~~~wh
def wbQ : W := wh&&&~~~wo
def wbR : W := wy&&&wd
def wbS : W := wy|||wd
def wbT : W := wy&&&~~~wd
def wbU : W := wd&&&~~~wy
def wbV : W := wy&&&wc
def wbW : W := wy|||wc
def wbX : W := wy&&&~~~wc
def wbY : W := wc&&&~~~wy
def wbZ : W := wy&&&wa
def wb0 : W := wy|||wa
def wb1 : W := wy&&&~~~wa
def wb2 : W := wa&&&~~~wy
def wb3 : W := wy|||wb
def wb4 : W := wy&&&~~~wb
def wb5 : W := wb&&&~~~wy
def wb6 : W := wy&&&wg
def wb7 : W := wy|||wg
def wb8 : W := wy&&&~~~wg
def wb9 : W := wg&&&~~~wy
def wca : W := wy&&&wh
def wcb : W := wy|||wh
def wcc : W := wy&&&~~~wh
def wcd : W := wh&&&~~~wy
def wce : W := ws&&&we
def wcf : W := ws|||we
def wcg : W := ws&&&~~~we
def wch : W := we&&&~~~ws
def wci : W := ws|||wd
def wcj : W := ws&&&~~~wd
def wck : W := wd&&&~~~ws
def wcl : W := ws&&&wa
def wcm : W := ws|||wa
def wcn : W := ws&&&~~~wa
def wco : W := wa&&&~~~ws
def wcp : W := ws|||wb
def wcq : W := ws&&&~~~wb
def wcr : W := wb&&&~~~ws
def wcs : W := ws&&&wg
def wct : W := ws|||wg
def wcu : W := ws&&&~~~wg
def wcv : W := wg&&&~~~ws
def wcw : W := ws&&&wh
def wcx : W := ws|||wh
def wcy : W := ws&&&~~~wh
def wcz : W := wh&&&~~~ws
def wcA : W := wt&&&we
def wcB : W := wt|||we
def wcC : W := wt&&&~~~we
def wcD : W := we&&&~~~wt
def wcE : W := wt|||wd
def wcF : W := wt&&&~~~wd
def wcG : W := wd&&&~~~wt
def wcH : W := wt|||wf
def wcI : W := wt&&&~~~wf
def wcJ : W := wf&&&~~~wt
def wcK : W := wt&&&wa
def wcL : W := wt|||wa
def wcM : W := wt&&&~~~wa
def wcN : W := wa&&&~~~wt
def wcO : W := wt|||wb
def wcP : W := wt&&&~~~wb
def wcQ : W := wb&&&~~~wt
def wcR : W := wt&&&wg
def wcS : W := wt|||wg
def wcT : W := wt&&&~~~wg
def wcU : W := wg&&&~~~wt
def wcV : W := ww&&&we
def wcW : W := ww|||we
def wcX : W := ww&&&~~~we
def wcY : W := we&&&~~~ww
def wcZ : W := ww&&&wf
def wc0 : W := ww|||wf
def wc1 : W := ww&&&~~~wf
def wc2 : W := wf&&&~~~ww
def wc3 : W := ww|||wc
def wc4 : W := ww&&&~~~wc
def wc5 : W := wc&&&~~~ww
def wc6 : W := ww&&&wa
def wc7 : W := ww|||wa
def wc8 : W := ww&&&~~~wa
def wc9 : W := wa&&&~~~ww
def wda : W := ww&&&wb
def wdb : W := ww|||wb
def wdc : W := ww&&&~~~wb
def wdd : W := wb&&&~~~ww
def wde : W := ww&&&wh
def wdf : W := ww|||wh
def wdg : W := ww&&&~~~wh
def wdh : W := wh&&&~~~ww
def wdi : W := wA&&&wd
def wdj : W := wA|||wd
def wdk : W := wA&&&~~~wd
def wdl : W := wd&&&~~~wA
def wdm : W := wA&&&wf
def wdn : W := wA|||wf
def wdo : W := wf&&&~~~wA
def wdp : W := wA|||wc
def wdq : W := wA&&&~~~wc
def wdr : W := wc&&&~~~wA
def wds : W := wA&&&wa
def wdt : W := wA|||wa
def wdu : W := wA&&&~~~wa
def wdv : W := wa&&&~~~wA
def wdw : W := wA|||wb
def wdx : W := wA&&&~~~wb
def wdy : W := wb&&&~~~wA
def wdz : W := wA&&&wg
def wdA : W := wA|||wg
def wdB : W := wA&&&~~~wg
def wdC : W := wg&&&~~~wA
def wdD : W := wz|||wd
def wdE : W := wz&&&~~~wd
def wdF : W := wd&&&~~~wz
def wdG : W := wz&&&wf
def wdH : W := wz|||wf
def wdI : W := wf&&&~~~wz
def wdJ : W := wz&&&wc
def wdK : W := wz|||wc
def wdL : W := wz&&&~~~wc
def wdM : W := wc&&&~~~wz
def wdN : W := wz&&&wa
def wdO : W := wz|||wa
def wdP : W := wz&&&~~~wa
def wdQ : W := wa&&&~~~wz
def wdR : W := wz|||wb
def wdS : W := wz&&&~~~wb
def wdT : W := wb&&&~~~wz
def wdU : W := wz&&&wh
def wdV : W := wz|||wh
def wdW : W := wh&&&~~~wz
def wdX : W := we|||wB
def wdY : W := we&&&~~~wB
def wdZ : W := wB&&&~~~we
def wd0 : W := wB|||wd
def wd1 : W := wB&&&~~~wd
def wd2 : W := wd&&&~~~wB
def wd3 : W := wB|||wc
def wd4 : W := wB&&&~~~wc
def wd5 : W := wc&&&~~~wB
def wd6 : W := wB&&&wa
def wd7 : W := wB|||wa
def wd8 : W := wB&&&~~~wa
def wd9 : W := wa&&&~~~wB
def wea : W := wB&&&wb
def web : W := wB|||wb
def wec : W := wB&&&~~~wb
def wed : W := wb&&&~~~wB
def wee : W := wB&&&wh
def wef : W := wB|||wh
def weg : W := wB&&&~~~wh
def weh : W := wh&&&~~~wB
def wei : W := we&&&wi
def wej : W := we|||wi
def wek : W := we&&&~~~wi
def wel : W := wi&&&~~~we
def wem : W := wi&&&wf
def wen : W := wi|||wf
def weo : W := wi&&&~~~wf
def wep : W := wf&&&~~~wi
def weq : W := wi|||wc
def wer : W := wi&&&~~~wc
def wes : W := wc&&&~~~wi
def wet : W := wi&&&wb
def weu : W := wi|||wb
def wev : W := wi&&&~~~wb
def wew : W := wb&&&~~~wi
def wex : W := wi&&&wg
def wey : W := wi|||wg
def wez : W := wg&&&~~~wi
def weA : W := wi&&&wh
def weB : W := wi|||wh
def weC : W := wi&&&~~~wh
def weD : W := wh&&&~~~wi
def weE : W := we&&&wk
def weF : W := we|||wk
def weG : W := we&&&~~~wk
def weH : W := wk&&&~~~we
def weI : W := wk|||wd
def weJ : W := wk&&&~~~wd
def weK : W := wd&&&~~~wk
def weL : W := wk|||wc
def weM : W := wk&&&~~~wc
def weN : W := wc&&&~~~wk
def weO : W := wk&&&wb
def weP : W := wk|||wb
def weQ : W := wk&&&~~~wb
def weR : W := wb&&&~~~wk
def weS : W := wk&&&wg
def weT : W := wk|||wg
def weU : W := wg&&&~~~wk
def weV : W := wk&&&wh
def weW : W := wk|||wh
def weX : W := wk&&&~~~wh
def weY : W := wh&&&~~~wk
def weZ : W := we|||wl
def we0 : W := we&&&~~~wl
def we1 : W := wl&&&~~~we
def we2 : W := wl|||wd
def we3 : W := wl&&&~~~wd
def we4 : W := wd&&&~~~wl
def we5 : W := wl|||wf
def we6 : W := wl&&&~~~wf
def we7 : W := wf&&&~~~wl
def we8 : W := wl|||wc
def we9 : W := wl&&&~~~wc
def wfa : W := wc&&&~~~wl
def wfb : W := wl&&&wb
def wfc : W := wl|||wb
def wfd : W := wl&&&~~~wb
def wfe : W := wb&&&~~~wl
def wff : W := wl&&&wg
def wfg : W := wl|||wg
def wfh : W := wl&&&~~~wg
def wfi : W := wg&&&~~~wl
def wfj : W := we|||wx
def wfk : W := we&&&~~~wx
def wfl : W := wx&&&~~~we
def wfm : W := wx&&&wf
def wfn : W := wx|||wf
def wfo : W := wx&&&~~~wf
def wfp : W := wf&&&~~~wx
def wfq : W := wx|||wc
def wfr : W := wx&&&~~~wc
def wfs : W := wc&&&~~~wx
def wft : W := wx|||wa
def wfu : W := wx&&&~~~wa
def wfv : W := wa&&&~~~wx
def wfw : W := wx&&&wb
def wfx : W := wx|||wb
def wfy : W := wx&&&~~~wb
def wfz : W := wb&&&~~~wx
def wfA : W := wx&&&wg
def wfB : W := wx|||wg
def wfC : W := wg&&&~~~wx
def wfD : W := wu&&&wf
def wfE : W := wu|||wf
def wfF : W := wu&&&~~~wf
def wfG : W := wf&&&~~~wu
def wfH : W := wu&&&wc
def wfI : W := wu|||wc
def wfJ : W := wu&&&~~~wc
def wfK : W := wc&&&~~~wu
def wfL : W := wu&&&wa
def wfM : W := wu|||wa
def wfN : W := wu&&&~~~wa
def wfO : W := wa&&&~~~wu
def wfP : W := wu&&&wb
def wfQ : W := wu|||wb
def wfR : W := wu&&&~~~wb
def wfS : W := wb&&&~~~wu
def wfT : W := wu&&&wg
def wfU : W := wu|||wg
def wfV : W := wu&&&~~~wg
def wfW : W := wg&&&~~~wu
def wfX : W := wu&&&wh
def wfY : W := wu|||wh
def wfZ : W := wu&&&~~~wh
def wf0 : W := wh&&&~~~wu
def wf1 : W := we&&&wv
def wf2 : W := wv&&&~~~we
def wf3 : W := wv&&&wc
def wf4 : W := wv|||wc
def wf5 : W := wv&&&~~~wc
def wf6 : W := wc&&&~~~wv
def wf7 : W := wv&&&wa
def wf8 : W := wv|||wa
def wf9 : W := wv&&&~~~wa
def wga : W := wa&&&~~~wv
def wgb : W := wv&&&wb
def wgc : W := wv|||wb
def wgd : W := wv&&&~~~wb
def wge : W := wb&&&~~~wv
def wgf : W := wv&&&wg
def wgg : W := wv|||wg
def wgh : W := wv&&&~~~wg
def wgi : W := wg&&&~~~wv
def wgj : W := wv&&&wh
def wgk : W := wv|||wh
def wgl : W := wv&&&~~~wh
def wgm : W := wh&&&~~~wv
def wgn : W := wd&&&wr
def wgo : W := wd&&&~~~wr
def wgp : W := wr&&&~~~wd
def wgq : W := wf&&&wr
def wgr : W := wf|||wr
def wgs : W := wf&&&~~~wr
def wgt : W := wr&&&~~~wf
def wgu : W := wr&&&wa
def wgv : W := wr|||wa
def wgw : W := wr&&&~~~wa
def wgx : W := wa&&&~~~wr
def wgy : W := wr&&&wb
def wgz : W := wr|||wb
def wgA : W := wr&&&~~~wb
def wgB : W := wb&&&~~~wr
def wgC : W := wr&&&wg
def wgD : W := wr|||wg
def wgE : W := wr&&&~~~wg
def wgF : W := wg&&&~~~wr
def wgG : W := wr&&&wh
def wgH : W := wr|||wh
def wgI : W := wr&&&~~~wh
def wgJ : W := wh&&&~~~wr
def wgK : W := we&&&wq
def wgL : W := we&&&~~~wq
def wgM : W := wq&&&~~~we
def wgN : W := wf&&&wq
def wgO : W := wf&&&~~~wq
def wgP : W := wq&&&~~~wf
def wgQ : W := wq&&&wa
def wgR : W := wq|||wa
def wgS : W := wq&&&~~~wa
def wgT : W := wa&&&~~~wq
def wgU : W := wq&&&wb
def wgV : W := wq|||wb
def wgW : W := wq&&&~~~wb
def wgX : W := wb&&&~~~wq
def wgY : W := wq&&&wg
def wgZ : W := wq|||wg
def wg0 : W := wq&&&~~~wg
def wg1 : W := wg&&&~~~wq
def wg2 : W := wq&&&wh
def wg3 : W := wq|||wh
def wg4 : W := wq&&&~~~wh
def wg5 : W := wh&&&~~~wq
def wg6 : W := we&&&wj
def wg7 : W := we&&&~~~wj
def wg8 : W := wj&&&~~~we
def wg9 : W := wf&&&wj
def wha : W := wf&&&~~~wj
def whb : W := wj&&&~~~wf
def whc : W := wc&&&wj
def whd : W := wc&&&~~~wj
def whe : W := wj&&&~~~wc
def whf : W := wj&&&wb
def whg : W := wj|||wb
def whh : W := wj&&&~~~wb
def whi : W := wb&&&~~~wj
def whj : W := wj&&&wg
def whk : W := wj|||wg
def whl : W := wj&&&~~~wg
def whm : W := wg&&&~~~wj
def whn : W := wj&&&wh
def who : W := wj|||wh
def whp : W := wj&&&~~~wh
def whq : W := wh&&&~~~wj
def whr : W := we&&&wn
def whs : W := we&&&~~~wn
def wht : W := wn&&&~~~we
def whu : W := wd&&&wn
def whv : W := wd&&&~~~wn
def whw : W := wn&&&~~~wd
def whx : W := wf&&&wn
def why : W := wf|||wn
def whz : W := wf&&&~~~wn
def whA : W := wn&&&~~~wf
def whB : W := wa&&&wn
def whC : W := wa|||wn
def whD : W := wa&&&~~~wn
def whE : W := wn&&&~~~wa
def whF : W := wn&&&wg
def whG : W := wn|||wg
def whH : W := wn&&&~~~wg
def whI : W := wg&&&~~~wn
def whJ : W := wn&&&wh
def whK : W := wn|||wh
def whL : W := wn&&&~~~wh
def whM : W := wh&&&~~~wn
def whN : W := we&&&~~~wbF
def whO : W := wbF|||wd
def whP : W := wd&&&~~~wbF
def whQ : W := wbF|||wf
def whR : W := wbF|||wc
def whS : W := wb&&&~~~wbF
def whT : W := wbF|||wg
def whU : W := wbF|||wh
def whV : W := wa7|||wd
def whW : W := wd&&&~~~wa7
def whX : W := wa7|||wf
def whY : W := wf&&&~~~wa7
def whZ : W := wa7|||wa
def wh0 : W := wa7|||wg
def wh1 : W := wa7|||wh
def wh2 : W := wbe|||we
def wh3 : W := we&&&~~~wbe
def wh4 : W := wbe|||wd
def wh5 : W := wc&&&~~~wbe
def wh6 : W := wbe|||wa
def wh7 : W := wa&&&~~~wbe
def wh8 : W := wbe|||wg
def wh9 : W := wbe|||wh
def wia : W := we&&&~~~wby
def wib : W := wby|||wd
def wic : W := wd&&&~~~wby
def wid : W := wby|||wc
def wie : W := wc&&&~~~wby
def wif : W := wby|||wa
def wig : W := wby|||wg
def wih : W := wby|||wh
def wii : W := wC|||wf
def wij : W := wf&&&~~~wC
def wik : W := wC|||wa
def wil : W := wC|||wb
def wim : W := wb&&&~~~wC
def win : W := wC|||wg
def wio : W := wC|||wh
def wip : W := wR|||we
def wiq : W := we&&&~~~wR
def wir : W := wR|||wf
def wis : W := wR|||wa
def wit : W := wR|||wg
def wiu : W := wg&&&~~~wR
def wiv : W := wR|||wh
def wiw : W := wbs|||we
def wix : W := wbs|||wd
def wiy : W := wbs|||wf
def wiz : W := wbs|||wa
def wiA : W := wa&&&~~~wbs
def wiB : W := wbs|||wg
def wiC : W := wg&&&~~~wbs
def wiD : W := wet|||we
def wiE : W := we&&&~~~wet
def wiF : W := wd&&&~~~wet
def wiG : W := wet|||wf
def wiH : W := wf&&&~~~wet
def wiI : W := wet|||wc
def wiJ : W := wet|||wg
def wiK : W := wg&&&~~~wet
def wiL : W := wet|||wh
def wiM : W := weO|||we
def wiN : W := weO|||wd
def wiO : W := wd&&&~~~weO
def wiP : W := wf&&&~~~weO
def wiQ : W := weO|||wc
def wiR : W := wc&&&~~~weO
def wiS : W := wa&&&~~~weO
def wiT : W := weO|||wg
def wiU : W := wg&&&~~~weO
def wiV : W := weO|||wh
def wiW : W := wfb|||we
def wiX : W := wfb|||wd
def wiY : W := wfb|||wf
def wiZ : W := wfb|||wc
def wi0 : W := wc&&&~~~wfb
def wi1 : W := wfb|||wg
def wi2 : W := wg&&&~~~wfb
def wi3 : W := wfb|||wh
def wi4 : W := wI|||we
def wi5 : W := we&&&~~~wI
def wi6 : W := wI|||wa
def wi7 : W := wa&&&~~~wI
def wi8 : W := wI|||wb
def wi9 : W := wI|||wg
def wja : W := wg&&&~~~wI
def wjb : W := wI|||wh
def wjc : W := wV|||we
def wjd : W := wd&&&~~~wV
def wje : W := wV|||wf
def wjf : W := wf&&&~~~wV
def wjg : W := wV|||wa
def wjh : W := wa&&&~~~wV
def wji : W := wV|||wb
def wjj : W := wb&&&~~~wV
def wjk : W := wV|||wh
def wjl : W := w1|||we
def wjm : W := w1|||wf
def wjn : W := w1|||wa
def wjo : W := wa&&&~~~w1
def wjp : W := w1|||wb
def wjq : W := w1|||wg
def wjr : W := wcs|||we
def wjs : W := we&&&~~~wcs
def wjt : W := wcs|||wd
def wju : W := wd&&&~~~wcs
def wjv : W := wf&&&~~~wcs
def wjw : W := wcs|||wa
def wjx : W := wa&&&~~~wcs
def wjy : W := wcs|||wb
def wjz : W := wcs|||wh
def wjA : W := wcR|||we
def wjB : W := we&&&~~~wcR
def wjC : W := wcR|||wd
def wjD : W := wcR|||wf
def wjE : W := wcR|||wa
def wjF : W := wa&&&~~~wcR
def wjG : W := wcR|||wb
def wjH : W := wb&&&~~~wcR
def wjI : W := wcR|||wh
def wjJ : W := wd&&&~~~wei
def wjK : W := wei|||wf
def wjL : W := wf&&&~~~wei
def wjM : W := wei|||wc
def wjN : W := wei|||wb
def wjO : W := wb&&&~~~wei
def wjP : W := wei|||wg
def wjQ : W := wg&&&~~~wei
def wjR : W := wei|||wh
def wjS : W := weE|||wd
def wjT : W := wd&&&~~~weE
def wjU : W := wf&&&~~~weE
def wjV : W := weE|||wc
def wjW : W := wc&&&~~~weE
def wjX : W := weE|||wb
def wjY : W := weE|||wg
def wjZ : W := wg&&&~~~weE
def wj0 : W := weE|||wh
def wj1 : W := wds|||wd
def wj2 : W := wds|||wf
def wj3 : W := wds|||wc
def wj4 : W := wc&&&~~~wds
def wj5 : W := wds|||wb
def wj6 : W := wds|||wg
def wj7 : W := wg&&&~~~wds
def wj8 : W := wds|||wh
def wj9 : W := wdz|||wd
def wka : W := wd&&&~~~wdz
def wkb : W := wdz|||wf
def wkc : W := wf&&&~~~wdz
def wkd : W := wdz|||wc
def wke : W := wc&&&~~~wdz
def wkf : W := wdz|||wa
def wkg : W := wa&&&~~~wdz
def wkh : W := wdz|||wb
def wki : W := wb&&&~~~wdz
def wkj : W := wdz|||wh
def wkk : W := wea|||we
def wkl : W := wea|||wd
def wkm : W := wd&&&~~~wea
def wkn : W := wea|||wc
def wko : W := wea|||wa
def wkp : W := wa&&&~~~wea
def wkq : W := wea|||wg
def wkr : W := wea|||wh
def wks : W := wh&&&~~~wea
def wkt : W := wP|||we
def wku : W := wP|||wf
def wkv : W := wf&&&~~~wP
def wkw : W := wP|||wb
def wkx : W := wP|||wg
def wky : W := wg&&&~~~wP
def wkz : W := wP|||wh
def wkA : W := wh&&&~~~wP
def wkB : W := wbi|||we
def wkC : W := wbi|||wd
def wkD : W := wbi|||wf
def wkE : W := wf&&&~~~wbi
def wkF : W := wc&&&~~~wbi
def wkG : W := wbi|||wg
def wkH : W := wbi|||wh
def wkI : W := wh&&&~~~wbi
def wkJ : W := wbo|||we
def wkK : W := wbo|||wd
def wkL : W := wd&&&~~~wbo
def wkM : W := wbo|||wf
def wkN : W := wbo|||wa
def wkO : W := wbo|||wh
def wkP : W := wh&&&~~~wbo
def wkQ : W := wN|||we
def wkR : W := wN|||wf
def wkS : W := wf&&&~~~wN
def wkT : W := wN|||wb
def wkU : W := wN|||wg
def wkV : W := wg&&&~~~wN
def wkW : W := wN|||wh
def wkX : W := wh&&&~~~wN
def wkY : W := wZ|||we
def wkZ : W := wZ|||wf
def wk0 : W := wc&&&~~~wZ
def wk1 : W := wZ|||wa
def wk2 : W := wa&&&~~~wZ
def wk3 : W := wZ|||wb
def wk4 : W := wZ|||wg
def wk5 : W := wX|||we
def wk6 : W := wX|||wf
def wk7 : W := wf&&&~~~wX
def wk8 : W := wX|||wa
def wk9 : W := wa&&&~~~wX
def wla : W := wX|||wb
def wlb : W := wb&&&~~~wX
def wlc : W := wX|||wh
def wld : W := wK|||we
def wle : W := we&&&~~~wK
def wlf : W := wK|||wa
def wlg : W := wa&&&~~~wK
def wlh : W := wK|||wb
def wli : W := wK|||wg
def wlj : W := wg&&&~~~wK
def wlk : W := wK|||wh
def wll : W := wT|||we
def wlm : W := we&&&~~~wT
def wln : W := wT|||wf
def wlo : W := wT|||wa
def wlp : W := wT|||wg
def wlq : W := wg&&&~~~wT
def wlr : W := wT|||wh
def wls : W := wE|||wf
def wlt : W := wf&&&~~~wE
def wlu : W := wE|||wa
def wlv : W := wE|||wb
def wlw : W := wb&&&~~~wE
def wlx : W := wE|||wg
def wly : W := wE|||wh
def wlz : W := wp|||way
def wlA : W := way|||we
def wlB : W := we&&&~~~way
def wlC : W := way|||wf
def wlD : W := wf&&&~~~way
def wlE : W := way|||wc
def wlF : W := way|||wa
def wlG : W := wa&&&~~~way
def wlH : W := way|||wb
def wlI : W := wb&&&~~~way
def wlJ : W := way|||wg
def wlK : W := wg&&&~~~way
def wlL : W := wd&&&~~~wF
def wlM : W := wp|||wao
def wlN : W := wao|||wc
def wlO : W := wg&&&~~~wao
def wlP : W := wh&&&~~~wao
def wlQ : W := w5|||wc
def wlR : W := w5|||wg
def wlS : W := wg&&&~~~w5
def wlT : W := wh&&&~~~w5
def wlU : W := wg&&&~~~wH
def wlV : W := we&&&~~~wM
def wlW : W := wf&&&~~~wM
def wlX : W := wh&&&~~~wM
def wlY : W := wc&&&wW
def wlZ : W := wc&&&wS
def wl0 : W := wd&&&wO
def wl1 : W := wq&&&~~~wp
def wl2 : W := wd&&&wJ
def wl3 : W := wde|||we
def wl4 : W := wde|||wf
def wl5 : W := wf&&&~~~wde
def wl6 : W := wde|||wc
def wl7 : W := wde|||wa
def wl8 : W := wa&&&~~~wde
def wl9 : W := wde|||wb
def wma : W := wb&&&~~~wde
def wmb : W := wdN|||wd
def wmc : W := wd&&&~~~wdN
def wmd : W := wdN|||wf
def wme : W := wf&&&~~~wdN
def wmf : W := wdN|||wc
def wmg : W := wc&&&~~~wdN
def wmh : W := wdN|||wb
def wmi : W := wdN|||wg
def wmj : W := wdN|||wh
def wmk : W := wh&&&~~~wdN
def wml : W := wdU|||wd
def wmm : W := wd&&&~~~wdU
def wmn : W := wdU|||wf
def wmo : W := wf&&&~~~wdU
def wmp : W := wdU|||wc
def wmq : W := wc&&&~~~wdU
def wmr : W := wdU|||wa
def wms : W := wa&&&~~~wdU
def wmt : W := wdU|||wb
def wmu : W := wb&&&~~~wdU
def wmv : W := wdU|||wg
def wmw : W := wcw|||we
def wmx : W := we&&&~~~wcw
def wmy : W := wcw|||wd
def wmz : W := wc&&&~~~wcw
def wmA : W := wcw|||wa
def wmB : W := wa&&&~~~wcw
def wmC : W := wcw|||wb
def wmD : W := wcw|||wg
def wmE : W := wee|||we
def wmF : W := we&&&~~~wee
def wmG : W := wee|||wd
def wmH : W := wd&&&~~~wee
def wmI : W := wee|||wc
def wmJ : W := wee|||wa
def wmK : W := wa&&&~~~wee
def wmL : W := wee|||wb
def wmM : W := wb&&&~~~wee
def wmN : W := wee|||wg
def wmO : W := weA|||we
def wmP : W := weA|||wf
def wmQ : W := wf&&&~~~weA
def wmR : W := weA|||wc
def wmS : W := wc&&&~~~weA
def wmT : W := weA|||wb
def wmU : W := weA|||wg
def wmV : W := wg&&&~~~weA
def wmW : W := wbZ|||wd
def wmX : W := wd&&&~~~wbZ
def wmY : W := wbZ|||wf
def wmZ : W := wbZ|||wc
def wm0 : W := wc&&&~~~wbZ
def wm1 : W := wbZ|||wb
def wm2 : W := wbZ|||wg
def wm3 : W := wg&&&~~~wbZ
def wm4 : W := wbZ|||wh
def wm5 : W := wh&&&~~~wbZ
def wm6 : W := weV|||we
def wm7 : W := weV|||wd
def wm8 : W := wd&&&~~~weV
def wm9 : W := weV|||wc
def wna : W := wc&&&~~~weV
def wnb : W := wa&&&~~~weV
def wnc : W := weV|||wb
def wnd : W := weV|||wg
def wne : W := wg&&&~~~weV
def wnf : W := waZ|||we
def wng : W := waZ|||wl
def wnh : W := waZ|||wd
def wni : W := waZ|||wf
def wnj : W := waZ|||wc
def wnk : W := wh&&&~~~waZ
def wnl : W := wbm|||we
def wnm : W := wbm|||wd
def wnn : W := wd&&&~~~wbm
def wno : W := wbm|||wf
def wnp : W := wbm|||wa
def wnq : W := wb&&&~~~wbm
def wnr : W := wbm|||wh
def wns : W := wh&&&~~~wbm
def wnt : W := wbk|||we
def wnu : W := wbk|||wd
def wnv : W := wbk|||wf
def wnw : W := wf&&&~~~wbk
def wnx : W := wbk|||wg
def wny : W := wbk|||wh
def wnz : W := wh&&&~~~wbk
def wnA : W := wbq|||we
def wnB : W := wbq|||wd
def wnC : W := wbq|||wf
def wnD : W := wbq|||wa
def wnE : W := wa&&&~~~wbq
def wnF : W := wbq|||wg
def wnG : W := wg&&&~~~wbq
def wnH : W := wbc|||we
def wnI : W := we&&&~~~wbc
def wnJ : W := wbc|||wf
def wnK : W := wbc|||wa
def wnL : W := wbc|||wg
def wnM : W := wg&&&~~~wbc
def wnN : W := wbc|||wh
def wnO : W := wbg|||we
def wnP : W := we&&&~~~wbg
def wnQ : W := wbg|||wd
def wnR : W := wbg|||wa
def wnS : W := wa&&&~~~wbg
def wnT : W := wbg|||wg
def wnU : W := wbg|||wh
def wnV : W := wa9|||wd
def wnW : W := wd&&&~~~wa9
def wnX : W := wa9|||wf
def wnY : W := wf&&&~~~wa9
def wnZ : W := wa9|||wa
def wn0 : W := wa9|||wg
def wn1 : W := wa9|||wh
def wn2 : W := wc&&&wbn
def wn3 : W := wn&&&~~~wm
def wn4 : W := wbj&&&wb
def wn5 : W := wbf&&&wb
def wn6 : W := wa8&&&wc
def wn7 : W := waT|||we
def wn8 : W := waT|||wd
def wn9 : W := waT|||wb
def woa : W := way|||ww
def wob : W := wbJ|||wd
def woc : W := wd&&&~~~wbJ
def wod : W := wbJ|||wf
def woe : W := wbJ|||wc
def wof : W := wbJ|||wa
def wog : W := wb&&&~~~wbJ
def woh : W := wbJ|||wh
def woi : W := wh&&&~~~wbJ
def woj : W := wbN|||wd
def wok : W := wd&&&~~~wbN
def wol : W := wbN|||wf
def wom : W := wbN|||wc
def won : W := wbN|||wa
def woo : W := wb&&&~~~wbN
def wop : W := wbN|||wg
def woq : W := wg&&&~~~wbN
def wor : W := wb6|||wd
def wos : W := wd&&&~~~wb6
def wot : W := wb6|||wf
def wou : W := wb6|||wc
def wov : W := wc&&&~~~wb6
def wow : W := wb6|||wa
def wox : W := wa&&&~~~wb6
def woy : W := wb6|||wb
def woz : W := wb6|||wh
def woA : W := wh&&&~~~wb6
def woB : W := wah|||wd
def woC : W := wah|||wc
def woD : W := wah|||wa
def woE : W := wa&&&~~~wah
def woF : W := wah|||wb
def woG : W := wca|||wd
def woH : W := wd&&&~~~wca
def woI : W := wca|||wf
def woJ : W := wca|||wc
def woK : W := wc&&&~~~wca
def woL : W := wca|||wa
def woM : W := wa&&&~~~wca
def woN : W := wca|||wb
def woO : W := wca|||wg
def woP : W := wg&&&~~~wca
def woQ : W := wak|||wd
def woR : W := wak|||wc
def woS : W := wak|||wa
def woT : W := wak|||wb
def woU : W := wgC|||wd
def woV : W := wd&&&~~~wgC
def woW : W := wgC|||wf
def woX : W := wf&&&~~~wgC
def woY : W := wgC|||wa
def woZ : W := wa&&&~~~wgC
def wo0 : W := wgC|||wb
def wo1 : W := wb&&&~~~wgC
def wo2 : W := wgC|||wh
def wo3 : W := wh&&&~~~wgC
def wo4 : W := wfX|||wf
def wo5 : W := wf&&&~~~wfX
def wo6 : W := wfX|||wc
def wo7 : W := wc&&&~~~wfX
def wo8 : W := wfX|||wa
def wo9 : W := wa&&&~~~wfX
def wpa : W := wfX|||wb
def wpb : W := wb&&&~~~wfX
def wpc : W := wfX|||wg
def wpd : W := wg&&&~~~wfX
def wpe : W := waH|||wd
def wpf : W := wd&&&~~~waH
def wpg : W := waH|||wc
def wph : W := waH|||wa
def wpi : W := waH|||wh
def wpj : W := wgj|||we
def wpk : W := we&&&~~~wgj
def wpl : W := wgj|||wd
def wpm : W := wgj|||wc
def wpn : W := wc&&&~~~wgj
def wpo : W := wgj|||wa
def wpp : W := wa&&&~~~wgj
def wpq : W := wgj|||wb
def wpr : W := wb&&&~~~wgj
def wps : W := wgj|||wg
def wpt : W := wg&&&~~~wgj
def wpu : W := wbV|||wf
def wpv : W := wb4|||wf
def wpw : W := wda|||we
def wpx : W := we&&&~~~wda
def wpy : W := wbP|||wd
def wpz : W := wd&&&~~~wbP
def wpA : W := wbL|||wd
def wpB : W := wd&&&~~~wbL
def wpC : W := wbA|||wd
def wpD : W := wd&&&~~~wbA
def wpE : W := wbD|||wd
def wpF : W := wd&&&~~~wbD
def wpG : W := wbH|||wd
def wpH : W := wd&&&~~~wbH
def wpI : W := wf&&&~~~waf
def wpJ : W := wag|||wg
def wpK : W := wg&&&~~~wag
def wpL : W := wae&&&~~~wo
def wpM : W := wa&&&wae
def wpN : W := wae&&&~~~wa
def wpO : W := we&&&wbv
def wpP : W := wgy|||wd
def wpQ : W := wd&&&~~~wgy
def wpR : W := wbR|||wb
def wpS : W := wb&&&~~~wbR
def wpT : W := wbX|||wd
def wpU : W := wd&&&~~~wbX
def wpV : W := wbX|||wb
def wpW : W := wb&&&~~~wbX
def wpX : W := wy|||w8
def wpY : W := w8|||wa
def wpZ : W := wa&&&~~~w8
def wp0 : W := wg&&&~~~w8
def wp1 : W := wd&&&wal
def wp2 : W := wcK|||wf
def wp3 : W := wf&&&~~~wcK
def wp4 : W := wcg|||wa
def wp5 : W := wa&&&~~~wcg
def wp6 : W := wcC|||wf
def wp7 : W := wf&&&~~~wcC
def wp8 : W := wcC|||wa
def wp9 : W := wa&&&~~~wcC
def wqa : W := wc6|||wf
def wqb : W := wf&&&~~~wc6
def wqc : W := wfh|||wf
def wqd : W := wf&&&~~~wfh
def wqe : W := wdZ|||wa
def wqf : W := wa&&&~~~wdZ
def wqg : W := wgL|||wd
def wqh : W := wf&&&~~~wce
def wqi : W := wcA|||wf
def wqj : W := wf&&&~~~wcA
def wqk : W := wdJ|||wf
def wql : W := wf&&&~~~wdJ
def wqm : W := wdJ|||wg
def wqn : W := wr&&&~~~w9
def wqo : W := wfH|||wf
def wqp : W := wf&&&~~~wfH
def wqq : W := wcn|||we
def wqr : W := we&&&~~~wcn
def wqs : W := wcM|||we
def wqt : W := we&&&~~~wcM
def wqu : W := wcM|||wf
def wqv : W := wf&&&~~~wcM
def wqw : W := wd|||waC
def wqx : W := wg&&&~~~waC
def wqy : W := wh&&&~~~waD
def wqz : W := waB&&&~~~ws
def wqA : W := wcT|||wf
def wqB : W := wf&&&~~~wcT
def wqC : W := wcF|||wf
def wqD : W := wf&&&~~~wcF
def wqE : W := wcP|||wf
def wqF : W := wf&&&~~~wcP
def wqG : W := wd|||wcJ
def wqH : W := waW|||wa
def wqI : W := wa&&&~~~waW
def wqJ : W := wab|||wa
def wqK : W := wa&&&~~~wab
def wqL : W := wh&&&~~~wab
def wqM : W := wt|||waY
def wqN : W := wg|||waY
def wqO : W := wg&&&~~~waY
def wqP : W := we&&&waX
def wqQ : W := waX&&&~~~wd
def wqR : W := we&&&~~~wdk
def wqS : W := we&&&~~~wdE
def wqT : W := wh&&&~~~w4
def wqU : W := wf&&&~~~wd1
def wqV : W := wd1|||wc
def wqW : W := wc&&&~~~wd1
def wqX : W := wdi|||wh
def wqY : W := wu&&&~~~w3
def wqZ : W := wg6|||wd
def wq0 : W := wc8|||we
def wq1 : W := we&&&~~~wc8
def wq2 : W := wdc|||wf
def wq3 : W := wf&&&~~~wdc
def wq4 : W := ww|||wao
def wq5 : W := ww|||wax
def wq6 : W := waw&&&~~~we
def wq7 : W := whs|||wd
def wq8 : W := wd&&&~~~whs
def wq9 : W := whs|||wf
def wra : W := wf&&&~~~whs
def wrb : W := wdq|||wd
def wrc : W := wd&&&~~~wdq
def wrd : W := we&&&~~~wdL
def wre : W := wdL|||wd
def wrf : W := wd&&&~~~wdL
def wrg : W := wg&&&~~~waa
def wrh : W := wcD|||wd
def wri : W := wd4|||wd
def wrj : W := wd&&&~~~wd4
def wrk : W := wdx|||wf
def wrl : W := wf&&&~~~wdx
def wrm : W := wdS|||wf
def wrn : W := wf&&&~~~wdS
def wro : W := wA|||wam
def wrp : W := we|||waV
def wrq : W := wz|||waj
def wrr : W := wc&&&wai
def wrs : W := wa4&&&~~~we
def wrt : W := we|||wd8
def wru : W := we&&&~~~wd8
def wrv : W := wd|||waJ
def wrw : W := waJ|||wa
def wrx : W := wa&&&~~~waJ
def wry : W := wB|||waL
def wrz : W := weo|||wg
def wrA : W := wg&&&~~~weo
def wrB : W := wd&&&~~~wfw
def wrC : W := wd&&&~~~wfo
def wrD : W := wao|||wx
def wrE : W := we3|||wf
def wrF : W := wf&&&~~~we3
def wrG : W := wfG|||wa
def wrH : W := wa&&&~~~wfG
def wrI : W := wd&&&~~~wfu
def wrJ : W := wem|||wg
def wrK : W := wg&&&~~~wem
def wrL : W := wex|||wf
def wrM : W := wf&&&~~~wex
def wrN : W := weC|||wf
def wrO : W := wf&&&~~~weC
def wrP : W := weC|||wg
def wrQ : W := wg&&&~~~weC
def wrR : W := wer|||wf
def wrS : W := wf&&&~~~wer
def wrT : W := wer|||wg
def wrU : W := wg&&&~~~wer
def wrV : W := wel|||wf
def wrW : W := wf&&&~~~wel
def wrX : W := wel|||wg
def wrY : W := wg&&&~~~wel
def wrZ : W := wev|||wf
def wr0 : W := wf&&&~~~wev
def wr1 : W := wev|||wg
def wr2 : W := wg&&&~~~wev
def wr3 : W := wh&&&~~~war
def wr4 : W := wj&&&~~~wi
def wr5 : W := wd&&&wen
def wr6 : W := wfL|||wf
def wr7 : W := wf&&&~~~wfL
def wr8 : W := wfL|||wg
def wr9 : W := wg&&&~~~wfL
def wsa : W := weS|||wd
def wsb : W := wd&&&~~~weS
def wsc : W := weM|||wd
def wsd : W := wd&&&~~~weM
def wse : W := weM|||wg
def wsf : W := wg&&&~~~weM
def wsg : W := wh&&&~~~waG
def wsh : W := waE&&&~~~wk
def wsi : W := wff|||wd
def wsj : W := wd&&&~~~wff
def wsk : W := wff|||wf
def wsl : W := wf&&&~~~wff
def wsm : W := we9|||wd
def wsn : W := wd&&&~~~we9
def wso : W := we9|||wf
def wsp : W := wf&&&~~~we9
def wsq : W := we9|||wg
def wsr : W := wg&&&~~~we9
def wss : W := we1|||wf
def wst : W := wf&&&~~~we1
def wsu : W := wfd|||wf
def wsv : W := wf&&&~~~wfd
def wsw : W := wh&&&~~~waQ
def wsx : W := wh&&&~~~wad
def wsy : W := wl|||wa3
def wsz : W := we&&&waO
def wsA : W := wfm|||wh
def wsB : W := wv&&&~~~wan
def wsC : W := wfy|||wf
def wsD : W := wf&&&~~~wfy
def wsE : W := whv|||wf
def wsF : W := wf&&&~~~whv
def wsG : W := wat|||wf
def wsH : W := wf&&&~~~wat
def wsI : W := wfR|||wf
def wsJ : W := wf&&&~~~wfR
def wsK : W := wfl|||wg
def wsL : W := wg&&&~~~wfl
def wsM : W := wgo|||wg
def wsN : W := wg&&&~~~wgo
def wsO : W := wdl|||wg
def wsP : W := wx|||waA
def wsQ : W := wf&&&waz
def wsR : W := wd|||wgs
def wsS : W := wd&&&~~~wgs
def wsT : W := wgs|||wa
def wsU : W := wa&&&~~~wgs
def wsV : W := wgs|||wg
def wsW : W := wg&&&~~~wgs
def wsX : W := wdo|||wa
def wsY : W := wdI|||wa
def wsZ : W := wa&&&~~~wdI
def ws0 : W := wd|||whz
def ws1 : W := wd&&&~~~whz
def ws2 : W := wfE&&&wh
def ws3 : W := wfE&&&~~~wh
def ws4 : W := wgu|||wc
def ws5 : W := wg2|||wa
def ws6 : W := wa&&&~~~wg2
def ws7 : W := wgG|||wa
def ws8 : W := wa&&&~~~wgG
def ws9 : W := wfK|||wa
def wta : W := wa&&&~~~wfK
def wtb : W := wdM|||wa
def wtc : W := wdr|||wa
def wtd : W := wa&&&~~~wdr
def wte : W := wdp&&&wg
def wtf : W := wdp&&&~~~wg
def wtg : W := wfI&&&wg
def wth : W := wfI&&&~~~wg
def wti : W := wgr&&&wg
def wtj : W := wgr&&&~~~wg
def wtk : W := wgT|||wg
def wtl : W := wg&&&~~~wgT
def wtm : W := whD|||wg
def wtn : W := wg&&&~~~whD
def wto : W := wgx|||wg
def wtp : W := wg&&&~~~wgx
def wtq : W := wga|||wh
def wtr : W := wh&&&~~~wga
def wts : W := wgv&&&wg
def wtt : W := wgv&&&~~~wg
def wtu : W := wa|||whI
def wtv : W := wa&&&~~~whI
def wtw : W := wa|||whM
def wtx : W := wa&&&~~~whM
def wty : W := whM|||wg
def wtz : W := wg&&&~~~whM
def wtA : W := wfS|||wg
def wtB : W := wg&&&~~~wfS
def wtC : W := wfS|||wh
def wtD : W := wh&&&~~~wfS
def wtE : W := wgB|||wg
def wtF : W := wg&&&~~~wgB
def wtG : W := wb5|||wg
def wtH : W := wdy|||wg
def wtI : W := wg&&&~~~wdy
def wtJ : W := wa&&&wdw
def wtK : W := wdw&&&~~~wa
def wtL : W := wa&&&wdR
def wtM : W := wdR&&&~~~wa
def wtN : W := wa&&&weu
def wtO : W := wa&&&wfQ
def wtP : W := wfQ&&&~~~wa
def wtQ : W := wa&&&wgz
def wtR : W := wgz&&&~~~wa
def wtS : W := wgz&&&wg
def wtT : W := wgz&&&~~~wg
def wtU : W := wgi|||wh
def wtV : W := wh&&&~~~wgi
def wtW : W := wg|||wgJ
def wtX : W := wg&&&~~~wgJ
def wtY : W := wg|||wg5
def wtZ : W := wg&&&~~~wg5
def wt0 : W := wd&&&wgH
def wt1 : W := wgH&&&~~~wd
def wt2 : W := wg&&&wgH
def wt3 : W := wgH&&&~~~wg
def wt4 : W := wd&&&whK
def wt5 : W := whK&&&~~~wd
def wt6 : W := wf&&&whK
def wt7 : W := whK&&&~~~wf
def wt8 : W := wf&&&was
def wt9 : W := wd&&&~~~waI
def wua : W := wp|||wlC
def wub : W := wp|||wlA
def wuc : W := wae&&&~~~wbH
def wud : W := wy|||wdo
def wue : W := wr&&&~~~wdJ
def wuf : W := waB&&&~~~wcq
def wug : W := wt|||wlX
def wuh : W := w4|||wdl
def wui : W := ww|||wlU
def wuj : W := wao|||wfp
def wuk : W := waE&&&~~~weQ
def wul : W := wl|||wsx
def tree5 : BinaryTree (List W) := .nil
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem closed5 : Closed 5 tree5 := closedEmpty 5
def tree6aaa : BinaryTree (List W) := (.node [we,we7,wd,wc,wb,wsy,wg] (.node [wba,wd,wf,wa,wn3,wg,wh] (.node [wgC,wd,wf,wqn,wa,wb,wh] (.node [wpM,wd,wf,wc,wpL,wg,wh] .nil .nil) (.node [wF,wf,wl1,wa,wb,wg,wh] .nil .nil)) (.node [we,wuj,wc,wa,wb,wg,wh] (.node [we,wsB,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wbh,wa,wn3,wg,wh] (.node [we,wbd,wf,wa,wn3,wg,wh] (.node [we,wep,wc,wr4,wb,wg,wh] .nil .nil) (.node [we,wd,wcJ,wa,wb,wg,wqM] .nil .nil)) (.node [we,wd,wf,wc,wa,wo0,wo2] (.node [we,wd,wf,wqO,wa,wb,wqM] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6aaa : everyKey (certRow 5 tree5) tree6aaa = true := by decide +kernel
def tree6aab : BinaryTree (List W) := (.node [we,wd,wf,wa,wb,wqM,wqN] (.node [we,wd,wf,wbl,wn3,wg,wh] (.node [we,wd,wf,wc,wb,wul,wg] (.node [we,wd,wf,wc,wb,wsy,wg] .nil .nil) (.node [we,wd,wf,woC,wa,wo0,wh] .nil .nil)) (.node [we,wd,wf,wa,wb,wg,wug] (.node [we,wd,wf,wa,wb,wg,wqM] .nil .nil) .nil)) (.node [we,wd,wf,wa,wn3,wg,wbr] (.node [we,wd,wf,wa,wn3,wg,wbt] (.node [we,wd,wf,wa,wn3,wbp,wh] .nil .nil) (.node [we,wd,wf,wa,wn3,wg,wh] .nil .nil)) (.node [we,wd,wf,wbj,wn3,wg,wh] (.node [we,wd,wf,wa,wn3,wbn,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6aab : everyKey (certRow 5 tree5) tree6aab = true := by decide +kernel
def tree6aa : BinaryTree (List W) := .node [we,wd,wf,wc,woY,wo0,wh] tree6aaa tree6aab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6aa : everyKey (certRow 5 tree5) tree6aa = true := splitCheck (by decide +kernel) ok_tree6aaa ok_tree6aab
def tree6aba : BinaryTree (List W) := (.node [we,wd,we5,wc,wb,wsy,wg] (.node [we,wd,woW,wc,wa,wb,wo2] (.node [we,wd,wbf,wa,wn,wg,wbr] (.node [we,wd,wbf,wa,wn3,wg,wh] .nil .nil) (.node [we,wd,wbf,wa,wn,wbn,wh] .nil .nil)) (.node [we,wd,wcH,wa,wb,wg,wqM] (.node [we,wd,woW,wc,wa,wo0,wh] .nil .nil) .nil)) (.node [we,wd,wqz,wa,wb,wg,wh] (.node [we,wd,wc,wuk,wb,wg,wh] (.node [we,wd,wc,wsh,wb,wg,wh] .nil .nil) (.node [we,wd,wc,wa,wb,wry,wh] .nil .nil)) (.node [we,wbb,wf,wa,wn3,wg,wh] (.node [we,wd,wuf,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6aba : everyKey (certRow 5 tree5) tree6aba = true := by decide +kernel
def tree6abb : BinaryTree (List W) := (.node [we,wf,wc,wr4,wb,wez,wh] (.node [we,woU,wf,wc,woY,wb,wh] (.node [we,wbb,wbf,wa,wn,wg,wh] (.node [we,wbb,wf,wbj,wn,wg,wh] .nil .nil) (.node [we,woU,wf,wc,wa,wb,wo2] .nil .nil)) (.node [we,wL,wl1,wa,wb,wg,wh] (.node [we,woU,wf,woC,wa,wb,wh] .nil .nil) .nil)) (.node [we,wf,wc,wa,wb,wq5,wh] (.node [we,wf,wc,wr4,wb,wey,wh] (.node [we,wf,wc,wr4,wb,wg,wh] .nil .nil) .nil) (.node [we,wf,wc,wa,wb,wg,wsP] (.node [we,wf,wc,wa,wb,wui,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6abb : everyKey (certRow 5 tree5) tree6abb = true := by decide +kernel
def tree6ab : BinaryTree (List W) := .node [we,wbb,wf,wa,wn,wg,wbr] tree6aba tree6abb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6ab : everyKey (certRow 5 tree5) tree6ab = true := splitCheck (by decide +kernel) ok_tree6aba ok_tree6abb
def tree6a : BinaryTree (List W) := .node [we,wd,wf,wbj,wn,wbn,wh] tree6aa tree6ab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6a : everyKey (certRow 5 tree5) tree6a = true := splitCheck (by decide +kernel) ok_tree6aa ok_tree6ab
def tree6baa : BinaryTree (List W) := (.node [we,wf,wl1,wa,wb,wg,w0] (.node [we,wf,wl1,wa,wb,wY,wh] (.node [we,wf,wl1,wQ,wb,wg,wh] (.node [we,wf,wlE,wa,wS,wg,wh] .nil .nil) (.node [we,wf,wl1,wa,wU,wg,wh] .nil .nil)) (.node [we,wf,wl1,wa,wb,wg,wh] (.node [we,wf,wl1,wa,wb,wg,w2] .nil .nil) .nil)) (.node [we,wf,wq,wa,wb,wW,w0] (.node [we,wf,wl1,wa,wS,wg,wh] (.node [we,wf,wl1,wa,wb,wW,wh] .nil .nil) (.node [we,wf,wl1,wO,wb,wg,wh] .nil .nil)) (.node [we,wf,wq,wO,wS,wg,wh] (.node [we,wf,wq,wa,wS,wg,w0] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6baa : everyKey (certRow 5 tree5) tree6baa = true := by decide +kernel
def tree6bab : BinaryTree (List W) := (.node [we,wen,wc,wr4,wb,wg,wh] (.node [we,wlC,wc,wa,wb,wW,wh] (.node [we,wJ,wq,wa,wS,wg,wh] (.node [we,wJ,wq,wa,wb,wg,w0] .nil .nil) (.node [we,wlC,wc,wa,wb,wg,w0] .nil .nil)) (.node [we,wua,wc,wa,wb,wg,w0] (.node [we,wlC,wc,wa,wS,wg,wh] .nil .nil) .nil)) (.node [wD,wf,wq,wa,wb,wW,wh] (.node [wD,wf,wl1,wa,wb,wg,wh] (.node [we,wen,wc,wj,wb,wey,wh] .nil .nil) (.node [wD,wf,wq,wa,wb,wg,w0] .nil .nil)) (.node [wa8,wd,wf,wa,wn3,wg,wh] (.node [wD,wf,wq,wO,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6bab : everyKey (certRow 5 tree5) tree6bab = true := by decide +kernel
def tree6ba : BinaryTree (List W) := .node [we,wJ,wl1,wa,wb,wg,wh] tree6baa tree6bab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6ba : everyKey (certRow 5 tree5) tree6ba = true := splitCheck (by decide +kernel) ok_tree6baa ok_tree6bab
def tree6bba : BinaryTree (List W) := (.node [wlA,wf,wc,wa,wS,wg,wh] (.node [wn7,wd,wf,wc,woY,wb,wh] (.node [wa8,wd,wf,wbj,wn,wg,wh] (.node [wa8,wd,wf,wa,wn,wbn,wh] .nil .nil) (.node [wn7,wd,wf,wc,wa,wb,wo2] .nil .nil)) (.node [wlA,wf,wc,wa,wb,wW,wh] (.node [wlA,wf,wc,wa,wb,wg,w0] .nil .nil) .nil)) (.node [wbx,wf,wc,wa,wpL,wg,wh] (.node [wqY,wf,wc,wa,wb,wg,wh] (.node [wub,wf,wc,wa,wb,wg,w0] .nil .nil) (.node [wuh,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wd,wpX,wc,wa,wb,wg,wh] (.node [wd,wpX,wc,wpZ,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6bba : everyKey (certRow 5 tree5) tree6bba = true := by decide +kernel
def tree6bbb : BinaryTree (List W) := (.node [wd,wf,wc,wpL,wpN,wg,wh] (.node [wd,wf,wc,wa,wb,wrq,wh] (.node [wd,wqh,wqn,wa,wb,wg,wh] (.node [wd,wud,wc,wa,wb,wg,wh] .nil .nil) (.node [wd,wf,wc,wa,wb,wg,wro] .nil .nil)) (.node [wd,wf,wc,wa,wuc,wg,wh] (.node [wd,wf,wc,wa,wpL,wg,wh] .nil .nil) .nil)) (.node [wd,wf,wue,wa,wb,wg,wh] (.node [wd,wf,wqn,wa,wb,wg,wh] (.node [wd,wf,wqn,wgE,wa,wb,wh] .nil .nil) .nil) (.node [wbv,wf,wc,wa,wpL,wg,wh] (.node [wd,wpu,wqn,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6bbb : everyKey (certRow 5 tree5) tree6bbb = true := by decide +kernel
def tree6bb : BinaryTree (List W) := .node [wd,wpX,wc,wpY,wb,wg,wh] tree6bba tree6bbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6bb : everyKey (certRow 5 tree5) tree6bb = true := splitCheck (by decide +kernel) ok_tree6bba ok_tree6bbb
def tree6b : BinaryTree (List W) := .node [wa8,wd,wf,wa,wn,wg,wbr] tree6ba tree6bb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6b : everyKey (certRow 5 tree5) tree6b = true := splitCheck (by decide +kernel) ok_tree6ba ok_tree6bb
def tree6 : BinaryTree (List W) := .node [we,wf,wlE,wa,wb,wW,wh] tree6a tree6b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree6 : everyKey (certRow 5 tree5) tree6 = true := splitCheck (by decide +kernel) ok_tree6a ok_tree6b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem closed6 : Closed 6 tree6 := checkedLayer 5 (by decide) _ _ closed5 ok_tree6
def tree7aaaaaaa : BinaryTree (List W) := (.node [wp,we,wf,wlQ,wa,wb,wg,wh] (.node [wp,we,wf,wlE,wa,wb,wg,wh] (.node [wp,we,wL,wq,wa,wb,wg,wh] (.node [wp,wF,wf,wq,wa,wb,wg,wh] .nil .nil) .nil) (.node [wp,we,wf,wlN,wa,wb,wg,wh] .nil .nil)) (.node [wp,we,wf,wq,wa,wU,wg,wh] (.node [wp,we,wf,wq,wQ,wb,wg,wh] (.node [wp,we,wf,wl1,wa,wb,wg,wh] .nil .nil) .nil) (.node [wp,we,wf,wq,wa,wb,wY,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaaaa : everyKey (certRow 6 tree6) tree7aaaaaaa = true := by decide +kernel
def tree7aaaaaab : BinaryTree (List W) := (.node [wp,we,wf,wq,wO,wb,wg,wh] (.node [wp,we,wf,wq,wa,wb,wW,wh] (.node [wp,we,wf,wq,wa,wb,wg,w0] (.node [wp,we,wf,wq,wa,wb,wg,wh] .nil .nil) .nil) (.node [wp,we,wf,wq,wa,wS,wg,wh] .nil .nil)) (.node [wp,wD,wf,wq,wa,wb,wg,wh] (.node [wp,we,wlC,wc,wa,wb,wg,wh] (.node [wp,we,wJ,wq,wa,wb,wg,wh] .nil .nil) .nil) (.node [wp,wlA,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaaab : everyKey (certRow 6 tree6) tree7aaaaaab = true := by decide +kernel
def tree7aaaaaa : BinaryTree (List W) := .node [wp,we,wf,wq,wa,wb,wg,w2] tree7aaaaaaa tree7aaaaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaaa : everyKey (certRow 6 tree6) tree7aaaaaa = true := splitCheck (by decide +kernel) ok_tree7aaaaaaa ok_tree7aaaaaab
def tree7aaaaaba : BinaryTree (List W) := (.node [wm,we,wbd,wf,wa,wn,wg,wh] (.node [wpM,wo,wd,wf,wc,wae,wg,wh] (.node [wtL,we,wd,wf,wc,wb,wg,wh] (.node [wtJ,we,wd,wf,wc,wb,wg,wh] .nil .nil) .nil) (.node [wm,wba,wd,wf,wa,wn,wg,wh] .nil .nil)) (.node [wm,we,wd,wf,wa,wn3,wg,wh] (.node [wm,we,wd,wf,wbl,wn,wg,wh] (.node [wm,we,wd,wbh,wa,wn,wg,wh] .nil .nil) .nil) (.node [wm,we,wd,wf,wa,wn,wbp,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaaba : everyKey (certRow 6 tree6) tree7aaaaaba = true := by decide +kernel
def tree7aaaaabb : BinaryTree (List W) := (.node [wm,we,wd,wbf,wa,wn,wg,wh] (.node [wm,we,wd,wf,wa,wn,wbn,wh] (.node [wm,we,wd,wf,wa,wn,wg,wbr] (.node [wm,we,wd,wf,wa,wn,wg,wh] .nil .nil) .nil) (.node [wm,we,wd,wf,wbj,wn,wg,wh] .nil .nil)) (.node [wm,wa8,wd,wf,wa,wn,wg,wh] (.node [wm,we,wbb,wf,wa,wn,wg,wh] .nil .nil) (.node [wlZ,we,wd,wf,wa,wn,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaabb : everyKey (certRow 6 tree6) tree7aaaaabb = true := by decide +kernel
def tree7aaaaab : BinaryTree (List W) := .node [wm,we,wd,wf,wa,wn,wg,wbt] tree7aaaaaba tree7aaaaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaab : everyKey (certRow 6 tree6) tree7aaaaab = true := splitCheck (by decide +kernel) ok_tree7aaaaaba ok_tree7aaaaabb
def tree7aaaaa : BinaryTree (List W) := .node [waZ,we,wd,wf,wc,wfc,wg,wh] tree7aaaaaa tree7aaaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaa : everyKey (certRow 6 tree6) tree7aaaaa = true := splitCheck (by decide +kernel) ok_tree7aaaaaa ok_tree7aaaaab
def tree7aaaabaa : BinaryTree (List W) := (.node [way,we,wf,wc,wa,wb,wg,w0] (.node [wlY,we,wf,wq,wa,wb,wg,wh] (.node [wn2,we,wd,wf,wa,wn,wg,wh] (.node [wte,we,wd,wf,wc,wa,wb,wh] .nil .nil) .nil) (.node [wn4,we,wd,wf,wa,wn,wg,wh] .nil .nil)) (.node [way,we,wf,wc,wa,wb,wW,wh] (.node [way,we,wf,wc,wa,wb,wg,waz] (.node [way,we,wf,wc,wa,wb,wg,wdf] .nil .nil) .nil) (.node [way,we,wf,wc,wa,wS,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaabaa : everyKey (certRow 6 tree6) tree7aaaabaa = true := by decide +kernel
def tree7aaaabab : BinaryTree (List W) := (.node [wgC,w9,wd,wf,wr,wa,wb,wh] (.node [wah,wd,wf,wc,wa,wb,wai,wh] (.node [wlz,we,wf,wq,wa,wb,wg,wh] (.node [wlz,we,wf,wc,wa,wb,wg,w0] .nil .nil) .nil) (.node [wak,wd,wf,wc,wa,wb,wg,wal] .nil .nil)) (.node [wgC,we,woV,wf,wc,wa,wb,wh] (.node [wgC,wz,wd,wf,wc,wa,wb,wh] .nil .nil) (.node [wgC,we,wd,woX,wc,wa,wb,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaabab : everyKey (certRow 6 tree6) tree7aaaabab = true := by decide +kernel
def tree7aaaaba : BinaryTree (List W) := .node [wlz,we,wf,wc,wa,wb,wg,wh] tree7aaaabaa tree7aaaabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaaba : everyKey (certRow 6 tree6) tree7aaaaba = true := splitCheck (by decide +kernel) ok_tree7aaaabaa ok_tree7aaaabab
def tree7aaaabba : BinaryTree (List W) := (.node [wgC,we,wd,wf,wc,wa,wb,wo2] (.node [wgC,we,wd,wf,wc,wa,wb,wo3] (.node [wgC,we,wd,wf,wc,wa,wo1,wh] (.node [wgC,we,wd,wf,wc,woZ,wb,wh] .nil .nil) .nil) (.node [wgC,we,wd,wf,wc,wa,wb,wh] .nil .nil)) (.node [wgC,we,wd,wf,woC,wa,wb,wh] (.node [wgC,we,wd,wf,wc,woY,wb,wh] (.node [wgC,we,wd,wf,wc,wa,wo0,wh] .nil .nil) .nil) (.node [wgC,we,wd,wf,wa,wb,waU,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaabba : everyKey (certRow 6 tree6) tree7aaaabba = true := by decide +kernel
def tree7aaaabbb : BinaryTree (List W) := (.node [wfX,wd,wf,wc,wa,wb,wg,wal] (.node [wgC,wd,wf,wc,wa,wb,wai,wh] (.node [wgC,wn7,wd,wf,wc,wa,wb,wh] (.node [wgC,we,woU,wf,wc,wa,wb,wh] .nil .nil) .nil) (.node [wfX,we,wf,wc,wa,wb,wg,waz] .nil .nil)) (.node [wgj,we,wd,wc,wa,wb,wg,waM] (.node [wn5,we,wd,wf,wa,wn,wg,wh] .nil .nil) (.node [wgj,we,wf,wc,wa,wb,wg,waz] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaabbb : everyKey (certRow 6 tree6) tree7aaaabbb = true := by decide +kernel
def tree7aaaabb : BinaryTree (List W) := .node [wgC,we,wd,woW,wc,wa,wb,wh] tree7aaaabba tree7aaaabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaabb : everyKey (certRow 6 tree6) tree7aaaabb = true := splitCheck (by decide +kernel) ok_tree7aaaabba ok_tree7aaaabbb
def tree7aaaab : BinaryTree (List W) := .node [wgC,we,wd,wf,waV,wa,wb,wh] tree7aaaaba tree7aaaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaab : everyKey (certRow 6 tree6) tree7aaaab = true := splitCheck (by decide +kernel) ok_tree7aaaaba ok_tree7aaaabb
def tree7aaaa : BinaryTree (List W) := .node [wlZ,we,wf,wq,wa,wb,wg,wh] tree7aaaaa tree7aaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaa : everyKey (certRow 6 tree6) tree7aaaa = true := splitCheck (by decide +kernel) ok_tree7aaaaa ok_tree7aaaab
def tree7aaabaaa : BinaryTree (List W) := (.node [wo,wd,wf,wc,wpN,wae,wg,wh] (.node [wo,wd,wf,wc,wa,wpL,wg,wh] (.node [wo,wbx,wf,wc,wa,wae,wg,wh] (.node [wbH,wd,wf,wc,wa,wae,wg,wh] .nil .nil) .nil) (.node [wo,wd,wf,wc,wa,wae,wg,wh] .nil .nil)) (.node [wy,wd,w8,wc,wpZ,wb,wg,wh] (.node [wgy,wd,wf,wc,wa,wae,wg,wh] (.node [wo,wbv,wf,wc,wa,wae,wg,wh] .nil .nil) .nil) (.node [wy,wd,w8,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabaaa : everyKey (certRow 6 tree6) tree7aaabaaa = true := by decide +kernel
def tree7aaabaab : BinaryTree (List W) := (.node [wru,wd,wf,wc,wa,wb,wg,wh] (.node [wy,wd,wpX,wc,wa,wb,wg,wh] (.node [wy,wd,wdo,wc,wa,wb,wg,wh] (.node [wy,wd,wpI,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wdY,wd,w8,wc,wa,wb,wg,wh] .nil .nil)) (.node [w9,wd,wqh,wr,wa,wb,wg,wh] (.node [wdJ,wd,wf,wr,wa,wb,wg,wh] .nil .nil) (.node [w9,wd,wf,wqn,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabaab : everyKey (certRow 6 tree6) tree7aaabaab = true := by decide +kernel
def tree7aaabaa : BinaryTree (List W) := .node [wy,wd,w8,wc,wpY,wb,wg,wh] tree7aaabaaa tree7aaabaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabaa : everyKey (certRow 6 tree6) tree7aaabaa = true := splitCheck (by decide +kernel) ok_tree7aaabaaa ok_tree7aaabaab
def tree7aaababa : BinaryTree (List W) := (.node [wn6,wd,wf,wr,wa,wb,wg,wh] (.node [wfH,wd,wf,wr,wa,wb,wg,wh] (.node [w9,wd,wpu,wr,wa,wb,wg,wh] (.node [w9,wd,wf,wr,wa,wb,wg,wh] .nil .nil) .nil) (.node [wsz,wd,wf,wr,wa,wb,wg,wh] .nil .nil)) (.node [wqP,wd,wf,wr,wa,wb,wg,wh] (.node [wrd,wd,wf,wr,wa,wb,wg,wh] (.node [wrr,wd,wf,wr,wa,wb,wg,wh] .nil .nil) .nil) (.node [wcq,we,wd,waB,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaababa : everyKey (certRow 6 tree6) tree7aaababa = true := by decide +kernel
def tree7aaababb : BinaryTree (List W) := (.node [wt,we,wd,wcJ,wa,wb,wg,waY] (.node [whx,we,wd,waB,wa,wb,wg,wh] (.node [wf3,we,wd,waB,wa,wb,wg,wh] (.node [ws,we,wd,waB,wa,wb,wg,wh] .nil .nil) .nil) (.node [wt6,we,wd,wc,wa,wb,wg,wh] .nil .nil)) (.node [wt,we,wd,wf,wa,wb,wg,waY] (.node [wt,we,wd,wf,wqO,wa,wb,waY] .nil .nil) (.node [wt,we,wd,wf,wa,wb,wg,wlX] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaababb : everyKey (certRow 6 tree6) tree7aaababb = true := by decide +kernel
def tree7aaabab : BinaryTree (List W) := .node [ws,we,wd,wqz,wa,wb,wg,wh] tree7aaababa tree7aaababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabab : everyKey (certRow 6 tree6) tree7aaabab = true := splitCheck (by decide +kernel) ok_tree7aaababa ok_tree7aaababb
def tree7aaaba : BinaryTree (List W) := .node [w9,wd,wf,wgE,wr,wa,wb,wh] tree7aaabaa tree7aaabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaaba : everyKey (certRow 6 tree6) tree7aaaba = true := splitCheck (by decide +kernel) ok_tree7aaabaa ok_tree7aaabab
def tree7aaabbaa : BinaryTree (List W) := (.node [w4,w5,wf,wc,wa,wb,wg,wh] (.node [wt,we,wd,wf,wa,wb,waY,wqN] (.node [wt,we,wd,wf,wa,wb,wg,wqM] (.node [wt,we,wd,wf,wa,wb,wg,wqy] .nil .nil) .nil) (.node [wt,we,wd,wcH,wa,wb,wg,waY] .nil .nil)) (.node [wcY,w5,wf,wc,wa,wb,wg,wh] (.node [wfk,w5,wf,wc,wa,wb,wg,wh] (.node [w4,wdl,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wq1,wd,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabbaa : everyKey (certRow 6 tree6) tree7aaabbaa = true := by decide +kernel
def tree7aaabbab : BinaryTree (List W) := (.node [wp1,wu,wf,wc,wa,wb,wg,wh] (.node [wgn,wu,wf,wc,wa,wb,wg,wh] (.node [w3,wu,wf,wc,wa,wb,wg,wh] (.node [w3,wqY,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wg6,wu,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wqS,wu,wf,wc,wa,wb,wg,wh] (.node [wt0,we,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [wqR,wu,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabbab : everyKey (certRow 6 tree6) tree7aaabbab = true := by decide +kernel
def tree7aaabba : BinaryTree (List W) := .node [wdi,wu,wf,wc,wa,wb,wg,wh] tree7aaabbaa tree7aaabbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabba : everyKey (certRow 6 tree6) tree7aaabba = true := splitCheck (by decide +kernel) ok_tree7aaabbaa ok_tree7aaabbab
def tree7aaabbba : BinaryTree (List W) := (.node [ww,we,wf,wc,wa,wb,wlO,wh] (.node [ww,we,wf,wc,wa,wb,wlS,wh] (.node [ww,we,wf,wc,wa,wb,wlU,wh] (.node [ww,we,wf,wc,wa,wb,wax,wh] .nil .nil) .nil) (.node [ww,we,wf,wc,wa,wb,wq5,wh] .nil .nil)) (.node [ww,we,wlC,wc,wa,wb,wg,wh] (.node [ww,we,wf,wlE,wa,wb,wg,wh] (.node [ww,we,wf,wc,wa,wb,wlK,wh] .nil .nil) .nil) (.node [ww,wlA,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabbba : everyKey (certRow 6 tree6) tree7aaabbba = true := by decide +kernel
def tree7aaabbbb : BinaryTree (List W) := (.node [wqt,wd,wf,wc,wa,wb,wg,wh] (.node [wlV,wu,wf,wc,wa,wb,wg,wh] (.node [waa,wd,wf,wdM,wa,wb,wg,wh] (.node [waa,wd,wf,wab,wa,wb,wg,wh] .nil .nil) .nil) (.node [wcD,wd,wf,wab,wa,wb,wg,wh] .nil .nil)) (.node [wdm,wd,w7,wc,wa,wb,wg,wh] (.node [wqr,wd,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [w6,wd,w7,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabbbb : everyKey (certRow 6 tree6) tree7aaabbbb = true := by decide +kernel
def tree7aaabbb : BinaryTree (List W) := .node [woa,we,wf,wc,wa,wb,wg,wh] tree7aaabbba tree7aaabbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabbb : everyKey (certRow 6 tree6) tree7aaabbb = true := splitCheck (by decide +kernel) ok_tree7aaabbba ok_tree7aaabbbb
def tree7aaabb : BinaryTree (List W) := .node [wpO,wu,wf,wc,wa,wb,wg,wh] tree7aaabba tree7aaabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaabb : everyKey (certRow 6 tree6) tree7aaabb = true := splitCheck (by decide +kernel) ok_tree7aaabba ok_tree7aaabbb
def tree7aaab : BinaryTree (List W) := .node [wt,we,wd,wf,wa,wb,wg,wqL] tree7aaaba tree7aaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaab : everyKey (certRow 6 tree6) tree7aaab = true := splitCheck (by decide +kernel) ok_tree7aaaba ok_tree7aaabb
def tree7aaa : BinaryTree (List W) := .node [ws2,we,wd,wf,wc,wa,wb,wg] tree7aaaa tree7aaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaa : everyKey (certRow 6 tree6) tree7aaa = true := splitCheck (by decide +kernel) ok_tree7aaaa ok_tree7aaab
def tree7aabaaaa : BinaryTree (List W) := (.node [wA,wd,wf,wc,wa,wb,wg,wcd] (.node [wA,wd,wf,wc,wa,wb,wg,wam] (.node [wpx,wd,wf,wc,wa,wb,wg,wh] (.node [waf,wd,wf,wc,wa,wb5,wg,wh] .nil .nil) .nil) (.node [wA,wd,wf,wc,wa,wb,wg,wqT] .nil .nil)) (.node [wA,woQ,wf,wc,wa,wb,wg,wh] (.node [wA,wd,woI,wc,wa,wb,wg,wh] (.node [wA,wd,wf,wc,wa,wb,wg,wro] .nil .nil) .nil) (.node [wz,we,wd,wf,wc,wa,wn9,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabaaaa : everyKey (certRow 6 tree6) tree7aabaaaa = true := by decide +kernel
def tree7aabaaab : BinaryTree (List W) := (.node [wz,wd,wf,wc,wa,wb,wrg,wh] (.node [wz,wd,wf,wc,wrp,wa,wb,wh] (.node [wz,wd,wf,waV,wr,wa,wb,wh] (.node [wz,wn7,wd,wf,wc,wa,wb,wh] .nil .nil) .nil) (.node [wz,wd,wf,wc,wa,wb,waj,wh] .nil .nil)) (.node [wz,wd,wf,wc,wa,wb,wrs,wh] (.node [wz,wd,wf,wc,wa,wb,wrq,wh] (.node [wz,wd,wf,wc,wa,wb,wq6,wh] .nil .nil) .nil) (.node [wz,wd,wf,woC,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabaaab : everyKey (certRow 6 tree6) tree7aabaaab = true := by decide +kernel
def tree7aabaaa : BinaryTree (List W) := .node [wz,we,wn8,wf,wc,wa,wb,wh] tree7aabaaaa tree7aabaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabaaa : everyKey (certRow 6 tree6) tree7aabaaa = true := splitCheck (by decide +kernel) ok_tree7aabaaaa ok_tree7aabaaab
def tree7aabaaba : BinaryTree (List W) := (.node [wF,wlL,wf,wc,wa,wb,wg,wh] (.node [wlB,wd,wf,wc,wa,wb,wg,wh] (.node [wmF,wd,wf,wc,wa,wb,wg,wh] (.node [wpk,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wF,w5,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wF,wd,wf,wc,wa,wU,wg,wh] (.node [wF,wd,wf,wc,wQ,wb,wg,wh] (.node [wF,wd,wL,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wF,wd,wf,wc,wa,wb,wY,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabaaba : everyKey (certRow 6 tree6) tree7aabaaba = true := by decide +kernel
def tree7aabaabb : BinaryTree (List W) := (.node [wF,wd,wf,wc,wO,wb,wg,wh] (.node [wF,wd,wf,wc,wa,wb,wW,wh] (.node [wF,wd,wf,wc,wa,wb,wg,w0] (.node [wF,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wF,wd,wf,wc,wa,wS,wg,wh] .nil .nil)) (.node [wF,wu,wf,wc,wa,wb,wg,wh] (.node [wF,wd,wJ,wc,wa,wb,wg,wh] .nil .nil) (.node [wlm,wd,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabaabb : everyKey (certRow 6 tree6) tree7aabaabb = true := by decide +kernel
def tree7aabaab : BinaryTree (List W) := .node [wF,wd,wf,wc,wa,wb,wg,w2] tree7aabaaba tree7aabaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabaab : everyKey (certRow 6 tree6) tree7aabaab = true := splitCheck (by decide +kernel) ok_tree7aabaaba ok_tree7aabaabb
def tree7aabaa : BinaryTree (List W) := .node [we0,wd,wf,wc,wad,wb,wg,wh] tree7aabaaa tree7aabaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabaa : everyKey (certRow 6 tree6) tree7aabaa = true := splitCheck (by decide +kernel) ok_tree7aabaaa ok_tree7aabaab
def tree7aababaa : BinaryTree (List W) := (.node [wba,wbd,wf,wc,wa,wb,wg,wh] (.node [wjB,wd,wf,wc,wa,wb,wg,wh] (.node [wmx,wd,wf,wc,wa,wb,wg,wh] (.node [wia,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wjs,wd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wba,wd,wf,wc,wa,wb,wbp,wh] (.node [wba,wd,wf,wc,wbl,wb,wg,wh] (.node [wba,wd,wbh,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wba,wd,wf,wc,wa,wb,wg,wbt] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aababaa : everyKey (certRow 6 tree6) tree7aababaa = true := by decide +kernel
def tree7aababab : BinaryTree (List W) := (.node [wba,wbb,wf,wc,wa,wb,wg,wh] (.node [wba,wd,wf,wc,wbj,wb,wg,wh] (.node [wba,wd,wf,wc,wa,wb,wbn,wh] (.node [wba,wd,wf,wc,wa,wb,wg,wbr] .nil .nil) .nil) (.node [wba,wd,wbf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wh3,wd,wf,wc,wa,wb,wg,wh] (.node [wnI,wd,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [wle,wd,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aababab : everyKey (certRow 6 tree6) tree7aababab = true := by decide +kernel
def tree7aababa : BinaryTree (List W) := .node [wba,wd,wf,wc,wa,wb,wg,wh] tree7aababaa tree7aababab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aababa : everyKey (certRow 6 tree6) tree7aababa = true := splitCheck (by decide +kernel) ok_tree7aababaa ok_tree7aababab
def tree7aababba : BinaryTree (List W) := (.node [we,wB,wd,wc,wa,wb,wqx,wh] (.node [wiE,wd,wf,wc,wa,wb,wg,wh] (.node [whN,wd,wf,wc,wa,wb,wg,wh] (.node [wiq,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wB,wd,wc,wa,wb,waL,wh] .nil .nil)) (.node [we,whu,wf,wc,wa,was,wg,wh] (.node [we,wB,wd,wc,wa,wb,wry,wh] (.node [we,wB,wd,wc,wa,wb,wp0,wh] .nil .nil) .nil) (.node [we,wt4,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aababba : everyKey (certRow 6 tree6) tree7aababba = true := by decide +kernel
def tree7aababbb : BinaryTree (List W) := (.node [we,wao,wfp,wc,wa,wb,wg,wh] (.node [we,wfP,wf,wc,wa,was,wg,wh] (.node [we,wgb,wf,wc,wa,was,wg,wh] (.node [we,wgU,wf,wc,wa,was,wg,wh] .nil .nil) .nil) (.node [we,wao,wap,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wao,wL,wc,wa,wb,wg,wh] (.node [we,wao,wc2,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wao,wf,wc,wa,wb,wg,w0] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aababbb : everyKey (certRow 6 tree6) tree7aababbb = true := by decide +kernel
def tree7aababb : BinaryTree (List W) := .node [we,whf,wf,wc,wa,was,wg,wh] tree7aababba tree7aababbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aababb : everyKey (certRow 6 tree6) tree7aababb = true := splitCheck (by decide +kernel) ok_tree7aababba ok_tree7aababbb
def tree7aabab : BinaryTree (List W) := .node [wnP,wd,wf,wc,wa,wb,wg,wh] tree7aababa tree7aababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabab : everyKey (certRow 6 tree6) tree7aabab = true := splitCheck (by decide +kernel) ok_tree7aababa ok_tree7aababb
def tree7aaba : BinaryTree (List W) := .node [wi5,wd,wf,wc,wa,wb,wg,wh] tree7aabaa tree7aabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aaba : everyKey (certRow 6 tree6) tree7aaba = true := splitCheck (by decide +kernel) ok_tree7aabaa ok_tree7aabab
def tree7aabbaaa : BinaryTree (List W) := (.node [we,wlM,wv,wc,wa,wb,wg,wh] (.node [we,wlM,wL,wc,wa,wb,wg,wh] (.node [we,wlM,wcJ,wc,wa,wb,wg,wh] (.node [we,wao,wf,wc,wa,wS,wg,wh] .nil .nil) .nil) (.node [we,wlM,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wq4,wf,wc,wa,wb,wg,wh] (.node [we,wsS,wf,wc,wa,wb,wg,wh] (.node [we,ws1,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wsJ,wd,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbaaa : everyKey (certRow 6 tree6) tree7aabbaaa = true := by decide +kernel
def tree7aabbaab : BinaryTree (List W) := (.node [we,wsB,wf,wc,wa,wb,wg,wh] (.node [we,wsB,wan,wc,wa,wb,wg,wh] (.node [we,wsD,wd,wc,wa,wb,wg,wh] (.node [we,wsF,wd,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wsB,wd,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wsB,wc,wa,wb,wg,wh] (.node [we,wsB,wv,wc,wa,wb,wg,wh] .nil .nil) (.node [we,waq,wf,wc,war,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbaab : everyKey (certRow 6 tree6) tree7aabbaab = true := by decide +kernel
def tree7aabbaa : BinaryTree (List W) := .node [we,wsH,wv,wc,wa,wb,wg,wh] tree7aabbaaa tree7aabbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbaa : everyKey (certRow 6 tree6) tree7aabbaa = true := splitCheck (by decide +kernel) ok_tree7aabbaaa ok_tree7aabbaab
def tree7aabbaba : BinaryTree (List W) := (.node [we,waF,wd,wc,waG,wb,wg,wh] (.node [we,wsd,wf,wc,wa,wb,wg,wh] (.node [we,wsj,wf,wc,wa,wb,wg,wh] (.node [we,wsn,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wsb,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,we7,wd,wc,wnb,wb,wg,wh] (.node [we,we7,wd,wc,waG,wb,wg,wh] (.node [we,we7,wl,wd,wc,wb,wa3,wg] .nil .nil) .nil) (.node [we,we7,wd,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbaba : everyKey (certRow 6 tree6) tree7aabbaba = true := by decide +kernel
def tree7aabbabb : BinaryTree (List W) := (.node [we,wr7,wd,wc,wa,wb,wg,wh] (.node [we,wsp,wd,wc,wa,wb,wg,wh] (.node [we,wst,wd,wc,wa,wb,wg,wh] (.node [we,wsv,wd,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wsl,wd,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wep,wd,wc,wa,wb,wez,wh] (.node [we,wep,wi,wc,wj,wb,wg,wh] .nil .nil) (.node [we,wep,wd,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbabb : everyKey (certRow 6 tree6) tree7aabbabb = true := by decide +kernel
def tree7aabbab : BinaryTree (List W) := .node [we,we7,wd,wc,waE,wb,wg,wh] tree7aabbaba tree7aabbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbab : everyKey (certRow 6 tree6) tree7aabbab = true := splitCheck (by decide +kernel) ok_tree7aabbaba ok_tree7aabbabb
def tree7aabba : BinaryTree (List W) := .node [we,we4,wf,wc,war,wb,wg,wh] tree7aabbaa tree7aabbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabba : everyKey (certRow 6 tree6) tree7aabba = true := splitCheck (by decide +kernel) ok_tree7aabbaa ok_tree7aabbab
def tree7aabbbaa : BinaryTree (List W) := (.node [we,wrM,wd,wc,wa,wb,wg,wh] (.node [we,wrW,wd,wc,wa,wb,wg,wh] (.node [we,wrS,wd,wc,wa,wb,wg,wh] (.node [we,wr0,wd,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wrO,wd,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wi,wf,wc,wj,wb,wg,wh] (.node [we,wi,wf,wc,wj,wb,wez,wh] (.node [we,wi,wf,wc,wr4,wb,wg,wh] .nil .nil) .nil) (.node [we,wi,wf,wc,wj,wb,wey,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbbaa : everyKey (certRow 6 tree6) tree7aabbbaa = true := by decide +kernel
def tree7aabbbab : BinaryTree (List W) := (.node [we,wrI,wf,wc,wj,wb,wg,wh] (.node [we,wtN,wf,wc,wj,wb,wg,wh] (.node [we,wfL,wf,wc,wj,wb,wg,wh] (.node [we,wl0,wf,wc,wj,wb,wg,wh] .nil .nil) .nil) (.node [we,wtO,wd,wf,wc,wb,wg,wh] .nil .nil)) (.node [we,wk,wd,wc,wsh,wb,wg,wh] (.node [we,weQ,wd,wc,waE,wb,wg,wh] .nil .nil) (.node [we,wk,wd,wc,waE,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbbab : everyKey (certRow 6 tree6) tree7aabbbab = true := by decide +kernel
def tree7aabbba : BinaryTree (List W) := .node [we,wi,wen,wc,wj,wb,wg,wh] tree7aabbbaa tree7aabbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbba : everyKey (certRow 6 tree6) tree7aabbba = true := splitCheck (by decide +kernel) ok_tree7aabbbaa ok_tree7aabbbab
def tree7aabbbba : BinaryTree (List W) := (.node [we,wl,wd,wf,wc,wb,wsy,wg] (.node [we,wl,wd,wf,wc,wb,wsx,wg] (.node [we,wl,wd,wf,wc,wb,wr3,wg] (.node [we,wl,wd,wf,wc,wb,wa3,wg] .nil .nil) .nil) (.node [we,wl,wd,wf,wc,wb,wsg,wg] .nil .nil)) (.node [we,wl,wd,wf,wnj,wb,wg,wh] (.node [we,wl,wd,wf,wc,wb,wg,wnk] (.node [we,wl,wd,wf,wc,wb,wsw,wg] .nil .nil) .nil) (.node [we,wl,wd,wni,wc,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbbba : everyKey (certRow 6 tree6) tree7aabbbba = true := by decide +kernel
def tree7aabbbbb : BinaryTree (List W) := (.node [we,wl2,wv,wc,wa,wb,wg,wh] (.node [we,wfm,wv,wc,wa,wb,wg,wh] (.node [we,wng,wd,wf,wc,wb,wg,wh] (.node [we,wl,wnh,wf,wc,wb,wg,wh] .nil .nil) .nil) (.node [we,wan,wv,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wt8,wv,wc,wa,wb,wg,wh] (.node [we,wrC,wv,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wsQ,wv,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbbbb : everyKey (certRow 6 tree6) tree7aabbbbb = true := by decide +kernel
def tree7aabbbb : BinaryTree (List W) := .node [we,wl,wd,we5,wc,wb,wa3,wg] tree7aabbbba tree7aabbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbbb : everyKey (certRow 6 tree6) tree7aabbbb = true := splitCheck (by decide +kernel) ok_tree7aabbbba ok_tree7aabbbbb
def tree7aabbb : BinaryTree (List W) := .node [we,wf7,wd,wc,waE,wb,wg,wh] tree7aabbba tree7aabbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabbb : everyKey (certRow 6 tree6) tree7aabbb = true := splitCheck (by decide +kernel) ok_tree7aabbba ok_tree7aabbbb
def tree7aabb : BinaryTree (List W) := .node [we,wep,wd,wc,wa,wb,wey,wh] tree7aabba tree7aabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aabb : everyKey (certRow 6 tree6) tree7aabb = true := splitCheck (by decide +kernel) ok_tree7aabba ok_tree7aabbb
def tree7aab : BinaryTree (List W) := .node [we,wao,wf,wc,wa,wb,wW,wh] tree7aaba tree7aabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aab : everyKey (certRow 6 tree6) tree7aab = true := splitCheck (by decide +kernel) ok_tree7aaba ok_tree7aabb
def tree7aa : BinaryTree (List W) := .node [waf,wd,wf,wc,wa,wag,wg,wh] tree7aaa tree7aab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aa : everyKey (certRow 6 tree6) tree7aa = true := splitCheck (by decide +kernel) ok_tree7aaa ok_tree7aab
def tree7abaaaaa : BinaryTree (List W) := (.node [we,wfT,wf,wc,wa,wb,waw,wh] (.node [we,wav,wf,wc,wa,wb,waw,wh] (.node [we,wrB,wf,wc,wa,wb,wg,wh] (.node [we,wt9,wv,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wgY,wf,wc,wa,wb,waw,wh] .nil .nil)) (.node [we,w5,wf,wc,wa,wb,wg,w0] (.node [we,wrj,wf,wc,wa,wb,wg,wh] (.node [we,wtg,wd,wf,wc,wa,wb,wh] .nil .nil) .nil) (.node [we,w5,wf,wc,wa,wb,wW,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaaaa : everyKey (certRow 6 tree6) tree7abaaaaa = true := by decide +kernel
def tree7abaaaab : BinaryTree (List W) := (.node [we,wrf,wf,wc,wa,wb,wg,wh] (.node [we,wrc,wf,wc,wa,wb,wg,wh] (.node [we,wlL,wf,wc,wa,wb,wg,wh] (.node [we,w5,wf,wc,wO,wb,wg,wh] .nil .nil) .nil) (.node [we,wdF,wf,wc,wa,wb,waw,wh] .nil .nil)) (.node [we,wpU,wf,wc,wa,wb,wg,wh] (.node [we,wqY,wf,wc,wa,wb,wg,wh] (.node [we,wq8,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wpQ,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaaab : everyKey (certRow 6 tree6) tree7abaaaab = true := by decide +kernel
def tree7abaaaa : BinaryTree (List W) := .node [we,w5,wf,wc,wa,wS,wg,wh] tree7abaaaaa tree7abaaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaaa : everyKey (certRow 6 tree6) tree7abaaaa = true := splitCheck (by decide +kernel) ok_tree7abaaaaa ok_tree7abaaaab
def tree7abaaaba : BinaryTree (List W) := (.node [we,wpB,wf,wc,wa,wb,wg,wh] (.node [we,wpz,wf,wc,wa,wb,wg,wh] (.node [we,wpF,wf,wc,wa,wb,wg,wh] (.node [we,wpH,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wpD,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wx,wf,wc,wa,wb,wg,wlP] (.node [we,wx,wf,wc,wa,wb,wg,wlT] (.node [we,wx,wf,wc,wa,wb,wg,waA] .nil .nil) .nil) (.node [we,wx,wf,wc,wa,wb,wg,wsP] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaaba : everyKey (certRow 6 tree6) tree7abaaaba = true := by decide +kernel
def tree7abaaabb : BinaryTree (List W) := (.node [we,wrD,wf,wc,wa,wb,wg,wh] (.node [we,wH,wf,wc,wa,wb,wW,wh] (.node [we,wH,wf,wc5,wa,wb,wg,wh] (.node [we,wH,wf,wM,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wH,wf,wc,wa,wS,wg,wh] .nil .nil)) (.node [we,woV,wf,wc,wa,wb,wg,wh] (.node [we,wm8,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wka,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaabb : everyKey (certRow 6 tree6) tree7abaaabb = true := by decide +kernel
def tree7abaaab : BinaryTree (List W) := .node [we,wx,wlC,wc,wa,wb,wg,wh] tree7abaaaba tree7abaaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaab : everyKey (certRow 6 tree6) tree7abaaab = true := splitCheck (by decide +kernel) ok_tree7abaaaba ok_tree7abaaabb
def tree7abaaa : BinaryTree (List W) := .node [we,wbx,wf,wc,wa,wb,wg,wh] tree7abaaaa tree7abaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaa : everyKey (certRow 6 tree6) tree7abaaa = true := splitCheck (by decide +kernel) ok_tree7abaaaa ok_tree7abaaab
def tree7abaabaa : BinaryTree (List W) := (.node [we,wpf,wv,wc,wa,wb,wg,wh] (.node [we,wjd,wf,wc,wa,wb,wg,wh] (.node [we,wcG,wf,wM,wa,wb,wg,wh] (.node [we,wjT,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wju,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wos,wf,wc,wa,wb,wg,wh] (.node [we,wiO,wf,wc,wa,wb,wg,wh] (.node [we,wiF,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,woc,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaabaa : everyKey (certRow 6 tree6) tree7abaabaa = true := by decide +kernel
def tree7abaabab : BinaryTree (List W) := (.node [we,wbd,wf,wc,wa,wb,wg,wbr] (.node [we,wbd,wf,wc,wa,wb,wg,wbt] (.node [we,wbd,wf,wc,wa,wb,wbp,wh] (.node [we,wbd,wf,wc,wbl,wb,wg,wh] .nil .nil) .nil) (.node [we,wbd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wbd,wf,wc,wbj,wb,wg,wh] (.node [we,wbd,wf,wc,wa,wb,wbn,wh] .nil .nil) (.node [we,wbd,wbf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaabab : everyKey (certRow 6 tree6) tree7abaabab = true := by decide +kernel
def tree7abaaba : BinaryTree (List W) := .node [we,wbd,wbh,wc,wa,wb,wg,wh] tree7abaabaa tree7abaabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaaba : everyKey (certRow 6 tree6) tree7abaaba = true := splitCheck (by decide +kernel) ok_tree7abaabaa ok_tree7abaabab
def tree7abaabba : BinaryTree (List W) := (.node [we,wkm,wf,wc,wa,wb,wg,wh] (.node [we,wmH,wf,wc,wa,wb,wg,wh] (.node [we,wmX,wf,wc,wa,wb,wg,wh] (.node [we,wnn,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wmm,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,woH,wf,wc,wa,wb,wg,wh] (.node [we,wmc,wf,wc,wa,wb,wg,wh] (.node [we,wic,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wok,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaabba : everyKey (certRow 6 tree6) tree7abaabba = true := by decide +kernel
def tree7abaabbb : BinaryTree (List W) := (.node [we,wd,wti,wf,wc,wa,wb,wh] (.node [we,wd,wrF,wc,wa,wb,wg,wh] (.node [we,whP,wf,wc,wa,wb,wg,wh] (.node [we,whW,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,waJ,wc,wa,wb,waK,wh] .nil .nil)) (.node [we,wd,wrl,wc,wa,wb,wg,wh] (.node [we,wd,wpI,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wrn,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaabbb : everyKey (certRow 6 tree6) tree7abaabbb = true := by decide +kernel
def tree7abaabb : BinaryTree (List W) := .node [we,wkL,wf,wc,wa,wb,wg,wh] tree7abaabba tree7abaabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaabb : everyKey (certRow 6 tree6) tree7abaabb = true := splitCheck (by decide +kernel) ok_tree7abaabba ok_tree7abaabbb
def tree7abaab : BinaryTree (List W) := .node [we,wnW,wf,wc,wa,wb,wg,wh] tree7abaaba tree7abaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaab : everyKey (certRow 6 tree6) tree7abaab = true := splitCheck (by decide +kernel) ok_tree7abaaba ok_tree7abaabb
def tree7abaa : BinaryTree (List W) := .node [we,wjJ,wf,wc,wa,wb,wg,wh] tree7abaaa tree7abaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abaa : everyKey (certRow 6 tree6) tree7abaa = true := splitCheck (by decide +kernel) ok_tree7abaaa ok_tree7abaab
def tree7ababaaa : BinaryTree (List W) := (.node [we,wd,wcJ,waD,wa,wb,wg,wh] (.node [we,wd,waC,waD,wa,wb,wg,wh] (.node [we,wd,wq3,wc,wa,wb,wg,wh] (.node [we,wd,wra,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,waC,wd5,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wcJ,waB,wa,wb,wg,wh] (.node [we,wd,wcJ,wc,wa,wb,wg,wh] (.node [we,wd,wcJ,wmz,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wqF,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababaaa : everyKey (certRow 6 tree6) tree7ababaaa = true := by decide +kernel
def tree7ababaab : BinaryTree (List W) := (.node [we,wd,wql,wc,wa,wb,wg,wh] (.node [we,wd,wqp,wc,wa,wb,wg,wh] (.node [we,wd,wqv,wc,wa,wb,wg,wh] (.node [we,wd,wqB,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wqh,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wqd,wc,wa,wb,wg,wh] (.node [we,wd,wqj,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wqb,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababaab : everyKey (certRow 6 tree6) tree7ababaab = true := by decide +kernel
def tree7ababaa : BinaryTree (List W) := .node [we,wd,wqD,wc,wa,wb,wg,wh] tree7ababaaa tree7ababaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababaa : everyKey (certRow 6 tree6) tree7ababaa = true := splitCheck (by decide +kernel) ok_tree7ababaaa ok_tree7ababaab
def tree7abababa : BinaryTree (List W) := (.node [we,wd,woX,wc,wa,wb,wg,wh] (.node [we,wd,wlD,wc,wa,wb,wg,wh] (.node [we,wd,wo5,wc,wa,wb,wg,wh] (.node [we,wd,wp3,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wmQ,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wjL,wc,wa,wb,wg,wh] (.node [we,wd,wjU,wc,wa,wb,wg,wh] (.node [we,wd,wkc,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wjv,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abababa : everyKey (certRow 6 tree6) tree7abababa = true := by decide +kernel
def tree7abababb : BinaryTree (List W) := (.node [we,wd,wL,wc,wa,wb,wg,w0] (.node [we,wd,wL,wc,wa,wb,wg,w2] (.node [we,wd,wL,wc,wa,wb,wY,wh] (.node [we,wd,wL,wc,wa,wU,wg,wh] .nil .nil) .nil) (.node [we,wd,wL,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wL,wc,wa,wS,wg,wh] (.node [we,wd,wL,wc,wa,wb,wW,wh] .nil .nil) (.node [we,wd,wL,wc,wO,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abababb : everyKey (certRow 6 tree6) tree7abababb = true := by decide +kernel
def tree7ababab : BinaryTree (List W) := .node [we,wd,wL,wc,wQ,wb,wg,wh] tree7abababa tree7abababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababab : everyKey (certRow 6 tree6) tree7ababab = true := splitCheck (by decide +kernel) ok_tree7abababa ok_tree7abababb
def tree7ababa : BinaryTree (List W) := .node [we,wd,wp7,wc,wa,wb,wg,wh] tree7ababaa tree7ababab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababa : everyKey (certRow 6 tree6) tree7ababa = true := splitCheck (by decide +kernel) ok_tree7ababaa ok_tree7ababab
def tree7ababbaa : BinaryTree (List W) := (.node [we,wd,wkv,wc,wa,wb,wg,wh] (.node [we,wd,wiP,wc,wa,wb,wg,wh] (.node [we,wd,wkS,wc,wa,wb,wg,wh] (.node [we,wd,wjf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wiH,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wk7,wc,wa,wb,wg,wh] (.node [we,wd,wl5,wc,wa,wb,wg,wh] (.node [we,wd,wmo,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wij,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababbaa : everyKey (certRow 6 tree6) tree7ababbaa = true := by decide +kernel
def tree7ababbab : BinaryTree (List W) := (.node [we,wd,wbh,wc,wa,wb,wg,wbr] (.node [we,wd,wbh,wc,wa,wb,wg,wbt] (.node [we,wd,wbh,wc,wa,wb,wbp,wh] (.node [we,wd,wbh,wc,wbl,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wbh,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wbh,wc,wbj,wb,wg,wh] (.node [we,wd,wbh,wc,wa,wb,wbn,wh] .nil .nil) (.node [we,wd,wnw,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababbab : everyKey (certRow 6 tree6) tree7ababbab = true := by decide +kernel
def tree7ababba : BinaryTree (List W) := .node [we,wd,wme,wc,wa,wb,wg,wh] tree7ababbaa tree7ababbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababba : everyKey (certRow 6 tree6) tree7ababba = true := splitCheck (by decide +kernel) ok_tree7ababbaa ok_tree7ababbab
def tree7ababbba : BinaryTree (List W) := (.node [we,wd,wf,wtX,wc,wa,wb,wh] (.node [we,wd,wf,ws3,wc,wa,wb,wg] (.node [we,wd,wkE,wc,wa,wb,wg,wh] (.node [we,wd,wnY,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wtZ,wc,wa,wb,wh] .nil .nil)) (.node [we,wd,wf,whB,waO,wb,wg,wh] (.node [we,wd,wf,wgu,waO,wb,wg,wh] (.node [we,wd,wf,whc,waO,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wtQ,wc,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababbba : everyKey (certRow 6 tree6) tree7ababbba = true := by decide +kernel
def tree7ababbbb : BinaryTree (List W) := (.node [we,wd,wf,wqW,wa,wb,wg,wh] (.node [we,wd,wf,wg2,wa,wb,wg,waX] (.node [we,wd,wf,waW,wa,wb,wg,waX] (.node [we,wd,wf,wtv,wc,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wgG,wa,wb,wg,waX] .nil .nil)) (.node [we,wd,wf,waV,wdK,wa,wb,wh] (.node [we,wd,wf,wfa,waQ,wb,wg,wh] .nil .nil) (.node [we,wd,wf,waR,wa,waS,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababbbb : everyKey (certRow 6 tree6) tree7ababbbb = true := by decide +kernel
def tree7ababbb : BinaryTree (List W) := .node [we,wd,wf,wtx,wc,wb,wg,wh] tree7ababbba tree7ababbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababbb : everyKey (certRow 6 tree6) tree7ababbb = true := splitCheck (by decide +kernel) ok_tree7ababbba ok_tree7ababbbb
def tree7ababb : BinaryTree (List W) := .node [we,wd,whY,wc,wa,wb,wg,wh] tree7ababba tree7ababbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ababb : everyKey (certRow 6 tree6) tree7ababb = true := splitCheck (by decide +kernel) ok_tree7ababba ok_tree7ababbb
def tree7abab : BinaryTree (List W) := .node [we,wd,wlt,wc,wa,wb,wg,wh] tree7ababa tree7ababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abab : everyKey (certRow 6 tree6) tree7abab = true := splitCheck (by decide +kernel) ok_tree7ababa ok_tree7ababb
def tree7aba : BinaryTree (List W) := .node [we,wd,wpX,wc,wa,wb,wg,wh] tree7abaa tree7abab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7aba : everyKey (certRow 6 tree6) tree7aba = true := splitCheck (by decide +kernel) ok_tree7abaa ok_tree7abab
def tree7abbaaaa : BinaryTree (List W) := (.node [we,wd,wf,wmq,wa,wb,wg,wh] (.node [we,wd,wf,wna,wa,wb,wg,wh] (.node [we,wd,wf,wmz,wa,wb,wg,wh] (.node [we,wd,wf,wpn,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wo7,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wm0,wa,wb,wg,wh] (.node [we,wd,wf,wmg,wa,wb,wg,wh] (.node [we,wd,wf,woK,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wM,wa,wb,wg,w0] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaaaa : everyKey (certRow 6 tree6) tree7abbaaaa = true := by decide +kernel
def tree7abbaaab : BinaryTree (List W) := (.node [we,wd,wf,wie,wa,wb,wg,wh] (.node [we,wd,wf,wke,wa,wb,wg,wh] (.node [we,wd,wf,wkF,wa,wb,wg,wh] (.node [we,wd,wf,wmS,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wh5,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wjW,wa,wb,wg,wh] (.node [we,wd,wf,wj4,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wi0,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaaab : everyKey (certRow 6 tree6) tree7abbaaab = true := by decide +kernel
def tree7abbaaa : BinaryTree (List W) := .node [we,wd,wf,wk0,wa,wb,wg,wh] tree7abbaaaa tree7abbaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaaa : everyKey (certRow 6 tree6) tree7abbaaa = true := splitCheck (by decide +kernel) ok_tree7abbaaaa ok_tree7abbaaab
def tree7abbaaba : BinaryTree (List W) := (.node [we,wd,wf,wc,wtj,wa,wb,wh] (.node [we,wd,wf,wc,wgE,wa,wb,wh] (.node [we,wd,wf,wc,wtf,wa,wb,wh] (.node [we,wd,wf,wov,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wth,wa,wb,wh] .nil .nil)) (.node [we,wd,wf,wc,wtV,wa,wb,wg] (.node [we,wd,wf,wc,wtT,wa,wb,wh] (.node [we,wd,wf,wc,wtt,wa,wb,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wt3,wa,wb,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaaba : everyKey (certRow 6 tree6) tree7abbaaba = true := by decide +kernel
def tree7abbaabb : BinaryTree (List W) := (.node [we,wd,wf,wc,ws6,wb,wg,wh] (.node [we,wd,wf,wc,wta,wb,wg,wh] (.node [we,wd,wf,wc,wqK,wb,wg,wh] (.node [we,wd,wf,wc,wtd,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,ws8,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa1,wb,wg,wa2] (.node [we,wd,wf,wc,wqI,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wc,whn,wb,wg,wa2] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaabb : everyKey (certRow 6 tree6) tree7abbaabb = true := by decide +kernel
def tree7abbaab : BinaryTree (List W) := .node [we,wd,wf,wc,wts,wa,wb,wh] tree7abbaaba tree7abbaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaab : everyKey (certRow 6 tree6) tree7abbaab = true := splitCheck (by decide +kernel) ok_tree7abbaaba ok_tree7abbaabb
def tree7abbaa : BinaryTree (List W) := .node [we,wd,wf,wiR,wa,wb,wg,wh] tree7abbaaa tree7abbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaa : everyKey (certRow 6 tree6) tree7abbaa = true := splitCheck (by decide +kernel) ok_tree7abbaaa ok_tree7abbaab
def tree7abbabaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wr4,wb,wg,wh] (.node [we,wd,wf,wc,wrx,wb,wg,wh] (.node [we,wd,wf,wc,wsU,wb,wg,wh] (.node [we,wd,wf,wc,wpZ,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wsh,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wp9,wb,wg,wh] (.node [we,wd,wf,wc,wqf,wb,wg,wh] (.node [we,wd,wf,wc,wrH,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wp5,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbabaa : everyKey (certRow 6 tree6) tree7abbabaa = true := by decide +kernel
def tree7abbabab : BinaryTree (List W) := (.node [we,wd,wf,wc,woE,wb,wg,wh] (.node [we,wd,wf,wc,woZ,wb,wg,wh] (.node [we,wd,wf,wc,wo9,wb,wg,wh] (.node [we,wd,wf,wc,wnb,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,woM,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wlG,wb,wg,wh] (.node [we,wd,wf,wc,wox,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wc,wmK,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbabab : everyKey (certRow 6 tree6) tree7abbabab = true := by decide +kernel
def tree7abbaba : BinaryTree (List W) := .node [we,wd,wf,wc,wpp,wb,wg,wh] tree7abbabaa tree7abbabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbaba : everyKey (certRow 6 tree6) tree7abbaba = true := splitCheck (by decide +kernel) ok_tree7abbabaa ok_tree7abbabab
def tree7abbabba : BinaryTree (List W) := (.node [we,wd,wf,wc,wQ,wb,wg,w2] (.node [we,wd,wf,wc,wQ,wU,wg,wh] (.node [we,wd,wf,wc,wl8,wb,wg,wh] (.node [we,wd,wf,wc,wms,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wQ,wb,wY,wh] .nil .nil)) (.node [we,wd,wf,wc,wQ,wb,wW,wh] (.node [we,wd,wf,wc,wQ,wb,wg,w0] (.node [we,wd,wf,wc,wQ,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wQ,wS,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbabba : everyKey (certRow 6 tree6) tree7abbabba = true := by decide +kernel
def tree7abbabbb : BinaryTree (List W) := (.node [we,wd,wf,wc,wbl,wb,wg,wh] (.node [we,wd,wf,wc,wbl,wb,wbp,wh] (.node [we,wd,wf,wc,wk2,wb,wg,wh] (.node [we,wd,wf,wc,wk9,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wbl,wb,wg,wbt] .nil .nil)) (.node [we,wd,wf,wc,wbl,wb,wbn,wh] (.node [we,wd,wf,wc,wbl,wb,wg,wbr] .nil .nil) (.node [we,wd,wf,wc,wnS,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbabbb : everyKey (certRow 6 tree6) tree7abbabbb = true := by decide +kernel
def tree7abbabb : BinaryTree (List W) := .node [we,wd,wf,wc,wlg,wb,wg,wh] tree7abbabba tree7abbabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbabb : everyKey (certRow 6 tree6) tree7abbabb = true := splitCheck (by decide +kernel) ok_tree7abbabba ok_tree7abbabbb
def tree7abbab : BinaryTree (List W) := .node [we,wd,wf,wc,wmB,wb,wg,wh] tree7abbaba tree7abbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbab : everyKey (certRow 6 tree6) tree7abbab = true := splitCheck (by decide +kernel) ok_tree7abbaba ok_tree7abbabb
def tree7abba : BinaryTree (List W) := .node [we,wd,wf,wc,wsZ,wb,wg,wh] tree7abbaa tree7abbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abba : everyKey (certRow 6 tree6) tree7abba = true := splitCheck (by decide +kernel) ok_tree7abbaa ok_tree7abbab
def tree7abbbaaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wjh,wb,wg,wh] (.node [we,wd,wf,wc,wjx,wb,wg,wh] (.node [we,wd,wf,wc,wjF,wb,wg,wh] (.node [we,wd,wf,wc,wkg,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wjo,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wkp,wb,wg,wh] (.node [we,wd,wf,wc,wiS,wb,wg,wh] (.node [we,wd,wf,wc,wi7,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wiA,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbaaa : everyKey (certRow 6 tree6) tree7abbbaaa = true := by decide +kernel
def tree7abbbaab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wtD,wb,wg] (.node [we,wd,wf,wc,wa,wtF,wb,wh] (.node [we,wd,wf,wc,wa,wpK,wb,wh] (.node [we,wd,wf,wc,wa,wtI,wb,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wtB,wb,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wtS,wb,wh] (.node [we,wd,wf,wc,wa,whF,wa4,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wtz,wb,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbaab : everyKey (certRow 6 tree6) tree7abbbaab = true := by decide +kernel
def tree7abbbaa : BinaryTree (List W) := .node [we,wd,wf,wc,wh7,wb,wg,wh] tree7abbbaaa tree7abbbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbaa : everyKey (certRow 6 tree6) tree7abbbaa = true := splitCheck (by decide +kernel) ok_tree7abbbaaa ok_tree7abbbaab
def tree7abbbaba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wo1,wg,wh] (.node [we,wd,wf,wc,wa,wpr,wg,wh] (.node [we,wd,wf,wc,wa,wpS,wg,wh] (.node [we,wd,wf,wc,wa,wdT,wa4,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wpb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wlI,wg,wh] (.node [we,wd,wf,wc,wa,wog,wg,wh] (.node [we,wd,wf,wc,wa,woo,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,waS,wbn,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbaba : everyKey (certRow 6 tree6) tree7abbbaba = true := by decide +kernel
def tree7abbbabb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wjH,wg,wh] (.node [we,wd,wf,wc,wa,wma,wg,wh] (.node [we,wd,wf,wc,wa,wmu,wg,wh] (.node [we,wd,wf,wc,wa,wmM,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wki,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wU,wg,w2] (.node [we,wd,wf,wc,wa,wU,wY,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wU,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbabb : everyKey (certRow 6 tree6) tree7abbbabb = true := by decide +kernel
def tree7abbbab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wnq,wg,wh] tree7abbbaba tree7abbbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbab : everyKey (certRow 6 tree6) tree7abbbab = true := splitCheck (by decide +kernel) ok_tree7abbbaba ok_tree7abbbabb
def tree7abbba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wpW,wg,wh] tree7abbbaa tree7abbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbba : everyKey (certRow 6 tree6) tree7abbba = true := splitCheck (by decide +kernel) ok_tree7abbbaa ok_tree7abbbab
def tree7abbbbaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wim,wg,wh] (.node [we,wd,wf,wc,wa,wjj,wg,wh] (.node [we,wd,wf,wc,wa,wlw,wg,wh] (.node [we,wd,wf,wc,wa,wU,wW,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wlb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wtp,wh] (.node [we,wd,wf,wc,wa,wjO,wg,wh] (.node [we,wd,wf,wc,wa,whS,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wtn,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbbaa : everyKey (certRow 6 tree6) tree7abbbbaa = true := by decide +kernel
def tree7abbbbab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wry,wh] (.node [we,wd,wf,wc,wa,wb,wt2,wh] (.node [we,wd,wf,wc,wa,wb,wsy,wg] (.node [we,wd,wf,wc,wa,wb,wtr,wg] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wsW,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wsN,wh] (.node [we,wd,wf,wc,wa,wb,wlS,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wsL,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbbab : everyKey (certRow 6 tree6) tree7abbbbab = true := by decide +kernel
def tree7abbbba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wtl,wh] tree7abbbbaa tree7abbbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbba : everyKey (certRow 6 tree6) tree7abbbba = true := splitCheck (by decide +kernel) ok_tree7abbbbaa ok_tree7abbbbab
def tree7abbbbba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wr2,wh] (.node [we,wd,wf,wc,wa,wb,wr9,wh] (.node [we,wd,wf,wc,wa,wb,wsf,wh] (.node [we,wd,wf,wc,wa,wb,wsr,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wez,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wrQ,wh] (.node [we,wd,wf,wc,wa,wb,wrY,wh] (.node [we,wd,wf,wc,wa,wb,wrU,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wrK,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbbba : everyKey (certRow 6 tree6) tree7abbbbba = true := by decide +kernel
def tree7abbbbbb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wlK,wh] (.node [we,wd,wf,wc,wa,wb,woP,wh] (.node [we,wd,wf,wc,wa,wb,wpd,wh] (.node [we,wd,wf,wc,wa,wb,wpt,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,woq,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wbp,wh] (.node [we,wd,wf,wc,wa,wb,wbp,wbt] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wbp,wbr] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbbbb : everyKey (certRow 6 tree6) tree7abbbbbb = true := by decide +kernel
def tree7abbbbb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wrA,wh] tree7abbbbba tree7abbbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbbb : everyKey (certRow 6 tree6) tree7abbbbb = true := splitCheck (by decide +kernel) ok_tree7abbbbba ok_tree7abbbbbb
def tree7abbbb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wq5,wh] tree7abbbba tree7abbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbbb : everyKey (certRow 6 tree6) tree7abbbb = true := splitCheck (by decide +kernel) ok_tree7abbbba ok_tree7abbbbb
def tree7abbb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wU,wg,w0] tree7abbba tree7abbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abbb : everyKey (certRow 6 tree6) tree7abbb = true := splitCheck (by decide +kernel) ok_tree7abbba ok_tree7abbbb
def tree7abb : BinaryTree (List W) := .node [we,wd,wf,wc,wnE,wb,wg,wh] tree7abba tree7abbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7abb : everyKey (certRow 6 tree6) tree7abb = true := splitCheck (by decide +kernel) ok_tree7abba ok_tree7abbb
def tree7ab : BinaryTree (List W) := .node [we,wd,wf,waR,wbj,wb,wg,wh] tree7aba tree7abb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ab : everyKey (certRow 6 tree6) tree7ab = true := splitCheck (by decide +kernel) ok_tree7aba ok_tree7abb
def tree7a : BinaryTree (List W) := .node [we,wr5,wv,wc,wa,wb,wg,wh] tree7aa tree7ab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7a : everyKey (certRow 6 tree6) tree7a = true := splitCheck (by decide +kernel) ok_tree7aa ok_tree7ab
def tree7baaaaaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wj7,wh] (.node [we,wd,wf,wc,wa,wb,wm3,wh] (.node [we,wd,wf,wc,wa,wb,wne,wh] (.node [we,wd,wf,wc,wa,wb,wnG,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wmV,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wY,w2] (.node [we,wd,wf,wc,wa,wb,wjQ,wh] (.node [we,wd,wf,wc,wa,wb,wjZ,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wY,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaaaa : everyKey (certRow 6 tree6) tree7baaaaaa = true := by decide +kernel
def tree7baaaaab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wiU,wh] (.node [we,wd,wf,wc,wa,wb,wkV,wh] (.node [we,wd,wf,wc,wa,wb,wja,wh] (.node [we,wd,wf,wc,wa,wb,wlq,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wi2,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wlj,wh] (.node [we,wd,wf,wc,wa,wb,wky,wh] (.node [we,wd,wf,wc,wa,wb,wiK,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wiC,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaaab : everyKey (certRow 6 tree6) tree7baaaaab = true := by decide +kernel
def tree7baaaaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wY,w0] tree7baaaaaa tree7baaaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaaa : everyKey (certRow 6 tree6) tree7baaaaa = true := splitCheck (by decide +kernel) ok_tree7baaaaaa ok_tree7baaaaab
def tree7baaaaba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wbt] (.node [we,wd,wf,wc,wa,wb,wg,woA] (.node [we,wd,wf,wc,wa,wb,wg,wo3] (.node [we,wd,wf,wc,wa,wb,wg,wqM] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,woi] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wm5] (.node [we,wd,wf,wc,wa,wb,wg,wns] (.node [we,wd,wf,wc,wa,wb,wg,wnz] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wmk] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaaba : everyKey (certRow 6 tree6) tree7baaaaba = true := by decide +kernel
def tree7baaaabb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wks] (.node [we,wd,wf,wc,wa,wb,wg,wkI] (.node [we,wd,wf,wc,wa,wb,wg,wkP] (.node [we,wd,wf,wc,wa,wb,wg,wkX] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wkA] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wg,whU] (.node [we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wg,wkH] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaabb : everyKey (certRow 6 tree6) tree7baaaabb = true := by decide +kernel
def tree7baaaab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,w2] tree7baaaaba tree7baaaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaab : everyKey (certRow 6 tree6) tree7baaaab = true := splitCheck (by decide +kernel) ok_tree7baaaaba ok_tree7baaaabb
def tree7baaaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wiu,wh] tree7baaaaa tree7baaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaa : everyKey (certRow 6 tree6) tree7baaaa = true := splitCheck (by decide +kernel) ok_tree7baaaaa ok_tree7baaaab
def tree7baaabaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wkr] (.node [we,wd,wf,wc,wa,wb,wg,wmj] (.node [we,wd,wf,wc,wa,wb,wg,wkO] (.node [we,wd,wf,wc,wa,wb,wg,wh9] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wih] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wnN] (.node [we,wd,wf,wc,wa,wb,wg,wlc] (.node [we,wd,wf,wc,wa,wb,wg,wio] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wm4] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaabaa : everyKey (certRow 6 tree6) tree7baaabaa = true := by decide +kernel
def tree7baaabab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wbr] (.node [we,wd,wf,wc,wa,wb,wg,wn1] (.node [we,wd,wf,wc,wa,wb,wg,wnU] (.node [we,wd,wf,wc,wa,wb,wg,wnr] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wny] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wg,woh] (.node [we,wd,wf,wc,wa,wb,wg,wlk] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wg,woz] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaabab : everyKey (certRow 6 tree6) tree7baaabab = true := by decide +kernel
def tree7baaaba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wiv] tree7baaabaa tree7baaabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaaba : everyKey (certRow 6 tree6) tree7baaaba = true := splitCheck (by decide +kernel) ok_tree7baaabaa ok_tree7baaabab
def tree7baaabba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wjb] (.node [we,wd,wf,wc,wa,wb,wg,wi3] (.node [we,wd,wf,wc,wa,wb,wg,wiV] (.node [we,wd,wf,wc,wa,wb,wg,wiL] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wkW] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wly] (.node [we,wd,wf,wc,wa,wb,wg,wjk] (.node [we,wd,wf,wc,wa,wb,wg,wlr] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,w0] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaabba : everyKey (certRow 6 tree6) tree7baaabba = true := by decide +kernel
def tree7baaabbb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wkj] (.node [we,wd,wf,wc,wa,wb,wg,wj0] (.node [we,wd,wf,wc,wa,wb,wg,wjR] (.node [we,wd,wf,wc,wa,wb,wg,wjI] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wj8] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wro] (.node [we,wd,wf,wc,wa,wb,wg,wo2] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wg,wtq] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaabbb : everyKey (certRow 6 tree6) tree7baaabbb = true := by decide +kernel
def tree7baaabb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wjz] tree7baaabba tree7baaabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaabb : everyKey (certRow 6 tree6) tree7baaabb = true := splitCheck (by decide +kernel) ok_tree7baaabba ok_tree7baaabbb
def tree7baaab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wkz] tree7baaaba tree7baaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaab : everyKey (certRow 6 tree6) tree7baaab = true := splitCheck (by decide +kernel) ok_tree7baaaba ok_tree7baaabb
def tree7baaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wh1] tree7baaaa tree7baaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaa : everyKey (certRow 6 tree6) tree7baaa = true := splitCheck (by decide +kernel) ok_tree7baaaa ok_tree7baaab
def tree7baabaaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wiJ,wh] (.node [we,wd,wf,wc,wa,wb,whT,wh] (.node [we,wd,wf,wc,wa,wb,wg,wsP] (.node [we,wd,wf,wc,wa,wb,wg,wtU] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wit,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wh0,wh] (.node [we,wd,wf,wc,wa,wb,wi1,wh] (.node [we,wd,wf,wc,wa,wb,wiT,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wh8,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabaaa : everyKey (certRow 6 tree6) tree7baabaaa = true := by decide +kernel
def tree7baabaab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,win,wh] (.node [we,wd,wf,wc,wa,wb,wj6,wh] (.node [we,wd,wf,wc,wa,wb,wjY,wh] (.node [we,wd,wf,wc,wa,wb,wjP,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wig,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wjq,wh] (.node [we,wd,wf,wc,wa,wb,wi9,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wop,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabaab : everyKey (certRow 6 tree6) tree7baabaab = true := by decide +kernel
def tree7baabaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wiB,wh] tree7baabaaa tree7baabaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabaa : everyKey (certRow 6 tree6) tree7baabaa = true := splitCheck (by decide +kernel) ok_tree7baabaaa ok_tree7baabaab
def tree7baababa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wnT,wh] (.node [we,wd,wf,wc,wa,wb,wkG,wh] (.node [we,wd,wf,wc,wa,wb,wkx,wh] (.node [we,wd,wf,wc,wa,wb,wnx,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wnF,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wbn,wbt] (.node [we,wd,wf,wc,wa,wb,wnL,wh] (.node [we,wd,wf,wc,wa,wb,wn0,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wbn,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baababa : everyKey (certRow 6 tree6) tree7baababa = true := by decide +kernel
def tree7baababb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wlx,wh] (.node [we,wd,wf,wc,wa,wb,wk4,wh] (.node [we,wd,wf,wc,wa,wb,wmU,wh] (.node [we,wd,wf,wc,wa,wb,wkU,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wli,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wW,w2] (.node [we,wd,wf,wc,wa,wb,wlp,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wW,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baababb : everyKey (certRow 6 tree6) tree7baababb = true := by decide +kernel
def tree7baabab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wbn,wbr] tree7baababa tree7baababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabab : everyKey (certRow 6 tree6) tree7baabab = true := splitCheck (by decide +kernel) ok_tree7baababa ok_tree7baababb
def tree7baaba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wkq,wh] tree7baabaa tree7baabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baaba : everyKey (certRow 6 tree6) tree7baaba = true := splitCheck (by decide +kernel) ok_tree7baabaa ok_tree7baabab
def tree7baabbaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wmv,wh] (.node [we,wd,wf,wc,wa,wb,wmi,wh] (.node [we,wd,wf,wc,wa,wb,wm2,wh] (.node [we,wd,wf,wc,wa,wb,wlJ,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,woO,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wmD,wh] (.node [we,wd,wf,wc,wa,wb,wnd,wh] (.node [we,wd,wf,wc,wa,wb,wpc,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wmN,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabbaa : everyKey (certRow 6 tree6) tree7baabbaa = true := by decide +kernel
def tree7baabbab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wrX,wh] (.node [we,wd,wf,wc,wa,wb,wrP,wh] (.node [we,wd,wf,wc,wa,wb,wrJ,wh] (.node [we,wd,wf,wc,wa,wb,wrz,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wrT,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wey,wh] (.node [we,wd,wf,wc,wa,wb,wr1,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wr8,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabbab : everyKey (certRow 6 tree6) tree7baabbab = true := by decide +kernel
def tree7baabba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wps,wh] tree7baabbaa tree7baabbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabba : everyKey (certRow 6 tree6) tree7baabba = true := splitCheck (by decide +kernel) ok_tree7baabbaa ok_tree7baabbab
def tree7baabbba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wsO,wh] (.node [we,wd,wf,wc,wa,wb,wsM,wh] (.node [we,wd,wf,wc,wa,wb,wsK,wh] (.node [we,wd,wf,wc,wa,wb,wsq,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wlR,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wtk,wh] (.node [we,wd,wf,wc,wa,wb,wrq,wh] (.node [we,wd,wf,wc,wa,wb,wsV,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wtm,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabbba : everyKey (certRow 6 tree6) tree7baabbba = true := by decide +kernel
def tree7baabbbb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wtG,wh] (.node [we,wd,wf,wc,wa,wb,wtE,wh] (.node [we,wd,wf,wc,wa,wb,wtA,wh] (.node [we,wd,wf,wc,wa,wb,wty,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wpJ,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wb,wtW,wh] (.node [we,wd,wf,wc,wa,wb,wtH,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wb,wtY,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabbbb : everyKey (certRow 6 tree6) tree7baabbbb = true := by decide +kernel
def tree7baabbb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wto,wh] tree7baabbba tree7baabbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabbb : everyKey (certRow 6 tree6) tree7baabbb = true := splitCheck (by decide +kernel) ok_tree7baabbba ok_tree7baabbbb
def tree7baabb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wse,wh] tree7baabba tree7baabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baabb : everyKey (certRow 6 tree6) tree7baabb = true := splitCheck (by decide +kernel) ok_tree7baabba ok_tree7baabbb
def tree7baab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wW,w0] tree7baaba tree7baabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baab : everyKey (certRow 6 tree6) tree7baab = true := splitCheck (by decide +kernel) ok_tree7baaba ok_tree7baabb
def tree7baa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wtC] tree7baaa tree7baab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baa : everyKey (certRow 6 tree6) tree7baa = true := splitCheck (by decide +kernel) ok_tree7baaa ok_tree7baab
def tree7babaaaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wjG,wg,wh] (.node [we,wd,wf,wc,wa,wjp,wg,wh] (.node [we,wd,wf,wc,wa,wji,wg,wh] (.node [we,wd,wf,wc,wa,wi8,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wjy,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wj5,wg,wh] (.node [we,wd,wf,wc,wa,wjX,wg,wh] (.node [we,wd,wf,wc,wa,wjN,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wkh,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babaaaa : everyKey (certRow 6 tree6) tree7babaaaa = true := by decide +kernel
def tree7babaaab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wlv,wg,wh] (.node [we,wd,wf,wc,wa,wla,wg,wh] (.node [we,wd,wf,wc,wa,wk3,wg,wh] (.node [we,wd,wf,wc,wa,wkT,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wlh,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wS,wg,wh] (.node [we,wd,wf,wc,wa,wS,wg,w2] (.node [we,wd,wf,wc,wa,wS,wY,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wS,wg,w0] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babaaab : everyKey (certRow 6 tree6) tree7babaaab = true := by decide +kernel
def tree7babaaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wkw,wg,wh] tree7babaaaa tree7babaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babaaa : everyKey (certRow 6 tree6) tree7babaaa = true := splitCheck (by decide +kernel) ok_tree7babaaaa ok_tree7babaaab
def tree7babaaba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wmL,wg,wh] (.node [we,wd,wf,wc,wa,wmt,wg,wh] (.node [we,wd,wf,wc,wa,wmh,wg,wh] (.node [we,wd,wf,wc,wa,wl9,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wmC,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wlH,wg,wh] (.node [we,wd,wf,wc,wa,wmT,wg,wh] (.node [we,wd,wf,wc,wa,wn9,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wm1,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babaaba : everyKey (certRow 6 tree6) tree7babaaba = true := by decide +kernel
def tree7babaabb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wpa,wg,wh] (.node [we,wd,wf,wc,wa,woT,wg,wh] (.node [we,wd,wf,wc,wa,woN,wg,wh] (.node [we,wd,wf,wc,wa,woF,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wo0,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wpq,wg,wh] (.node [we,wd,wf,wc,wa,wnc,wg,wh] .nil .nil) (.node [we,wd,wf,wc,wa,wpR,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babaabb : everyKey (certRow 6 tree6) tree7babaabb = true := by decide +kernel
def tree7babaab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,woy,wg,wh] tree7babaaba tree7babaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babaab : everyKey (certRow 6 tree6) tree7babaab = true := splitCheck (by decide +kernel) ok_tree7babaaba ok_tree7babaabb
def tree7babaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wS,wW,wh] tree7babaaa tree7babaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babaa : everyKey (certRow 6 tree6) tree7babaa = true := splitCheck (by decide +kernel) ok_tree7babaaa ok_tree7babaab
def tree7bababaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wh6,wb,wg,wh] (.node [we,wd,wf,wc,wa,wn,wbn,wh] (.node [we,wd,wf,wc,wa,wn3,wg,wh] (.node [we,wd,wf,wc,wa,wpL,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,whZ,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wis,wb,wg,wh] (.node [we,wd,wf,wc,wik,wb,wg,wh] (.node [we,wd,wf,wc,wif,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wiz,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bababaa : everyKey (certRow 6 tree6) tree7bababaa = true := by decide +kernel
def tree7bababab : BinaryTree (List W) := (.node [we,wd,wf,wc,wkf,wb,wg,wh] (.node [we,wd,wf,wc,wjw,wb,wg,wh] (.node [we,wd,wf,wc,wjn,wb,wg,wh] (.node [we,wd,wf,wc,wjg,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wjE,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wkN,wb,wg,wh] (.node [we,wd,wf,wc,wko,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wc,wk1,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bababab : everyKey (certRow 6 tree6) tree7bababab = true := by decide +kernel
def tree7bababa : BinaryTree (List W) := .node [we,wd,wf,wc,wi6,wb,wg,wh] tree7bababaa tree7bababab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bababa : everyKey (certRow 6 tree6) tree7bababa = true := splitCheck (by decide +kernel) ok_tree7bababaa ok_tree7bababab
def tree7bababba : BinaryTree (List W) := (.node [we,wd,wf,wc,wO,wb,wY,wh] (.node [we,wd,wf,wc,wlu,wb,wg,wh] (.node [we,wd,wf,wc,wlo,wb,wg,wh] (.node [we,wd,wf,wc,wlf,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wO,wU,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wO,wb,wg,w0] (.node [we,wd,wf,wc,wO,wb,wg,wh] (.node [we,wd,wf,wc,wO,wb,wg,w2] .nil .nil) .nil) (.node [we,wd,wf,wc,wO,wb,wW,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bababba : everyKey (certRow 6 tree6) tree7bababba = true := by decide +kernel
def tree7bababbb : BinaryTree (List W) := (.node [we,wd,wf,wc,wnp,wb,wg,wh] (.node [we,wd,wf,wc,wmA,wb,wg,wh] (.node [we,wd,wf,wc,wmr,wb,wg,wh] (.node [we,wd,wf,wc,wl7,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wmJ,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wnK,wb,wg,wh] (.node [we,wd,wf,wc,wnD,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wc,wnR,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bababbb : everyKey (certRow 6 tree6) tree7bababbb = true := by decide +kernel
def tree7bababb : BinaryTree (List W) := .node [we,wd,wf,wc,wO,wS,wg,wh] tree7bababba tree7bababbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bababb : everyKey (certRow 6 tree6) tree7bababb = true := splitCheck (by decide +kernel) ok_tree7bababba ok_tree7bababbb
def tree7babab : BinaryTree (List W) := .node [we,wd,wf,wc,wk8,wb,wg,wh] tree7bababa tree7bababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babab : everyKey (certRow 6 tree6) tree7babab = true := splitCheck (by decide +kernel) ok_tree7bababa ok_tree7bababb
def tree7baba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wpV,wg,wh] tree7babaa tree7babab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7baba : everyKey (certRow 6 tree6) tree7baba = true := splitCheck (by decide +kernel) ok_tree7babaa ok_tree7babab
def tree7babbaaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wbj,wb,wbn,wh] (.node [we,wd,wf,wc,wbj,wb,wg,wh] (.node [we,wd,wf,wc,wbj,wb,wg,wbt] (.node [we,wd,wf,wc,wbj,wb,wbp,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wbj,wb,wg,wbr] .nil .nil)) (.node [we,wd,wf,wc,won,wb,wg,wh] (.node [we,wd,wf,wc,wof,wb,wg,wh] (.node [we,wd,wf,wc,wlF,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wow,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbaaa : everyKey (certRow 6 tree6) tree7babbaaa = true := by decide +kernel
def tree7babbaab : BinaryTree (List W) := (.node [we,wd,wf,wc,wpo,wb,wg,wh] (.node [we,wd,wf,wc,woY,wb,wg,wh] (.node [we,wd,wf,wc,woS,wb,wg,wh] (.node [we,wd,wf,wc,woL,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wo8,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wp8,wb,wg,wh] (.node [we,wd,wf,wc,wp4,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wc,wqe,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbaab : everyKey (certRow 6 tree6) tree7babbaab = true := by decide +kernel
def tree7babbaa : BinaryTree (List W) := .node [we,wd,wf,wc,woD,wb,wg,wh] tree7babbaaa tree7babbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbaa : everyKey (certRow 6 tree6) tree7babbaa = true := splitCheck (by decide +kernel) ok_tree7babbaaa ok_tree7babbaab
def tree7babbaba : BinaryTree (List W) := (.node [we,wd,wf,wc,wqH,wb,wg,wh] (.node [we,wd,wf,wc,wsX,wb,wg,wh] (.node [we,wd,wf,wc,wsT,wb,wg,wh] (.node [we,wd,wf,wc,wrw,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wsY,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,ws9,wb,wg,wh] (.node [we,wd,wf,wc,ws7,wb,wg,wh] (.node [we,wd,wf,wc,ws5,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wqJ,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbaba : everyKey (certRow 6 tree6) tree7babbaba = true := by decide +kernel
def tree7babbabb : BinaryTree (List W) := (.node [we,wd,wf,wc,wb,wtM,wg,wh] (.node [we,wd,wf,wc,wtw,wb,wg,wh] (.node [we,wd,wf,wc,wtu,wb,wg,wh] (.node [we,wd,wf,wc,wtc,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wb,wtK,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wb,wtR,wg,wh] (.node [we,wd,wf,wc,wb,wtP,wg,wh] .nil .nil) (.node [we,wd,wf,wc,wb,wa3,wsy,wg] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbabb : everyKey (certRow 6 tree6) tree7babbabb = true := by decide +kernel
def tree7babbab : BinaryTree (List W) := .node [we,wd,wf,wc,wtb,wb,wg,wh] tree7babbaba tree7babbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbab : everyKey (certRow 6 tree6) tree7babbab = true := splitCheck (by decide +kernel) ok_tree7babbaba ok_tree7babbabb
def tree7babba : BinaryTree (List W) := .node [we,wd,wf,wc,wrG,wb,wg,wh] tree7babbaa tree7babbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babba : everyKey (certRow 6 tree6) tree7babba = true := splitCheck (by decide +kernel) ok_tree7babbaa ok_tree7babbab
def tree7babbbaa : BinaryTree (List W) := (.node [we,wd,wf,wiQ,wa,wb,wg,wh] (.node [we,wd,wf,wid,wa,wb,wg,wh] (.node [we,wd,wf,whR,wa,wb,wg,wh] (.node [we,wd,wf,wc,wb,wsy,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wiI,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wjV,wa,wb,wg,wh] (.node [we,wd,wf,wjM,wa,wb,wg,wh] (.node [we,wd,wf,wiZ,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wj3,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbbaa : everyKey (certRow 6 tree6) tree7babbbaa = true := by decide +kernel
def tree7babbbab : BinaryTree (List W) := (.node [we,wd,wf,wmI,wa,wb,wg,wh] (.node [we,wd,wf,wmp,wa,wb,wg,wh] (.node [we,wd,wf,wl6,wa,wb,wg,wh] (.node [we,wd,wf,wmf,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wkn,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wmZ,wa,wb,wg,wh] (.node [we,wd,wf,wmR,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wf,ws4,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbbab : everyKey (certRow 6 tree6) tree7babbbab = true := by decide +kernel
def tree7babbba : BinaryTree (List W) := .node [we,wd,wf,wkd,wa,wb,wg,wh] tree7babbbaa tree7babbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbba : everyKey (certRow 6 tree6) tree7babbba = true := splitCheck (by decide +kernel) ok_tree7babbbaa ok_tree7babbbab
def tree7babbbba : BinaryTree (List W) := (.node [we,wd,wf,wou,wa,wb,wg,wh] (.node [we,wd,wf,woe,wa,wb,wg,wh] (.node [we,wd,wf,wlE,wa,wb,wg,wh] (.node [we,wd,wf,wnj,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wom,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,woR,wa,wb,wg,wh] (.node [we,wd,wf,woJ,wa,wb,wg,wh] (.node [we,wd,wf,woC,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wo6,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbbba : everyKey (certRow 6 tree6) tree7babbbba = true := by decide +kernel
def tree7babbbbb : BinaryTree (List W) := (.node [we,wd,wf,wq,wa,wb,wg,w0] (.node [we,wd,wf,wqn,wa,wb,wg,wh] (.node [we,wd,wf,wqV,wa,wb,wg,wh] (.node [we,wd,wf,wpm,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wl1,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wa,wb,wn3,wg,wh] (.node [we,wd,wf,wqz,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wf,wa,wb,wg,waY,wqM] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbbbb : everyKey (certRow 6 tree6) tree7babbbbb = true := by decide +kernel
def tree7babbbb : BinaryTree (List W) := .node [we,wd,wf,wpg,wa,wb,wg,wh] tree7babbbba tree7babbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbbb : everyKey (certRow 6 tree6) tree7babbbb = true := splitCheck (by decide +kernel) ok_tree7babbbba ok_tree7babbbbb
def tree7babbb : BinaryTree (List W) := .node [we,wd,wf,wm9,wa,wb,wg,wh] tree7babbba tree7babbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babbb : everyKey (certRow 6 tree6) tree7babbb = true := splitCheck (by decide +kernel) ok_tree7babbba ok_tree7babbbb
def tree7babb : BinaryTree (List W) := .node [we,wd,wf,wc,wb,wsy,wg] tree7babba tree7babbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7babb : everyKey (certRow 6 tree6) tree7babb = true := splitCheck (by decide +kernel) ok_tree7babba ok_tree7babbb
def tree7bab : BinaryTree (List W) := .node [we,wd,wf,wc,wnZ,wb,wg,wh] tree7baba tree7babb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bab : everyKey (certRow 6 tree6) tree7bab = true := splitCheck (by decide +kernel) ok_tree7baba ok_tree7babb
def tree7ba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wil,wg,wh] tree7baa tree7bab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7ba : everyKey (certRow 6 tree6) tree7ba = true := splitCheck (by decide +kernel) ok_tree7baa ok_tree7bab
def tree7bbaaaaa : BinaryTree (List W) := (.node [we,wd,whQ,wc,wa,wb,wg,wh] (.node [we,wd,wf,wa,wn3,wg,wh] (.node [we,wd,wf,wa,wn3,wn,wg,wh] (.node [we,wd,wf,wa,wb,wg,wqM,wh] .nil .nil) .nil) (.node [we,wd,wf,wbj,wb,wn,wg,wh] .nil .nil)) (.node [we,wd,wjK,wc,wa,wb,wg,wh] (.node [we,wd,wii,wc,wa,wb,wg,wh] (.node [we,wd,whX,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wj2,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaaaa : everyKey (certRow 6 tree6) tree7bbaaaaa = true := by decide +kernel
def tree7bbaaaab : BinaryTree (List W) := (.node [we,wd,wjm,wc,wa,wb,wg,wh] (.node [we,wd,wiy,wc,wa,wb,wg,wh] (.node [we,wd,wir,wc,wa,wb,wg,wh] (.node [we,wd,wiY,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wje,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wku,wc,wa,wb,wg,wh] (.node [we,wd,wkb,wc,wa,wb,wg,wh] (.node [we,wd,wjD,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wkD,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaaab : everyKey (certRow 6 tree6) tree7bbaaaab = true := by decide +kernel
def tree7bbaaaa : BinaryTree (List W) := .node [we,wd,wiG,wc,wa,wb,wg,wh] tree7bbaaaaa tree7bbaaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaaa : everyKey (certRow 6 tree6) tree7bbaaaa = true := splitCheck (by decide +kernel) ok_tree7bbaaaaa ok_tree7bbaaaab
def tree7bbaaaba : BinaryTree (List W) := (.node [we,wd,wls,wc,wa,wb,wg,wh] (.node [we,wd,wk6,wc,wa,wb,wg,wh] (.node [we,wd,wkZ,wc,wa,wb,wg,wh] (.node [we,wd,wkR,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wln,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wJ,wc,wa,wb,wY,wh] (.node [we,wd,wJ,wc,wa,wU,wg,wh] (.node [we,wd,wJ,wc,wQ,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wJ,wc,wa,wb,wg,w2] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaaba : everyKey (certRow 6 tree6) tree7bbaaaba = true := by decide +kernel
def tree7bbaaabb : BinaryTree (List W) := (.node [we,wd,wl4,wc,wa,wb,wg,wh] (.node [we,wd,wJ,wc,wa,wS,wg,wh] (.node [we,wd,wJ,wc,wa,wb,wW,wh] (.node [we,wd,wJ,wc,wa,wb,wg,w0] .nil .nil) .nil) (.node [we,wd,wJ,wc,wO,wb,wg,wh] .nil .nil)) (.node [we,wd,wmn,wc,wa,wb,wg,wh] (.node [we,wd,wmd,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wmP,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaabb : everyKey (certRow 6 tree6) tree7bbaaabb = true := by decide +kernel
def tree7bbaaab : BinaryTree (List W) := .node [we,wd,wJ,wc,wa,wb,wg,wh] tree7bbaaaba tree7bbaaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaab : everyKey (certRow 6 tree6) tree7bbaaab = true := splitCheck (by decide +kernel) ok_tree7bbaaaba ok_tree7bbaaabb
def tree7bbaaa : BinaryTree (List W) := .node [we,wd,wkM,wc,wa,wb,wg,wh] tree7bbaaaa tree7bbaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaa : everyKey (certRow 6 tree6) tree7bbaaa = true := splitCheck (by decide +kernel) ok_tree7bbaaaa ok_tree7bbaaab
def tree7bbaabaa : BinaryTree (List W) := (.node [we,wd,wnX,wc,wa,wb,wg,wh] (.node [we,wd,wnC,wc,wa,wb,wg,wh] (.node [we,wd,wnv,wc,wa,wb,wg,wh] (.node [we,wd,wno,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wnJ,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wbf,wc,wa,wb,wbp,wh] (.node [we,wd,wbf,wc,wbl,wb,wg,wh] (.node [we,wd,wbf,waR,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wbf,wc,wa,wb,wg,wbt] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaabaa : everyKey (certRow 6 tree6) tree7bbaabaa = true := by decide +kernel
def tree7bbaabab : BinaryTree (List W) := (.node [we,wd,wlC,wc,wa,wb,wg,wh] (.node [we,wd,wbf,wc,wbj,wb,wg,wh] (.node [we,wd,wbf,wc,wa,wb,wbn,wh] (.node [we,wd,wbf,wc,wa,wb,wg,wbr] .nil .nil) .nil) (.node [we,wd,wbf,wa,wb,wn,wg,wh] .nil .nil)) (.node [we,wd,wol,wc,wa,wb,wg,wh] (.node [we,wd,wod,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wot,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaabab : everyKey (certRow 6 tree6) tree7bbaabab = true := by decide +kernel
def tree7bbaaba : BinaryTree (List W) := .node [we,wd,wbf,wc,wa,wb,wg,wh] tree7bbaabaa tree7bbaabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaaba : everyKey (certRow 6 tree6) tree7bbaaba = true := splitCheck (by decide +kernel) ok_tree7bbaabaa ok_tree7bbaabab
def tree7bbaabba : BinaryTree (List W) := (.node [we,wd,wqa,wc,wa,wb,wg,wh] (.node [we,wd,wp2,wc,wa,wb,wg,wh] (.node [we,wd,wo4,wc,wa,wb,wg,wh] (.node [we,wd,woW,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wp6,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wqk,wc,wa,wb,wg,wh] (.node [we,wd,wqi,wc,wa,wb,wg,wh] (.node [we,wd,wqc,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wpu,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaabba : everyKey (certRow 6 tree6) tree7bbaabba = true := by decide +kernel
def tree7bbaabbb : BinaryTree (List W) := (.node [we,wd,wcH,wc,wa,wb,wg,wh] (.node [we,wd,wqC,wc,wa,wb,wg,wh] (.node [we,wd,wqA,wc,wa,wb,wg,wh] (.node [we,wd,wqu,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wqE,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wq9,wc,wa,wb,wg,wh] (.node [we,wd,wq2,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wrk,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaabbb : everyKey (certRow 6 tree6) tree7bbaabbb = true := by decide +kernel
def tree7bbaabb : BinaryTree (List W) := .node [we,wd,wqo,wc,wa,wb,wg,wh] tree7bbaabba tree7bbaabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaabb : everyKey (certRow 6 tree6) tree7bbaabb = true := splitCheck (by decide +kernel) ok_tree7bbaabba ok_tree7bbaabbb
def tree7bbaab : BinaryTree (List W) := .node [we,wd,woI,wc,wa,wb,wg,wh] tree7bbaaba tree7bbaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaab : everyKey (certRow 6 tree6) tree7bbaab = true := splitCheck (by decide +kernel) ok_tree7bbaaba ok_tree7bbaabb
def tree7bbaa : BinaryTree (List W) := .node [we,wd,wmY,wc,wa,wb,wg,wh] tree7bbaaa tree7bbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaa : everyKey (certRow 6 tree6) tree7bbaa = true := splitCheck (by decide +kernel) ok_tree7bbaaa ok_tree7bbaab
def tree7bbabaaa : BinaryTree (List W) := (.node [we,wd,wrR,wc,wa,wb,wg,wh] (.node [we,wd,wrL,wc,wa,wb,wg,wh] (.node [we,wd,wrE,wc,wa,wb,wg,wh] (.node [we,wd,wpv,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wrN,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wen,wc,wa,wb,wez,wh] (.node [we,wd,wrV,wc,wa,wb,wg,wh] (.node [we,wd,wrZ,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wen,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabaaa : everyKey (certRow 6 tree6) tree7bbabaaa = true := by decide +kernel
def tree7bbabaab : BinaryTree (List W) := (.node [we,wd,wss,wc,wa,wb,wg,wh] (.node [we,wd,wso,wc,wa,wb,wg,wh] (.node [we,wd,wsk,wc,wa,wb,wg,wh] (.node [we,wd,wr6,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wsu,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wgd,wc,wa,waI,wg,wh] (.node [we,wd,we5,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wd,wsC,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabaab : everyKey (certRow 6 tree6) tree7bbabaab = true := by decide +kernel
def tree7bbabaa : BinaryTree (List W) := .node [we,wd,wen,wc,wa,wb,wey,wh] tree7bbabaaa tree7bbabaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabaa : everyKey (certRow 6 tree6) tree7bbabaa = true := splitCheck (by decide +kernel) ok_tree7bbabaaa ok_tree7bbabaab
def tree7bbababa : BinaryTree (List W) := (.node [we,wd,wv,wpg,wa,wb,wg,wh] (.node [we,wd,wv,wc,wa,wb,wg,wpi] (.node [we,wd,wsI,wc,wa,wb,wg,wh] (.node [we,wd,wsG,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wv,wc,wph,wb,wg,wh] .nil .nil)) (.node [we,wd,wc,wsh,waE,wb,wg,wh] (.node [we,wd,wc,wsh,wa,wb,wg,wh] (.node [we,wd,wc,wqz,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wc,wsh,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbababa : everyKey (certRow 6 tree6) tree7bbababa = true := by decide +kernel
def tree7bbababb : BinaryTree (List W) := (.node [we,wd,wqz,waB,wa,wb,wg,wh] (.node [we,wd,wc,wa,wb,wg,wh,wt7] (.node [we,wd,wc,wa,wb,wry,wh] (.node [we,wd,wc,wa,wb,wry,wg,wh] .nil .nil) .nil) (.node [we,wd,wc,waE,wb,weP,wg,wh] .nil .nil)) (.node [we,wd,waB,wa,wb,wcp,wg,wh] (.node [we,wd,wqz,wa,wb,wg,wh] .nil .nil) (.node [we,whO,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbababb : everyKey (certRow 6 tree6) tree7bbababb = true := by decide +kernel
def tree7bbabab : BinaryTree (List W) := .node [we,wd,wc,wa,wb,waL,wry,wh] tree7bbababa tree7bbababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabab : everyKey (certRow 6 tree6) tree7bbabab = true := splitCheck (by decide +kernel) ok_tree7bbababa ok_tree7bbababb
def tree7bbaba : BinaryTree (List W) := .node [we,wd,wsE,wc,wa,wb,wg,wh] tree7bbabaa tree7bbabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbaba : everyKey (certRow 6 tree6) tree7bbaba = true := splitCheck (by decide +kernel) ok_tree7bbabaa ok_tree7bbabab
def tree7bbabbaa : BinaryTree (List W) := (.node [we,wiX,wf,wc,wa,wb,wg,wh] (.node [we,wix,wf,wc,wa,wb,wg,wh] (.node [we,wib,wf,wc,wa,wb,wg,wh] (.node [we,wh4,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wiN,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wjS,wf,wc,wa,wb,wg,wh] (.node [we,wjC,wf,wc,wa,wb,wg,wh] (.node [we,wjt,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wj1,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabbaa : everyKey (certRow 6 tree6) tree7bbabbaa = true := by decide +kernel
def tree7bbabbab : BinaryTree (List W) := (.node [we,wml,wf,wc,wa,wb,wg,wh] (.node [we,wkK,wf,wc,wa,wb,wg,wh] (.node [we,wkC,wf,wc,wa,wb,wg,wh] (.node [we,wkl,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wmb,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wmG,wf,wc,wa,wb,wg,wh] (.node [we,wmy,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wmW,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabbab : everyKey (certRow 6 tree6) tree7bbabbab = true := by decide +kernel
def tree7bbabba : BinaryTree (List W) := .node [we,wj9,wf,wc,wa,wb,wg,wh] tree7bbabbaa tree7bbabbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabba : everyKey (certRow 6 tree6) tree7bbabba = true := splitCheck (by decide +kernel) ok_tree7bbabbaa ok_tree7bbabbab
def tree7bbabbba : BinaryTree (List W) := (.node [we,wnB,wf,wc,wa,wb,wg,wh] (.node [we,wnm,wf,wc,wa,wb,wg,wh] (.node [we,wnh,wf,wc,wa,wb,wg,wh] (.node [we,wm7,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wnu,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wbb,wbh,wc,wa,wb,wg,wh] (.node [we,wnV,wf,wc,wa,wb,wg,wh] (.node [we,wnQ,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wbb,wf,wc,wbl,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabbba : everyKey (certRow 6 tree6) tree7bbabbba = true := by decide +kernel
def tree7bbabbbb : BinaryTree (List W) := (.node [we,wbb,wf,wc,wa,wb,wbn,wh] (.node [we,wbb,wf,wc,wa,wb,wg,wh] (.node [we,wbb,wf,wc,wa,wb,wg,wbt] (.node [we,wbb,wf,wc,wa,wb,wbp,wh] .nil .nil) .nil) (.node [we,wbb,wf,wc,wa,wb,wg,wbr] .nil .nil)) (.node [we,wbb,wf,wc,wbj,wb,wg,wh] (.node [we,wbb,wf,wc,wa,wn,wg,wh] .nil .nil) (.node [we,wbb,wbf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabbbb : everyKey (certRow 6 tree6) tree7bbabbbb = true := by decide +kernel
def tree7bbabbb : BinaryTree (List W) := .node [we,wbb,wf,wc,wa,waS,wg,wh] tree7bbabbba tree7bbabbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabbb : everyKey (certRow 6 tree6) tree7bbabbb = true := splitCheck (by decide +kernel) ok_tree7bbabbba ok_tree7bbabbbb
def tree7bbabb : BinaryTree (List W) := .node [we,wqZ,wf,wc,wa,wb,wg,wh] tree7bbabba tree7bbabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbabb : everyKey (certRow 6 tree6) tree7bbabb = true := splitCheck (by decide +kernel) ok_tree7bbabba ok_tree7bbabbb
def tree7bbab : BinaryTree (List W) := .node [we,whV,wf,wc,wa,wb,wg,wh] tree7bbaba tree7bbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbab : everyKey (certRow 6 tree6) tree7bbab = true := splitCheck (by decide +kernel) ok_tree7bbaba ok_tree7bbabb
def tree7bba : BinaryTree (List W) := .node [we,wd,wrm,wc,wa,wb,wg,wh] tree7bbaa tree7bbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bba : everyKey (certRow 6 tree6) tree7bba = true := splitCheck (by decide +kernel) ok_tree7bbaa ok_tree7bbab
def tree7bbbaaaa : BinaryTree (List W) := (.node [we,woG,wf,wc,wa,wb,wg,wh] (.node [we,wor,wf,wc,wa,wb,wg,wh] (.node [we,woj,wf,wc,wa,wb,wg,wh] (.node [we,wob,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,woB,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wpe,wf,wc,wa,wb,wg,wh] (.node [we,woU,wf,wc,wa,wb,wg,wh] (.node [we,woQ,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wpl,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaaaa : everyKey (certRow 6 tree6) tree7bbbaaaa = true := by decide +kernel
def tree7bbbaaab : BinaryTree (List W) := (.node [we,wbv,wf,wc,wa,wb,wg,wh] (.node [we,wpE,wf,wc,wa,wb,wg,wh] (.node [we,wpC,wf,wc,wa,wb,wg,wh] (.node [we,wpA,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wpG,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wpT,wf,wc,wa,wb,wg,wh] (.node [we,wpP,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wq7,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaaab : everyKey (certRow 6 tree6) tree7bbbaaab = true := by decide +kernel
def tree7bbbaaa : BinaryTree (List W) := .node [we,wpy,wf,wc,wa,wb,wg,wh] tree7bbbaaaa tree7bbbaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaaa : everyKey (certRow 6 tree6) tree7bbbaaa = true := splitCheck (by decide +kernel) ok_tree7bbbaaaa ok_tree7bbbaaab
def tree7bbbaaba : BinaryTree (List W) := (.node [we,wri,wf,wc,wa,wb,wg,wh] (.node [we,wqg,wf,wc,wa,wb,wg,wh] (.node [we,wfJ,wf,wM,wa,wb,wg,wh] (.node [we,wre,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wrh,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wu,wf,wc,wa,wS,wg,wh] (.node [we,wu,wf,wc,wa,wb,wW,wh] (.node [we,wu,wf,wc,wa,wb,wg,w0] .nil .nil) .nil) (.node [we,wu,wf,wc,wO,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaaba : everyKey (certRow 6 tree6) tree7bbbaaba = true := by decide +kernel
def tree7bbbaabb : BinaryTree (List W) := (.node [we,wlW,wv,wc,wa,wb,wg,wh] (.node [we,wsm,wf,wc,wa,wb,wg,wh] (.node [we,wsi,wf,wc,wa,wb,wg,wh] (.node [we,wsc,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wqU,wv,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wL,wv,wc,wa,wb,wg,wh] (.node [we,wcJ,wqG,wc,wa,wb,wg,wh] .nil .nil) (.node [we,wf,wgf,wc,wa,wb,waw,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaabb : everyKey (certRow 6 tree6) tree7bbbaabb = true := by decide +kernel
def tree7bbbaab : BinaryTree (List W) := .node [we,wsa,wf,wc,wa,wb,wg,wh] tree7bbbaaba tree7bbbaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaab : everyKey (certRow 6 tree6) tree7bbbaab = true := splitCheck (by decide +kernel) ok_tree7bbbaaba ok_tree7bbbaabb
def tree7bbbaa : BinaryTree (List W) := .node [we,wrb,wf,wc,wa,wb,wg,wh] tree7bbbaaa tree7bbbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaa : everyKey (certRow 6 tree6) tree7bbbaa = true := splitCheck (by decide +kernel) ok_tree7bbbaaa ok_tree7bbbaab
def tree7bbbabaa : BinaryTree (List W) := (.node [we,wf,wqG,wc,wa,wb,wg,wh] (.node [we,wf,wf5,wM,wa,wb,wg,wh] (.node [we,wf,ws0,wc,wa,wb,wg,wh] (.node [we,wf,wsR,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wf,wqw,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wf,wv,wc,wa,wS,wg,wh] (.node [we,wf,wv,wc,wa,wb,wW,wh] (.node [we,wf,wv,wc,wa,wb,wg,w0] .nil .nil) .nil) (.node [we,wf,wc,wl1,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbabaa : everyKey (certRow 6 tree6) tree7bbbabaa = true := by decide +kernel
def tree7bbbabab : BinaryTree (List W) := (.node [we,wf,wc,wa,wb,wax,wq5,wh] (.node [we,wf,wc,wr4,wj,wb,wg,wh] (.node [we,wf,wc,wr4,wa,wb,wg,wh] (.node [we,wf,wc,wq,wa,wS,wg,wh] .nil .nil) .nil) (.node [we,wf,wc,wr4,wb,wg,wh] .nil .nil)) (.node [we,wf,wc,wa,wb,wq5,wh] (.node [we,wf,wc,wa,wb,wq5,wg,wh] .nil .nil) (.node [we,wf,wc,wa,wb,wg,waA,w0] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbabab : everyKey (certRow 6 tree6) tree7bbbabab = true := by decide +kernel
def tree7bbbaba : BinaryTree (List W) := .node [we,wf,wc,wq,wa,wb,wW,wh] tree7bbbabaa tree7bbbabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbaba : everyKey (certRow 6 tree6) tree7bbbaba = true := splitCheck (by decide +kernel) ok_tree7bbbabaa ok_tree7bbbabab
def tree7bbbabba : BinaryTree (List W) := (.node [we,wf,wc,wa,wb,wg,wsP] (.node [we,wf,wc,wa,wb,wg,wh,wt5] (.node [we,wf,wc,wa,wb,wg,wh,wt1] (.node [we,wf,wc,wa,wb,wg,wh,wqQ] .nil .nil) .nil) (.node [we,wf,wc,wa,wb,wg,wh,wsP] .nil .nil)) (.node [we,wf,wl1,wq,wa,wb,wg,wh] (.node [we,wf,wc,wa,wS,wg,waA,wh] (.node [we,wf,wc,wa,wb,wW,waA,wh] .nil .nil) .nil) (.node [we,wf,wl1,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbabba : everyKey (certRow 6 tree6) tree7bbbabba = true := by decide +kernel
def tree7bbbabbb : BinaryTree (List W) := (.node [wiM,wd,wf,wc,wa,wb,wg,wh] (.node [wiw,wd,wf,wc,wa,wb,wg,wh] (.node [wip,wd,wf,wc,wa,wb,wg,wh] (.node [wh2,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wiD,wd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wi4,wd,wf,wc,wa,wb,wg,wh] (.node [wiW,wd,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [wjc,wd,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbabbb : everyKey (certRow 6 tree6) tree7bbbabbb = true := by decide +kernel
def tree7bbbabb : BinaryTree (List W) := .node [we,wv,wc,wa,wb,wg,wh,wsA] tree7bbbabba tree7bbbabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbabb : everyKey (certRow 6 tree6) tree7bbbabb = true := splitCheck (by decide +kernel) ok_tree7bbbabba ok_tree7bbbabbb
def tree7bbbab : BinaryTree (List W) := .node [we,wf,wc,wa,wb,wg,waA,wsP] tree7bbbaba tree7bbbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbab : everyKey (certRow 6 tree6) tree7bbbab = true := splitCheck (by decide +kernel) ok_tree7bbbaba ok_tree7bbbabb
def tree7bbba : BinaryTree (List W) := .node [we,wf,wrv,wc,wa,wb,wg,wh] tree7bbbaa tree7bbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbba : everyKey (certRow 6 tree6) tree7bbba = true := splitCheck (by decide +kernel) ok_tree7bbbaa ok_tree7bbbab
def tree7bbbbaaa : BinaryTree (List W) := (.node [wkB,wd,wf,wc,wa,wb,wg,wh] (.node [wkk,wd,wf,wc,wa,wb,wg,wh] (.node [wjA,wd,wf,wc,wa,wb,wg,wh] (.node [wjr,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wkt,wd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wkY,wd,wf,wc,wa,wb,wg,wh] (.node [wkQ,wd,wf,wc,wa,wb,wg,wh] (.node [wkJ,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wk5,wd,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbaaa : everyKey (certRow 6 tree6) tree7bbbbaaa = true := by decide +kernel
def tree7bbbbaab : BinaryTree (List W) := (.node [wD,wd,wf,wc,wa,wb,wY,wh] (.node [wD,wd,wf,wc,wQ,wb,wg,wh] (.node [wD,wd,wL,wc,wa,wb,wg,wh] (.node [wll,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wD,wd,wf,wc,wa,wU,wg,wh] .nil .nil)) (.node [wD,wd,wf,wc,wa,wb,wg,wh] (.node [wD,wd,wf,wc,wa,wb,wg,w2] .nil .nil) (.node [wD,wd,wf,wc,wa,wb,wg,w0] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbaab : everyKey (certRow 6 tree6) tree7bbbbaab = true := by decide +kernel
def tree7bbbbaa : BinaryTree (List W) := .node [wld,wd,wf,wc,wa,wb,wg,wh] tree7bbbbaaa tree7bbbbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbaa : everyKey (certRow 6 tree6) tree7bbbbaa = true := splitCheck (by decide +kernel) ok_tree7bbbbaaa ok_tree7bbbbaab
def tree7bbbbaba : BinaryTree (List W) := (.node [wmw,wd,wf,wc,wa,wb,wg,wh] (.node [wD,wd,wJ,wc,wa,wb,wg,wh] (.node [wD,wd,wf,wc,wO,wb,wg,wh] (.node [wD,wd,wf,wc,wa,wS,wg,wh] .nil .nil) .nil) (.node [wl3,wd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wm6,wd,wf,wc,wa,wb,wg,wh] (.node [wmO,wd,wf,wc,wa,wb,wg,wh] (.node [wmE,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wnf,wl,wd,wf,wc,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbaba : everyKey (certRow 6 tree6) tree7bbbbaba = true := by decide +kernel
def tree7bbbbabb : BinaryTree (List W) := (.node [wa8,wbd,wf,wc,wa,wb,wg,wh] (.node [wnH,wd,wf,wc,wa,wb,wg,wh] (.node [wnA,wd,wf,wc,wa,wb,wg,wh] (.node [wnt,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wnO,wd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wa8,wd,wf,wc,wbl,wb,wg,wh] (.node [wa8,wd,wbh,wc,wa,wb,wg,wh] .nil .nil) (.node [wa8,wd,wf,wc,wa,wb,wbp,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbabb : everyKey (certRow 6 tree6) tree7bbbbabb = true := by decide +kernel
def tree7bbbbab : BinaryTree (List W) := .node [wnl,wd,wf,wc,wa,wb,wg,wh] tree7bbbbaba tree7bbbbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbab : everyKey (certRow 6 tree6) tree7bbbbab = true := splitCheck (by decide +kernel) ok_tree7bbbbaba ok_tree7bbbbabb
def tree7bbbba : BinaryTree (List W) := .node [wD,wd,wf,wc,wa,wb,wW,wh] tree7bbbbaa tree7bbbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbba : everyKey (certRow 6 tree6) tree7bbbba = true := splitCheck (by decide +kernel) ok_tree7bbbbaa ok_tree7bbbbab
def tree7bbbbbaa : BinaryTree (List W) := (.node [wa8,wd,wbf,wc,wa,wb,wg,wh] (.node [wa8,wd,wf,wc,wa,wb,wbn,wh] (.node [wa8,wd,wf,wc,wa,wb,wg,wbr] (.node [wa8,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wa8,wd,wf,wc,wbj,wb,wg,wh] .nil .nil)) (.node [wlA,wx,wf,wc,wa,wb,wg,wh] (.node [wn7,wd,wf,wc,wa,wb,wg,wh] (.node [wa8,wbb,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wlA,wd,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbbaa : everyKey (certRow 6 tree6) tree7bbbbbaa = true := by decide +kernel
def tree7bbbbbab : BinaryTree (List W) := (.node [wrt,wd,wf,wc,wa,wb,wg,wh] (.node [wqs,wd,wf,wc,wa,wb,wg,wh] (.node [wqq,wd,wf,wc,wa,wb,wg,wh] (.node [wpw,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wq0,wd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wqY,wd,wf,wc,wa,wb,wg,wh] (.node [wlL,wu,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [wqY,wu,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbbab : everyKey (certRow 6 tree6) tree7bbbbbab = true := by decide +kernel
def tree7bbbbba : BinaryTree (List W) := .node [wpj,wd,wf,wc,wa,wb,wg,wh] tree7bbbbbaa tree7bbbbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbba : everyKey (certRow 6 tree6) tree7bbbbba = true := splitCheck (by decide +kernel) ok_tree7bbbbbaa ok_tree7bbbbbab
def tree7bbbbbba : BinaryTree (List W) := (.node [wd,wf,wc,wa,wbG,wae,wg,wh] (.node [wd,wpX,wc,wa,wb,wg,wh] (.node [wd,wpX,wf,wc,wa,wb,wg,wh] (.node [wd,w8,wpX,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wd,wf,wc,wqn,wa,wb,wg,wh] .nil .nil)) (.node [wd,wf,wc,wa,wb,wg,wrq,wh] (.node [wd,wf,wc,wa,wb,waj,wrq,wh] (.node [wd,wf,wc,wa,wb,wpL,wg,wh] .nil .nil) .nil) (.node [wd,wf,wc,wa,wb,wg,wam,wro] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbbba : everyKey (certRow 6 tree6) tree7bbbbbba = true := by decide +kernel
def tree7bbbbbbb : BinaryTree (List W) := (.node [wd,wf,wqn,wr,wa,wb,wg,wh] (.node [wd,wf,wc,wa,wpL,wae,wg,wh] (.node [wd,wf,wc,wa,wb,wrq,wh] (.node [wd,wf,wc,wa,wb,wg,wro] .nil .nil) .nil) (.node [wd,wf,wc,wa,wpL,wg,wh] .nil .nil)) (.node [wd,wf,wr,wa,wb,wg,wqm,wh] (.node [wd,wf,wqn,wa,wb,wg,wh] .nil .nil) (.node [wu,wf,wc,wa,wb,wg,wh,wqX] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbbbb : everyKey (certRow 6 tree6) tree7bbbbbbb = true := by decide +kernel
def tree7bbbbbb : BinaryTree (List W) := .node [wd,wf,wc,wa,wb,wg,wh,wro] tree7bbbbbba tree7bbbbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbbb : everyKey (certRow 6 tree6) tree7bbbbbb = true := splitCheck (by decide +kernel) ok_tree7bbbbbba ok_tree7bbbbbbb
def tree7bbbbb : BinaryTree (List W) := .node [wqY,wf,wc,wa,wb,wg,wh] tree7bbbbba tree7bbbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbbb : everyKey (certRow 6 tree6) tree7bbbbb = true := splitCheck (by decide +kernel) ok_tree7bbbbba ok_tree7bbbbbb
def tree7bbbb : BinaryTree (List W) := .node [wa8,wd,wf,wc,wa,wb,wg,wbt] tree7bbbba tree7bbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbbb : everyKey (certRow 6 tree6) tree7bbbb = true := splitCheck (by decide +kernel) ok_tree7bbbba ok_tree7bbbbb
def tree7bbb : BinaryTree (List W) := .node [wjl,wd,wf,wc,wa,wb,wg,wh] tree7bbba tree7bbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bbb : everyKey (certRow 6 tree6) tree7bbb = true := splitCheck (by decide +kernel) ok_tree7bbba ok_tree7bbbb
def tree7bb : BinaryTree (List W) := .node [we,wn8,wf,wc,wa,wb,wg,wh] tree7bba tree7bbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7bb : everyKey (certRow 6 tree6) tree7bb = true := splitCheck (by decide +kernel) ok_tree7bba ok_tree7bbb
def tree7b : BinaryTree (List W) := .node [we,wd,wf,wa,wb,wg,wqM] tree7ba tree7bb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7b : everyKey (certRow 6 tree6) tree7b = true := splitCheck (by decide +kernel) ok_tree7ba ok_tree7bb
def tree7 : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wnM,wh] tree7a tree7b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree7 : everyKey (certRow 6 tree6) tree7 = true := splitCheck (by decide +kernel) ok_tree7a ok_tree7b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem closed7 : Closed 7 tree7 := checkedLayer 6 (by decide) _ _ closed6 ok_tree7
def tree8aaaaaa : BinaryTree (List W) := (.node [wR,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbe,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbF,we,wd,wf,wc,wa,wb,wg,wh] (.node [wG,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) (.node [wa7,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [wC,we,wd,wf,wc,wa,wb,wg,wh] (.node [wby,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [weO,we,wd,wf,wc,wa,wb,wg,wh] (.node [wet,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbs,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wI,we,wd,wf,wc,wa,wb,wg,wh] (.node [wfb,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaaaa : everyKey (certRow 7 tree7) tree8aaaaaa = true := by decide +kernel
def tree8aaaaab : BinaryTree (List W) := (.node [wds,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcR,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcs,we,wd,wf,wc,wa,wb,wg,wh] (.node [w1,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [weE,we,wd,wf,wc,wa,wb,wg,wh] (.node [wei,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wP,we,wd,wf,wc,wa,wb,wg,wh] (.node [wea,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdz,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wbo,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbi,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaaab : everyKey (certRow 7 tree7) tree8aaaaab = true := by decide +kernel
def tree8aaaaa : BinaryTree (List W) := .node [wV,we,wd,wf,wc,wa,wb,wg,wh] tree8aaaaaa tree8aaaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaaa : everyKey (certRow 7 tree7) tree8aaaaa = true := splitCheck (by decide +kernel) ok_tree8aaaaaa ok_tree8aaaaab
def tree8aaaaba : BinaryTree (List W) := (.node [wp,way,we,wf,wc,wa,wb,wg,wh] (.node [wK,we,wd,wf,wc,wa,wb,wg,wh] (.node [wX,we,wd,wf,wc,wa,wb,wg,wh] (.node [wZ,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wE,we,wd,wf,wc,wa,wb,wg,wh] (.node [wT,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wp,we,w5,wf,wc,wa,wb,wg,wh] (.node [wp,we,wao,wf,wc,wa,wb,wg,wh] (.node [wp,wF,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wp,we,wd,wL,wc,wa,wb,wg,wh] (.node [wp,we,wH,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaaba : everyKey (certRow 7 tree7) tree8aaaaba = true := by decide +kernel
def tree8aaaabb : BinaryTree (List W) := (.node [wp,we,wd,wf,wc,wa,wb,wg,w0] (.node [wp,we,wd,wf,wc,wa,wb,wY,wh] (.node [wp,we,wd,wf,wc,wa,wU,wg,wh] (.node [wp,we,wd,wf,wc,wQ,wb,wg,wh] .nil .nil) .nil) (.node [wp,we,wd,wf,wc,wa,wb,wg,wh] (.node [wp,we,wd,wf,wc,wa,wb,wg,w2] .nil .nil) .nil)) (.node [wp,we,wd,wf,wc,wO,wb,wg,wh] (.node [wp,we,wd,wf,wc,wa,wS,wg,wh] (.node [wp,we,wd,wf,wc,wa,wb,wW,wh] .nil .nil) .nil) (.node [wp,we,wd,wJ,wc,wa,wb,wg,wh] (.node [wp,we,wd,wf,wq,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaabb : everyKey (certRow 7 tree7) tree8aaaabb = true := by decide +kernel
def tree8aaaab : BinaryTree (List W) := .node [wp,we,wd,wf,wM,wa,wb,wg,wh] tree8aaaaba tree8aaaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaab : everyKey (certRow 7 tree7) tree8aaaab = true := splitCheck (by decide +kernel) ok_tree8aaaaba ok_tree8aaaabb
def tree8aaaa : BinaryTree (List W) := .node [wN,we,wd,wf,wc,wa,wb,wg,wh] tree8aaaaa tree8aaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaa : everyKey (certRow 7 tree7) tree8aaaa = true := splitCheck (by decide +kernel) ok_tree8aaaaa ok_tree8aaaab
def tree8aaabaa : BinaryTree (List W) := (.node [wde,we,wd,wf,wc,wa,wb,wg,wh] (.node [wp,we,wf,wc,wa,wb,wg,waA,wh] (.node [wp,we,wf,wc,wq,wa,wb,wg,wh] (.node [wp,we,wf,wv,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wp,wD,wd,wf,wc,wa,wb,wg,wh] (.node [wp,we,wf,wq,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wcw,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdU,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdN,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [weA,we,wd,wf,wc,wa,wb,wg,wh] (.node [wee,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaabaa : everyKey (certRow 7 tree7) tree8aaabaa = true := by decide +kernel
def tree8aaabab : BinaryTree (List W) := (.node [wbc,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbm,we,wd,wf,wc,wa,wb,wg,wh] (.node [waZ,we,wl,wd,wf,wc,wb,wg,wh] (.node [weV,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wbq,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbk,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wm,wba,wd,wf,wc,wa,wb,wg,wh] (.node [wa9,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbg,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wm,we,wd,wbh,wc,wa,wb,wg,wh] (.node [wm,we,wbd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaabab : everyKey (certRow 7 tree7) tree8aaabab = true := by decide +kernel
def tree8aaaba : BinaryTree (List W) := .node [wbZ,we,wd,wf,wc,wa,wb,wg,wh] tree8aaabaa tree8aaabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaaba : everyKey (certRow 7 tree7) tree8aaaba = true := splitCheck (by decide +kernel) ok_tree8aaabaa ok_tree8aaabab
def tree8aaabba : BinaryTree (List W) := (.node [wm,we,wd,wf,wc,wa,wb,wg,wbr] (.node [wm,we,wd,wf,wc,wa,wb,wbp,wh] (.node [wm,we,wd,wf,wc,wa,waS,wg,wh] (.node [wm,we,wd,wf,wc,wbl,wb,wg,wh] .nil .nil) .nil) (.node [wm,we,wd,wf,wc,wa,wb,wg,wh] (.node [wm,we,wd,wf,wc,wa,wb,wg,wbt] .nil .nil) .nil)) (.node [wm,we,wd,wf,wc,wbj,wb,wg,wh] (.node [wm,we,wd,wf,wc,wa,wn,wg,wh] (.node [wm,we,wd,wf,wc,wa,wb,wbn,wh] .nil .nil) .nil) (.node [wm,we,wd,wf,wa,wn,wg,wh] (.node [wm,we,wd,wf,wa,wb,wn,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaabba : everyKey (certRow 7 tree7) tree8aaabba = true := by decide +kernel
def tree8aaabbb : BinaryTree (List W) := (.node [way,we,wd,wf,wc,wa,wb,wg,wh] (.node [waT,wz,we,wd,wf,wc,wa,wb,wh] (.node [wm,wa8,wd,wf,wc,wa,wb,wg,wh] (.node [wm,we,wbb,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [way,we,wx,wf,wc,wa,wb,wg,wh] (.node [way,ww,we,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wb6,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbN,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbJ,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wah,we,wd,wf,wc,wa,wb,wg,wh] (.node [wah,wz,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaabbb : everyKey (certRow 7 tree7) tree8aaabbb = true := by decide +kernel
def tree8aaabb : BinaryTree (List W) := .node [wm,we,wd,wbf,wc,wa,wb,wg,wh] tree8aaabba tree8aaabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaabb : everyKey (certRow 7 tree7) tree8aaabb = true := splitCheck (by decide +kernel) ok_tree8aaabba ok_tree8aaabbb
def tree8aaab : BinaryTree (List W) := .node [wm,we,wd,wf,waR,wa,wb,wg,wh] tree8aaaba tree8aaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaab : everyKey (certRow 7 tree7) tree8aaab = true := splitCheck (by decide +kernel) ok_tree8aaaba ok_tree8aaabb
def tree8aaa : BinaryTree (List W) := .node [wp,we,wu,wf,wc,wa,wb,wg,wh] tree8aaaa tree8aaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaa : everyKey (certRow 7 tree7) tree8aaa = true := splitCheck (by decide +kernel) ok_tree8aaaa ok_tree8aaab
def tree8aabaaa : BinaryTree (List W) := (.node [wfX,we,wd,wf,wc,wa,wb,wg,wh] (.node [wgC,we,wd,wf,wc,wr,wa,wb,wh] (.node [wak,we,wd,wf,wc,wa,wb,wg,wh] (.node [wak,wA,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wgC,we,wd,wf,wc,wa,wb,wh] (.node [wgC,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wbw,we,wd,wf,wc,wa,wb,wg,wh] (.node [wgj,we,wd,wf,wc,wa,wb,wg,wh] (.node [waH,we,wd,wv,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wcI,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbV,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabaaa : everyKey (certRow 7 tree7) tree8aabaaa = true := by decide +kernel
def tree8aabaab : BinaryTree (List W) := (.node [wbA,we,wd,wf,wc,wa,wb,wg,wh] (.node [wda,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbu,we,wd,wf,wc,wa,wb,wg,wh] (.node [wb4,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wbL,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbP,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wo,waf,wd,wf,wc,wa,wb,wg,wh] (.node [wbH,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbD,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wo,we,wd,wf,wc,wa,wag,wg,wh] (.node [wo,we,wbx,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabaab : everyKey (certRow 7 tree7) tree8aabaab = true := by decide +kernel
def tree8aabaa : BinaryTree (List W) := .node [wbT,we,wd,wf,wc,wa,wb,wg,wh] tree8aabaaa tree8aabaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabaa : everyKey (certRow 7 tree7) tree8aabaa = true := splitCheck (by decide +kernel) ok_tree8aabaaa ok_tree8aabaab
def tree8aababa : BinaryTree (List W) := (.node [wbR,we,wd,wf,wc,wa,wb,wg,wh] (.node [wo,wd,wf,wc,wa,wb,wae,wg,wh] (.node [wo,we,wbv,wf,wc,wa,wb,wg,wh] (.node [wo,we,wd,wf,wc,wa,wae,wg,wh] .nil .nil) .nil) (.node [wgy,we,wd,wf,wc,wa,wb,wg,wh] (.node [wo,wd,wf,wc,wa,wae,wg,wh] .nil .nil) .nil)) (.node [wcc,we,wd,wf,wc,wa,wb,wg,wh] (.node [wbX,we,wd,wf,wc,wa,wb,wg,wh] (.node [wc1,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wb1,we,wd,wf,wc,wa,wb,wg,wh] (.node [wb8,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aababa : everyKey (certRow 7 tree7) tree8aababa = true := by decide +kernel
def tree8aababb : BinaryTree (List W) := (.node [wy,wd,w8,wf,wc,wa,wb,wg,wh] (.node [wy,we,wd,w8,wc,wa,wb,wg,wh] (.node [wy,wA,wd,wf,wc,wa,wb,wg,wh] (.node [wy,waf,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wy,we,wd,w7,wc,wa,wb,wg,wh] (.node [wy,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wy,wd,wf,wc,wa,wb,wg,wh,wal] (.node [wy,wd,wf,wc,wa,wb,wae,wg,wh] (.node [wy,wd,w8,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wcl,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdY,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aababb : everyKey (certRow 7 tree7) tree8aababb = true := by decide +kernel
def tree8aabab : BinaryTree (List W) := .node [wy,w6,wd,wf,wc,wa,wb,wg,wh] tree8aababa tree8aababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabab : everyKey (certRow 7 tree7) tree8aabab = true := splitCheck (by decide +kernel) ok_tree8aababa ok_tree8aababb
def tree8aaba : BinaryTree (List W) := .node [wo,we,wd,wf,wc,wa,wb,wg,wh] tree8aabaa tree8aabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aaba : everyKey (certRow 7 tree7) tree8aaba = true := splitCheck (by decide +kernel) ok_tree8aabaa ok_tree8aabab
def tree8aabbaa : BinaryTree (List W) := (.node [wcX,we,wd,wf,wc,wa,wb,wg,wh] (.node [wc6,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcC,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcg,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wfh,we,wd,wf,wc,wa,wb,wg,wh] (.node [wd6,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wce,we,wd,wf,wc,wa,wb,wg,wh] (.node [wgL,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdZ,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wdJ,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcA,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabbaa : everyKey (certRow 7 tree7) tree8aabbaa = true := by decide +kernel
def tree8aabbab : BinaryTree (List W) := (.node [wcM,we,wd,wf,wc,wa,wb,wg,wh] (.node [wfH,we,wd,wf,wc,wa,wb,wg,wh] (.node [w9,wd,wf,wr,wa,wb,wg,wh] (.node [w9,wd,wf,wc,wr,wa,wb,wg,wh] .nil .nil) .nil) (.node [wcn,we,wd,wf,wc,wa,wb,wg,wh] (.node [whr,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wcj,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcu,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcy,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [ws,we,wd,waC,wc,wa,wb,wg,wh] (.node [wcq,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabbab : everyKey (certRow 7 tree7) tree8aabbab = true := by decide +kernel
def tree8aabba : BinaryTree (List W) := .node [w9,we,wd,wf,wr,wa,wb,wg,wh] tree8aabbaa tree8aabbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabba : everyKey (certRow 7 tree7) tree8aabba = true := splitCheck (by decide +kernel) ok_tree8aabbaa ok_tree8aabbab
def tree8aabbba : BinaryTree (List W) := (.node [whx,we,wd,wf,wc,wa,wb,wg,wh] (.node [ws,we,wd,wc,waB,wa,wb,wg,wh] (.node [ws,we,wd,wf,waB,wa,wb,wg,wh] (.node [ws,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wf3,we,wd,wf,wc,wa,wb,wg,wh] (.node [ws,we,wd,waB,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wcP,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcF,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcT,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wt,we,wd,wf,waW,wa,wb,wg,wh] (.node [wt,we,wd,wcJ,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabbba : everyKey (certRow 7 tree7) tree8aabbba = true := by decide +kernel
def tree8aabbbb : BinaryTree (List W) := (.node [wt,we,wd,wf,wr,wa,wb,wg,wh] (.node [wt,we,wd,wf,wc,wa,wb,wg,waY] (.node [wt,we,wd,wf,wM,wa,wb,wg,wh] (.node [wt,we,wd,wf,wab,wa,wb,wg,wh] .nil .nil) .nil) (.node [wt,we,wd,wf,wc,wa,wb,wg,waX] (.node [wt,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wt,we,wd,wf,wa,wb,wg,waY] (.node [wt,we,wd,wf,waB,wa,wb,wg,wh] (.node [wt,we,wd,wf,wq,wa,wb,wg,wh] .nil .nil) .nil) (.node [wt,we,wd,wcH,wc,wa,wb,wg,wh] (.node [wt,we,wd,wf,wa,wb,wg,waY,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabbbb : everyKey (certRow 7 tree7) tree8aabbbb = true := by decide +kernel
def tree8aabbb : BinaryTree (List W) := .node [wt,we,wd,wf,waD,wa,wb,wg,wh] tree8aabbba tree8aabbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabbb : everyKey (certRow 7 tree7) tree8aabbb = true := splitCheck (by decide +kernel) ok_tree8aabbba ok_tree8aabbbb
def tree8aabb : BinaryTree (List W) := .node [ws,we,wd,wf,waD,wa,wb,wg,wh] tree8aabba tree8aabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aabb : everyKey (certRow 7 tree7) tree8aabb = true := splitCheck (by decide +kernel) ok_tree8aabba ok_tree8aabbb
def tree8aab : BinaryTree (List W) := .node [wcK,we,wd,wf,wc,wa,wb,wg,wh] tree8aaba tree8aabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aab : everyKey (certRow 7 tree7) tree8aab = true := splitCheck (by decide +kernel) ok_tree8aaba ok_tree8aabb
def tree8aa : BinaryTree (List W) := .node [wca,we,wd,wf,wc,wa,wb,wg,wh] tree8aaa tree8aab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aa : everyKey (certRow 7 tree7) tree8aa = true := splitCheck (by decide +kernel) ok_tree8aaa ok_tree8aab
def tree8abaaaa : BinaryTree (List W) := (.node [w4,wd,wf,wc,wr,wa,wb,wg,wh] (.node [w4,wA,wd,wf,wc,wa,wb,wg,wh] (.node [wg7,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdE,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [w4,we,wu,wf,wc,wa,wb,wg,wh] (.node [w4,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wd1,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcY,we,wd,wf,wc,wa,wb,wg,wh] (.node [wfk,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wdi,we,wd,wf,wc,wa,wb,wg,wh] (.node [wcV,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abaaaa : everyKey (certRow 7 tree7) tree8abaaaa = true := by decide +kernel
def tree8abaaab : BinaryTree (List W) := (.node [wcZ,we,wd,wf,wc,wa,wb,wg,wh] (.node [wgn,we,wd,wf,wc,wa,wb,wg,wh] (.node [w3,wu,wf,wc,wa,wb,wg,wh] (.node [w3,wd,wu,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wc8,we,wd,wf,wc,wa,wb,wg,wh] (.node [wg6,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wc4,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdg,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdc,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [ww,we,wav,wf,wc,wa,wb,wg,wh] (.node [ww,we,wao,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abaaab : everyKey (certRow 7 tree7) tree8abaaab = true := by decide +kernel
def tree8abaaa : BinaryTree (List W) := .node [w3,we,wu,wf,wc,wa,wb,wg,wh] tree8abaaaa tree8abaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abaaa : everyKey (certRow 7 tree7) tree8abaaa = true := splitCheck (by decide +kernel) ok_tree8abaaaa ok_tree8abaaab
def tree8abaaba : BinaryTree (List W) := (.node [ww,we,wf,wv,wc,wa,wb,wg,wh] (.node [ww,we,wd,wf,wc,wa,wb,wg,wh] (.node [ww,we,wd,wf,wc,wa,wb,wax,wh] (.node [ww,we,wH,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [ww,we,wu,wf,wc,wa,wb,wg,wh] (.node [ww,we,wd,wf,wc,wa,wb,waw,wh] .nil .nil) .nil)) (.node [ww,we,wf,wc,wa,wb,wax,wh] (.node [ww,we,wf,wc,wa,wb,wax,wg,wh] (.node [ww,we,wf,wc,wq,wa,wb,wg,wh] .nil .nil) .nil) (.node [whs,we,wd,wf,wc,wa,wb,wg,wh] (.node [ww,we,wf,wc,wa,wb,wg,waA,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abaaba : everyKey (certRow 7 tree7) tree8abaaba = true := by decide +kernel
def tree8abaabb : BinaryTree (List W) := (.node [wcD,we,wd,wf,wc,wa,wb,wg,wh] (.node [waa,we,wd,wf,wc,wa,wb,wg,wh] (.node [waa,wz,wd,wf,wc,wa,wb,wg,wh] (.node [wdL,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [waa,wd,wu,wf,wc,wa,wb,wg,wh] (.node [waa,we,wd,wf,wr,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wgK,we,wd,wf,wc,wa,wb,wg,wh] (.node [wd4,we,wd,wf,wc,wa,wb,wg,wh] (.node [wch,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wdm,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdG,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abaabb : everyKey (certRow 7 tree7) tree8abaabb = true := by decide +kernel
def tree8abaab : BinaryTree (List W) := .node [wdq,we,wd,wf,wc,wa,wb,wg,wh] tree8abaaba tree8abaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abaab : everyKey (certRow 7 tree7) tree8abaab = true := splitCheck (by decide +kernel) ok_tree8abaaba ok_tree8abaabb
def tree8abaa : BinaryTree (List W) := .node [ww,we,w5,wf,wc,wa,wb,wg,wh] tree8abaaa tree8abaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abaa : everyKey (certRow 7 tree7) tree8abaa = true := splitCheck (by decide +kernel) ok_tree8abaaa ok_tree8abaab
def tree8ababaa : BinaryTree (List W) := (.node [wdB,we,wd,wf,wc,wa,wb,wg,wh] (.node [waf,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdS,we,wd,wf,wc,wa,wb,wg,wh] (.node [wdx,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wf1,we,wd,wf,wc,wa,wb,wg,wh] (.node [waf,wd,wf,wc,wr,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wA,we,wd,wf,wc,wa,wb,wg,wh] (.node [wA,we,wd,wf,wc,wa,wb,wg,wam] (.node [wdu,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [wA,wd,wu,wf,wc,wa,wb,wg,wh] (.node [wA,we,wd,wf,wc,wa,wb,wg,wal] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ababaa : everyKey (certRow 7 tree7) tree8ababaa = true := by decide +kernel
def tree8ababab : BinaryTree (List W) := (.node [wz,we,wd,wf,wc,wa,wb,wax,wh] (.node [wdP,we,wd,wf,wc,wa,wb,wg,wh] (.node [wA,wd,wf,wc,wa,wb,wg,wam,wh] (.node [wA,wd,wf,wc,wa,wb,wg,wam] .nil .nil) .nil) (.node [wz,we,wd,wf,wc,wa,wa6,wb,wh] (.node [wz,we,wd,wf,waV,wc,wa,wb,wh] .nil .nil) .nil)) (.node [wz,we,wd,wf,wc,wa,wb,waw,wh] (.node [wz,we,wd,wf,wc,wa,wb,wg,wh] (.node [wz,we,wd,wf,wc,wa,wb,waj,wh] .nil .nil) .nil) (.node [wz,we,wd,wf,wc,wa,wb,wa4,wh] (.node [wz,we,wd,wf,wc,wa,wb,wai,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ababab : everyKey (certRow 7 tree7) tree8ababab = true := by decide +kernel
def tree8ababa : BinaryTree (List W) := .node [wA,wd,wf,w7,wc,wa,wb,wg,wh] tree8ababaa tree8ababab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ababa : everyKey (certRow 7 tree7) tree8ababa = true := splitCheck (by decide +kernel) ok_tree8ababaa ok_tree8ababab
def tree8ababba : BinaryTree (List W) := (.node [wF,we,wd,wf,wc,wa,wb,wg,wh] (.node [we0,we,wd,wf,wc,wa,wb,wg,wh] (.node [wz,wd,wf,wc,wa,wb,waj,wh] (.node [wz,wd,wf,wc,wa,wb,waj,wg,wh] .nil .nil) .nil) (.node [wek,we,wd,wf,wc,wa,wb,wg,wh] (.node [weG,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wba,wd,wf,wc,wa,wb,wg,wh] (.node [wba,we,wd,wf,wc,wa,wb,wg,wh] (.node [wF,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wD,wd,wf,wc,wa,wb,wg,wh] (.node [we,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ababba : everyKey (certRow 7 tree7) tree8ababba = true := by decide +kernel
def tree8ababbb : BinaryTree (List W) := (.node [we,wfV,wd,wf,wc,wa,wb,wg,wh] (.node [we,wgI,wd,wf,wc,wa,wb,wg,wh] (.node [we,wcf,wd,wf,wc,wa,wb,wg,wh] (.node [we,wgq,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd8,wd,wf,wc,wa,wb,wg,wh] (.node [we,wcB,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wec,wd,wf,wc,wa,wb,wg,wh] (.node [we,weg,wd,wf,wc,wa,wb,wg,wh] (.node [we,wcW,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wB,wd,w8,wc,wa,wb,wg,wh] (.node [we,wB,wd,waJ,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ababbb : everyKey (certRow 7 tree7) tree8ababbb = true := by decide +kernel
def tree8ababb : BinaryTree (List W) := .node [we,wa8,wd,wf,wc,wa,wb,wg,wh] tree8ababba tree8ababbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ababb : everyKey (certRow 7 tree7) tree8ababb = true := splitCheck (by decide +kernel) ok_tree8ababba ok_tree8ababbb
def tree8abab : BinaryTree (List W) := .node [wz,wd,wf,wc,wr,wa,wb,wg,wh] tree8ababa tree8ababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abab : everyKey (certRow 7 tree7) tree8abab = true := splitCheck (by decide +kernel) ok_tree8ababa ok_tree8ababb
def tree8aba : BinaryTree (List W) := .node [w6,we,wd,wf,wc,wa,wb,wg,wh] tree8abaa tree8abab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8aba : everyKey (certRow 7 tree7) tree8aba = true := splitCheck (by decide +kernel) ok_tree8abaa ok_tree8abab
def tree8abbaaa : BinaryTree (List W) := (.node [we,wB,wd,wc,wa,wb,waL,wg,wh] (.node [we,wB,wd,wf,wc,wa,wb,waK,wh] (.node [we,wB,wd,wf,wc,wa,wb,wg,wh] (.node [we,wB,wd,wf,wc,wa,wb,waL,wh] .nil .nil) .nil) (.node [we,wB,wd,wc,waB,wa,wb,wg,wh] (.node [we,wB,wd,w7,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wdX,wd,wf,wc,wa,wb,wg,wh] (.node [we,wgh,wd,wf,wc,wa,wb,wg,wh] (.node [we,wB,wd,wc,wa,wb,waL,wh] .nil .nil) .nil) (.node [we,we6,wd,wf,wc,wa,wb,wg,wh] (.node [we,weo,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbaaa : everyKey (certRow 7 tree7) tree8abbaaa = true := by decide +kernel
def tree8abbaab : BinaryTree (List W) := (.node [we,whL,wd,wf,wc,wa,wb,wg,wh] (.node [we,wgU,wd,wf,wc,wa,wb,wg,wh] (.node [we,whf,wd,wf,wc,wa,wb,wg,wh] (.node [we,whu,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wfP,wd,wf,wc,wa,wb,wg,wh] (.node [we,wgb,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wao,wd,wf,wc,wa,wb,wg,wh] (.node [we,wao,wx,wf,wc,wa,wb,wg,wh] (.node [we,wfo,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wfF,wd,wf,wc,wa,wb,wg,wh] (.node [we,wao,wd,wv,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbaab : everyKey (certRow 7 tree7) tree8abbaab = true := by decide +kernel
def tree8abbaa : BinaryTree (List W) := .node [we,wfw,wd,wf,wc,wa,wb,wg,wh] tree8abbaaa tree8abbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbaa : everyKey (certRow 7 tree7) tree8abbaa = true := splitCheck (by decide +kernel) ok_tree8abbaaa ok_tree8abbaab
def tree8abbaba : BinaryTree (List W) := (.node [we,wap,wf,wv,wc,wa,wb,wg,wh] (.node [we,wfG,wd,wf,wc,wa,wb,wg,wh] (.node [we,we3,wd,wf,wc,wa,wb,wg,wh] (.node [we,weJ,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wap,wd,wf,wc,wa,wb,wg,wh] (.node [we,wgO,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,waq,wi,wf,wc,wa,wb,wg,wh] (.node [we,wfu,wd,wf,wc,wa,wb,wg,wh] (.node [we,wfp,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,waq,wd,wf,wc,wj,wb,wg,wh] (.node [we,waq,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbaba : everyKey (certRow 7 tree7) tree8abbaba = true := by decide +kernel
def tree8abbabb : BinaryTree (List W) := (.node [we,waF,wd,wv,wc,wa,wb,wg,wh] (.node [we,weK,wd,wf,wc,wa,wb,wg,wh] (.node [we,wfN,wd,wf,wc,wa,wb,wg,wh] (.node [we,we4,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,waF,wd,wf,wc,wa,wb,wg,wh] (.node [we,waF,wk,wd,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,we7,wd,wc,wa,wb,wg,wh] (.node [we,we7,wd,wf,wc,wa,wb,wg,wh] (.node [we,we7,wl,wd,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wep,wi,wd,wc,wa,wb,wg,wh] (.node [we,wf9,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbabb : everyKey (certRow 7 tree7) tree8abbabb = true := by decide +kernel
def tree8abbab : BinaryTree (List W) := .node [we,waq,wu,wf,wc,wa,wb,wg,wh] tree8abbaba tree8abbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbab : everyKey (certRow 7 tree7) tree8abbab = true := splitCheck (by decide +kernel) ok_tree8abbaba ok_tree8abbabb
def tree8abba : BinaryTree (List W) := .node [we,wha,wd,wf,wc,wa,wb,wg,wh] tree8abbaa tree8abbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abba : everyKey (certRow 7 tree7) tree8abba = true := splitCheck (by decide +kernel) ok_tree8abbaa ok_tree8abbab
def tree8abbbaa : BinaryTree (List W) := (.node [we,wel,wd,wf,wc,wa,wb,wg,wh] (.node [we,wex,wd,wf,wc,wa,wb,wg,wh] (.node [we,wem,wd,wf,wc,wa,wb,wg,wh] (.node [we,wep,wd,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wer,wd,wf,wc,wa,wb,wg,wh] (.node [we,weC,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wi,wd,wf,wc,wa,wb,wez,wh] (.node [we,wi,wd,wf,wc,war,wb,wg,wh] (.node [we,wev,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wi,wd,wf,wc,wa,wb,wey,wh] (.node [we,wi,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbbaa : everyKey (certRow 7 tree7) tree8abbbaa = true := by decide +kernel
def tree8abbbab : BinaryTree (List W) := (.node [we,weS,wd,wf,wc,wa,wb,wg,wh] (.node [we,wi,wf,wc,wj,wb,wg,wh] (.node [we,wi,wf,wc,wa,wj,wb,wg,wh] (.node [we,wi,wd,wen,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wej,wd,wf,wc,wa,wb,wg,wh] (.node [we,wfL,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,weH,wd,wf,wc,wa,wb,wg,wh] (.node [we,weX,wd,wf,wc,wa,wb,wg,wh] (.node [we,weM,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wk,wd,wf,wc,waG,wb,wg,wh] (.node [we,weQ,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbbab : everyKey (certRow 7 tree7) tree8abbbab = true := by decide +kernel
def tree8abbba : BinaryTree (List W) := .node [we,wi,wd,wf,wc,wj,wb,wg,wh] tree8abbbaa tree8abbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbba : everyKey (certRow 7 tree7) tree8abbba = true := splitCheck (by decide +kernel) ok_tree8abbbaa ok_tree8abbbab
def tree8abbbba : BinaryTree (List W) := (.node [we,wff,wd,wf,wc,wa,wb,wg,wh] (.node [we,wk,wd,wc,waE,wb,wg,wh] (.node [we,wk,wd,wc,wa,waE,wb,wg,wh] (.node [we,wk,wd,wf,wc,waE,wb,wg,wh] .nil .nil) .nil) (.node [we,wf7,wd,wf,wc,wa,wb,wg,wh] (.node [we,weF,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wfd,wd,wf,wc,wa,wb,wg,wh] (.node [we,we1,wd,wf,wc,wa,wb,wg,wh] (.node [we,we9,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wl,wd,wf,wc,wa1,wb,wg,wh] (.node [we,wl,wd,wf,wc,waQ,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbbba : everyKey (certRow 7 tree7) tree8abbbba = true := by decide +kernel
def tree8abbbbb : BinaryTree (List W) := (.node [we,wl,wd,wf,wc,wac,wb,wg,wh] (.node [we,wl,wd,wf,wc,wa,wb,wa3,wg] (.node [we,wl,wd,wf,wc,wad,wb,wg,wh] (.node [we,wl,wd,wf,wc,war,wb,wg,wh] .nil .nil) .nil) (.node [we,wl,wd,wf,wc,wa,wb,wg,wa2] (.node [we,wl,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wl,wd,wf,wc,waO,wb,wg,wh] (.node [we,wl,wd,wf,wc,waE,wb,wg,wh] (.node [we,wl,wd,wf,wc,wj,wb,wg,wh] .nil .nil) .nil) (.node [we,wl,wd,wf,wc,wb,wa3,wg] (.node [we,wl,wd,wf,wc,wa0,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbbbb : everyKey (certRow 7 tree7) tree8abbbbb = true := by decide +kernel
def tree8abbbb : BinaryTree (List W) := .node [we,wl,wd,wf,wc,waG,wb,wg,wh] tree8abbbba tree8abbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbbb : everyKey (certRow 7 tree7) tree8abbbb = true := splitCheck (by decide +kernel) ok_tree8abbbba ok_tree8abbbbb
def tree8abbb : BinaryTree (List W) := .node [we,wk,wd,wf,wc,wa,wb,wg,wh] tree8abbba tree8abbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abbb : everyKey (certRow 7 tree7) tree8abbb = true := splitCheck (by decide +kernel) ok_tree8abbba ok_tree8abbbb
def tree8abb : BinaryTree (List W) := .node [we,wep,wd,wf,wc,wa,wb,wg,wh] tree8abba tree8abbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8abb : everyKey (certRow 7 tree7) tree8abb = true := splitCheck (by decide +kernel) ok_tree8abba ok_tree8abbb
def tree8ab : BinaryTree (List W) := .node [we,wB,wd,waC,wc,wa,wb,wg,wh] tree8aba tree8abb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ab : everyKey (certRow 7 tree7) tree8ab = true := splitCheck (by decide +kernel) ok_tree8aba ok_tree8abb
def tree8a : BinaryTree (List W) := .node [wdk,we,wd,wf,wc,wa,wb,wg,wh] tree8aa tree8ab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8a : everyKey (certRow 7 tree7) tree8a = true := splitCheck (by decide +kernel) ok_tree8aa ok_tree8ab
def tree8baaaaa : BinaryTree (List W) := (.node [we,wan,wv,wc,wa,wb,wg,wh] (.node [we,wfm,wd,wf,wc,wa,wb,wg,wh] (.node [we,weZ,wd,wf,wc,wa,wb,wg,wh] (.node [we,wl,wd,we5,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wan,wf,wv,wc,wa,wb,wg,wh] (.node [we,wan,wd,wv,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wfy,wd,wf,wc,wa,wb,wg,wh] (.node [we,wfD,wd,wf,wc,wa,wb,wg,wh] (.node [we,wgN,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wat,wu,wf,wc,wa,wb,wg,wh] (.node [we,whv,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaaaa : everyKey (certRow 7 tree7) tree8baaaaa = true := by decide +kernel
def tree8baaaab : BinaryTree (List W) := (.node [we,wgY,wd,wf,wc,wa,wb,wg,wh] (.node [we,wfR,wd,wf,wc,wa,wb,wg,wh] (.node [we,wat,wf,wc,wa,wj,wb,wg,wh] (.node [we,wat,wf,wc,wq,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wav,wd,wf,wc,wa,wb,wg,wh] (.node [we,wfA,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wfl,wd,wf,wc,wa,wb,wg,wh] (.node [we,wd2,wd,wf,wc,wa,wb,wg,wh] (.node [we,wfT,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,w5,wx,wf,wc,wa,wb,wg,wh] (.node [we,wgo,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaaab : everyKey (certRow 7 tree7) tree8baaaab = true := by decide +kernel
def tree8baaaa : BinaryTree (List W) := .node [we,wat,wf,wv,wc,wa,wb,wg,wh] tree8baaaaa tree8baaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaaa : everyKey (certRow 7 tree7) tree8baaaa = true := splitCheck (by decide +kernel) ok_tree8baaaaa ok_tree8baaaab
def tree8baaaba : BinaryTree (List W) := (.node [we,wbx,wf,wc,wa,wb,wg,wh] (.node [we,wdF,wd,wf,wc,wa,wb,wg,wh] (.node [we,wdl,wd,wf,wc,wa,wb,wg,wh] (.node [we,w5,wf,wc,wa,wj,wb,wg,wh] .nil .nil) .nil) (.node [we,wbx,wd,wf,wc,wa,wb,wg,wh] (.node [we,wbU,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wx,wd,wf,wc,wa,wb,wg,wh] (.node [we,wx,wd,wf,wc,wa,wb,wg,waA] (.node [we,wfr,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wx,wu,wf,wc,wa,wb,wg,wh] (.node [we,wx,wd,wf,wc,wa,wb,wg,waz] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaaba : everyKey (certRow 7 tree7) tree8baaaba = true := by decide +kernel
def tree8baaabb : BinaryTree (List W) := (.node [we,wck,wd,wf,wc,wa,wb,wg,wh] (.node [we,wH,wd,wf,wc,wa,wb,wg,wh] (.node [we,wx,wf,wc,wa,wb,wg,waA,wh] (.node [we,wx,wf,wc,wa,wb,wg,waA] .nil .nil) .nil) (.node [we,wcG,wd,wf,wc,wa,wb,wg,wh] (.node [we,wH,wd,wf,wq,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wd,wf,wc,wa,wb,wg,wh] (.node [we,wbd,wf,wc,wa,wb,wg,wh] (.node [we,wbd,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wbv,wf,wc,wa,wb,wg,wh] (.node [we,wd,wbb,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaabb : everyKey (certRow 7 tree7) tree8baaabb = true := by decide +kernel
def tree8baaab : BinaryTree (List W) := .node [we,wx,wf,wv,wc,wa,wb,wg,wh] tree8baaaba tree8baaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaab : everyKey (certRow 7 tree7) tree8baaab = true := splitCheck (by decide +kernel) ok_tree8baaaba ok_tree8baaabb
def tree8baaa : BinaryTree (List W) := .node [we,w5,wd,wf,wc,wa,wb,wg,wh] tree8baaaa tree8baaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaa : everyKey (certRow 7 tree7) tree8baaa = true := splitCheck (by decide +kernel) ok_tree8baaaa ok_tree8baaab
def tree8baabaa : BinaryTree (List W) := (.node [we,wd,wdj,wf,wc,wa,wb,wg,wh] (.node [we,wd,wg4,wf,wc,wa,wb,wg,wh] (.node [we,wd,wci,wf,wc,wa,wb,wg,wh] (.node [we,wd,wfJ,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wfZ,wf,wc,wa,wb,wg,wh] (.node [we,wd,wcE,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wu,wf,wc,wa,wb,wg,wh] (.node [we,wd,wfj,wf,wc,wa,wb,wg,wh] (.node [we,wd,wdD,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wg9,wf,wc,wa,wb,wg,wh] (.node [we,wd,wd0,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baabaa : everyKey (certRow 7 tree7) tree8baabaa = true := by decide +kernel
def tree8baabab : BinaryTree (List W) := (.node [we,wd,wdI,wf,wc,wa,wb,wg,wh] (.node [we,wd,waJ,wf,wc,wa,wb,wg,wh] (.node [we,wd,we2,wf,wc,wa,wb,wg,wh] (.node [we,wd,whp,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wdo,wf,wc,wa,wb,wg,wh] (.node [we,wd,wgs,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,waC,wf,wc,wa,wb,wg,wh] (.node [we,wd,whz,wf,wc,wa,wb,wg,wh] (.node [we,wd,wc2,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wcJ,wf,wc,wa,wb,wg,wh] (.node [we,wd,waC,wv,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baabab : everyKey (certRow 7 tree7) tree8baabab = true := by decide +kernel
def tree8baaba : BinaryTree (List W) := .node [we,wd,weI,wf,wc,wa,wb,wg,wh] tree8baabaa tree8baabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baaba : everyKey (certRow 7 tree7) tree8baaba = true := splitCheck (by decide +kernel) ok_tree8baabaa ok_tree8baabab
def tree8baabba : BinaryTree (List W) := (.node [we,wd,wbh,wc,wa,wb,wg,wh] (.node [we,wd,wL,wc,wa,wb,wg,wh] (.node [we,wd,wL,wf,wc,wa,wb,wg,wh] (.node [we,wd,waN,wv,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wbh,wf,wc,wa,wb,wg,wh] (.node [we,wd,wbB,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wbf,wc,wa,wb,wg,wh] (.node [we,wd,wf,wJ,wc,wa,wb,wg,wh] (.node [we,wd,wf,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wbz,wc,wa,wb,wg,wh] (.node [we,wd,wf,wcH,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baabba : everyKey (certRow 7 tree7) tree8baabba = true := by decide +kernel
def tree8baabbb : BinaryTree (List W) := (.node [we,wd,wf,wgd,wc,wa,wb,wg,wh] (.node [we,wd,wf,w7,wc,wa,wb,wg,wh] (.node [we,wd,wf,wdH,wc,wa,wb,wg,wh] (.node [we,wd,wf,wdn,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,we5,wc,wa,wb,wg,wh] (.node [we,wd,wf,wen,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wf5,wc,wa,wb,wg,wh] (.node [we,wd,wf,wf2,wc,wa,wb,wg,wh] (.node [we,wd,wf,wgf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wfn,wc,wa,wb,wg,wh] (.node [we,wd,wf,wgl,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baabbb : everyKey (certRow 7 tree7) tree8baabbb = true := by decide +kernel
def tree8baabb : BinaryTree (List W) := .node [we,wd,wf,wc0,wc,wa,wb,wg,wh] tree8baabba tree8baabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baabb : everyKey (certRow 7 tree7) tree8baabb = true := splitCheck (by decide +kernel) ok_tree8baabba ok_tree8baabbb
def tree8baab : BinaryTree (List W) := .node [we,wd,wcJ,wc,wa,wb,wg,wh] tree8baaba tree8baabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baab : everyKey (certRow 7 tree7) tree8baab = true := splitCheck (by decide +kernel) ok_tree8baaba ok_tree8baabb
def tree8baa : BinaryTree (List W) := .node [we,wd,wbS,wf,wc,wa,wb,wg,wh] tree8baaa tree8baab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baa : everyKey (certRow 7 tree7) tree8baa = true := splitCheck (by decide +kernel) ok_tree8baaa ok_tree8baab
def tree8babaaa : BinaryTree (List W) := (.node [we,wd,wf,wgw,wc,wa,wb,wg,wh] (.node [we,wd,wf,whd,wc,wa,wb,wg,wh] (.node [we,wd,wf,wa5,wc,wa,wn,wg,wh] (.node [we,wd,wf,wfE,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,waP,wa,wb,wn,wg,wh] (.node [we,wd,wf,waP,wr,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wgu,wc,wa,wb,wg,wh] (.node [we,wd,wf,whc,wc,wa,wb,wg,wh] (.node [we,wd,wf,wgS,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wgQ,wc,wa,wb,wg,wh] (.node [we,wd,wf,whB,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babaaa : everyKey (certRow 7 tree7) tree8babaaa = true := by decide +kernel
def tree8babaab : BinaryTree (List W) := (.node [we,wd,wf,waD,wa,wb,wn,wg,wh] (.node [we,wd,wf,wgG,wc,wa,wb,wg,wh] (.node [we,wd,wf,wg2,wc,wa,wb,wg,wh] (.node [we,wd,wf,waW,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,waD,wc,wa,wb,wg,wh] (.node [we,wd,wf,wf6,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wfK,wc,wa,wb,wg,wh] (.node [we,wd,wf,wgt,wc,wa,wb,wg,wh] (.node [we,wd,wf,wd5,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wdM,wc,wa,wb,wg,wh] (.node [we,wd,wf,wab,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babaab : everyKey (certRow 7 tree7) tree8babaab = true := by decide +kernel
def tree8babaa : BinaryTree (List W) := .node [we,wd,wf,whl,wc,wa,wb,wg,wh] tree8babaaa tree8babaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babaa : everyKey (certRow 7 tree7) tree8babaa = true := splitCheck (by decide +kernel) ok_tree8babaaa ok_tree8babaab
def tree8bababa : BinaryTree (List W) := (.node [we,wd,wf,waR,wc,wa,wn,wg,wh] (.node [we,wd,wf,wbY,wc,wa,wb,wg,wh] (.node [we,wd,wf,weN,wc,wa,wb,wg,wh] (.node [we,wd,wf,wfa,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,waR,wc,wa,wb,wg,wh] (.node [we,wd,wf,waV,wr,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wes,wc,wa,wb,wg,wh] (.node [we,wd,wf,wc5,wc,wa,wb,wg,wh] (.node [we,wd,wf,wM,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wbE,wc,wa,wb,wg,wh] (.node [we,wd,wf,wfs,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bababa : everyKey (certRow 7 tree7) tree8bababa = true := by decide +kernel
def tree8bababb : BinaryTree (List W) := (.node [we,wd,wf,wc,wgA,wa,wb,wg,wh] (.node [we,wd,wf,wc,wgp,wa,wb,wg,wh] (.node [we,wd,wf,wc,wbW,wa,wb,wg,wh] (.node [we,wd,wf,wc,wbC,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wc3,wa,wb,wg,wh] (.node [we,wd,wf,wc,wg0,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wgE,wa,wb,wh] (.node [we,wd,wf,wc,wgE,wa,wb,wg,wh] (.node [we,wd,wf,wc,wgE,wr,wa,wb,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wdK,wa,wb,wg,wh] (.node [we,wd,wf,wc,wdp,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bababb : everyKey (certRow 7 tree7) tree8bababb = true := by decide +kernel
def tree8babab : BinaryTree (List W) := .node [we,wd,wf,wc,wc,wa,wb,wg,wh] tree8bababa tree8bababb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babab : everyKey (certRow 7 tree7) tree8babab = true := splitCheck (by decide +kernel) ok_tree8bababa ok_tree8bababb
def tree8baba : BinaryTree (List W) := .node [we,wd,wf,wdr,wc,wa,wb,wg,wh] tree8babaa tree8babab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8baba : everyKey (certRow 7 tree7) tree8baba = true := splitCheck (by decide +kernel) ok_tree8babaa ok_tree8babab
def tree8babbaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wgW,wa,wb,wg,wh] (.node [we,wd,wf,wc,weq,wa,wb,wg,wh] (.node [we,wd,wf,wc,wgP,wa,wb,wg,wh] (.node [we,wd,wf,wc,wd3,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,we8,wa,wb,wg,wh] (.node [we,wd,wf,wc,weL,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wq,wa,wb,wg,wh] (.node [we,wd,wf,wc,wfq,wa,wb,wg,wh] (.node [we,wd,wf,wc,wgM,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wgr,wa,wb,wg,wh] (.node [we,wd,wf,wc,wfI,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babbaa : everyKey (certRow 7 tree7) tree8babbaa = true := by decide +kernel
def tree8babbab : BinaryTree (List W) := (.node [we,wd,wf,wc,waQ,wj,wb,wg,wh] (.node [we,wd,wf,wc,wgT,wa,wb,wg,wh] (.node [we,wd,wf,wc,whj,wa,wb,wg,wh] (.node [we,wd,wf,wc,whH,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wgx,wa,wb,wg,wh] (.node [we,wd,wf,wc,whD,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,whn,wa,wb,wg,wh] (.node [we,wd,wf,wc,wa1,wa,wb,wg,wh] (.node [we,wd,wf,wc,whe,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,waG,wa,wb,wg,wh] (.node [we,wd,wf,wc,wga,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babbab : everyKey (certRow 7 tree7) tree8babbab = true := by decide +kernel
def tree8babba : BinaryTree (List W) := .node [we,wd,wf,wc,wf4,wa,wb,wg,wh] tree8babbaa tree8babbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babba : everyKey (certRow 7 tree7) tree8babba = true := splitCheck (by decide +kernel) ok_tree8babbaa ok_tree8babbab
def tree8babbba : BinaryTree (List W) := (.node [we,wd,wf,wc,wcN,wa,wb,wg,wh] (.node [we,wd,wf,wc,wfv,wa,wb,wg,wh] (.node [we,wd,wf,wc,war,wa,wb,wg,wh] (.node [we,wd,wf,wc,wfO,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wc9,wa,wb,wg,wh] (.node [we,wd,wf,wc,wd9,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wdQ,wa,wb,wg,wh] (.node [we,wd,wf,wc,wb2,wa,wb,wg,wh] (.node [we,wd,wf,wc,wco,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wQ,wb,wg,wh] (.node [we,wd,wf,wc,wQ,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babbba : everyKey (certRow 7 tree7) tree8babbba = true := by decide +kernel
def tree8babbbb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wbj,wb,wg,wh] (.node [we,wd,wf,wc,wbI,wa,wb,wg,wh] (.node [we,wd,wf,wc,wdv,wa,wb,wg,wh] (.node [we,wd,wf,wc,wbl,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wO,wb,wg,wh] (.node [we,wd,wf,wc,wa,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wcm,wb,wg,wh] (.node [we,wd,wf,wc,wa,wb0,wb,wg,wh] (.node [we,wd,wf,wc,wa,wbG,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wc7,wb,wg,wh] (.node [we,wd,wf,wc,wa,wcL,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babbbb : everyKey (certRow 7 tree7) tree8babbbb = true := by decide +kernel
def tree8babbb : BinaryTree (List W) := .node [we,wd,wf,wc,wbl,wa,wb,wg,wh] tree8babbba tree8babbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babbb : everyKey (certRow 7 tree7) tree8babbb = true := splitCheck (by decide +kernel) ok_tree8babbba ok_tree8babbbb
def tree8babb : BinaryTree (List W) := .node [we,wd,wf,wc,whb,wa,wb,wg,wh] tree8babba tree8babbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8babb : everyKey (certRow 7 tree7) tree8babb = true := splitCheck (by decide +kernel) ok_tree8babba ok_tree8babbb
def tree8bab : BinaryTree (List W) := .node [we,wd,wf,wc,wr,wa,wb,wg,wh] tree8baba tree8babb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bab : everyKey (certRow 7 tree7) tree8bab = true := splitCheck (by decide +kernel) ok_tree8baba ok_tree8babb
def tree8ba : BinaryTree (List W) := .node [we,wd,wf,wv,wc,wa,wb,wg,wh] tree8baa tree8bab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8ba : everyKey (certRow 7 tree7) tree8ba = true := splitCheck (by decide +kernel) ok_tree8baa ok_tree8bab
def tree8bbaaaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wj,wb,wg,wh] (.node [we,wd,wf,wc,wa,whh,wb,wg,wh] (.node [we,wd,wf,wc,wa,wd7,wb,wg,wh] (.node [we,wd,wf,wc,wa,wdO,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wft,wb,wg,wh] (.node [we,wd,wf,wc,wa,wg8,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wgv,wb,wg,wh] (.node [we,wd,wf,wc,wa,wf8,wb,wg,wh] (.node [we,wd,wf,wc,wa,wfM,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,whI,wb,wg,wh] (.node [we,wd,wf,wc,wa,wgR,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaaaa : everyKey (certRow 7 tree7) tree8bbaaaa = true := by decide +kernel
def tree8bbaaab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wau,wn,wg,wh] (.node [we,wd,wf,wc,wa,wge,wb,wg,wh] (.node [we,wd,wf,wc,wa,wfS,wb,wg,wh] (.node [we,wd,wf,wc,wa,whF,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,whi,wb,wg,wh] (.node [we,wd,wf,wc,wa,wgX,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wag,wb,wg,wh] (.node [we,wd,wf,wc,wa,wgB,wb,wg,wh] (.node [we,wd,wf,wc,wa,wfz,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wdT,wb,wg,wh] (.node [we,wd,wf,wc,wa,wb5,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaaab : everyKey (certRow 7 tree7) tree8bbaaab = true := by decide +kernel
def tree8bbaaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,whM,wb,wg,wh] tree8bbaaaa tree8bbaaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaaa : everyKey (certRow 7 tree7) tree8bbaaa = true := splitCheck (by decide +kernel) ok_tree8bbaaaa ok_tree8bbaaab
def tree8bbaaba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wew,wb,wg,wh] (.node [we,wd,wf,wc,wa,wed,wb,wg,wh] (.node [we,wd,wf,wc,wa,waS,wb,wg,wh] (.node [we,wd,wf,wc,wa,wdd,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,weR,wb,wg,wh] (.node [we,wd,wf,wc,wa,wfe,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wU,wg,wh] (.node [we,wd,wf,wc,wa,wU,wb,wg,wh] (.node [we,wd,wf,wc,wa,wcQ,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wb,wg,wh] (.node [we,wd,wf,wc,wa,wcr,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaaba : everyKey (certRow 7 tree7) tree8bbaaba = true := by decide +kernel
def tree8bbaabb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wdR,wg,wh] (.node [we,wd,wf,wc,wa,wb,wcO,wg,wh] (.node [we,wd,wf,wc,wa,wb,wcp,wg,wh] (.node [we,wd,wf,wc,wa,wb,wb3,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wdw,wg,wh] (.node [we,wd,wf,wc,wa,wb,wdb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,weP,wg,wh] (.node [we,wd,wf,wc,wa,wb,weu,wg,wh] (.node [we,wd,wf,wc,wa,wb,web,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wfx,wg,wh] (.node [we,wd,wf,wc,wa,wb,wfc,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaabb : everyKey (certRow 7 tree7) tree8bbaabb = true := by decide +kernel
def tree8bbaab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wS,wg,wh] tree8bbaaba tree8bbaabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaab : everyKey (certRow 7 tree7) tree8bbaab = true := splitCheck (by decide +kernel) ok_tree8bbaaba ok_tree8bbaabb
def tree8bbaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wdy,wb,wg,wh] tree8bbaaa tree8bbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaa : everyKey (certRow 7 tree7) tree8bbaa = true := splitCheck (by decide +kernel) ok_tree8bbaaa ok_tree8bbaab
def tree8bbabaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wht,wg,wh] (.node [we,wd,wf,wc,wa,wb,whJ,wg,wh] (.node [we,wd,wf,wc,wa,wb,whE,wg,wh] (.node [we,wd,wf,wc,wa,wb,wgc,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,whA,wg,wh] (.node [we,wd,wf,wc,wa,wb,whw,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wgV,wg,wh] (.node [we,wd,wf,wc,wa,wb,wgz,wg,wh] (.node [we,wd,wf,wc,wa,wb,wn,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,whm,wg,wh] (.node [we,wd,wf,wc,wa,wb,why,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbabaa : everyKey (certRow 7 tree7) tree8bbabaa = true := by decide +kernel
def tree8bbabab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wfC,wg,wh] (.node [we,wd,wf,wc,wa,wb,wgi,wg,wh] (.node [we,wd,wf,wc,wa,wb,whC,wg,wh] (.node [we,wd,wf,wc,wa,wb,whg,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg1,wg,wh] (.node [we,wd,wf,wc,wa,wb,wfW,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wez,wg,wh] (.node [we,wd,wf,wc,wa,wb,weU,wg,wh] (.node [we,wd,wf,wc,wa,wb,wfi,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wgF,wg,wh] (.node [we,wd,wf,wc,wa,wb,wez,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbabab : everyKey (certRow 7 tree7) tree8bbabab = true := by decide +kernel
def tree8bbaba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,whq,wg,wh] tree8bbabaa tree8bbabab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbaba : everyKey (certRow 7 tree7) tree8bbaba = true := splitCheck (by decide +kernel) ok_tree8bbabaa ok_tree8bbabab
def tree8bbabba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wcv,wg,wh] (.node [we,wd,wf,wc,wa,wb,wbp,wh] (.node [we,wd,wf,wc,wa,wb,wbp,wg,wh] (.node [we,wd,wf,wc,wa,wb,wbM,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wcU,wg,wh] (.node [we,wd,wf,wc,wa,wb,wdC,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wg,wh] (.node [we,wd,wf,wc,wa,wb,wY,wh] (.node [we,wd,wf,wc,wa,wb,wY,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wW,wh] (.node [we,wd,wf,wc,wa,wb,wg,wbn,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbabba : everyKey (certRow 7 tree7) tree8bbabba = true := by decide +kernel
def tree8bbabbb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wcS,wh] (.node [we,wd,wf,wc,wa,wb,wg,weT,wh] (.node [we,wd,wf,wc,wa,wb,wg,wey,wh] (.node [we,wd,wf,wc,wa,wb,wg,wb7,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wct,wh] (.node [we,wd,wf,wc,wa,wb,wg,wfg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wdA,wh] (.node [we,wd,wf,wc,wa,wb,wg,waw,wh] (.node [we,wd,wf,wc,wa,wb,wg,wfB,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wfU,wh] (.node [we,wd,wf,wc,wa,wb,wg,wai,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbabbb : everyKey (certRow 7 tree7) tree8bbabbb = true := by decide +kernel
def tree8bbabb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wbK,wh] tree8bbabba tree8bbabbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbabb : everyKey (certRow 7 tree7) tree8bbabb = true := splitCheck (by decide +kernel) ok_tree8bbabba ok_tree8bbabbb
def tree8bbab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wb9,wg,wh] tree8bbaba tree8bbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbab : everyKey (certRow 7 tree7) tree8bbab = true := splitCheck (by decide +kernel) ok_tree8bbaba ok_tree8bbabb
def tree8bba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wfQ,wg,wh] tree8bbaa tree8bbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bba : everyKey (certRow 7 tree7) tree8bba = true := splitCheck (by decide +kernel) ok_tree8bbaa ok_tree8bbab
def tree8bbbaaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wgD,wh] (.node [we,wd,wf,wc,wa,wb,wg,wg5,wh] (.node [we,wd,wf,wc,wa,wb,wg,wgJ,wh] (.node [we,wd,wf,wc,wa,wb,wg,wgg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wgZ,wh] (.node [we,wd,wf,wc,wa,wb,wg,whk,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wf0,wh] (.node [we,wd,wf,wc,wa,wb,wg,wgm,wh] (.node [we,wd,wf,wc,wa,wb,wg,whG,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wbQ,wh] (.node [we,wd,wf,wc,wa,wb,wg,wcd,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbaaa : everyKey (certRow 7 tree7) tree8bbbaaa = true := by decide +kernel
def tree8bbbaab : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wdW,wh] (.node [we,wd,wf,wc,wa,wb,wg,weD,wh] (.node [we,wd,wf,wc,wa,wb,wg,weY,wh] (.node [we,wd,wf,wc,wa,wb,wg,wbt,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wcz,wh] (.node [we,wd,wf,wc,wa,wb,wg,weh,wh] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wg,w2,wh] (.node [we,wd,wf,wc,wa,wb,wg,w2] (.node [we,wd,wf,wc,wa,wb,wg,wdh,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wh,wh] (.node [we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbaab : everyKey (certRow 7 tree7) tree8bbbaab = true := by decide +kernel
def tree8bbbaa : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wbt] tree8bbbaaa tree8bbbaab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbaa : everyKey (certRow 7 tree7) tree8bbbaa = true := splitCheck (by decide +kernel) ok_tree8bbbaaa ok_tree8bbbaab
def tree8bbbaba : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wh,wdf] (.node [we,wd,wf,wc,wa,wb,wg,wh,wcb] (.node [we,wd,wf,wc,wa,wb,wg,wh,wbO] (.node [we,wd,wf,wc,wa,wb,wg,wh,w0] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wh,waX] (.node [we,wd,wf,wc,wa,wb,wg,wh,wcx] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wg,wh,wgH] (.node [we,wd,wf,wc,wa,wb,wg,wh,wal] (.node [we,wd,wf,wc,wa,wb,wg,wh,wdV] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wh,whK] (.node [we,wd,wf,wc,wa,wb,wg,wh,wef] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbaba : everyKey (certRow 7 tree7) tree8bbbaba = true := by decide +kernel
def tree8bbbabb : BinaryTree (List W) := (.node [we,wd,wf,wc,wa,wb,wg,wh,who] (.node [we,wd,wf,wc,wa,wb,wg,wh,waz] (.node [we,wd,wf,wc,wa,wb,wg,wh,wa2] (.node [we,wd,wf,wc,wa,wb,wg,wh,weW] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wg,wh,wfY] (.node [we,wd,wf,wc,wa,wb,wg,wh,wg3] .nil .nil) .nil)) (.node [we,wd,wf,wc,wa,wb,wg,w0] (.node [we,wd,wf,wc,wa,wb,wg,wbr] (.node [we,wd,wf,wc,wa,wb,wg,wh,wgk] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wW,wh] (.node [we,wd,wf,wc,wa,wb,wbn,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbabb : everyKey (certRow 7 tree7) tree8bbbabb = true := by decide +kernel
def tree8bbbab : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wh,weB] tree8bbbaba tree8bbbabb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbab : everyKey (certRow 7 tree7) tree8bbbab = true := splitCheck (by decide +kernel) ok_tree8bbbaba ok_tree8bbbabb
def tree8bbba : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,wh,wbr] tree8bbbaa tree8bbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbba : everyKey (certRow 7 tree7) tree8bbba = true := splitCheck (by decide +kernel) ok_tree8bbbaa ok_tree8bbbab
def tree8bbbbaa : BinaryTree (List W) := (.node [we,wd,wf,wc,wj,waO,wb,wg,wh] (.node [we,wd,wf,wc,wa,wn,wg,wa4,wh] (.node [we,wd,wf,wc,wa,was,wn,wg,wh] (.node [we,wd,wf,wc,wa,wS,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wbj,wb,wg,wh] (.node [we,wd,wf,wc,wO,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wf,wr,wa,wb,wg,waU,wh] (.node [we,wd,wf,wr,wa,waO,wb,wg,wh] (.node [we,wd,wf,wc,wj,wb,wg,wh,wa2] .nil .nil) .nil) (.node [we,wd,wf,wq,wa,wb,wg,wh,waX] (.node [we,wd,wf,wr,wa,wb,wg,wh,waX] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbbaa : everyKey (certRow 7 tree7) tree8bbbbaa = true := by decide +kernel
def tree8bbbbab : BinaryTree (List W) := (.node [we,wd,wen,wc,wa,wb,wg,wh] (.node [we,wd,wJ,wc,wa,wb,wg,wh] (.node [we,wd,wf,wa,waS,wb,wn,wg,wh] (.node [we,wd,wf,wa,waO,wb,wn,wg,wh] .nil .nil) .nil) (.node [we,wd,wcH,wc,wa,wb,wg,wh] (.node [we,wd,wbf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [we,wd,wv,wc,wa,waE,wb,wg,wh] (.node [we,wd,wv,wc,waB,wa,wb,wg,wh] (.node [we,wd,we5,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wv,wc,wa,wb,wg,wh,waM] (.node [we,wd,wv,wc,wa,waI,wb,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbbab : everyKey (certRow 7 tree7) tree8bbbbab = true := by decide +kernel
def tree8bbbba : BinaryTree (List W) := .node [we,wd,wf,waB,wa,wb,wn,wg,wh] tree8bbbbaa tree8bbbbab
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbba : everyKey (certRow 7 tree7) tree8bbbba = true := splitCheck (by decide +kernel) ok_tree8bbbbaa ok_tree8bbbbab
def tree8bbbbba : BinaryTree (List W) := (.node [we,wu,wf,wc,wa,wb,wg,wh,waz] (.node [we,wu,wf,wc,wa,wj,wb,wg,wh] (.node [we,wu,wf,wM,wc,wa,wb,wg,wh] (.node [we,wbv,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wu,wf,wc,wa,wb,wg,waw,wh] (.node [we,wu,wf,wc,wa,wb,was,wg,wh] .nil .nil) .nil)) (.node [we,wf,wv,wc,wa,wb,wg,waw,wh] (.node [we,wf,wv,wc,wa,wb,was,wg,wh] (.node [we,wf,wv,wM,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wf,wM,wc,wq,wa,wb,wg,wh] (.node [we,wf,wv,wc,wa,wb,wg,wh,waz] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbbba : everyKey (certRow 7 tree7) tree8bbbbba = true := by decide +kernel
def tree8bbbbbb : BinaryTree (List W) := (.node [w5,wd,wu,wf,wc,wa,wb,wg,wh] (.node [we,wf,wc,wa,wj,wb,was,wg,wh] (.node [we,wf,wc,war,wa,wj,wb,wg,wh] (.node [we,wf,wc,wq,wa,wb,wg,waw,wh] .nil .nil) .nil) (.node [wa8,wd,wf,wc,wa,wb,wg,wh] (.node [wD,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wd,wf,wab,wc,wr,wa,wb,wg,wh] (.node [wd,wu,wf,wc,wa,wb,wg,wh,wal] (.node [wd,wu,wf,wc,wr,wa,wb,wg,wh] .nil .nil) .nil) (.node [wd,wf,wc,wr,wa,wb,wg,wai,wh] (.node [wd,wf,wc,wr,wa,wb,wae,wg,wh] .nil .nil) .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbbbb : everyKey (certRow 7 tree7) tree8bbbbbb = true := by decide +kernel
def tree8bbbbb : BinaryTree (List W) := .node [we,wf,wc,wq,wa,wb,was,wg,wh] tree8bbbbba tree8bbbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbbb : everyKey (certRow 7 tree7) tree8bbbbb = true := splitCheck (by decide +kernel) ok_tree8bbbbba ok_tree8bbbbbb
def tree8bbbb : BinaryTree (List W) := .node [we,wbb,wf,wc,wa,wb,wg,wh] tree8bbbba tree8bbbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbbb : everyKey (certRow 7 tree7) tree8bbbb = true := splitCheck (by decide +kernel) ok_tree8bbbba ok_tree8bbbbb
def tree8bbb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wey,wh] tree8bbba tree8bbbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bbb : everyKey (certRow 7 tree7) tree8bbb = true := splitCheck (by decide +kernel) ok_tree8bbba ok_tree8bbbb
def tree8bb : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wb,wg,waK,wh] tree8bba tree8bbb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8bb : everyKey (certRow 7 tree7) tree8bb = true := splitCheck (by decide +kernel) ok_tree8bba ok_tree8bbb
def tree8b : BinaryTree (List W) := .node [we,wd,wf,wc,wa,wdt,wb,wg,wh] tree8ba tree8bb
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8b : everyKey (certRow 7 tree7) tree8b = true := splitCheck (by decide +kernel) ok_tree8ba ok_tree8bb
def tree8 : BinaryTree (List W) := .node [we,wl,wd,wf,wc,wb,wa3,wg,wh] tree8a tree8b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree8 : everyKey (certRow 7 tree7) tree8 = true := splitCheck (by decide +kernel) ok_tree8a ok_tree8b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem closed8 : Closed 8 tree8 := checkedLayer 7 (by decide) _ _ closed7 ok_tree8
def tree9a : BinaryTree (List W) := (.node [wt,we,wd,wf,wc,wa,wb,wg,wh] (.node [wo,we,wd,wf,wc,wa,wb,wg,wh] (.node [wm,we,wd,wf,wc,wa,wb,wg,wh] (.node [wp,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [ws,we,wd,wf,wc,wa,wb,wg,wh] (.node [wy,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil)) (.node [wz,we,wd,wf,wc,wa,wb,wg,wh] (.node [wA,we,wd,wf,wc,wa,wb,wg,wh] (.node [ww,we,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wB,wd,wf,wc,wa,wb,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree9a : everyKey (certRow 8 tree8) tree9a = true := by decide +kernel
def tree9b : BinaryTree (List W) := (.node [we,wd,wf,wv,wc,wa,wb,wg,wh] (.node [we,wx,wd,wf,wc,wa,wb,wg,wh] (.node [we,wl,wd,wf,wc,wa,wb,wg,wh] (.node [we,wk,wd,wf,wc,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wu,wf,wc,wa,wb,wg,wh] .nil .nil)) (.node [we,wd,wf,wc,wa,wj,wb,wg,wh] (.node [we,wd,wf,wc,wq,wa,wb,wg,wh] (.node [we,wd,wf,wc,wr,wa,wb,wg,wh] .nil .nil) .nil) (.node [we,wd,wf,wc,wa,wb,wn,wg,wh] .nil .nil)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree9b : everyKey (certRow 8 tree8) tree9b = true := by decide +kernel
def tree9 : BinaryTree (List W) := .node [we,wi,wd,wf,wc,wa,wb,wg,wh] tree9a tree9b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ok_tree9 : everyKey (certRow 8 tree8) tree9 = true := splitCheck (by decide +kernel) ok_tree9a ok_tree9b
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem closed9 : Closed 9 tree9 := checkedLayer 8 (by decide) _ _ closed8 ok_tree9


def orbitRep0 : List W := [0x4200022001110010804844011100089240, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep1 : List W := [0x10002110000001002000400022010084080128, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep2 : List W := [0xf803e000000400000400000020040084400000f80be000000, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep3 : List W := [0xfffffc00000421084422000022249000000000dfff7c10402, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep4 : List W := [0x3e003fe00000000000000010800022220000013e04bfe000000000000, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep5 : List W := [0x3e003fe0007c0000fe000000000022221112491e049ee0113c4089fe8, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep6 : List W := [0x7c01fc000ff8003ff0000000422110000000005c81fc440bd9003ff240, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep7 : List W := [0x7ffe00000fffffc000000000000004444222493dee808087bbdec10402, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep8 : List W := [0x7ffe00000fffffc000000000844220000000005ef680808bddef410402, 0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep9 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0x7ffffffff000000000000001088440000000005ef7fef7f20008100010, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep10 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xf000078000001e00000000003c000010040010f0000f8000401e04000880007c200, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep11 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xf0f0000000001e3e1c00000000000040100040f0f0000000423e3e1c00000000000, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep12 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xf0f00780e0001e3e1c0000003cf0300000000070700b81e0422e1e0c0884245cf07, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep13 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff00000000000077007bb003c80ec4407b9001dd240, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep14 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xff00fff007ffffc000ffffffff0006318c6633ff44fff497ffffcc48ffffffff642, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep15 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0xfffffff007ffffffffff8003ff000a5294aa55fffffff807ffffffffff9083ff250, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep16 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x3ff0000000000007ffe03fe0fffffc00fe05297ff52266663336dfffecbfe8fffffc99fea, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep17 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x3ff000ff00fff007fe1fffe0fffc03fffe0318fff311ff22fff24ffe1fffe0fffc43fffe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep18 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0x7c3e0078fff0fff0e7c01ffe1cff8003fff032fcbe22f9fff0fff1e7ca3ffe5cff9427fff47, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitRep19 : List W := [0x7ffe00000fffffc000004210844224444222497ffe80808fffffc10402, 0xff00fff007c01fc000ff8003ff000210842211ff00fff007c81fc440ff9003ff240, 0xffff000007ffffffff00000000000842108844ffff400807ffffffff20008100010, 0x3ff00000000000003e003fe0007c0000fe01087ff10022221112493e04bfe0117c4089fe8, 0x7c3e0078f0f00780e0001e3e1c0000003cf030fc3e00f8f0f00f81e0423e3e1c0884247cf07, 0xf80000f800000f80f0000000000f803e3c001cf84021f881111f88f2084424225f80be3c413d, 0xf803fff800000f80f003e003fe0f87fe3c0ffcf8c7fff883333f99f69be46ffe5f97fe3cdffd, 0xfffc00000fffffffff80000000000000000000fffe10000fffffffffa1080108042210800880, 0xfffffffff00000000000000000000000000000fffffffff88888440042111211284421222000]
def orbitTree : BinaryTree (List W) := (.node orbitRep10 (.node orbitRep5 (.node orbitRep2 (.node orbitRep1 (.node orbitRep0 .nil .nil) .nil) (.node orbitRep4 (.node orbitRep3 .nil .nil) .nil)) (.node orbitRep8 (.node orbitRep7 (.node orbitRep6 .nil .nil) .nil) (.node orbitRep9 .nil .nil))) (.node orbitRep15 (.node orbitRep13 (.node orbitRep12 (.node orbitRep11 .nil .nil) .nil) (.node orbitRep14 .nil .nil)) (.node orbitRep18 (.node orbitRep17 (.node orbitRep16 .nil .nil) .nil) (.node orbitRep19 .nil .nil))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def orbitHash : List W → Nat
  | [] => 0
  | w :: t => ((w.toNat % 65521 + 1) ^ 3) % 65521 + orbitHash t
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def proposed (j : Nat) : Fin 8 :=
  match j with
  | 144 => 3
  | 5253 => 2
  | 5021 => 4
  | 3395 => 1
  | 170 => 5
  | 8730 => 1
  | 3736 => 6
  | 9502 => 7
  | 12277 => 6
  | 15084 => 6
  | 741 => 5
  | 15363 => 5
  | 8144 => 3
  | 9322 => 3
  | 1626 => 6
  | 6972 => 6
  | 12768 => 6
  | 841 => 1
  | 15757 => 7
  | 2177 => 5
  | 477 => 6
  | 15937 => 3
  | 16372 => 3
  | 24 => 2
  | 4312 => 2
  | 4392 => 1
  | 9429 => 4
  | 12525 => 4
  | 12709 => 5
  | 15208 => 6
  | 7964 => 7
  | 15071 => 6
  | 15898 => 6
  | 6265 => 1
  | 2649 => 7
  | 4764 => 4
  | 4688 => 3
  | 10734 => 2
  | 12020 => 3
  | 5482 => 4
  | 2616 => 3
  | 12134 => 3
  | 10902 => 7
  | 15762 => 7
  | 10160 => 2
  | 13372 => 1
  | 12692 => 1
  | 1471 => 7
  | 13777 => 2
  | 3828 => 4
  | 2156 => 3
  | 9601 => 2
  | 6326 => 3
  | 12974 => 3
  | 712 => 3
  | 4443 => 7
  | 1270 => 7
  | 9591 => 2
  | 7865 => 4
  | 12385 => 5
  | 15351 => 2
  | 157 => 1
  | 12806 => 1
  | 9536 => 5
  | 8810 => 5
  | 12238 => 1
  | 6418 => 6
  | 7104 => 5
  | 10638 => 4
  | 3426 => 2
  | 2710 => 1
  | 8590 => 1
  | 3092 => 4
  | 6214 => 4
  | 5250 => 5
  | 2229 => 1
  | 3886 => 5
  | 8159 => 4
  | 11933 => 5
  | 1815 => 1
  | 13036 => 2
  | 11283 => 4
  | 2369 => 2
  | 15989 => 2
  | 4887 => 4
  | 3643 => 4
  | 15189 => 1
  | 6880 => 1
  | 13469 => 2
  | 8653 => 1
  | 12742 => 7
  | 10146 => 4
  | _ => 0
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def sourceWord (j : Nat) : W := ins.getD (j % 8) 0
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def rotatedIndex (i : Fin 8) : Nat := ![0xfac688, 0x5717e0, 0x977053, 0x3aa13b, 0x8c7c8d, 0x2c2be6, 0xe1ca56, 0x419d3d] i

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def rotatedWord (i : Fin 8) (j : Nat) : W :=
  ins.getD ((rotatedIndex i >>> (3 * (j % 8))) &&& 7) 0
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma rotatedWord_eq (i : Fin 8) (j : Nat) : sym i (sourceWord j) = rotatedWord i j := by
  have bits : ∀ (i a : Fin 8) (b : Fin 304), (sourceWord a.val)[(co i b).val] =
        (rotatedWord i a.val)[b.val] := by decide +kernel
  have hb (i j : Fin 8) : sym i (sourceWord j.val) = rotatedWord i j.val := by
    apply BitVec.eq_of_getElem_eq
    intro b hb
    rw [sym_bit i _ ⟨b,hb⟩]
    exact bits i j ⟨b,hb⟩
  simpa only [sourceWord,rotatedWord,Nat.mod_mod] using hb i ⟨j % 8, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def evalCode (raw : Nat → W) (c : Nat) : W :=
  if c < 8 then raw c else
    let j := c - 8
    let a := raw (j / 32)
    let b := raw ((j / 4) % 8)
    match j % 4 with
    | 0 => a &&& b
    | 1 => a ||| b
    | 2 => a &&& ~~~b
    | _ => b &&& ~~~a
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma evalCode_sym (i : Fin 8) (c : Nat) : sym i (evalCode sourceWord c) = evalCode (rotatedWord i) c := by
  unfold evalCode
  split
  · apply rotatedWord_eq
  · dsimp only
    split <;> simp [sym_and, sym_or, sym_not, rotatedWord_eq]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def wordCode (w : W) : Nat :=
  match w.toNat % 65521 with
  | 16243 => 84
  | 14463 => 24
  | 56530 => 12
  | 10428 => 48
  | 3436 => 96
  | 51947 => 132
  | 33892 => 160
  | 30627 => 164
  | 63767 => 60
  | 31343 => 196
  | 22264 => 56
  | 38331 => 158
  | 54399 => 88
  | 56275 => 92
  | 27946 => 102
  | 45326 => 123
  | 35157 => 120
  | 38568 => 130
  | 26084 => 91
  | 42152 => 156
  | 58219 => 59
  | 49856 => 166
  | 46591 => 162
  | 499 => 27
  | 14962 => 4
  | 58784 => 194
  | 5519 => 52
  | 40571 => 70
  | 16146 => 126
  | 54933 => 127
  | 52188 => 23
  | 27901 => 31
  | 49154 => 20
  | 46707 => 28
  | 42018 => 38
  | 19675 => 124
  | 30302 => 55
  | 62774 => 128
  | 664 => 122
  | 49395 => 134
  | 19578 => 87
  | 35821 => 3
  | 15626 => 121
  | 15824 => 192
  | 32456 => 159
  | 18333 => 95
  | 43265 => 198
  | 10841 => 63
  | 9087 => 5
  | 47418 => 157
  | 25233 => 125
  | 37320 => 230
  | 1453 => 66
  | 46006 => 19
  | 31981 => 16
  | 37460 => 34
  | 50041 => 100
  | 21712 => 94
  | 23588 => 90
  | 9030 => 98
  | 2038 => 51
  | 61744 => 86
  | 12466 => 2
  | 38550 => 89
  | 32044 => 85
  | 30799 => 93
  | 10695 => 231
  | 32469 => 32
  | 37948 => 18
  | 27911 => 36
  | 23222 => 30
  | 20775 => 22
  | 13399 => 14
  | 55466 => 26
  | 4408 => 0
  | 4907 => 25
  | 56596 => 21
  | 32309 => 29
  | 50414 => 17
  | 57796 => 67
  | 4768 => 71
  | 20803 => 64
  | 47206 => 68
  | 16737 => 54
  | 65513 => 58
  | 24010 => 62
  | 11828 => 50
  | 31247 => 15
  | 22256 => 1
  | 14954 => 57
  | 52558 => 53
  | 33097 => 61
  | 24294 => 49
  | 46130 => 35
  | 24063 => 39
  | 35655 => 13
  | 41279 => 228
  | 62775 => 195
  | 15825 => 131
  | 44707 => 163
  | 9642 => 99
  | 13078 => 6
  | 51646 => 129
  | 59669 => 161
  | 6341 => 193
  | 14531 => 65
  | 1933 => 103
  | 50538 => 33
  | 22108 => 97
  | 20631 => 199
  | 21347 => 167
  | 27 => 135
  | 51974 => 7
  | 14399 => 101
  | 36309 => 165
  | 27024 => 69
  | 28471 => 37
  | 35848 => 133
  | 29718 => 197
  | 23773 => 229
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def orbitKey (ws : List W) : List W :=
  let i := proposed (orbitHash ws % 16381)
  ordered (ws.map (fun w => evalCode (rotatedWord i) (wordCode w)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def goodCodes (ws : List W) : Bool := ws.all (fun w => evalCode sourceWord (wordCode w) == w)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
def outsideReps (ws : List W) : Bool := !(goodCodes ws && containsKey (orbitKey ws) orbitTree)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma orbit_sound {ys : List W} (hc : goodCodes ys = true) : orbitKey ys =
    ordered (ys.map (sym (proposed (orbitHash ys % 16381)))) := by
  apply congrArg ordered
  apply List.map_congr_left
  intro w hw
  have h := beq_iff_eq.mp (List.all_eq_true.mp hc w hw)
  rw [← evalCode_sym, h]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma firstSetCovers : (doneTest ins || descend 9 ins outsideReps) = false := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma subCover : ins.sublists.all (fun ys => !(cuts ys == -1) || ys == ins) = true := by decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
lemma distinctIns : ins.Nodup := by unfold ins; decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem lower_of_tree9 (tr : BinaryTree (List W)) (hc : Closed 9 tr)
    (hm : everyKey (fun q => containsKey q tr) orbitTree = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g 10 ins.toFinset := by
  intro hb
  classical
  obtain ⟨s,hs,hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hl' : live basicOps g 10 ws.toFinset := eq.symm ▸ hl
  have hsub : ws.Sublist ins := List.filter_sublist ..
  have hstart := List.all_eq_true.mp subCover ws (List.mem_sublists.mpr hsub)
  have hfull : ws = ins := by simpa [cuts_full hg hl'] using hstart
  rw [hfull] at hl'
  have hit := descend_sound hg distinctIns hl' outsideReps (by
    intro ys hy hrun
    let i := proposed (orbitHash ys % 16381)
    have move := symOK i 9 g hg ys hrun
    have perm := ordered_perm (ys.map (sym i))
    rw [outsideReps,Bool.not_eq_true',Bool.eq_false_iff]
    intro hh
    simp only [Bool.and_eq_true] at hh
    obtain ⟨good, hp⟩ := hh
    have hkey := orbit_sound good
    have st : live basicOps g 9 (orbitKey ys).toFinset := by
      rw [hkey,perm_set perm]; exact move
    have nd : (orbitKey ys).Nodup := by
      rw [hkey]; exact perm.nodup_iff.mpr (hy.map (sym_injective i))
    have len := live_card st
    rw [List.toFinset_card_of_nodup nd] at len
    exact hc g hg _ nd (by omega) (every_at orbitTree hm hp) st)
  have no := firstSetCovers
  cases hd : doneTest ins <;> cases ht : descend 9 ins outsideReps <;> simp [hd,ht] at hit no

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem lower (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g 10 ins.toFinset := lower_of_tree9 tree9 closed9 (by decide +kernel) g hg
end H8Free

end PEqualNP.Outside.L_meta_3068_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3068_aux
theorem PEqualNP.Outside.L_meta_3068 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  have pin := PinFour.pin_four
  have single := Meta3068OneNot.remove_only_not_rec
  have positive := Pos3068.positive
  have multiple := H8Free.core_two H8Free.lower
  intro gs pins hlen hfan _ _
  by_contra hbad
  let E := fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
      x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let w := fun x : Fin 9 → Bool => (Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])
  have he (x : Fin 9 → Bool) :
      GateOp.not.eval (pins.map fun i => (w x).getD i.val false) = E x := by
    exact not_ne_iff.mp (fun h => hbad ⟨x,h⟩)
  cases pins with
  | nil =>
    have h := he (fun _ => false)
    change true = false at h
    contradiction
  | cons i rest =>
    let C : Circuit := ⟨gs,i.val⟩
    have hC (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 4 || x 6]) = !(E x) := by
      have h := he x
      change (!((w x).getD i.val false)) = E x at h
      change (w x).getD i.val false = !(E x)
      simpa only [Bool.not_not] using congrArg Bool.not h
    obtain ⟨D,hm,hs,heval⟩ := pin C hfan (by dsimp only; rw [hC,hC]; decide) (by dsimp only; rw [hC,hC]; decide)
    let F := fun y : Fin 8 → Bool => (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4)
    have hsize : D.size ≤ 12 := by
      change D.size + 1 ≤ gs.length at hs
      omega
    have hD (y : Fin 8 → Bool) : D.eval (List.ofFn y) = !(F y) := by
      change D.eval (List.ofFn y) = _
      rw [heval]; dsimp only; rw [hC]
      change (!(y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && false || false && y 0 ||
        y 0 && y 4 || y 1 && y 5 || y 2 && y 6 || y 3 && y 7 ||
        y 4 && y 6 || y 5 && y 7 || y 7 && y 4)) = _
      simp only [Bool.and_false,Bool.false_and,Bool.or_false] <;> rfl
    by_cases hn : D.gates.countP (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ 1
    · obtain ⟨D',hf',hs',he'⟩ := single 8 D F hm hn rfl rfl hD
      exact positive ⟨D',hf',hs'.trans hsize,he'⟩
    · exact multiple D hm hsize (by omega) hD
