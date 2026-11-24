import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2895_aux

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

namespace Compress2895

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

end Compress2895

namespace Cut2895

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

abbrev Lit := Option (Fin 9) × Bool

def val (l : Lit) (x : Fin 9 → Bool) := (l.1.elim false x) ^^ l.2

def src (k : ℕ) : Option (Fin 9) := if h : k < 9 then some ⟨k,h⟩ else none

theorem source_value (k : ℕ) (x : Fin 9 → Bool) :
    (List.ofFn x ++ [false]).getD k false = (src k).elim false x := by
  by_cases h : k < 9
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
    simp only [src,dif_pos h,Option.elim_some]
  · by_cases e : k = 9
    · subst k; simp [src,List.getD_append_right]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [src,h]

theorem second_literal (g : Gate) (hok : Ok g) (hr : 9 ∈ g.inputs) :
    ∃ l : Lit, ∀ x : Fin 9 → Bool,
      g.op.eval (g.inputs.map fun k => (List.ofFn x ++ [false]).getD k false) = val l x := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨ops,hlen⟩ := hok
  change ins.length ≤ 2 at hlen
  change 9 ∈ ins at hr
  change op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
  cases ins with
  | nil => simp at hr
  | cons a xs =>
    cases xs with
    | nil =>
      simp only [List.mem_singleton] at hr
      subst a
      rcases ops with rfl|rfl|rfl
      · exact ⟨(none,false),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
      · exact ⟨(none,false),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
      · exact ⟨(none,true),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
    | cons b xs =>
      have emp : xs = [] := by apply List.eq_nil_of_length_eq_zero; simp only [List.length_cons] at hlen; omega
      subst xs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with h|h
      · subst a
        rcases ops with rfl|rfl|rfl
        · exact ⟨(none,false),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
        · exact ⟨(src b,false),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
        · exact ⟨(none,true),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
      · subst b
        rcases ops with rfl|rfl|rfl
        · exact ⟨(none,false),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
        · exact ⟨(src a,false),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩
        · exact ⟨(src a,true),by intro x; simp only [List.map_cons,List.map_nil,source_value]; simp [GateOp.eval,val,show src 9 = none from rfl]⟩

def index (l : Lit) : Fin 8 := l.1.elim 0 (fun j => (6 : Fin 8).predAbove j)

def inMap (σ : Fin 8 → Fin 8) (j : Fin 9) : Stat :=
  if j = 6 then Sum.inl false else Sum.inr (σ ((6 : Fin 8).predAbove j)).val

def litMap (σ : Fin 8 → Fin 8) (l : Lit) : Stat :=
  match l.1 with
  | none => Sum.inl l.2
  | some j => if j = 6 then Sum.inl l.2 else if l.2 then Sum.inr 8 else inMap σ j

def mapt (σ : Fin 8 → Fin 8) (l : Lit) : List Stat :=
  List.ofFn (inMap σ) ++ [Sum.inl false, litMap σ l]

def old (l : Lit) (x : Fin 9 → Bool) := List.ofFn x ++ [false,val l x]
def newv (l : Lit) (σ : Fin 8 → Fin 8) (y : Fin 8 → Bool) :=
  List.ofFn y ++ [!(y (σ (index l)))]

theorem insert_val (j : Fin 9) (h : j ≠ 6) (y : Fin 8 → Bool) :
    Fin.insertNth (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false y j = y ((6 : Fin 8).predAbove j) := by
  fin_cases j <;> first | contradiction | rfl

theorem raw_map (l : Lit) (σ : Fin 8 → Fin 8) (y : Fin 8 → Bool) (j : Fin 9) :
    (inMap σ j).val (newv l σ y) = Fin.insertNth (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false (y ∘ σ) j := by
  by_cases e : j = 6
  · subst j; simp [inMap,Stat.val]
  rw [insert_val _ e]
  let i := σ ((6 : Fin 8).predAbove j)
  change Stat.val _ (if j = 6 then Sum.inl false else Sum.inr i.val) = _
  rw [if_neg e]
  change (List.ofFn y ++ _).getD i.val false = y i
  rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]

theorem lit_map (l : Lit) (σ : Fin 8 → Fin 8) (y : Fin 8 → Bool) :
    (litMap σ l).val (newv l σ y) = val l (Fin.insertNth (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false (y ∘ σ)) := by
  obtain ⟨p,b⟩ := l
  cases p with
  | none => cases b <;> rfl
  | some j =>
    by_cases e : j = 6
    · subst j; cases b <;> rfl
    have h := raw_map (some j,false) σ y j
    cases b
    · simpa [litMap,e,val] using h
    · simp [litMap,e,val,Stat.val,newv,index,List.getD_append_right,insert_val _ e]

theorem get_init {α : Type} (r : Fin 9 → α) (a b d : α) (k : ℕ) :
    (List.ofFn r ++ [a,b]).getD k d =
      if hk : k < 9 then r ⟨k,hk⟩ else if k = 9 then a else if k = 10 then b else d := by
  by_cases hk : k < 9
  · rw [List.getD_append _ _ _ _ (by simpa using hk)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hk),List.getElem_ofFn,dif_pos hk]
  · simp only [dif_neg hk]
    by_cases h : k = 9
    · subst k; simp [List.getD_append_right]
    by_cases h' : k = 10
    · subst k; simp [List.getD_append_right]
    rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [h,h']

theorem valid_map (σ : Fin 8 → Fin 8) (l : Lit) (k : ℕ) :
    ((mapt σ l).getD k (Sum.inl false)).Valid 9 := by
  unfold mapt
  rw [get_init]
  split
  · unfold inMap; split
    · trivial
    · change _ < 9; exact Nat.lt_trans (Fin.isLt _) (by decide : 8 < 9)
  · split
    · trivial
    split
    · obtain ⟨p,b⟩ := l
      cases p with
      | none => trivial
      | some j =>
        simp only [litMap]
        split
        · trivial
        split
        · exact (by decide : 8 < 9)
        unfold inMap; split
        · trivial
        · change _ < 9; exact Nat.lt_trans (Fin.isLt _) (by decide : 8 < 9)
    · trivial

theorem map_values (σ : Fin 8 → Fin 8) (l : Lit) (y : Fin 8 → Bool) (k : ℕ) :
    ((mapt σ l).getD k (Sum.inl false)).val (newv l σ y) =
    (old l (Fin.insertNth (α := fun _ : Fin 9 => Bool) (6 : Fin 9) false (y ∘ σ))).getD k false := by
  unfold mapt old
  rw [get_init,get_init]
  by_cases h : k < 9
  · simp only [dif_pos h]; exact raw_map _ _ _ _
  · simp only [dif_neg h]
    by_cases h9 : k = 9
    · simp [h9,Stat.val]
    by_cases h10 : k = 10
    · simp only [if_neg h9,if_pos h10]; exact lit_map _ _ _
    · simp [h9,h10,Stat.val]

def probeA (j : Fin 9) := decide (j = 1)
def probeB (j : Fin 9) := decide (j = 1 ∨ j = 6)

theorem agree_map (σ : Fin 8 → Fin 8) (l : Lit) (k i : ℕ)
    (e : (mapt σ l).getD k (Sum.inl false) = Sum.inr i) :
    (old l probeA).getD k false = (old l probeB).getD k false := by
  unfold mapt at e
  unfold old
  rw [get_init] at e
  rw [get_init,get_init]
  by_cases h : k < 9
  · simp only [dif_pos h] at e ⊢
    have hn : (⟨k,h⟩ : Fin 9) ≠ 6 := by intro eq; simp [inMap,eq] at e
    simp [probeA,probeB,hn]
  · simp only [dif_neg h] at e ⊢
    by_cases h9 : k = 9
    · simp [h9]
    by_cases h10 : k = 10
    · simp only [if_neg h9,if_pos h10] at e ⊢
      obtain ⟨p,b⟩ := l
      cases p with
      | none => rfl
      | some j =>
        have hn : j ≠ 6 := by rintro rfl; simp [litMap] at e
        simp [val,probeA,probeB,hn]
    · simp [h9,h10]

end Cut2895

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers Cut2895

theorem main2895 : ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool), ((x1 fun (x2 : Fin (9 : ℕ)) => Decidable.decide (x2 = (1 : Fin (9 : ℕ)))) ≠ x1 fun (x2 : Fin (9 : ℕ)) => Decidable.decide (x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)))) → x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false fun (x3 : Fin (8 : ℕ)) => Bool.false) ≠ x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false fun (x3 : Fin (8 : ℕ)) => Bool.true) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ x5 ∈ x4.gates[(1 : ℕ)]?.toList, (9 : ℕ) ∈ x5.inputs) → PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = (x7 (0 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x4 = x1 → ∃ (x9 : Fin (8 : ℕ)), ∀ (x10 : Fin (8 : ℕ) → Fin (8 : ℕ)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (3 : ℕ) ≤ x4.size ∧ ∀ (x12 : Fin (8 : ℕ) → Bool), x11.eval (List.ofFn x12 ++ [!x12 (x10 x9)]) = x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (x12 ∘ x10)) := by
  intro f hprobe hnc C hr hfan h9 hfun
  obtain ⟨g,hmem,hread⟩ := hr
  cases hgs : C.gates with
  | nil => simp [hgs] at hmem
  | cons a tail =>
    cases tail with
    | nil => simp [hgs] at hmem
    | cons b gs =>
      have hbg : b = g := by simpa [hgs, eq_comm] using hmem
      subst g
      have hgood : Ok b := hfan b (by simp [hgs])
      obtain ⟨l,hl⟩ := second_literal b hgood hread
      let aval := fun x : Fin 9 → Bool => a.op.eval (a.inputs.map fun k => (List.ofFn x).getD k false)
      have hfirst (x : Fin 9 → Bool) : aval x = (x 0 && x 6) := by
        have h := h9 x
        rw [wires_eq,hgs] at h
        change (wiresFrom (b :: gs) (List.ofFn x ++ [aval x])).getD 9 false = _ at h
        rw [getD_wiresFrom _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)] at h
        simpa only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero] using h
      have heval (x : Fin 9 → Bool) (hx : (x 0 && x 6) = false) :
          (wiresFrom gs (old l x)).getD C.output false = f x := by
        have h := congrFun hfun x
        change (C.wires (List.ofFn x)).getD C.output false = _ at h
        rw [wires_eq,hgs] at h
        change (wiresFrom gs ((List.ofFn x ++ [aval x]) ++ [b.op.eval
          (b.inputs.map fun k => (List.ofFn x ++ [aval x]).getD k false)])).getD C.output false = _ at h
        rw [hfirst x,hx,hl x] at h
        simpa only [old,List.append_assoc,List.cons_append,List.nil_append] using h
      have hA : (probeA 0 && probeA 6) = false := by decide
      have hB : (probeB 0 && probeB 6) = false := by decide
      have hrest (y : Fin 8 → Bool) :
          (((Fin.insertNth (α := fun _ => Bool) (6 : Fin 9) false y) 0) && ((Fin.insertNth (α := fun _ => Bool) (6 : Fin 9) false y) 6)) = false := by simp
      refine ⟨index l,?_⟩
      intro σ
      let z := fun y : Fin 8 → Bool => old l ((6 : Fin 9).insertNth false (y ∘ σ))
      have hres (y : Fin 8 → Bool) : (wiresFrom gs (z y)).getD C.output false =
          f ((6 : Fin 9).insertNth false (y ∘ σ)) := heval _ (hrest _)
      have hdiff : (wiresFrom gs (old l probeA)).getD C.output false ≠
          (wiresFrom gs (old l probeB)).getD C.output false := by
        rw [heval _ hA, heval _ hB]; exact hprobe
      have hncd : ∃ y y', (wiresFrom gs (z y)).getD C.output false ≠
          (wiresFrom gs (z y')).getD C.output false := by
        refine ⟨fun _ => false,fun _ => true,?_⟩
        rw [hres,hres]; exact hnc
      obtain ⟨D,hD,hs,he⟩ := Compress2895.compressTail 9 gs C.output (mapt σ l)
        (old l probeA) (old l probeB) (newv l σ) z
        (fun g hg => hfan g (by simp [hgs,hg])) (by simp [old,mapt]) (by simp [old,mapt])
        (fun _ => by simp [newv]) (fun _ => by simp [z,old,mapt])
        (valid_map σ l) (agree_map σ l) (map_values σ l) hdiff hncd
      refine ⟨D,hD,?_,fun y => (he y).trans (hres y)⟩
      have hsize : C.size = gs.length + 2 := by simp [Circuit.size,hgs]
      omega

end PEqualNP.Outside.L_meta_2895_aux

theorem PEqualNP.Outside.L_meta_2895 : ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool), ((x1 fun (x2 : Fin (9 : ℕ)) => Decidable.decide (x2 = (1 : Fin (9 : ℕ)))) ≠ x1 fun (x2 : Fin (9 : ℕ)) => Decidable.decide (x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)))) → x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false fun (x3 : Fin (8 : ℕ)) => Bool.false) ≠ x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false fun (x3 : Fin (8 : ℕ)) => Bool.true) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ x5 ∈ x4.gates[(1 : ℕ)]?.toList, (9 : ℕ) ∈ x5.inputs) → PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = (x7 (0 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x4 = x1 → ∃ (x9 : Fin (8 : ℕ)), ∀ (x10 : Fin (8 : ℕ) → Fin (8 : ℕ)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (3 : ℕ) ≤ x4.size ∧ ∀ (x12 : Fin (8 : ℕ) → Bool), x11.eval (List.ofFn x12 ++ [!x12 (x10 x9)]) = x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (x12 ∘ x10)) :=
  PEqualNP.Outside.L_meta_2895_aux.main2895
