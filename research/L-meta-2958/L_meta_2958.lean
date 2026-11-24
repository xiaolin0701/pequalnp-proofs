import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2958_aux

-- Basic circuit semantics and constant propagation from the project proof of L_meta_720.
open PEqualNP.MetaComplexity
namespace Helpers
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

noncomputable def charged (g : Gate) : Bool :=
  GateOp.rec true true false (fun _ => true) true g.op

noncomputable def cost (gs : List Gate) : ℕ := gs.countP charged



-- A surviving charged gate has two live operands. A surviving NOT has one.
-- Hence if no charged gate is lost, probes agreeing on live wires still agree.
theorem step_account (op : GateOp) (m : ℕ) (ins : List ℕ)
    (M : ℕ → Stat) (u v : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hag : ∀ i j, M i = Sum.inr j → u i = v i) :
    let r := simplify op m (ins.map M)
    let original := cost [⟨op, ins⟩]
    cost r.1.toList ≤ original ∧
      (cost r.1.toList = original → ∀ j, r.2 = Sum.inr j →
        op.eval (ins.map u) = op.eval (ins.map v)) := by
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try have ha := hag a; cases hma : M a) <;>
    (try have hb := hag b; cases hmb : M b) <;>
    simp_all [simplify, simpAnd, simpOr, simpNot, cost, charged, GateOp.eval]

theorem weakCost (n : ℕ) (gs : List Gate) : ∀ (acc : List Stat × List Gate),
    (∀ g ∈ gs, Ok g) → cost (elim n gs acc).2 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil => intros; simp [elim,cost]
  | cons g gs ih =>
    intro acc hok
    have hg := hok g List.mem_cons_self
    have h := (step_account g.op (n + acc.2.length) g.inputs
        (fun i => acc.1.getD i (Sum.inl false)) (fun _ => false) (fun _ => false)
        hg.1 hg.2 (fun _ _ _ => rfl)).1
    change cost (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ≤ cost [g] at h
    have ht := ih (elimStep n acc g) (fun g' h' => hok g' (List.mem_cons_of_mem _ h'))
    show cost (elim n gs (elimStep n acc g)).2 ≤ _
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    rw [hcons]
    have hadd : cost (elimStep n acc g).2 = cost acc.2 +
        cost (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList :=
      List.countP_append
    rw [hadd] at ht
    omega

theorem strictCost (n : ℕ) (gs : List Gate) (out j : ℕ) :
    ∀ (acc : List Stat × List Gate) (u v : List Bool),
      (∀ g ∈ gs, Ok g) → u.length = acc.1.length → v.length = acc.1.length →
      (∀ i k, acc.1.getD i (Sum.inl false) = Sum.inr k → u.getD i false = v.getD i false) →
      (elim n gs acc).1.getD out (Sum.inl false) = Sum.inr j →
      (wiresFrom gs u).getD out false ≠ (wiresFrom gs v).getD out false →
      cost (elim n gs acc).2 + 1 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil =>
    intro acc u v _ _ _ hag hj hdiff
    exact (hdiff (hag out j hj)).elim
  | cons g gs ih =>
    intro acc u v hok hu hv hag hj hdiff
    let M := fun i => acc.1.getD i (Sum.inl false)
    let r := simplify g.op (n + acc.2.length) (g.inputs.map M)
    have hg := hok g List.mem_cons_self
    have ha := step_account g.op (n + acc.2.length) g.inputs M
      (fun i => u.getD i false) (fun i => v.getD i false) hg.1 hg.2 hag
    change cost r.1.toList ≤ cost [g] ∧ _ at ha
    have hcost : cost (elimStep n acc g).2 = cost acc.2 + cost r.1.toList := by
      apply List.countP_append
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    have htail (g' : Gate) (h' : g' ∈ gs) := hok g' (List.mem_cons_of_mem _ h')
    change cost (elim n gs (elimStep n acc g)).2 + 1 ≤ _
    rw [hcons]
    by_cases heq : cost r.1.toList = cost [g]
    · let U := g.op.eval (g.inputs.map fun i => u.getD i false)
      let V := g.op.eval (g.inputs.map fun i => v.getD i false)
      have hnext := ih (elimStep n acc g) (u ++ [U]) (v ++ [V]) htail
        (by simp [elimStep,hu]) (by simp [elimStep,hv]) (by
          intro i k h
          change (acc.1 ++ [r.2]).getD i (Sum.inl false) = Sum.inr k at h
          by_cases hi : i = acc.1.length
          · subst i
            rw [getD_snoc_eq] at h
            rw [← hu, getD_snoc_eq, hu, ← hv, getD_snoc_eq]
            exact ha.2 heq k h
          · rw [getD_snoc_ne _ _ _ _ hi] at h
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag i k h) hj hdiff
      omega
    · have hweak := weakCost n gs (elimStep n acc g) htail
      omega

-- Track the surviving input wire for each occurrence in the original input list.
def pinStat {n : ℕ} (p : Fin (n+1)) : Fin (n+1) → Stat :=
  Fin.insertNth (α := fun _ => Stat) p (Sum.inl false) (fun j => Sum.inr j.val)

theorem pinStat_valid {n : ℕ} (p i : Fin (n+1)) : (pinStat p i).Valid n := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.Valid]
  · rename_i j
    simpa [pinStat, Stat.Valid] using j.isLt

theorem pinStat_val {n : ℕ} (p i : Fin (n+1)) (y : Fin n → Bool) :
    (pinStat p i).val (List.ofFn y) = Fin.insertNth (α := fun _ => Bool) p false y i := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.val]
  · rename_i j
    simp only [pinStat, Fin.insertNth_apply_succAbove, Stat.val]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),List.getElem_ofFn]

theorem getMap {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (d : β) :
    (l.map f).getD i d = if h : i < l.length then f l[i] else d := by
  by_cases h : i < l.length
  · rw [dite_eq_left h,List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map]
  · rw [dite_eq_right h,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]

theorem pinValid {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).Valid n := by
  rw [getMap]; split
  · exact pinStat_valid _ _
  · trivial

theorem pinMap {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (y : Fin n → Bool) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).val (List.ofFn y) =
      (l.map (Fin.insertNth (α := fun _ => Bool) p false y)).getD k false := by
  rw [getMap,getMap]; split
  · exact pinStat_val _ _ _
  · rfl

theorem pinAgree {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (x : Fin (n+1) → Bool) (k j : ℕ)
    (h : (l.map (pinStat p)).getD k (Sum.inl false) = Sum.inr j) :
    (l.map (Function.update x p true)).getD k false = (l.map (Function.update x p false)).getD k false := by
  rw [getMap] at h
  rw [getMap,getMap]
  by_cases hk : k < l.length
  · simp only [dite_eq_left hk] at h ⊢
    have e : l[k] ≠ p := by
      intro e
      simp [e,pinStat] at h
    simp [Function.update_of_ne e]
  · simp [hk]


theorem restrict2958 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11) := by
  dsimp only
  intro n p C l hfan
  intro hprobe hnc
  obtain ⟨x, hx⟩ := hprobe
  let M := l.map (pinStat p)
  let gs := C.gates
  let acc := elim n gs (M,[])
  have hok (g) (hg : g ∈ gs) : Ok g := hfan g hg
  have hval (y : Fin n → Bool) : (acc.1.getD C.output (Sum.inl false)).val
      (wiresFrom acc.2 (List.ofFn y)) = C.eval (l.map (p.insertNth false y)) := by
    let z := l.map (p.insertNth false y)
    have hi : Inv n (List.ofFn y) z (M,[]) := by
      refine ⟨by simp [M,z],?_⟩
      intro k
      exact ⟨pinValid p l k,pinMap p l y k⟩
    have he := ((inv_elim n (List.ofFn y) (by simp) gs z (M,[]) hok hi).2 C.output).2
    exact he
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨a,c,hac⟩ := hnc
    exact (hac (by rw [← hval a, ← hval c, ho]; rfl)).elim
  | inr j =>
    let u := l.map (Function.update x p true)
    let v := l.map (Function.update x p false)
    have hdiff : (wiresFrom gs u).getD C.output false ≠ (wiresFrom gs v).getD C.output false := by
      exact hx
    have hs := strictCost n gs C.output j (M,[]) u v hok
      (by simp [u,M]) (by simp [v,M]) (pinAgree p l x) ho hdiff
    refine ⟨⟨acc.2,j⟩, elim_ok n gs (M,[]) (by simp), ?_, ?_⟩
    · change cost acc.2 + 1 ≤ cost gs
      simpa only [show cost [] = 0 from rfl, Nat.zero_add] using hs
    · funext y
      have h := hval y
      rw [ho] at h
      exact h

end Helpers
end PEqualNP.Outside.L_meta_2958_aux

theorem PEqualNP.Outside.L_meta_2958 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates ∧ PEqualNP.MetaComplexity.circuitFun x2 x10 = fun (x11 : Fin x2 → Bool) => x7 (x3.insertNth Bool.false x11) :=
  PEqualNP.Outside.L_meta_2958_aux.Helpers.restrict2958
