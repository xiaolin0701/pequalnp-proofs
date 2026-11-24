import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Tactic.Choose
import PlaneFormulaTree

namespace PlaneUnfold


inductive Op (α : Type) where
  | empty
  | copy (a : α)
  | join (a b : α)
  | meet (a b : α)

abbrev Steps (n : ℕ) := (i : ℕ) → Op (Fin (n+i))

def Op.onSets {α Z : Type} (args : α → Set Z) : Op α → Set Z
  | .empty => ∅
  | .copy a => args a
  | .join a b => args a ∪ args b
  | .meet a b => args a ∩ args b

def realizes {n : ℕ} {Z : Type} (W : ℕ → Set Z) (m : ℕ) (ops : Steps n) : Prop :=
  ∀ i < m, W (n+i) = (ops i).onSets (fun a => W a.val)

/-- Choose an operation for every live row of the original set-circuit presentation. -/
theorem chooseSteps {n m : ℕ} {Z : Type} (W : ℕ → Set Z)
    (gates : ∀ i < m, ∃ a < n+i, ∃ b < n+i,
      W (n+i) = W a ∪ W b ∨ W (n+i) = W a ∨ W (n+i) = ∅ ∨ W (n+i) = W a ∩ W b) :
    ∃ ops : Steps n, realizes W m ops := by
  classical
  have row (i : ℕ) : ∃ op : Op (Fin (n+i)),
      i < m → W (n+i) = op.onSets (fun a => W a.val) := by
    by_cases hi : i < m
    · obtain ⟨a,ha,b,hb,h | h | h | h⟩ := gates i hi
      · exact ⟨.join ⟨a,ha⟩ ⟨b,hb⟩,fun _ => h⟩
      · exact ⟨.copy ⟨a,ha⟩,fun _ => h⟩
      · exact ⟨.empty,fun _ => h⟩
      · exact ⟨.meet ⟨a,ha⟩ ⟨b,hb⟩,fun _ => h⟩
    · exact ⟨.empty,fun h => False.elim (hi h)⟩
  choose ops ho using row
  exact ⟨ops,ho⟩

structure Expansion (V : Type) where
  tree : PlaneFormula.Tree V
  labels : Multiset ℕ

private def copied {V : Type} (g : ℕ) (v : Expansion V) : Expansion V :=
  ⟨v.tree, g ::ₘ v.labels⟩

private def branch {V : Type} (g : ℕ) (op : PlaneFormula.Tree V → PlaneFormula.Tree V → PlaneFormula.Tree V)
    (v w : Expansion V) : Expansion V := ⟨op v.tree w.tree, g ::ₘ (v.labels + w.labels)⟩

/-- Every visited gate emits its label once. A copy and a binary gate with identical
parents both follow their single effective parent exactly once. -/
def Op.expand {α V : Type} [DecidableEq α] (g : ℕ) (args : α → Expansion V) :
    Op α → Expansion V
  | .empty => ⟨.bot,{g}⟩
  | .copy a => copied g (args a)
  | .join a b => if a=b then copied g (args a) else branch g PlaneFormula.Tree.join (args a) (args b)
  | .meet a b => if a=b then copied g (args a) else branch g PlaneFormula.Tree.meet (args a) (args b)

/-- Unfold the circuit backward. An input has no gate label. Fuel `n+m` suffices for
every wire of a topologically ordered circuit with `n` inputs and `m` gates. -/
def trace {n : ℕ} (ops : Steps n) : ℕ → ℕ → Expansion (Fin n)
  | 0, _ => ⟨.bot,0⟩
  | fuel+1,w =>
    if h : w < n then ⟨.input ⟨w,h⟩,0⟩ else
    (ops (w-n)).expand (w-n) (fun a => trace ops fuel a.val)

/-- The number of backward paths from the output to gate `i`, counted by its occurrences
in the expansion. A direct use of a gate reached by two different paths counts twice. -/
def pathCount {n : ℕ} (ops : Steps n) (fuel o i : ℕ) : ℕ :=
  (trace ops fuel o).labels.count i

private def Good {V Z : Type} (bits : Z → V → Bool) (m : ℕ)
    (A : Set Z) (r : Expansion V) : Prop :=
  (∀ z, r.tree.eval (bits z) = true ↔ z ∈ A) ∧
  (∀ i ∈ r.labels, i < m) ∧ r.tree.leaves ≤ r.labels.card+1

private theorem copiedGood {V Z : Type} (bits : Z → V → Bool) {g m : ℕ} (hg : g < m)
    {A : Set Z} {r : Expansion V} (h : Good bits m A r) : Good bits m A (copied g r) := by
  obtain ⟨he,hl,hc⟩ := h
  refine ⟨he,?_,?_⟩
  · intro i hi
    rcases Multiset.mem_cons.mp hi with rfl | hi
    · exact hg
    · exact hl i hi
  · simp only [copied,Multiset.card_cons]
    omega

private theorem buildGood {V Z α : Type} [DecidableEq α] (bits : Z → V → Bool)
    {g m : ℕ} (hg : g < m) (sets : α → Set Z) (args : α → Expansion V)
    (h : ∀ a, Good bits m (sets a) (args a)) (op : Op α) :
    Good bits m (op.onSets sets) (op.expand g args) := by
  cases op with
  | empty =>
    refine ⟨by simp [Op.expand,Op.onSets,PlaneFormula.Tree.eval],?_,by simp [Op.expand,PlaneFormula.Tree.leaves]⟩
    intro i hi
    have eq : i=g := by simpa [Op.expand] using hi
    exact eq ▸ hg
  | copy a => exact copiedGood bits hg (h a)
  | join a b =>
    by_cases ab : a=b
    · subst b
      simpa [Op.expand,Op.onSets] using copiedGood bits hg (h a)
    · obtain ⟨he,hl,hc⟩ := h a
      obtain ⟨he',hl',hc'⟩ := h b
      simp only [Op.expand,Op.onSets,ab,ite_false]
      refine ⟨?_,?_,?_⟩
      · intro z
        simp [branch,PlaneFormula.Tree.eval,he,he']
      · intro i hi
        rcases Multiset.mem_cons.mp hi with rfl | hi
        · exact hg
        · rcases Multiset.mem_add.mp hi with hi | hi
          · exact hl i hi
          · exact hl' i hi
      · simp only [branch,PlaneFormula.Tree.leaves,Multiset.card_cons,Multiset.card_add]
        omega
  | meet a b =>
    by_cases ab : a=b
    · subst b
      simpa [Op.expand,Op.onSets] using copiedGood bits hg (h a)
    · obtain ⟨he,hl,hc⟩ := h a
      obtain ⟨he',hl',hc'⟩ := h b
      simp only [Op.expand,Op.onSets,ab,ite_false]
      refine ⟨?_,?_,?_⟩
      · intro z
        simp [branch,PlaneFormula.Tree.eval,he,he']
      · intro i hi
        rcases Multiset.mem_cons.mp hi with rfl | hi
        · exact hg
        · rcases Multiset.mem_add.mp hi with hi | hi
          · exact hl i hi
          · exact hl' i hi
      · simp only [branch,PlaneFormula.Tree.leaves,Multiset.card_cons,Multiset.card_add]
        omega

private theorem traceGood {n m : ℕ} {Z : Type} {W : ℕ → Set Z} (bits : Z → Fin n → Bool)
    (inputs : ∀ a : Fin n, ∀ z, bits z a = true ↔ z ∈ W a.val)
    (ops : Steps n) (hop : realizes W m ops) :
    ∀ fuel w, w < fuel → w < n+m → Good bits m (W w) (trace ops fuel w) := by
  intro fuel
  induction fuel with
  | zero => intro w hw; omega
  | succ fuel ih =>
    intro w hw hm
    rw [trace]
    split
    next h => exact ⟨fun z => inputs ⟨w,h⟩ z,by simp,by simp [PlaneFormula.Tree.leaves]⟩
    next h =>
      have g : w-n < m := by omega
      have row := hop (w-n) g
      have rowVal : W w = (ops (w-n)).onSets (fun a => W a.val) :=
        (congrArg W (show w = n+(w-n) by omega)).trans row
      rw [rowVal]
      apply buildGood bits g
      intro a
      apply ih a.val <;> have := a.isLt <;> omega

/-- Without a cap, the sum of output path counts controls the entire formula size. -/
theorem toFormulaTotal {n m o : ℕ} {Z : Type} (W : ℕ → Set Z) (bits : Z → Fin n → Bool)
    (inputs : ∀ a : Fin n, ∀ z, bits z a = true ↔ z ∈ W a.val)
    (ops : Steps n) (hop : realizes W m ops) (hout : o < n+m) :
    ∃ T : PlaneFormula.Tree (Fin n), T.leaves ≤ (∑ i ∈ Finset.range m, pathCount ops (n+m) o i)+1 ∧
      ∀ z, T.eval (bits z) = true ↔ z ∈ W o := by
  let r := trace ops (n+m) o
  obtain ⟨he,hl,hc⟩ := traceGood bits inputs ops hop (n+m) o hout hout
  have total : (∑ i ∈ Finset.range m, r.labels.count i) = r.labels.card :=
    Multiset.sum_count_eq_card (fun i hi => Finset.mem_range.mpr (hl i hi))
  refine ⟨r.tree,?_,he⟩
  change r.tree.leaves ≤ (∑ i ∈ Finset.range m, r.labels.count i)+1
  rwa [total]

/-- A per-gate path bound gives a formula with at most `cap*m+1` leaves. The tree computes
the output set everywhere, so it preserves both the positive and the negative inputs. -/
theorem toFormula {n m o cap : ℕ} {Z : Type} (W : ℕ → Set Z) (bits : Z → Fin n → Bool)
    (inputs : ∀ a : Fin n, ∀ z, bits z a = true ↔ z ∈ W a.val)
    (ops : Steps n) (hop : realizes W m ops) (hout : o < n+m)
    (paths : ∀ i < m, pathCount ops (n+m) o i ≤ cap) :
    ∃ T : PlaneFormula.Tree (Fin n), T.leaves ≤ cap*m+1 ∧ ∀ z, T.eval (bits z) = true ↔ z ∈ W o := by
  let r := trace ops (n+m) o
  obtain ⟨he,hl,hc⟩ := traceGood bits inputs ops hop (n+m) o hout hout
  have sum : (∑ i ∈ Finset.range m, r.labels.count i) = r.labels.card :=
    Multiset.sum_count_eq_card (fun i hi => Finset.mem_range.mpr (hl i hi))
  have bound := Finset.sum_le_sum (s := Finset.range m) (fun i hi =>
    (show r.labels.count i ≤ cap from paths i (Finset.mem_range.mp hi)))
  simp only [sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at bound
  refine ⟨r.tree,?_,he⟩
  change r.tree.leaves ≤ r.labels.card+1 at hc
  change r.labels.card ≤ m*cap at bound
  exact hc.trans (Nat.add_le_add_right (by simpa only [Nat.mul_comm m cap] using bound) 1)

end PlaneUnfold
