import Mathlib
import PEqualNP.Defs.TopForm
import PEqualNP.Defs.ReadK

namespace PlaneStar
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

inductive Tree (n : ℕ) where
  | leaf (i : Fin n)
  | fork (meet : Bool) (left right : Tree n)

namespace Tree
variable {n : ℕ}

def count : Tree n → ℕ
  | .leaf _ => 0
  | .fork _ l r => l.count+r.count+1

def root (t : Tree n) (start : ℕ) : ℕ :=
  match t with
  | .leaf i => i.val
  | .fork _ l r => start + (l.count+r.count)

def op (meet : Bool) : GateOp := if meet then .and else .or

def compile : Tree n → ℕ → List Gate
  | .leaf _, _ => []
  | .fork meet l r, start =>
      l.compile start ++ r.compile (start+l.count) ++
        [⟨op meet,[l.root start,r.root (start+l.count)]⟩]

theorem length_compile (t : Tree n) (s : ℕ) : (t.compile s).length = t.count := by
  induction t generalizing s with
  | leaf => rfl
  | fork m l r hl hr => simp [compile,count,hl,hr,Nat.add_assoc]

theorem root_lt (t : Tree n) (s : ℕ) (hs : n ≤ s) : t.root s < s+t.count := by
  cases t with
  | leaf i => simpa [root,count] using i.isLt.trans_le hs
  | fork m l r => simp [root,count,Nat.add_assoc]

def Valid (s : ℕ) (gs : List Gate) := ∀ j : Fin gs.length,
  let g := gs[j.val]
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < s+j.val

theorem valid_append {s : ℕ} {gs hs : List Gate} (l : Valid s gs)
    (r : Valid (s+gs.length) hs) : Valid s (gs++hs) := by
  intro j
  by_cases before : j.val < gs.length
  · simpa only [List.getElem_append_left before] using l ⟨j.val,before⟩
  · have hi : j.val-gs.length < hs.length := by have := j.isLt; simp only [List.length_append] at this; omega
    have eq : s+(gs.length+(j.val-gs.length))=s+j.val := by omega
    simpa only [List.getElem_append_right (by omega : gs.length ≤ j.val),Nat.add_assoc,eq] using r ⟨_,hi⟩

theorem valid_compile (t : Tree n) (s : ℕ) (hs : n ≤ s) : Valid s (t.compile s) := by
  induction t generalizing s with
  | leaf i => intro j; exact Fin.elim0 j
  | fork m l r hl hr =>
    apply valid_append (valid_append (hl s hs) (by simpa [length_compile] using hr (s+l.count) (by omega)))
    intro j
    have v : j.val=0 := by have hj := j.isLt; simpa only [List.length_singleton,Nat.lt_one_iff] using hj
    simp only [v,List.getElem_cons_zero,List.length_cons,List.length_nil,List.mem_cons,List.not_mem_nil,or_false,true_and,Nat.add_zero]
    constructor
    · cases m <;> simp [op]
    · intro i hi
      have a := root_lt l s hs
      have b := root_lt r (s+l.count) (by omega)
      simp only [List.length_append,length_compile]
      rcases hi with rfl|rfl <;> omega

def circuit (t : Tree n) : Circuit := ⟨t.compile n,t.root n⟩

theorem size (t : Tree n) : t.circuit.size=t.count := length_compile t n

theorem ao (t : Tree n) : PEqualNP.TopForm.IsAO2 n t.circuit := by
  have h := valid_compile t n le_rfl
  constructor
  · intro g hg
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hg
    exact eq ▸ (h ⟨i,hi⟩).1
  constructor
  · intro j hj i hi
    apply (h ⟨j,hj⟩).2.2 i
    change i ∈ (t.compile n)[j].inputs
    change i ∈ ((t.compile n).getD j _).inputs at hi
    have hj' : j < (t.compile n).length := hj
    rw [List.getD_eq_getElem (t.compile n) _ hj'] at hi
    exact hi
  · intro g hg
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hg
    exact eq ▸ (h ⟨i,hi⟩).2.1

end Tree
end PlaneStar

namespace PlaneStar
namespace Tree
variable {n : ℕ}

def value (z : Fin n → Bool) : Tree n → Bool
  | .leaf i => z i
  | .fork m l r => if m then value z l && value z r else value z l || value z r

def join (ts : List (Tree n)) (ne : ts ≠ []) : Tree n :=
  match ts with
  | [] => False.elim (ne rfl)
  | t::rest => rest.foldl (.fork false) t

private theorem fold_count (ts : List (Tree n)) (t : Tree n) :
    (ts.foldl (.fork false) t).count = t.count + (ts.map (fun t => t.count+1)).sum := by
  induction ts generalizing t with
  | nil => simp
  | cons a ts ih => simp [ih,count]; omega

theorem join_count (ts : List (Tree n)) (ne : ts ≠ []) :
    (join ts ne).count + 1 = (ts.map (fun t => t.count+1)).sum := by
  cases ts with
  | nil => contradiction
  | cons t ts => simp [join,fold_count]; omega

private theorem fold_value (ts : List (Tree n)) (t : Tree n) (z : Fin n → Bool) :
    (ts.foldl (.fork false) t).value z = true ↔ t.value z = true ∨ ∃ r ∈ ts, r.value z = true := by
  induction ts generalizing t with
  | nil => simp
  | cons a ts ih => simp [ih,value]; tauto

theorem join_value (ts : List (Tree n)) (ne : ts ≠ []) (z : Fin n → Bool) :
    (join ts ne).value z = true ↔ ∃ t ∈ ts, t.value z = true := by
  cases ts with
  | nil => contradiction
  | cons t ts => simp [join,fold_value]

end Tree

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

noncomputable def points (l : Fin N) := (Finset.univ.filter (fun p => I p l)).toList

noncomputable def star (hn : ∀ l, points I l ≠ []) (l : Fin N) : Tree (N+N) :=
  .fork true (.leaf (Fin.natAdd N l))
    (Tree.join ((points I l).map fun p => .leaf (Fin.castAdd N p)) (by simpa using hn l))

theorem star_count (hn : ∀ l, points I l ≠ []) (l : Fin N) :
    (star I hn l).count = (points I l).length := by
  simpa [star,Tree.count, Function.comp_def] using Tree.join_count
    ((points I l).map fun p => Tree.leaf (Fin.castAdd N p)) (by simpa using hn l)

theorem star_value (hn : ∀ l, points I l ≠ []) (l : Fin N) (z : Fin (N+N) → Bool) :
    (star I hn l).value z = true ↔ z (Fin.natAdd N l) = true ∧
      ∃ p, I p l ∧ z (Fin.castAdd N p) = true := by
  simp [star,Tree.value,Tree.join_value,points]

noncomputable def plane (hn : ∀ l, points I l ≠ []) (pos : 0 < N) : Tree (N+N) :=
  Tree.join (List.ofFn (star I hn)) (by simpa using Nat.ne_of_gt pos)

theorem plane_count {q : ℕ} (hn : ∀ l, points I l ≠ []) (pos : 0 < N)
    (size : ∀ l, (points I l).length = q+1) :
    (plane I hn pos).circuit.size+1 = N*(q+2) := by
  rw [Tree.size,plane,Tree.join_count,List.map_ofFn]
  simp [Function.comp_def,star_count,size,List.ofFn_const]

theorem plane_value (hn : ∀ l, points I l ≠ []) (pos : 0 < N) (z : Fin (N+N) → Bool) :
    (plane I hn pos).value z = true ↔
      ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  simp [plane,Tree.join_value,star_value]
  aesop

end PlaneStar

namespace PlaneStar.Tree
open PEqualNP.CircuitLowerBounds
variable {n : ℕ} {α : Type}

def run (alg : Gate → List α → α) (gs : List Gate) (xs : List α) :=
  gs.foldl (fun ys g => ys ++ [alg g ys]) xs

theorem run_length (alg : Gate → List α → α) (gs : List Gate) (xs : List α) :
    (run alg gs xs).length = xs.length+gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons a gs ih => rw [show run alg (a::gs) xs = run alg gs (xs++[alg a xs]) from rfl,ih]; simp; omega

theorem run_before (alg : Gate → List α → α) (d : α) (gs : List Gate) (xs : List α)
    (i : ℕ) (hi : i < xs.length) : (run alg gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons a gs ih =>
    change (run alg gs (xs++[alg a xs])).getD i d = xs.getD i d
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

def interpret (comb : Bool → α → α → α) (z : Fin n → α) : Tree n → α
  | .leaf i => z i
  | .fork m l r => comb m (interpret comb z l) (interpret comb z r)

theorem run_compile (t : Tree n) (alg : Gate → List α → α) (d : α)
    (comb : Bool → α → α → α) (law : ∀ m a b (xs : List α),
      alg ⟨op m,[a,b]⟩ xs = comb m (xs.getD a d) (xs.getD b d))
    (xs : List α) (z : Fin n → α) (hs : n ≤ xs.length)
    (input : ∀ i : Fin n, xs.getD i.val d = z i) :
    (run alg (t.compile xs.length) xs).getD (t.root xs.length) d = t.interpret comb z := by
  induction t generalizing xs with
  | leaf i => exact input i
  | fork m l r left right =>
    let s := xs.length
    let L := run alg (l.compile s) xs
    let R := run alg (r.compile (s+l.count)) L
    have lenL : L.length = s+l.count := by simp [L,run_length,length_compile,s]
    have lenR : R.length = s+(l.count+r.count) := by simp [R,run_length,lenL,length_compile,Nat.add_assoc]
    have stable (i : Fin n) : L.getD i.val d = z i :=
      (run_before alg d _ xs _ (i.isLt.trans_le hs)).trans (input i)
    have lh : R.getD (l.root s) d = l.interpret comb z := by
      exact (run_before alg d _ L _ (by rw [lenL]; exact root_lt l s hs)).trans (left xs hs input)
    have rh : R.getD (r.root (s+l.count)) d = r.interpret comb z := by
      have h := right L (by rw [lenL]; dsimp [s]; omega) stable
      simpa only [lenL,R] using h
    let g : Gate := ⟨op m,[l.root s,r.root (s+l.count)]⟩
    have eq : run alg ((fork m l r).compile s) xs = R++[alg g R] := by
      simp only [compile,run,List.foldl_append,List.foldl_cons,List.foldl_nil]; rfl
    change (run alg ((fork m l r).compile s) xs).getD (s+(l.count+r.count)) d = _
    rw [eq,← lenR,List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self]
    exact (law m _ _ R).trans (by rw [lh,rh]; rfl)

def boolAlg (g : Gate) (xs : List Bool) := g.op.eval (g.inputs.map fun i => xs.getD i false)

def boolComb (m a b : Bool) := if m then a && b else a || b

theorem eval_circuit (t : Tree n) (z : Fin n → Bool) : t.circuit.eval (List.ofFn z) = t.value z := by
  have h := run_compile t boolAlg false boolComb (fun m a b xs => by cases m <;> simp [boolAlg,boolComb,op,GateOp.eval])
    (List.ofFn z) z (by simp) (fun i => by simp [List.getD_eq_getElem?_getD])
  have val : t.interpret boolComb z = t.value z := by
    clear h
    induction t with
    | leaf => rfl
    | fork m l r hl hr => simp [interpret,value,boolComb,hl,hr]
  exact (by simpa [List.length_ofFn,circuit,Circuit.eval,Circuit.wires,run,boolAlg] using h.trans val)

end PlaneStar.Tree

namespace PlaneStar
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A nonempty projective-plane column has q point-OR gates, one AND, and
-- the N completed column-stars are combined by N-1 more OR gates.
theorem columnCircuit {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (pos : 0 < N) (deg : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q+1) :
    ∃ C : Circuit, PEqualNP.TopForm.IsAO2 (N+N) C ∧ C.size+1=N*(q+2) ∧
      ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  have sizes (l : Fin N) : (points I l).length = q+1 := by simpa [points] using deg l
  have hn (l : Fin N) : points I l ≠ [] := by intro e; have h := sizes l; rw [e] at h; simp at h
  refine ⟨(plane I hn pos).circuit,Tree.ao _,plane_count I hn pos sizes,?_⟩
  intro z
  change (plane I hn pos).circuit.eval (List.ofFn z) = _
  rw [Tree.eval_circuit]
  apply Bool.eq_iff_iff.mpr
  rw [plane_value,decide_eq_true_eq]

end PlaneStar
