import PEqualNP.Outside.L_meta_171
import Mathlib.Data.Finset.Card
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PetersenDistinct3095

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LowMergeProof

/-- NOT uses just its first input, including when the gate lists two operands. -/
def used (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private theorem usedLength (g : Gate) : (used g).length ≤ g.inputs.length := by
  cases g with
  | mk op args => cases op <;> simp [used]

private theorem opAgree (g : Gate) (f h : ℕ → Bool)
    (eqv : ∀ i ∈ used g, f i = h i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map h) := by
  cases g with
  | mk op args =>
    cases op <;> try exact congrArg _ (List.map_congr_left eqv)
    cases args with
    | nil => rfl
    | cons a as =>
      have eq := eqv a (by simp [used])
      simp [GateOp.eval,eq]

def val (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false

private theorem gateAtEq (C : Circuit) (x y : Fin 9 → Bool) (j : Fin C.size)
    (h : ∀ t ∈ used C.gates[j.val], t < 9+j.val → val C x t = val C y t) :
    val C x (9+j.val) = val C y (9+j.val) := by
  have hx := wires_gate C (List.ofFn x) j.val j.isLt
  have hy := wires_gate C (List.ofFn y) j.val j.isLt
  simp only [List.length_ofFn] at hx hy
  unfold val
  rw [hx,hy]
  apply opAgree
  intro t ht
  by_cases hb : t < 9+j.val
  · simpa [rd,hb,val] using h t ht hb
  · simp [rd,hb]

private theorem raw (C : Circuit) (x : Fin 9 → Bool) (a : Fin 9) : val C x a.val = x a := by
  unfold val
  rw [wires_input C _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using a.isLt),List.getElem_ofFn]

/-- If changing an input changes the output, some gate reading a changed raw input must
change, unless the output itself is one of the changed inputs. -/
private theorem agree (C : Circuit) (x y : Fin 9 → Bool) (mask : Finset ℕ)
    (inputs : ∀ a : Fin 9, a.val ∉ mask → x a = y a) (out : C.output ∉ mask)
    (boundary : ∀ j : Fin C.size, (∃ a ∈ mask, a ∈ used C.gates[j.val]) →
      val C x (9+j.val) = val C y (9+j.val)) : circuitFun 9 C x = circuitFun 9 C y := by
  have equal : ∀ w, w ∉ mask → val C x w = val C y w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases small : w<9
      · let a : Fin 9 := ⟨w,small⟩
        exact (raw C x a).trans ((inputs a hw).trans (raw C y a).symm)
      by_cases valid : w<9+C.size
      · let j : Fin C.size := ⟨w-9,by omega⟩
        have he : 9+j.val=w := by dsimp [j]; omega
        by_cases cross : ∃ a ∈ mask, a ∈ used C.gates[j.val]
        · simpa only [he] using boundary j cross
        · rw [← he]
          apply gateAtEq
          intro t ht hlt
          exact ih t (he ▸ hlt) (fun hmem => cross ⟨t,hmem,ht⟩)
      · unfold val
        rw [List.getD_eq_default _ _ (by rw [wires_length,List.length_ofFn]; exact Nat.le_of_not_gt valid),
          List.getD_eq_default _ _ (by rw [wires_length,List.length_ofFn]; exact Nat.le_of_not_gt valid)]
  exact equal _ out

def bits (m : ℕ) (a : Fin 9) := m.testBit a.val

private theorem onlyTwo (L : List ℕ) (len : L.length ≤ 2) (h0 : 0∈L) (h1 : 1∈L) :
    ∀ t ∈ L, t=0 ∨ t=1 := by
  intro t ht
  by_contra! h
  have sub : ({0,1,t} : Finset ℕ) ⊆ L.toFinset := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> simpa using (by assumption : _ ∈ L)
  have card := (Finset.card_le_card sub).trans L.toFinset_card_le
  have n0 : 0 ≠ t := Ne.symm h.1
  have n1 : 1 ≠ t := Ne.symm h.2
  simp [n0,n1] at card
  omega

/-- Two distinct gates after the first OR read its two endpoints. Five restrictions
suffice: the two singletons, their edge, and those singletons with vertex 4 added.
No circuit minimality or specific syntax for the first gate is required. -/
theorem distinctLater (C : Circuit) (fan : FanInTwo C)
    (first : ∀ x : Fin 9 → Bool, val C x 9 = (x 0 || x 1))
    (s0 : circuitFun 9 C (bits 1) = false) (s1 : circuitFun 9 C (bits 2) = false)
    (e01 : circuitFun 9 C (bits 3) = true)
    (e04 : circuitFun 9 C (bits 17) = true) (n14 : circuitFun 9 C (bits 18) = false) :
    ∃ j k : Fin C.size, j ≠ k ∧ 0 < j.val ∧ 0 < k.val ∧
      0 ∈ used C.gates[j.val] ∧ 1 ∈ used C.gates[k.val] := by
  classical
  have noOut : C.output ∉ ({0,1} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (h|h)
    · change val C (bits 1) C.output = false at s0
      rw [h,show val C (bits 1) 0 = true from raw C (bits 1) 0] at s0
      contradiction
    · change val C (bits 2) C.output = false at s1
      rw [h,show val C (bits 2) 1 = true from raw C (bits 2) 1] at s1
      contradiction
  have later (a : ℕ) (ha : a ∈ ({0,1} : Finset ℕ)) (u : ℕ)
      (hd : circuitFun 9 C (bits u) = false)
      (hs : ∀ b : Fin 9, b.val ∉ ({a} : Finset ℕ) → bits u b = bits 3 b)
      (fst : (bits u 0 || bits u 1) = true) :
      ∃ j : Fin C.size, 0 < j.val ∧ a ∈ used C.gates[j.val] ∧
        val C (bits u) (9+j.val) ≠ val C (bits 3) (9+j.val) := by
    by_contra! h
    have equ := agree C (bits u) (bits 3) {a} hs (fun hh => noOut ((Finset.mem_singleton.mp hh).symm ▸ ha)) (by
      intro j hj
      obtain ⟨b,hb,hj⟩ := hj
      have eq := Finset.mem_singleton.mp hb
      subst b
      by_cases pos : 0 < j.val
      · exact h j pos hj
      · have z : j.val = 0 := by omega
        rw [z,Nat.add_zero,first,first,fst]
        decide)
    rw [hd,e01] at equ
    contradiction
  obtain ⟨j,hj,rj,dj⟩ := later 0 (by simp) 2 s1 (by decide) (by decide)
  obtain ⟨k,hk,rk,dk⟩ := later 1 (by simp) 1 s0 (by decide) (by decide)
  by_cases eq : j=k
  · subst k
    by_contra! bad
    have sole (u : Fin C.size) (hu : 0 < u.val)
        (h : 0 ∈ used C.gates[u.val] ∨ 1 ∈ used C.gates[u.val]) : u=j := by
      rcases h with h|h
      · by_contra! ne
        exact bad u j ne hu hj h rk
      · by_contra! ne
        exact bad j u (Ne.symm ne) hj hu rj h
    have just := onlyTwo _ ((usedLength _).trans (fan _ (List.getElem_mem _)).2) rj rk
    have rawEq (u v : ℕ) (eqs : ∀ a : Fin 9, (a.val=0 ∨ a.val=1) → bits u a = bits v a) :
        val C (bits u) (9+j.val) = val C (bits v) (9+j.val) := by
      apply gateAtEq
      intro t ht _
      have hor := just t ht
      let a : Fin 9 := ⟨t,by omega⟩
      exact (raw C _ a).trans ((eqs a hor).trans (raw C _ a).symm)
    have alone : val C (bits 1) (9+j.val) = val C (bits 2) (9+j.val) := by
      cases h : val C (bits 3) (9+j.val) <;> cases h1 : val C (bits 1) (9+j.val) <;>
        cases h2 : val C (bits 2) (9+j.val) <;> simp_all
    have equ := agree C (bits 17) (bits 18) {0,1} (by decide) noOut (by
      intro t ⟨a,ha,hr⟩
      by_cases pos : 0 < t.val
      · have same := sole t pos (by
          simp only [Finset.mem_insert,Finset.mem_singleton] at ha
          rcases ha with rfl|rfl
          · exact Or.inl hr
          · exact Or.inr hr)
        subst t
        exact (rawEq 17 1 (by decide)).trans (alone.trans (rawEq 2 18 (by decide)))
      · have z : t.val=0 := by omega
        rw [z,Nat.add_zero,first,first]
        decide)
    rw [e04,n14] at equ
    contradiction
  · exact ⟨j,k,eq,hj,hk,rj,rk⟩

/-- A direct effective input of a fan-in-two gate forces the gate to a constant or to
one of its original operands when that input is fixed to false. -/
private theorem zeroForm (g : Gate) (i : ℕ)
    (ok : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (len : g.inputs.length ≤ 2) (hi : i ∈ used g) :
    (∃ b : Bool, ∀ f : ℕ → Bool, f i = false → g.op.eval (g.inputs.map f) = b) ∨
    ∃ t : ℕ, ∀ f : ℕ → Bool, f i = false → g.op.eval (g.inputs.map f) = f t := by
  rcases g with ⟨op,ins⟩
  change op = .and ∨ op = .or ∨ op = .not at ok
  rcases ok with rfl | rfl | rfl
  · left
    refine ⟨false,?_⟩
    intro f hf
    have he : ∃ t ∈ ins, f t = false := ⟨i,hi,hf⟩
    simp [GateOp.eval,List.all_eq_false] at he ⊢
    exact he
  · change i ∈ ins at hi
    change ins.length ≤ 2 at len
    rcases ins with _ | ⟨a,tail⟩
    · simp at hi
    rcases tail with _ | ⟨b,rest⟩
    · have eq : i=a := by simpa using hi
      subst a
      exact Or.inl ⟨false,fun f hf => by simp [GateOp.eval,hf]⟩
    rcases rest with _ | ⟨c,rest⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact Or.inr ⟨b,fun f hf => by simp [GateOp.eval,hf]⟩
      · have eq : i=b := by simpa using hi
        subst b
        exact Or.inr ⟨a,fun f hf => by simp [GateOp.eval,hf]⟩
    · simp at len
  · rcases ins with _ | ⟨a,tail⟩
    · simp [used] at hi
    · have eq : i=a := by simpa [used] using hi
      subst a
      exact Or.inl ⟨true,fun f hf => by simp [GateOp.eval,hf]⟩

def ZeroSimple (C : Circuit) (a : Fin 9) (j : ℕ) : Prop :=
  (∃ b : Bool, ∀ x : Fin 9 → Bool, x a=false → val C x (9+j)=b) ∨
  ∃ t < 9+j, ∀ x : Fin 9 → Bool, x a=false → val C x (9+j)=val C x t

theorem readerZero (C : Circuit) (fan : FanInTwo C) (a : Fin 9) (j : Fin C.size)
    (hread : a.val ∈ used C.gates[j.val]) : ZeroSimple C a j.val := by
  have hf := fan _ (List.getElem_mem (l := C.gates) (n := j.val) j.isLt)
  have hg (x : Fin 9 → Bool) : val C x (9+j.val) =
      C.gates[j.val].op.eval (C.gates[j.val].inputs.map (fun w => rd C (List.ofFn x) (9+j.val) w)) := by
    have hv := wires_gate C (List.ofFn x) j.val j.isLt
    simp only [List.length_ofFn] at hv
    exact hv
  have hx (x : Fin 9 → Bool) (ha : x a=false) : rd C (List.ofFn x) (9+j.val) a.val=false := by
    have h := a.isLt
    rw [rd,ite_eq_left (show a.val < 9+j.val by omega)]
    exact (raw C x a).trans ha
  rcases zeroForm _ a.val hf.1 hf.2 hread with ⟨b,hh⟩ | ⟨t,hh⟩
  · exact Or.inl ⟨b,fun x ha => (hg x).trans (hh _ (hx x ha))⟩
  · by_cases good : t < 9+j.val
    · exact Or.inr ⟨t,good,fun x ha => (hg x).trans ((hh _ (hx x ha)).trans (ite_eq_left good))⟩
    · exact Or.inl ⟨false,fun x ha => (hg x).trans ((hh _ (hx x ha)).trans (ite_eq_right good))⟩

/-- At the endpoints of the named first OR, gate zero itself is also removable when
the corresponding input is fixed to false. -/
theorem endpointPair (C : Circuit) (fan : FanInTwo C)
    (first : ∀ x : Fin 9 → Bool, val C x 9 = (x 0 || x 1))
    (s0 : circuitFun 9 C (bits 1) = false) (s1 : circuitFun 9 C (bits 2) = false)
    (e01 : circuitFun 9 C (bits 3) = true)
    (e04 : circuitFun 9 C (bits 17) = true) (n14 : circuitFun 9 C (bits 18) = false) :
    ∃ j k : Fin C.size, j ≠ k ∧ 0 < j.val ∧ 0 < k.val ∧
      ZeroSimple C 0 0 ∧ ZeroSimple C 1 0 ∧ ZeroSimple C 0 j.val ∧ ZeroSimple C 1 k.val := by
  obtain ⟨j,k,ne,hj,hk,rj,rk⟩ := distinctLater C fan first s0 s1 e01 e04 n14
  refine ⟨j,k,ne,hj,hk,?_,?_,readerZero C fan 0 j rj,readerZero C fan 1 k rk⟩
  · refine Or.inr ⟨1,by decide,?_⟩
    intro x hx
    simpa [hx,show val C x 1=x 1 from raw C x 1] using first x
  · refine Or.inr ⟨0,by decide,?_⟩
    intro x hx
    simpa [hx,show val C x 0=x 0 from raw C x 0] using first x

def ZeroBudget (C : Circuit) : Prop :=
  ∀ (a : Fin 9) (S : Finset ℕ), (∀ t ∈ S, t < C.size ∧ ZeroSimple C a t) →
    (a ∈ [0,1,2,3,5,8] → S.card ≤ 3) ∧ (a ∈ [4,6,7] → S.card ≤ 2)

private theorem remainingOne (C : Circuit) (bu : ZeroBudget C) (a : Fin 9)
    (ha : a ∈ [0,1,2,3,5,8]) (r : Fin C.size) (hr : 0 < r.val)
    (base : ZeroSimple C a 0) (reader : ZeroSimple C a r.val) (rest : Finset ℕ)
    (good : ∀ t ∈ rest, t < C.size ∧ ZeroSimple C a t) (h0 : 0 ∉ rest) (hr' : r.val ∉ rest) :
    rest.card ≤ 1 := by
  let E := insert 0 (insert r.val rest)
  have ok : ∀ t ∈ E, t < C.size ∧ ZeroSimple C a t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | h
    · exact ⟨by have := r.isLt; omega,base⟩
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact ⟨r.isLt,reader⟩
      · exact good _ h
  have card := (bu a E ok).1 ha
  have hne : (0:ℕ) ≠ r.val := by omega
  have nz : 0 ∉ insert r.val rest := by simp [hne,h0]
  simp only [E,Finset.card_insert_of_notMem nz,Finset.card_insert_of_notMem hr'] at card
  omega

/-- The exact zero-cofactor budgets from the desk statement leave at most one further
simplified gate at each endpoint after accounting for gate zero and its distinct reader. -/
theorem endpointBudget (C : Circuit) (fan : FanInTwo C) (bu : ZeroBudget C)
    (first : ∀ x : Fin 9 → Bool, val C x 9 = (x 0 || x 1))
    (s0 : circuitFun 9 C (bits 1) = false) (s1 : circuitFun 9 C (bits 2) = false)
    (e01 : circuitFun 9 C (bits 3) = true)
    (e04 : circuitFun 9 C (bits 17) = true) (n14 : circuitFun 9 C (bits 18) = false) :
    ∃ j k : Fin C.size, j ≠ k ∧ 0 < j.val ∧ 0 < k.val ∧
      (∀ S : Finset ℕ, (∀ t ∈ S, t < C.size ∧ ZeroSimple C 0 t) →
        0 ∉ S → j.val ∉ S → S.card ≤ 1) ∧
      (∀ S : Finset ℕ, (∀ t ∈ S, t < C.size ∧ ZeroSimple C 1 t) →
        0 ∉ S → k.val ∉ S → S.card ≤ 1) := by
  obtain ⟨j,k,ne,hj,hk,z0,z1,sj,sk⟩ := endpointPair C fan first s0 s1 e01 e04 n14
  exact ⟨j,k,ne,hj,hk,remainingOne C bu 0 (by decide) j hj z0 sj,
    remainingOne C bu 1 (by decide) k hk z1 sk⟩

private theorem andOrOnDistinct (C : Circuit) (fan : FanInTwo C) (g : Fin C.size)
    {p q : ℕ} (ne : p ≠ q) (hp : p ∈ used C.gates[g.val]) (hq : q ∈ used C.gates[g.val])
    (earlierP : p < 9+g.val) (earlierQ : q < 9+g.val) :
    (∀ x : Fin 9 → Bool, val C x (9+g.val) = (val C x p && val C x q)) ∨
    (∀ x : Fin 9 → Bool, val C x (9+g.val) = (val C x p || val C x q)) := by
  let G := C.gates[g.val]
  have hf := fan G (List.getElem_mem _)
  change p ∈ used G at hp
  change q ∈ used G at hq
  have listPair (L : List ℕ) (len : L.length ≤ 2) (ph : p∈L) (qh : q∈L) :
      L=[p,q] ∨ L=[q,p] := by
    rcases L with _ | ⟨a,t⟩
    · simp at ph
    rcases t with _ | ⟨b,t⟩
    · simp_all
    rcases t with _ | ⟨d,t⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ph qh
      rcases ph with rfl | rfl <;> rcases qh with rfl | rfl <;> simp_all
    · simp at len
  have eqw (x : Fin 9 → Bool) : val C x (9+g.val) =
      G.op.eval (G.inputs.map fun i => rd C (List.ofFn x) (9+g.val) i) := by
    have hh := wires_gate C (List.ofFn x) g.val g.isLt
    simp only [List.length_ofFn] at hh
    exact hh
  have valid : G.op = .and ∨ G.op = .or ∨ G.op = .not := hf.1
  have use (hop : G.op = .and ∨ G.op = .or) : used G = G.inputs := by
    rcases hop with ho|ho <;> simp [used,ho]
  rcases valid with ha | ho | hn
  · have u := use (Or.inl ha)
    rw [u] at hp hq
    left
    intro x
    rw [eqw,ha]
    rcases listPair _ hf.2 hp hq with eq|eq <;>
      simp [eq,rd,earlierP,earlierQ,val,GateOp.eval,Bool.and_comm]
  · have u := use (Or.inr ho)
    rw [u] at hp hq
    right
    intro x
    rw [eqw,ho]
    rcases listPair _ hf.2 hp hq with eq|eq <;>
      simp [eq,rd,earlierP,earlierQ,val,GateOp.eval,Bool.or_comm]
  · have le1 : (used G).length ≤ 1 := by simp [used,hn]
    rcases listPair (used G) (by omega) hp hq with eq|eq <;> simp [eq] at le1

private theorem inheritedZero (C : Circuit) (fan : FanInTwo C) (a : Fin 9)
    (w : ℕ) (j : Fin C.size) (read : w ∈ used C.gates[j.val]) (early : w < 9+j.val)
    (zero : ∀ x : Fin 9 → Bool, x a=false → val C x w=false) : ZeroSimple C a j.val := by
  have hgate (x : Fin 9 → Bool) := wires_gate C (List.ofFn x) j.val j.isLt
  have eq (x : Fin 9 → Bool) : val C x (9+j.val) =
      C.gates[j.val].op.eval (C.gates[j.val].inputs.map fun i => rd C (List.ofFn x) (9+j.val) i) := by
    have hh := hgate x
    simp only [List.length_ofFn] at hh
    exact hh
  have hf := fan _ (List.getElem_mem (l := C.gates) (n := j.val) j.isLt)
  have wz (x : Fin 9 → Bool) (hx : x a=false) : rd C (List.ofFn x) (9+j.val) w=false := by
    rw [rd,ite_eq_left early]
    exact zero x hx
  rcases zeroForm _ w hf.1 hf.2 read with ⟨b,hh⟩|⟨t,hh⟩
  · exact Or.inl ⟨b,fun x ha => (eq x).trans (hh _ (wz x ha))⟩
  · by_cases h : t < 9+j.val
    · exact Or.inr ⟨t,h,fun x ha => (eq x).trans ((hh _ (wz x ha)).trans (ite_eq_left h))⟩
    · exact Or.inl ⟨false,fun x ha => (eq x).trans ((hh _ (wz x ha)).trans (ite_eq_right h))⟩

def Shorter (C : Circuit) : Prop :=
  ∃ D : Circuit, FanInTwo D ∧ D.size+1=C.size ∧ circuitFun 9 D = circuitFun 9 C

private theorem dropGate (C : Circuit) (fan : FanInTwo C) (j : Fin C.size)
    (r : ℕ) (earlier : r < 9+j.val)
    (child : ∀ h : Fin C.size, j.val<h.val → 9+j.val ∈ used C.gates[h.val] →
      ∀ x : Fin 9 → Bool, val C x (9+j.val)=val C x r)
    (out : C.output=9+j.val → ∀ x : Fin 9 → Bool, val C x (9+j.val)=val C x r) :
    Shorter C := by
  let D : Circuit := ⟨PEqualNP.Outside.L171.del C.gates j.val (9+j.val) r,
    PEqualNP.Outside.L171.ren (9+j.val) r C.output⟩
  refine ⟨D,PEqualNP.Outside.L171.fanInTwo_del _ C.output _ _ _ _ fan,?_,?_⟩
  · change (PEqualNP.Outside.L171.del _ _ _ _).length +1 = C.gates.length
    rw [PEqualNP.Outside.L171.del_length _ _ _ _ j.isLt]
    have := j.isLt
    change j.val < C.gates.length at this
    omega
  · funext x
    have hh := PEqualNP.Outside.L171.del_eval C.gates C.output (List.ofFn x) j.val r j.isLt
    simp only [List.length_ofFn] at hh
    apply hh (Or.inl earlier)
    · intro g hg read
      obtain ⟨t,ht,he⟩ := List.mem_iff_getElem.mp hg
      simp only [List.length_drop] at ht
      let k : Fin C.size := ⟨j.val+1+t,by change j.val+1+t < C.gates.length; omega⟩
      have eqg : C.gates[k.val] = g := by simpa only [List.getElem_drop,k] using he
      have deps (v : Gate) : used v = PEqualNP.Outside.L171.deps v := by
        rcases v with ⟨op,L⟩
        cases op <;> cases L <;> rfl
      exact child k (by dsimp [k]; omega) (by rw [eqg,deps]; exact read) x
    · intro ho
      exact out ho x

/-- If an effective reader after the first OR reads both endpoints, the zero budgets
force an actual one-gate saving on the same graph function. -/
theorem commonReaderSaves (C : Circuit) (fan : FanInTwo C) (bu : ZeroBudget C)
    (first : ∀ x : Fin 9 → Bool, val C x 9 = (x 0 || x 1))
    (s0 : circuitFun 9 C (bits 1) = false) (s1 : circuitFun 9 C (bits 2) = false)
    (e01 : circuitFun 9 C (bits 3) = true)
    (e04 : circuitFun 9 C (bits 17) = true) (n14 : circuitFun 9 C (bits 18) = false)
    (g : Fin C.size) (gpos : 0 < g.val)
    (reads0 : 0 ∈ used C.gates[g.val]) (reads1 : 1 ∈ used C.gates[g.val]) : Shorter C := by
  have saveAlias (t : Fin C.size) (r : ℕ) (ht : r < 9+t.val)
      (equ : ∀ x : Fin 9 → Bool, val C x (9+t.val)=val C x r) : Shorter C :=
    dropGate C fan t r ht (fun _ _ _ => equ) (fun _ => equ)
  rcases andOrOnDistinct C fan g (by decide : (0:ℕ)≠1) reads0 reads1 (by omega) (by omega) with hand | hor
  · by_contra ns
    have notOut : C.output ≠ 9+g.val := by
      intro eq
      change val C (bits 17) C.output=true at e04
      rw [eq,hand,show val C (bits 17) 0=true from raw C _ 0,
        show val C (bits 17) 1=false from raw C _ 1] at e04
      contradiction
    have reader : ∃ h : Fin C.size, g.val<h.val ∧ 9+g.val ∈ used C.gates[h.val] := by
      by_contra! dead
      apply ns
      exact dropGate C fan g 0 (by omega)
        (fun h hlt hr => False.elim (dead h hlt hr)) (fun ho => False.elim (notOut ho))
    obtain ⟨h,hgt,rh⟩ := reader
    obtain ⟨j,k,nej,hj,hk,rj,rk⟩ := distinctLater C fan first s0 s1 e01 e04 n14
    have solveOne (a : Fin 9) (endpoint : a=0 ∨ a=1) (t : Fin C.size)
        (tpos : 0<t.val) (tg : t≠g) (rt : a.val ∈ used C.gates[t.val]) :
        False := by
      have zeroG (x : Fin 9 → Bool) (hx : x a=false) : val C x (9+g.val)=false := by
        rw [hand,show val C x 0=x 0 from raw C x 0,show val C x 1=x 1 from raw C x 1]
        rcases endpoint with rfl|rfl <;> simp [hx]
      have z0 : ZeroSimple C a 0 := by
        rcases endpoint with rfl|rfl
        · exact Or.inr ⟨1,by decide,fun x hx => by simpa [hx,show val C x 1=x 1 from raw C x 1] using first x⟩
        · exact Or.inr ⟨0,by decide,fun x hx => by simpa [hx,show val C x 0=x 0 from raw C x 0] using first x⟩
      have ah : a ∈ [0,1,2,3,5,8] := by rcases endpoint with rfl|rfl <;> decide
      have th : t=h := by
        by_contra ne
        have gg : g.val ≠ h.val := by omega
        have ntg : t.val ≠ g.val := fun e => tg (Fin.ext e)
        have nth : t.val ≠ h.val := fun e => ne (Fin.ext e)
        have all : ∀ i ∈ ({g.val,h.val} : Finset ℕ), i<C.size ∧ ZeroSimple C a i := by
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl|hi
          · exact ⟨g.isLt,Or.inl ⟨false,zeroG⟩⟩
          · obtain rfl : i = h.val := Finset.mem_singleton.mp hi
            exact ⟨h.isLt,inheritedZero C fan a _ h rh (by omega) zeroG⟩
        have card := remainingOne C bu a ah t tpos z0 (readerZero C fan a t rt)
          {g.val,h.val} all (by simp; omega) (by simp [ntg,nth])
        simp [gg] at card
      subst t
      have order : 9+g.val < 9+h.val := by omega
      have absorption (x : Fin 9 → Bool) :
          (val C x a.val && val C x (9+g.val)) = val C x (9+g.val) ∧
          (val C x a.val || val C x (9+g.val)) = val C x a.val := by
        rw [hand]
        have leftAbs (z w : Bool) : (z && (z && w)) = (z && w) ∧ (z || (z && w)) = z := by
          cases z <;> cases w <;> decide
        have rightAbs (z w : Bool) : (w && (z && w)) = (z && w) ∧ (w || (z && w)) = w := by
          cases z <;> cases w <;> decide
        rcases endpoint with rfl|rfl
        · exact leftAbs _ _
        · exact rightAbs _ _
      have av := a.isLt
      rcases andOrOnDistinct C fan h (show a.val ≠ 9+g.val by omega) rt rh (by omega) order with hAnd|hOr
      · exact ns (saveAlias h _ order (fun x => (hAnd x).trans (absorption x).1))
      · exact ns (saveAlias h _ (by omega) (fun x => (hOr x).trans (absorption x).2))
    by_cases jg : j=g
    · subst j
      exact solveOne 1 (Or.inr rfl) k hk (Ne.symm nej) rk
    · exact solveOne 0 (Or.inl rfl) j hj jg rj
  · apply saveAlias g 9 (by omega)
    intro x
    rw [hor,first,show val C x 0=x 0 from raw C x 0,show val C x 1=x 1 from raw C x 1]

/-- The two endpoint reader sets after the first OR are disjoint in a circuit of
at most 15 gates whenever its function has the established 15-gate lower bound. -/
theorem disjointAt15 (C : Circuit) (fan : FanInTwo C) (bu : ZeroBudget C)
    (first : ∀ x : Fin 9 → Bool, val C x 9 = (x 0 || x 1))
    (s0 : circuitFun 9 C (bits 1) = false) (s1 : circuitFun 9 C (bits 2) = false)
    (e01 : circuitFun 9 C (bits 3) = true)
    (e04 : circuitFun 9 C (bits 17) = true) (n14 : circuitFun 9 C (bits 18) = false)
    (small : C.size ≤ 15) (lower : ¬ HasCircuitSize 9 (circuitFun 9 C) 14)
    (g : Fin C.size) (gpos : 0 < g.val) (reads0 : 0 ∈ used C.gates[g.val]) :
    1 ∉ used C.gates[g.val] := by
  intro reads1
  obtain ⟨D,hfan,hs,eq⟩ := commonReaderSaves C fan bu first s0 s1 e01 e04 n14 g gpos reads0 reads1
  exact lower ⟨D,hfan,by omega,fun x => congrFun eq x⟩

/-- When the direct readers of an input already exhaust its zero-cofactor budget,
every gate vanishing on that cofactor can be removed or has a removable child,
provided the gate is not the output. -/
theorem saturatedZeroSaves (C : Circuit) (fan : FanInTwo C) (bud : ZeroBudget C)
    (a : Fin 9) (R : Finset ℕ)
    (readers : ∀ i ∈ R, ∃ h : Fin C.size, h.val = i ∧ a.val ∈ used C.gates[h.val])
    (full : (a ∈ [0,1,2,3,5,8] ∧ R.card = 3) ∨ (a ∈ [4,6,7] ∧ R.card = 2))
    (g : Fin C.size) (notOut : C.output ≠ 9+g.val)
    (zero : ∀ x : Fin 9 → Bool, x a=false → val C x (9+g.val)=false) : Shorter C := by
  classical
  by_cases live : ∃ h : Fin C.size, g.val<h.val ∧ 9+g.val ∈ used C.gates[h.val]
  · obtain ⟨h,gh,uses⟩ := live
    have simple := inheritedZero C fan a _ h uses (by omega) zero
    have mem : h.val ∈ R := by
      by_contra outside
      have ok : ∀ i ∈ insert h.val R, i<C.size ∧ ZeroSimple C a i := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl|old
        · exact ⟨h.isLt,simple⟩
        · obtain ⟨s,rfl,reads⟩ := readers i old
          exact ⟨s.isLt,readerZero C fan a s reads⟩
      have bound := bud a _ ok
      rw [Finset.card_insert_of_notMem outside] at bound
      rcases full with ⟨group,sz⟩|⟨group,sz⟩
      · have := bound.1 group
        omega
      · have := bound.2 group
        omega
    obtain ⟨v,veq,rawUse⟩ := readers h.val mem
    have vh : v = h := Fin.ext veq
    subst v
    have av := a.isLt
    have absorption (x : Fin 9 → Bool) : (val C x a.val && val C x (9+g.val))=val C x (9+g.val) ∧
        (val C x a.val || val C x (9+g.val))=val C x a.val := by
      rw [raw]
      cases hxa : x a with
      | false => simp [zero x hxa]
      | true => simp
    rcases andOrOnDistinct C fan h (show a.val≠9+g.val by omega) rawUse uses
      (by omega) (by omega) with hand|hor
    · have sameValue (x : Fin 9 → Bool) := (hand x).trans (absorption x).1
      exact dropGate C fan h (9+g.val) (by omega) (fun _ _ _ => sameValue) (fun _ => sameValue)
    · have sameValue (x : Fin 9 → Bool) := (hor x).trans (absorption x).2
      exact dropGate C fan h a.val (by omega) (fun _ _ _ => sameValue) (fun _ => sameValue)
  · exact dropGate C fan g 0 (by omega)
      (fun h hh hu => False.elim (live ⟨h,hh,hu⟩)) (fun ho => False.elim (notOut ho))

/-- With all raw-reader slots used, every gate of a 15-gate candidate must still
be true on some input with the chosen variable zero.  The disjoint edges 01
and 23 ensure this also holds for the output gate. -/
theorem saturatedGateWitness (C : Circuit) (fan : FanInTwo C) (bud : ZeroBudget C)
    (small : C.size ≤ 15) (lower : ¬ HasCircuitSize 9 (circuitFun 9 C) 14)
    (e01 : circuitFun 9 C (bits 3) = true) (e23 : circuitFun 9 C (bits 12) = true)
    (a : Fin 9) (R : Finset ℕ)
    (readers : ∀ i ∈ R, ∃ h : Fin C.size, h.val = i ∧ a.val ∈ used C.gates[h.val])
    (full : (a ∈ [0,1,2,3,5,8] ∧ R.card = 3) ∨ (a ∈ [4,6,7] ∧ R.card = 2))
    (g : Fin C.size) : ∃ x : Fin 9 → Bool, x a=false ∧ val C x (9+g.val)=true := by
  by_contra! missing
  have vanished (x : Fin 9 → Bool) (atZero : x a=false) : val C x (9+g.val)=false := by
    simpa using missing x atZero
  have hm : bits 3 a=false ∨ bits 12 a=false := by fin_cases a <;> decide
  have notOut : C.output ≠ 9+g.val := by
    intro eq
    change val C (bits 3) C.output=true at e01
    change val C (bits 12) C.output=true at e23
    rcases hm with hm|hm
    · rw [eq,vanished _ hm] at e01
      contradiction
    · rw [eq,vanished _ hm] at e23
      contradiction
  obtain ⟨D,hfan,hs,eq⟩ := saturatedZeroSaves C fan bud a R readers full g notOut vanished
  exact lower ⟨D,hfan,by omega,fun x => congrFun eq x⟩

end PetersenDistinct3095
