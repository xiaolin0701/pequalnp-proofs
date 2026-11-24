import PEqualNP.Defs.TopForm
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace Meta2796

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.TopForm

def Sensitive {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y

theorem essential_bound {n : ℕ} {C : Circuit} (hc : IsAO2 n C)
    (h : ∀ i, Sensitive (circuitFun n C) i) : n ≤ C.size + 1 := by
  classical
  refine dep_lower n (circuitFun n C) ?_ C.size ?_
  · intro i
    obtain ⟨x,y,ha,hxy⟩ := h i
    have hne : x i ≠ y i := by
      intro hi
      apply hxy
      congr 1
      funext j
      by_cases hj : j = i
      · simpa [hj] using hi
      · exact ha j hj
    have hflip : (!x i) = y i := by
      revert hne
      cases x i <;> cases y i <;> decide
    refine ⟨x, ?_⟩
    convert hxy.symm using 2
    funext j
    by_cases hj : j = i
    · simpa [hj] using hflip
    · simpa [Function.update_of_ne hj] using ha j hj
  · refine ⟨C, ?_, le_rfl, fun _ => rfl⟩
    intro g hg
    obtain hp | hp := hc.1 g hg
    · exact ⟨by simp [hp], (hc.2.2 g hg).le⟩
    · exact ⟨by simp [hp], (hc.2.2 g hg).le⟩

theorem tail_ao {n : ℕ} {g : Gate} {gs : List Gate} {o : ℕ}
    (h : IsAO2 n ⟨g :: gs,o⟩) : IsAO2 (n+1) ⟨gs,o⟩ := by
  refine ⟨fun a ha => h.1 a (List.mem_cons_of_mem _ ha), ?_,
    fun a ha => h.2.2 a (List.mem_cons_of_mem _ ha)⟩
  intro j hj i hi
  have hh := h.2.1 (j+1) (by change j+1 < (g::gs).length; simp; exact hj) i (by
    simpa only [gateAt,List.getD_cons_succ] using hi)
  omega

theorem relabel_ao {n m : ℕ} (p : Fin n → Fin m) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 m (relabel n m p C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact h.1 a ha
  · intro j hj i hi
    have hlen : j < C.gates.length := by simpa [relabel] using hj
    change i ∈ ((C.gates.map (relGate n m p)).getD j _).inputs at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hlen),List.getElem_map] at hi
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hi
    have hz' := h.2.1 j hlen z (by change z ∈ (C.gates.getD j _).inputs; rw [List.getD_eq_getElem _ _ hlen]; exact hz)
    unfold wmap
    split
    · rename_i hp
      have := (p ⟨z,hp⟩).isLt
      omega
    · omega
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using h.2.2 a ha

theorem relabel_fun {n m : ℕ} (p : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    circuitFun m (relabel n m p C) x = circuitFun n C (x ∘ p) :=
  (rel_fold n m p C.gates _ _ (rel_init n m p x)).2.2 C.output

def PairSensitive {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ (a b : Fin n), a ≠ b → ∀ (op : GateOp), (op = .and ∨ op = .or) → ∀ i : Fin n,
    ∃ x y, (∀ j, j ≠ i → x j = y j) ∧
      op.eval [x a,x b] = op.eval [y a,y b] ∧ f x ≠ f y

theorem first_gate_bound {n : ℕ} (hn : 2 ≤ n) (f : (Fin n → Bool) → Bool)
    (ess : ∀ i, Sensitive f i) (sep : PairSensitive f) (C : Circuit)
    (hc : IsAO2 n C) (hf : circuitFun n C = f) : n+1 ≤ C.size := by
  classical
  generalize hsize : C.size = s
  induction s using Nat.strong_induction_on generalizing C with
  | ind s ih =>
    obtain ⟨gs,o⟩ := C
    cases gs with
    | nil =>
      have h := essential_bound hc (by simpa [hf] using ess)
      change n ≤ 0 + 1 at h
      omega
    | cons g gs =>
      let D : Circuit := ⟨gs,o⟩
      have hD : IsAO2 (n+1) D := tail_ao hc
      have hds : D.size+1 = s := hsize
      have hop := hc.1 g List.mem_cons_self
      have hlen := hc.2.2 g List.mem_cons_self
      obtain ⟨a₀,b₀,hins⟩ : ∃ a b, g.inputs = [a,b] := by
        cases ea : g.inputs with
        | nil => simp [ea] at hlen
        | cons a l =>
          cases l with
          | nil => simp [ea] at hlen
          | cons b l =>
            cases l with
            | nil => exact ⟨a,b,rfl⟩
            | cons z l => simp [ea] at hlen
      have bound (j : ℕ) (hj : j ∈ g.inputs) := hc.2.1 0 (by simp) j (by simpa [gateAt] using hj)
      let a : Fin n := ⟨a₀,by simpa using bound a₀ (by simp [hins])⟩
      let b : Fin n := ⟨b₀,by simpa using bound b₀ (by simp [hins])⟩
      let t (x : Fin n → Bool) := g.op.eval [x a,x b]
      let H := circuitFun (n+1) D
      have fit (x : Fin n → Bool) : H (Fin.snoc x (t x)) = f x := by
        rw [← hf]
        change D.eval (List.ofFn (Fin.snoc x (t x))) = _
        rw [ofFn_snoc]
        change D.eval ((List.ofFn x) ++ [t x]) =
          D.eval ((List.ofFn x) ++ [g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)])
        rw [hins]
        simp [t,List.getD_eq_getElem?_getD, a, b, a.isLt, b.isLt]
      by_cases hskip : ∀ x : Fin n → Bool, H (Fin.snoc x (x a)) = f x
      · let p : Fin (n+1) → Fin n := Fin.snoc id a
        let E := relabel (n+1) n p D
        have he : circuitFun n E = f := by
          funext x
          rw [show circuitFun n E x = H (x ∘ p) from relabel_fun p D x]
          rw [show x ∘ p = Fin.snoc x (x a) by
            funext j
            refine Fin.lastCases (by simp [p]) (fun k => by simp [p]) j]
          exact hskip x
        have hs : E.size = D.size := by simp [E,relabel,Circuit.size]
        exact le_trans (ih _ (by omega : D.size < s) E (relabel_ao p D hD) he hs) (by omega)
      · have hab : a ≠ b := by
          intro eqab
          apply hskip
          intro x
          have tt : t x = x a := by rcases hop with hop | hop <;> simp [t,hop,GateOp.eval,← eqab]
          simpa [tt] using fit x
        have htail : ∀ i, Sensitive H i := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · push_neg at hskip
            obtain ⟨x,hx⟩ := hskip
            refine ⟨Fin.snoc x (x a), Fin.snoc x (t x), ?_, ?_⟩
            · intro k hk
              obtain ⟨l,rfl⟩ := Fin.exists_castSucc_eq.mpr hk
              simp
            · rwa [fit]
          · obtain ⟨x,y,heq,ht,hne⟩ := sep a b hab g.op hop j
            refine ⟨Fin.snoc x (t x), Fin.snoc y (t y), ?_, ?_⟩
            · intro k
              refine Fin.lastCases (fun _ => by simpa [t] using ht) (fun l hlj => ?_) k
              simp only [Fin.snoc_castSucc]
              exact heq l (fun h => hlj (h ▸ rfl))
            · simpa only [fit] using hne
        have hh := essential_bound hD htail
        omega

end Meta2796
