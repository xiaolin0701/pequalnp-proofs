import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Support

namespace FanoStarPrefix
open PEqualNP.CircuitLowerBounds

/-- The three lines at point zero are 0, 4, 6. The prefix computes their OR and the six other stars. -/
def front : Circuit := ⟨[
  ⟨.or, [7,13]⟩,
  ⟨.or, [14,11]⟩,
  ⟨.or, [8,7]⟩,
  ⟨.or, [16,12]⟩,
  ⟨.and, [1,17]⟩,
  ⟨.or, [9,8]⟩,
  ⟨.or, [19,13]⟩,
  ⟨.and, [2,20]⟩,
  ⟨.or, [10,9]⟩,
  ⟨.or, [22,7]⟩,
  ⟨.and, [3,23]⟩,
  ⟨.or, [11,10]⟩,
  ⟨.or, [25,8]⟩,
  ⟨.and, [4,26]⟩,
  ⟨.or, [12,11]⟩,
  ⟨.or, [28,9]⟩,
  ⟨.and, [5,29]⟩,
  ⟨.or, [13,12]⟩,
  ⟨.or, [31,10]⟩,
  ⟨.and, [6,32]⟩], 33⟩

def tap (k : Fin 8) : ℕ := ![0,18,21,24,27,30,33,15] k

def signals (x : Fin 14 → Bool) (k : Fin 8) : Bool :=
  (front.wires (List.ofFn x)).getD (tap k) false

/-- Set the first seven bits freely. Off the three lines at point zero, all line bits are true. -/
def lift (u : Fin 8 → Bool) : Fin 14 → Bool :=
  ![u 0,u 1,u 2,u 3,u 4,u 5,u 6,u 7,true,true,true,u 7,true,u 7]

theorem rightInverse (u : Fin 8 → Bool) : signals (lift u) = u := by
  funext k
  fin_cases k <;> simp [signals, lift, front, tap, Circuit.wires, GateOp.eval, List.getD, List.foldl]

theorem surjective : Function.Surjective signals := fun u => ⟨lift u,rightInverse u⟩

/-- Each point occurs in exactly one terminal, with marked degree one there. -/
theorem point_degrees : ∀ (p : Fin 7) (k : Fin 8),
    (front.lineDegrees 14 {p.val}).getD (tap k) 0 = (if p.val = k.val then 1 else 0) := by
  decide +kernel

def target (u : Fin 8 → Bool) : Bool :=
  (u 1 || u 2 || u 3 || u 4 || u 5 || u 6) || (u 0 && u 7)

def incident (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

def pred (x : Fin 14 → Bool) (p : Fin 7) : Prop :=
  x (Fin.castAdd 7 p) = true ∧ ∃ l : Fin 7, incident p l ∧ x (Fin.natAdd 7 l) = true

private def star (x : Fin 14 → Bool) (p : Fin 7) : Bool :=
  x (Fin.castAdd 7 p) && ((x (Fin.natAdd 7 p) || x (Fin.natAdd 7 (p-1))) ||
    x (Fin.natAdd 7 (p-3)))

private theorem star_correct (x : Fin 14 → Bool) (p : Fin 7) : star x p = true ↔ pred x p := by
  simp only [star, pred, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨hp, (h | h) | h⟩
    · exact ⟨hp,p,Or.inl rfl,h⟩
    · exact ⟨hp,p-1,Or.inr (Or.inl (by simp)),h⟩
    · exact ⟨hp,p-3,Or.inr (Or.inr (by simp)),h⟩
  · rintro ⟨hp,l,(h|h|h),hl⟩
    · subst p; exact ⟨hp,Or.inl (Or.inl hl)⟩
    · subst p; exact ⟨hp, Or.inl (Or.inr (by simpa using hl))⟩
    · subst p; exact ⟨hp, Or.inr (by simpa using hl)⟩

private theorem target_stars (x : Fin 14 → Bool) : target (signals x) =
    (star x 0 || (star x 1 || (star x 2 || (star x 3 || (star x 4 || (star x 5 || star x 6)))))) := by
  have perm (a b c d e f g : Bool) :
      ((b || c || d || e || f || g) || a) = (a || (b || (c || (d || (e || (f || g)))))) := by ac_rfl
  simp [target,signals,tap,front,Circuit.wires,GateOp.eval,List.getD,List.foldl]
  exact perm (star x 0) (star x 1) (star x 2) (star x 3) (star x 4) (star x 5) (star x 6)

theorem target_correct (x : Fin 14 → Bool) : target (signals x) = true ↔
    ∃ p l : Fin 7, incident p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  rw [target_stars]
  simp only [Bool.or_eq_true,star_correct]
  constructor
  · intro h
    have hh : ∃ p : Fin 7, pred x p := by
      rcases h with h|h|h|h|h|h|h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
      · exact ⟨3,h⟩
      · exact ⟨4,h⟩
      · exact ⟨5,h⟩
      · exact ⟨6,h⟩
    obtain ⟨p,hp,l,hpl,hl⟩ := hh
    exact ⟨p,l,hpl,hp,hl⟩
  · rintro ⟨p,l,hpl,hp,hl⟩
    have h : pred x p := ⟨hp,l,hpl,hl⟩
    fin_cases p <;> solve_by_elim (maxDepth := 10) only [Or.inl, Or.inr, h]

/-- All eight independent terminal coordinates are essential to the tail. -/
theorem essential : ∀ i : Fin 8, ∃ u : Fin 8 → Bool,
    target (Function.update u i true) ≠ target (Function.update u i false) := by
  decide +kernel

end FanoStarPrefix

namespace TightTerminal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

private def Sharp {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (D : List ℕ) : Prop :=
  ∀ W : Finset ℕ, t + W.card ≤ (W.biUnion fun j => L.getD j ∅).card →
    (∑ j ∈ W, D.getD j 0) ≤ 1

private theorem sharp_step {n t : ℕ} {L : List (Finset (Fin n))} {D : List ℕ}
    (hl : D.length = L.length) (g : Gate) (a b : ℕ) (hi : g.inputs = [a,b])
    (hc : Cnt t L) (hs : Sharp t L D) :
    Sharp (t+1) (L ++ [gateSupp L g]) (D ++ [g.lineDegree D]) := by
  intro W hbig
  by_cases hW : L.length ∈ W
  · let E := W.erase L.length
    let U := insert a (insert b E)
    have sub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) ⊆
        U.biUnion fun j => L.getD j ∅ := by
      intro v hv
      obtain ⟨j,hj,hv⟩ := Finset.mem_biUnion.mp hv
      by_cases eqn : j = L.length
      · subst j
        rw [getD_snoc_eq] at hv
        obtain ⟨k,hk,hh⟩ := (mem_gateSupp L g v).mp hv
        rw [hi] at hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl <;> exact Finset.mem_biUnion.mpr ⟨_,by simp [U],hh⟩
      · rw [getD_snoc_ne _ _ _ _ eqn] at hv
        exact Finset.mem_biUnion.mpr ⟨j,by simp [U,E,eqn,hj],hv⟩
    have csub := Finset.card_le_card sub
    have cU := hc U
    have cE : E.card+1=W.card := Finset.card_erase_add_one hW
    have cb := Finset.card_insert_le b E
    have ca := Finset.card_insert_le a (insert b E)
    have cl : E.card+2 ≤ U.card := by omega
    have fb : b ∉ E := by
      intro h; rw [Finset.insert_eq_of_mem h] at ca
      change E.card+2 ≤ (insert a (insert b E)).card at cl
      rw [Finset.insert_eq_of_mem h] at cl; omega
    have fa : a ∉ insert b E := by
      intro h
      change E.card+2 ≤ (insert a (insert b E)).card at cl
      rw [Finset.insert_eq_of_mem h] at cl; omega
    have sharp := hs U (by change t+(insert a (insert b E)).card ≤ _; omega)
    rw [show U = insert a (insert b E) from rfl, Finset.sum_insert fa, Finset.sum_insert fb] at sharp
    have esum : ∑ j ∈ E, (D ++ [g.lineDegree D]).getD j 0 = ∑ j ∈ E, D.getD j 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (by simpa only [hl] using (Finset.mem_erase.mp hj).1)
    have ws : W = insert L.length E := (Finset.insert_erase hW).symm
    rw [ws, Finset.sum_insert (by simp [E]), esum, ←hl, getD_snoc_eq]
    have ledeg : g.lineDegree D ≤ D.getD a 0 + D.getD b 0 := by
      unfold Gate.lineDegree
      rw [hi]
      split <;> simp
    omega
  · have es : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
        W.biUnion fun j => L.getD j ∅ := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun he => hW (he ▸ hj))
    rw [es] at hbig
    have h := hc W
    omega

private def runD (gs : List Gate) (D : List ℕ) :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) D

private theorem sharp_run {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))) (D : List ℕ),
    (∀ g ∈ gs, ∃ a b, g.inputs = [a,b]) → D.length = L.length →
    Cnt t L → Sharp t L D → Sharp (t+gs.length) (suppsFrom gs L) (runD gs D) := by
  induction gs with
  | nil => intros; simpa [runD,suppsFrom]
  | cons g gs ih =>
    intro t L D shape hl cnt sh
    obtain ⟨a,b,hi⟩ := shape _ List.mem_cons_self
    have hc := cnt_step t L g (by simp [hi]) cnt
    have hs := sharp_step hl g a b hi cnt sh
    simpa only [List.length_cons, Nat.add_right_comm, Nat.add_assoc,suppsFrom,runD,List.foldl_cons] using
      ih (t+1) (L ++ [gateSupp L g]) (D ++ [g.lineDegree D])
        (fun g' h => shape _ (List.mem_cons_of_mem _ h)) (by simp [hl]) hc hs

private theorem sharp_inputs {n : ℕ} (p : Fin n) :
    Sharp 0 (inputSupps n) ((List.range n).map fun a => if a ∈ ({p.val} : Finset ℕ) then 1 else 0) := by
  intro W _
  have atWire (j : ℕ) : ((List.range n).map (fun a => if a ∈ ({p.val} : Finset ℕ) then 1 else 0)).getD j 0 =
      (if j = p.val then 1 else 0) := by
    by_cases hj : j < n
    · have hj' : j < ((List.range n).map (fun a => if a ∈ ({p.val} : Finset ℕ) then 1 else 0)).length := by simpa using hj
      rw [List.getD_eq_getElem _ _ hj',List.getElem_map,List.getElem_range]; simp
    · have hne : j ≠ p.val := by have := p.isLt; omega
      rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [hne]
  simp_rw [atWire]
  simp only [Finset.sum_ite_eq']
  split <;> omega

/-- A binary circuit on n independent, essential inputs and at most n−1 gates gives each
    individual input marked degree at most one. The gates may share intermediate wires. -/
theorem tight_degree {n : ℕ} (C : Circuit) (p : Fin n)
    (shape : ∀ g ∈ C.gates, ∃ a b, g.inputs = [a,b])
    (size : C.size+1 ≤ n)
    (sensitive : ∀ i : Fin n, ∃ x : Fin n → Bool,
      C.eval (List.ofFn (Function.update x i true)) ≠ C.eval (List.ofFn (Function.update x i false))) :
    C.lineDeg n {p.val} ≤ 1 := by
  classical
  let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  have hall (i : Fin n) : i ∈ S := by
    by_contra hi
    obtain ⟨x,hx⟩ := sensitive i
    apply hx
    exact (agree_wiresFrom (Function.update x i true) (Function.update x i false) C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have hne : k ≠ i := fun h => hi (h ▸ hk)
        simp [Function.update_of_ne hne])
  have hS : S.card = n := by rw [Finset.eq_univ_of_forall hall]; simp
  let D := (List.range n).map (fun a => if a ∈ ({p.val} : Finset ℕ) then 1 else 0)
  have hx := sharp_run C.gates 0 (inputSupps n) D shape (by simp [D,inputSupps]) cnt_inputs
    (sharp_inputs p) {C.output} (by
      simp only [Finset.singleton_biUnion, Finset.card_singleton,Nat.zero_add]
      change C.size + 1 ≤ S.card
      rwa [hS])
  simpa only [Finset.sum_singleton,runD,D,Circuit.lineDeg,Circuit.lineDegrees] using hx

end TightTerminal

namespace FanoStarPrefix
open PEqualNP.CircuitLowerBounds

/-- A tail using only these eight taps and at most seven binary gates cannot
    reread any point while computing the target. Each point has the singleton
    terminal marking certified by point_degrees above. -/
theorem no_point_reread (C : Circuit)
    (shape : ∀ g ∈ C.gates, ∃ a b, g.inputs = [a,b]) (budget : C.size ≤ 7)
    (correct : ∀ x, C.eval (List.ofFn (signals x)) = target (signals x))
    (p : Fin 7) : C.lineDeg 8 {p.val} ≤ 1 := by
  apply TightTerminal.tight_degree C (Fin.castLE (by decide : 7 ≤ 8) p) shape (by omega)
  intro i
  obtain ⟨u,hu⟩ := essential i
  have tail (v : Fin 8 → Bool) : C.eval (List.ofFn v) = target v := by
    obtain ⟨x,rfl⟩ := surjective v
    exact correct x
  exact ⟨u,by simpa only [tail] using hu⟩

theorem no_point_reread_incidence (C : Circuit)
    (shape : ∀ g ∈ C.gates, ∃ a b, g.inputs = [a,b]) (budget : C.size ≤ 7)
    (correct : ∀ x, C.eval (List.ofFn (signals x)) = true ↔ ∃ p l : Fin 7,
        incident p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
    (p : Fin 7) : C.lineDeg 8 {p.val} ≤ 1 := by
  apply no_point_reread C shape budget _ p
  intro x
  exact Bool.eq_iff_iff.mpr ((correct x).trans (target_correct x).symm)

/-- Start the tail with the actual marked degrees of these eight prefix wires. -/
def outputPointDegree (C : Circuit) (p : Fin 7) : ℕ :=
  (C.gates.foldl (fun d g => d ++ [g.lineDegree d])
    (List.ofFn fun k : Fin 8 => (front.lineDegrees 14 {p.val}).getD (tap k) 0)).getD C.output 0

theorem outputPointDegree_eq (C : Circuit) (p : Fin 7) :
    outputPointDegree C p = C.lineDeg 8 {p.val} := by
  have initial :
      (List.ofFn fun k : Fin 8 => (front.lineDegrees 14 {p.val}).getD (tap k) 0) =
        (List.range 8).map (fun j => if j ∈ ({p.val} : Finset ℕ) then 1 else 0) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range,point_degrees,Finset.mem_singleton]
      by_cases h : p.val = i
      · simp [h]
      · simp [h, Ne.symm h]
  unfold outputPointDegree
  rw [initial]
  rfl

theorem prefix_tail_obstruction (C : Circuit)
    (shape : ∀ g ∈ C.gates, ∃ a b, g.inputs = [a,b]) (budget : C.size ≤ 7)
    (correct : ∀ x, C.eval (List.ofFn (signals x)) = true ↔ ∃ p l : Fin 7,
        incident p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
    (p : Fin 7) : outputPointDegree C p ≤ 1 := by
  rw [outputPointDegree_eq]
  exact no_point_reread_incidence C shape budget correct p

end FanoStarPrefix
