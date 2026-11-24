import Mathlib
import PEqualNP.Defs.TopForm

namespace PlaneStarTail
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def evalGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def tailEval (gs : List Gate) (w : List Bool) := gs.foldl (fun w g => w ++ [evalGate g w]) w

private theorem gateMono (g : Gate) (op : g.op = .and ∨ g.op = .or) (w w' : List Bool)
    (inc : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true) :
    evalGate g w = true → evalGate g w' = true := by
  rcases op with h|h
  · simp only [evalGate,h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
    intro all b i hi eq
    exact eq ▸ inc i hi (all _ i hi rfl)
  · simp only [evalGate,h,GateOp.eval,List.any_eq_true,List.mem_map]
    rintro ⟨b,⟨i,hi,rfl⟩,on⟩
    exact ⟨_,⟨i,hi,rfl⟩,inc i hi on⟩

theorem smallSupport {X : Type} (gs : List Gate) (out : ℕ) (w : X → List Bool) (n : ℕ)
    (hlen : ∀ x, (w x).length=n)
    (shape : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∃ S : Finset ℕ, S.card ≤ gs.length+1 ∧
      ∀ x y, (∀ t ∈ S, (w x).getD t false = true → (w y).getD t false = true) →
        (tailEval gs (w x)).getD out false = true → (tailEval gs (w y)).getD out false = true := by
  classical
  induction gs generalizing n w with
  | nil => exact ⟨{out}, by simp,fun x y h => h out (by simp)⟩
  | cons g gs ih =>
    let v (x : X) := w x ++ [evalGate g (w x)]
    have eqLen (x : X) : (v x).length=n+1 := by simp [v,hlen]
    have prev (x : X) (t : ℕ) (ne : t ≠ n) : (v x).getD t false = (w x).getD t false := by
      by_cases lt : t<n
      · exact List.getD_append _ _ _ _ (by rw [hlen]; exact lt)
      · rw [List.getD_eq_default _ _ (by rw [eqLen]; omega),List.getD_eq_default _ _ (by rw [hlen]; omega)]
    have now (x : X) : (v x).getD n false = evalGate g (w x) := by
      rw [show v x = _ from rfl,List.getD_append_right _ _ _ _ (by rw [hlen]),hlen,Nat.sub_self]; rfl
    obtain ⟨S,size,dep⟩ := ih v (n+1) eqLen (fun g hg => shape g (List.mem_cons_of_mem _ hg))
    by_cases hn : n ∈ S
    · let R := S.erase n ∪ g.inputs.toFinset
      have bound : R.card ≤ (g::gs).length+1 := by
        have h1 := Finset.card_union_le (S.erase n) g.inputs.toFinset
        have h2 := Finset.card_erase_add_one hn
        have h3 := g.inputs.toFinset_card_le
        have h4 := (shape g List.mem_cons_self).2
        dsimp [R]; omega
      refine ⟨R,bound,fun x y h => dep x y (fun t ht => ?_)⟩
      by_cases eq : t=n
      · subst t
        rw [now,now]
        exact gateMono g (shape g List.mem_cons_self).1 _ _
          (fun i hi => h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
      · rw [prev x t eq,prev y t eq]
        exact h t (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ht⟩))
    · refine ⟨S,by simp only [List.length_cons]; omega,fun x y h => dep x y (fun t ht => ?_)⟩
      have ne : t≠n := fun e => hn (e ▸ ht)
      rw [prev x t ne,prev y t ne]
      exact h t ht

end PlaneStarTail

namespace PlaneStarTail
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

abbrev Cells (N : ℕ) := Finset (Fin N) × Finset (Fin N)

inductive Signal (N : ℕ) where
  | point (p : Fin N)
  | line (l : Fin N)
  | pointOr (owner : Fin N) (terms : Finset (Fin N))
  | completed (p : Fin N)

namespace Signal
variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def holds (s : Signal N) (x : Cells N) : Prop :=
  match s with
  | .point p => p ∈ x.1
  | .line l => l ∈ x.2
  | .pointOr _ T => ∃ l ∈ T, l ∈ x.2
  | .completed p => p ∈ x.1 ∧ ∃ l ∈ x.2, I p l

instance (s : Signal N) (x : Cells N) : Decidable (s.holds I x) := by
  cases s <;> unfold holds <;> infer_instance

def allowed (U : Finset (Fin N)) : Signal N → Prop
  | .point _ | .line _ => True
  | .pointOr p T => p ∉ U ∧ 2 ≤ T.card ∧ ∀ l ∈ T, I p l
  | .completed p => p ∉ U

def tag : Signal N → ℕ
  | .point p | .completed p => p.val
  | .line l => N+l.val
  | .pointOr _ _ => N+N

def flag (x : Cells N) : Prop := ∃ p ∈ x.1, ∃ l ∈ x.2, I p l

instance (x : Cells N) : Decidable (flag I x) := by unfold flag; infer_instance

private theorem pick {n : ℕ} {T : Finset (Fin n)} (big : 2 ≤ T.card) :
    ∃ a ∈ T, ∃ b ∈ T, a ≠ b := Finset.one_lt_card.mp big

def wanted (U : Finset (Fin N)) : Finset ℕ :=
    (Finset.univ.image (fun p : Fin N => p.val)) ∪
      ((U.biUnion (fun p => Finset.univ.filter (fun l => I p l))).image (fun l => N+l.val))

def wireTag (sigs : List (Signal N)) (t : ℕ) := ((sigs[t]?).map tag).getD (N+N)

theorem tagsNecessary (U : Finset (Fin N))
    (row : ∀ p, ∃ l, I p l)
    (intersection : ∀ p r, p ≠ r → ∀ l k, I p l → I r l → I p k → I r k → l=k)
    (sigs : List (Signal N)) (valid : ∀ s ∈ sigs, s.allowed I U)
    (S : Finset ℕ)
    (separates : ∀ x y : Cells N, flag I x → ¬ flag I y →
      ∃ t ∈ S, ∃ s : Signal N, sigs[t]? = some s ∧ s.holds I x ∧ ¬ s.holds I y) :
    N+(U.biUnion fun p => Finset.univ.filter (fun l => I p l)).card ≤ S.card ∧ wanted I U ⊆ S.image (wireTag sigs) := by
  classical
  let label (t : ℕ) := ((sigs[t]?).map tag).getD (N+N)
  let P := (Finset.univ : Finset (Fin N)).image Fin.val
  let H := U.biUnion (fun p => Finset.univ.filter (fun l => I p l))
  let L := H.image (fun l => N+l.val)
  have point (p : Fin N) : p.val ∈ S.image label := by
    obtain ⟨l,inc⟩ := row p
    let x : Cells N := ({p},{l})
    let y : Cells N := (∅,Finset.univ)
    have pos : flag I x := ⟨p,by simp [x],l,by simp [x],inc⟩
    have neg : ¬ flag I y := by simp [flag,y]
    obtain ⟨t,ht,s,eq,sx,sy⟩ := separates x y pos neg
    refine Finset.mem_image.mpr ⟨t,ht,?_⟩
    simp [label,eq]
    cases s with
    | point r => simpa [holds,x,tag] using congrArg Fin.val (show r = p by simpa [holds,x] using sx)
    | line j => exact False.elim (sy (by simp [holds,y]))
    | pointOr r T =>
      obtain ⟨j,hj,_⟩ := sx
      exact False.elim (sy ⟨j,hj,Finset.mem_univ _⟩)
    | completed r => exact congrArg Fin.val (show r=p by simpa [holds,x] using sx.1)
  have line (l : Fin N) (hl : l ∈ H) : N+l.val ∈ S.image label := by
    obtain ⟨p,hp,pl⟩ := Finset.mem_biUnion.mp hl
    have inc := (Finset.mem_filter.mp pl).2
    let x : Cells N := ({p},{l})
    let y : Cells N := ({p},Finset.univ.filter (fun j => ¬ I p j))
    have pos : flag I x := ⟨p,by simp [x],l,by simp [x],inc⟩
    have neg : ¬ flag I y := by
      simp [flag,y]
    obtain ⟨t,ht,s,eq,sx,sy⟩ := separates x y pos neg
    have ok := valid s (List.mem_of_getElem? eq)
    refine Finset.mem_image.mpr ⟨t,ht,?_⟩
    simp [label,eq]
    cases s with
    | point r => exact False.elim (sy sx)
    | line j =>
      have e : j=l := by simpa [holds,x] using sx
      rw [e]; rfl
    | completed r =>
      have e : r=p := by simpa [holds,x] using sx.1
      exact False.elim (ok (e ▸ hp))
    | pointOr r T =>
      obtain ⟨outside,big,good⟩ := ok
      have ne : p ≠ r := fun e => outside (e ▸ hp)
      obtain ⟨u,hu,v,hv,diff⟩ := pick big
      have no (j : Fin N) (hj : j ∈ T) : I p j := by
        by_contra bad
        exact sy ⟨j,hj,by simpa [y] using bad⟩
      exact False.elim (diff (intersection p r ne u v (no u hu) (good u hu) (no v hv) (good v hv)))
  have disj : Disjoint P L := by
    apply Finset.disjoint_left.mpr
    intro k hk lk
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨l,_,e⟩ := Finset.mem_image.mp lk
    have h := p.isLt
    omega
  have incl : P ∪ L ⊆ S.image label := by
    intro t ht
    rcases Finset.mem_union.mp ht with hp|hl
    · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hp
      exact point p
    · obtain ⟨l,member,eq⟩ := Finset.mem_image.mp (show t ∈ H.image (fun l => N+l.val) from hl)
      exact eq ▸ line l member
  have cb := (Finset.card_le_card incl).trans Finset.card_image_le
  have lc : L.card=H.card := Finset.card_image_of_injective _ (fun _ _ e => Fin.ext (by omega))
  have pc : P.card=N := by simp [P,Finset.card_image_of_injective _ Fin.val_injective]
  exact ⟨by simpa only [Finset.card_union_of_disjoint disj,pc,lc] using cb,incl⟩

end Signal
end PlaneStarTail

namespace PlaneStarTail
open PEqualNP.CircuitLowerBounds

theorem tailGateCount {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (U : Finset (Fin N)) (row : ∀ p, ∃ l, I p l)
    (intersection : ∀ p r, p ≠ r → ∀ l k, I p l → I r l → I p k → I r k → l=k)
    (sigs : List (Signal N)) (valid : ∀ s ∈ sigs, s.allowed I U)
    (C : Circuit) (shape : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ x : Cells N, C.eval (sigs.map (fun s => decide (s.holds I x))) = decide (Signal.flag I x)) :
    N+(U.biUnion fun p => Finset.univ.filter (fun l => I p l)).card ≤ C.size+1 := by
  let w (x : Cells N) := sigs.map (fun s => decide (s.holds I x))
  obtain ⟨S,small,dep⟩ := smallSupport C.gates C.output w sigs.length (fun x => by simp [w]) shape
  refine (Signal.tagsNecessary I U row intersection sigs valid S ?_).1.trans small
  intro x y px py
  by_contra! fail
  have seen : (tailEval C.gates (w x)).getD C.output false = true := (correct x).trans (decide_eq_true px)
  have gone : (tailEval C.gates (w y)).getD C.output false = false := (correct y).trans (decide_eq_false py)
  have force := dep x y (fun t ht => ?_) seen
  · exact Bool.false_ne_true (gone.symm.trans force)
  · intro on
    by_cases h : t<sigs.length
    · have lenX : t<(w x).length := by simpa [w] using h
      have lenY : t<(w y).length := by simpa [w] using h
      rw [List.getD_eq_getElem _ _ lenX] at on
      rw [List.getD_eq_getElem _ _ lenY]
      have hx : sigs[t].holds I x := by simpa [w] using on
      have hy := fail t ht sigs[t] (List.getElem?_eq_getElem h) hx
      simpa [w] using hy
    · have bad : (w x).length ≤ t := by simp [w]; omega
      rw [List.getD_eq_default _ _ bad] at on
      contradiction

namespace Heawood

def I (p l : Fin 7) : Prop := l ∈ (![({0,1,3} : Finset (Fin 7)),{0,2,6},{1,5,6},
    {0,4,5},{3,4,6},{2,3,5},{1,2,4}] : Fin 7 → Finset (Fin 7)) p
instance : DecidableRel I := fun p l => by unfold I; infer_instance

private theorem row : ∀ p, ∃ l, I p l := by decide +kernel
private theorem intersection : ∀ p r, p ≠ r → ∀ l k, I p l → I r l → I p k → I r k → l=k := by decide +kernel
private theorem degree : ∀ p : Fin 7, (Finset.univ.filter (fun l : Fin 7 => I p l)).card = 3 := by decide +kernel

-- All 14 raw signals, both intermediate line-ORs at each processed point,
-- and every completed star may be read arbitrarily many times in the suffix.
-- The size bound even permits extra copies of any permitted signal for free.
theorem sixCompleted (remaining : Fin 7) (sigs : List (Signal 7))
    (valid : ∀ s ∈ sigs, s.allowed I {remaining})
    (C : Circuit) (shape : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ x : Cells 7, C.eval (sigs.map (fun s => decide (s.holds I x))) = decide (Signal.flag I x)) :
    27 ≤ 18+C.size := by
  have h := tailGateCount I {remaining} row intersection sigs valid C shape correct
  simp [degree] at h
  omega

end Heawood
end PlaneStarTail
