import SixStarTail
import DoubleStarTerminal

namespace PlaneStarTail.Five
open Signal Heawood
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def U : Finset (Fin 7) := {5,6}
def pvar : Fin 7 → Fin 12 := ![7,8,9,10,11,1,3]
def lvar : Fin 7 → Fin 12 := ![0,5,2,0,6,4,0]
def outside : Finset (Fin 7) := {0,6}
def lift (x : Fin 12 → Bool) : Cells 7 :=
  (Finset.univ.filter (fun p => x (pvar p)=true),
   Finset.univ.filter (fun l => l ∈ outside ∨ x (lvar l)=true))
def index : Signal 7 → Fin 12
  | .point p | .completed p => pvar p
  | .line l => lvar l
  | .pointOr _ _ => 0

private theorem count : (wanted I U).card=12 := by decide +kernel
private theorem far (p : Fin 7) (hp : p ∉ U) : ∃ l ∈ outside, I p l := by
  revert p
  decide +kernel
private theorem lineTag (l : Fin 7) (hl : 7+l.val ∈ wanted I U) : l ∉ outside := by
  revert l
  decide +kernel
private theorem junk : 14 ∉ wanted I U := by decide +kernel

private theorem onChosen (s : Signal 7) (valid : s.allowed I U) (tagged : s.tag ∈ wanted I U)
    (x : Fin 12 → Bool) : s.holds I (lift x) ↔ x (index s)=true := by
  cases s with
  | point p => simp [holds,lift,index]
  | line l => simp [holds,lift,index,lineTag l tagged]
  | completed p =>
    obtain ⟨l,hl,il⟩ := far p valid
    simp only [holds,lift,Finset.mem_filter,Finset.mem_univ,true_and,index]
    exact ⟨And.left,fun h => ⟨h,l,Or.inl hl,il⟩⟩
  | pointOr p T => exact (junk tagged).elim

private theorem exists7 (P : Fin 7 → Prop) : (∃ i, P i) ↔
    P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6 := by
  constructor
  · rintro ⟨i,h⟩; fin_cases i <;> tauto
  · rintro (h|h|h|h|h|h|h) <;> exact ⟨_,h⟩

set_option maxHeartbeats 5000000 in
theorem liftedFlag (x : Fin 12 → Bool) : decide (flag I (lift x)) = DoubleStar.terminal 12 x := by
  rw [Bool.eq_iff_iff,decide_eq_true_eq]
  have pts (p : Fin 7) : p ∈ (lift x).1 ↔ x (pvar p) = true := by simp [lift]
  have lns (l : Fin 7) : l ∈ (lift x).2 ↔ l ∈ outside ∨ x (lvar l) = true := by simp [lift]
  simp only [flag,exists7,pts,lns]
  simp [DoubleStar.terminal,I,pvar,lvar,outside]
  <;> tauto

end PlaneStarTail.Five

namespace PlaneStarTail.Five
open Signal Heawood
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The unfinished rows are 5 and 6 in the labelling of the 21 original edges.
theorem fiveCompleted (sigs : List (Signal 7)) (ok : ∀ s ∈ sigs, s.allowed I U)
    (C : Circuit) (shape : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ x : Cells 7, C.eval (sigs.map (fun s => decide (s.holds I x))) = decide (flag I x)) :
    27 ≤ 15+C.size := by
  classical
  by_contra! bounded
  let w := fun z : Fin sigs.length → Bool => List.ofFn z
  let obs (x : Cells 7) := fun i : Fin sigs.length => decide (sigs[i.val].holds I x)
  have lookup (z : Fin sigs.length → Bool) (i : ℕ) (h : i<sigs.length) :
      (w z).getD i false = z ⟨i,h⟩ := by simp [w,List.getD_eq_getElem?_getD,h]
  have zero (z : Fin sigs.length → Bool) (i : ℕ) (h : sigs.length ≤ i) :
      (w z).getD i false = false := List.getD_eq_default _ _ (by simpa [w] using h)
  have obsCorrect (x : Cells 7) : C.eval (w (obs x)) = decide (flag I x) := by
    change C.eval (List.ofFn _) = _
    rw [List.ofFn_getElem_eq_map sigs (fun s => decide (s.holds I x))]
    exact correct x
  obtain ⟨S,small,dep⟩ := smallSupport C.gates C.output w sigs.length (fun z => by simp [w]) shape
  have sep : ∀ x y : Cells 7, flag I x → ¬ flag I y →
      ∃ t ∈ S, ∃ s : Signal 7, sigs[t]? = some s ∧ s.holds I x ∧ ¬s.holds I y := by
    intro x y px py
    by_contra! fail
    have seen : (tailEval C.gates (w (obs x))).getD C.output false = true := (obsCorrect x).trans (decide_eq_true px)
    have dead : (tailEval C.gates (w (obs y))).getD C.output false = false := (obsCorrect y).trans (decide_eq_false py)
    apply Bool.false_ne_true (dead.symm.trans (dep _ _ (fun t ht => ?_) seen))
    by_cases h : t<sigs.length
    · rw [lookup _ _ h,lookup _ _ h]
      exact fun on => decide_eq_true (fail t ht sigs[t] (List.getElem?_eq_getElem h) (of_decide_eq_true on))
    · rw [zero _ _ (by omega),zero _ _ (by omega)]; exact id
  have row : ∀ p, ∃ l, I p l := by decide +kernel
  have cross : ∀ p r, p ≠ r → ∀ l k, I p l → I r l → I p k → I r k → l=k := by decide +kernel
  have sub := (tagsNecessary I U row cross sigs ok S sep).2
  have maxCard : (S.image (wireTag sigs)).card ≤ 12 := by
    have h := (Finset.card_image_le : (S.image (wireTag sigs)).card ≤ S.card).trans small
    change 27 > 15+C.gates.length at bounded
    omega
  have full : wanted I U = S.image (wireTag sigs) := Finset.eq_of_subset_of_card_le sub (count ▸ maxCard)
  let π := fun i : Fin sigs.length => index sigs[i.val]
  let F := fun z : Fin sigs.length → Bool => C.eval (w z)
  have hF : HasCircuitSize sigs.length F 11 := by
    refine ⟨C,?_,by omega,fun _ => rfl⟩
    intro g hg
    obtain ⟨op,arity⟩ := shape g hg
    exact ⟨by rcases op with h|h <;> simp [h],arity⟩
  have h12 := PEqualNP.Outside.L_meta_245.Helpers.PermInputs.relabel_size π F 11 hF
  have eq : (fun z : Fin 12 → Bool => F (z ∘ π)) = DoubleStar.terminal 12 := by
    funext z
    have agree (t : ℕ) (ht : t ∈ S) : (w (z ∘ π)).getD t false = (w (obs (lift z))).getD t false := by
      by_cases h : t < sigs.length
      · have tagMem : wireTag sigs t ∈ wanted I U := full ▸ Finset.mem_image_of_mem _ ht
        have good : sigs[t].tag ∈ wanted I U := by simpa [wireTag,List.getElem?_eq_getElem h] using tagMem
        rw [lookup _ _ h,lookup _ _ h]
        change z (index sigs[t]) = decide _
        exact Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq]; exact (onChosen _ (ok _ (List.getElem_mem _)) good z).symm)
      · rw [zero _ _ (by omega),zero _ _ (by omega)]
    have ev : F (z ∘ π) = C.eval (w (obs (lift z))) := by
      apply Bool.eq_iff_iff.mpr
      exact ⟨dep _ _ (fun t ht => (agree t ht) ▸ id),dep _ _ (fun t ht => (agree t ht).symm ▸ id)⟩
    exact ev.trans ((obsCorrect (lift z)).trans (liftedFlag z))
  exact DoubleStar.lower (eq ▸ h12)

end PlaneStarTail.Five
