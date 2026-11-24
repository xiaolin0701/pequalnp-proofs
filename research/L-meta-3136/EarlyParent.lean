import Mathlib
import PEqualNP.Defs

namespace Petersen3136
open PEqualNP.CircuitLowerBounds

def evalGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)

def tailEval (gs : List Gate) (w : List Bool) := gs.foldl (fun w g => w ++ [evalGate g w]) w

private theorem gateAgree (g : Gate) (w w' : List Bool)
    (inc : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : evalGate g w = evalGate g w' := by
  have h := List.map_congr_left inc
  exact congrArg g.op.eval h

theorem smallSupport {X : Type} (gs : List Gate) (out : ℕ) (w : X → List Bool) (n : ℕ)
    (hlen : ∀ x, (w x).length=n)
    (shape : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ S : Finset ℕ, S.card ≤ gs.length+1 ∧
      ∀ x y, (∀ t ∈ S, (w x).getD t false = (w y).getD t false) →
        (tailEval gs (w x)).getD out false = (tailEval gs (w y)).getD out false := by
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
        have h4 := (shape g List.mem_cons_self)
        dsimp [R]; omega
      refine ⟨R,bound,fun x y h => dep x y (fun t ht => ?_)⟩
      by_cases eq : t=n
      · subst t
        rw [now,now]
        exact gateAgree g _ _
          (fun i hi => h i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)))
      · rw [prev x t eq,prev y t eq]
        exact h t (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ht⟩))
    · refine ⟨S,by simp only [List.length_cons]; omega,fun x y h => dep x y (fun t ht => ?_)⟩
      have ne : t≠n := fun e => hn (e ▸ ht)
      rw [prev x t ne,prev y t ne]
      exact h t ht


end Petersen3136

namespace Petersen3136
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def F (x : Fin 9 → Bool) := edges.any fun e => x e.1 && x e.2

def signals (x : Fin 9 → Bool) (j : Fin 10) : Bool :=
  if h : j.val<9 then x ⟨j.val,h⟩ else x 0 || x 3

def wires (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]

theorem signals_read (x : Fin 9 → Bool) (i : Fin 10) : (wires x).getD i.val false = signals x i := by
  fin_cases i <;> simp [wires,signals,List.getD_eq_getElem?_getD ]

def K₁ : Finset (Fin 10) := {1,7,8,9}
def K₂ : Finset (Fin 10) := {2,5,6,9}

def blocked (Z : Finset (Fin 10)) (i : Fin 9) : Prop := i.castSucc ∈ Z ∨ (9 ∈ Z ∧ (i=0 ∨ i=3))
instance (Z : Finset (Fin 10)) (i : Fin 9) : Decidable (blocked Z i) := by unfold blocked; infer_instance

def cover (Z : Finset (Fin 10)) : Prop := ∀ e ∈ edges, blocked Z e.1 ∨ blocked Z e.2
instance (Z : Finset (Fin 10)) : Decidable (cover Z) := by unfold cover; infer_instance

private theorem only_covers : ∀ Z : Finset (Fin 10), Z.card ≤ 4 → cover Z → Z=K₁ ∨ Z=K₂ := by
  decide +kernel

private theorem card₁ : K₁.card=4 := by decide
private theorem card₂ : K₂.card=4 := by decide

def zeros (S : Finset (Fin 10)) (x : Fin 9 → Bool) := S.filter (fun j => signals x j = false)
def extend (S : Finset (Fin 10)) (x : Fin 9 → Bool) (i : Fin 9) : Bool := decide (¬ blocked (zeros S x) i)

private theorem included (S : Finset (Fin 10)) (x : Fin 9 → Bool) {i : Fin 9} (h : x i = true) :
    extend S x i = true := by
  apply decide_eq_true
  rintro (a|⟨a,b⟩)
  · have f := (Finset.mem_filter.mp a).2
    simp [signals,i.isLt,h] at f
  · have f := (Finset.mem_filter.mp a).2
    rcases b with rfl|rfl <;> simp [signals,h] at f

private theorem agrees (S : Finset (Fin 10)) (x : Fin 9 → Bool) {j : Fin 10} (hj : j ∈ S) :
    signals (extend S x) j = signals x j := by
  by_cases h : j.val<9
  · let i : Fin 9 := ⟨j.val,h⟩
    change (if _ : j.val<9 then _ else _) = _
    simp only [signals,dite_eq_left h]
    change extend S x i = x i
    cases e : x i with
    | true => exact included S x e
    | false =>
      apply decide_eq_false
      apply not_not_intro
      apply Or.inl
      have eq : i.castSucc=j := Fin.ext rfl
      rw [eq]
      exact Finset.mem_filter.mpr ⟨hj,by simpa [signals,h,i] using e⟩
  · have eq : j=9 := Fin.ext (by have := j.isLt; omega)
    subst j
    change (extend S x 0 || extend S x 3) = (x 0 || x 3)
    cases e : (x 0 || x 3) with
    | true =>
      rcases Bool.or_eq_true_iff.mp e with a|b
      · simp [included S x a]
      · simp [included S x b]
    | false =>
      have nine : (9 : Fin 10) ∈ zeros S x := Finset.mem_filter.mpr ⟨hj,by simpa [signals] using e⟩
      simp [extend,blocked,nine]

private theorem false_covers (S : Finset (Fin 10)) (x : Fin 9 → Bool)
    (h : F (extend S x)=false) : cover (zeros S x) := by
  intro e he
  by_contra! miss
  have h1 : extend S x e.1 = true := decide_eq_true miss.1
  have h2 : extend S x e.2 = true := decide_eq_true miss.2
  have yes : F (extend S x) = true := List.any_eq_true.mpr ⟨e,he,by simp [h1,h2]⟩
  exact Bool.false_ne_true (h.symm.trans yes)

private theorem allZero (S : Finset (Fin 10)) (x : Fin 9 → Bool) (lim : S.card≤4)
    (h : F (extend S x)=false) : (S=K₁ ∨ S=K₂) ∧ zeros S x = S := by
  let Z := zeros S x
  have sub : Z ⊆ S := Finset.filter_subset _ _
  have c := only_covers Z ((Finset.card_le_card sub).trans lim) (false_covers S x h)
  have eq : Z=S := Finset.eq_of_subset_of_card_le sub (by rcases c with a|a <;> rw [a] <;> simpa [card₁,card₂] using lim)
  exact ⟨eq ▸ c,eq⟩

theorem majorant_support (W : (Fin 9 → Bool) → Bool) (S : Finset (Fin 10)) (lim : S.card≤4)
    (dep : ∀ x y, (∀ j ∈ S, signals x j = signals y j) → W x=W y)
    (covers : ∀ x, F x=true → W x=true) (nontrivial : ∃ y, W y=false) :
    (S=K₁ ∨ S=K₂) ∧ ∀ x, W x = decide (∃ j ∈ S, signals x j = true) := by
  have onFalse (x : Fin 9 → Bool) (off : W x=false) : F (extend S x)=false := by
    have same := dep (extend S x) x (fun _ hj => agrees S x hj)
    cases h : F (extend S x) with
    | false => rfl
    | true => have yes := (same.symm.trans (covers _ h)); simp [off] at yes
  obtain ⟨y,hy⟩ := nontrivial
  obtain ⟨forms,zy⟩ := allZero S y lim (onFalse y hy)
  refine ⟨forms,fun x => Bool.eq_iff_iff.mpr ?_⟩
  rw [decide_eq_true_eq]
  constructor
  · intro yes
    by_contra! all
    have eq := dep x y (fun j hj => (by
      have hz := (Finset.mem_filter.mp (show j ∈ zeros S y by rw [zy]; exact hj)).2
      rw [hz]
      exact Bool.eq_false_iff.mpr (all j hj) : signals x j = signals y j))
    exact Bool.false_ne_true (hy.symm.trans (eq.symm.trans yes))
  · rintro ⟨j,hj,active⟩
    cases off : W x with
    | true => rfl
    | false =>
      have z := (allZero S x lim (onFalse x off)).2
      have bad := (Finset.mem_filter.mp (show j ∈ zeros S x by rw [z]; exact hj)).2
      exact False.elim (Bool.false_ne_true (bad.symm.trans active))

end Petersen3136

namespace Petersen3136
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem runLen (gs : List Gate) (w : List Bool) : (tailEval gs w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [tailEval]
  | cons g gs ih => change (tailEval gs (w++[evalGate g w])).length = _; rw [ih]; simp; omega

private theorem stable (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (tailEval gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (tailEval gs (w++[evalGate g w])).getD i false = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ h]

theorem early_parent (gs : List Gate) (len : gs.length = 13)
    (fan : FanInTwo (⟨gs,0⟩ : Circuit)) (j : ℕ) (early : j ≤ 12)
    (W : (Fin 9 → Bool) → Bool) (wire : ∀ x, W x = ((⟨gs,0⟩ : Circuit).wires (wires x)).getD j false)
    (covers : ∀ x, F x=true → W x=true) (nontrivial : ∃ y, W y=false) :
    j=12 ∧ ((∀ x, W x = decide (∃ i ∈ K₁, signals x i = true)) ∨
      (∀ x, W x = decide (∃ i ∈ K₂, signals x i = true))) := by
  classical
  let k := (j+1)-10
  have hk : k≤3 := by dsimp [k]; omega
  let block := gs.take k
  have blen : block.length=k := by simp [block,len,Nat.min_eq_left (show k≤13 by omega)]
  have val (x : Fin 9 → Bool) : W x = (tailEval block (wires x)).getD j false := by
    rw [wire]
    change (tailEval gs (wires x)).getD j false = _
    have eq : gs=block++gs.drop k := (List.take_append_drop k gs).symm
    conv_lhs => rw [eq]
    rw [show tailEval (block++gs.drop k) (wires x) = tailEval (gs.drop k) (tailEval block (wires x))
      by simp only [tailEval,List.foldl_append]]
    apply stable
    rw [runLen,blen]; simp [wires,k]; omega
  have arity (g : Gate) (hg : g ∈ block) : g.inputs.length≤2 := (fan g (List.mem_of_mem_take hg)).2
  obtain ⟨T,size,dep⟩ := smallSupport block j wires 10 (fun x => by simp [wires]) arity
  let S := Finset.univ.filter (fun i : Fin 10 => i.val ∈ T)
  have small : S.card ≤ T.card := by
    have sub : S.image Fin.val ⊆ T := by
      intro t ht; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht; exact (Finset.mem_filter.mp hi).2
    simpa [Finset.card_image_of_injective _ Fin.val_injective] using Finset.card_le_card sub
  have bound : S.card ≤ k+1 := by rw [← blen]; exact small.trans size
  have eq (x y : Fin 9 → Bool) (h : ∀ i ∈ S, signals x i = signals y i) : W x = W y := by
    rw [val,val]
    apply dep x y
    intro t ht
    by_cases lt : t<10
    · let i : Fin 10 := ⟨t,lt⟩
      exact (signals_read x i).trans ((h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)).trans (signals_read y i).symm)
    · rw [List.getD_eq_default _ _ (by simp [wires];omega),List.getD_eq_default _ _ (by simp [wires];omega)]
  obtain ⟨form,hW⟩ := majorant_support W S (by omega) eq covers nontrivial
  have c : S.card=4 := by rcases form with t|t <;> rw [t] <;> decide
  refine ⟨by dsimp [k] at bound; omega,?_⟩
  rcases form with t|t
  · exact Or.inl (t ▸ hW)
  · exact Or.inr (t ▸ hW)

end Petersen3136

namespace Petersen3136

def missingWitness (a b : Fin 9) (i : Fin 9) : Bool :=
  Nat.testBit (([10, 104, 10, 0, 10, 138, 10, 40, 10, 104, 1, 9, 5, 1, 1, 257, 4, 9, 10, 9, 2, 385, 8, 9, 2, 34, 8, 0, 5, 385, 5, 5, 5, 257, 5, 69, 10, 1, 8, 5, 1, 1, 10, 5, 8, 138, 1, 9, 5, 1, 1, 130, 5, 9, 10, 257, 2, 257, 10, 130, 2, 34, 10, 40, 4, 34, 5, 5, 5, 34, 4, 32, 10, 9, 8, 69, 8, 9, 10, 32, 8] : List ℕ).getD (9*a.val+b.val) 0) i.val

def activate (x : Fin 9 → Bool) (a i : Fin 9) : Bool := if i=a then true else x i

def exceptional (a b : Fin 9) : Prop := (a=0 ∧ b=3) ∨ (a=3 ∧ b=0)
instance (a b : Fin 9) : Decidable (exceptional a b) := by unfold exceptional; infer_instance

private theorem witnesses : ∀ (a b : Fin 9), ¬ exceptional a b →
    let x := missingWitness a b
    F x=false ∧ F (activate x a)=true ∧ F (activate x b)=true ∧
    signals (activate x a) 9=signals x 9 ∧ signals (activate x b) 9=signals x 9 := by
  decide +kernel

def depends (P : (Fin 9 → Bool) → Bool) (S : Finset (Fin 10)) : Prop :=
  ∀ x y, (∀ i ∈ S, signals x i=signals y i) → P x=P y

private theorem activate_agrees (x : Fin 9 → Bool) (a : Fin 9) (S : Finset (Fin 10))
    (ha : a.castSucc ∉ S) (sticky : 9 ∈ S → signals (activate x a) 9=signals x 9) :
    ∀ i ∈ S, signals (activate x a) i = signals x i := by
  intro i hi
  by_cases h : i.val<9
  · let t : Fin 9 := ⟨i.val,h⟩
    have ne : t≠a := by
      intro eq
      have hcast : t.castSucc=i := Fin.ext rfl
      exact ha (eq ▸ hcast.symm ▸ hi)
    simpa [signals,h,activate,t] using (ite_eq_right ne : (if t=a then true else x t)=x t)
  · have nine : i=9 := Fin.ext (by have := i.isLt; omega)
    subst i; exact sticky hi

theorem omitted_pair (P Q : (Fin 9 → Bool) → Bool) (S T : Finset (Fin 10))
    (dp : depends P S) (dq : depends Q T) (split : ∀ x, (P x && Q x)=F x)
    (a b : Fin 9) (ha : a.castSucc ∉ S) (hb : b.castSucc ∉ T) : exceptional a b := by
  by_contra ne
  let x := missingWitness a b
  obtain ⟨no,yesA,yesB,sA,sB⟩ := witnesses a b ne
  have A := (Bool.and_eq_true_iff.mp ((split (activate x a)).trans yesA)).1
  have B := (Bool.and_eq_true_iff.mp ((split (activate x b)).trans yesB)).2
  have vA : P (activate x a)=P x := dp _ _ (activate_agrees x a S ha (fun _ => sA))
  have vB : Q (activate x b)=Q x := dq _ _ (activate_agrees x b T hb (fun _ => sB))
  change F x=false at no
  have yes : F x=true := (split x).symm.trans (Bool.and_eq_true_iff.mpr ⟨vA ▸ A,vB ▸ B⟩)
  exact Bool.false_ne_true (no.symm.trans yes)

theorem needs_free_signal (P Q : (Fin 9 → Bool) → Bool) (S T : Finset (Fin 10))
    (dp : depends P S) (dq : depends Q T) (split : ∀ x, (P x && Q x)=F x)
    (a b : Fin 9) (ha : a.castSucc ∉ S) (hb : b.castSucc ∉ T) : 9 ∈ S ∨ 9 ∈ T := by
  by_contra! miss
  let x : Fin 9 → Bool := fun i => decide (i=4)
  have exc := omitted_pair P Q S T dp dq split a b ha hb
  have yesA : F (activate x a)=true := by rcases exc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have yesB : F (activate x b)=true := by rcases exc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have A := (Bool.and_eq_true_iff.mp ((split (activate x a)).trans yesA)).1
  have B := (Bool.and_eq_true_iff.mp ((split (activate x b)).trans yesB)).2
  have vA := dp _ _ (activate_agrees x a S ha (fun h => False.elim (miss.1 h)))
  have vB := dq _ _ (activate_agrees x b T hb (fun h => False.elim (miss.2 h)))
  have yes : F x=true := (split x).symm.trans (Bool.and_eq_true_iff.mpr ⟨vA ▸ A,vB ▸ B⟩)
  exact (by decide : F x=false).symm.trans yes |> Bool.false_ne_true

end Petersen3136

namespace Petersen3136

theorem companion_reads_all (P Q : (Fin 9 → Bool) → Bool) (S T : Finset (Fin 10))
    (dp : depends P S) (dq : depends Q T) (split : ∀ x, (P x && Q x)=F x)
    (miss : (4 : Fin 10) ∉ S) (i : Fin 9) : i.castSucc ∈ T := by
  by_contra hi
  have ex := omitted_pair P Q S T dp dq split 4 i miss hi
  rcases ex with ⟨h,_⟩|⟨h,_⟩ <;> contradiction

theorem partner_of_early (P Q : (Fin 9 → Bool) → Bool) (T : Finset (Fin 10))
    (dp : depends P K₁ ∨ depends P K₂) (dq : depends Q T)
    (split : ∀ x, (P x && Q x)=F x) (i : Fin 9) : i.castSucc ∈ T := by
  rcases dp with dp|dp
  · exact companion_reads_all P Q K₁ T dp dq split (by decide) i
  · exact companion_reads_all P Q K₂ T dp dq split (by decide) i

end Petersen3136

namespace Petersen3136

def prefixMasks : List (ℕ × ℕ) := [(130, 386), (130, 139), (130, 265), (258, 386), (258, 267), (258, 137), (11, 139), (11, 267), (11, 384), (384, 386), (384, 393), (137, 139), (137, 393), (265, 267), (265, 393)]

def prefixOr (m : ℕ) (x : Fin 9 → Bool) : Bool :=
  (List.finRange 9).any fun i => m.testBit i.val && x i

private def prefixWitness (tree : Fin 15) (i j : Fin 9) : Bool :=
  Nat.testBit (([10, 129, 2, 5, 1, 1, 2, 34, 10, 10, 129, 2, 5, 1, 1, 2, 34, 8, 10, 129, 2, 5, 1, 1, 2, 34, 8, 10, 257, 2, 5, 1, 1, 2, 34, 10, 10, 257, 2, 5, 1, 1, 2, 5, 10, 10, 257, 2, 5, 1, 1, 2, 5, 10, 10, 1, 2, 5, 1, 1, 2, 5, 8, 10, 1, 2, 5, 1, 1, 2, 5, 8, 10, 1, 2, 5, 1, 1, 2, 260, 136, 10, 129, 2, 5, 1, 1, 2, 260, 136, 10, 1, 2, 5, 1, 1, 2, 260, 136, 10, 1, 2, 5, 1, 1, 2, 5, 8, 10, 1, 2, 5, 1, 1, 2, 5, 8, 10, 1, 2, 5, 1, 1, 2, 5, 8, 10, 1, 2, 5, 1, 1, 2, 5, 8] : List ℕ).getD (9*tree.val+i.val) 0) j.val

/-- For each canonical three-gate OR tree for K₁, the i-th coordinate has a
strictly increasing witness with every available prefix gate fixed. -/
theorem direct_raw_needed (tree : Fin 15) (i : Fin 9) :
    ∃ x : Fin 9 → Bool, let y := activate x i
      let masks := prefixMasks.getD tree.val (0,0)
      F x=false ∧ F y=true ∧ prefixOr 395 x=true ∧ prefixOr 395 y=true ∧
      prefixOr 9 x=prefixOr 9 y ∧ prefixOr masks.1 x=prefixOr masks.1 y ∧
        prefixOr masks.2 x=prefixOr masks.2 y := by
  refine ⟨prefixWitness tree i, ?_⟩
  revert tree i
  decide +kernel

end Petersen3136
