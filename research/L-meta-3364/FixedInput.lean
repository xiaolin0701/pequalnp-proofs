import FirstGate
import OutputBudget

namespace PlaneFixedInput

open PlaneSignalCompression PlaneUnfold PlaneFirstGate

def cut {Z : Type} (W : ℕ → Set Z) (a i : ℕ) : Set {z // z ∉ W a} :=
  Subtype.val ⁻¹' W i

@[simp] theorem cut_self {Z : Type} (W : ℕ → Set Z) (a : ℕ) : cut W a a=∅ := by
  ext z
  exact iff_false_intro z.property

theorem cutLaw {Z : Type} {n m : ℕ} (W : ℕ → Set Z) (ops : PlaneUnfold.Steps n)
    (law : realizes W m ops) (a : ℕ) : realizes (cut W a) m ops := by
  intro i hi
  have h := congrArg (fun A : Set Z => (Subtype.val : {z // z∉W a} → Z) ⁻¹' A) (law i hi)
  cases e : ops i <;> simpa [cut,e,Op.onSets] using h

theorem toSteps {Z : Type} {n m : ℕ} (hn : 0 < n) (W : ℕ → Set Z)
    (ops : PlaneUnfold.Steps n) (law : realizes W m ops) : PlaneSignalCompression.Steps n m W := by
  intro i hi
  have h := law i hi
  cases e : ops i with
  | empty => exact ⟨0,by omega,0,by omega,Or.inr (Or.inr (Or.inl (by simpa [e,Op.onSets] using h)))⟩
  | copy t => exact ⟨t.val,t.isLt,t.val,t.isLt,Or.inr (Or.inl (by simpa [e,Op.onSets] using h))⟩
  | join t u => exact ⟨t.val,t.isLt,u.val,u.isLt,Or.inl (by simpa [e,Op.onSets] using h)⟩
  | meet t u => exact ⟨t.val,t.isLt,u.val,u.isLt,Or.inr (Or.inr (Or.inr (by simpa [e,Op.onSets] using h)))⟩

theorem readNotFresh {Z : Type} {n m a i : ℕ} (W : ℕ → Set Z)
    (ops : PlaneUnfold.Steps n) (law : realizes W m ops)
    (hi : i < m) (read : reads (ops i) a) : ¬ Fresh (cut W a) (n+i) := by
  intro fresh
  have h := cutLaw W ops law a i hi
  cases e : ops i with
  | empty => simp [e,reads] at read
  | copy t =>
    exact fresh.2 t.val t.isLt (by simpa [e,Op.onSets] using h)
  | join t u =>
    have choice : a=t.val ∨ a=u.val := by simpa [e,reads] using read
    rcases choice with eq|eq
    · exact fresh.2 u.val u.isLt (by simpa [e,Op.onSets,←eq] using h)
    · exact fresh.2 t.val t.isLt (by simpa [e,Op.onSets,←eq] using h)
  | meet t u =>
    have choice : a=t.val ∨ a=u.val := by simpa [e,reads] using read
    rcases choice with eq|eq <;> exact fresh.1 (by simpa [e,Op.onSets,←eq] using h)

def PinReady {Z : Type} (n o : ℕ) (W : ℕ → Set Z) (a : ℕ) : Prop :=
  ∃ U : ℕ → Set {z // z∉W a},
    (∀ i < n, cut W a i=∅ ∨ ∃ j < n-1, cut W a i=U j) ∧ (cut W a o).Nonempty ∧
    ∀ (V : ℕ → Set {z // z∉W a}) t, (∀ j < n-1, V j=U j) → cut W a o=V t →
      PlanePrivate.Exchange (n-1) t V

theorem compactBound {Z : Type} {r n m o : ℕ} (hr : 2≤r) (W U : ℕ → Set Z)
    (inputs : ∀ i < n, W i=∅ ∨ ∃ j < r, W i=U j) (steps : PlaneSignalCompression.Steps n m W)
    (ho : o < n+m) (on : (W o).Nonempty)
    (transfer : ∀ (V : ℕ → Set Z) t, (∀ j < r, V j=U j) → W o=V t → PlanePrivate.Exchange r t V) :
    3*r ≤ 2*(kept n m W).card+2 := by
  obtain ⟨V,raw,run,covered⟩ := compact W U inputs steps
  obtain ⟨t,ht,eq⟩ := (covered o ho).resolve_left on.ne_empty
  exact PlaneOutputBudget.exchangeBound hr V run ht (transfer V t raw eq)

theorem sharpen {Z : Type} {n m o : ℕ} (hn : 3≤n) (W : ℕ → Set Z)
    (steps : PlaneSignalCompression.Steps n m W) (ho : o < n+m) (ex : PlanePrivate.Exchange n o W)
    (pin : ∀ a < n, PinReady n o W a) : 3*n ≤ 2*m+1 := by
  classical
  obtain ⟨x,hx,y,hy,_,_,_⟩ := ex 0 (by omega) 1 (by omega) (by decide)
  have positive : 0 < m := by
    by_contra! zero
    have raw : o < n := by omega
    obtain ⟨j,hj,ne⟩ : ∃ j < n, j≠o :=
      if eq : o=0 then ⟨1,by omega,by omega⟩ else ⟨0,by omega,by omega⟩
    obtain ⟨z,hz,_,_,off,_,_⟩ := ex j hj o raw ne
    exact off hz
  obtain ⟨ops,law⟩ := PlaneUnfold.chooseSteps W steps
  by_cases first : Fresh W n
  · obtain ⟨a,ha,i,hi,pos,base,again⟩ := repeatedRead (by omega) W ops law ho ex first
    obtain ⟨U,raw,on,carry⟩ := pin a ha
    have count := compactBound (r:=n-1) (by omega) (cut W a) U raw
      (toSteps (by omega) _ ops (cutLaw W ops law a)) ho on carry
    have savings := dropTwo (n:=n) (m:=m) (a:=0) (b:=i) (cut W a) positive hi (by omega)
      (by simpa using readNotFresh W ops law positive base) (readNotFresh W ops law hi again)
    omega
  · have count := compactBound (r:=n) (by omega) W W (fun i hi => Or.inr ⟨i,hi,rfl⟩)
        steps ho ⟨x,hx⟩ (by
          intro V t raw eq a ha b hb ne
          obtain ⟨p,hp,q,hq,off,on,stable⟩ := ex a ha b hb ne
          exact ⟨p,eq ▸ hp,q,eq ▸ hq,(raw b hb).symm ▸ off,(raw b hb).symm ▸ on,
            fun u hu ne => (raw u hu).symm ▸ stable u hu ne⟩)
    have sub : insert 0 (kept n m W) ⊆ Finset.range m := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl|ht
      · exact Finset.mem_range.mpr positive
      · exact (Finset.mem_filter.mp ht).1
    have hcard : (kept n m W).card+1 ≤ m := by
      have hzero : 0∉kept n m W := by simp [kept,first]
      simpa [Finset.card_insert_of_notMem hzero] using Finset.card_le_card sub
    omega

end PlaneFixedInput
