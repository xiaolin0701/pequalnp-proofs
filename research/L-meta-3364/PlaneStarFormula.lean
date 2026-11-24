import StarFactors
import RankSamples

namespace PlaneStarFormula

open PlaneRankSamples PlaneLeafProtocol

abbrev Vertex (N : ℕ) := Fin N ⊕ Fin N

def vertex {N : ℕ} (i : Fin (N+N)) : Vertex N := Fin.addCases Sum.inl Sum.inr i

def star {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Vertex N → Finset (Edge I)
  | .inl p => Finset.univ.filter (fun e => e.val.1=p)
  | .inr l => Finset.univ.filter (fun e => e.val.2=l)

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

theorem inStar (e : Edge I) (v : Fin (N+N)) :
    e∈star I (vertex v) ↔ raw (pos I e) v=true := by
  induction v using Fin.addCases <;>
    simp only [vertex,Fin.addCases_left,Fin.addCases_right,star,Finset.mem_filter,
      Finset.mem_univ,true_and,raw,pos,decide_eq_true_eq] <;> exact eq_comm

theorem same {v : Vertex N} {e f : Edge I} (he : e∈star I v) (hf : f∈star I v) :
    e.val.1=f.val.1 ∨ e.val.2=f.val.2 := by
  cases v <;> simp [star] at he hf <;> first | exact Or.inl (he.trans hf.symm) | exact Or.inr (he.trans hf.symm)

theorem uniqueVertex {v w : Vertex N} {e f : Edge I} (ne : e≠f) (ev : e∈star I v)
    (fv : f∈star I v) (ew : e∈star I w) (fw : f∈star I w) : v=w := by
  cases v <;> cases w <;> simp [star] at * <;>
    first | exact ev.symm.trans ew | exact False.elim (ne (Subtype.ext (Prod.ext (ev.trans fv.symm) (ew.trans fw.symm))))
          | exact False.elim (ne (Subtype.ext (Prod.ext (ew.trans fw.symm) (ev.trans fv.symm))))

theorem starDegree {d : ℕ} (rows : ∀ p, (Finset.univ.filter (I p)).card=d)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card=d) (v : Vertex N) :
    (star I v).card=d := by
  classical
  rw [← Fintype.card_coe]
  cases v with
  | inl p =>
    let iso : ↥(star I (.inl p)) ≃ {l // I p l} :=
      { toFun := fun e => ⟨e.val.val.2, by
          have coord : e.val.val.1=p := by simpa [star] using e.property
          exact (congrArg (fun i => I i e.val.val.2) coord).mp e.val.property⟩
        invFun := fun l => ⟨⟨(p,l.val),l.property⟩,by simp [star]⟩
        left_inv := fun e => Subtype.ext (Subtype.ext (Prod.ext
          (Eq.symm (by simpa [star] using e.property : e.val.val.1=p)) rfl))
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr iso,Fintype.card_subtype,rows]
  | inr l =>
    let iso : ↥(star I (.inr l)) ≃ {p // I p l} :=
      { toFun := fun e => ⟨e.val.val.1, by
          have coord : e.val.val.2=l := by simpa [star] using e.property
          exact (congrArg (fun i => I e.val.val.1 i) coord).mp e.val.property⟩
        invFun := fun p => ⟨⟨(p.val,l),p.property⟩,by simp [star]⟩
        left_inv := fun e => Subtype.ext (Subtype.ext (Prod.ext rfl
          (Eq.symm (by simpa [star] using e.property : e.val.val.2=l))))
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr iso,Fintype.card_subtype,cols]

theorem leaves {q : ℕ} (hq : 2≤q) (hN : N=q^2+q+1)
    (rows : ∀ p, (Finset.univ.filter (I p)).card=q+1)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (T : PlaneFormula.Tree (Fin (N+N))) (yes : ∀ e : Edge I, T.eval (raw (pos I e))=true)
    (no : ∀ f : Edge I, T.eval (raw (neg I f))=false) : N*(q+1)+N ≤ T.leaves := by
  classical
  have npos : 0 < N := by omega
  let : Nonempty (Fin (N+N)) := ⟨⟨0,by omega⟩⟩
  obtain ⟨a,valid,weights⟩ := tiles (fun e => raw (pos I e)) (fun f => raw (neg I f)) T
    Set.univ Set.univ (fun e _ => yes e) (fun f _ => no f)
  have winners (e f : Edge I) : ∃! i, e∈a.row i ∧ f∈a.col i :=
    oneWinner a e f (by simpa using weights e f)
  choose win winMem winUniq using winners
  let colored : Tiles (Vertex N) (Edge I) T.leaves := ⟨fun i => vertex (a.color i),a.row,a.col⟩
  apply PlaneStarFactors.count colored (star I) win
    (fun e f i => ⟨winUniq e f i,fun h => h ▸ winMem e f⟩) _ _ (starDegree I rows cols)
    (by simp [Vertex]; omega) (edgeCard I rows) (by omega)
  · intro e
    exact (inStar I e _).mpr (valid.1 _ e (winMem e e).1)
  · intro v e f he hf diff
    have ep := valid.1 _ e (winMem e f).1
    have fn := valid.2 _ f (winMem e f).2
    have fp := (separated I e f _ ep fn).mp (same I he hf)
    exact uniqueVertex I diff ((inStar I e _).mpr ep) ((inStar I f _).mpr fp) he hf

end PlaneStarFormula
