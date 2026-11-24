import TrackedTiles
import PlaneStarFormula
import TightOwner

namespace PlaneStarFormula

open PlaneRankSamples PlaneLeafProtocol

/-- At the optimal leaf count, each incidence has an endpoint that occurs
at most once in the entire tree. -/
theorem edgeReadOnce {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2≤q) (hN : N=q^2+q+1)
    (rows : ∀ p, (Finset.univ.filter (I p)).card=q+1)
    (cols : ∀ l, (Finset.univ.filter (fun p => I p l)).card=q+1)
    (T : PlaneFormula.Tree (Fin (N+N))) (yes : ∀ e : Edge I, T.eval (raw (pos I e))=true)
    (no : ∀ f : Edge I, T.eval (raw (neg I f))=false) (budget : T.leaves ≤ N*(q+1)+N)
    (e : Edge I) : ∃ v, raw (pos I e) v=true ∧ T.occurs v≤1 := by
  classical
  let _ : Nonempty (Fin (N+N)) := ⟨⟨0,by omega⟩⟩
  obtain ⟨a,counts,valid,weights⟩ := tracked (fun e => raw (pos I e)) (fun f => raw (neg I f))
    T Set.univ Set.univ (fun e _ => yes e) (fun f _ => no f)
  have winners (e f : Edge I) : ∃! i, e∈a.row i ∧ f∈a.col i :=
    oneWinner a e f (by simpa using weights e f)
  choose win winMem winUniq using winners
  let C : Tiles (Vertex N) (Edge I) T.leaves := ⟨fun i => vertex (a.color i),a.row,a.col⟩
  let own := fun e => C.color (win e e)
  have belongs (e : Edge I) : e∈star I (own e) :=
    (inStar I e _).mpr (valid.1 _ e (winMem e e).1)
  have shared (v : Vertex N) (e f : Edge I) (he : e∈star I v) (hf : f∈star I v)
      (diff : e≠f) : C.color (win e f)=v := by
    have ep := valid.1 _ e (winMem e f).1
    have fn := valid.2 _ f (winMem e f).2
    have fp := (separated I e f _ ep fn).mp (same I he hf)
    exact uniqueVertex I diff ((inStar I e _).mpr ep) ((inStar I f _).mpr fp) he hf
  have bounds := PlaneStarFactors.localBound C (star I) win
    (fun e f i => ⟨winUniq e f i,fun h => h ▸ winMem e f⟩) belongs shared
    (starDegree I rows cols) (by omega)
  have countOne := PetersenStarCount.tightOwner N (q+1) own C.color (star I)
    (starDegree I rows cols) belongs (by simp [Vertex]; omega) (edgeCard I rows)
    (by omega) bounds (by simpa using budget) e
  let v := a.color (win e e)
  refine ⟨v,valid.1 _ e (winMem e e).1,(counts v).trans ?_⟩
  rw [tally,←Finset.card_filter,←countOne]
  apply Finset.card_le_card
  intro k hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg vertex (Finset.mem_filter.mp hk).2⟩

end PlaneStarFormula
