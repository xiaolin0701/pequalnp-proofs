import PEqualNP.Defs.EdgeOwnership
import PEqualNP.Defs.NestedCoverCircuit
import Mathlib.Data.Finset.Max

namespace Meta2262

def edges : List (ℕ × ℕ) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

abbrev G := PEqualNP.EdgeOwnership.edgeGraph 11 edges

def pairs : List (Fin 11 × Fin 11) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def missing (T : Finset (Fin 11)) : Finset (Sym2 (Fin 11)) :=
  ((pairs.filter fun e => e.1 ∉ T ∧ e.2 ∉ T).map fun e => s(e.1,e.2)).toFinset

def profile (k : ℕ) : ℕ := [16,12,8,5,3,2,1].getD k 0

private def vertices : List (Fin 11) := [0,1,2,3,4,5,6,7,8,9,10]

private theorem count_through_map {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length = ((l.map p).filter id).length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases hp : p a <;> simp [hp, ih]

private theorem boolean_profile : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Bool,
    profile ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10].filter id).length ≤
      ([(!x0 && !x9),(!x0 && !x10),(!x1 && !x4),(!x1 && !x8),
        (!x2 && !x5),(!x2 && !x10),(!x3 && !x6),(!x3 && !x7),
        (!x4 && !x8),(!x4 && !x10),(!x5 && !x8),(!x5 && !x9),
        (!x6 && !x7),(!x6 && !x10),(!x7 && !x9),(!x8 && !x9)].filter id).length := by
  set_option maxRecDepth 10000 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem profile_bound (T : Finset (Fin 11)) : profile T.card ≤ (missing T).card := by
  have hv : ∀ i : Fin 11, i ∈ vertices := by decide
  have heq : ((vertices.filter fun i => decide (i ∈ T)).toFinset) = T := by
    ext i
    simp [hv i]
  have hverts : vertices.Nodup := by decide
  have hpair : (pairs.map fun e => s(e.1,e.2)).Nodup := by decide
  have hsub := (List.filter_sublist
    (p := fun e : Fin 11 × Fin 11 => decide (e.1 ∉ T ∧ e.2 ∉ T)) (l := pairs)).map
      (fun e => s(e.1,e.2))
  have hcard : T.card = (vertices.filter fun i => decide (i ∈ T)).length := by
    calc
      T.card = (vertices.filter fun i => decide (i ∈ T)).toFinset.card := congrArg Finset.card heq.symm
      _ = _ := List.toFinset_card_of_nodup (hverts.filter _)
  have hsize : (missing T).card = (pairs.filter fun e => decide (e.1 ∉ T ∧ e.2 ∉ T)).length := by
    rw [missing, List.toFinset_card_of_nodup (hsub.nodup hpair), List.length_map]
  rw [hcard, hsize, count_through_map, count_through_map pairs]
  simpa only [vertices, pairs, List.map_cons, List.map_nil, Bool.decide_and, decide_not] using
    boolean_profile (decide (0 ∈ T)) (decide (1 ∈ T)) (decide (2 ∈ T)) (decide (3 ∈ T)) (decide (4 ∈ T))
      (decide (5 ∈ T)) (decide (6 ∈ T)) (decide (7 ∈ T)) (decide (8 ∈ T)) (decide (9 ∈ T)) (decide (10 ∈ T))

private def minimizers : List (Finset (Fin 11)) :=
  [∅,
   {8},
   {8,10},
   {7,8,10},
   {3,8,9,10},
   {0,5,7,8,10},
   {0,1,5,7,8,10},
   {0,1,3,5,7,8,10},
   {0,1,2,3,4,5,6,9},
   {0,1,2,3,4,5,6,7,8},
   {0,1,2,3,4,5,6,7,8,9},
   {0,1,2,3,4,5,6,7,8,9,10}]

theorem profile_attained (k : Fin 12) :
    ∃ T : Finset (Fin 11), T.card = k.val ∧ (missing T).card = profile k.val := by
  have h : ∀ i : Fin 12, (minimizers.getD i.val ∅).card = i.val ∧
      (missing (minimizers.getD i.val ∅)).card = profile i.val := by decide +kernel
  exact ⟨_, h k⟩

theorem mem_missing_iff (T : Finset (Fin 11)) (v w : Fin 11) :
    s(v,w) ∈ missing T ↔ G.Adj v w ∧ v ∉ T ∧ w ∉ T := by
  have hs : ∀ a b, G.Adj a b ↔ (a,b) ∈ pairs ∨ (b,a) ∈ pairs := by decide +kernel
  simp only [missing, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a,b⟩, ⟨hp, ha, hb⟩, heq⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨(hs _ _).mpr (Or.inl hp), ha, hb⟩
    · exact ⟨(hs _ _).mpr (Or.inr hp), hb, ha⟩
  · rintro ⟨hadj, hv, hw⟩
    rcases (hs v w).mp hadj with hp | hp
    · exact ⟨(v,w), ⟨hp,hv,hw⟩, rfl⟩
    · exact ⟨(w,v), ⟨hp,hw,hv⟩, Sym2.eq_swap⟩

theorem missing_subset (U : Finset (Sym2 (Fin 11))) (T : Finset (Fin 11))
    (hcover : (G.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (T : Set (Fin 11))) :
    missing T ⊆ U := by
  intro e he
  simp only [missing, List.mem_toFinset, List.mem_map, List.mem_filter] at he
  obtain ⟨p, ⟨hp, hmiss⟩, rfl⟩ := he
  have hpAdj : ∀ q ∈ pairs, G.Adj q.1 q.2 := by decide +kernel
  by_contra hu
  have hadj : (G.deleteEdges (U : Set (Sym2 (Fin 11)))).Adj p.1 p.2 :=
    SimpleGraph.deleteEdges_adj.mpr ⟨hpAdj p hp, hu⟩
  have hh := hcover hadj
  simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at hmiss
  exact hh.elim hmiss.1 hmiss.2

theorem minCover_exists {n : ℕ} (H : SimpleGraph (Fin n)) :
    ∃ T, PEqualNP.MetaComplexity.NestedCover.IsMinCover H T := by
  classical
  let S := Finset.univ.filter fun T : Finset (Fin n) => H.IsVertexCover (T : Set (Fin n))
  have hs : ∀ {T : Finset (Fin n)}, T ∈ S ↔ H.IsVertexCover (T : Set (Fin n)) := by
    intro T
    simp [S]
  have hall : Finset.univ ∈ S := hs.mpr (by simp)
  obtain ⟨T, hT, hmin⟩ := S.exists_min_image Finset.card ⟨_, hall⟩
  exact ⟨T, hs.mp hT, fun T' hT' => hmin T' (hs.mpr hT')⟩

theorem profile_le_deleted (U : Finset (Sym2 (Fin 11))) (T : Finset (Fin 11))
    (hcover : (G.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (T : Set (Fin 11))) :
    profile T.card ≤ U.card :=
  (profile_bound T).trans
    (Finset.card_le_card (missing_subset U T hcover))

/-- This is the arithmetic part of the posted 2262 branch, with the
gate classification appearing only through its four cardinalities. -/
theorem small_Ustar (U : Finset (Sym2 (Fin 11))) (t z o size : ℕ)
    (hc : ∀ T, PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) T →
      T.card ≤ t)
    (hcount : 17 + t + 2*z + o ≤ size + U.card) (hu : U.card ≤ 1) :
    24 ≤ size + 2*U.card := by
  obtain ⟨T, hT⟩ := minCover_exists (G.deleteEdges ↑U)
  have hp := profile_le_deleted U T hT.1
  have ht := hc T hT
  have hsum : 7 ≤ T.card + U.card := by
    by_contra h
    have hcard : T.card ≤ 6 := by omega
    have hfinite : ∀ k : Fin 7, ∀ u : Fin 2, profile k.val ≤ u.val → 7 ≤ k.val + u.val := by decide
    exact h (hfinite ⟨T.card, by omega⟩ ⟨U.card, by omega⟩ hp)
  omega

theorem two_Ustar (U : Finset (Sym2 (Fin 11))) (t z o size : ℕ)
    (hc : ∀ T, PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) T →
      T.card ≤ t)
    (hcount : 17 + t + 2*z + o ≤ size + U.card) (hu : U.card = 2)
    (hsize : size ≤ 21) : z = 0 ∧ o ≤ 1 ∧ (o = 1 → t = 5) := by
  obtain ⟨T, hT⟩ := minCover_exists (G.deleteEdges ↑U)
  have hp := profile_le_deleted U T hT.1
  have ht := hc T hT
  have h5 : 5 ≤ T.card := by
    by_contra h
    have hcard : T.card ≤ 4 := by omega
    have hfinite : ∀ k : Fin 5, ¬ profile k.val ≤ 2 := by decide
    exact hfinite ⟨T.card, by omega⟩ (hu ▸ hp)
  omega

open PEqualNP.EdgeOwnership PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem cover_child : ∀ (G : SimpleGraph (Fin 11)) (U : Finset (Sym2 (Fin 11))) (t : ℕ),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] → U.card ≤ 2 →
      (∀ T, IsMinCover (G.deleteEdges ↑U) T → T.card ≤ t) → 7 ≤ t + U.card := by
  intro G U t hG hu hc
  subst G
  obtain ⟨T,hT⟩ := Meta2262.minCover_exists (Meta2262.G.deleteEdges ↑U)
  have ht := hc T hT
  have hp := Meta2262.profile_le_deleted U T hT.1
  by_contra h
  have hfinite : ∀ k : Fin 7, ∀ u : Fin 3, Meta2262.profile k.val ≤ u.val → 7 ≤ k.val + u.val := by decide
  have hh := hfinite ⟨T.card, by omega⟩ ⟨U.card, by omega⟩ hp
  change 7 ≤ T.card + U.card at hh
  omega

end Meta2262
