import PEqualNP.Defs

namespace Petersen2373.Stars

section Gates

variable {α : Type*} [DecidableEq α]

/-- Reverse topological order. An input or the empty disjunction is freely available. -/
def Available (gs : List (Finset α)) (w : Finset α) :=
  w.card ≤ 1 ∨ w ∈ gs

/-- Each entry is the support of a binary OR of two earlier wires. Wires may be
used arbitrarily often, and their supports may intersect or coincide. -/
def OrDAG : List (Finset α) → Prop
  | [] => True
  | w :: gs => (∃ a b, Available gs a ∧ Available gs b ∧ w = a ∪ b) ∧ OrDAG gs

def countFor (N : Finset α) (gs : List (Finset α)) : ℕ :=
  gs.countP fun w => decide (1 < w.card ∧ w ⊆ N)

/-- With r distinct requested outputs, exposing d distinct leaves in a
neighborhood takes at least d-r binary OR gates supported inside it. -/
theorem leaves_le (N : Finset α) (gs : List (Finset α)) (built : OrDAG gs)
    (O : Finset (Finset α)) (inside : ∀ w ∈ O, w ⊆ N)
    (avail : ∀ w ∈ O, Available gs w) :
    (O.biUnion id).card ≤ O.card + countFor N gs := by
  classical
  induction gs generalizing O with
  | nil =>
    have h := Finset.card_biUnion_le (s := O) (t := id)
    have small (w) (hw : w ∈ O) : (id w).card ≤ 1 := by
      simpa [Available] using avail w hw
    have h' := Finset.sum_le_sum small
    simpa [countFor] using h.trans h'
  | cons w gs ih =>
    obtain ⟨⟨a, b, ha, hb, e⟩, built'⟩ := built
    by_cases must : w ∈ O ∧ 1 < w.card
    · obtain ⟨hw, big⟩ := must
      let P := insert a (insert b (O.erase w))
      have both : a ⊆ w ∧ b ⊆ w := by rw [e]; exact ⟨Finset.subset_union_left, Finset.subset_union_right⟩
      have pin : ∀ t ∈ P, t ⊆ N := by
        intro t ht
        simp only [P, Finset.mem_insert, Finset.mem_erase] at ht
        rcases ht with rfl | rfl | ⟨_, ht⟩
        · exact both.1.trans (inside _ hw)
        · exact both.2.trans (inside _ hw)
        · exact inside _ ht
      have pav : ∀ t ∈ P, Available gs t := by
        intro t ht
        simp only [P, Finset.mem_insert, Finset.mem_erase] at ht
        rcases ht with rfl | rfl | ⟨hne, ht⟩
        · exact ha
        · exact hb
        · simpa [Available, hne] using avail t ht
      have uni : O.biUnion id ⊆ P.biUnion id := by
        intro v hv
        obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hv
        by_cases teq : t = w
        · subst t
          change v ∈ w at hvt
          rw [e, Finset.mem_union] at hvt
          rcases hvt with va | vb
          · exact Finset.mem_biUnion.mpr ⟨a, by simp [P], va⟩
          · exact Finset.mem_biUnion.mpr ⟨b, by simp [P], vb⟩
        · exact Finset.mem_biUnion.mpr ⟨t, by simp [P, ht, teq], hvt⟩
      have step := (Finset.card_le_card uni).trans (ih built' P pin pav)
      have ca := Finset.card_insert_le a (insert b (O.erase w))
      have cb := Finset.card_insert_le b (O.erase w)
      have ce := Finset.card_erase_add_one (s := O) hw
      have paid : countFor N (w::gs) = countFor N gs + 1 := by
        simp [countFor, big, inside w hw]
      dsimp [P] at step
      omega
    · have pav : ∀ t ∈ O, Available gs t := by
        intro t ht
        by_cases teq : t = w
        · subst t; exact Or.inl (by by_contra! h; exact must ⟨ht,h⟩)
        · simpa [Available, teq] using avail t ht
      have nondecreasing : countFor N gs ≤ countFor N (w::gs) := by
        simp [countFor, List.countP_cons]
      exact (ih built' O inside pav).trans (Nat.add_le_add_left nondecreasing _)

end Gates


abbrev Vertex := Fin 10
def edgeFrom (a b : Vertex) : Vertex × Vertex := (min a b,max a b)
def edges : Finset (Vertex × Vertex) :=
  {(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)}
def incident (a b : Vertex) : Bool := decide (edgeFrom a b ∈ edges)
def nbr (v : Vertex) : Finset Vertex := Finset.univ.filter fun w => incident v w
private theorem geom : (∀ c, (nbr c).card = 3) ∧
    ∀ c d, c ≠ d → ((nbr c) ∩ (nbr d)).card ≤ 1 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem vertexCover (s : Finset Vertex) (h : ∀ e ∈ edges, e.1 ∈ s ∨ e.2 ∈ s) :
    6 ≤ s.card := by
  revert s
  decide +kernel
private theorem allCharges (gs : List (Finset Vertex)) :
    (∑ c : Vertex, countFor (nbr c) gs) ≤ gs.length := by
  classical
  induction gs with
  | nil => simp [countFor]
  | cons w gs ih =>
    let eligible := fun c : Vertex => 1 < w.card ∧ w ⊆ nbr c
    have atMost : (Finset.univ.filter eligible).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro c hc d hd
      by_contra hne
      have cgood := (Finset.mem_filter.mp hc).2
      have dgood := (Finset.mem_filter.mp hd).2
      have lo := Finset.card_le_card (Finset.subset_inter cgood.2 dgood.2)
      have hi := geom.2 c d hne
      exact (Nat.not_lt_of_ge (lo.trans hi)) cgood.1
    have weight : (∑ c : Vertex, if eligible c then 1 else 0) ≤ 1 := by
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using atMost
    have step (c : Vertex) : countFor (nbr c) (w::gs) =
        countFor (nbr c) gs + (if eligible c then 1 else 0) := by
      by_cases h : eligible c <;> simp [countFor, List.countP_cons, eligible] at h ⊢
    simp_rw [step]
    rw [Finset.sum_add_distrib, List.length_cons]
    omega

theorem shared_star_profile
    (gs : List (Finset Vertex)) (built : OrDAG gs)
    (k : ℕ) (center : Fin k → Vertex) (leaf : Fin k → Finset Vertex)
    (subset : ∀ j, leaf j ⊆ nbr (center j))
    (available : ∀ j, Available gs (leaf j))
    (cover : edges ⊆ Finset.univ.biUnion (fun j => (leaf j).image (edgeFrom (center j)))) :
    15 ≤ gs.length + k ∧ 6 ≤ (Finset.univ.image center).card := by
  classical
  let group := fun c : Vertex => Finset.univ.filter (fun j : Fin k => center j = c)
  let outputs := fun c => (group c).image leaf
  let leaves := fun c => (outputs c).biUnion id
  have vertexLower : edges.card ≤ ∑ c : Vertex, (leaves c).card := by
    have coverage : edges ⊆ Finset.univ.biUnion (fun c => (leaves c).image (edgeFrom c)) := by
      intro e he
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (cover he)
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_biUnion.mpr
      refine ⟨center j, Finset.mem_univ _, Finset.mem_image.mpr ⟨a, ?_, rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨leaf j, Finset.mem_image.mpr ⟨j, by simp [group], rfl⟩, ha⟩
    exact (Finset.card_le_card coverage).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le))
  have bound (c) : (leaves c).card ≤ (group c).card + countFor (nbr c) gs := by
    apply (leaves_le (nbr c) gs built (outputs c) ?_ ?_).trans
      (Nat.add_le_add_right Finset.card_image_le _)
    · intro w hw
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      simpa [(Finset.mem_filter.mp hj).2] using subset j
    · intro w hw
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
      exact available j
  have groupCount : (∑ c : Vertex, (group c).card) = k := by
    simpa [group] using (Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ center)
  have bottom := vertexLower.trans (Finset.sum_le_sum fun c _ => bound c)
  rw [Finset.sum_add_distrib, groupCount] at bottom
  have total := allCharges gs
  have six := vertexCover (Finset.univ.image center) (by
    intro e he
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (cover he)
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hj
    have inC : center j ∈ Finset.univ.image center := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    rcases le_total (center j) b with h|h
    · exact Or.inl (by simpa [edgeFrom,min_eq_left h] using inC)
    · exact Or.inr (by simpa [edgeFrom,max_eq_left h] using inC))
  have ec : edges.card = 15 := by decide
  exact ⟨by omega,six⟩

theorem shared_star_lower
    (gs : List (Finset Vertex)) (built : OrDAG gs)
    (k : ℕ) (center : Fin k → Vertex) (leaf : Fin k → Finset Vertex)
    (subset : ∀ j, leaf j ⊆ nbr (center j))
    (available : ∀ j, Available gs (leaf j))
    (cover : edges ⊆ Finset.univ.biUnion (fun j => (leaf j).image (edgeFrom (center j)))) :
    20 ≤ gs.length + k + (k-1) := by
  obtain ⟨h,six⟩ := shared_star_profile gs built k center leaf subset available cover
  have bound : (Finset.univ.image center).card ≤ k := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := center))
  omega

def minimumCovers : List (Finset Vertex) :=
  [{0,1,3,7,8,9},{0,2,3,5,6,9},{0,2,4,6,7,8},{1,2,4,5,8,9},{1,3,4,5,6,7}]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem classify_covers : ∀ S : Finset Vertex, S.card = 6 →
    (∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S) → S ∈ minimumCovers := by decide +kernel

set_option maxRecDepth 10000 in
theorem cover_neighborhoods : minimumCovers.all (fun S => (List.finRange 10).all (fun v =>
    decide (v ∈ S → (nbr v ∩ S).card = 1 ∧ (nbr v \ S).card = 2))) = true := by decide +kernel

theorem optimal_star_centers (gs : List (Finset Vertex)) (built : OrDAG gs)
    (k : Nat) (center : Fin k → Vertex) (leaf : Fin k → Finset Vertex)
    (subset : ∀ j, leaf j ⊆ nbr (center j)) (available : ∀ j, Available gs (leaf j))
    (cover : edges ⊆ Finset.univ.biUnion (fun j => (leaf j).image (edgeFrom (center j))))
    (budget : gs.length + k + (k-1) ≤ 20) :
    k = 6 ∧ gs.length = 9 ∧ (Finset.univ.image center) ∈ minimumCovers := by
  obtain ⟨size,six⟩ := shared_star_profile gs built k center leaf subset available cover
  have bound : (Finset.univ.image center).card ≤ k := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := center))
  refine ⟨by omega,by omega,classify_covers _ (by omega) ?_⟩
  intro e he
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp (cover he)
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hj
  have hc : center j ∈ Finset.univ.image center := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rcases le_total (center j) b with h | h
  · exact Or.inl (by simpa [edgeFrom,min_eq_left h] using hc)
  · exact Or.inr (by simpa [edgeFrom,max_eq_left h] using hc)

private theorem incident_symm (a b : Vertex) : incident a b = incident b a := by
  revert a b; decide +kernel
private theorem edgeFrom_symm (a b : Vertex) : edgeFrom a b = edgeFrom b a := by
  simp [edgeFrom,min_comm,max_comm]
private theorem orient (A B : Finset Vertex)
    (valid : ∀ a ∈ A, ∀ b ∈ B, incident a b = true) :
    ∃ c : Vertex, ∃ L : Finset Vertex, (L = ∅ ∨ L = A ∨ L = B) ∧ L ⊆ nbr c ∧
      ∀ a ∈ A, ∀ b ∈ B, edgeFrom a b ∈ L.image (edgeFrom c) := by
  classical
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · have thin : A.card ≤ 1 ∨ B.card ≤ 1 := by
        by_contra! thick
        obtain ⟨a,ha',a',ha'',ne⟩ := Finset.one_lt_card.mp thick.1
        have sub : B ⊆ nbr a ∩ nbr a' := by
          intro b hb'
          exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid _ ha' _ hb'⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid _ ha'' _ hb'⟩⟩
        exact (Nat.not_lt_of_ge ((Finset.card_le_card sub).trans (geom.2 _ _ ne))) thick.2
      rcases thin with h | h
      · obtain ⟨c,hc⟩ := ha
        refine ⟨c,B,Or.inr (Or.inr rfl), fun b hb' => Finset.mem_filter.mpr ⟨Finset.mem_univ _, valid _ hc _ hb'⟩,?_⟩
        intro a ha' b hb'
        rw [Finset.card_le_one.mp h a ha' c hc]
        exact Finset.mem_image_of_mem _ hb'
      · obtain ⟨c,hc⟩ := hb
        refine ⟨c,A,Or.inr (Or.inl rfl),fun a ha' => Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by rw [incident_symm]; exact valid _ ha' _ hc⟩,?_⟩
        intro a ha' b hb'
        rw [Finset.card_le_one.mp h b hb' c hc, edgeFrom_symm]
        exact Finset.mem_image_of_mem _ ha'
    · exact ⟨0,∅,Or.inl rfl,Finset.empty_subset _,fun _ _ b h => (hb ⟨b,h⟩).elim⟩
  · exact ⟨0,∅,Or.inl rfl,Finset.empty_subset _,fun a h => (ha ⟨a,h⟩).elim⟩

/-- A gate-level count for the single-level form: both operands of every AND
can be arbitrary wires from the same shared bottom OR DAG. Empty operand
supports, a one-edge rectangle, and arbitrary partial overlaps of wires are
all allowed. The edge-compatibility hypothesis is forced for every live
AND feeding the output through ORs when the computed function is Petersen. -/
theorem shared_rectangles_lower (gs : List (Finset Vertex)) (built : OrDAG gs)
    (k : ℕ) (A B : Fin k → Finset Vertex)
    (available : ∀ j, Available gs (A j) ∧ Available gs (B j))
    (valid : ∀ j, ∀ a ∈ A j, ∀ b ∈ B j, incident a b = true)
    (cover : ∀ e ∈ edges, ∃ j, ∃ a ∈ A j, ∃ b ∈ B j, edgeFrom a b = e) :
    20 ≤ gs.length + k + (k-1) := by
  classical
  choose c L source sub transfer using fun j => orient (A j) (B j) (valid j)
  apply shared_star_lower gs built k c L sub
  · intro j
    rcases source j with h|h|h
    · rw [h]; exact Or.inl (by simp)
    · simpa [h] using (available j).1
    · simpa [h] using (available j).2
  · intro e he
    obtain ⟨j,a,ha,b,hb,rfl⟩ := cover e he
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,transfer _ _ ha _ hb⟩


/-- A final shared OR DAG taking the union of all k AND outputs needs at
least k−1 gates, including in the presence of repeated or absorbed signals. -/
theorem top_lower (k : ℕ) (top : List (Finset (Fin k))) (built : OrDAG top)
    (output : Available top Finset.univ) : k-1 ≤ top.length := by
  classical
  have count := leaves_le (Finset.univ : Finset (Fin k)) top built {Finset.univ}
    (fun _ _ => Finset.subset_univ _) (by simpa using output)
  have sub : countFor (Finset.univ : Finset (Fin k)) top ≤ top.length := List.countP_le_length
  simp at count
  omega

/-- A fully shared bottom and top OR network separated by one level of AND
gates cannot beat the 20-gate star construction. -/
theorem shared_single_level_lower (gs : List (Finset Vertex)) (built : OrDAG gs)
    (k : ℕ) (A B : Fin k → Finset Vertex)
    (available : ∀ j, Available gs (A j) ∧ Available gs (B j))
    (valid : ∀ j, ∀ a ∈ A j, ∀ b ∈ B j, incident a b = true)
    (cover : ∀ e ∈ edges, ∃ j, ∃ a ∈ A j, ∃ b ∈ B j, edgeFrom a b = e)
    (top : List (Finset (Fin k))) (topBuilt : OrDAG top) (output : Available top Finset.univ) :
    20 ≤ gs.length + k + top.length :=
  (shared_rectangles_lower gs built k A B available valid cover).trans
    (Nat.add_le_add_left (top_lower k top topBuilt output) _)

def graphValue (x : Vertex → Bool) : Bool :=
  decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true)

def rectangleValue (A B : Finset Vertex) (x : Vertex → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true) && decide (∃ b ∈ B, x b = true)

private theorem graph_pair : ∀ a b : Vertex,
    graphValue (fun v => decide (v = a ∨ v = b)) = incident a b := by decide +kernel

private theorem ends_mem : ∀ e ∈ edges, edgeFrom e.1 e.2 = e := by decide +kernel
private theorem distinct_ends : ∀ e ∈ edges, e.1 ≠ e.2 := by decide +kernel

theorem semantic_single_level_lower (gs : List (Finset Vertex)) (built : OrDAG gs)
    (k : Nat) (A B : Fin k → Finset Vertex)
    (available : ∀ j, Available gs (A j) ∧ Available gs (B j))
    (correct : ∀ x : Vertex → Bool,
      (List.finRange k).any (fun j => rectangleValue (A j) (B j) x) = graphValue x)
    (top : List (Finset (Fin k))) (topBuilt : OrDAG top) (output : Available top Finset.univ) :
    20 ≤ gs.length + k + top.length := by
  classical
  have valid (j : Fin k) (a : Vertex) (ha : a ∈ A j) (b : Vertex) (hb : b ∈ B j) : incident a b = true := by
    rw [← graph_pair,← correct]
    apply List.any_eq_true.mpr ⟨j,by simp,?_⟩
    simp only [rectangleValue,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨a,ha,by simp⟩,⟨b,hb,by simp⟩⟩
  apply shared_single_level_lower gs built k A B available valid _ top topBuilt output
  intro e he
  let x := fun v : Vertex => decide (v = e.1 ∨ v = e.2)
  have yes : graphValue x = true := by
    exact decide_eq_true ⟨e, he, by simp [x]⟩
  rw [← correct] at yes
  obtain ⟨j,_,hj⟩ := List.any_eq_true.mp yes
  simp only [rectangleValue,Bool.and_eq_true,decide_eq_true_eq] at hj
  obtain ⟨⟨a,ha,aa⟩,⟨b,hb,bb⟩⟩ := hj
  have av := valid j a ha b hb
  have hn : a ≠ b := by
    rintro rfl
    have diag : ∀ c : Vertex, incident c c = false := by decide +kernel
    rw [diag] at av
    contradiction
  refine ⟨j,a,ha,b,hb,?_⟩
  simp only [x,decide_eq_true_eq] at aa bb
  rcases aa with h|h <;> rcases bb with u|u <;> subst a <;> subst b
  · contradiction
  · exact ends_mem e he
  · rw [edgeFrom_symm]; exact ends_mem e he
  · contradiction

end Petersen2373.Stars
