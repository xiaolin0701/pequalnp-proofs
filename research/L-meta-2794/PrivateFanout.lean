import Mathlib

namespace PrivateFanout2794

/-- The live gates reading a wire. Duplicate reads in one gate count once. -/
def children (G : Finset ℕ) (parents : ℕ → Finset ℕ) (i : ℕ) : Finset ℕ :=
  G.filter fun g => i ∈ parents g

/-- One edge whose source has exactly one live reading gate. -/
def soleStep (G : Finset ℕ) (parents : ℕ → Finset ℕ) (u v : ℕ) : Prop :=
  v ∈ children G parents u ∧ (children G parents u).card = 1

private theorem twoSlots (S G : Finset ℕ) (parents : ℕ → Finset ℕ)
    (hslots : ∀ g ∈ G, (parents g).card ≤ 2) :
    ∑ w ∈ S, (children G parents w).card ≤ 2*G.card := by
  have expand (T : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
      (T.filter p).card = ∑ w ∈ T, if p w then 1 else 0 := by simp
  calc
    _ = ∑ g ∈ G, (S.filter fun w => w ∈ parents g).card := by
      simp only [children,expand]
      rw [Finset.sum_comm]
    _ ≤ ∑ _g ∈ G, 2 := by
      apply Finset.sum_le_sum
      intro g hg
      exact (Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2)).trans (hslots g hg)
    _ = _ := by simp [Nat.mul_comm]

private theorem countMarked (V Q : Finset ℕ) (hq : Q ⊆ V) :
    (∑ w ∈ V, if w ∈ Q then 1 else 0) = Q.card := by
  exact (Finset.card_eq_sum_ite hq).symm

private theorem branchingBudget (I G H : Finset ℕ) (parents : ℕ → Finset ℕ) (o : ℕ)
    (disj : Disjoint I G) (out : o ∈ G) (hG : H ⊆ G)
    (slots : ∀ g ∈ G, (parents g).card ≤ 2)
    (live : ∀ w ∈ I ∪ G, w ≠ o → (children G parents w).Nonempty)
    (heavy : ∀ w ∈ H, 2 ≤ (children G parents w).card) :
    2*I.card + H.card ≤ G.card + (I.filter fun i => (children G parents i).card = 1).card + 1 := by
  classical
  let V := I ∪ G
  let P := I.filter fun i => (children G parents i).card = 1
  let Q := (I \ P) ∪ H
  have pI : P ⊆ I := Finset.filter_subset _ _
  have cv : V.card = I.card + G.card := Finset.card_union_of_disjoint disj
  have qdis : Disjoint (I \ P) H :=
    disj.mono Finset.sdiff_subset hG
  have cq : Q.card + P.card = I.card + H.card := by
    have h := Finset.card_sdiff_add_card_eq_card pI
    unfold Q
    rw [Finset.card_union_of_disjoint qdis]
    omega
  have qsub : Q ⊆ V := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp h).1
    · exact Finset.mem_union_right _ (hG h)
  have oq : ∀ {w}, w ∈ Q → 2 ≤ (children G parents w).card := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨hi,hp⟩ := Finset.mem_sdiff.mp h
      have ne : w ≠ o := fun he => Finset.disjoint_left.mp disj hi (he.symm ▸ out)
      have pos := Finset.card_pos.mpr (live w (Finset.mem_union_left _ hi) ne)
      have hh : (children G parents w).card ≠ 1 := fun eq => hp (Finset.mem_filter.mpr ⟨hi,eq⟩)
      omega
    · exact heavy w h
  have localBound (w) (hw : w ∈ V) :
      1 + (if w ∈ Q then 1 else 0) ≤ (children G parents w).card + (if w = o then 1 else 0) := by
    by_cases hq : w ∈ Q
    · have h := oq hq
      simp only [hq,ite_true]
      omega
    · simp only [hq,ite_false,Nat.add_zero]
      by_cases he : w = o
      · simp [he]
      · simpa [he] using Finset.card_pos.mpr (live w hw he)
  have count1 := Finset.sum_le_sum localBound
  have edgeBound := twoSlots V G parents slots
  have vo : o ∈ V := Finset.mem_union_right _ out
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,countMarked V Q qsub,
    Finset.sum_ite_eq',vo,ite_true] at count1
  change 2*I.card + H.card ≤ G.card + P.card + 1
  omega

/-- `I` consists of the input wires, `G` of the gates, both in earlier-first topological
order. Mark the unique reader of each singly-read input. If these readers are distinct,
and any singly-read marked gate cannot feed a differently marked gate, then the circuit
has at least the claimed number of gates. -/
theorem fanoutBound (I G : Finset ℕ) (parents : ℕ → Finset ℕ) (o : ℕ)
    (disj : Disjoint I G) (out : o ∈ G)
    (slots : ∀ g ∈ G, (parents g).card ≤ 2)
    (back : ∀ g ∈ G, ∀ w ∈ parents g, w < g)
    (live : ∀ w ∈ I ∪ G, w ≠ o → (children G parents w).Nonempty)
    (c : ℕ → ℕ)
    (mark : ∀ a ∈ I, (children G parents a).card = 1 → c a ∈ children G parents a)
    (distinct : ∀ a ∈ I, ∀ b ∈ I, (children G parents a).card = 1 →
      (children G parents b).card = 1 → c a = c b → a = b)
    (separate : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → (children G parents a).card = 1 →
      (children G parents b).card = 1 → (children G parents (c a)).card = 1 →
      c a ∉ parents (c b)) :
    6 * I.card ≤ 5 * G.card + 4 := by
  classical
  let P := I.filter fun a => (children G parents a).card = 1
  let A := P.image c
  let H := A.filter fun g => 2 ≤ (children G parents g).card
  have aG : A ⊆ G := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    have h := Finset.mem_filter.mp ha
    exact (Finset.mem_filter.mp (mark a h.1 h.2)).1
  have hA : H ⊆ A := Finset.filter_subset _ _
  have ca : A.card = P.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb h
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    exact distinct a ha'.1 b hb'.1 ha'.2 hb'.2 h
  have count1 : 2*I.card + H.card ≤ G.card + P.card + 1 :=
    branchingBudget I G H parents o disj out (fun _ h => aG (hA h)) slots live
      (fun _ h => (Finset.mem_filter.mp h).2)
  let F := (A \ H).erase o
  have fc : A.card ≤ F.card + H.card + 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hA
    have he : (A \ H).card - 1 ≤ F.card := Finset.pred_card_le_card_erase
    omega
  have fReader (w) (hw : w ∈ F) : (children (G \ A) parents w).Nonempty := by
    obtain ⟨hne,hw⟩ := Finset.mem_erase.mp hw
    obtain ⟨ha,hh⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨a,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨g,hg⟩ := live (c a) (Finset.mem_union_right _ (aG ha)) hne
    obtain ⟨hG,hr⟩ := Finset.mem_filter.mp hg
    have pos := Finset.card_pos.mpr (show (children G parents (c a)).Nonempty from ⟨g,hg⟩)
    have less : ¬ 2 ≤ (children G parents (c a)).card := fun h => hh (Finset.mem_filter.mpr ⟨ha,h⟩)
    have one : (children G parents (c a)).card = 1 := by omega
    refine ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hG,?_⟩,hr⟩⟩
    intro hag
    obtain ⟨b,hbp,rfl⟩ := Finset.mem_image.mp hag
    by_cases eq : a=b
    · subst b
      exact (Nat.lt_irrefl _) (back _ hG _ hr)
    · have hap := Finset.mem_filter.mp hp
      have hbp' := Finset.mem_filter.mp hbp
      exact separate a hap.1 b hbp'.1 eq hap.2 hbp'.2 one hr
  have count2 : F.card ≤ 2*(G \ A).card := by
    have positive (w) (hw : w ∈ F) : 1 ≤ (children (G \ A) parents w).card := Finset.card_pos.mpr (fReader w hw)
    have hh := Finset.sum_le_sum positive
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at hh
    exact hh.trans (twoSlots F (G \ A) parents (fun g hg => slots g (Finset.mem_sdiff.mp hg).1))
  have cga := Finset.card_sdiff_add_card_eq_card aG
  omega

private theorem primaryReaders (I G : Finset ℕ) (parents : ℕ → Finset ℕ) (o : ℕ)
    (disj : Disjoint I G) (out : o ∈ G)
    (slots : ∀ g ∈ G, (parents g).card ≤ 2)
    (live : ∀ w ∈ I ∪ G, w ≠ o → (children G parents w).Nonempty)
    (c : ℕ → ℕ)
    (mark : ∀ a ∈ I, (children G parents a).card = 1 → c a ∈ children G parents a)
    (distinct : ∀ a ∈ I, ∀ b ∈ I, ∀ g ∈ G, a ≠ b → (children G parents a).card = 1 →
      b ∈ parents g → c a ≠ g) :
    let P := I.filter fun a => (children G parents a).card = 1
    let A := P.image c
    let D := G.filter fun g => ∃ b ∈ I, b ∈ parents g
    A ⊆ D ∧ A.card = P.card ∧ I.card ≤ D.card := by
  classical
  let P := I.filter fun a => (children G parents a).card = 1
  let A := P.image c
  let D := G.filter fun g => ∃ b ∈ I, b ∈ parents g
  have dG : D ⊆ G := Finset.filter_subset _ _
  have aD : A ⊆ D := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hi,hp⟩ := Finset.mem_filter.mp ha
    obtain ⟨hg,hr⟩ := Finset.mem_filter.mp (mark a hi hp)
    exact Finset.mem_filter.mpr ⟨hg,a,hi,hr⟩
  have ca : A.card = P.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb eq
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have h := Finset.mem_filter.mp (mark b hb'.1 hb'.2)
    by_contra ne
    exact distinct a ha'.1 b hb'.1 (c b) h.1 ne ha'.2 h.2 eq
  have inputHeavy (w) (hw : w ∈ I \ P) : 2 ≤ (children (D \ A) parents w).card := by
    obtain ⟨hi,hp⟩ := Finset.mem_sdiff.mp hw
    have nz := Finset.card_pos.mpr (live w (Finset.mem_union_left _ hi)
      (fun he => Finset.disjoint_left.mp disj hi (he.symm ▸ out)))
    have ne : (children G parents w).card ≠ 1 := fun h => hp (Finset.mem_filter.mpr ⟨hi,h⟩)
    have sub : children G parents w ⊆ children (D \ A) parents w := by
      intro g hg
      obtain ⟨hG,hwg⟩ := Finset.mem_filter.mp hg
      have hd : g ∈ D := Finset.mem_filter.mpr ⟨hG,w,hi,hwg⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hd,?_⟩,hwg⟩
      rintro hA
      obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp hA
      have ain := Finset.mem_filter.mp ha
      have nw : a ≠ w := fun e => hp (e ▸ ha)
      exact distinct a ain.1 w hi g hG nw ain.2 hwg eq
    have h := Finset.card_le_card sub
    omega
  have dcard : I.card ≤ D.card := by
    have hcount := (Finset.sum_le_sum inputHeavy).trans (twoSlots (I \ P) (D \ A) parents
      (fun g hg => slots g (dG (Finset.mem_sdiff.mp hg).1)))
    simp only [Finset.sum_const,smul_eq_mul] at hcount
    have hc := Finset.card_sdiff_add_card_eq_card aD
    have hp := Finset.card_sdiff_add_card_eq_card (show P ⊆ I from Finset.filter_subset _ _)
    omega
  exact ⟨aD,ca,dcard⟩

/-- If the same two obstructions apply to every reader of a primary input, all such
readers must be counted separately from the readers of singly-read marked gates. -/
theorem fanoutStrong (I G : Finset ℕ) (parents : ℕ → Finset ℕ) (o : ℕ)
    (disj : Disjoint I G) (out : o ∈ G)
    (slots : ∀ g ∈ G, (parents g).card ≤ 2)
    (back : ∀ g ∈ G, ∀ w ∈ parents g, w < g)
    (live : ∀ w ∈ I ∪ G, w ≠ o → (children G parents w).Nonempty)
    (c : ℕ → ℕ)
    (mark : ∀ a ∈ I, (children G parents a).card = 1 → c a ∈ children G parents a)
    (distinct : ∀ a ∈ I, ∀ b ∈ I, ∀ g ∈ G, a ≠ b → (children G parents a).card = 1 →
      b ∈ parents g → c a ≠ g)
    (separate : ∀ a ∈ I, ∀ b ∈ I, ∀ g ∈ G, a ≠ b → (children G parents a).card = 1 →
      (children G parents (c a)).card = 1 → c a ∈ parents g → b ∈ parents g → False) :
    4 * I.card ≤ 3 * G.card + 2 := by
  classical
  let P := I.filter fun a => (children G parents a).card = 1
  let A := P.image c
  let H := A.filter fun g => 2 ≤ (children G parents g).card
  let D := G.filter fun g => ∃ b ∈ I, b ∈ parents g
  have hA : H ⊆ A := Finset.filter_subset _ _
  have dG : D ⊆ G := Finset.filter_subset _ _
  obtain ⟨aD,ca,dcard⟩ : A ⊆ D ∧ A.card = P.card ∧ I.card ≤ D.card :=
    primaryReaders I G parents o disj out slots live c mark distinct
  have count1 : 2*I.card + H.card ≤ G.card + P.card + 1 :=
    branchingBudget I G H parents o disj out (fun _ h => dG (aD (hA h))) slots live
      (fun _ h => (Finset.mem_filter.mp h).2)
  let F := (A \ H).erase o
  have fc : A.card ≤ F.card + H.card + 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hA
    have he : (A \ H).card - 1 ≤ F.card := Finset.pred_card_le_card_erase
    omega
  have fReader (w) (hw : w ∈ F) : (children (G \ D) parents w).Nonempty := by
    obtain ⟨hne,hw⟩ := Finset.mem_erase.mp hw
    obtain ⟨ha,hh⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨a,hp,rfl⟩ := Finset.mem_image.mp ha
    have hap := Finset.mem_filter.mp hp
    obtain ⟨g,hg⟩ := live (c a) (Finset.mem_union_right _ (dG (aD ha))) hne
    obtain ⟨hG,hr⟩ := Finset.mem_filter.mp hg
    have pos := Finset.card_pos.mpr (show (children G parents (c a)).Nonempty from ⟨g,hg⟩)
    have less : ¬ 2 ≤ (children G parents (c a)).card := fun h => hh (Finset.mem_filter.mpr ⟨ha,h⟩)
    have one : (children G parents (c a)).card = 1 := by omega
    refine ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hG,?_⟩,hr⟩⟩
    intro hd
    obtain ⟨_,b,hb,br⟩ := Finset.mem_filter.mp hd
    by_cases eq : a=b
    · subst b
      obtain ⟨v,vs⟩ := Finset.card_eq_one.mp hap.2
      have hg' : g = v := by simpa [vs] using
        (show g ∈ children G parents a from Finset.mem_filter.mpr ⟨hG,br⟩)
      have hc' : c a = v := by simpa [vs] using mark a hap.1 hap.2
      have before := back _ hG _ hr
      omega
    · exact separate a hap.1 b hb g hG eq hap.2 one hr br
  have count2 : F.card ≤ 2*(G \ D).card := by
    have positive (w) (hw : w ∈ F) : 1 ≤ (children (G \ D) parents w).card :=
      Finset.card_pos.mpr (fReader w hw)
    have hh := Finset.sum_le_sum positive
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at hh
    exact hh.trans (twoSlots F (G \ D) parents (fun g hg => slots g (Finset.mem_sdiff.mp hg).1))
  have cgd := Finset.card_sdiff_add_card_eq_card dG
  omega


/-- Following a singly-read input through successive singly-read gates up to its first
branch point gains another gate bound. All gates met after the first reader must have
no primary operand. -/
theorem fanoutLong (I G : Finset ℕ) (parents : ℕ → Finset ℕ) (o : ℕ)
    (disj : Disjoint I G) (out : o ∈ G)
    (slots : ∀ g ∈ G, (parents g).card ≤ 2)
    (live : ∀ w ∈ I ∪ G, w ≠ o → (children G parents w).Nonempty)
    (c : ℕ → ℕ)
    (mark : ∀ a ∈ I, (children G parents a).card = 1 → c a ∈ children G parents a)
    (distinct : ∀ a ∈ I, ∀ b ∈ I, ∀ g ∈ G, a ≠ b → (children G parents a).card = 1 →
      b ∈ parents g → c a ≠ g)
    (long : ∀ a ∈ I, (children G parents a).card = 1 → ∀ w v,
      Relation.ReflTransGen (soleStep G parents) (c a) w →
      soleStep G parents w v → ∀ b ∈ I, b ∉ parents v) :
    3*I.card ≤ 2*G.card + 2 := by
  classical
  let P := I.filter fun a => (children G parents a).card = 1
  let A := P.image c
  let D := G.filter fun g => ∃ b ∈ I, b ∈ parents g
  let H := G.filter fun g => 2 ≤ (children G parents g).card
  let S := G.filter fun w => ∃ a ∈ P, Relation.ReflTransGen (soleStep G parents) (c a) w
  let F := (S \ H).erase o
  have dG : D ⊆ G := Finset.filter_subset _ _
  have sG : S ⊆ G := Finset.filter_subset _ _
  have hG : H ⊆ G := Finset.filter_subset _ _
  obtain ⟨aD,ca,dcard⟩ : A ⊆ D ∧ A.card = P.card ∧ I.card ≤ D.card :=
    primaryReaders I G parents o disj out slots live c mark distinct
  have aS : A ⊆ S := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_filter.mpr ⟨dG (aD hg),a,ha,.refl⟩
  have sD : S \ A ⊆ G \ D := by
    intro w hw
    obtain ⟨hs,ha⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hg,a,hp,hpath⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_sdiff.mpr ⟨hg,?_⟩
    obtain ⟨hi,hone⟩ := Finset.mem_filter.mp hp
    rcases hpath with _ | ⟨hfirst,hlast⟩
    · exact (ha (Finset.mem_image.mpr ⟨a,hp,rfl⟩)).elim
    · intro hd
      obtain ⟨_,b,hb,hr⟩ := Finset.mem_filter.mp hd
      exact long _ hi hone _ _ hfirst hlast _ hb hr
  have count1 : 2*I.card + H.card ≤ G.card + P.card + 1 :=
    branchingBudget I G H parents o disj out hG slots live (fun _ h => (Finset.mem_filter.mp h).2)
  have fReader (w) (hw : w ∈ F) : (children (S \ A) parents w).Nonempty := by
    obtain ⟨hne,hw⟩ := Finset.mem_erase.mp hw
    obtain ⟨hs,nh⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hg,a,hp,hpath⟩ := Finset.mem_filter.mp hs
    obtain ⟨v,hv⟩ := live w (Finset.mem_union_right _ hg) hne
    have pos := Finset.card_pos.mpr (show (children G parents w).Nonempty from ⟨v,hv⟩)
    have less : ¬ 2 ≤ (children G parents w).card := fun h => nh (Finset.mem_filter.mpr ⟨hg,h⟩)
    have st : soleStep G parents w v := ⟨hv,by omega⟩
    obtain ⟨gv,read⟩ := Finset.mem_filter.mp hv
    have vs : v ∈ S := Finset.mem_filter.mpr ⟨gv,a,hp,hpath.tail st⟩
    have hap := Finset.mem_filter.mp hp
    refine ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨vs,?_⟩,read⟩⟩
    intro va
    obtain ⟨_,b,hb,hr⟩ := Finset.mem_filter.mp (aD va)
    exact long _ hap.1 hap.2 _ _ hpath st _ hb hr
  have slotsUsed : F.card ≤ 2*(S \ A).card := by
    have positive (w) (hw : w ∈ F) : 1 ≤ (children (S \ A) parents w).card :=
      Finset.card_pos.mpr (fReader w hw)
    have hh := Finset.sum_le_sum positive
    simp only [Finset.sum_const,smul_eq_mul,mul_one] at hh
    exact hh.trans (twoSlots F (S \ A) parents (fun g hg => slots g (sG (Finset.mem_sdiff.mp hg).1)))
  have fbound : S.card ≤ F.card + H.card + 1 := by
    have he : (S \ H).card - 1 ≤ F.card := Finset.pred_card_le_card_erase
    have hi := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := H))
    have hh := Finset.card_sdiff_add_card_inter S H
    omega
  have := Finset.card_le_card sD
  have := Finset.card_sdiff_add_card_eq_card aS
  have := Finset.card_sdiff_add_card_eq_card dG
  omega

end PrivateFanout2794
