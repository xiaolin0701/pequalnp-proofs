import Mathlib
import PEqualNP.Defs

-- The rectangular charging lemma is adapted from upstream R_meta_2794_42.
-- With every AND separated, both missing grid axes and uncovered incident pairs are impossible.
set_option maxHeartbeats 20000000 in
theorem SeparatedPlaneBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    1 ≤ q → (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
    let n := N+N
    let one := fun (a b : Fin N) => decide (b = a)
    o < n+s →
    (∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) →
    (∀ i < s, ∃ a < n+i, ∃ b < n+i, let g := W (n+i)
      g = W a ∪ W b ∨ g = W a ∨ g = ∅ ∨ g = W a ∩ W b ∧
      (∃ (S T : Set (Fin N → Bool)), W a = S ×ˢ Set.univ ∧ W b = Set.univ ×ˢ T)) →
    (∀ p l, I p l → (one p,one l) ∈ W o) →
    (∀ y : Fin N → Bool, Fintype.card {l : Fin N // y l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o) →
    N*(q+1) ≤ 4*s := by
  let charged {α : Type} [DecidableEq α] (P : ℕ → Finset α) (A : Finset α) (n : ℕ) : Finset ℕ :=
    (Finset.range n).filter fun w => 2 ≤ (P w).card ∧ P w ⊆ A
  have budget {α : Type} [DecidableEq α] (P : ℕ → Finset α) (A : Finset α)
      (split : ∀ w, 2 ≤ (P w).card → P w ⊆ A →
        ∃ a < w, ∃ b < w, P w = P a ∪ P b) (n : ℕ) :
      ∀ R : Finset ℕ, R ⊆ Finset.range n → (∀ w ∈ R, P w ⊆ A) →
        (R.biUnion P).card ≤ R.card + (charged P A n).card := by
    induction n with
    | zero =>
      intro R scope allowed
      have empty : R = ∅ := Finset.subset_empty.mp (by simpa using scope)
      subst R
      simp
    | succ n ih =>
      intro R scope allowed
      have monotone : charged P A n ⊆ charged P A (n+1) := by
        intro w member
        simp only [charged, Finset.mem_filter, Finset.mem_range] at member ⊢
        exact ⟨by omega,member.2⟩
      by_cases top : n ∈ R
      · let rest := R.erase n
        have insertBack : insert n rest = R := Finset.insert_erase top
        have restBound : rest ⊆ Finset.range n := by
          intro w used
          obtain ⟨different, old⟩ := Finset.mem_erase.mp used
          have range := Finset.mem_range.mp (scope old)
          exact Finset.mem_range.mpr (by omega)
        have allowedRest (w : ℕ) (used : w ∈ rest) := allowed w (Finset.mem_erase.mp used).2
        have restCard : rest.card + 1 = R.card := Finset.card_erase_add_one top
        by_cases large : 2 ≤ (P n).card
        · obtain ⟨a, ha, b, hb, same⟩ := split n large (allowed n top)
          let enlarged := insert a (insert b rest)
          have subA : P a ⊆ A := fun v hv => allowed n top (same ▸ Finset.mem_union_left _ hv)
          have subB : P b ⊆ A := fun v hv => allowed n top (same ▸ Finset.mem_union_right _ hv)
          have inside : enlarged ⊆ Finset.range n := by
            intro w set
            rcases Finset.mem_insert.mp set with rfl | more
            · exact Finset.mem_range.mpr ha
            rcases Finset.mem_insert.mp more with rfl | old
            · exact Finset.mem_range.mpr hb
            · exact restBound old
          have enlargedAllowed (w : ℕ) (used : w ∈ enlarged) : P w ⊆ A := by
            rcases Finset.mem_insert.mp used with rfl | more
            · exact subA
            rcases Finset.mem_insert.mp more with rfl | old
            · exact subB
            · exact allowedRest w old
          have coverage : R.biUnion P = enlarged.biUnion P := by
            rw [← insertBack, Finset.biUnion_insert, same]
            simp [enlarged, Finset.union_assoc]
          have growth : enlarged.card ≤ R.card + 1 := by
            have one := Finset.card_insert_le (s := rest) (a := b)
            have two := Finset.card_insert_le (s := insert b rest) (a := a)
            change (insert a (insert b rest)).card ≤ R.card + 1
            omega
          have chargeGrowth : (charged P A (n+1)).card = (charged P A n).card + 1 := by
            have chargedTop : n ∉ charged P A n := by simp [charged]
            have addTop : charged P A (n+1) = insert n (charged P A n) := by
              ext w
              simp only [charged, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
              constructor
              · rintro ⟨h,wsize,wallow⟩
                by_cases eq : w = n
                · exact Or.inl eq
                · exact Or.inr ⟨by omega,wsize,wallow⟩
              · rintro (rfl | ⟨h,wsize,wallow⟩)
                · exact ⟨by omega,large,allowed _ top⟩
                · exact ⟨by omega,wsize,wallow⟩
            rw [addTop, Finset.card_insert_of_notMem chargedTop]
          have prior := ih enlarged inside enlargedAllowed
          rw [coverage]
          omega
        · have prior := ih rest restBound allowedRest
          have limit : (R.biUnion P).card ≤ (P n).card + (rest.biUnion P).card := by
            rw [← insertBack, Finset.biUnion_insert]
            exact Finset.card_union_le _ _
          have monotoneCard := Finset.card_le_card monotone
          omega
      · have priorScope : R ⊆ Finset.range n := by
          intro w used
          have different : w ≠ n := fun eq => top (eq ▸ used)
          have range := Finset.mem_range.mp (scope used)
          exact Finset.mem_range.mpr (by omega)
        exact (ih R priorScope allowed).trans
          (Nat.add_le_add_left (Finset.card_le_card monotone) _)
  have starBudget {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype β]
      (P : ℕ → Finset α) (neighbors : β → Finset α) (raw n : ℕ) (roots : β → Finset ℕ)
      (splits : ∀ w, 2 ≤ (P w).card → ∃ a < w, ∃ b < w, P w = P a ∪ P b)
      (smallInputs : ∀ w < raw, (P w).card ≤ 1)
      (unique : ∀ u v, u ≠ v → ((neighbors u) ∩ (neighbors v)).card ≤ 1)
      (scope : ∀ b, roots b ⊆ Finset.range n)
      (covered : ∀ b w, w ∈ roots b → P w ⊆ neighbors b) :
      (∑ b, ((roots b).biUnion P).card) ≤ (∑ b, (roots b).card) + (n-raw) := by
    let charges (b : β) := charged P (neighbors b) n
    have each (b : β) : ((roots b).biUnion P).card ≤ (roots b).card + (charges b).card :=
      budget P (neighbors b) (fun w big _ => splits w big) n (roots b) (scope b) (covered b)
    have distinct : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint charges := by
      intro u _ v _ different
      refine Finset.disjoint_left.mpr ?_
      intro w inU inV
      have first := (Finset.mem_filter.mp inU).2
      have second := (Finset.mem_filter.mp inV).2
      have both : P w ⊆ neighbors u ∩ neighbors v :=
        fun i seen => Finset.mem_inter.mpr ⟨first.2 seen,second.2 seen⟩
      have upper := (Finset.card_le_card both).trans (unique u v different)
      omega
    have total : (∑ b, (charges b).card) ≤ n-raw := by
      rw [← Finset.card_biUnion distinct]
      have within : (Finset.univ.biUnion charges) ⊆ Finset.Ico raw n := by
        intro w used
        obtain ⟨b,_,member⟩ := Finset.mem_biUnion.mp used
        have below := Finset.mem_range.mp (Finset.mem_filter.mp member).1
        have above : raw ≤ w := by
          by_contra! before
          have notLarge := smallInputs w before
          have large := (Finset.mem_filter.mp member).2.1
          omega
        exact Finset.mem_Ico.mpr ⟨above,below⟩
      exact (Finset.card_le_card within).trans (by simp)
    calc
      (∑ b, ((roots b).biUnion P).card) ≤ ∑ b, ((roots b).card + (charges b).card) :=
        Finset.sum_le_sum fun b _ => each b
      _ = (∑ b, (roots b).card) + (∑ b, (charges b).card) := Finset.sum_add_distrib
      _ ≤ (∑ b, (roots b).card) + (n-raw) := Nat.add_le_add_left total _
  have buckets {α γ : Type} [DecidableEq α] [Fintype α] [DecidableEq γ]
      (rects : Finset γ) (axis : γ → Finset α) (destination : γ → ℕ) :
      (∑ a : α, ((rects.filter fun r => axis r = {a}).image destination).card) ≤ rects.card := by
    let group (a : α) := rects.filter fun r => axis r = {a}
    have distinct : (↑(Finset.univ : Finset α) : Set α).PairwiseDisjoint group := by
      intro a _ b _ different
      refine Finset.disjoint_left.mpr ?_
      intro r left right
      have equal : ({a} : Finset α) = {b} := (Finset.mem_filter.mp left).2.symm.trans (Finset.mem_filter.mp right).2
      exact different (Finset.singleton_injective equal)
    have inside : Finset.univ.biUnion group ⊆ rects := by
      intro r mem
      obtain ⟨a,_,used⟩ := Finset.mem_biUnion.mp mem
      exact (Finset.mem_filter.mp used).1
    calc
      _ ≤ ∑ a : α, (group a).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = (Finset.univ.biUnion group).card := (Finset.card_biUnion distinct).symm
      _ ≤ rects.card := Finset.card_le_card inside
  have incidenceBudget {α β : Type} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
      (I : α → β → Prop) [DecidableRel I] (P : ℕ → Finset α) (L : ℕ → Finset β) (raw n : ℕ)
      (splitsP : ∀ w, 2 ≤ (P w).card → ∃ a < w, ∃ b < w, P w = P a ∪ P b)
      (splitsL : ∀ w, 2 ≤ (L w).card → ∃ a < w, ∃ b < w, L w = L a ∪ L b)
      (smallP : ∀ w < raw, (P w).card ≤ 1) (smallL : ∀ w < raw, (L w).card ≤ 1)
      (linear : ∀ a a' b b', I a b → I a b' → I a' b → I a' b' → a = a' ∨ b = b')
      (rects : Finset (ℕ × ℕ))
      (range : ∀ e ∈ rects, e.1 < n ∧ e.2 < n)
      (sound : ∀ e ∈ rects, ∀ a ∈ P e.1, ∀ b ∈ L e.2, I a b)
      (pairs : Finset (α × β)) (cover : ∀ a b, (a,b) ∈ pairs → ∃ e ∈ rects, a ∈ P e.1 ∧ b ∈ L e.2) :
      pairs.card ≤ 2 * (rects.card + (n - raw)) := by
    let leftN (a : α) := Finset.univ.filter fun b => I a b
    let rightN (b : β) := Finset.univ.filter fun a => I a b
    let leftR (a : α) := (rects.filter fun e => P e.1 = {a}).image Prod.snd
    let rightR (b : β) := (rects.filter fun e => L e.2 = {b}).image Prod.fst
    have leftUnique (a a' : α) (different : a ≠ a') : ((leftN a) ∩ (leftN a')).card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro b b' left right
      simp only [leftN, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at left right
      exact (linear a a' b b' left.1 right.1 left.2 right.2).resolve_left different
    have rightUnique (b b' : β) (different : b ≠ b') : ((rightN b) ∩ (rightN b')).card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro a a' left right
      simp only [rightN, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at left right
      exact (linear a a' b b' left.1 left.2 right.1 right.2).resolve_right different
    have leftRange (a : α) : leftR a ⊆ Finset.range n := by
      intro w used
      obtain ⟨e,mem,rfl⟩ := Finset.mem_image.mp used
      exact Finset.mem_range.mpr (range e (Finset.mem_filter.mp mem).1).2
    have rightRange (b : β) : rightR b ⊆ Finset.range n := by
      intro w used
      obtain ⟨e,mem,rfl⟩ := Finset.mem_image.mp used
      exact Finset.mem_range.mpr (range e (Finset.mem_filter.mp mem).1).1
    have leftSound (a : α) (w : ℕ) (used : w ∈ leftR a) : L w ⊆ leftN a := by
      obtain ⟨e,mem,rfl⟩ := Finset.mem_image.mp used
      obtain ⟨belongs, center⟩ := Finset.mem_filter.mp mem
      intro b hb
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, sound e belongs a (by simp [center]) b hb⟩
    have rightSound (b : β) (w : ℕ) (used : w ∈ rightR b) : P w ⊆ rightN b := by
      obtain ⟨e,mem,rfl⟩ := Finset.mem_image.mp used
      obtain ⟨belongs, center⟩ := Finset.mem_filter.mp mem
      intro a ha
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, sound e belongs a ha b (by simp [center])⟩
    let leftPairs (a : α) := ((leftR a).biUnion L).image fun b => (a,b)
    let rightPairs (b : β) := ((rightR b).biUnion P).image fun a => (a,b)
    have all : pairs ⊆ (Finset.univ.biUnion leftPairs) ∪ (Finset.univ.biUnion rightPairs) := by
      rintro ⟨a,b⟩ accepted
      obtain ⟨e,member,usesA,usesB⟩ := cover a b accepted
      by_cases leftCenter : P e.1 = {a}
      · apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,Finset.mem_image.mpr
          ⟨b,Finset.mem_biUnion.mpr ⟨e.2,Finset.mem_image.mpr
            ⟨e,Finset.mem_filter.mpr ⟨member,leftCenter⟩,rfl⟩,usesB⟩,rfl⟩⟩
      · have different : ∃ a' ∈ P e.1, a' ≠ a := by
          by_contra! all
          apply leftCenter
          ext p
          exact ⟨fun present => Finset.mem_singleton.mpr (all p present),
            fun present => (Finset.mem_singleton.mp present).symm ▸ usesA⟩
        obtain ⟨a',usesA',distinct⟩ := different
        have rightCenter : L e.2 = {b} := by
          ext b'
          constructor
          · intro usesB'
            apply Finset.mem_singleton.mpr
            apply (linear a' a b' b (sound e member a' usesA' b' usesB')
              (sound e member a' usesA' b usesB) (sound e member a usesA b' usesB')
              (sound e member a usesA b usesB)).resolve_left distinct
          · intro present
            exact (Finset.mem_singleton.mp present).symm ▸ usesB
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,Finset.mem_image.mpr
          ⟨a,Finset.mem_biUnion.mpr ⟨e.1,Finset.mem_image.mpr
            ⟨e,Finset.mem_filter.mpr ⟨member,rightCenter⟩,rfl⟩,usesA⟩,rfl⟩⟩
    have leftBound : (Finset.univ.biUnion leftPairs).card ≤ rects.card + (n-raw) := by
      apply Finset.card_biUnion_le.trans
      apply (Finset.sum_le_sum fun _ _ => Finset.card_image_le).trans
      apply (starBudget L leftN raw n leftR splitsL smallL leftUnique leftRange leftSound).trans
      exact Nat.add_le_add_right (buckets rects (fun e => P e.1) Prod.snd) _
    have rightBound : (Finset.univ.biUnion rightPairs).card ≤ rects.card + (n-raw) := by
      apply Finset.card_biUnion_le.trans
      apply (Finset.sum_le_sum fun _ _ => Finset.card_image_le).trans
      apply (starBudget P rightN raw n rightR splitsP smallP rightUnique rightRange rightSound).trans
      exact Nat.add_le_add_right (buckets rects (fun e => L e.2) Prod.fst) _
    have coverBound := (Finset.card_le_card all).trans (Finset.card_union_le _ _)
    omega
  let cell (N : ℕ) := (Fin N → Bool) × (Fin N → Bool)
  let one {N : ℕ} (a : Fin N) (b : Fin N) : Bool := decide (b = a)
  let zero {N : ℕ} : Fin N → Bool := fun _ => false
  let separated {N : ℕ} (W : ℕ → Set (cell N)) (a b : ℕ) : Prop :=
    ∃ P L : Set (Fin N → Bool), W a = P ×ˢ Set.univ ∧ W b = Set.univ ×ˢ L
  let gridInputs {N : ℕ} (W : ℕ → Set (cell N)) : Prop :=
    ∀ p : Fin N, W p.val = {x | x.1 p = true} ∧ W (N + p.val) = {x | x.2 p = true}
  let gridNegative {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
      (q : ℕ) (W : ℕ → Set (cell N)) (o : ℕ) : Prop :=
    ∀ L : Fin N → Bool, Fintype.card {l : Fin N // L l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ L l = true)), L) ∉ W o

  let axisMissing {N : ℕ} (s : ℕ) (W : ℕ → Set (cell N)) : Prop :=
    let m := N+N
    let A := fun (d : Bool) (w : ℕ) => {p : Fin N |
      (if d then (one p,zero) else (zero,one p)) ∈ W w}
    ∃ i < s, ∃ d : Bool, ∃ p r : Fin N, p ≠ r ∧ p ∈ A d (m+i) ∧ r ∈ A d (m+i) ∧
      ¬ ∃ a < m+i, ∃ b < m+i, A d (m+i) = A d a ∪ A d b
  let cleanPairs {N : ℕ} (s o : ℕ) (I : Fin N → Fin N → Prop) (W : ℕ → Set (cell N)) :
      Set (Fin N × Fin N) :=
    let m := N+N
    { e | I e.1 e.2 ∧
      ∃ i < s, W (m+i) ⊆ W o ∧ (one e.1,one e.2) ∈ W (m+i) ∧
      ∃ a b, max a b < m+i ∧ W (m+i) = W a ∩ W b ∧ separated W a b }
  have geometry (q N s o : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (qpos : 1 ≤ q)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (W : ℕ → Set (cell N)) (output : o < N+N+s) (raw : gridInputs W)
      (steps : ∀ i < s, ∃ a < N+N+i, ∃ b < N+N+i,
        W (N+N+i) = W a ∪ W b ∨ W (N+N+i) = W a ∨ W (N+N+i) = ∅ ∨ W (N+N+i) = W a ∩ W b)
      (negative : gridNegative I q W o) (supports : ¬axisMissing s W) :
      (cleanPairs s o I W).ncard ≤ 4*s := by
    classical
    let m := N+N
    have split (w : ℕ) (hw : w < m+s) (hw' : ¬ w < m) :
        ∃ a < w, ∃ b < w, W w = W a ∪ W b ∨ W w = W a ∨ W w = ∅ ∨ W w = W a ∩ W b := by
      have eq : m + (w-m) = w := by omega
      obtain ⟨a, ha, b, hb, law⟩ := steps (w-m) (by omega)
      change a < m+(w-m) at ha
      change b < m+(w-m) at hb
      change W (m+(w-m)) = W a ∪ W b ∨ W (m+(w-m)) = W a ∨ W (m+(w-m)) = ∅ ∨
        W (m+(w-m)) = W a ∩ W b at law
      rw [eq] at ha hb law
      exact ⟨a,ha,b,hb,law⟩
    have rawShape (w : ℕ) (hw : w < m) :
        (∃ p : Fin N, W w = {x | x.1 p = true}) ∨
        (∃ l : Fin N, W w = {x | x.2 l = true}) := by
      by_cases point : w < N
      · exact Or.inl ⟨⟨w,point⟩,(raw ⟨w,point⟩).1⟩
      · let l : Fin N := ⟨w-N,by omega⟩
        have id : N + l.val = w := by change N+(w-N)=w; omega
        exact Or.inr ⟨l,id ▸ (raw l).2⟩
    let above (x y : cell N) : Prop :=
      (∀ p, x.1 p = true → y.1 p = true) ∧ (∀ l, x.2 l = true → y.2 l = true)
    have monotone (w : ℕ) (within : w < m+s) :
        ∀ x y, above x y → x ∈ W w → y ∈ W w := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro x y order active
        by_cases input : w < m
        · rcases rawShape w input with ⟨p,shape⟩ | ⟨l,shape⟩
          · rw [shape] at active ⊢
            exact order.1 p active
          · rw [shape] at active ⊢
            exact order.2 l active
        · obtain ⟨a,ha,b,hb,union | copy | empty | meet⟩ := split w within input
          · rw [union] at active ⊢
            exact active.imp (ih a ha (by omega) x y order) (ih b hb (by omega) x y order)
          · rw [copy] at active ⊢
            exact ih a ha (by omega) x y order active
          · rw [empty] at active
            exact active.elim
          · rw [meet] at active ⊢
            exact ⟨ih a ha (by omega) x y order active.1, ih b hb (by omega) x y order active.2⟩
    have oneCard (l : Fin N) : Fintype.card {k : Fin N // one l k = true} ≤ q := by
      rw [Fintype.card_of_subtype ({l} : Finset (Fin N)) (by intro k; simp [one])]
      simpa using qpos
    have singletonSound (p l : Fin N) (active : (one p,one l) ∈ W o) : I p l := by
      by_contra wrong
      let Points : Fin N → Bool := fun a => decide (¬∃ k, I a k ∧ one l k = true)
      have hi : above (one p,one l) (Points,one l) := by
        refine ⟨?_,fun _ h => h⟩
        intro a key
        have id : a = p := by simpa [one] using key
        subst a
        change decide (¬∃ k, I p k ∧ one l k = true) = true
        simp [one,wrong]
      exact negative (one l) (oneCard l) (monotone o output _ _ hi active)
    let pointSupport (w : ℕ) := if w < m+s then
      Finset.univ.filter fun p : Fin N => (one p,zero) ∈ W w else ∅
    let lineSupport (w : ℕ) := if w < m+s then
      Finset.univ.filter fun l : Fin N => (zero,one l) ∈ W w else ∅
    have pointMem (w : ℕ) (p : Fin N) (hw : w < m+s) :
        p ∈ pointSupport w ↔ (one p,zero) ∈ W w := by simp [pointSupport,hw]
    have lineMem (w : ℕ) (l : Fin N) (hw : w < m+s) :
        l ∈ lineSupport w ↔ (zero,one l) ∈ W w := by simp [lineSupport,hw]
    have rawPoint (w : ℕ) (hw : w < m) : (pointSupport w).card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro a b left right
      have aHome := (pointMem w a (by omega)).mp left
      have bHome := (pointMem w b (by omega)).mp right
      rcases rawShape w hw with ⟨p,shape⟩ | ⟨l,shape⟩
      · rw [shape] at aHome bHome
        have first : p = a := of_decide_eq_true aHome
        have second : p = b := of_decide_eq_true bHome
        exact first.symm.trans second
      · rw [shape] at aHome
        exact Bool.noConfusion (show false = true from aHome)
    have rawLine (w : ℕ) (hw : w < m) : (lineSupport w).card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro a b left right
      have aHome := (lineMem w a (by omega)).mp left
      have bHome := (lineMem w b (by omega)).mp right
      rcases rawShape w hw with ⟨p,shape⟩ | ⟨l,shape⟩
      · rw [shape] at aHome
        exact Bool.noConfusion (show false = true from aHome)
      · rw [shape] at aHome bHome
        have first : l = a := of_decide_eq_true aHome
        have second : l = b := of_decide_eq_true bHome
        exact first.symm.trans second

    have axisSplits (d : Bool) (S : ℕ → Finset (Fin N))
        (he : ∀ w i, w < m+s →
          (i ∈ S w ↔ (if d then (one i,zero) else (zero,one i)) ∈ W w))
        (rawSmall : ∀ w < m, (S w).card ≤ 1) (outsideEmpty : ∀ w, ¬ w < m+s → S w = ∅) :
        ∀ w, 2 ≤ (S w).card → ∃ a < w, ∃ b < w, S w = S a ∪ S b := by
      intro w big
      have within : w < m+s := by
        by_contra outside
        simp [outsideEmpty w outside] at big
      have after : ¬ w < m := by intro input; have := rawSmall w input; omega
      let i := w-m
      have id : m+i = w := by dsimp [i]; omega
      obtain ⟨p, seen, r, found, different⟩ := Finset.one_lt_card.mp big
      by_contra bad
      apply supports
      refine ⟨i,by dsimp [i]; omega,d,p,r,different,?_,?_,?_⟩
      · rw [id]
        exact (he w p within).mp seen
      · rw [id]
        exact (he w r within).mp found
      · intro law
        rw [id] at law
        obtain ⟨a,ha,b,hb,combine⟩ := law
        apply bad
        refine ⟨a,ha,b,hb,?_⟩
        ext j
        rw [Finset.mem_union, he w j within, he a j (by omega), he b j (by omega)]
        exact Set.ext_iff.mp combine j
    have splitP := axisSplits true pointSupport (by simpa only [ite_true] using pointMem) rawPoint
      (fun w hw => by simp [pointSupport,hw])
    have splitL := axisSplits false lineSupport (by simpa using lineMem) rawLine
      (fun w hw => by simp [lineSupport,hw])
    let shape (i a b : ℕ) : Prop :=
      a < m+i ∧ b < m+i ∧ W (m+i) = W a ∩ W b ∧ separated W a b
    let candidates (i : ℕ) := ∃ a b, shape i a b
    let chosen (i : ℕ) : ℕ × ℕ := if law : candidates i then
      (Classical.choose law,Classical.choose (Classical.choose_spec law)) else (0,0)
    let finalGates := (Finset.range s).filter fun i => candidates i ∧ W (m+i) ⊆ W o
    let rectangles := finalGates.image chosen
    have choiceShape (i : ℕ) (law : candidates i) : shape i (chosen i).1 (chosen i).2 := by
      simp only [chosen,dite_eq_left law]
      exact Classical.choose_spec (Classical.choose_spec law)
    have rectangleSpec (i : ℕ) (used : i ∈ finalGates) :
        (chosen i).1 < m+s ∧ (chosen i).2 < m+s ∧
        ∀ p l : Fin N, (one p,one l) ∈ W (m+i) ↔
          p ∈ pointSupport (chosen i).1 ∧ l ∈ lineSupport (chosen i).2 := by
      obtain ⟨range,law,live⟩ := Finset.mem_filter.mp used
      have small := Finset.mem_range.mp range
      obtain ⟨ha,hb,form,A,B,pureA,pureB⟩ := choiceShape i law
      refine ⟨by omega,by omega,?_⟩
      intro p l
      rw [pointMem _ _ (by omega), lineMem _ _ (by omega), form, pureA, pureB]
      exact Iff.rfl
    have valid (e : ℕ × ℕ) (taken : e ∈ rectangles) : e.1 < m+s ∧ e.2 < m+s := by
      obtain ⟨i,used,rfl⟩ := Finset.mem_image.mp taken
      exact ⟨(rectangleSpec i used).1,(rectangleSpec i used).2.1⟩
    have sound (e : ℕ × ℕ) (taken : e ∈ rectangles) :
        ∀ p ∈ pointSupport e.1, ∀ l ∈ lineSupport e.2, I p l := by
      obtain ⟨i,used,rfl⟩ := Finset.mem_image.mp taken
      intro p inP l inL
      apply singletonSound
      exact (Finset.mem_filter.mp used).2.2 ((rectangleSpec i used).2.2 p l |>.mpr ⟨inP,inL⟩)

    have finitePairs : (cleanPairs s o I W).Finite := Set.toFinite _
    let pairs := finitePairs.toFinset
    have covers (p l : Fin N) (hit : (p,l) ∈ pairs) :
        ∃ e ∈ rectangles, p ∈ pointSupport e.1 ∧ l ∈ lineSupport e.2 := by
      have member : (p,l) ∈ cleanPairs s o I W := (Set.Finite.mem_toFinset finitePairs).mp hit
      obtain ⟨_,i,inside,below,active,a,b,bounds,eq,pure⟩ := member
      have present : i ∈ finalGates := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr inside, ⟨a,b,(max_lt_iff.mp bounds).1,(max_lt_iff.mp bounds).2,eq,pure⟩, below⟩
      exact ⟨chosen i,Finset.mem_image.mpr ⟨i,present,rfl⟩,(rectangleSpec i present).2.2 p l |>.mp active⟩
    have linear (a a' b b' : Fin N) (ab : I a b) (ab' : I a b') (a'b : I a' b) (a'b' : I a' b') :
        a = a' ∨ b = b' := by
      by_cases equal : a = a'
      · exact Or.inl equal
      · exact Or.inr ((unique a a' equal).unique ⟨ab,a'b⟩ ⟨ab',a'b'⟩)
    have upper := incidenceBudget I pointSupport lineSupport m (m+s) splitP splitL rawPoint rawLine
      linear rectangles valid sound pairs covers
    have enclosures : rectangles.card ≤ s := Finset.card_image_le.trans (by
      exact (Finset.card_filter_le _ _).trans (by simp))
    rw [Set.ncard_eq_toFinset_card _ finitePairs]
    change pairs.card ≤ 4*s
    have sub : m+s-m = s := by omega
    rw [sub] at upper
    omega
  intro q N I inst hq degree uniq s o W
  dsimp only
  intro ho raw steps positive negative
  classical
  let n := N+N
  have rawShape (w : ℕ) (hw : w < n) :
      (∃ p : Fin N, W w = {x | x.1 p = true}) ∨
      (∃ l : Fin N, W w = {x | x.2 l = true}) := by
    by_cases point : w < N
    · exact Or.inl ⟨⟨w,point⟩,(raw ⟨w,point⟩).1⟩
    · let l : Fin N := ⟨w-N,by dsimp [n] at hw; omega⟩
      have e : N+l.val = w := by dsimp [l]; omega
      exact Or.inr ⟨l,e ▸ (raw l).2⟩
  have split (w : ℕ) (hw : w < n+s) (later : ¬w<n) :
      ∃ a < w, ∃ b < w, W w = W a ∪ W b ∨ W w = W a ∨ W w = ∅ ∨
        W w = W a ∩ W b ∧ separated W a b := by
    obtain ⟨a,ha,b,hb,law⟩ := steps (w-n) (by omega)
    have e : N+N+(w-n)=w := by change n+(w-n)=w; omega
    rw [e] at ha hb law
    exact ⟨a,ha,b,hb,law⟩
  have off (w : ℕ) (hw : w < n+s) : (zero,zero) ∉ W w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases early : w<n
      · rcases rawShape w early with ⟨p,eq⟩|⟨l,eq⟩ <;> rw [eq] <;> exact Bool.noConfusion
      · obtain ⟨a,ha,b,hb,eq|eq|eq|⟨eq,_,_,_,_⟩⟩ := split w hw early
        · rw [eq]; exact fun h => h.elim (ih a ha (by omega)) (ih b hb (by omega))
        · rw [eq]; exact ih a ha (by omega)
        · rw [eq]; exact id
        · rw [eq]; exact fun h => ih a ha (by omega) h.1
  have axes : ¬axisMissing s W := by
    rintro ⟨i,hi,d,p,r,_,hp,_,missing⟩
    obtain ⟨a,ha,b,hb,eq|eq|eq|⟨eq,P,L,pureP,pureL⟩⟩ := steps i hi
    · apply missing ⟨a,ha,b,hb,?_⟩
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_union, eq]
    · apply missing ⟨a,ha,a,ha,?_⟩
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_union, eq, or_self]
    · change (if d then (one p,zero) else (zero,one p)) ∈ W (N+N+i) at hp
      simp [eq] at hp
    · change (if d then (one p,zero) else (zero,one p)) ∈ W (N+N+i) at hp
      rw [eq,pureP,pureL] at hp
      cases d with
      | false =>
        apply off a (by dsimp [n]; omega)
        rw [pureP]
        exact ⟨hp.1.1,Set.mem_univ _⟩
      | true =>
        apply off b (by dsimp [n]; omega)
        rw [pureL]
        exact ⟨Set.mem_univ _,hp.2.2⟩
  have noraw (w : ℕ) (h : w<n) : ¬ W w ⊆ W o := by
    intro below
    rcases rawShape w h with ⟨p,shape⟩|⟨l,shape⟩
    · apply negative zero (by simp [zero]) (below ?_)
      rw [shape]; simp [zero]
    · apply negative (one l) (by simpa [one] using hq) (below ?_)
      rw [shape]; simp [one]
  have eqPairs : cleanPairs s o I W = {e : Fin N × Fin N | I e.1 e.2} := by
    ext e
    constructor
    · exact fun h => h.1
    · intro he
      refine ⟨he,?_⟩
      have trace (w : ℕ) (hw : w<n+s) (sub : W w ⊆ W o) (onW : (one e.1,one e.2) ∈ W w) :
          ∃ i<s, W (n+i) ⊆ W o ∧ (one e.1,one e.2) ∈ W (n+i) ∧
            ∃ a b, max a b < n+i ∧ W (n+i)=W a ∩ W b ∧ separated W a b := by
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          by_cases early : w<n
          · exact False.elim (noraw w early sub)
          · obtain ⟨a,ha,b,hb,eq|eq|eq|⟨eq,hsep⟩⟩ := split w hw early
            · rw [eq] at onW sub
              rcases onW with h|h
              · exact ih a ha (by omega) (Set.Subset.trans Set.subset_union_left sub) h
              · exact ih b hb (by omega) (Set.Subset.trans Set.subset_union_right sub) h
            · rw [eq] at onW sub
              exact ih a ha (by omega) sub onW
            · simp [eq] at onW
            · refine ⟨w-n,by omega,?_⟩
              rw [show n+(w-n)=w by omega]
              exact ⟨sub,onW,a,b,max_lt_iff.mpr ⟨ha,hb⟩,eq,hsep⟩
      exact trace o ho Set.Subset.rfl (positive _ _ he)
  have hbound := geometry q N s o I hq uniq W ho raw (by
    intro i hi
    obtain ⟨a,ha,b,hb,h⟩ := steps i hi
    exact ⟨a,ha,b,hb,h.imp_right (Or.imp_right (Or.imp_right And.left))⟩) negative axes
  rw [eqPairs, Set.ncard_ofPred, Nat.card_eq_fintype_card] at hbound
  let e : {pl : Fin N × Fin N // I pl.1 pl.2} ≃ Σ l : Fin N, {p : Fin N // I p l} :=
    { toFun := fun z => ⟨z.val.2,⟨z.val.1,z.property⟩⟩
      invFun := fun z => ⟨(z.2.val,z.1),z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [Fintype.card_congr e, Fintype.card_sigma, show (∑ l : Fin N, Fintype.card {p : Fin N // I p l})=N*(q+1) by simp [degree]] at hbound
