import Mathlib

namespace PlanePrivate

-- Every ordered pair of distinct primary wires has a separating change of input.
-- On that change the first wire may fall, while the second definitely rises.
def Exchange {Z : Type} (n o : ℕ) (W : ℕ → Set Z) : Prop :=
  ∀ a < n, ∀ b < n, a ≠ b → ∃ x ∈ W o, ∃ y ∉ W o,
    x ∉ W b ∧ y ∈ W b ∧ ∀ t < n, t ≠ a → x ∈ W t → y ∈ W t

-- For a binary AND a rising operand makes the old value false, and for OR it
-- makes the new value true. The companion operand is free to change in either direction.
def Rising {Z : Type} (G : Finset ℕ) (P : ℕ → Finset ℕ) (W : ℕ → Set Z) : Prop :=
  ∀ g ∈ G, ∀ b ∈ P g, ∀ x y, x ∉ W b → y ∈ W b → x ∈ W g → y ∈ W g

def Forward {Z : Type} (G : Finset ℕ) (P : ℕ → Finset ℕ) (W : ℕ → Set Z) : Prop :=
  ∀ g ∈ G, ∀ x y, (∀ t ∈ P g, x ∈ W t → y ∈ W t) → x ∈ W g → y ∈ W g

theorem blocked {Z : Type} {n o : ℕ} {G : Finset ℕ} {P : ℕ → Finset ℕ} {W : ℕ → Set Z}
    (top : ∀ g ∈ G, ∀ t ∈ P g, t<g ∧ (t<n ∨ t∈G))
    (atOut : o∈G) (order : Forward G P W) (rising : Rising G P W) (ex : Exchange n o W)
    {a b v : ℕ} (ha : a<n) (hb : b<n) (ne : a≠b) (hv : v∈G) (bv : b∈P v)
    (bad : Finset ℕ) (lose : a∈bad) (clear : o∉bad)
    (sealed : ∀ g ∈ G, g∉bad → g≠v → ∀ t∈P g, t∉bad) : False := by
  obtain ⟨x,hx,y,hy,old,newer,stable⟩ := ex a ha b hb ne
  have ord (w : ℕ) (hlive : w<n ∨ w∈G) (good : w∉bad) : x∈W w → y∈W w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rcases hlive with raw|gate
      · exact stable w raw (fun eq => good (eq ▸ lose))
      · by_cases ev : w=v
        · subst w; exact rising v hv b bv x y old newer
        · apply order w gate x y
          intro t read
          obtain ⟨earlier,live⟩ := top w gate t read
          exact ih t earlier live (sealed w gate good ev t read)
  exact hy (ord o (Or.inr atOut) clear hx)

-- A private primary wire is one whose only reading gate is the indicated gate.
def UsesOnly (G : Finset ℕ) (P : ℕ → Finset ℕ) (a u : ℕ) : Prop :=
  ∀ g∈G, a∈P g → g=u

theorem distinctUsers {Z : Type} {n o : ℕ} {G : Finset ℕ} {P : ℕ → Finset ℕ} {W : ℕ → Set Z}
    (top : ∀ g ∈ G, ∀ t ∈ P g, t<g ∧ (t<n ∨ t∈G))
    (atOut : o∈G) (outGate : n≤o) (order : Forward G P W) (rising : Rising G P W)
    (ex : Exchange n o W) {a b u v : ℕ} (ha : a<n) (hb : b<n) (ne : a≠b)
    (au : UsesOnly G P a u) (gv : v∈G) (bv : b∈P v) : u≠v := by
  rintro rfl
  apply blocked top atOut order rising ex ha hb ne gv bv {a} (by simp) (by simp; omega)
  intro g hg _ nv t ht
  simpa only [Finset.mem_singleton] using fun e : t=a => nv (au g hg (e ▸ ht))

theorem noSuccessive {Z : Type} {n o : ℕ} {G : Finset ℕ} {P : ℕ → Finset ℕ} {W : ℕ → Set Z}
    (top : ∀ g ∈ G, ∀ t ∈ P g, t<g ∧ (t<n ∨ t∈G))
    (atOut : o∈G) (outGate : n≤o) (bounded : ∀ g∈G, g≤o)
    (order : Forward G P W) (rising : Rising G P W) (ex : Exchange n o W)
    {a b u v : ℕ} (ha : a<n) (hb : b<n) (ne : a≠b)
    (au : UsesOnly G P a u) (uv : UsesOnly G P u v) (gv : v∈G) (bv : b∈P v) (read : u∈P v) : False := by
  have earlier := (top v gv u read).1
  have limit := bounded v gv
  apply blocked top atOut order rising ex ha hb ne gv bv {a,u} (by simp) (by simp; omega)
  intro g hg ng nv t ht member
  rcases Finset.mem_insert.mp member with e | mem
  · exact ng (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (au g hg (e ▸ ht))))
  · exact nv (uv g hg ((Finset.mem_singleton.mp mem) ▸ ht))

end PlanePrivate

namespace PlanePrivate

-- Follow a private wire through an arbitrary number of gates with a unique reader.
-- The cut contains the original input and every gate strictly before the last gate.
theorem noRawAfterChain {Z : Type} {n o : ℕ} {G : Finset ℕ} {P : ℕ → Finset ℕ} {W : ℕ → Set Z}
    (top : ∀ g ∈ G, ∀ t ∈ P g, t<g ∧ (t<n ∨ t∈G))
    (atOut : o∈G) (bounded : ∀ g∈G, g≤o)
    (order : Forward G P W) (rising : Rising G P W) (ex : Exchange n o W)
    {a u w v : ℕ} (ha : a<n) (au : a<u) (soleA : UsesOnly G P a u)
    (R : ℕ → ℕ → Prop) (step : ∀ i j, R i j → i<j ∧ UsesOnly G P i j)
    (chain : Relation.ReflTransGen R u w) (last : R w v) (gv : v∈G) : ∀ b<n, b∉P v := by
  classical
  have cut {z : ℕ} (path : Relation.ReflTransGen R u z) :
      ∃ bad : Finset ℕ, a∈bad ∧ (∀ t∈bad, t<z) ∧
        ∀ g∈G, g∉bad → g≠z → ∀ t∈P g, t∉bad := by
    induction path with
    | refl =>
      refine ⟨{a},by simp,by simpa using au,?_⟩
      intro g hg _ diff t ht mem
      exact diff (soleA g hg ((Finset.mem_singleton.mp mem) ▸ ht))
    | @tail z k _ h ih =>
      obtain ⟨bad,ab,under,closedCut⟩ := ih
      obtain ⟨zk,sole⟩ := step z k h
      refine ⟨insert z bad,Finset.mem_insert_of_mem ab,?_,?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl|hi
        · exact zk
        · exact (under i hi).trans zk
      · intro g hg safe other t ht hit
        have gz : g ≠ z := fun eq => safe (eq ▸ Finset.mem_insert_self _ _)
        have none : g ∉ bad := fun h => safe (Finset.mem_insert_of_mem h)
        rcases Finset.mem_insert.mp hit with eq|hit
        · exact other (sole g hg (eq ▸ ht))
        · exact closedCut g hg none gz t ht hit
  have chainOrder {i j : ℕ} (p : Relation.ReflTransGen R i j) : i≤j := by
    induction p with
    | refl => rfl
    | tail _ h ih => exact ih.trans (step _ _ h).1.le
  have uv := (chainOrder chain).trans_lt (step w v last).1
  intro b hb bv
  by_cases same : a=b
  · exact (Nat.ne_of_lt uv) (soleA v gv (same ▸ bv)).symm
  · obtain ⟨bad,ab,under,closedCut⟩ := cut (chain.tail last)
    have clear : o∉bad := fun h => (Nat.not_lt_of_le (bounded v gv)) (under o h)
    exact blocked top atOut order rising ex ha hb same gv bv bad ab clear closedCut

end PlanePrivate
