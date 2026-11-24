import Mathlib

-- Point degree by counting the other points on the pencil through p.
-- Adapted from the merged PEqualNP.Outside.L_meta_1955.lines_through.
namespace RectangleCost.Geometry

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

end RectangleCost.Geometry

namespace RectangleCost

def Flag {N : ℕ} (I : Fin N → Fin N → Prop) (bits : Finset ℕ) : Prop :=
  ∃ p l, I p l ∧ p.val ∈ bits ∧ N+l.val ∈ bits

theorem distinguish {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1) (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) :
    ∀ a < N+N, ∀ b < N+N, a ≠ b →
    ∃ p l, I p l ∧ b ∉ ({p.val,N+l.val} : Finset ℕ) ∧
      ¬ Flag I (insert b (({p.val,N+l.val} : Finset ℕ).erase a)) := by
  classical
  let C (l : Fin N) := Finset.univ.filter (fun p => I p l)
  let R (p : Fin N) := Finset.univ.filter (fun l => I p l)
  have hC (l : Fin N) : (C l).card = q+1 := by
    simpa only [C,← Fintype.card_subtype] using cols l
  have hR := Geometry.lines_through q N I hq hN hC unique
  have twoP (l : Fin N) : ∃ p r, I p l ∧ I r l ∧ p ≠ r := by
    obtain ⟨p,r,hp,hr,ne⟩ := Finset.one_lt_card_iff.mp (show 1 < (C l).card by rw [hC]; omega)
    exact ⟨p,r,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hr).2,ne⟩
  have twoL (p : Fin N) : ∃ l k, I p l ∧ I p k ∧ l ≠ k := by
    obtain ⟨l,k,hl,hk,ne⟩ := Finset.one_lt_card_iff.mp (show 1 < (R p).card by dsimp [R]; rw [hR]; omega)
    exact ⟨l,k,(Finset.mem_filter.mp hl).2,(Finset.mem_filter.mp hk).2,ne⟩
  have rowDiff (p r : Fin N) (pr : p ≠ r) : ∃ l, I p l ∧ ¬ I r l := by
    obtain ⟨l,k,hl,hk,lk⟩ := twoL p
    by_contra! fail
    exact lk ((unique p r pr).unique ⟨hl,fail l hl⟩ ⟨hk,fail k hk⟩)
  have colDiff (l k : Fin N) (lk : l ≠ k) : ∃ p, I p l ∧ ¬ I p k := by
    obtain ⟨p,r,hp,hr,pr⟩ := twoP l
    by_contra! fail
    exact lk ((unique p r pr).unique ⟨hp,hr⟩ ⟨fail p hp,fail r hr⟩)
  intro a ha b hb ne
  by_cases ap : a < N
  · let p : Fin N := ⟨a,ap⟩
    have ep : p.val=a := rfl
    by_cases bp : b < N
    · let r : Fin N := ⟨b,bp⟩
      have er : r.val=b := rfl
      obtain ⟨l,pl,rl⟩ := rowDiff p r (fun h => ne (congrArg Fin.val h))
      refine ⟨p,l,pl,by simp [ep]; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [ep,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hu hv
      have eu : u=r := Fin.ext (by have := u.isLt; omega)
      have ev : v=l := Fin.ext (by have := v.isLt; omega)
      exact rl (eu ▸ ev ▸ uv)
    · let k : Fin N := ⟨b-N,by omega⟩
      have ek : N+k.val=b := by dsimp [k]; omega
      obtain ⟨l0,l1,h0,h1,neL⟩ := twoL p
      have alt : ∃ l, I p l ∧ l ≠ k := by
        by_cases eq : l0=k
        · exact ⟨l1,h1,fun e => neL (eq.trans e.symm)⟩
        · exact ⟨l0,h0,eq⟩
      obtain ⟨l,pl,lk⟩ := alt
      have vk : l.val ≠ k.val := fun e => lk (Fin.ext e)
      refine ⟨p,l,pl,by simp [ep]; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [ep,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hu
      have := u.isLt
      omega
  · let l : Fin N := ⟨a-N,by omega⟩
    have el : N+l.val=a := by dsimp [l]; omega
    by_cases bp : b < N
    · let r : Fin N := ⟨b,bp⟩
      have er : r.val=b := rfl
      obtain ⟨p0,p1,h0,h1,neP⟩ := twoP l
      have alt : ∃ p, I p l ∧ p ≠ r := by
        by_cases eq : p0=r
        · exact ⟨p1,h1,fun e => neP (eq.trans e.symm)⟩
        · exact ⟨p0,h0,eq⟩
      obtain ⟨p,pl,pr⟩ := alt
      have vr : p.val ≠ r.val := fun e => pr (Fin.ext e)
      refine ⟨p,l,pl,by simp [el]; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [el,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hv
      have := p.isLt
      omega
    · let k : Fin N := ⟨b-N,by omega⟩
      have ek : N+k.val=b := by dsimp [k]; omega
      have lk : l ≠ k := fun e => ne (by rw [← el,← ek,e])
      obtain ⟨p,pl,pk⟩ := colDiff l k lk
      refine ⟨p,l,pl,by simp [el]; have := p.isLt; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [el,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hu hv
      have eu : u=p := Fin.ext (by have := u.isLt; omega)
      have ev : v=k := Fin.ext (by have := p.isLt; omega)
      exact pk (eu ▸ ev ▸ uv)

end RectangleCost

-- Every fan-in-two monotone output is monotone on a support of at most m+1 primary wires.
theorem MonotoneSupport : ∀ (Z : Type) (n m o : ℕ) (W : ℕ → Set Z), o < n+m →
      (∀ g < m, ∃ a < n+g, ∃ b < n+g,
        W (n+g) = W a ∪ W b ∨ W (n+g) = W a ∨ W (n+g) = ∅ ∨ W (n+g) = W a ∩ W b) →
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ m+1 ∧
        ∀ x y, (∀ v ∈ S, x ∈ W v → y ∈ W v) → x ∈ W o → y ∈ W o := by
  intro Z n m o W ho gates
  classical
  have reach (k : ℕ) (hk : k ≤ m) (T : Finset ℕ) (ht : ∀ u ∈ T, u < n+k) :
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ T.card+k ∧
        ∀ x y, (∀ v ∈ S, x ∈ W v → y ∈ W v) → ∀ u ∈ T, x ∈ W u → y ∈ W u := by
    induction k generalizing T with
    | zero =>
      exact ⟨T, fun u hu => Finset.mem_range.mpr (by simpa using ht u hu), by simp, fun _ _ h => h⟩
    | succ k ih =>
      let w := n+k
      by_cases hwat : w ∈ T
      · obtain ⟨a,ha,b,hb,law⟩ := gates k (by omega)
        let U := insert a (insert b (T.erase w))
        have hU : ∀ u ∈ U, u < n+k := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl|hu
          · exact ha
          rcases Finset.mem_insert.mp hu with rfl|hu
          · exact hb
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hu
          have := ht u hm
          change u ≠ n+k at hne
          omega
        obtain ⟨S, hs, hc, hdep⟩ := ih (by omega) U hU
        have c1 := Finset.card_insert_le a (insert b (T.erase w))
        have c2 := Finset.card_insert_le b (T.erase w)
        rw [Finset.card_erase_of_mem hwat] at c2
        have := Finset.card_pos.mpr ⟨w,hwat⟩
        have uc : U.card ≤ T.card+1 := by dsimp [U]; omega
        refine ⟨S,hs,by omega,?_⟩
        intro x y hxy u hu
        by_cases eq : u = w
        · subst u
          have pa := hdep x y hxy a (by simp [U])
          have pb := hdep x y hxy b (by simp [U])
          change x ∈ W (n+k) → y ∈ W (n+k)
          rcases law with h | h | h | h <;> rw [h]
          · exact Or.imp pa pb
          · exact pa
          · exact id
          · exact And.imp pa pb
        · exact hdep x y hxy u (by simp [U,eq,hu])
      · have ht' : ∀ u ∈ T, u < n+k := by
          intro u hu
          have hne : u ≠ w := fun e => hwat (e ▸ hu)
          have := ht u hu
          change u ≠ n+k at hne
          omega
        obtain ⟨S,hs,hc,hdep⟩ := ih (by omega) T ht'
        exact ⟨S,hs,by omega,hdep⟩
  obtain ⟨S,hs,hc,hdep⟩ := reach m le_rfl {o} (by simpa using ho)
  exact ⟨S,hs,by simpa [Nat.add_comm] using hc,fun x y h => hdep x y h o (by simp)⟩

namespace NoTwins

abbrev steps {Z : Type} (n m : ℕ) (W : ℕ → Set Z) :=
  ∀ g < m, ∃ a < n+g, ∃ b < n+g,
    W (n+g) = W a ∪ W b ∨ W (n+g) = W a ∨ W (n+g) = ∅ ∨ W (n+g) = W a ∩ W b

end NoTwins

namespace RectangleCost

theorem planeExchange {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N = q^2+q+1) (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (ho : o < N+N+m)
    (inputs : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
    (gates : NoTwins.steps (N+N) m W)
    (pos : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (neg : ∀ y : Fin N → Bool, Fintype.card {l // y l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l = true)), y) ∉ W o) :
    ∀ a < N+N, ∀ b < N+N, a ≠ b → ∃ x ∈ W o, ∃ y ∉ W o,
      x ∉ W b ∧ y ∈ W b ∧ ∀ t < N+N, t ≠ a → x ∈ W t → y ∈ W t := by
  classical
  let state (T : Finset ℕ) : (Fin N → Bool) × (Fin N → Bool) :=
    ((fun p => decide (p.val ∈ T)),(fun l => decide (N+l.val ∈ T)))
  have raw (T : Finset ℕ) (v : ℕ) (hv : v < N+N) : state T ∈ W v ↔ v ∈ T := by
    by_cases hp : v < N
    · let p : Fin N := ⟨v,hp⟩
      rw [show v = p.val from rfl,(inputs p).1]
      simp [state]
    · let l : Fin N := ⟨v-N,by omega⟩
      have eq : v=N+l.val := by dsimp [l]; omega
      rw [eq,(inputs l).2]
      simp [state]
  obtain ⟨S,scope,ss,dep⟩ := MonotoneSupport _ (N+N) m o W ho gates
  have falseOn (T : Finset ℕ) (small : T.card ≤ q) (clean : ¬ Flag I T) : state T ∉ W o := by
    let y := (state T).2
    let x := fun p : Fin N => decide (¬∃ l, I p l ∧ y l = true)
    let active := Finset.univ.filter (fun l : Fin N => N+l.val ∈ T)
    have counts : Fintype.card {l // y l = true} ≤ q := by
      have im : active.image (fun l => N+l.val) ⊆ T := by
        intro v hv
        obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hl).2
      have inj : Function.Injective (fun l : Fin N => N+l.val) := fun a b e => Fin.ext (Nat.add_left_cancel e)
      have count := Finset.card_le_card im
      rw [Finset.card_image_of_injective _ inj] at count
      simpa [Fintype.card_subtype,y,state,active] using count.trans small
    intro seen
    apply neg y counts (dep (state T) (x,y) (fun v hv => ?_) seen)
    have range := Finset.mem_range.mp (scope hv)
    by_cases hp : v < N
    · let p : Fin N := ⟨v,hp⟩
      rw [show v = p.val from rfl,(inputs p).1]
      change decide (p.val ∈ T) = true → decide (¬∃ l, I p l ∧ y l = true) = true
      intro bit
      apply decide_eq_true
      rintro ⟨l,pl,on⟩
      exact clean ⟨p,l,pl,of_decide_eq_true bit,of_decide_eq_true on⟩
    · let l : Fin N := ⟨v-N,by omega⟩
      rw [show v = N+l.val by dsimp [l]; omega,(inputs l).2]
      exact id
  have trueOn (p l : Fin N) (inc : I p l) : state {p.val,N+l.val} ∈ W o := by
    have e : state {p.val,N+l.val} = ((fun t => decide (t=p)),(fun t => decide (t=l))) := by
      apply Prod.ext <;> funext t
      · have ne : t.val ≠ N+l.val := by have := t.isLt; omega
        simp [state,Fin.ext_iff,ne]
      · have ne : N+t.val ≠ p.val := by have := p.isLt; omega
        simp [state,Fin.ext_iff,ne]
    exact e ▸ pos p l inc
  intro a ha b hb ne
  obtain ⟨p,l,pl,miss,clean⟩ := distinguish I (by omega) hN cols unique a ha b hb ne
  let E : Finset ℕ := {p.val,N+l.val}
  let F := insert b (E.erase a)
  have hE : E.card ≤ 2 := by simpa [E] using Finset.card_insert_le p.val {N+l.val}
  have hF : F.card ≤ q := by
    have h := Finset.card_insert_le b (E.erase a)
    have h2 := Finset.card_le_card (Finset.erase_subset a E)
    dsimp [F]; omega
  refine ⟨state E,trueOn p l pl,state F,falseOn F hF clean,?_,?_,?_⟩
  · exact fun bit => miss ((raw E b hb).1 bit)
  · exact (raw F b hb).2 (Finset.mem_insert_self _ _)
  · intro t ht hne bit
    exact (raw F t ht).2 (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne,(raw E t ht).1 bit⟩))

end RectangleCost
