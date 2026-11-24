import PlaneGeometry
import SparseExactness

namespace RectangleCost

private theorem twoAvoid {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (inj : Function.Injective f) (drop : ℕ) (rich : 3 ≤ S.card) :
    ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ f x ≠ drop ∧ f y ≠ drop := by
  by_cases found : ∃ z ∈ S, f z=drop
  · obtain ⟨z,hz,eq⟩ := found
    have card : 1 < (S.erase z).card := by rw [Finset.card_erase_of_mem hz]; omega
    obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp card
    obtain ⟨xz,xS⟩ := Finset.mem_erase.mp hx
    obtain ⟨yz,yS⟩ := Finset.mem_erase.mp hy
    exact ⟨x,y,xS,yS,ne,fun h => xz (inj (h.trans eq.symm)),fun h => yz (inj (h.trans eq.symm))⟩
  · obtain ⟨x,y,hx,hy,ne⟩ := Finset.one_lt_card_iff.mp (show 1<S.card by omega)
    exact ⟨x,y,hx,hy,ne,fun h => found ⟨x,hx,h⟩,fun h => found ⟨y,hy,h⟩⟩

theorem distinguishAvoid {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1) (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) :
    ∀ drop a, a < N+N → a ≠ drop → ∀ b < N+N, a ≠ b →
    ∃ p l, I p l ∧ drop ∉ ({p.val,N+l.val} : Finset ℕ) ∧ b ∉ ({p.val,N+l.val} : Finset ℕ) ∧
      ¬ Flag I (insert b (({p.val,N+l.val} : Finset ℕ).erase a)) := by
  classical
  let C (l : Fin N) := Finset.univ.filter (fun p => I p l)
  let R (p : Fin N) := Finset.univ.filter (fun l => I p l)
  have hC (l : Fin N) : (C l).card = q+1 := by
    simpa only [C,← Fintype.card_subtype] using cols l
  have hR := Geometry.lines_through q N I hq hN hC unique
  intro drop
  have twoP (l : Fin N) : ∃ p r, I p l ∧ I r l ∧ p ≠ r ∧ p.val ≠ drop ∧ r.val ≠ drop := by
    obtain ⟨p,r,hp,hr,ne,dp,dr⟩ := twoAvoid (C l) Fin.val Fin.val_injective drop (by rw [hC]; omega)
    exact ⟨p,r,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hr).2,ne,dp,dr⟩
  have twoL (p : Fin N) : ∃ l k, I p l ∧ I p k ∧ l ≠ k ∧ N+l.val ≠ drop ∧ N+k.val ≠ drop := by
    have inj : Function.Injective (fun l : Fin N => N+l.val) := fun _ _ h => Fin.ext (Nat.add_left_cancel h)
    obtain ⟨l,k,hl,hk,ne,dl,dk⟩ := twoAvoid (R p) (fun l => N+l.val) inj drop (by dsimp [R]; rw [hR]; omega)
    exact ⟨l,k,(Finset.mem_filter.mp hl).2,(Finset.mem_filter.mp hk).2,ne,dl,dk⟩
  have rowDiff (p r : Fin N) (pr : p ≠ r) : ∃ l, I p l ∧ ¬ I r l ∧ N+l.val ≠ drop := by
    obtain ⟨l,k,hl,hk,lk,dl,dk⟩ := twoL p
    by_cases h : I r l
    · exact ⟨k,hk,fun bad => lk ((unique p r pr).unique ⟨hl,h⟩ ⟨hk,bad⟩),dk⟩
    · exact ⟨l,hl,h,dl⟩
  have colDiff (l k : Fin N) (lk : l ≠ k) : ∃ p, I p l ∧ ¬ I p k ∧ p.val ≠ drop := by
    obtain ⟨p,r,hp,hr,pr,dp,dr⟩ := twoP l
    by_cases h : I p k
    · exact ⟨r,hr,fun bad => lk ((unique p r pr).unique ⟨hp,hr⟩ ⟨h,bad⟩),dr⟩
    · exact ⟨p,hp,h,dp⟩
  intro a ha ad b hb ne
  by_cases ap : a < N
  · let p : Fin N := ⟨a,ap⟩
    have ep : p.val=a := rfl
    by_cases bp : b < N
    · let r : Fin N := ⟨b,bp⟩
      have er : r.val=b := rfl
      obtain ⟨l,pl,rl,dl⟩ := rowDiff p r (fun h => ne (congrArg Fin.val h))
      refine ⟨p,l,pl,by simp only [Finset.mem_insert,Finset.mem_singleton,ep]; omega,by simp [ep]; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [ep,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hu hv
      have eu : u=r := Fin.ext (by have := u.isLt; omega)
      have ev : v=l := Fin.ext (by have := v.isLt; omega)
      exact rl (eu ▸ ev ▸ uv)
    · let k : Fin N := ⟨b-N,by omega⟩
      have ek : N+k.val=b := by dsimp [k]; omega
      obtain ⟨l0,l1,h0,h1,neL,d0,d1⟩ := twoL p
      have alt : ∃ l, I p l ∧ l ≠ k ∧ N+l.val ≠ drop := by
        by_cases eq : l0=k
        · exact ⟨l1,h1,fun e => neL (eq.trans e.symm),d1⟩
        · exact ⟨l0,h0,eq,d0⟩
      obtain ⟨l,pl,lk,dl⟩ := alt
      have vk : l.val ≠ k.val := fun e => lk (Fin.ext e)
      refine ⟨p,l,pl,by simp only [Finset.mem_insert,Finset.mem_singleton,ep]; omega,by simp [ep]; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [ep,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hu
      have := u.isLt
      omega
  · let l : Fin N := ⟨a-N,by omega⟩
    have el : N+l.val=a := by dsimp [l]; omega
    by_cases bp : b < N
    · let r : Fin N := ⟨b,bp⟩
      have er : r.val=b := rfl
      obtain ⟨p0,p1,h0,h1,neP,d0,d1⟩ := twoP l
      have alt : ∃ p, I p l ∧ p ≠ r ∧ p.val ≠ drop := by
        by_cases eq : p0=r
        · exact ⟨p1,h1,fun e => neP (eq.trans e.symm),d1⟩
        · exact ⟨p0,h0,eq,d0⟩
      obtain ⟨p,pl,pr,dp⟩ := alt
      have vr : p.val ≠ r.val := fun e => pr (Fin.ext e)
      refine ⟨p,l,pl,by simp only [Finset.mem_insert,Finset.mem_singleton,el]; omega,by simp [el]; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [el,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hv
      have := p.isLt
      omega
    · let k : Fin N := ⟨b-N,by omega⟩
      have ek : N+k.val=b := by dsimp [k]; omega
      have lk : l ≠ k := fun e => ne (by rw [← el,← ek,e])
      obtain ⟨p,pl,pk,dp⟩ := colDiff l k lk
      refine ⟨p,l,pl,by simp only [Finset.mem_insert,Finset.mem_singleton,el]; omega,by simp [el]; have := p.isLt; omega,?_⟩
      rintro ⟨u,v,uv,hu,hv⟩
      simp only [el,Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton] at hu hv
      have eu : u=p := Fin.ext (by have := u.isLt; omega)
      have ev : v=k := Fin.ext (by have := p.isLt; omega)
      exact pk (eu ▸ ev ▸ uv)

theorem pinnedExchange {q N m o : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 100 < q) (hN : N = q^2+q+1) (cols : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))) (ho : o < N+N+m)
    (inputs : ∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true})
    (gates : NoTwins.steps (N+N) m W)
    (pos : ∀ p l, I p l → ((fun t => decide (t=p)),(fun t => decide (t=l))) ∈ W o)
    (neg : ∀ y : Fin N → Bool, Fintype.card {l // y l = true} ≤ q →
      ((fun p => decide (¬∃ l, I p l ∧ y l = true)), y) ∉ W o) :
    ∀ d < N+N, ∀ a < N+N, a ≠ d → ∀ b < N+N, b ≠ d → a ≠ b → ∃ x ∈ W o, ∃ y ∉ W o,
      x ∉ W d ∧ y ∉ W d ∧ x ∉ W b ∧ y ∈ W b ∧ ∀ t < N+N, t ≠ a → x ∈ W t → y ∈ W t := by
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
  have falseOn (T : Finset ℕ) (small : T.card ≤ q) (clean : ¬ Flag I T) : state T ∉ W o := by
    let y := (state T).2
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
    obtain ⟨p,l,hpl,hp,hl⟩ :=
      (SparsePlaneIncidence.exactOnSparseLines I (W o)
        (SparsePlaneIncidence.wireMonotone W inputs gates o ho) pos neg
        (state T).1 y counts).mp seen
    exact clean ⟨p,l,hpl,of_decide_eq_true hp,of_decide_eq_true hl⟩
  have trueOn (p l : Fin N) (inc : I p l) : state {p.val,N+l.val} ∈ W o := by
    have e : state {p.val,N+l.val} = ((fun t => decide (t=p)),(fun t => decide (t=l))) := by
      apply Prod.ext <;> funext t
      · have ne : t.val ≠ N+l.val := by have := t.isLt; omega
        simp [state,Fin.ext_iff,ne]
      · have ne : N+t.val ≠ p.val := by have := p.isLt; omega
        simp [state,Fin.ext_iff,ne]
    exact e ▸ pos p l inc
  intro d hd a ha ad b hb bd ne
  obtain ⟨p,l,pl,avoid,miss,clean⟩ := distinguishAvoid I (by omega) hN cols unique d a ha ad b hb ne
  let E : Finset ℕ := {p.val,N+l.val}
  let F := insert b (E.erase a)
  have hE : E.card ≤ 2 := by simpa [E] using Finset.card_insert_le p.val {N+l.val}
  have hF : F.card ≤ q := by
    have h := Finset.card_insert_le b (E.erase a)
    have h2 := Finset.card_le_card (Finset.erase_subset a E)
    dsimp [F]; omega
  refine ⟨state E,trueOn p l pl,state F,falseOn F hF clean,?_,?_,?_,?_,?_⟩
  · exact fun bit => avoid ((raw E d hd).1 bit)
  · intro bit
    obtain eq|rest := Finset.mem_insert.mp ((raw F d hd).1 bit)
    · exact bd eq.symm
    · exact avoid (Finset.mem_of_mem_erase rest)
  · exact fun bit => miss ((raw E b hb).1 bit)
  · exact (raw F b hb).2 (Finset.mem_insert_self _ _)
  · intro t ht hne bit
    exact (raw F t ht).2 (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne,(raw E t ht).1 bit⟩))

end RectangleCost
