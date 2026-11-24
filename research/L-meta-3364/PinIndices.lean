import PrivateInputs

namespace PlanePin

def skipIndex (a i : ℕ) := if i<a then i else i+1

theorem skipIndex_lt {a i n : ℕ} (ha : a<n) (hi : i<n-1) : skipIndex a i<n := by
  simp only [skipIndex]
  split <;> omega

theorem skipIndex_ne (a i : ℕ) : skipIndex a i ≠ a := by
  simp only [skipIndex]
  split <;> omega

theorem skipIndex_injective (a : ℕ) : Function.Injective (skipIndex a) := by
  intro i j
  simp only [skipIndex]
  split <;> split <;> omega

theorem skipIndex_surj {a n t : ℕ} (ha : a<n) (ht : t<n) (ne : t≠a) :
    ∃ i<n-1, skipIndex a i=t := by
  by_cases low : t<a
  · exact ⟨t,by omega,by simp [skipIndex,low]⟩
  · exact ⟨t-1,by omega,by simp [skipIndex,show ¬t-1<a by omega]; omega⟩

theorem liftExchange {Z : Type} {n a o out : ℕ} (ha : a<n)
    (W : ℕ → Set Z) (U : ℕ → Set {z : Z // z∉W a})
    (rawEqual : ∀ i<n-1, ∀ z : {z : Z // z∉W a}, z∈U i ↔ z.val∈W (skipIndex a i))
    (outputEqual : ∀ z : {z : Z // z∉W a}, z∈U out ↔ z.val∈W o)
    (ex : ∀ k<n, k≠a → ∀ l<n, l≠a → k≠l →
      ∃ x∈W o, ∃ y∉W o, x∉W a ∧ y∉W a ∧ x∉W l ∧ y∈W l ∧
        ∀ t<n, t≠k → x∈W t → y∈W t) :
    PlanePrivate.Exchange (n-1) out U := by
  intro i hi j hj ne
  have inj := skipIndex_injective a
  obtain ⟨x,hx,y,hy,dx,dy,bx,by',stable⟩ := ex
    _ (skipIndex_lt ha hi) (skipIndex_ne a i)
    _ (skipIndex_lt ha hj) (skipIndex_ne a j) (fun eq => ne (inj eq))
  let x' : {z : Z // z∉W a} := ⟨x,dx⟩
  let y' : {z : Z // z∉W a} := ⟨y,dy⟩
  refine ⟨x',(outputEqual x').2 hx,y',fun h => hy ((outputEqual y').1 h),
    fun h => bx ((rawEqual j hj x').1 h),(rawEqual j hj y').2 by',?_⟩
  intro t ht nt h
  exact (rawEqual t ht y').2 (stable _ (skipIndex_lt ha ht) (fun eq => nt (inj eq))
    ((rawEqual t ht x').1 h))

theorem pinReadyFrom {Z : Type} {n a o : ℕ} (many : 3≤n) (ha : a<n) (W : ℕ → Set Z)
    (ex : ∀ k<n, k≠a → ∀ l<n, l≠a → k≠l →
      ∃ x∈W o, ∃ y∉W o, x∉W a ∧ y∉W a ∧ x∉W l ∧ y∈W l ∧
        ∀ t<n, t≠k → x∈W t → y∈W t) :
    ∃ U : ℕ → Set {z : Z // z∉W a},
      (∀ i<n, Subtype.val ⁻¹' W i = (∅ : Set {z : Z // z∉W a}) ∨
        ∃ j<n-1, Subtype.val ⁻¹' W i=U j) ∧
      (Subtype.val ⁻¹' W o : Set {z : Z // z∉W a}).Nonempty ∧
      ∀ (V : ℕ → Set {z : Z // z∉W a}) t, (∀ j<n-1, V j=U j) →
        Subtype.val ⁻¹' W o=V t → PlanePrivate.Exchange (n-1) t V := by
  let U (i : ℕ) : Set {z : Z // z∉W a} := Subtype.val ⁻¹' W (skipIndex a i)
  refine ⟨U,?_,?_,?_⟩
  · intro i hi
    by_cases eq : i=a
    · subst i
      left
      exact Set.eq_empty_iff_forall_notMem.mpr (fun z hz => z.property hz)
    · obtain ⟨j,hj,ij⟩ := skipIndex_surj ha hi eq
      exact Or.inr ⟨j,hj,by simp only [U,ij]⟩
  · obtain ⟨x,hx,y,hy,dx,_⟩ := ex _ (skipIndex_lt ha (show 0<n-1 by omega)) (skipIndex_ne a 0)
      _ (skipIndex_lt ha (show 1<n-1 by omega)) (skipIndex_ne a 1)
      (fun eq => Nat.zero_ne_one (skipIndex_injective a eq))
    exact ⟨⟨x,dx⟩,hx⟩
  · intro V t inputs output
    apply liftExchange ha W V _ _ ex
    · intro i hi z
      rw [inputs i hi]
      rfl
    · intro z
      rw [←output]
      rfl

end PlanePin
