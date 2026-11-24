import SixStarTail

namespace PlaneStarTail.HeawoodSymmetry
open PlaneStarTail.Heawood

structure Witness where
  point : Fin 7 → Fin 7
  line : Fin 7 → Fin 7

private def representatives : Fin 21 → Witness := ![
  ⟨![0,1,2,3,4,5,6],![0,1,2,3,4,5,6]⟩,
  ⟨![0,3,2,1,5,4,6],![0,1,4,3,2,6,5]⟩,
  ⟨![0,3,6,1,4,5,2],![0,1,5,3,6,2,4]⟩,
  ⟨![0,1,6,3,5,4,2],![0,1,6,3,5,4,2]⟩,
  ⟨![1,0,5,3,4,2,6],![0,2,1,6,4,5,3]⟩,
  ⟨![1,0,6,3,2,4,5],![0,2,3,6,5,4,1]⟩,
  ⟨![0,6,3,2,4,5,1],![1,0,2,3,6,5,4]⟩,
  ⟨![0,6,1,2,5,4,3],![1,0,4,3,5,6,2]⟩,
  ⟨![0,2,1,6,4,5,3],![1,0,5,3,4,2,6]⟩,
  ⟨![0,2,3,6,5,4,1],![1,0,6,3,2,4,5]⟩,
  ⟨![6,0,5,2,4,3,1],![1,2,0,4,6,5,3]⟩,
  ⟨![1,6,3,5,4,2,0],![2,0,1,6,3,5,4]⟩,
  ⟨![1,5,3,6,2,4,0],![2,0,3,6,1,4,5]⟩,
  ⟨![1,5,0,6,4,2,3],![2,0,5,6,4,1,3]⟩,
  ⟨![6,1,2,5,4,3,0],![2,1,0,4,3,5,6]⟩,
  ⟨![0,5,3,4,2,6,1],![3,0,2,1,6,4,5]⟩,
  ⟨![0,4,1,5,2,6,3],![3,0,4,1,5,2,6]⟩,
  ⟨![0,4,3,5,6,2,1],![3,0,6,1,2,5,4]⟩,
  ⟨![3,4,1,6,2,5,0],![4,0,3,5,1,2,6]⟩,
  ⟨![6,3,2,4,5,1,0],![4,1,0,2,3,6,5]⟩,
  ⟨![3,2,1,5,4,6,0],![5,0,1,4,3,2,6]⟩]

private theorem wellFormed : ∀ k : Fin 21,
    Function.Injective (representatives k).point ∧ Function.Injective (representatives k).line ∧
    ∀ p l, I ((representatives k).point p) ((representatives k).line l) ↔ I p l := by
  decide +kernel

private theorem covers : ∀ a b : Fin 7, a ≠ b → ∃ k : Fin 21,
    ({(representatives k).point 5, (representatives k).point 6} : Finset (Fin 7)) = {a,b} := by
  decide +kernel

theorem pairSymmetry (a b : Fin 7) (ne : a ≠ b) : ∃ f g : Fin 7 → Fin 7,
    Function.Injective f ∧ Function.Injective g ∧ (∀ p l, I (f p) (g l) ↔ I p l) ∧
    ({f 5,f 6} : Finset (Fin 7)) = {a,b} := by
  obtain ⟨k,h⟩ := covers a b ne
  obtain ⟨f,g,inc⟩ := wellFormed k
  exact ⟨_,_,f,g,inc,h⟩

end PlaneStarTail.HeawoodSymmetry
