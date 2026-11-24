import PEqualNP.Outside.L_meta_245

namespace PlaneStarTail.DoubleStar
open PEqualNP.MetaComplexity

def terminal (n : ℕ) (x : Fin n → Bool) : Bool :=
  let b := fun k : ℕ => if hk : k<n then x ⟨k,hk⟩ else false
  (b 0 && b 1) || (b 1 && b 2) || (b 2 && b 3) || (b 1 && b 4) || (b 3 && b 5) || (b 3 && b 6) || b 7 || b 8 || b 9 || b 10 || b 11

-- Five essential singleton disjuncts and two unfinished point-stars with one common line.
theorem lower : ¬ HasCircuitSize 12 (terminal 12) 11 := by
  intro h12
  have h11 : HasCircuitSize 11 (terminal 11) 10 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 11 (terminal 12) false 10
      (by exact ⟨fun _ => false,by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h12
  have h10 : HasCircuitSize 10 (terminal 10) 9 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 10 (terminal 11) false 9
      (by exact ⟨fun _ => false,by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h11
  have h9 : HasCircuitSize 9 (terminal 9) 8 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 9 (terminal 10) false 8
      (by exact ⟨fun _ => false,by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h10
  have h8 : HasCircuitSize 8 (terminal 8) 7 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 8 (terminal 9) false 7
      (by exact ⟨fun _ => false,by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h9
  have h7 : HasCircuitSize 7 (terminal 7) 6 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 7 (terminal 8) false 6
      (by exact ⟨fun _ => false,by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h8
  have h6 : HasCircuitSize 6 (terminal 6) 5 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 6 (terminal 7) false 5
      (by exact ⟨fun i => decide (i.val=3),by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h7
  have h5 : HasCircuitSize 5 (terminal 5) 4 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 5 (terminal 6) false 4
      (by exact ⟨fun i => decide (i.val=3),by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h6
  have h4 : HasCircuitSize 4 (terminal 4) 3 :=
    PEqualNP.Outside.L_meta_245.Helpers.gate_elim 4 (terminal 5) false 3
      (by exact ⟨fun i => decide (i.val=1),by decide⟩)
      (by exact ⟨fun i => decide (i.val ≤ 1),fun _ => false,by decide⟩) h5
  have e : (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, i.val+1=j.val ∧ x i=true ∧ x j=true)) = terminal 4 := by
    funext x
    revert x
    decide +kernel
  have low := (PEqualNP.Outside.L_meta_245.path_size4 3).1 (e ▸ h4)
  omega

end PlaneStarTail.DoubleStar
