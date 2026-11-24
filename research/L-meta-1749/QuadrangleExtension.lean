import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LineDegTest

namespace Plane1749

abbrev labels : Finset (Fin 13) := {0, 1, 3, 9}
abbrev Inc (p l : Fin 13) := p-l ∈ labels
abbrev Arc (P : Finset (Fin 13)) := ∀ l : Fin 13, (P.filter fun p => Inc p l).card ≤ 2
abbrev DualArc (L : Finset (Fin 13)) := ∀ p : Fin 13, (L.filter fun l => Inc p l).card ≤ 2
abbrev Miss (P : Finset (Fin 13)) := Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ P, ¬Inc p l)
abbrev Outside (L : Finset (Fin 13)) := Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ L, ¬Inc p l)

private theorem fail_triple (P : Finset (Fin 13)) (cap : Arc P) (a l u v w : Fin 13)
    (h : u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ Inc u l ∧ Inc v l ∧ Inc w l)
    (hu : a+u ∈ P) (hv : a+v ∈ P) (hw : a+w ∈ P) : False := by
  rcases h with ⟨uv,uw,vw,iu,iv,iw⟩
  have at' (t) (hit : t ∈ P) (i : Inc t (a+l)) : t ∈ P.filter (fun p => Inc p (a+l)) :=
    Finset.mem_filter.mpr ⟨hit,i⟩
  have inc' (t : Fin 13) (h : Inc t l) : Inc (a+t) (a+l) := by
    simpa only [Inc,add_sub_add_left_eq_sub] using h
  have sub : {a+u,a+v,a+w} ⊆ P.filter (fun p => Inc p (a+l)) := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨at' _ hu (inc' _ iu),at' _ hv (inc' _ iv),at' _ hw (inc' _ iw)⟩
  have count : ({a+u,a+v,a+w} : Finset (Fin 13)).card = 3 := by simp [uv,uw,vw]
  have := (Finset.card_le_card sub).trans (cap (a+l))
  omega

private theorem success_line (P : Finset (Fin 13)) (a l u v w z : Fin 13)
    (h : ¬Inc 0 l ∧ ∀ p, Inc p l → p=u ∨ p=v ∨ p=w ∨ p=z)
    (hu : a+u ∉ P) (hv : a+v ∉ P) (hw : a+w ∉ P) (hz : a+z ∉ P) :
    ∃ k ∈ Miss P, ¬Inc a k := by
  refine ⟨a+l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · intro p hp i
    have hit : Inc (p-a) l := by simpa only [Inc,sub_sub] using i
    have yes : a+(p-a) ∈ P := by simpa [add_comm a] using hp
    rcases h.2 (p-a) hit with e|e|e|e
    · exact hu (e ▸ yes)
    · exact hv (e ▸ yes)
    · exact hw (e ▸ yes)
    · exact hz (e ▸ yes)
  · simpa [Inc] using h.1

set_option maxHeartbeats 0 in
theorem outside_pencil (P : Finset (Fin 13)) (cap : Arc P) (a : Fin 13) : ∃ l ∈ Miss P, ¬Inc a l := by
  by_cases h1 : a+1 ∈ P
  · by_cases h2 : a+2 ∈ P
    · by_cases h4 : a+4 ∈ P
      · exact False.elim (fail_triple P cap a 1 1 2 4 (by decide) h1 h2 h4)
      · by_cases h10 : a+10 ∈ P
        · exact False.elim (fail_triple P cap a 1 1 2 10 (by decide) h1 h2 h10)
        · by_cases h3 : a+3 ∈ P
          · by_cases h5 : a+5 ∈ P
            · exact False.elim (fail_triple P cap a 2 2 3 5 (by decide) h2 h3 h5)
            · by_cases h9 : a+9 ∈ P
              · exact False.elim (fail_triple P cap a 0 1 3 9 (by decide) h1 h3 h9)
              · by_cases h8 : a+8 ∈ P
                · by_cases h12 : a+12 ∈ P
                  · exact False.elim (fail_triple P cap a 12 2 8 12 (by decide) h2 h8 h12)
                  · exact success_line P a 9 5 9 10 12 (by decide) h5 h9 h10 h12
                · by_cases h11 : a+11 ∈ P
                  · exact False.elim (fail_triple P cap a 2 2 3 11 (by decide) h2 h3 h11)
                  · exact success_line P a 8 4 8 9 11 (by decide) h4 h8 h9 h11
          · by_cases h6 : a+6 ∈ P
            · by_cases h7 : a+7 ∈ P
              · exact False.elim (fail_triple P cap a 6 2 6 7 (by decide) h2 h6 h7)
              · by_cases h8 : a+8 ∈ P
                · exact False.elim (fail_triple P cap a 5 1 6 8 (by decide) h1 h6 h8)
                · exact success_line P a 7 3 7 8 10 (by decide) h3 h7 h8 h10
            · by_cases h12 : a+12 ∈ P
              · by_cases h7 : a+7 ∈ P
                · exact False.elim (fail_triple P cap a 11 1 7 12 (by decide) h1 h7 h12)
                · by_cases h8 : a+8 ∈ P
                  · exact False.elim (fail_triple P cap a 12 2 8 12 (by decide) h2 h8 h12)
                  · exact success_line P a 7 3 7 8 10 (by decide) h3 h7 h8 h10
              · exact success_line P a 3 3 4 6 12 (by decide) h3 h4 h6 h12
    · by_cases h5 : a+5 ∈ P
      · by_cases h6 : a+6 ∈ P
        · exact False.elim (fail_triple P cap a 5 1 5 6 (by decide) h1 h5 h6)
        · by_cases h8 : a+8 ∈ P
          · exact False.elim (fail_triple P cap a 5 1 5 8 (by decide) h1 h5 h8)
          · by_cases h7 : a+7 ∈ P
            · by_cases h4 : a+4 ∈ P
              · exact False.elim (fail_triple P cap a 4 4 5 7 (by decide) h4 h5 h7)
              · by_cases h3 : a+3 ∈ P
                · by_cases h9 : a+9 ∈ P
                  · exact False.elim (fail_triple P cap a 0 1 3 9 (by decide) h1 h3 h9)
                  · by_cases h11 : a+11 ∈ P
                    · exact False.elim (fail_triple P cap a 2 3 5 11 (by decide) h3 h5 h11)
                    · exact success_line P a 8 4 8 9 11 (by decide) h4 h8 h9 h11
                · by_cases h12 : a+12 ∈ P
                  · exact False.elim (fail_triple P cap a 11 1 7 12 (by decide) h1 h7 h12)
                  · exact success_line P a 3 3 4 6 12 (by decide) h3 h4 h6 h12
            · by_cases h9 : a+9 ∈ P
              · by_cases h3 : a+3 ∈ P
                · exact False.elim (fail_triple P cap a 0 1 3 9 (by decide) h1 h3 h9)
                · by_cases h10 : a+10 ∈ P
                  · exact False.elim (fail_triple P cap a 9 5 9 10 (by decide) h5 h9 h10)
                  · exact success_line P a 7 3 7 8 10 (by decide) h3 h7 h8 h10
              · exact success_line P a 6 2 6 7 9 (by decide) h2 h6 h7 h9
      · by_cases h3 : a+3 ∈ P
        · by_cases h9 : a+9 ∈ P
          · exact False.elim (fail_triple P cap a 0 1 3 9 (by decide) h1 h3 h9)
          · by_cases h6 : a+6 ∈ P
            · by_cases h4 : a+4 ∈ P
              · exact False.elim (fail_triple P cap a 3 3 4 6 (by decide) h3 h4 h6)
              · by_cases h8 : a+8 ∈ P
                · exact False.elim (fail_triple P cap a 5 1 6 8 (by decide) h1 h6 h8)
                · by_cases h10 : a+10 ∈ P
                  · by_cases h11 : a+11 ∈ P
                    · exact False.elim (fail_triple P cap a 10 6 10 11 (by decide) h6 h10 h11)
                    · exact success_line P a 8 4 8 9 11 (by decide) h4 h8 h9 h11
                  · by_cases h12 : a+12 ∈ P
                    · exact False.elim (fail_triple P cap a 3 3 6 12 (by decide) h3 h6 h12)
                    · exact success_line P a 9 5 9 10 12 (by decide) h5 h9 h10 h12
            · by_cases h7 : a+7 ∈ P
              · by_cases h10 : a+10 ∈ P
                · exact False.elim (fail_triple P cap a 7 3 7 10 (by decide) h3 h7 h10)
                · by_cases h12 : a+12 ∈ P
                  · exact False.elim (fail_triple P cap a 11 1 7 12 (by decide) h1 h7 h12)
                  · exact success_line P a 9 5 9 10 12 (by decide) h5 h9 h10 h12
              · exact success_line P a 6 2 6 7 9 (by decide) h2 h6 h7 h9
        · by_cases h11 : a+11 ∈ P
          · by_cases h7 : a+7 ∈ P
            · exact False.elim (fail_triple P cap a 11 1 7 11 (by decide) h1 h7 h11)
            · by_cases h6 : a+6 ∈ P
              · by_cases h8 : a+8 ∈ P
                · exact False.elim (fail_triple P cap a 5 1 6 8 (by decide) h1 h6 h8)
                · by_cases h10 : a+10 ∈ P
                  · exact False.elim (fail_triple P cap a 10 6 10 11 (by decide) h6 h10 h11)
                  · exact success_line P a 7 3 7 8 10 (by decide) h3 h7 h8 h10
              · by_cases h4 : a+4 ∈ P
                · by_cases h9 : a+9 ∈ P
                  · exact False.elim (fail_triple P cap a 8 4 9 11 (by decide) h4 h9 h11)
                  · exact success_line P a 6 2 6 7 9 (by decide) h2 h6 h7 h9
                · by_cases h12 : a+12 ∈ P
                  · exact False.elim (fail_triple P cap a 11 1 11 12 (by decide) h1 h11 h12)
                  · exact success_line P a 3 3 4 6 12 (by decide) h3 h4 h6 h12
          · exact success_line P a 2 2 3 5 11 (by decide) h2 h3 h5 h11
  · by_cases h2 : a+2 ∈ P
    · by_cases h5 : a+5 ∈ P
      · by_cases h3 : a+3 ∈ P
        · exact False.elim (fail_triple P cap a 2 2 3 5 (by decide) h2 h3 h5)
        · by_cases h11 : a+11 ∈ P
          · exact False.elim (fail_triple P cap a 2 2 5 11 (by decide) h2 h5 h11)
          · by_cases h7 : a+7 ∈ P
            · by_cases h4 : a+4 ∈ P
              · exact False.elim (fail_triple P cap a 4 4 5 7 (by decide) h4 h5 h7)
              · by_cases h6 : a+6 ∈ P
                · exact False.elim (fail_triple P cap a 6 2 6 7 (by decide) h2 h6 h7)
                · by_cases h8 : a+8 ∈ P
                  · by_cases h12 : a+12 ∈ P
                    · exact False.elim (fail_triple P cap a 12 2 8 12 (by decide) h2 h8 h12)
                    · exact success_line P a 3 3 4 6 12 (by decide) h3 h4 h6 h12
                  · by_cases h9 : a+9 ∈ P
                    · exact False.elim (fail_triple P cap a 6 2 7 9 (by decide) h2 h7 h9)
                    · exact success_line P a 8 4 8 9 11 (by decide) h4 h8 h9 h11
            · by_cases h12 : a+12 ∈ P
              · by_cases h8 : a+8 ∈ P
                · exact False.elim (fail_triple P cap a 12 2 8 12 (by decide) h2 h8 h12)
                · by_cases h10 : a+10 ∈ P
                  · exact False.elim (fail_triple P cap a 9 5 10 12 (by decide) h5 h10 h12)
                  · exact success_line P a 7 3 7 8 10 (by decide) h3 h7 h8 h10
              · exact success_line P a 11 1 7 11 12 (by decide) h1 h7 h11 h12
      · by_cases h6 : a+6 ∈ P
        · by_cases h7 : a+7 ∈ P
          · exact False.elim (fail_triple P cap a 6 2 6 7 (by decide) h2 h6 h7)
          · by_cases h9 : a+9 ∈ P
            · exact False.elim (fail_triple P cap a 6 2 6 9 (by decide) h2 h6 h9)
            · by_cases h10 : a+10 ∈ P
              · by_cases h4 : a+4 ∈ P
                · exact False.elim (fail_triple P cap a 1 2 4 10 (by decide) h2 h4 h10)
                · by_cases h11 : a+11 ∈ P
                  · exact False.elim (fail_triple P cap a 10 6 10 11 (by decide) h6 h10 h11)
                  · by_cases h8 : a+8 ∈ P
                    · by_cases h12 : a+12 ∈ P
                      · exact False.elim (fail_triple P cap a 12 2 8 12 (by decide) h2 h8 h12)
                      · exact success_line P a 11 1 7 11 12 (by decide) h1 h7 h11 h12
                    · exact success_line P a 8 4 8 9 11 (by decide) h4 h8 h9 h11
              · by_cases h12 : a+12 ∈ P
                · by_cases h3 : a+3 ∈ P
                  · exact False.elim (fail_triple P cap a 3 3 6 12 (by decide) h3 h6 h12)
                  · by_cases h8 : a+8 ∈ P
                    · exact False.elim (fail_triple P cap a 12 2 8 12 (by decide) h2 h8 h12)
                    · exact success_line P a 7 3 7 8 10 (by decide) h3 h7 h8 h10
                · exact success_line P a 9 5 9 10 12 (by decide) h5 h9 h10 h12
        · by_cases h8 : a+8 ∈ P
          · by_cases h12 : a+12 ∈ P
            · exact False.elim (fail_triple P cap a 12 2 8 12 (by decide) h2 h8 h12)
            · by_cases h3 : a+3 ∈ P
              · by_cases h7 : a+7 ∈ P
                · exact False.elim (fail_triple P cap a 7 3 7 8 (by decide) h3 h7 h8)
                · by_cases h11 : a+11 ∈ P
                  · exact False.elim (fail_triple P cap a 2 2 3 11 (by decide) h2 h3 h11)
                  · exact success_line P a 11 1 7 11 12 (by decide) h1 h7 h11 h12
              · by_cases h4 : a+4 ∈ P
                · by_cases h9 : a+9 ∈ P
                  · exact False.elim (fail_triple P cap a 8 4 8 9 (by decide) h4 h8 h9)
                  · by_cases h10 : a+10 ∈ P
                    · exact False.elim (fail_triple P cap a 1 2 4 10 (by decide) h2 h4 h10)
                    · exact success_line P a 9 5 9 10 12 (by decide) h5 h9 h10 h12
                · exact success_line P a 3 3 4 6 12 (by decide) h3 h4 h6 h12
          · exact success_line P a 5 1 5 6 8 (by decide) h1 h5 h6 h8
    · by_cases h4 : a+4 ∈ P
      · by_cases h6 : a+6 ∈ P
        · by_cases h3 : a+3 ∈ P
          · exact False.elim (fail_triple P cap a 3 3 4 6 (by decide) h3 h4 h6)
          · by_cases h12 : a+12 ∈ P
            · exact False.elim (fail_triple P cap a 3 4 6 12 (by decide) h4 h6 h12)
            · by_cases h5 : a+5 ∈ P
              · by_cases h7 : a+7 ∈ P
                · exact False.elim (fail_triple P cap a 4 4 5 7 (by decide) h4 h5 h7)
                · by_cases h8 : a+8 ∈ P
                  · exact False.elim (fail_triple P cap a 5 5 6 8 (by decide) h5 h6 h8)
                  · by_cases h10 : a+10 ∈ P
                    · by_cases h11 : a+11 ∈ P
                      · exact False.elim (fail_triple P cap a 10 6 10 11 (by decide) h6 h10 h11)
                      · exact success_line P a 11 1 7 11 12 (by decide) h1 h7 h11 h12
                    · exact success_line P a 7 3 7 8 10 (by decide) h3 h7 h8 h10
              · by_cases h11 : a+11 ∈ P
                · by_cases h9 : a+9 ∈ P
                  · exact False.elim (fail_triple P cap a 8 4 9 11 (by decide) h4 h9 h11)
                  · by_cases h10 : a+10 ∈ P
                    · exact False.elim (fail_triple P cap a 10 6 10 11 (by decide) h6 h10 h11)
                    · exact success_line P a 9 5 9 10 12 (by decide) h5 h9 h10 h12
                · exact success_line P a 2 2 3 5 11 (by decide) h2 h3 h5 h11
        · by_cases h5 : a+5 ∈ P
          · by_cases h7 : a+7 ∈ P
            · exact False.elim (fail_triple P cap a 4 4 5 7 (by decide) h4 h5 h7)
            · by_cases h9 : a+9 ∈ P
              · by_cases h11 : a+11 ∈ P
                · exact False.elim (fail_triple P cap a 8 4 9 11 (by decide) h4 h9 h11)
                · by_cases h12 : a+12 ∈ P
                  · exact False.elim (fail_triple P cap a 9 5 9 12 (by decide) h5 h9 h12)
                  · exact success_line P a 11 1 7 11 12 (by decide) h1 h7 h11 h12
              · exact success_line P a 6 2 6 7 9 (by decide) h2 h6 h7 h9
          · by_cases h8 : a+8 ∈ P
            · by_cases h3 : a+3 ∈ P
              · by_cases h7 : a+7 ∈ P
                · exact False.elim (fail_triple P cap a 7 3 7 8 (by decide) h3 h7 h8)
                · by_cases h9 : a+9 ∈ P
                  · exact False.elim (fail_triple P cap a 8 4 8 9 (by decide) h4 h8 h9)
                  · exact success_line P a 6 2 6 7 9 (by decide) h2 h6 h7 h9
              · by_cases h11 : a+11 ∈ P
                · exact False.elim (fail_triple P cap a 8 4 8 11 (by decide) h4 h8 h11)
                · exact success_line P a 2 2 3 5 11 (by decide) h2 h3 h5 h11
            · exact success_line P a 5 1 5 6 8 (by decide) h1 h5 h6 h8
      · by_cases h10 : a+10 ∈ P
        · by_cases h3 : a+3 ∈ P
          · by_cases h7 : a+7 ∈ P
            · exact False.elim (fail_triple P cap a 7 3 7 10 (by decide) h3 h7 h10)
            · by_cases h6 : a+6 ∈ P
              · by_cases h11 : a+11 ∈ P
                · exact False.elim (fail_triple P cap a 10 6 10 11 (by decide) h6 h10 h11)
                · by_cases h12 : a+12 ∈ P
                  · exact False.elim (fail_triple P cap a 3 3 6 12 (by decide) h3 h6 h12)
                  · exact success_line P a 11 1 7 11 12 (by decide) h1 h7 h11 h12
              · by_cases h5 : a+5 ∈ P
                · by_cases h9 : a+9 ∈ P
                  · exact False.elim (fail_triple P cap a 9 5 9 10 (by decide) h5 h9 h10)
                  · exact success_line P a 6 2 6 7 9 (by decide) h2 h6 h7 h9
                · by_cases h8 : a+8 ∈ P
                  · exact False.elim (fail_triple P cap a 7 3 8 10 (by decide) h3 h8 h10)
                  · exact success_line P a 5 1 5 6 8 (by decide) h1 h5 h6 h8
          · by_cases h6 : a+6 ∈ P
            · by_cases h11 : a+11 ∈ P
              · exact False.elim (fail_triple P cap a 10 6 10 11 (by decide) h6 h10 h11)
              · by_cases h5 : a+5 ∈ P
                · by_cases h8 : a+8 ∈ P
                  · exact False.elim (fail_triple P cap a 5 5 6 8 (by decide) h5 h6 h8)
                  · by_cases h9 : a+9 ∈ P
                    · exact False.elim (fail_triple P cap a 9 5 9 10 (by decide) h5 h9 h10)
                    · exact success_line P a 8 4 8 9 11 (by decide) h4 h8 h9 h11
                · exact success_line P a 2 2 3 5 11 (by decide) h2 h3 h5 h11
            · by_cases h12 : a+12 ∈ P
              · by_cases h5 : a+5 ∈ P
                · exact False.elim (fail_triple P cap a 9 5 10 12 (by decide) h5 h10 h12)
                · by_cases h7 : a+7 ∈ P
                  · by_cases h8 : a+8 ∈ P
                    · exact False.elim (fail_triple P cap a 7 7 8 10 (by decide) h7 h8 h10)
                    · exact success_line P a 5 1 5 6 8 (by decide) h1 h5 h6 h8
                  · by_cases h9 : a+9 ∈ P
                    · exact False.elim (fail_triple P cap a 9 9 10 12 (by decide) h9 h10 h12)
                    · exact success_line P a 6 2 6 7 9 (by decide) h2 h6 h7 h9
              · exact success_line P a 3 3 4 6 12 (by decide) h3 h4 h6 h12
        · exact success_line P a 1 1 2 4 10 (by decide) h1 h2 h4 h10

private def sh (a : Fin 13) (S : Finset (Fin 13)) :=
  S.map (Equiv.addLeft a).toEmbedding

private lemma sh_mem (a x : Fin 13) (S : Finset (Fin 13)) :
    a+x ∈ sh a S ↔ x ∈ S := by simp [sh,Finset.mem_map_equiv]

private lemma arc_sh (a : Fin 13) (S : Finset (Fin 13)) : Arc (sh a S) ↔ Arc S := by
  have eq (l : Fin 13) : ((sh a S).filter fun p => Inc p (a+l)).card = (S.filter fun p => Inc p l).card := by
    simp [sh,Finset.filter_map,Function.comp_def,Inc]
  constructor
  · exact fun h l => eq l ▸ h (a+l)
  · intro h y
    obtain ⟨l,rfl⟩ := (Equiv.addLeft a).surjective y
    exact (eq l).trans_le (h l)

private lemma dual_sh (a : Fin 13) (S : Finset (Fin 13)) : DualArc (sh a S) ↔ DualArc S := by
  have eq (p : Fin 13) : ((sh a S).filter fun l => Inc (a+p) l).card = (S.filter fun l => Inc p l).card := by
    simp [sh,Finset.filter_map,Function.comp_def,Inc]
  constructor
  · exact fun h p => eq p ▸ h (a+p)
  · intro h y
    obtain ⟨p,rfl⟩ := (Equiv.addLeft a).surjective y
    exact (eq p).trans_le (h p)

private lemma outside_sh (a : Fin 13) (S : Finset (Fin 13)) : Outside (sh a S) = sh a (Outside S) := by
  ext x
  obtain ⟨p,rfl⟩ := (Equiv.addLeft a).surjective x
  change a+p ∈ Outside (sh a S) ↔ a+p ∈ sh a (Outside S)
  rw [sh_mem]
  simp only [Outside,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h l hx
    have := h (a+l) ((sh_mem a l S).mpr hx)
    simpa only [Inc,add_sub_add_left_eq_sub] using this
  · intro h y hy
    obtain ⟨l,rfl⟩ := (Equiv.addLeft a).surjective y
    have := h l ((sh_mem a l S).mp hy)
    change ¬Inc (a+p) (a+l)
    simpa only [Inc,add_sub_add_left_eq_sub] using this

private lemma miss_sh (a : Fin 13) (S : Finset (Fin 13)) : Miss (sh a S) = sh a (Miss S) := by
  ext x
  obtain ⟨l,rfl⟩ := (Equiv.addLeft a).surjective x
  change a+l ∈ Miss (sh a S) ↔ a+l ∈ sh a (Miss S)
  rw [sh_mem]
  simp only [Miss,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h p hx
    have := h (a+p) ((sh_mem a p S).mpr hx)
    simpa only [Inc,add_sub_add_left_eq_sub] using this
  · intro h y hy
    obtain ⟨p,rfl⟩ := (Equiv.addLeft a).surjective y
    have := h p ((sh_mem a p S).mp hy)
    change ¬Inc (a+p) (a+l)
    simpa only [Inc,add_sub_add_left_eq_sub] using this

private def GoodTriangle (T : Finset (Fin 13)) :=
    DualArc T → (Outside T).card = 4 ∧ Arc (Outside T) ∧ Miss (Outside T) = T

private lemma good_sh (a : Fin 13) (T) (h : GoodTriangle T) : GoodTriangle (sh a T) := by
  intro cap
  obtain ⟨sz,q,inv⟩ := h ((dual_sh _ _).mp cap)
  rw [outside_sh,miss_sh,inv]
  exact ⟨by simpa [sh] using sz,(arc_sh _ _).mpr q,rfl⟩

private theorem tri_1_2 : GoodTriangle {0,1,2} := by
  intro cap
  have hO : Outside {0,1,2} = {6,7,8,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_3 : GoodTriangle {0,1,3} := by
  intro cap
  have hO : Outside {0,1,3} = {5,7,8,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_4 : GoodTriangle {0,1,4} := by
  intro cap
  have hO : Outside {0,1,4} = {6,8,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_5 : GoodTriangle {0,1,5} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,1,5} : Finset (Fin 13))) cap).elim

private theorem tri_1_6 : GoodTriangle {0,1,6} := by
  intro cap
  have hO : Outside {0,1,6} = {5,8,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_7 : GoodTriangle {0,1,7} := by
  intro cap
  have hO : Outside {0,1,7} = {5,6,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_8 : GoodTriangle {0,1,8} := by
  intro cap
  have hO : Outside {0,1,8} = {5,6,7,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_9 : GoodTriangle {0,1,9} := by
  intro cap
  have hO : Outside {0,1,9} = {6,7,8,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_10 : GoodTriangle {0,1,10} := by
  intro cap
  have hO : Outside {0,1,10} = {5,7,8,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_1_11 : GoodTriangle {0,1,11} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,1,11} : Finset (Fin 13))) cap).elim

private theorem tri_1_12 : GoodTriangle {0,1,12} := by
  intro cap
  have hO : Outside {0,1,12} = {5,6,7,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_3 : GoodTriangle {0,2,3} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,2,3} : Finset (Fin 13))) cap).elim

private theorem tri_2_4 : GoodTriangle {0,2,4} := by
  intro cap
  have hO : Outside {0,2,4} = {6,8,10,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_5 : GoodTriangle {0,2,5} := by
  intro cap
  have hO : Outside {0,2,5} = {4,7,10,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_6 : GoodTriangle {0,2,6} := by
  intro cap
  have hO : Outside {0,2,6} = {4,8,10,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_7 : GoodTriangle {0,2,7} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,2,7} : Finset (Fin 13))) cap).elim

private theorem tri_2_8 : GoodTriangle {0,2,8} := by
  intro cap
  have hO : Outside {0,2,8} = {6,7,10,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_9 : GoodTriangle {0,2,9} := by
  intro cap
  have hO : Outside {0,2,9} = {4,6,7,8} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_10 : GoodTriangle {0,2,10} := by
  intro cap
  have hO : Outside {0,2,10} = {4,7,8,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_11 : GoodTriangle {0,2,11} := by
  intro cap
  have hO : Outside {0,2,11} = {4,6,8,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_2_12 : GoodTriangle {0,2,12} := by
  intro cap
  have hO : Outside {0,2,12} = {4,6,7,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_4 : GoodTriangle {0,3,4} := by
  intro cap
  have hO : Outside {0,3,4} = {2,8,10,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_5 : GoodTriangle {0,3,5} := by
  intro cap
  have hO : Outside {0,3,5} = {2,7,10,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_6 : GoodTriangle {0,3,6} := by
  intro cap
  have hO : Outside {0,3,6} = {5,8,10,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_7 : GoodTriangle {0,3,7} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,3,7} : Finset (Fin 13))) cap).elim

private theorem tri_3_8 : GoodTriangle {0,3,8} := by
  intro cap
  have hO : Outside {0,3,8} = {2,5,7,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_9 : GoodTriangle {0,3,9} := by
  intro cap
  have hO : Outside {0,3,9} = {2,7,8,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_10 : GoodTriangle {0,3,10} := by
  intro cap
  have hO : Outside {0,3,10} = {2,5,7,8} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_11 : GoodTriangle {0,3,11} := by
  intro cap
  have hO : Outside {0,3,11} = {2,5,8,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_3_12 : GoodTriangle {0,3,12} := by
  intro cap
  have hO : Outside {0,3,12} = {5,7,10,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_4_5 : GoodTriangle {0,4,5} := by
  intro cap
  have hO : Outside {0,4,5} = {2,10,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_4_6 : GoodTriangle {0,4,6} := by
  intro cap
  have hO : Outside {0,4,6} = {8,10,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_4_7 : GoodTriangle {0,4,7} := by
  intro cap
  have hO : Outside {0,4,7} = {2,6,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_4_8 : GoodTriangle {0,4,8} := by
  intro cap
  have hO : Outside {0,4,8} = {2,6,10,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_4_9 : GoodTriangle {0,4,9} := by
  intro cap
  have hO : Outside {0,4,9} = {2,6,8,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_4_10 : GoodTriangle {0,4,10} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,4,10} : Finset (Fin 13))) cap).elim

private theorem tri_4_11 : GoodTriangle {0,4,11} := by
  intro cap
  have hO : Outside {0,4,11} = {2,6,8,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_4_12 : GoodTriangle {0,4,12} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,4,12} : Finset (Fin 13))) cap).elim

private theorem tri_5_6 : GoodTriangle {0,5,6} := by
  intro cap
  have hO : Outside {0,5,6} = {4,10,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_5_7 : GoodTriangle {0,5,7} := by
  intro cap
  have hO : Outside {0,5,7} = {2,4,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_5_8 : GoodTriangle {0,5,8} := by
  intro cap
  have hO : Outside {0,5,8} = {2,7,10,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_5_9 : GoodTriangle {0,5,9} := by
  intro cap
  have hO : Outside {0,5,9} = {2,4,7,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_5_10 : GoodTriangle {0,5,10} := by
  intro cap
  have hO : Outside {0,5,10} = {2,4,7,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_5_11 : GoodTriangle {0,5,11} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,5,11} : Finset (Fin 13))) cap).elim

private theorem tri_5_12 : GoodTriangle {0,5,12} := by
  intro cap
  have hO : Outside {0,5,12} = {4,7,10,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_6_7 : GoodTriangle {0,6,7} := by
  intro cap
  have hO : Outside {0,6,7} = {4,5,11,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_6_8 : GoodTriangle {0,6,8} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,6,8} : Finset (Fin 13))) cap).elim

private theorem tri_6_9 : GoodTriangle {0,6,9} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,6,9} : Finset (Fin 13))) cap).elim

private theorem tri_6_10 : GoodTriangle {0,6,10} := by
  intro cap
  have hO : Outside {0,6,10} = {4,5,8,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_6_11 : GoodTriangle {0,6,11} := by
  intro cap
  have hO : Outside {0,6,11} = {4,5,8,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_6_12 : GoodTriangle {0,6,12} := by
  intro cap
  have hO : Outside {0,6,12} = {4,5,10,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_7_8 : GoodTriangle {0,7,8} := by
  intro cap
  have hO : Outside {0,7,8} = {2,5,6,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_7_9 : GoodTriangle {0,7,9} := by
  intro cap
  have hO : Outside {0,7,9} = {2,4,6,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_7_10 : GoodTriangle {0,7,10} := by
  intro cap
  have hO : Outside {0,7,10} = {2,4,5,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_7_11 : GoodTriangle {0,7,11} := by
  intro cap
  have hO : Outside {0,7,11} = {2,4,5,6} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_7_12 : GoodTriangle {0,7,12} := by
  intro cap
  have hO : Outside {0,7,12} = {4,5,6,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_8_9 : GoodTriangle {0,8,9} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,8,9} : Finset (Fin 13))) cap).elim

private theorem tri_8_10 : GoodTriangle {0,8,10} := by
  intro cap
  have hO : Outside {0,8,10} = {2,5,7,12} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_8_11 : GoodTriangle {0,8,11} := by
  intro cap
  have hO : Outside {0,8,11} = {2,5,6,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_8_12 : GoodTriangle {0,8,12} := by
  intro cap
  have hO : Outside {0,8,12} = {5,6,7,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_9_10 : GoodTriangle {0,9,10} := by
  intro cap
  have hO : Outside {0,9,10} = {2,4,7,8} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_9_11 : GoodTriangle {0,9,11} := by
  intro cap
  have hO : Outside {0,9,11} = {2,4,6,8} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_9_12 : GoodTriangle {0,9,12} := by
  intro cap
  have hO : Outside {0,9,12} = {4,6,7,11} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_10_11 : GoodTriangle {0,10,11} := by
  intro cap
  have hO : Outside {0,10,11} = {2,4,5,8} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem tri_10_12 : GoodTriangle {0,10,12} := by
  intro cap
  exact ((by decide : ¬DualArc ({0,10,12} : Finset (Fin 13))) cap).elim

private theorem tri_11_12 : GoodTriangle {0,11,12} := by
  intro cap
  have hO : Outside {0,11,12} = {4,5,6,10} := by decide
  rw [hO]
  exact ⟨by decide,by decide,by decide⟩

private theorem flip_good {i j : Fin 13} (h : GoodTriangle {0,i,j}) : GoodTriangle {0,j,i} := by
  rw [show ({0,j,i} : Finset (Fin 13)) = {0,i,j} by ext x; simp [or_comm]]
  exact h

private theorem norm_geom (b c : Fin 13) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c) : GoodTriangle {0,b,c} := by
  fin_cases b
  · exact (hb (by decide)).elim
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact (hbc (by decide)).elim
    · exact tri_1_2
    · exact tri_1_3
    · exact tri_1_4
    · exact tri_1_5
    · exact tri_1_6
    · exact tri_1_7
    · exact tri_1_8
    · exact tri_1_9
    · exact tri_1_10
    · exact tri_1_11
    · exact tri_1_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_2
    · exact (hbc (by decide)).elim
    · exact tri_2_3
    · exact tri_2_4
    · exact tri_2_5
    · exact tri_2_6
    · exact tri_2_7
    · exact tri_2_8
    · exact tri_2_9
    · exact tri_2_10
    · exact tri_2_11
    · exact tri_2_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_3
    · exact flip_good tri_2_3
    · exact (hbc (by decide)).elim
    · exact tri_3_4
    · exact tri_3_5
    · exact tri_3_6
    · exact tri_3_7
    · exact tri_3_8
    · exact tri_3_9
    · exact tri_3_10
    · exact tri_3_11
    · exact tri_3_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_4
    · exact flip_good tri_2_4
    · exact flip_good tri_3_4
    · exact (hbc (by decide)).elim
    · exact tri_4_5
    · exact tri_4_6
    · exact tri_4_7
    · exact tri_4_8
    · exact tri_4_9
    · exact tri_4_10
    · exact tri_4_11
    · exact tri_4_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_5
    · exact flip_good tri_2_5
    · exact flip_good tri_3_5
    · exact flip_good tri_4_5
    · exact (hbc (by decide)).elim
    · exact tri_5_6
    · exact tri_5_7
    · exact tri_5_8
    · exact tri_5_9
    · exact tri_5_10
    · exact tri_5_11
    · exact tri_5_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_6
    · exact flip_good tri_2_6
    · exact flip_good tri_3_6
    · exact flip_good tri_4_6
    · exact flip_good tri_5_6
    · exact (hbc (by decide)).elim
    · exact tri_6_7
    · exact tri_6_8
    · exact tri_6_9
    · exact tri_6_10
    · exact tri_6_11
    · exact tri_6_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_7
    · exact flip_good tri_2_7
    · exact flip_good tri_3_7
    · exact flip_good tri_4_7
    · exact flip_good tri_5_7
    · exact flip_good tri_6_7
    · exact (hbc (by decide)).elim
    · exact tri_7_8
    · exact tri_7_9
    · exact tri_7_10
    · exact tri_7_11
    · exact tri_7_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_8
    · exact flip_good tri_2_8
    · exact flip_good tri_3_8
    · exact flip_good tri_4_8
    · exact flip_good tri_5_8
    · exact flip_good tri_6_8
    · exact flip_good tri_7_8
    · exact (hbc (by decide)).elim
    · exact tri_8_9
    · exact tri_8_10
    · exact tri_8_11
    · exact tri_8_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_9
    · exact flip_good tri_2_9
    · exact flip_good tri_3_9
    · exact flip_good tri_4_9
    · exact flip_good tri_5_9
    · exact flip_good tri_6_9
    · exact flip_good tri_7_9
    · exact flip_good tri_8_9
    · exact (hbc (by decide)).elim
    · exact tri_9_10
    · exact tri_9_11
    · exact tri_9_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_10
    · exact flip_good tri_2_10
    · exact flip_good tri_3_10
    · exact flip_good tri_4_10
    · exact flip_good tri_5_10
    · exact flip_good tri_6_10
    · exact flip_good tri_7_10
    · exact flip_good tri_8_10
    · exact flip_good tri_9_10
    · exact (hbc (by decide)).elim
    · exact tri_10_11
    · exact tri_10_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_11
    · exact flip_good tri_2_11
    · exact flip_good tri_3_11
    · exact flip_good tri_4_11
    · exact flip_good tri_5_11
    · exact flip_good tri_6_11
    · exact flip_good tri_7_11
    · exact flip_good tri_8_11
    · exact flip_good tri_9_11
    · exact flip_good tri_10_11
    · exact (hbc (by decide)).elim
    · exact tri_11_12
  · fin_cases c
    · exact (hc (by decide)).elim
    · exact flip_good tri_1_12
    · exact flip_good tri_2_12
    · exact flip_good tri_3_12
    · exact flip_good tri_4_12
    · exact flip_good tri_5_12
    · exact flip_good tri_6_12
    · exact flip_good tri_7_12
    · exact flip_good tri_8_12
    · exact flip_good tri_9_12
    · exact flip_good tri_10_12
    · exact flip_good tri_11_12
    · exact (hbc (by decide)).elim

theorem triangle_geom2 (T : Finset (Fin 13)) (h : T.card = 3) : GoodTriangle T := by
  obtain ⟨a,b,c,ab,ac,bc,rfl⟩ := Finset.card_eq_three.mp h
  have norm := norm_geom (b-a) (c-a) (sub_ne_zero.mpr ab.symm) (sub_ne_zero.mpr ac.symm) (by simpa using bc)
  have := good_sh a _ norm
  simpa [sh,add_comm a] using this

private theorem two_lines : ∀ u v : Fin 13, u ≠ v → ∃! a : Fin 13, Inc a u ∧ Inc a v := by
  unfold ExistsUnique
  decide +kernel

private theorem self_inc (l : Fin 13) : Inc l l := by simp

private theorem extend_pair (P : Finset (Fin 13)) (cap : Arc P)
    (u v : Fin 13) (uv : u ≠ v) (hu : u ∈ Miss P) (hv : v ∈ Miss P) :
    ∃ T : Finset (Fin 13), {u,v} ⊆ T ∧ T ⊆ Miss P ∧ T.card = 3 ∧ DualArc T := by
  obtain ⟨a,hav,unique⟩ := two_lines u v uv
  obtain ⟨w,hw,wa⟩ := outside_pencil P cap a
  have wu : w ≠ u := fun e => wa (e ▸ hav.1)
  have wv : w ≠ v := fun e => wa (e ▸ hav.2)
  refine ⟨{u,v,w}, by simp, ?_, by simp [uv,wu.symm,wv.symm], ?_⟩
  · simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hu (And.intro hv hw)
  · intro p
    by_cases A : Inc p u <;> by_cases B : Inc p v <;> by_cases C : Inc p w
    · exact False.elim (wa ((unique p ⟨A,B⟩) ▸ C))
    all_goals simp [Inc] at A B C
    all_goals simp [Finset.filter_insert, Finset.filter_singleton, A,B,C, uv,wu.symm,wv.symm]

private theorem extend_from_line (P : Finset (Fin 13)) (cap : Arc P)
    (u : Fin 13) (hu : u ∈ Miss P) :
    ∃ T : Finset (Fin 13), u ∈ T ∧ T ⊆ Miss P ∧ T.card = 3 ∧ DualArc T := by
  obtain ⟨v,hv,hn⟩ := outside_pencil P cap u
  have uv : u ≠ v := fun e => hn (e ▸ self_inc u)
  obtain ⟨T,h,rest⟩ := extend_pair P cap u v uv hu hv
  exact ⟨T,h (by simp),rest⟩

private theorem extend_lines (P L : Finset (Fin 13)) (cap : Arc P)
    (sub : L ⊆ Miss P) (small : L.card ≤ 3) (dual : DualArc L) :
    ∃ T : Finset (Fin 13), L ⊆ T ∧ T ⊆ Miss P ∧ T.card = 3 ∧ DualArc T := by
  by_cases h3 : L.card = 3
  · exact ⟨L,Finset.Subset.rfl,sub,h3,dual⟩
  by_cases h2 : L.card = 2
  · obtain ⟨u,v,uv,rfl⟩ := Finset.card_eq_two.mp h2
    exact extend_pair P cap u v uv (sub (by simp)) (sub (by simp))
  by_cases h1 : L.card = 1
  · obtain ⟨u,rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨T,hu,rest⟩ := extend_from_line P cap u (sub (by simp))
    exact ⟨T,Finset.singleton_subset_iff.mpr hu,rest⟩
  have empty : L = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨u,hu,_⟩ := outside_pencil P cap 0
  obtain ⟨T,_,rest⟩ := extend_from_line P cap u hu
  exact ⟨T,empty ▸ Finset.empty_subset _,rest⟩


private theorem quad_geom2 (Q : Finset (Fin 13)) (h4 : Q.card = 4) (cap : Arc Q) :
    (Miss Q).card = 3 ∧ DualArc (Miss Q) := by
  obtain ⟨T,_,within,sz,dual⟩ := extend_lines Q ∅ cap (Finset.empty_subset _) (by simp) (by simp [DualArc])
  obtain ⟨szQ,_,back⟩ := triangle_geom2 T sz dual
  have inside : Q ⊆ Outside T := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl => (Finset.mem_filter.mp (within hl)).2 p hp⟩
  have eq := Finset.eq_of_subset_of_card_le inside ((szQ.trans h4.symm).le)
  rw [eq,back]
  exact ⟨sz,dual⟩

/-- Any nonincident partial assignment with points in general position and at
most three lines in general position extends to an official negative probe. -/
theorem extends_to_probe (P L : Finset (Fin 13)) (cap : Arc P)
    (sub : L ⊆ Miss P) (small : L.card ≤ 3) (dual : DualArc L) :
    ∃ Q : Finset (Fin 13), Q.card = 4 ∧ Arc Q ∧ P ⊆ Q ∧ L ⊆ Miss Q := by
  obtain ⟨T,hLT,hT,ht,ha⟩ := extend_lines P L cap sub small dual
  obtain ⟨h4,hQ,_⟩ := triangle_geom2 T ht ha
  refine ⟨Outside T,h4,hQ,?_,?_⟩
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl => (Finset.mem_filter.mp (hT hl)).2 p hp⟩
  · intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => (Finset.mem_filter.mp hp).2 l (hLT hl)⟩

/-- Complete characterization of the downward closure of the negative tests. -/
theorem probe_iff (P L : Finset (Fin 13)) :
    (∃ Q : Finset (Fin 13), Q.card = 4 ∧ Arc Q ∧ P ⊆ Q ∧ L ⊆ Miss Q) ↔
      Arc P ∧ L ⊆ Miss P ∧ L.card ≤ 3 ∧ DualArc L := by
  refine ⟨?_, fun ⟨a,b,c,d⟩ => extends_to_probe P L a b c d⟩
  rintro ⟨Q,h4,cap,hP,hL⟩
  obtain ⟨size,dual⟩ := quad_geom2 Q h4 cap
  refine ⟨fun l => (Finset.card_le_card (Finset.filter_subset_filter _ hP)).trans (cap l), ?_,
    (Finset.card_le_card hL).trans size.le, ?_⟩
  · intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => (Finset.mem_filter.mp (hL hl)).2 p (hP hp)⟩
  · intro p
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hL)).trans (dual p)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.LineDegTest

def input (P L : Finset (Fin 13)) :=
  (List.ofFn fun p : Fin 13 => decide (p ∈ P)) ++ List.ofFn fun l : Fin 13 => decide (l ∈ L)

private theorem get_block (P : Finset (Fin 13)) (i : ℕ) (h : i < 13) :
    (List.ofFn fun p : Fin 13 => decide (p ∈ P)).getD i false = true ↔ (⟨i,h⟩ : Fin 13) ∈ P := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn,decide_eq_true_eq]

private theorem input_le (P L Q M : Finset (Fin 13)) (hP : P ⊆ Q) (hL : L ⊆ M) :
    Le (input P L) (input Q M) := by
  intro i hi
  by_cases h : i < 13
  · simp only [input,List.getD_append _ _ _ _ (show i < (List.ofFn fun p : Fin 13 => decide (p ∈ P)).length by simpa using h),
      List.getD_append _ _ _ _ (show i < (List.ofFn fun p : Fin 13 => decide (p ∈ Q)).length by simpa using h)] at hi ⊢
    exact (get_block Q i h).2 (hP ((get_block P i h).1 hi))
  · by_cases h' : i < 26
    · have hi' : i-13 < 13 := by omega
      simp only [input,List.getD_append_right _ _ _ _ (show (List.ofFn fun p : Fin 13 => decide (p ∈ P)).length ≤ i by simp; omega),
        List.getD_append_right _ _ _ _ (show (List.ofFn fun p : Fin 13 => decide (p ∈ Q)).length ≤ i by simp; omega),
        List.length_ofFn] at hi ⊢
      exact (get_block M _ hi').2 (hL ((get_block L _ hi').1 hi))
    · rw [List.getD_eq_default _ _ (by simp [input]; omega)] at hi
      contradiction

/-- The actual circuit's negative output extends to every assignment from the
characterized domain, by monotonicity of the gate list. -/
theorem circuit_rejects (C : Circuit) (mono : Monotone2 C)
    (rejects : ∀ Q, Q.card = 4 → Arc Q → C.eval (input Q (Miss Q)) = false)
    (P L : Finset (Fin 13)) (cap : Arc P) (sub : L ⊆ Miss P)
    (small : L.card ≤ 3) (dual : DualArc L) : C.eval (input P L) = false := by
  obtain ⟨Q,sz,hq,hP,hL⟩ := extends_to_probe P L cap sub small dual
  have lift := W_mono C.gates (fun g hg => (mono g hg).1)
    (input P L) (input Q (Miss Q)) (by simp [input]) (input_le _ _ _ _ hP hL)
  cases h : C.eval (input P L) with
  | false => rfl
  | true =>
    have yes : C.eval (input Q (Miss Q)) = true := lift C.output h
    rw [rejects Q sz hq] at yes
    contradiction


/-- No same-color pair or nonincident two-color pair can make the output true. -/
theorem rejects_small (C : Circuit) (mono : Monotone2 C)
    (rejects : ∀ Q, Q.card = 4 → Arc Q → C.eval (input Q (Miss Q)) = false)
    (P L : Finset (Fin 13)) (hp : P.card ≤ 2) (hl : L.card ≤ 2)
    (disjoint : L ⊆ Miss P) : C.eval (input P L) = false :=
  circuit_rejects C mono rejects P L (fun _ => (Finset.card_filter_le _ _).trans hp)
    disjoint (by omega) (fun _ => (Finset.card_filter_le _ _).trans hl)

/-- On the input containing a single point and a single line, the circuit
computes their incidence exactly. -/
theorem pair_exact (C : Circuit) (mono : Monotone2 C)
    (accepts : ∀ p l, Inc p l → C.eval (input {p} {l}) = true)
    (rejects : ∀ Q, Q.card = 4 → Arc Q → C.eval (input Q (Miss Q)) = false)
    (p l : Fin 13) : C.eval (input {p} {l}) = true ↔ Inc p l := by
  refine ⟨?_,accepts p l⟩
  intro yes
  by_contra no
  have h := rejects_small C mono rejects {p} {l} (by simp) (by simp) (by simpa [Miss] using no)
  rw [yes] at h
  contradiction


/-- Two wrong pairs assigned to opposite sides of an AND must have a
cross-incidence if the AND vanishes on every official negative assignment. -/
theorem nested_cross (G H : Finset (Fin 13) → Finset (Fin 13) → Prop)
    (gmono : ∀ {P L Q M}, P ⊆ Q → L ⊆ M → G P L → G Q M)
    (hmono : ∀ {P L Q M}, P ⊆ Q → L ⊆ M → H P L → H Q M)
    (vanish : ∀ Q, Q.card = 4 → Arc Q → ¬(G Q (Miss Q) ∧ H Q (Miss Q)))
    (p l r s : Fin 13) (pl : ¬Inc p l) (rs : ¬Inc r s)
    (g : G {p} {l}) (h : H {r} {s}) : Inc p s ∨ Inc r l := by
  by_contra! cross
  have pp : ({p,r} : Finset (Fin 13)).card ≤ 2 := Finset.card_le_two
  have ll : ({l,s} : Finset (Fin 13)).card ≤ 2 := Finset.card_le_two
  have disjoint : ({l,s} : Finset (Fin 13)) ⊆ Miss {p,r} := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    simpa [Miss] using And.intro (And.intro pl cross.2) (And.intro cross.1 rs)
  obtain ⟨Q,sz,cap,pts,lns⟩ := extends_to_probe {p,r} {l,s}
    (fun _ => (Finset.card_filter_le _ _).trans pp) disjoint (by omega)
    (fun _ => (Finset.card_filter_le _ _).trans ll)
  apply vanish Q sz cap
  exact ⟨gmono (Finset.Subset.trans (by simp : {p} ⊆ ({p,r} : Finset _)) pts)
    (Finset.Subset.trans (by simp : {l} ⊆ ({l,s} : Finset _)) lns) g,
    hmono (Finset.Subset.trans (by simp : {r} ⊆ ({p,r} : Finset _)) pts)
      (Finset.Subset.trans (by simp : {s} ⊆ ({l,s} : Finset _)) lns) h⟩

end Plane1749
