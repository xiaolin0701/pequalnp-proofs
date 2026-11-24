import PEqualNP.Defs

namespace FanoK4Subgraph

def incident (p l : Fin 7) : Prop := p = l ∨ p = l+1 ∨ p = l+3

-- The order and orientation of these edges are those in the posted K4 subdivision.
def links : List (Fin 10 × Fin 10) :=
  [(0,4),(4,1),(0,5),(5,2),(0,6),(6,3),(1,7),(7,2),(1,8),(8,3),(2,9),(9,3)]

def embed : Fin 10 → Fin 14 := ![8,9,10,12,2,4,1,3,5,6]

def samePair (p l : Fin 7) (u v : Fin 10) : Prop :=
  (embed u = p.castAdd 7 ∧ embed v = Fin.natAdd 7 l) ∨
  (embed v = p.castAdd 7 ∧ embed u = Fin.natAdd 7 l)

-- Removing the three lines through point zero leaves exactly the subdivided K4.
set_option maxRecDepth 20000 in
theorem remaining_edges : ∀ p l : Fin 7, incident p l ∧ ¬incident 0 l ↔
    ∃ uv ∈ links, samePair p l uv.1 uv.2 := by
  unfold incident samePair
  decide +kernel

private theorem endpoint (u v : Fin 10) (h : (u,v) ∈ links) :
    ∃ p l, samePair p l u v := by
  exact (by unfold samePair; decide +kernel : ∀ u v : Fin 10, (u,v) ∈ links → ∃ p l, samePair p l u v) u v h

theorem partition (x : Fin 14 → Bool) :
    (∃ p l, incident p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ↔
    (∃ l p, incident 0 l ∧ incident p l ∧ x (Fin.castAdd 7 p) = true ∧
      x (Fin.natAdd 7 l) = true) ∨
    ∃ uv ∈ links, x (embed uv.1) = true ∧ x (embed uv.2) = true := by
  constructor
  · rintro ⟨p,l,hp,ha,hb⟩
    by_cases h : incident 0 l
    · exact Or.inl ⟨l,p,h,hp,ha,hb⟩
    obtain ⟨uv,hm,hs⟩ := (remaining_edges p l).mp ⟨hp,h⟩
    refine Or.inr ⟨uv,hm,?_⟩
    rcases hs with ⟨e,e'⟩ | ⟨e,e'⟩
    · simpa only [e,e'] using And.intro ha hb
    · simpa only [e,e'] using And.intro hb ha
  · rintro (⟨l,p,_,hp,ha,hb⟩ | ⟨⟨u,v⟩,hm,ha,hb⟩)
    · exact ⟨p,l,hp,ha,hb⟩
    obtain ⟨p,l,hs⟩ := endpoint u v hm
    refine ⟨p,l,((remaining_edges p l).mpr ⟨(u,v),hm,hs⟩).1,?_⟩
    rcases hs with ⟨e,e'⟩ | ⟨e,e'⟩
    · simpa only [← e,← e'] using And.intro ha hb
    · simpa only [← e,← e'] using And.intro hb ha

end FanoK4Subgraph
