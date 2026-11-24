import PEqualNP.Defs

namespace HeawoodResidual

-- Entries 0 through 17 form the six remaining three-line stars, in point
-- order: two ORs gather the neighboring lines and an AND selects the point.
-- The remaining five ORs join those six star outputs.
def residual23 : List ℕ := [
    264171595797922329, 288167337562522425, 56,
    281826563967027394, 288230119687211490, 448,
    265911111072622089, 283937879088049801, 3584,
    269151924997141508, 288221854669305124, 28672,
    256193051121782804, 274226965962791060, 229376,
    228319279526477906, 232840552945329234, 1835008,
    504, 4088, 32760,
    262136, 2097144]

theorem one_over_budget : let B : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752] ++ [191866593364673099, 193001360500003407, 7]
    ∃ R : List ℕ, R.length ≤ 23 ∧
      (∃ r ∈ B ++ R, (r ||| 7) = 2097151) ∧
      ∀ i : Fin R.length,
        ∃ a ∈ B ++ R.take i.val, ∃ b ∈ B ++ R.take i.val,
          R.get i = (a &&& b) ∨ R.get i = (a ||| b) := by
  refine ⟨residual23,by decide,⟨2097144,by decide,by decide⟩,?_⟩
  decide +kernel


-- Omitting the third line at point 1 saves one gate, at the cost of the
-- single edge (point 1, line 13), whose frontier bit index is 5.
def residual22ExceptOne : List ℕ := [
    264171595797922329, 24, 281826563967027394,
    288230119687211490, 448, 265911111072622089,
    283937879088049801, 3584, 269151924997141508,
    288221854669305124, 28672, 256193051121782804,
    274226965962791060, 229376, 228319279526477906,
    232840552945329234, 1835008, 472,
    4056, 32728, 262104,
    2097112]

theorem one_missing_edge : let B : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752] ++ [191866593364673099, 193001360500003407, 7]
    ∃ R : List ℕ, R.length ≤ 22 ∧
      (∃ r ∈ B ++ R, (r ||| 7) = 2097119) ∧
      ∀ i : Fin R.length,
        ∃ a ∈ B ++ R.take i.val, ∃ b ∈ B ++ R.take i.val,
          R.get i = (a &&& b) ∨ R.get i = (a ||| b) := by
  refine ⟨residual22ExceptOne,by decide,⟨2097112,by decide,by decide⟩,?_⟩
  decide +kernel

end HeawoodResidual
