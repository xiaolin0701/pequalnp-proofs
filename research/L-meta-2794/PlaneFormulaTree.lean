import Mathlib.Data.Bool.Basic

namespace PlaneFormula

inductive Tree (V : Type) where
  | input (v : V)
  | bot
  | join (s t : Tree V)
  | meet (s t : Tree V)

namespace Tree

def eval {V : Type} : Tree V → (V → Bool) → Bool
  | .input v, x => x v
  | .bot, _ => false
  | .join s t, x => s.eval x || t.eval x
  | .meet s t, x => s.eval x && t.eval x

def leaves {V : Type} : Tree V → Nat
  | .input _ | .bot => 1
  | .join s t | .meet s t => s.leaves + t.leaves

end Tree
end PlaneFormula
