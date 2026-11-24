import Mathlib.Data.Bool.Basic

namespace Meta2081TwoStar

def out (a p l q b : Bool) : Bool :=
  let t := p && a
  let h := t || l
  let u := h && p
  let v := h || b
  let w := u || q
  w && v

theorem correct : ∀ a p l q b, out a p l q b =
    ((p && a) || (p && l) || (q && l) || (q && b)) := by decide

def conj (a b : Bool × Bool) : Bool × Bool :=
  (a.1 && b.1, (a.1 && b.2) || (a.2 && b.1))

def disj (a b : Bool × Bool) : Bool × Bool := (a.1 || b.1, a.2 || b.2)

def trace (a p l q b : Bool × Bool) : Bool × Bool :=
  let t := conj p a
  let h := disj t l
  let u := conj h p
  let v := disj h b
  let w := disj u q
  conj w v

theorem marked_flags :
    (trace (true,false) (false,true) (false,false) (false,false) (false,false)).2 = false ∧
    (trace (false,true) (true,false) (false,false) (false,false) (false,false)).2 = false := by decide

end Meta2081TwoStar
