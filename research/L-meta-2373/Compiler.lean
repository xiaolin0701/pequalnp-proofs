import PEqualNP.Defs
namespace Petersen2373
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev W := BitVec 1024

def build (s l : List W) := ∀ i : Fin l.length,
  ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val, l.get i = (a &&& b) ∨ l.get i = (a ||| b) ∨ l.get i = ~~~a

def generated (s : List W) (w : W) := ∃ a ∈ s, ∃ b ∈ s, w = (a &&& b) ∨ w = (a ||| b) ∨ w = ~~~a

theorem build_snoc (s l : List W) (w : W) :
    build s (l ++ [w]) ↔ build s l ∧ generated (s ++ l) w := by
  constructor
  · intro h
    constructor
    · intro i
      have hh := h ⟨i.val,by simp⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,List.take_append_of_le_length i.isLt.le] using hh
    · have hh := h ⟨l.length,by simp⟩
      simpa [generated,List.get_eq_getElem] using hh
  · rintro ⟨h,hw⟩ i
    by_cases hi : i.val < l.length
    · have hh := h ⟨i.val,hi⟩
      simpa only [List.get_eq_getElem,List.getElem_append_left hi,List.take_append_of_le_length hi.le] using hh
    · have hi' := i.isLt
      simp only [List.length_append,List.length_singleton] at hi'
      have e : i.val = l.length := by omega
      rw [List.get_eq_getElem,List.getElem_append_right (by omega),List.take_append_of_le_length (by omega)]
      simpa [e,generated] using hw

theorem compact (s l : List W) (h : build s l) :
    ∃ k : List W, k.length ≤ l.length ∧ k.Nodup ∧ (∀ w ∈ k, w ∉ s) ∧ build s k ∧
      ∀ w ∈ s ++ l, w ∈ s ++ k := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[],by simp,by simp,by simp,h,fun _ hh => hh⟩
  | append_singleton l w ih =>
    obtain ⟨hl,hw⟩ := (build_snoc s l w).mp h
    obtain ⟨k,hk,hn,hs,hwf,hcover⟩ := ih hl
    have old : ∀ z ∈ s ++ (l ++ [w]), z ∈ s ++ k ∨ z = w := by
      intro z hz
      rcases List.mem_append.mp (List.append_assoc s l [w] ▸ hz : z ∈ (s ++ l) ++ [w]) with h | h
      · exact Or.inl (hcover _ h)
      · exact Or.inr (by simpa using h)
    by_cases seen : w ∈ s ++ k
    · refine ⟨k,by simp; omega,hn,hs,hwf,?_⟩
      intro z hz
      rcases old z hz with hh | rfl
      · exact hh
      · exact seen
    · have nws : w ∉ s := fun he => seen (List.mem_append_left _ he)
      have nwk : w ∉ k := fun he => seen (List.mem_append_right _ he)
      refine ⟨k ++ [w],by simp; omega,?_,?_,?_,?_⟩
      · simp [List.nodup_append,hn]
        rintro a ha rfl
        exact nwk ha
      · intro z hz
        rcases List.mem_append.mp hz with hh | hh
        · exact hs z hh
        · simpa only [List.mem_singleton.mp hh] using nws
      · apply (build_snoc s k w).mpr
        obtain ⟨a,ha,b,hb,hop⟩ := hw
        exact ⟨hwf,a,hcover _ ha,b,hcover _ hb,hop⟩
      · intro z hz
        rw [← List.append_assoc]
        rcases old z hz with hh | rfl
        · exact List.mem_append_left _ hh
        · simp


private def bit (k : Fin 1024) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 1024) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 1024) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#1024)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl


set_option maxRecDepth 6000 in
theorem action_generated (w : List W) (g : Gate) (hg : legal g) :
    generated (([0,~~~0] : List W) ++ w) (action w g) := by
  let S : List W := [0,~~~0] ++ w
  have h0 : (0 : W) ∈ S := by simp [S]
  have h1 : (~~~(0 : W)) ∈ S := by simp [S]
  have hr (i : Nat) : w.getD i 0 ∈ S := by
    by_cases h : i < w.length
    · apply List.mem_append_right
      simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using List.getElem_mem (l := w) h
    · rw [List.getD_eq_default _ _ (by omega)]
      exact h0
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [action,List.head?_nil,List.head?_cons,
    List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,Option.map_none,Option.map_some,
    Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact ⟨0,h0,0,h0,.inr (.inl BitVec.or_zero.symm)⟩
    | exact ⟨0,h0,0,h0,.inr (.inr rfl)⟩
    | exact ⟨w.getD i 0,hr i,0,h0,.inr (.inl BitVec.or_zero.symm)⟩
    | exact ⟨w.getD i 0,hr i,0,h0,.inr (.inr rfl)⟩
    | exact ⟨w.getD i 0,hr i,w.getD j 0,hr j,.inl rfl⟩
    | exact ⟨w.getD i 0,hr i,w.getD j 0,hr j,.inr (.inl rfl)⟩

theorem execute (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (S P : List W)
    (hp : build ([0,~~~0] ++ S) P) :
    ∃ L : List W, L.length = P.length + gs.length ∧ build ([0,~~~0] ++ S) L ∧
      ∀ i : Fin 1024, gs.foldl step ((S ++ P).map (bit i)) = (S ++ L).map (bit i) := by
  induction gs generalizing P with
  | nil => exact ⟨P,by simp,hp,by simp⟩
  | cons g gs ih =>
    have hg' := hg g (by simp)
    let z := action (S ++ P) g
    have hp' : build ([0,~~~0] ++ S) (P ++ [z]) :=
      (build_snoc ..).mpr ⟨hp,by simpa only [List.append_assoc] using action_generated (S ++ P) g hg'⟩
    obtain ⟨L,hl,hw,he⟩ := ih (fun x hx => hg x (by simp [hx])) (P ++ [z]) hp'
    refine ⟨L,by simp at hl ⊢; omega,hw,?_⟩
    intro i; rw [List.foldl_cons,action_spec _ g hg' i]
    simpa only [List.append_assoc,z] using he i

theorem compiler (C : Circuit) (S : List (BitVec 1024)) (hc : FanInTwo C) :
    let B : List (BitVec 1024) := [0,~~~0] ++ S
    ∃ K : List (BitVec 1024), K.length ≤ C.size ∧ K.Nodup ∧ (∀ w ∈ K, w ∉ B) ∧
      (∀ i : Fin K.length, ∃ a ∈ B ++ K.take i.val, ∃ b ∈ B ++ K.take i.val,
        K.get i = (a &&& b) ∨ K.get i = (a ||| b) ∨ K.get i = ~~~a) ∧
      ∀ j : Nat, ∃ w ∈ B ++ K, ∀ i : Fin 1024,
        w.getLsbD i.val = (C.wires (S.map fun z => z.getLsbD i.val)).getD j false := by
  dsimp only
  obtain ⟨L,hl,hw,he⟩ := execute C.gates (by
    intro g hg; obtain ⟨ho,hn⟩ := hc g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ho,hn⟩) S []
      (by intro i; exact Fin.elim0 i)
  obtain ⟨K,hk,hd,hn,hb,hcover⟩ := compact _ _ hw
  refine ⟨K,by simpa [Circuit.size] using hk.trans hl.le,hd,hn,hb,?_⟩
  intro j
  let v := (S ++ L).getD j 0
  have hv : v ∈ ([0,~~~0] ++ S) ++ L := by
    by_cases hj : j < (S ++ L).length
    · rw [List.append_assoc]
      apply List.mem_append_right
      simpa [v,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using List.getElem_mem (l := S++L) hj
    · have hv0 : v = 0 := List.getD_eq_default _ _ (by omega)
      rw [hv0]; simp
  refine ⟨v,hcover v hv,?_⟩
  intro i
  have eval : C.wires (S.map (bit i)) = (S ++ L).map (bit i) := by
    change C.gates.foldl step (S.map (bit i)) = _
    simpa only [List.append_nil] using he i
  have fn : (fun z : W => z.getLsbD i.val) = bit i := by
    funext z
    exact BitVec.getLsbD_eq_getElem i.isLt
  rw [fn,eval,read_bit,BitVec.getLsbD_eq_getElem i.isLt]
  rfl

end Petersen2373
