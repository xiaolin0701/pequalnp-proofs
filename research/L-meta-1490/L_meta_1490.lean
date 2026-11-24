import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1490_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- The wire evaluation lemmas follow the list folds in L-meta-1046.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp


variable {n : ℕ} {C : Circuit}

lemma gate_eq {j} (hj : j < C.gates.length) : gateAt C j = C.gates[j] :=
  List.getD_eq_getElem _ _ hj

lemma gate_mem {j} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gate_eq hj]
  exact List.getElem_mem hj

lemma input_value (x : Fin n → Bool) (i : Fin n) : wireVal n C i x = x i := by
  change (wiresFrom C.gates (List.ofFn x)).getD i false = _
  rw [getD_wiresFrom_lt _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma too_far (x : Fin n → Bool) {w} (hw : n+C.gates.length ≤ w) :
    wireVal n C w x = false := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = false
  apply List.getD_eq_default
  simpa only [length_wiresFrom, List.length_ofFn] using hw

lemma at_gate (ao : IsAO2 n C) (x : Fin n → Bool) {j} (hj : j < C.gates.length) :
    wireVal n C (n+j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map (fun i => wireVal n C i x)) := by
  have h := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, ← gate_eq hj] at h
  change (wiresFrom _ _).getD _ _ = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (ao.2.1 j hj i hi)]
  rfl

lemma or_history (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    ∃ tail, gs.foldl (orStep n) cs = cs ++ tail ∧ tail.length = gs.length := by
  letI : DecidableEq GateOp := gateOpDecEq
  induction gs generalizing cs with
  | nil => exact ⟨[],by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨tail, h, hl⟩ := ih (orStep n cs g)
    let row := cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n+cs.length))).flatMap
        (fun w => cs.getD (w-n) []) else [])
    change gs.foldl (orStep n) (cs ++ [row]) = (cs ++ [row]) ++ tail at h
    refine ⟨row :: tail, ?_, by simp [hl]⟩
    change gs.foldl (orStep n) (cs ++ [row]) = _
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h

lemma sets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  obtain ⟨tail,h,hl⟩ := or_history n C.gates []
  simpa [orSets,h] using hl

lemma reaches_valid {w h} (hr : OrReaches n C w h) : w < n + C.gates.length := by
  by_contra! hw
  obtain ⟨_, hm⟩ := hr
  rw [List.getD_eq_default _ _ (by rw [sets_length]; omega)] at hm
  exact List.not_mem_nil hm

lemma reaches_at {j h} (hj : j < C.gates.length) :
    OrReaches n C (n+j) h ↔
      h=j ∨ (gateAt C j).op = GateOp.or ∧ ∃ w ∈ (gateAt C j).inputs,
        w < n+j ∧ OrReaches n C w h := by
  letI : DecidableEq GateOp := gateOpDecEq
  let pre := (C.gates.take j).foldl (orStep n) []
  have hpre : pre.length=j := by
    obtain ⟨tail, ht, hl⟩ := or_history n (C.gates.take j) []
    simpa [pre, ht, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using hl
  let child := fun w : ℕ => pre.getD (w-n) []
  let row := j :: (if (gateAt C j).op=GateOp.or then
    ((gateAt C j).inputs.filter fun w => decide (n ≤ w ∧ w < n+j)).flatMap child else [])
  have split : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    have hs := (List.take_append_drop j C.gates).symm
    rw [List.drop_eq_getElem_cons hj] at hs
    exact hs
  obtain ⟨tail, ht, _⟩ := or_history n (C.gates.drop (j+1)) (orStep n pre (gateAt C j))
  have htotal : orSets n C = (pre ++ [row]) ++ tail := by
    unfold orSets
    conv_lhs => rw [split, List.foldl_append, List.foldl_cons]
    rw [← gate_eq hj]
    change (C.gates.drop (j+1)).foldl _ (orStep n pre _) = _
    rw [ht]
    simp only [orStep, hpre, row, child]
  have old {w} (hl : n ≤ w) (hu : w < n+j) :
      h ∈ child w ↔ OrReaches n C w h := by
    unfold OrReaches
    rw [htotal, List.append_assoc, List.getD_append _ _ _ _ (by omega : w-n < pre.length)]
    exact ⟨fun h => ⟨hl,h⟩, And.right⟩
  have current : (orSets n C).getD j []=row := by
    rw [htotal, List.getD_append _ _ _ _ (by simp [hpre])]
    rw [← hpre]
    simp
  unfold OrReaches
  rw [Nat.add_sub_cancel_left, current]
  change (_ ∧ h ∈ row) ↔ _
  simp only [Nat.le_add_right, true_and, row, List.mem_cons]
  by_cases ho : (gateAt C j).op = GateOp.or
  · simp only [ho, if_true, true_and, List.mem_flatMap, List.mem_filter,
      decide_eq_true_iff]
    constructor
    · rintro (e | ⟨w, ⟨hw, hl, hu⟩, hh⟩)
      · exact .inl e
      · exact .inr ⟨w, hw, hu, (old hl hu).mp hh⟩
    · rintro (e | ⟨w, hw, hu, hh⟩)
      · exact .inl e
      · exact .inr ⟨w, ⟨hw, hh.1, hu⟩, (old hh.1 hu).mpr hh⟩
  · simp [ho]


lemma or_up (ao : IsAO2 n C) {j w} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hw : w ∈ (gateAt C j).inputs)
    (x : Fin n → Bool) (hx : wireVal n C w x = true) : wireVal n C (n+j) x = true := by
  rw [at_gate ao x hj, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  exact ⟨true, ⟨w, hw, hx⟩, rfl⟩

lemma reach_info (ao : IsAO2 n C) {w h} (hr : OrReaches n C w h) :
    n+h ≤ w ∧ ∀ x, gateVal n C h x = true → wireVal n C w x = true := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn := hr.1
    obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
    have hw := reaches_valid hr
    have hj : j<C.gates.length := by omega
    rcases (reaches_at hj).mp hr with rfl | ⟨hop, t, ht, hlt, hrt⟩
    · exact ⟨by omega, fun _ hh => hh⟩
    · obtain ⟨ho, hval⟩ := ih t hlt hrt
      exact ⟨by omega, fun x hx => or_up ao hj hop ht x (hval x hx)⟩

lemma or_in_up (ao : IsAO2 n C) {w} {i : Fin n} (hi : i ∈ orIn n C w)
    (x : Fin n → Bool) (hx : x i = true) : wireVal n C w x = true := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  rcases (Finset.mem_filter.mp hi).2 with eq | ⟨k,hk,hr,hop,hm⟩
  · rw [← eq, input_value, hx]
  · apply (reach_info ao hr).2 x
    exact or_up ao hk hop hm x (by rw [input_value, hx])

lemma trace_on (ao : IsAO2 n C) {w} {x : Fin n → Bool} (hx : wireVal n C w x = true) :
    (∃ i ∈ orIn n C w, x i = true) ∨ ∃ h < C.gates.length,
      (gateAt C h).op = GateOp.and ∧ OrReaches n C w h ∧ gateVal n C h x = true := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let i : Fin n := ⟨w,hw⟩
      have hval : wireVal n C i x = true := hx
      exact .inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩,
        (input_value x i).symm.trans hval⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j<C.gates.length := by
        by_contra! h
        rw [too_far x (by omega)] at hx
        contradiction
      have here : OrReaches n C (n+j) j := (reaches_at hj).mpr (.inl rfl)
      rcases ao.1 _ (gate_mem hj) with ha | ho
      · exact .inr ⟨j,hj,ha,here,hx⟩
      · rw [at_gate ao x hj, ho] at hx
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx
        obtain ⟨_, ⟨t,ht,rfl⟩,htv⟩ := hx
        have hlt := ao.2.1 j hj t ht
        have lift {h} (hr : OrReaches n C t h) : OrReaches n C (n+j) h :=
          (reaches_at hj).mpr (.inr ⟨ho,t,ht,hlt,hr⟩)
        rcases ih t hlt htv with ⟨i,hi,hxi⟩ | ⟨h,hh,hand,hr,hval⟩
        · left
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩, hxi⟩
          rcases (Finset.mem_filter.mp hi).2 with hti | ⟨g,hg,hreach,hop,hm⟩
          · exact ⟨j,hj,here,ho,hti ▸ ht⟩
          · exact ⟨g,hg,lift hreach,hop,hm⟩
        · exact .inr ⟨h,hh,hand,lift hr,hval⟩

lemma opnd_mem (ao : IsAO2 n C) {a} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  have hl := ao.2.2 _ (gate_mem ha)
  have hi : b.val < (gateAt C a).inputs.length := by omega
  rw [opnd, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

lemma and_arms (ao : IsAO2 n C) {a} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, wireVal n C (opnd C a b) x = true := by
  change wireVal n C (n+a) x = true ↔ _
  rw [at_gate ao x ha, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h b
    exact h _ ⟨_, opnd_mem ao ha b, rfl⟩
  · rintro h _ ⟨t,ht,rfl⟩
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem ht
    have hl := ao.2.2 _ (gate_mem ha)
    have hz := h ⟨i,by omega⟩
    simpa only [opnd, List.getD_eq_getElem _ _ hi, he] using hz

lemma graph_pair (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_iff, pairInput]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u,v,h,Or.inl rfl,Or.inr rfl⟩


variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma top_mem {a} : a ∈ tops G C ↔
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]

lemma top_cross (ao : IsAO2 n C) {a} (ha : a ∈ tops G C) {u v : Fin n}
    (hu : u ∈ side (n:=n) C a 0) (hv : v ∈ side (n:=n) C a 1) : G.Adj u v := by
  obtain ⟨hl,ha,hs⟩ := top_mem.mp ha
  apply (graph_pair G u v).mp
  apply hs
  apply (and_arms ao hl ha _).mpr
  intro b
  fin_cases b
  · apply or_in_up ao hu
    simp [pairInput]
  · apply or_in_up ao hv
    simp [pairInput]

lemma side_bound (cycle : NoFourCycle G) {A B : Finset (Fin n)}
    (h : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra! bad
  obtain ⟨u,hu,w,hw,hn⟩ := Finset.one_lt_card.mp bad.1
  have incl : B ⊆ Finset.univ.filter (fun z => G.Adj u z ∧ G.Adj w z) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h u hu v hv, h w hw v hv⟩
  exact (Nat.not_lt_of_ge ((Finset.card_le_card incl).trans (cycle u w hn))) bad.2

lemma output_value (hc : circuitFun n C = graphFun G ∅) (x : Fin n → Bool) :
    wireVal n C C.output x = graphFun G ∅ x := congrFun hc x

lemma top_exists (ao : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅) {u v} (he : G.Adj u v) :
    ∃ a, a ∈ tops G C ∧ gateVal n C a (pairInput u v) = true := by
  have hval : wireVal n C C.output (pairInput u v) = true :=
    (output_value hc _).trans ((graph_pair G u v).mpr he)
  rcases trace_on ao hval with ⟨i,hi,_⟩ | ⟨a,ha,hop,hr,hv⟩
  · have hh := or_in_up ao hi (pairInput i i) (by simp [pairInput])
    rw [output_value hc] at hh
    exact (G.loopless.irrefl _ ((graph_pair G i i).mp hh)).elim
  · refine ⟨a,top_mem.mpr ⟨ha,hop,?_⟩,hv⟩
    intro y hy
    rw [← output_value hc]
    exact (reach_info ao hr).2 _ hy

lemma remaining (ao : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) h ∧
      gateVal n C h (pairInput u v) = true := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨hedge, hstar⟩ := Finset.mem_sdiff.mp he
  have huv : G.Adj u v := by simpa using hedge
  let P (a : ℕ) := a ∈ tops G C ∧ gateVal n C a (pairInput u v) = true
  have hex : ∃ a, P a := top_exists ao hc huv
  let a := Nat.find hex
  have hP : P a := Nat.find_spec hex
  obtain ⟨hal, hop, _⟩ := top_mem.mp hP.1
  have arms := (and_arms ao hal hop _).mp hP.2
  have witness (b : Fin 2) : (∃ i ∈ side (n:=n) C a b, i=u ∨ i=v) ∨
      ∃ h ∈ junk G C, OrReaches n C (opnd C a b) h ∧ gateVal n C h (pairInput u v) = true := by
    rcases trace_on ao (arms b) with ⟨i,hi,hxi⟩ | ⟨h,hl,ha,hr,hval⟩
    · exact .inl ⟨i,hi,of_decide_eq_true hxi⟩
    · have hprior := (reach_info ao hr).1
      have hread := ao.2.1 a hal _ (opnd_mem ao hal b)
      have hn : ¬ BelowF G C h := by
        intro hs
        have hm := Nat.find_min' hex (show P h from ⟨top_mem.mpr ⟨hl,ha,hs⟩,hval⟩)
        change a ≤ h at hm
        omega
      unfold BelowF at hn
      push Not at hn
      obtain ⟨x,hx,hy⟩ := hn
      have hy' : graphFun G ∅ x = false := by
        cases hh : graphFun G ∅ x with
        | false => rfl
        | true => exact (hy hh).elim
      have hjunk : h ∈ junk G C := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr hl, ha, hl, x, hx, hy'⟩
      exact .inr ⟨h,hjunk,hr,hval⟩
  rcases witness 0 with ⟨p,hp,hu⟩ | ⟨h,hh,hr,hv⟩
  · rcases witness 1 with ⟨q,hq,hv⟩ | ⟨h,hh,hr,hv⟩
    · exfalso
      have hne := (top_cross ao hP.1 hp hq).ne
      have eq : s(p,q)=s(u,v) := by
        rw [Sym2.eq_iff]
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all
      apply hstar
      apply Finset.mem_biUnion.mpr
      refine ⟨a,hP.1,Finset.mem_image.mpr ⟨(p,q), Finset.mem_product.mpr ⟨hp,hq⟩,eq⟩⟩
    · exact ⟨a,hP.1,1,h,hh,hP.2,hr,hv⟩
  · exact ⟨a,hP.1,0,h,hh,hP.2,hr,hv⟩

end PEqualNP.Outside.L_meta_1490_aux

open PEqualNP.Outside.L_meta_1490_aux
theorem PEqualNP.Outside.L_meta_1490 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    (∀ a ∈ PEqualNP.TopForm.tops G C,
      Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧
      (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧
      ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧
    ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C →
      ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C,
        PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧
        PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true := by
  intro n G _ C hcycle _ hleast _
  have ao := hleast.1
  constructor
  · intro a ha
    have cross := fun u hu v hv => top_cross ao ha (u:=u) (v:=v) hu hv
    refine ⟨Finset.disjoint_left.mpr ?_, cross, side_bound hcycle cross⟩
    intro x hl hr
    exact G.loopless.irrefl x (cross x hl x hr)
  · exact remaining ao hleast.2.1
