import PEqualNP.Outside.L_meta_1046

namespace PEqualNP.Outside.SafeAndStar

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1046 (wiresFrom getD_wiresFrom_lt getD_wiresFrom_gate wiresFrom_mono length_wiresFrom)

abbrev PairInput {n : ℕ} (u v : Fin n) := List.ofFn (fun k : Fin n => decide (k = u ∨ k = v))
abbrev val (C : Circuit) {n : ℕ} (u v : Fin n) (i : ℕ) := (C.wires (PairInput u v)).getD i false
abbrev step (C : Circuit) (n i j : ℕ) := i < j ∧ ∃ k g, j = n+k ∧ C.gates[k]? = some g ∧ i ∈ g.inputs
abbrev below (C : Circuit) (n i j : ℕ) := Relation.TransGen (step C n) i j

private lemma primary {n} (C : Circuit) (u v p : Fin n) :
    val C u v p = decide (p = u ∨ p = v) := by
  change (wiresFrom C.gates _).getD _ _ = _
  rw [getD_wiresFrom_lt _ _ _ (by simp [PairInput])]
  rw [List.getD_eq_getElem _ _ (by simp [PairInput])]
  simp [PairInput]

private lemma atGate {n} (C : Circuit) (u v : Fin n) {k g} (hg : C.gates[k]? = some g) :
    val C u v (n+k) = g.op.eval (g.inputs.map fun i => if i < n+k then val C u v i else false) := by
  have hk : k < C.gates.length := by
    by_contra! h
    rw [List.getElem?_eq_none h] at hg
    contradiction
  have heq : C.gates[k] = g := by simpa [List.getElem?_eq_getElem hk] using hg
  simpa [PairInput, val, Circuit.wires, wiresFrom, heq] using getD_wiresFrom_gate C.gates (PairInput u v) k hk

/-- A true wire with no active AND in its predecessor cone traces to a
singleton endpoint. Invalid forward reads have value false in the gate. -/
theorem trace_single {n} (C : Circuit) (u v : Fin n)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (i : ℕ)
    (active : val C u v i = true)
    (quiet : ∀ k g, C.gates[k]? = some g → g.op = GateOp.and →
      (n+k = i ∨ below C n (n+k) i) → val C u v (n+k) = false) :
    ∃ p : Fin n, (p = u ∨ p = v) ∧ val C p p i = true := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hi : i < n
    · let p : Fin n := ⟨i, hi⟩
      have hp : val C u v p = true := active
      rw [primary] at hp
      exact ⟨p, of_decide_eq_true hp, by rw [show i = p.val from rfl, primary]; simp⟩
    · let k := i-n
      have hi' : n+k=i := by dsimp [k]; omega
      have hk : k < C.gates.length := by
        by_contra! h
        change (wiresFrom C.gates (PairInput u v)).getD i false = true at active
        rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp [PairInput]; omega)] at active
        contradiction
      let g := C.gates[k]
      have hg : C.gates[k]? = some g := List.getElem?_eq_getElem hk
      have hor : g.op = GateOp.or := by
        rcases mono g (List.getElem_mem hk) with ha | ho
        · have hfalse := quiet k g hg ha (Or.inl hi')
          rw [hi', active] at hfalse
          contradiction
        · exact ho
      rw [← hi', atGate C u v hg, hor] at active
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at active
      obtain ⟨_, ⟨j, hj, rfl⟩, hval⟩ := active
      split_ifs at hval with hlt
      · have hji : step C n j i := ⟨by omega, k, g, hi'.symm, hg, hj⟩
        obtain ⟨p, hp, hsingle⟩ := ih j (by omega) hval (by
          intro l f hf ha hanc
          apply quiet l f hf ha
          rcases hanc with hj' | hj'
          · exact Or.inr (hj' ▸ Relation.TransGen.single hji)
          · exact Or.inr (Relation.TransGen.tail hj' hji))
        refine ⟨p, hp, ?_⟩
        rw [← hi', atGate C p p hg, hor]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨true, ⟨j, hj, by rw [if_pos hlt]; exact hsingle⟩, rfl⟩

private lemma enlarge {n} (C : Circuit) (u v p : Fin n) (hp : p = u ∨ p = v)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (i : ℕ)
    (h : val C p p i = true) : val C u v i = true := by
  apply wiresFrom_mono C.gates mono (PairInput p p) (PairInput u v) (by simp [PairInput]) _ i h
  intro j hj
  by_cases hj' : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa [PairInput] using hj')] at hj ⊢
    simp [PairInput] at hj ⊢
    simpa [← hj] using hp
  · rw [List.getD_eq_default _ _ (by simpa [PairInput] using Nat.le_of_not_lt hj')] at hj
    contradiction

/-- The conjunct for a particular owned input in the official statement. -/
def owns {n} (C : Circuit) (k : ℕ) (u v : Fin n) : Prop :=
  val C u v (n+k) = true ∧ ∀ l g, C.gates[l]? = some g → g.op = GateOp.and →
    below C n (n+l) (n+k) → val C u v (n+l) = false

/-- If the current AND owns an edge, each of its input wires is already true
on a singleton endpoint. -/
private lemma trace_input {n} (C : Circuit) (u v : Fin n)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {k g} (hg : C.gates[k]? = some g) (ha : g.op = GateOp.and)
    (ho : owns C k u v) {j} (hj : j ∈ g.inputs) :
    j < n+k ∧ ∃ p, (p = u ∨ p = v) ∧ val C p p j = true := by
  have h := ho.1
  rw [atGate C u v hg, ha] at h
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at h
  have hjval := h _ ⟨j,hj,rfl⟩
  split_ifs at hjval with hjlt
  · refine ⟨hjlt, trace_single C u v mono j hjval ?_⟩
    intro l f hf hfop hanc
    apply ho.2 l f hf hfop
    have hstep : step C n j (n+k) := ⟨hjlt,k,g,rfl,hg,hj⟩
    rcases hanc with hj' | hj'
    · exact hj' ▸ Relation.TransGen.single hstep
    · exact Relation.TransGen.tail hj' hstep

/-- No-C4 graphs have no complete bipartite subgraph with both parts
containing two different vertices. The square-free hypothesis is written
exactly as in the official statement, and no triangle hypothesis is needed. -/
theorem cross_star {α : Type*} (G : SimpleGraph α) (A B : α → Prop)
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (cross : ∀ a b, A a → B b → G.Adj a b) {a₀ b₀} (ha : A a₀) (hb : B b₀) :
    (∀ a, A a → a=a₀) ∨ (∀ b, B b → b=b₀) := by
  by_cases h : ∀ a, A a → a=a₀
  · exact Or.inl h
  · push Not at h
    obtain ⟨a, ha', hne⟩ := h
    right
    intro b hb'
    exact (square a b a₀ b₀ (cross a b ha' hb') (cross a₀ b ha hb').symm
      (cross a₀ b₀ ha hb) (cross a b₀ ha' hb).symm).resolve_left hne

set_option maxHeartbeats 600000 in
theorem safe_owns_star {n} (G : SimpleGraph (Fin n)) (C : Circuit)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    {k g} (hg : C.gates[k]? = some g) (ha : g.op = GateOp.and) (hfan : g.inputs.length ≤ 2)
    (safe : ∀ u v, val C u v (n+k) = true → G.Adj u v)
    (nonempty : ∃ u v, G.Adj u v ∧ owns C k u v) :
    ∃ c, ∀ u v, G.Adj u v → owns C k u v → u=c ∨ v=c := by
  obtain ⟨u₀,v₀,_, ho₀⟩ := nonempty
  have hlist : ∀ p q : Fin n,
      (∀ j ∈ g.inputs, j < n+k ∧ val C p q j = true) → G.Adj p q := by
    intro p q h
    apply safe
    rw [atGate C p q hg, ha]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro _ ⟨j,hj,rfl⟩
    obtain ⟨hlt, hv⟩ := h j hj
    rw [if_pos hlt]; exact hv
  match hin : g.inputs with
  | [] =>
    exact (G.loopless.irrefl u₀ (hlist u₀ u₀ (by simp [hin]))).elim
  | [i] =>
    obtain ⟨hi, p, _, hp⟩ := trace_input C u₀ v₀ mono hg ha ho₀ (j := i) (by simp [hin])
    exact (G.loopless.irrefl p (hlist p p (by simpa [hin] using And.intro hi hp))).elim
  | i :: j :: tl =>
    have hlen : (i::j::tl).length ≤ 2 := hin ▸ hfan
    simp only [List.length_cons] at hlen
    have htl : tl=[] := List.length_eq_zero_iff.mp (by omega)
    have hin' : g.inputs=[i,j] := by simp [hin, htl]
    have hi : i ∈ g.inputs := by simp [hin']
    have hj : j ∈ g.inputs := by simp [hin']
    obtain ⟨hil,p₀,_,hp₀⟩ := trace_input C u₀ v₀ mono hg ha ho₀ hi
    obtain ⟨hjl,q₀,_,hq₀⟩ := trace_input C u₀ v₀ mono hg ha ho₀ hj
    have hcross : ∀ p q, val C p p i = true → val C q q j = true → G.Adj p q := by
      intro p q hp hq
      apply hlist
      intro t ht
      simp [hin'] at ht
      rcases ht with rfl | rfl
      · exact ⟨hil, enlarge C p q p (Or.inl rfl) mono _ hp⟩
      · exact ⟨hjl, enlarge C p q q (Or.inr rfl) mono _ hq⟩
    rcases cross_star G (fun p => val C p p i = true) (fun q => val C q q j = true)
        square hcross hp₀ hq₀ with h | h
    · refine ⟨p₀, ?_⟩
      intro u v _ ho
      obtain ⟨_,p,hp,hs⟩ := trace_input C u v mono hg ha ho hi
      have he := h p hs
      rcases hp with rfl | rfl
      · exact Or.inl he
      · exact Or.inr he
    · refine ⟨q₀, ?_⟩
      intro u v _ ho
      obtain ⟨_,q,hq,hs⟩ := trace_input C u v mono hg ha ho hj
      have he := h q hs
      rcases hq with rfl | rfl
      · exact Or.inl he
      · exact Or.inr he

/-- A thin input arm directly supplies a star center, even if the AND
accepts some nonedges and the graph has four-cycles. -/
theorem thin_input_star {n} (C : Circuit)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {k g} (hg : C.gates[k]? = some g) (ha : g.op = GateOp.and)
    {j} (hj : j ∈ g.inputs) {c : Fin n} (thin : ∀ p, val C p p j = true → p = c)
    {u v : Fin n} (ho : owns C k u v) : u = c ∨ v = c := by
  obtain ⟨_,p,hp,hv⟩ := trace_input C u v mono hg ha ho hj
  have he := thin p hv
  rcases hp with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

private lemma below_lt {C : Circuit} {n i j} (h : below C n i j) : i < j := by
  induction h with
  | single h => exact h.1
  | tail _ hs ih => exact lt_trans ih hs.1

/-- In every correct monotone circuit each graph edge is owned by at least
one AND. Choosing globally least active AND suffices. -/
theorem every_edge_owned {n} (G : SimpleGraph (Fin n)) (C : Circuit)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ u v, val C u v C.output = true ↔ G.Adj u v)
    {u v} (he : G.Adj u v) :
    ∃ k g, C.gates[k]? = some g ∧ g.op = GateOp.and ∧ owns C k u v := by
  classical
  let P (k : ℕ) := ∃ g, C.gates[k]? = some g ∧ g.op = GateOp.and ∧ val C u v (n+k) = true
  have hex : ∃ k, P k := by
    by_contra! hn
    obtain ⟨p, _, hp⟩ := trace_single C u v mono C.output ((correct u v).mpr he) (by
      intro k g hg ha _
      cases hh : val C u v (n+k) with
      | false => rfl
      | true => exact (hn k ⟨g, hg, ha, hh⟩).elim)
    exact G.loopless.irrefl p ((correct p p).mp hp)
  obtain ⟨g, hg, ha, hval⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, g, hg, ha, hval, ?_⟩
  intro l f hf hfa hbelow
  have hlt := below_lt hbelow
  cases hh : val C u v (n+l) with
  | false => rfl
  | true =>
    have hmin := Nat.find_min' hex (show P l from ⟨f,hf,hfa,hh⟩)
    omega

#print axioms safe_owns_star
#print axioms every_edge_owned
#print axioms thin_input_star

end PEqualNP.Outside.SafeAndStar
