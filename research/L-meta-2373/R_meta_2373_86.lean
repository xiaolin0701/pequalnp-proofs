import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2373_86
    (compile : ∀ (C : Circuit) (S : List (BitVec 1024)), FanInTwo C →
    let B : List (BitVec 1024) := [0,~~~0] ++ S
    ∃ K : List (BitVec 1024), K.length ≤ C.size ∧ K.Nodup ∧ (∀ w ∈ K, w ∉ B) ∧
      (∀ i : Fin K.length, ∃ a ∈ B ++ K.take i.val, ∃ b ∈ B ++ K.take i.val,
        K.get i = (a &&& b) ∨ K.get i = (a ||| b) ∨ K.get i = ~~~a) ∧
      ∀ j : Nat, ∃ w ∈ B ++ K, ∀ i : Fin 1024,
        w.getLsbD i.val = (C.wires (S.map fun z => z.getLsbD i.val)).getD j false)
    (exclude : let S : List (BitVec 1024) := List.ofFn (fun j : Fin 10 => BitVec.ofNat 1024 (((2^1024-1) / (2^(2^((List.finRange 10).idxOf j))+1)) * 2^(2^((List.finRange 10).idxOf j))))
      let B : List (BitVec 1024) := [0,~~~0] ++ S
      let f := fun i => S.getD i 0
      let T := (List.range 5).foldl (fun v i => v ||| (f i &&& f ((i+1)%5)) ||| (f i &&& f (5+i)) ||| (f (5+i) &&& f (5+(i+2)%5))) 0
      ∀ P : List (BitVec 1024), P.length ≤ 17 → P.Nodup → (∀ w ∈ P, w ∉ B) →
        (∀ i : Fin P.length, ∃ b ∈ B ++ P.take i.val, ∃ c ∈ B ++ P.take i.val, P.get i = (b &&& c) ∨ P.get i = (b ||| c) ∨ P.get i = ~~~b) →
        let A := B ++ P
        ∀ u ∈ A, ∀ c ∈ A, ∀ d ∈ A, ∀ v ∈ [c &&& d,c ||| d,~~~c], u ≠ T → v ≠ T → u ||| v ≠ T) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  let W := BitVec 1024
  let build := fun (B P : List W) => ∀ i : Fin P.length, ∃ b ∈ B ++ P.take i.val, ∃ c ∈ B ++ P.take i.val, P.get i = (b &&& c) ∨ P.get i = (b ||| c) ∨ P.get i = ~~~b
  have cut (B K : List W) (hbuild : build B K) (hd : K.Nodup)
      (hs : ∀ w ∈ K, w ∉ B) (a b : W) (ha : a ∈ B ++ K) (hb : b ∈ B ++ K)
      (diff : a ≠ b) (fresh : ¬ (a ∈ B ∧ b ∈ B)) :
      ∃ P : List W, P.length < K.length ∧ P.Nodup ∧ (∀ w ∈ P, w ∉ B) ∧ build B P ∧
        ∃ u ∈ B ++ P, ∃ c ∈ B ++ P, ∃ d ∈ B ++ P, ∃ v ∈ [c &&& d,c ||| d,~~~c],
        (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
    induction K using List.reverseRecOn with
    | nil => exact False.elim (fresh ⟨by simpa only [List.append_nil] using ha,by simpa only [List.append_nil] using hb⟩)
    | append_singleton K w ih =>
      have nd : K.Nodup := (List.nodup_append.mp hd).1
      have ss : ∀ v ∈ K,v ∉ B := fun v hv => hs v (List.mem_append_left _ hv)
      have prior : build B K := by
        intro i
        have h := hbuild ⟨i.val,by simp only [List.length_append,List.length_singleton]; omega⟩
        simpa only [List.get_eq_getElem,List.getElem_append_left i.isLt,
          List.take_append_of_le_length i.isLt.le] using h
      have last : ∃ c ∈ B ++ K, ∃ d ∈ B ++ K, w ∈ [c &&& d,c ||| d,~~~c] := by
        have h := hbuild ⟨K.length,by simp⟩
        simpa [List.get_eq_getElem, List.getElem_append_right, List.take_append] using h
      have subs {v : W} (hv : v ∈ B ++ (K ++ [w])) (ne : v ≠ w) : v ∈ B ++ K := by
        simpa [← List.append_assoc,ne] using hv
      by_cases ac : a = w
      · obtain ⟨c,hc,d,hh,hv⟩ := last
        exact ⟨K,by simp,nd,ss,prior,b,subs hb (fun eq => diff (ac.trans eq.symm)),c,hc,d,hh,w,hv,.inr ⟨rfl,ac.symm⟩⟩
      by_cases bc : b = w
      · obtain ⟨c,hc,d,hh,hv⟩ := last
        exact ⟨K,by simp,nd,ss,prior,a,subs ha ac,c,hc,d,hh,w,hv,.inl ⟨rfl,bc.symm⟩⟩
      obtain ⟨P,hl,hP⟩ := ih prior nd ss (subs ha ac) (subs hb bc)
      exact ⟨P,by simp; omega,hP⟩
  let S : List W := List.ofFn (fun j : Fin 10 => BitVec.ofNat 1024 (((2^1024-1) / (2^(2^((List.finRange 10).idxOf j))+1)) * 2^(2^((List.finRange 10).idxOf j))))
  let B : List W := [0,~~~0] ++ S
  let f := fun i => S.getD i 0
  let T : W := (List.range 5).foldl (fun v i => v ||| (f i &&& f ((i+1)%5)) ||| (f i &&& f (5+i)) ||| (f (5+i) &&& f (5+(i+2)%5))) 0
  let F := fun (x : Fin 10 → Bool) => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  let row := fun (k : Fin 1024) (j : Fin 10) => k.val.testBit j.val
  have cols : ∀ (k : Fin 1024) (j : Fin 10), (f j.val).getLsbD k.val = row k j := by decide +kernel
  have rows (k : Fin 1024) : List.ofFn (row k) = S.map fun z => z.getLsbD k.val := by
    apply List.ext_getElem
    · simp [S]
    · intro i hi hj
      have i10 : i < 10 := by simpa using hi
      have hlen : i < S.length := by simpa using hj
      simpa only [List.getElem_ofFn,List.getElem_map,f,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlen,Option.getD_some] using (cols k ⟨i,i10⟩).symm
  have truth : ∀ k : Fin 1024, T.getLsbD k.val = F (row k) := by decide +kernel
  have onto (x : Fin 10 → Bool) : ∃ k : Fin 1024, row k = x := by
    let n : BitVec 10 := (BitVec.ofBoolListLE (List.ofFn x)).cast (by simp)
    refine ⟨n.toFin,?_⟩
    funext j
    change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD j.val = x j
    simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using j.isLt)]
    exact List.getElem_ofFn _
  intro g C a b hg hc size
  let D : Circuit := ⟨g :: C.gates,0⟩
  let wire := fun (x : Fin 10 → Bool) (i : Nat) => (D.wires (List.ofFn x)).getD i false
  change (∃ x,wire x a = true ∧ wire x b = false) → (∃ x,wire x a = false ∧ wire x b = true) →
    (∀ x,F x = false → wire x a = false ∧ wire x b = false) →
    ∃ x,F x = true ∧ wire x a = false ∧ wire x b = false
  rintro ⟨xa,haa,hab⟩ ⟨xb,hba,hbb⟩ off
  by_contra miss
  have eq (x : Fin 10 → Bool) : (wire x a || wire x b) = F x := by
    cases e : F x with
    | false => have h := off x e; simp [h]
    | true =>
      cases p : wire x a <;> cases q : wire x b <;> first | rfl | exact False.elim (miss ⟨x,e,p,q⟩)
  obtain ⟨K,hk,hd,hs,hbuild,reads⟩ := compile D S (by
    intro z hz; rcases List.mem_cons.mp hz with rfl | ht
    · exact hg _ (by simp)
    · exact hc _ ht)
  obtain ⟨u,hu,du⟩ := reads a
  obtain ⟨v,hv,dv⟩ := reads b
  have eu (k : Fin 1024) : u.getLsbD k.val = wire (row k) a := by change _ = (D.wires (List.ofFn (row k))).getD a false; rw [rows]; exact du k
  have ev (k : Fin 1024) : v.getLsbD k.val = wire (row k) b := by change _ = (D.wires (List.ofFn (row k))).getD b false; rw [rows]; exact dv k
  have uni : u ||| v = T := by
    apply BitVec.eq_of_getElem_eq; intro k hk'
    simpa only [← BitVec.getLsbD_eq_getElem hk',BitVec.getLsbD_or, eu, ev, truth] using
      (show (u ||| v).getLsbD k = T.getLsbD k from by rw [BitVec.getLsbD_or,eu ⟨k,hk'⟩,ev ⟨k,hk'⟩,truth ⟨k,hk'⟩,eq])
  obtain ⟨ka,ha⟩ := onto xa
  obtain ⟨kb,hb⟩ := onto xb
  have ua : u.getLsbD ka.val = true := by rw [eu,ha,haa]
  have va : v.getLsbD ka.val = false := by rw [ev,ha,hab]
  have ub : u.getLsbD kb.val = false := by rw [eu,hb,hba]
  have vb : v.getLsbD kb.val = true := by rw [ev,hb,hbb]
  have un : u ≠ T := by
    intro h; have e := congrArg (fun w : W => w.getLsbD kb.val) uni
    simp only [BitVec.getLsbD_or,ub,vb,← h] at e
    simp [ub] at e
  have vn : v ≠ T := by
    intro h; have e := congrArg (fun w : W => w.getLsbD ka.val) uni
    simp only [BitVec.getLsbD_or,ua,va,← h] at e
    simp [va] at e
  have sb : B.all (fun w => B.all fun z => (w ||| z) != T) = true := by decide +kernel
  have seed (w : W) (hw : w ∈ B) (z : W) (hz : z ∈ B) : w ||| z ≠ T := by
    simpa using List.all_eq_true.mp (List.all_eq_true.mp sb w hw) z hz
  obtain ⟨P,hlen,pd,ps,pbuild,q,hq,c,hc',d,hd',z,hz,hpair⟩ :=
    cut B K hbuild hd hs u v hu hv (fun h => by rw [h,va] at ua; contradiction)
      (fun both => seed _ both.1 _ both.2 uni)
  have lim : K.length ≤ 18 := by
    change K.length ≤ C.gates.length+1 at hk
    change C.gates.length ≤ 17 at size
    omega
  have ex := exclude P (by omega) pd ps pbuild q hq c hc' d hd' z hz
  rcases hpair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ex un vn uni
  · exact ex vn un ((BitVec.or_comm _ _).trans uni)
