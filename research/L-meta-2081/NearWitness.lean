import Std.Tactic.BVDecide
import PEqualNP.Defs.TopForm
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace Meta2081Near

open PEqualNP.CircuitLowerBounds

def C : Circuit := ⟨[
    ⟨GateOp.or, [13,23]⟩,
    ⟨GateOp.or, [26,17]⟩,
    ⟨GateOp.or, [15,14]⟩,
    ⟨GateOp.or, [28,19]⟩,
    ⟨GateOp.and, [0,27]⟩,
    ⟨GateOp.or, [30,25]⟩,
    ⟨GateOp.and, [31,0]⟩,
    ⟨GateOp.or, [31,29]⟩,
    ⟨GateOp.or, [32,2]⟩,
    ⟨GateOp.and, [34,33]⟩,
    ⟨GateOp.or, [14,13]⟩,
    ⟨GateOp.or, [36,24]⟩,
    ⟨GateOp.or, [37,18]⟩,
    ⟨GateOp.and, [1,38]⟩,
    ⟨GateOp.or, [16,15]⟩,
    ⟨GateOp.or, [40,13]⟩,
    ⟨GateOp.or, [41,20]⟩,
    ⟨GateOp.and, [3,42]⟩,
    ⟨GateOp.or, [17,16]⟩,
    ⟨GateOp.or, [44,14]⟩,
    ⟨GateOp.or, [45,21]⟩,
    ⟨GateOp.and, [4,46]⟩,
    ⟨GateOp.or, [18,17]⟩,
    ⟨GateOp.or, [48,15]⟩,
    ⟨GateOp.or, [49,22]⟩,
    ⟨GateOp.and, [5,50]⟩,
    ⟨GateOp.or, [19,18]⟩,
    ⟨GateOp.or, [52,16]⟩,
    ⟨GateOp.or, [53,23]⟩,
    ⟨GateOp.and, [6,54]⟩,
    ⟨GateOp.or, [20,19]⟩,
    ⟨GateOp.or, [56,17]⟩,
    ⟨GateOp.or, [57,24]⟩,
    ⟨GateOp.and, [7,58]⟩,
    ⟨GateOp.or, [21,20]⟩,
    ⟨GateOp.or, [60,18]⟩,
    ⟨GateOp.or, [61,25]⟩,
    ⟨GateOp.and, [8,62]⟩,
    ⟨GateOp.or, [22,21]⟩,
    ⟨GateOp.or, [64,19]⟩,
    ⟨GateOp.or, [65,13]⟩,
    ⟨GateOp.and, [9,66]⟩,
    ⟨GateOp.or, [23,22]⟩,
    ⟨GateOp.or, [68,20]⟩,
    ⟨GateOp.or, [69,14]⟩,
    ⟨GateOp.and, [10,70]⟩,
    ⟨GateOp.or, [24,23]⟩,
    ⟨GateOp.or, [72,21]⟩,
    ⟨GateOp.or, [73,15]⟩,
    ⟨GateOp.and, [11,74]⟩,
    ⟨GateOp.or, [25,24]⟩,
    ⟨GateOp.or, [76,22]⟩,
    ⟨GateOp.or, [77,16]⟩,
    ⟨GateOp.and, [12,78]⟩,
    ⟨GateOp.or, [35,39]⟩,
    ⟨GateOp.or, [80,43]⟩,
    ⟨GateOp.or, [81,47]⟩,
    ⟨GateOp.or, [82,51]⟩,
    ⟨GateOp.or, [83,55]⟩,
    ⟨GateOp.or, [84,59]⟩,
    ⟨GateOp.or, [85,63]⟩,
    ⟨GateOp.or, [86,67]⟩,
    ⟨GateOp.or, [87,71]⟩,
    ⟨GateOp.or, [88,75]⟩,
    ⟨GateOp.or, [89,79]⟩], 90⟩

def adj (p l : Fin 13) : Prop := (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)

def F (x y : Fin 13 → Bool) : Bool := (
    ((x 0 && y 0) || (x 0 && y 12) || (x 0 && y 10) || (x 0 && y 4)) ||
    ((x 1 && y 1) || (x 1 && y 0) || (x 1 && y 11) || (x 1 && y 5)) ||
    ((x 2 && y 2) || (x 2 && y 1) || (x 2 && y 12) || (x 2 && y 6)) ||
    ((x 3 && y 3) || (x 3 && y 2) || (x 3 && y 0) || (x 3 && y 7)) ||
    ((x 4 && y 4) || (x 4 && y 3) || (x 4 && y 1) || (x 4 && y 8)) ||
    ((x 5 && y 5) || (x 5 && y 4) || (x 5 && y 2) || (x 5 && y 9)) ||
    ((x 6 && y 6) || (x 6 && y 5) || (x 6 && y 3) || (x 6 && y 10)) ||
    ((x 7 && y 7) || (x 7 && y 6) || (x 7 && y 4) || (x 7 && y 11)) ||
    ((x 8 && y 8) || (x 8 && y 7) || (x 8 && y 5) || (x 8 && y 12)) ||
    ((x 9 && y 9) || (x 9 && y 8) || (x 9 && y 6) || (x 9 && y 0)) ||
    ((x 10 && y 10) || (x 10 && y 9) || (x 10 && y 7) || (x 10 && y 1)) ||
    ((x 11 && y 11) || (x 11 && y 10) || (x 11 && y 8) || (x 11 && y 2)) ||
    ((x 12 && y 12) || (x 12 && y 11) || (x 12 && y 9) || (x 12 && y 3)))

def inputs (x y : Fin 13 → Bool) : List Bool := List.ofFn (Fin.addCases x y)

open PEqualNP.MetaComplexity.LowMergeProof

theorem gate_value (D : Circuit) (z : List Bool) (n j a b : ℕ) (op : GateOp)
    (hlen : z.length = n) (hg : D.gates[j]? = some ⟨op,[a,b]⟩)
    (ha : a < n+j) (hb : b < n+j) :
    (D.wires z).getD (n+j) false = op.eval [(D.wires z).getD a false, (D.wires z).getD b false] := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hg
  have h := wires_gate D z j hj
  rw [hlen, he] at h
  simpa [rd, ha, hb] using h

theorem logic (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 : Bool) :
    ((((((((((((((((a0 && ((a13 || a23) || a17)) || a25) && a0) || a2) && (((a0 && ((a13 || a23) || a17)) || a25) || ((a15 || a14) || a19))) || (a1 && (((a14 || a13) || a24) || a18))) || (a3 && (((a16 || a15) || a13) || a20))) || (a4 && (((a17 || a16) || a14) || a21))) || (a5 && (((a18 || a17) || a15) || a22))) || (a6 && (((a19 || a18) || a16) || a23))) || (a7 && (((a20 || a19) || a17) || a24))) || (a8 && (((a21 || a20) || a18) || a25))) || (a9 && (((a22 || a21) || a19) || a13))) || (a10 && (((a23 || a22) || a20) || a14))) || (a11 && (((a24 || a23) || a21) || a15))) || (a12 && (((a25 || a24) || a22) || a16))) = (
    ((a0 && a13) || (a0 && a25) || (a0 && a23) || (a0 && a17)) ||
    ((a1 && a14) || (a1 && a13) || (a1 && a24) || (a1 && a18)) ||
    ((a2 && a15) || (a2 && a14) || (a2 && a25) || (a2 && a19)) ||
    ((a3 && a16) || (a3 && a15) || (a3 && a13) || (a3 && a20)) ||
    ((a4 && a17) || (a4 && a16) || (a4 && a14) || (a4 && a21)) ||
    ((a5 && a18) || (a5 && a17) || (a5 && a15) || (a5 && a22)) ||
    ((a6 && a19) || (a6 && a18) || (a6 && a16) || (a6 && a23)) ||
    ((a7 && a20) || (a7 && a19) || (a7 && a17) || (a7 && a24)) ||
    ((a8 && a21) || (a8 && a20) || (a8 && a18) || (a8 && a25)) ||
    ((a9 && a22) || (a9 && a21) || (a9 && a19) || (a9 && a13)) ||
    ((a10 && a23) || (a10 && a22) || (a10 && a20) || (a10 && a14)) ||
    ((a11 && a24) || (a11 && a23) || (a11 && a21) || (a11 && a15)) ||
    ((a12 && a25) || (a12 && a24) || (a12 && a22) || (a12 && a16))) := by bv_decide

theorem or_value (D : Circuit) (z : List Bool) (n j a b : ℕ)
    (hz : z.length = n) (hg : D.gates[j]? = some ⟨.or,[a,b]⟩)
    (ha : a < n+j) (hb : b < n+j) :
    (D.wires z).getD (n+j) false = ((D.wires z).getD a false || (D.wires z).getD b false) := by
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using gate_value D z n j a b .or hz hg ha hb

theorem and_value (D : Circuit) (z : List Bool) (n j a b : ℕ)
    (hz : z.length = n) (hg : D.gates[j]? = some ⟨.and,[a,b]⟩)
    (ha : a < n+j) (hb : b < n+j) :
    (D.wires z).getD (n+j) false = ((D.wires z).getD a false && (D.wires z).getD b false) := by
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using gate_value D z n j a b .and hz hg ha hb

theorem bridge (x y : Fin 13 → Bool) (w : ℕ → Bool)
    (h0 : w 0 = x 0)
    (h1 : w 1 = x 1)
    (h2 : w 2 = x 2)
    (h3 : w 3 = x 3)
    (h4 : w 4 = x 4)
    (h5 : w 5 = x 5)
    (h6 : w 6 = x 6)
    (h7 : w 7 = x 7)
    (h8 : w 8 = x 8)
    (h9 : w 9 = x 9)
    (h10 : w 10 = x 10)
    (h11 : w 11 = x 11)
    (h12 : w 12 = x 12)
    (h13 : w 13 = y 0)
    (h14 : w 14 = y 1)
    (h15 : w 15 = y 2)
    (h16 : w 16 = y 3)
    (h17 : w 17 = y 4)
    (h18 : w 18 = y 5)
    (h19 : w 19 = y 6)
    (h20 : w 20 = y 7)
    (h21 : w 21 = y 8)
    (h22 : w 22 = y 9)
    (h23 : w 23 = y 10)
    (h24 : w 24 = y 11)
    (h25 : w 25 = y 12)
    (h26 : w 26 = (w 13 || w 23))
    (h27 : w 27 = (w 26 || w 17))
    (h28 : w 28 = (w 15 || w 14))
    (h29 : w 29 = (w 28 || w 19))
    (h30 : w 30 = (w 0 && w 27))
    (h31 : w 31 = (w 30 || w 25))
    (h32 : w 32 = (w 31 && w 0))
    (h33 : w 33 = (w 31 || w 29))
    (h34 : w 34 = (w 32 || w 2))
    (h35 : w 35 = (w 34 && w 33))
    (h36 : w 36 = (w 14 || w 13))
    (h37 : w 37 = (w 36 || w 24))
    (h38 : w 38 = (w 37 || w 18))
    (h39 : w 39 = (w 1 && w 38))
    (h40 : w 40 = (w 16 || w 15))
    (h41 : w 41 = (w 40 || w 13))
    (h42 : w 42 = (w 41 || w 20))
    (h43 : w 43 = (w 3 && w 42))
    (h44 : w 44 = (w 17 || w 16))
    (h45 : w 45 = (w 44 || w 14))
    (h46 : w 46 = (w 45 || w 21))
    (h47 : w 47 = (w 4 && w 46))
    (h48 : w 48 = (w 18 || w 17))
    (h49 : w 49 = (w 48 || w 15))
    (h50 : w 50 = (w 49 || w 22))
    (h51 : w 51 = (w 5 && w 50))
    (h52 : w 52 = (w 19 || w 18))
    (h53 : w 53 = (w 52 || w 16))
    (h54 : w 54 = (w 53 || w 23))
    (h55 : w 55 = (w 6 && w 54))
    (h56 : w 56 = (w 20 || w 19))
    (h57 : w 57 = (w 56 || w 17))
    (h58 : w 58 = (w 57 || w 24))
    (h59 : w 59 = (w 7 && w 58))
    (h60 : w 60 = (w 21 || w 20))
    (h61 : w 61 = (w 60 || w 18))
    (h62 : w 62 = (w 61 || w 25))
    (h63 : w 63 = (w 8 && w 62))
    (h64 : w 64 = (w 22 || w 21))
    (h65 : w 65 = (w 64 || w 19))
    (h66 : w 66 = (w 65 || w 13))
    (h67 : w 67 = (w 9 && w 66))
    (h68 : w 68 = (w 23 || w 22))
    (h69 : w 69 = (w 68 || w 20))
    (h70 : w 70 = (w 69 || w 14))
    (h71 : w 71 = (w 10 && w 70))
    (h72 : w 72 = (w 24 || w 23))
    (h73 : w 73 = (w 72 || w 21))
    (h74 : w 74 = (w 73 || w 15))
    (h75 : w 75 = (w 11 && w 74))
    (h76 : w 76 = (w 25 || w 24))
    (h77 : w 77 = (w 76 || w 22))
    (h78 : w 78 = (w 77 || w 16))
    (h79 : w 79 = (w 12 && w 78))
    (h80 : w 80 = (w 35 || w 39))
    (h81 : w 81 = (w 80 || w 43))
    (h82 : w 82 = (w 81 || w 47))
    (h83 : w 83 = (w 82 || w 51))
    (h84 : w 84 = (w 83 || w 55))
    (h85 : w 85 = (w 84 || w 59))
    (h86 : w 86 = (w 85 || w 63))
    (h87 : w 87 = (w 86 || w 67))
    (h88 : w 88 = (w 87 || w 71))
    (h89 : w 89 = (w 88 || w 75))
    (h90 : w 90 = (w 89 || w 79))
    : w 90 = F x y := by
  simp only [h90, h89, h88, h87, h86, h85, h84, h83, h82, h81, h80, h79, h78, h77, h76, h75, h74, h73, h72, h71, h70, h69, h68, h67, h66, h65, h64, h63, h62, h61, h60, h59, h58, h57, h56, h55, h54, h53, h52, h51, h50, h49, h48, h47, h46, h45, h44, h43, h42, h41, h40, h39, h38, h37, h36, h35, h34, h33, h32, h31, h30, h29, h28, h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  exact logic (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8) (y 9) (y 10) (y 11) (y 12)

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
theorem computes (x y : Fin 13 → Bool) : C.eval (inputs x y) = F x y := by
  let z := inputs x y
  let w := fun i : ℕ => (C.wires z).getD i false
  have zl : z.length = 26 := by simp [z, inputs]
  have get (i : ℕ) (h : i < 26) : w i = z.getD i false :=
    wires_input C z i (zl ▸ h)
  have h0 : w 0 = x 0 := (get 0 (by decide)).trans (by rfl)
  have h1 : w 1 = x 1 := (get 1 (by decide)).trans (by rfl)
  have h2 : w 2 = x 2 := (get 2 (by decide)).trans (by rfl)
  have h3 : w 3 = x 3 := (get 3 (by decide)).trans (by rfl)
  have h4 : w 4 = x 4 := (get 4 (by decide)).trans (by rfl)
  have h5 : w 5 = x 5 := (get 5 (by decide)).trans (by rfl)
  have h6 : w 6 = x 6 := (get 6 (by decide)).trans (by rfl)
  have h7 : w 7 = x 7 := (get 7 (by decide)).trans (by rfl)
  have h8 : w 8 = x 8 := (get 8 (by decide)).trans (by rfl)
  have h9 : w 9 = x 9 := (get 9 (by decide)).trans (by rfl)
  have h10 : w 10 = x 10 := (get 10 (by decide)).trans (by rfl)
  have h11 : w 11 = x 11 := (get 11 (by decide)).trans (by rfl)
  have h12 : w 12 = x 12 := (get 12 (by decide)).trans (by rfl)
  have h13 : w 13 = y 0 := (get 13 (by decide)).trans (by rfl)
  have h14 : w 14 = y 1 := (get 14 (by decide)).trans (by rfl)
  have h15 : w 15 = y 2 := (get 15 (by decide)).trans (by rfl)
  have h16 : w 16 = y 3 := (get 16 (by decide)).trans (by rfl)
  have h17 : w 17 = y 4 := (get 17 (by decide)).trans (by rfl)
  have h18 : w 18 = y 5 := (get 18 (by decide)).trans (by rfl)
  have h19 : w 19 = y 6 := (get 19 (by decide)).trans (by rfl)
  have h20 : w 20 = y 7 := (get 20 (by decide)).trans (by rfl)
  have h21 : w 21 = y 8 := (get 21 (by decide)).trans (by rfl)
  have h22 : w 22 = y 9 := (get 22 (by decide)).trans (by rfl)
  have h23 : w 23 = y 10 := (get 23 (by decide)).trans (by rfl)
  have h24 : w 24 = y 11 := (get 24 (by decide)).trans (by rfl)
  have h25 : w 25 = y 12 := (get 25 (by decide)).trans (by rfl)
  have h26 : w 26 = (w 13 || w 23) :=
    or_value C z 26 0 13 23 zl rfl (by decide) (by decide)
  have h27 : w 27 = (w 26 || w 17) :=
    or_value C z 26 1 26 17 zl rfl (by decide) (by decide)
  have h28 : w 28 = (w 15 || w 14) :=
    or_value C z 26 2 15 14 zl rfl (by decide) (by decide)
  have h29 : w 29 = (w 28 || w 19) :=
    or_value C z 26 3 28 19 zl rfl (by decide) (by decide)
  have h30 : w 30 = (w 0 && w 27) :=
    and_value C z 26 4 0 27 zl rfl (by decide) (by decide)
  have h31 : w 31 = (w 30 || w 25) :=
    or_value C z 26 5 30 25 zl rfl (by decide) (by decide)
  have h32 : w 32 = (w 31 && w 0) :=
    and_value C z 26 6 31 0 zl rfl (by decide) (by decide)
  have h33 : w 33 = (w 31 || w 29) :=
    or_value C z 26 7 31 29 zl rfl (by decide) (by decide)
  have h34 : w 34 = (w 32 || w 2) :=
    or_value C z 26 8 32 2 zl rfl (by decide) (by decide)
  have h35 : w 35 = (w 34 && w 33) :=
    and_value C z 26 9 34 33 zl rfl (by decide) (by decide)
  have h36 : w 36 = (w 14 || w 13) :=
    or_value C z 26 10 14 13 zl rfl (by decide) (by decide)
  have h37 : w 37 = (w 36 || w 24) :=
    or_value C z 26 11 36 24 zl rfl (by decide) (by decide)
  have h38 : w 38 = (w 37 || w 18) :=
    or_value C z 26 12 37 18 zl rfl (by decide) (by decide)
  have h39 : w 39 = (w 1 && w 38) :=
    and_value C z 26 13 1 38 zl rfl (by decide) (by decide)
  have h40 : w 40 = (w 16 || w 15) :=
    or_value C z 26 14 16 15 zl rfl (by decide) (by decide)
  have h41 : w 41 = (w 40 || w 13) :=
    or_value C z 26 15 40 13 zl rfl (by decide) (by decide)
  have h42 : w 42 = (w 41 || w 20) :=
    or_value C z 26 16 41 20 zl rfl (by decide) (by decide)
  have h43 : w 43 = (w 3 && w 42) :=
    and_value C z 26 17 3 42 zl rfl (by decide) (by decide)
  have h44 : w 44 = (w 17 || w 16) :=
    or_value C z 26 18 17 16 zl rfl (by decide) (by decide)
  have h45 : w 45 = (w 44 || w 14) :=
    or_value C z 26 19 44 14 zl rfl (by decide) (by decide)
  have h46 : w 46 = (w 45 || w 21) :=
    or_value C z 26 20 45 21 zl rfl (by decide) (by decide)
  have h47 : w 47 = (w 4 && w 46) :=
    and_value C z 26 21 4 46 zl rfl (by decide) (by decide)
  have h48 : w 48 = (w 18 || w 17) :=
    or_value C z 26 22 18 17 zl rfl (by decide) (by decide)
  have h49 : w 49 = (w 48 || w 15) :=
    or_value C z 26 23 48 15 zl rfl (by decide) (by decide)
  have h50 : w 50 = (w 49 || w 22) :=
    or_value C z 26 24 49 22 zl rfl (by decide) (by decide)
  have h51 : w 51 = (w 5 && w 50) :=
    and_value C z 26 25 5 50 zl rfl (by decide) (by decide)
  have h52 : w 52 = (w 19 || w 18) :=
    or_value C z 26 26 19 18 zl rfl (by decide) (by decide)
  have h53 : w 53 = (w 52 || w 16) :=
    or_value C z 26 27 52 16 zl rfl (by decide) (by decide)
  have h54 : w 54 = (w 53 || w 23) :=
    or_value C z 26 28 53 23 zl rfl (by decide) (by decide)
  have h55 : w 55 = (w 6 && w 54) :=
    and_value C z 26 29 6 54 zl rfl (by decide) (by decide)
  have h56 : w 56 = (w 20 || w 19) :=
    or_value C z 26 30 20 19 zl rfl (by decide) (by decide)
  have h57 : w 57 = (w 56 || w 17) :=
    or_value C z 26 31 56 17 zl rfl (by decide) (by decide)
  have h58 : w 58 = (w 57 || w 24) :=
    or_value C z 26 32 57 24 zl rfl (by decide) (by decide)
  have h59 : w 59 = (w 7 && w 58) :=
    and_value C z 26 33 7 58 zl rfl (by decide) (by decide)
  have h60 : w 60 = (w 21 || w 20) :=
    or_value C z 26 34 21 20 zl rfl (by decide) (by decide)
  have h61 : w 61 = (w 60 || w 18) :=
    or_value C z 26 35 60 18 zl rfl (by decide) (by decide)
  have h62 : w 62 = (w 61 || w 25) :=
    or_value C z 26 36 61 25 zl rfl (by decide) (by decide)
  have h63 : w 63 = (w 8 && w 62) :=
    and_value C z 26 37 8 62 zl rfl (by decide) (by decide)
  have h64 : w 64 = (w 22 || w 21) :=
    or_value C z 26 38 22 21 zl rfl (by decide) (by decide)
  have h65 : w 65 = (w 64 || w 19) :=
    or_value C z 26 39 64 19 zl rfl (by decide) (by decide)
  have h66 : w 66 = (w 65 || w 13) :=
    or_value C z 26 40 65 13 zl rfl (by decide) (by decide)
  have h67 : w 67 = (w 9 && w 66) :=
    and_value C z 26 41 9 66 zl rfl (by decide) (by decide)
  have h68 : w 68 = (w 23 || w 22) :=
    or_value C z 26 42 23 22 zl rfl (by decide) (by decide)
  have h69 : w 69 = (w 68 || w 20) :=
    or_value C z 26 43 68 20 zl rfl (by decide) (by decide)
  have h70 : w 70 = (w 69 || w 14) :=
    or_value C z 26 44 69 14 zl rfl (by decide) (by decide)
  have h71 : w 71 = (w 10 && w 70) :=
    and_value C z 26 45 10 70 zl rfl (by decide) (by decide)
  have h72 : w 72 = (w 24 || w 23) :=
    or_value C z 26 46 24 23 zl rfl (by decide) (by decide)
  have h73 : w 73 = (w 72 || w 21) :=
    or_value C z 26 47 72 21 zl rfl (by decide) (by decide)
  have h74 : w 74 = (w 73 || w 15) :=
    or_value C z 26 48 73 15 zl rfl (by decide) (by decide)
  have h75 : w 75 = (w 11 && w 74) :=
    and_value C z 26 49 11 74 zl rfl (by decide) (by decide)
  have h76 : w 76 = (w 25 || w 24) :=
    or_value C z 26 50 25 24 zl rfl (by decide) (by decide)
  have h77 : w 77 = (w 76 || w 22) :=
    or_value C z 26 51 76 22 zl rfl (by decide) (by decide)
  have h78 : w 78 = (w 77 || w 16) :=
    or_value C z 26 52 77 16 zl rfl (by decide) (by decide)
  have h79 : w 79 = (w 12 && w 78) :=
    and_value C z 26 53 12 78 zl rfl (by decide) (by decide)
  have h80 : w 80 = (w 35 || w 39) :=
    or_value C z 26 54 35 39 zl rfl (by decide) (by decide)
  have h81 : w 81 = (w 80 || w 43) :=
    or_value C z 26 55 80 43 zl rfl (by decide) (by decide)
  have h82 : w 82 = (w 81 || w 47) :=
    or_value C z 26 56 81 47 zl rfl (by decide) (by decide)
  have h83 : w 83 = (w 82 || w 51) :=
    or_value C z 26 57 82 51 zl rfl (by decide) (by decide)
  have h84 : w 84 = (w 83 || w 55) :=
    or_value C z 26 58 83 55 zl rfl (by decide) (by decide)
  have h85 : w 85 = (w 84 || w 59) :=
    or_value C z 26 59 84 59 zl rfl (by decide) (by decide)
  have h86 : w 86 = (w 85 || w 63) :=
    or_value C z 26 60 85 63 zl rfl (by decide) (by decide)
  have h87 : w 87 = (w 86 || w 67) :=
    or_value C z 26 61 86 67 zl rfl (by decide) (by decide)
  have h88 : w 88 = (w 87 || w 71) :=
    or_value C z 26 62 87 71 zl rfl (by decide) (by decide)
  have h89 : w 89 = (w 88 || w 75) :=
    or_value C z 26 63 88 75 zl rfl (by decide) (by decide)
  have h90 : w 90 = (w 89 || w 79) :=
    or_value C z 26 64 89 79 zl rfl (by decide) (by decide)
  exact bridge x y w h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83 h84 h85 h86 h87 h88 h89 h90

def miss (x : Fin 13 → Bool) (j : Fin 13) : Bool :=
  !(x j || x (j+1) || x (j+3) || x (j+9))

set_option maxHeartbeats 0 in
theorem positive : ∀ p l : Fin 13, adj p l →
    F (fun i => decide (i=p)) (fun j => decide (j=l)) = true := by
  unfold adj
  decide +kernel

set_option maxHeartbeats 0 in
theorem negative (x : Fin 13 → Bool) : F x (miss x) = false := by
  change (
    ((x 0 && miss x 0) || (x 0 && miss x 12) || (x 0 && miss x 10) || (x 0 && miss x 4)) ||
    ((x 1 && miss x 1) || (x 1 && miss x 0) || (x 1 && miss x 11) || (x 1 && miss x 5)) ||
    ((x 2 && miss x 2) || (x 2 && miss x 1) || (x 2 && miss x 12) || (x 2 && miss x 6)) ||
    ((x 3 && miss x 3) || (x 3 && miss x 2) || (x 3 && miss x 0) || (x 3 && miss x 7)) ||
    ((x 4 && miss x 4) || (x 4 && miss x 3) || (x 4 && miss x 1) || (x 4 && miss x 8)) ||
    ((x 5 && miss x 5) || (x 5 && miss x 4) || (x 5 && miss x 2) || (x 5 && miss x 9)) ||
    ((x 6 && miss x 6) || (x 6 && miss x 5) || (x 6 && miss x 3) || (x 6 && miss x 10)) ||
    ((x 7 && miss x 7) || (x 7 && miss x 6) || (x 7 && miss x 4) || (x 7 && miss x 11)) ||
    ((x 8 && miss x 8) || (x 8 && miss x 7) || (x 8 && miss x 5) || (x 8 && miss x 12)) ||
    ((x 9 && miss x 9) || (x 9 && miss x 8) || (x 9 && miss x 6) || (x 9 && miss x 0)) ||
    ((x 10 && miss x 10) || (x 10 && miss x 9) || (x 10 && miss x 7) || (x 10 && miss x 1)) ||
    ((x 11 && miss x 11) || (x 11 && miss x 10) || (x 11 && miss x 8) || (x 11 && miss x 2)) ||
    ((x 12 && miss x 12) || (x 12 && miss x 11) || (x 12 && miss x 9) || (x 12 && miss x 3))) = false
  unfold miss
  change (
    ((x 0 && !(x 0 || x 1 || x 3 || x 9)) || (x 0 && !(x 12 || x 0 || x 2 || x 8)) || (x 0 && !(x 10 || x 11 || x 0 || x 6)) || (x 0 && !(x 4 || x 5 || x 7 || x 0))) ||
    ((x 1 && !(x 1 || x 2 || x 4 || x 10)) || (x 1 && !(x 0 || x 1 || x 3 || x 9)) || (x 1 && !(x 11 || x 12 || x 1 || x 7)) || (x 1 && !(x 5 || x 6 || x 8 || x 1))) ||
    ((x 2 && !(x 2 || x 3 || x 5 || x 11)) || (x 2 && !(x 1 || x 2 || x 4 || x 10)) || (x 2 && !(x 12 || x 0 || x 2 || x 8)) || (x 2 && !(x 6 || x 7 || x 9 || x 2))) ||
    ((x 3 && !(x 3 || x 4 || x 6 || x 12)) || (x 3 && !(x 2 || x 3 || x 5 || x 11)) || (x 3 && !(x 0 || x 1 || x 3 || x 9)) || (x 3 && !(x 7 || x 8 || x 10 || x 3))) ||
    ((x 4 && !(x 4 || x 5 || x 7 || x 0)) || (x 4 && !(x 3 || x 4 || x 6 || x 12)) || (x 4 && !(x 1 || x 2 || x 4 || x 10)) || (x 4 && !(x 8 || x 9 || x 11 || x 4))) ||
    ((x 5 && !(x 5 || x 6 || x 8 || x 1)) || (x 5 && !(x 4 || x 5 || x 7 || x 0)) || (x 5 && !(x 2 || x 3 || x 5 || x 11)) || (x 5 && !(x 9 || x 10 || x 12 || x 5))) ||
    ((x 6 && !(x 6 || x 7 || x 9 || x 2)) || (x 6 && !(x 5 || x 6 || x 8 || x 1)) || (x 6 && !(x 3 || x 4 || x 6 || x 12)) || (x 6 && !(x 10 || x 11 || x 0 || x 6))) ||
    ((x 7 && !(x 7 || x 8 || x 10 || x 3)) || (x 7 && !(x 6 || x 7 || x 9 || x 2)) || (x 7 && !(x 4 || x 5 || x 7 || x 0)) || (x 7 && !(x 11 || x 12 || x 1 || x 7))) ||
    ((x 8 && !(x 8 || x 9 || x 11 || x 4)) || (x 8 && !(x 7 || x 8 || x 10 || x 3)) || (x 8 && !(x 5 || x 6 || x 8 || x 1)) || (x 8 && !(x 12 || x 0 || x 2 || x 8))) ||
    ((x 9 && !(x 9 || x 10 || x 12 || x 5)) || (x 9 && !(x 8 || x 9 || x 11 || x 4)) || (x 9 && !(x 6 || x 7 || x 9 || x 2)) || (x 9 && !(x 0 || x 1 || x 3 || x 9))) ||
    ((x 10 && !(x 10 || x 11 || x 0 || x 6)) || (x 10 && !(x 9 || x 10 || x 12 || x 5)) || (x 10 && !(x 7 || x 8 || x 10 || x 3)) || (x 10 && !(x 1 || x 2 || x 4 || x 10))) ||
    ((x 11 && !(x 11 || x 12 || x 1 || x 7)) || (x 11 && !(x 10 || x 11 || x 0 || x 6)) || (x 11 && !(x 8 || x 9 || x 11 || x 4)) || (x 11 && !(x 2 || x 3 || x 5 || x 11))) ||
    ((x 12 && !(x 12 || x 0 || x 2 || x 8)) || (x 12 && !(x 11 || x 12 || x 1 || x 7)) || (x 12 && !(x 9 || x 10 || x 12 || x 5)) || (x 12 && !(x 3 || x 4 || x 6 || x 12)))) = false
  bv_decide

def marker (b : Bool) (i : ℕ) := (if b then 0x2c0000001 else 0x400000677cc002000 : ℕ).testBit i

def baseVals (b : Bool) := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if b = true then 13 else 0))

def next (g : Gate) (bs : List Bool) (v : ℕ → Bool) : Bool :=
  let a := g.inputs.getD 0 0
  let b := g.inputs.getD 1 0
  match g.op with
  | .and => bs.getD a false && v b || v a && bs.getD b false
  | _ => v a || v b

set_option maxHeartbeats 0 in
theorem marker_init : ∀ b : Bool, ∀ i : Fin 26,
    marker b i.val = decide (i.val = if b = true then 0 else 13) := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem marker_steps : ∀ b : Bool, ∀ j : Fin 65,
    marker b (26+j.val) = next (C.gates.getD j.val ⟨.and, []⟩) (baseVals b) (marker b) := by
  decide +kernel

theorem marker_out : ∀ b, marker b C.output = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem near : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (65 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false := by
  refine ⟨C, by decide, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · intro p l hp
    exact (computes _ _).trans (positive p l hp)
  · intro x _
    exact (computes x (miss x)).trans (negative x)
  · intro b
    refine ⟨marker b, fun i hi => marker_init b ⟨i,hi⟩, ?_, marker_out b⟩
    intro j g a t hj hg
    have hj' : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
    have h := marker_steps b ⟨j,hj'⟩
    have hget : C.gates.getD j ⟨.and,[]⟩ = g := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hget] at h
    constructor <;> intro ho <;> simpa [next, hg, ho, baseVals] using h

end Meta2081Near
