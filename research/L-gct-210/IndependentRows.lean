import Mathlib

/-!
## 一次只改一行的方向总共至多六维

设 L 满足五阶 permanent 的题设。对每一行 i，令 A_i⊂ℂ⁵ 是所有可以单独加在这一行上、
并仍属于 L 的行向量。则 ∑dim A_i≤6。这五个空间在原矩阵空间中的和是直和。
因此任意九维反例，在这个直和之外至少还有三个维度。对列有同样结论。

记 H={a : ∑a_j=0}，取双线性点积。取一、二、三行上的独立扰动，比较对应的混合系数：
一次系数是 24∑a_j，所以 A_i⊂H。二次系数是 −6∑a_j b_j，因此不同行的 A_i 彼此正交。
三次系数是 4∑a_j b_j c_j，因为在三个向量的坐标和都为零时，互异指标的乘积之和
为两倍的同指标乘积之和。故来自三个不同行的三元乘积之和也为零。

令 V=∑A_i⊂H，R=V∩Vᗮ（在 H 内取正交补），r=dim R。H 是四维非退化空间，
因此 r≤2、dim V≤4−r。V/R 中，各 A_i 的像彼此正交且张成全空间。
它们的和是直和：一个像中同时属于其他像之和的向量，对所有像都正交，因此为零。
故 ∑dim A_i=dim V−r+∑dim(A_i∩R)。

若 r=0，上式至多为 4。若 r=1，五个 A_i 不可能同时包含 R。
否则取非零 w∈R，就能构成五行都等于 w 的方向；缩放它，可使 J+T 出现零列。
因此 ∑dim A_i≤2+4=6。

若 r=2，则 V=R 是 H 内的极大全迷向平面，R 在 H 中的正交补恰是 R。
若三行均有 A_i=R，则对任意 a,b,c∈R，三次系数给出 ∑a_j b_j c_j=0。
逐坐标积 a*b 的坐标和是 a·b=0，故 a*b∈H；它又正交于 R，故 a*b∈R。
但 H 中没有非零的、对逐坐标乘法封闭的线性子空间。事实上，给定 w 的一个非零坐标值 z，
取多项式 P(X)=X∏_{k:w_k≠z}(X−w_k)。P(w) 仍在该空间，各坐标要么为零，要么取同一非零值
P(z)，故坐标和非零，矛盾。下面的 coordinate_product_obstruction 在 Lean 中核对这一点。

于是最多两行有 A_i=R。若维数总和仍超过 6，就必须是 2,2,1,1,1。
若三条一维直线张成 R，固定前两行，在其余三行中用三次系数并取线性组合，
再次得到 ∑a_j b_j c_j=0 对所有 a,b,c∈R 成立，产生同一矛盾。
否则这三条直线重合，五行均包含共同的非零方向，又和零列论证矛盾。

还有一个位置上的限制：至少一行的 A_i 等于零。否则每个 A_i 任选非零向量 w_i。
五条线两两正交。若三条线同为 ℂw，三次以前的混合项给出 ∑w_j^k=0（k=1,2,3）。
w 至少有四个不同的非零坐标值，否则以其相异非零值为底数的 Vandermonde 方程迫使
这些值的出现次数均为零。另两行各自的向量 u 满足 ∑u_j w_j^k=0（k=0,1,2,3）：
取这三行中的 k 行分别加 w，在另一个行加 u，混合系数正比于
∑u_j e_k(w 除去第 j 项)，而 e_k(w 除 j)=(−w_j)^k。因此另两行的向量在同一条
直线上。该直线的居中向量至少有两个非零坐标，w 至少有四个，二者必有共同非零坐标。
五行可以独立缩放，足以把该列在 J+T 中逐项清零，矛盾。

余下五条线没有三条相同。用五条线之和作为上文的 V。若 r=0，直和维数超过 4。
若 r=1，则 dim(V/R)≤2，至少三条线落在同一根线中。故只剩 r=2，V 是极大全迷向平面。
任取两条不同行的线，剩余三条张成 V，三阶混合系数给出 ∑_k(w_i)_k(w_j)_k z_k=0 对
任意 z∈V 成立。固定 i，余下四条线仍张成 V，从而三元形式在整个 V 上恒零，
与下文 self_dual_triple_obstruction 矛盾。这也适用于转置后的列。
-/

namespace LevelSpaceFive.IndependentRows

open Finset Module

abbrev Entry := Fin 5 × Fin 5 → ℂ
abbrev Row := Fin 5 → ℂ

theorem constant_rows_zero (L : Submodule ℂ Entry)
    (hl : ∀ t ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i,e i))) = 120)
    (w : Row) (hw : (fun p : Fin 5 × Fin 5 => w p.2) ∈ L) : w = 0 := by
  classical
  funext j
  change w j = 0
  by_contra h
  let u : Entry := fun p => w p.2
  let k : ℂ := -(w j)⁻¹
  have hh := hl (k • u) (L.smul_mem k hw)
  have hz : (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + (k • u) (i,e i))) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    obtain ⟨a,ha⟩ := Finite.surjective_of_injective e.injective j
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    change 1 + -(w j)⁻¹ * w (e a) = 0
    rw [ha,neg_mul,inv_mul_cancel₀ h]
    ring
  rw [hz] at hh
  norm_num at hh

theorem coordinate_product_obstruction (R : Submodule ℂ Row)
    (centered : ∀ x ∈ R, (∑ i, x i) = 0)
    (closed : ∀ x ∈ R, ∀ y ∈ R, x*y ∈ R) : R = ⊥ := by
  classical
  apply eq_bot_iff.mpr
  intro w hw
  change w = 0
  funext j
  change w j = 0
  by_contra hn
  let b : Finset (Fin 5) := Finset.univ.filter (fun k => w k ≠ w j)
  let v (s : Finset (Fin 5)) : Row := fun i => w i * ∏ k ∈ s, (w i - w k)
  have mem (s : Finset (Fin 5)) : v s ∈ R := by
    induction s using Finset.induction_on with
    | empty => simpa [v] using hw
    | @insert k s hk ih =>
      have e : v (insert k s) = v s * w - w k • v s := by
        funext i
        simp only [v, Finset.prod_insert hk, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact R.sub_mem (closed _ ih _ hw) (R.smul_mem _ ih)
  have nonzero : v b j ≠ 0 := by
    apply mul_ne_zero hn
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hk).2)
  have eqv (i : Fin 5) : v b i = if w i = w j then v b j else 0 := by
    by_cases he : w i = w j
    · simp [v,he]
    · rw [ite_eq_right_iff.mpr (fun h => (he h).elim)]
      have hi : i ∈ b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      have h0 : (∏ k ∈ b, (w i - w k)) = 0 :=
        Finset.prod_eq_zero hi (sub_self _)
      simp [v,h0]
  have z : (∑ i : Fin 5, if w i = w j then v b j else 0) = 0 :=
    (Finset.sum_congr rfl (fun i _ => (eqv i).symm)).trans (centered (v b) (mem b))
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at z
  have hcard : 0 < (Finset.univ.filter (fun i => w i = w j)).card :=
    Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcard)) nonzero) z

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem centered_triple (a b c : Row)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0) :
    (∑ i, ∑ j, ∑ k, if i = j ∨ i = k ∨ j = k then 0 else a i*b j*c k) =
      2 * ∑ i, a i*b i*c i := by
  have h : (∑ i, ∑ j, ∑ k, if i = j ∨ i = k ∨ j = k then 0 else a i*b j*c k) =
      (∑ i, a i)*(∑ i, b i)*(∑ i, c i) - (∑ i, a i*b i)*(∑ i, c i)
      - (∑ i, a i*c i)*(∑ i, b i) - (∑ i, b i*c i)*(∑ i, a i)
      + 2 * ∑ i, a i*b i*c i := by
    simp (config := {decide := true}) [Fin.sum_univ_succ]
    ring
  rw [h,ha,hb,hc]
  ring

theorem self_dual_triple_obstruction (R : Submodule ℂ Row)
    (centered : ∀ x ∈ R, (∑ i, x i) = 0)
    (orthogonal : ∀ x ∈ R, ∀ y ∈ R, (∑ i, x i*y i) = 0)
    (selfDual : ∀ z : Row, (∑ i, z i) = 0 → (∀ w ∈ R, (∑ i, z i*w i) = 0) → z ∈ R)
    (triple : ∀ x ∈ R, ∀ y ∈ R, ∀ w ∈ R, (∑ i, x i*y i*w i) = 0) : R = ⊥ := by
  apply coordinate_product_obstruction R centered
  intro x hx y hy
  exact selfDual (x*y) (orthogonal x hx y hy) (triple x hx y hy)

end LevelSpaceFive.IndependentRows
