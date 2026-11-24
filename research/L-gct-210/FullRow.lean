import Mathlib
import PEqualNP.Gct.Helpers.BorderedPerm

/-!
## 包含一整行自由变化时的八维上界

设 J 为五阶全 1 矩阵。若复线性空间 L 满足 per(J+T)=120，并且包含所有仅在某个指定行
上变化、该行元素之和为零的矩阵，则 dim L ≤ 8。转置给出同样的列结论。
下文给出维数推导。文件中的 Lean 定理核对行展开、余子式的二至四阶展开和末尾的数值 8。

把指定行排到最后。固定 T，记 C_j 为删除最后一行、第 j 列所得的四阶 permanent。
在最后一行加 e_j−e_k 得 C_j=C_k。于是 per(J+T) 是最后一行之和乘 C_1。
若某个 T 的最后一行之和非零，用标量缩放 T 就能令 J+T 的最后一行之和为零，与 120 矛盾。
故所有 T 的最后一行之和为零，且所有 C_j=24。令 W 为删去最后一行所得的 4×5 空间。
删除映射的核正好是开头给定的四维空间，故 dim L=4+dim W。

对 W 中的一点，写 v_1,…,v_5 ∈ ℂ⁴ 为五个列向量，S=∑v_j。以下用双线性点积 x·y=∑x_i y_i。
从 C_j 在 J 的一次系数得到 ∑_{k≠j}∑_i (v_k)_i=0。因此每一列的坐标和都为零。
记 H 为 ℂ⁴ 中坐标和为零的超平面。其点积非退化，维数为 3。
二次系数给出 ∑_{k<l, k,l≠j} v_k·v_l=0。把五式相加，每对列被数到三次。
用总和减去第 j 式可得 v_j·(S−v_j)=0，亦即 (2v_j−S)·(2v_j−S)=S·S。

将 S 看作从 W 到 H 的线性映射，记 K=ker S。如果 S 满射，右侧二次型在 W 上秩为 3。
由上述恒等式，B_j=2v_j−S 也都满射。对恒等式极化，对每个 x∈K、y∈W 得
B_j(x)·B_j(y)=0。由满射和非退化性得 B_j(x)=0，故 x 的每列都是零。
此时 dim W=3。余下 rank S≤2，只需证明 dim K≤2。

对 x∈K，每个 v_j(x) 都满足 v_j(x)·v_j(x)=0。因此每列映射 v_j(K) 是 H 中的全迷向空间。
三维非退化点积的全迷向空间维数至多 1。把各非零列写成 α_j(x) w_j，其中 w_j 为固定非零
零长度向量，α_j 为 K 上非零线性型。记非零列数为 m，所有 w_j 张成空间的维数为 s。
由 ∑α_j w_j=0 和列坐标对 x 的单射性，有 dim K≤m−s。假设 dim K≥3，则 m≤5 给出 s≤2。

若 s=1，选同一个向量 w 写全部列，空列取 α_j=0。此时 m≥4，且 ∑α_j=0。
选四个非零列，其四次系数为 24·(∏_i w_i)·(∏α_j)。非零线性型的乘积非零，所以 e₄(w)=0。
这里 e_k 表示第 k 个初等对称多项式。已有 e₁(w)=e₂(w)=0。
每个四列余子式的三次系数为 6 e₃(w) e₃(α_除j)。若 e₃(w)≠0，所有 e₃(α_除j) 恒为零。
将这五式相加得 2e₃(α)=0。由 e₁(α)=0，依次展开 e₃ 和 e₂ 得
α_j(e₂(α)+α_j²)=0。于是在 K 的多项式环中，所有非零 α_j 的平方相等。
整环性质给出它们彼此只差一个正负号，与 dim K≥3 和坐标单射矛盾。
故 e₃(w)=0。w 的四个初等对称多项式全为零，推出 w=0，矛盾。

若 s=2，必有 m=5、dim K=3，且 α(K) 恰好等于关系空间 {a : ∑a_j w_j=0}。
在 w_j 张成的平面上，点积的二次型不恒为零。其零点最多是两条直线，因此恰有两个方向 u,v。
每个方向至少出现两次，否则孤立的一列系数恒为零。重排列并吸收标量后，列可写成
a u, −a u, b v, c v, −(b+c)v，且 a,b,c 独立任取。
删除第一列。在剩余四列的 permanent的三次项中，令 a=0 可得 e₃(v)=0；
再取含一次 a 的部分可得 ∑u_i v_i²=0。此处三元混合系数为 2∑u_i v_i²，
其乘数为 −a·(bc+b(−b−c)+c(−b−c))，是非零多项式。
v 的坐标和、平方和及 e₃(v) 都为零，故其坐标是 X⁴+e₄(v) 的四个根。
v 非零，故 e₄(v) 非零。缩放并重排行后可取 v=(1,i,−1,−i)。
从 ∑u_i=0、∑u_i v_i²=0 得 u=(p,q,−p,−q)。由 u·u=0 和 u、v 方向不同，
再缩放后得 u=(1,−i,−1,i)。删除最后一列，此时四次项是
−a²bc·per[u,u,v,v]=−8a²bc，不恒为零，矛盾。由此 dim K≤2。

综上，当 rank S≤2 时 dim W≤2+2=4。两种秩情形合并给出 dim L≤8。
-/

namespace LevelSpaceFive.FullRow

open Finset

abbrev Entry := Fin 5 × Fin 5 → ℂ
abbrev Row := Fin 5 → ℂ

def shifted (t : Entry) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j => 1 + t (i,j)

def cofactor (t : Entry) (j : Fin 5) : ℂ :=
  ((shifted t).submatrix Fin.castSucc j.succAbove).permanent

def lastRow (x : Row) : Entry := fun ij => if ij.1 = Fin.last 4 then x ij.2 else 0

def level (L : Submodule ℂ Entry) : Prop :=
  ∀ t ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i,e i))) = 120

def containsFullRow (L : Submodule ℂ Entry) : Prop :=
  ∀ x : Row, (∑ j, x j) = 0 → lastRow x ∈ L

private lemma expansion (L : Submodule ℂ Entry) (hl : level L) {t : Entry} (ht : t ∈ L) :
    (∑ j, (1 + t (Fin.last 4,j)) * cofactor t j) = 120 := by
  have h : (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i,e i))) = (shifted t).transpose.permanent :=
    (Equiv.embeddingEquivOfFinite (Fin 5)).sum_comp (fun e => ∏ i, (1 + t (i,e i)))
  rw [Matrix.permanent_transpose, PEqualNP.Gct.Helpers.BorderedPerm.permanent_succ_last_row] at h
  exact h.symm.trans (hl t ht)

private lemma add_last_cofactor (t : Entry) (x : Row) (j : Fin 5) :
    cofactor (t + lastRow x) j = cofactor t j := by
  apply congrArg Matrix.permanent
  ext i k
  change 1 + (t (i.castSucc,_) + (if i.castSucc = Fin.last 4 then _ else 0)) = _
  rw [ite_eq_right_iff.mpr (fun h => False.elim ((Fin.castSucc_lt_last i).ne h)), add_zero]
  rfl

private lemma cofactor_eq (L : Submodule ℂ Entry) (hl : level L) (hr : containsFullRow L)
    {t : Entry} (ht : t ∈ L) (a b : Fin 5) : cofactor t a = cofactor t b := by
  let x : Row := Pi.single a 1 - Pi.single b 1
  have hx : (∑ j, x j) = 0 := by simp [x, Finset.sum_sub_distrib, Pi.single_apply]
  have h1 := expansion L hl (L.add_mem ht (hr x hx))
  have h0 := expansion L hl ht
  change (∑ j, (1 + (t (Fin.last 4,j) + x j)) * cofactor (t + lastRow x) j) = 120 at h1
  simp only [add_last_cofactor] at h1
  have split (j : Fin 5) : (1 + (t (Fin.last 4,j) + x j)) * cofactor t j =
      (1 + t (Fin.last 4,j)) * cofactor t j + x j * cofactor t j := by ring
  simp only [split, Finset.sum_add_distrib, h0] at h1
  have h2 : (∑ j, x j * cofactor t j) = 0 := by linear_combination h1
  simpa [x, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, sub_eq_zero] using h2

theorem row_sum_and_cofactors (L : Submodule ℂ Entry) (hl : level L) (hr : containsFullRow L)
    {t : Entry} (ht : t ∈ L) :
    (∑ j, t (Fin.last 4,j)) = 0 ∧ ∀ j, cofactor t j = 24 := by
  have factor {u : Entry} (hu : u ∈ L) :
      ((5 : ℂ) + ∑ j, u (Fin.last 4,j)) * cofactor u 0 = 120 := by
    have h := expansion L hl hu
    simp_rw [fun j => cofactor_eq L hl hr hu j 0] at h
    simpa only [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one] using h
  have hz : (∑ j, t (Fin.last 4,j)) = 0 := by
    by_contra hn
    let c : ℂ := -5 / ∑ j, t (Fin.last 4,j)
    have van : (5 : ℂ) + c * (∑ j, t (Fin.last 4,j)) = 0 := by unfold c; rw [div_mul_cancel₀ _ hn]; ring
    have h := factor (L.smul_mem c ht)
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, van, zero_mul] at h
    norm_num at h
  refine ⟨hz,fun j => ?_⟩
  rw [cofactor_eq L hl hr ht j 0]
  have h := factor ht
  rw [hz,add_zero] at h
  linear_combination h / 5

-- Each of the four columns below has coordinate sum zero.
private def centered (a : Fin 3 → Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => ![a 0 j, a 1 j, a 2 j, -(a 0 j + a 1 j + a 2 j)] i

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem centered_expansion (a : Fin 3 → Fin 4 → ℂ) (z : ℂ) :
    (Matrix.of fun i j => 1 + z * centered a i j).permanent =
    24 - 2 * z^2 * (∑ i, ∑ j : Fin 4, ∑ k : Fin 4,
      if j < k then centered a i j * centered a i k else 0)
    + 2 * z^3 * (∑ i, ∑ j : Fin 4, ∑ k : Fin 4, ∑ m : Fin 4,
      if j < k ∧ k < m then centered a i j * centered a i k * centered a i m else 0)
    + z^4 * (centered a).permanent := by
  simp only [PEqualNP.Gct.Helpers.BorderedPerm.permanent_succ_last_row,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.submatrix_apply, Matrix.permanent_isEmpty]
  simp (config := {decide := true}) [centered, Fin.succAbove, Fin.castSucc, Fin.last, Matrix.of_apply]
  ring

-- The exceptional two-line calculation in the column-sum kernel.
-- The columns are v,v,u,u for v = (1,z,-1,-z), u = (1,-z,-1,z).
theorem mixed_fourth (z : ℂ) (hz : z^2 = -1) :
    (!![1,1,1,1; z,z,-z,-z; -1,-1,-1,-1; -z,-z,z,z] :
        Matrix (Fin 4) (Fin 4) ℂ).permanent = 8 := by
  simp only [PEqualNP.Gct.Helpers.BorderedPerm.permanent_succ_last_row,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.submatrix_apply, Matrix.permanent_isEmpty]
  simp (config := {decide := true}) [Fin.succAbove, Fin.castSucc, Fin.last, Matrix.of_apply]
  ring_nf
  rw [hz]
  norm_num

end LevelSpaceFive.FullRow
