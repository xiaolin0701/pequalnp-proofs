# 十一维二进极限的全奇异边际像必须恰为二维

在[重缩放模型](RescaledMatchingAtTwo.md)中，设特征二特殊纤维的十一维线性解 \(L\) 来自混合特征离散赋值环上的线性提升。四次式迫至少一个边际像满足 \(q=e_2=0\)。交换两侧，设为 \(b\) 像，它的维数至多二。它的维数不能为零，因为 \(b=0\) 的二十维空间中二次型非退化，最大全奇异维数为十。下文排除维数一。

若 \(b\) 像为 \(Kv\)，则 \(L=Kv\oplus T\)，\(T\subset H_c\oplus\operatorname{End}(H)\) 十维自对偶，见[二维另一边际的证明](RescaledMarginalOneTwo.md)。写 \(C=\operatorname{pr}_cT, k=\dim C, U=\{D:(0,D)\in T\}\)。纯 \(c\) 子空间恰为 \(C^\perp\)，其中所有向量满足 \(q=0\)，所以 \(2\le k\le4\)。上引证明已排除 \(k=2\)。设 \(k=3\) 或 \(4\)。有 \(\dim U=10-k\)，而 \(D(T)=U^\perp\) 的维数为 \(6+k\)，这里的正交是矩阵逐项点积。后一个等式由自对偶性和纯 \(c\) 子空间的维数 \(4-k\) 得出。

## 三维超平面与三次坐标幂

若 \(w\ne0, q(w)=0, C=w^\perp\subset H\)，则
\[
 C+\langle\operatorname{pr}_H(c^{\odot3}):c\in C\rangle=H.
\]
否则 \(\sum w_i c_i^3=0\) 恒成立，极化后得 \(w\odot c^{\odot2}\in\langle\mathbf 1,w\rangle\) 对所有 \(c\in C\) 成立。设 \(m=|\operatorname{supp}(w)|\)。由 \(s(w)=q(w)=0\) 有 \(m\ge3\)。若 \(m=5\)，左方像的维数三，而右方维数二。若 \(m=3,4\)，右方限制为支撑在这 \(m\) 格内时只余 \(Kw\)；而 \(C\) 中支撑在补集内的向量组成至多 \(4-m\) 维的空间，故左方像的维数至少 \(3-(4-m)=m-1\ge2\)。这里在代数闭剩余域中取平方不改变子空间的维数。

另一条引理是：若 \(A:C\to H\) 线性，\(A(w)=0\)，且 \((Ac)\cdot c=(Ac)\cdot c^{\odot3}=0\) 对所有 \(c\in C=w^\perp\) 成立，则 \(A=0\)。第一式用 \(c+t w\) 极化，得 \(Ac\in C\)。在二维辛商 \(C/Kw\) 上，\((c,c')\mapsto (Ac)\cdot c'\) 为交替双线性型，必为辛型的标量倍。因此 \(Ac=\alpha c+\ell(c)w\)。因 \(c\cdot c^{\odot3}=s(c)^4=0\)，第二式化为 \(\ell(c)(w\cdot c^{\odot3})=0\)。由上一段，后因子非零，故 \(\ell=0\)。再代入 \(w\) 得 \(\alpha=0\)。

## 四次式的可除性

在剩余域上 \(q|_C\ne0\)，因为其极化的最大全迷向子空间至多二维。写 \(f_4=q(b)q(c)+2\Phi\)。提升迫 \(\bar\Phi|_L\) 被 \(q|_C\) 整除：若 \(\Phi\) 特化不为零，比较 \(q(b)q(c)=-2\Phi\) 两侧系数的最小赋值并约化即可；若特化为零整除也成立。此时 \(b=t v\) 为纯方向。从 \(t^4\) 项得 \(e_4(v)=0\)，因为这个常数若非零就不可能被 \(q(c)\) 整除。前引二维情形的坐标种数论证给出 \(v,u=\operatorname{pr}_H(v^{\odot3})\) 独立。它们互相正交，所以 \(K_2=\langle v,u\rangle=K_2^\perp\)。

在前引二维情形的 \(\bar\Phi\) 展开中，去掉 \(q(b)=q(c)=0\) 要求只多出 \((q(b)+q(c))r_2(D)\)。这个完整的二进整系数公式也可通过[二十四元整多项式核验](check_rescaled_quartic.py)检查。因此在 \(L\) 上，\(t^2\) 系数为
\[
 (v^{\odot2})^TDc+B_v(D)=\lambda q(c),\qquad
 B_v(D)=\sum_{i<j}v_i v_j(D_i\cdot D_j)
\]
对某个标量 \(\lambda\) 成立，理由是两边均为齐次二次式。

## 三次与五次式迫第一个收缩恒零

对三、五次式在 \(t\) 中取系数，并将 \(D\) 改为 \(D+D_0\)（\(D_0\in U\)），得
\[
 v^TDc=0,\quad v^TD(c^{\odot3})=0,\quad u^TDc=e_3(v)q(c),\qquad
 D_0^Tv=0,\quad u^TD_0(C)=0 .
\]
其中 \(D_0^Tv=0\) 由 \(C\) 与其投影坐标立方的生成性得出，当 \(C=H\) 时已由三次式得到。于是 \(A:C\to H,\ A(c)=D^Tv\) 与 \(D\) 的代表选择无关，并且 \((Ac)\cdot c=(Ac)\cdot c^{\odot3}=0\)。

若 \(k=3\)，\(C=w^\perp\)，非零 \(w\) 是纯 \(c\) 方向，\(q(w)=0, A(w)=0\)。超平面引理直接给 \(A=0\)。

若 \(k=4\)，则 \(U\subset K_2\otimes H\)，且这个八维空间在矩阵点积下自对偶。所以 \(K_2\otimes H\subset U^\perp=D(T)\)，商维数二，且 \(D\mapsto D^Tv\) 在 \(K_2\otimes H\) 上为零。故 \(A:H\to H\) 的秩至多二。取 \(\ker A\) 中非零 \(q\)-奇异向量 \(w\)：代数闭域中二维向量空间上的齐次二次式必有射影零点。将 \(A\) 限制到 \(w^\perp\) 后，超平面引理推出 \(A|_{w^\perp}=0\)。因此 \(\dim\ker A\ge3\)，其中还可以选取一个不与 \(w\) 成比例的非零 \(q\)-奇异向量（在不含 \(w\) 的二维子空间中取射影零点）。同理第二个不同的超平面也被 \(A\) 杀掉，故 \(A=0\)。

## 最后的矛盾

从 \(D(T)=U^\perp\) 及 \(A=0\) 得 \(v\otimes H\subset U\)。对任意 \(a\in H\)，在 \(t^2\) 系数恒等式中分别代入 \(D\) 和 \(D+v\otimes a\)。相减后，第一项贡献 \(e_3(v)(a\cdot c)\)，这里 \(s(v^3)=e_3(v)\)。纯张量的 \(B_v\) 自项为零。极化项为
\[
 \sum_{i<j}v_i v_j (v_iD_j+v_jD_i)\cdot a
 =\sum_i v_i^3 D_i\cdot a=(D^Tu)\cdot a,
\]
因为 \(\sum_i v_i^2=0\) 且 \(D^T\mathbf 1=0\)。于是 \(D^Tu=e_3(v)c\)。结合五次式的 \(u^TDc=e_3(v)q(c)\)，因 \(c\cdot c=0\) 且 \(q(c)\) 非零，得到 \(e_3(v)=0\)。故 \(D^Tu=D^Tv=0\) 在整个 \(T\) 上成立，迫 \(D(T)\subset K_2\otimes H\)，但 \(\dim D(T)=6+k>8\)，矛盾。

## 二维边际像中的纯方向

设 \(R\) 为上述二维 \(q\)-全奇异边际像，\(P=\{b:(b,0,0)\in L\}\)。则 \(P\) 必为一维，且其生成元 \(v\) 满足 \(\operatorname{pr}_H(v^{\odot3})\in R\)。

首先，\(L\) 投影至 \((c,D)\) 仍全奇异，因为整个 \(R\) 满足 \(q=0\)。二十维非退化二次型给投影维数至多十，所以 \(\dim P\ge1\)。若 \(P=R\)，则 \(L=R\oplus T\)，\(\dim T=9\)。记 \(C\) 为 \(c\) 像、\(k=\dim C\)，\(U\) 为纯矩阵核，\(\dim U=9-k\)。若 \(q|_C\ne0\)，则 \(\bar\Phi|_L\) 被 \(q(c)\) 整除，在纯 \(R\) 上取值迫 \(e_4|_R=0\)，与前引二维平面的非零微分矛盾。因此 \(q|_C=0\)。以任意纯 \(b\in R\) 考察三、五次的系数，再用 \(D+D_0\) 减去 \(D\) 得
\[
 U(C)=0,\qquad U(\operatorname{pr}_H(c^{\odot3}))\subset R\quad(c\in C).
\]
第一式使用 \(R+\langle\operatorname{pr}_H(b^{\odot3})\rangle=H\)。由 \(9-k\le 8\) 及 \(q|_C=0\)，有 \(1\le k\le2\)。\(k=1\) 由以上单边秩一结果的转置排除；\(k=2\) 时，\(C\) 与其坐标立方的生成性给出 \(U\subset\operatorname{Hom}(H/C,R)\)，与 \(\dim U=7\) 矛盾。

现记 \(P=Kv, R=\langle v,z\rangle\)。可唯一写
\[
 L=\{(tv+\ell(c,D)z,c,D):(c,D)\in T,\ t\in K\}
\]
其中 \(\ell\) 非零线性型且 \(T\) 在二十维 \((c,D)\) 空间上十维自对偶。三次式按 \(t\) 展开，得 \(v^TDc=z^TDc=0\)，后式由 \(\ell z^TDc=0\) 消去非零因子。五次式的 \(t^3,t^2\) 系数分别给
\[
 (v^{\odot3})^TDc=e_3(v)q(c),\qquad
 (v^{\odot2}\odot z)^TDc=e_{21}(v,z)q(c),
\]
其中 \(e_{21}\) 是 \(e_3(tv+sz)\) 的 \(t^2s\) 系数，第二式也消去了 \(\ell\)。于是纯矩阵 \(D_0\) 的 \(D_0(C)\) 正交于 \(R,v^{\odot3},v^{\odot2}\odot z\)。

设 \(\operatorname{pr}_H(v^{\odot3})\notin R\)。在重缩放模型原文的 Fourier 坐标中，\(\operatorname{pr}_H(b^{\odot3})\) 模 \(R\) 的类形如 \(a(b)^2 J(b)\)，其中 \(a\) 为非零线性型、\(J:R\to H/R\) 为线性同构。由假设 \(a(v)\ne0\)。在 \(b=v+xz\) 中取 \(1,x\) 系数，得上述两个三次向量模 \(R\) 独立。因此 \(U(C)=0\)，而 \(\dim U=10-k\) 强制 \(10-k\le 4(4-k)\)，故 \(k\le2\)。自对偶性又给 \(k\ge2\)。于是 \(C=C^\perp\) 是纯 \(c\) 平面，\(U=H\otimes C\)，维数八，\(T=C\oplus U\)。在此整个 \(T\) 上 \(Dc=0, q(c)=0\)。五次式只余 \((tv+\ell z)^TD(c^{\odot3})=0\)，消去 \(\ell\) 得 \(D(c^{\odot3})\in R\) 对所有 \(c,D\) 成立。然而某个 \(c\) 的投影立方不属于 \(C\)；对这个 \(c\)，\(D\) 跑遍 \(H\otimes C\) 可得整个 \(H\)，矛盾。故 \(a(v)=0\)，这给出了 \(R\) 中唯一的可能纯线。
