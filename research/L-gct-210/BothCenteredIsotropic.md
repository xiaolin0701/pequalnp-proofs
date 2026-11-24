# 两个零和迷向公共法向量的八维界

设 \(a,b\in\mathbb C^5\) 非零且
\[
 s(a)=s(b)=a\cdot a=b\cdot b=0,\qquad s(x)=\sum_i x_i .
\]
若五阶复矩阵方向空间 \(L\) 满足 \(Xa=0,\ b^TX=0,\ \operatorname{per}(J+X)=120\)，则 \(\dim L\le8\)。点积为复双线性。

置 \(U=b^\perp,\ V=a^\perp\)。五阶 permanent 的二阶项的极化在 \(E=U\otimes V\) 上是 \((J-I)|_U\otimes(J-I)|_V\)，相差非零常数。其中两个因子的根基分别为 \(\mathbb Cb,\mathbb Ca\)。故 \(E\) 的根基为
\[
 R=U\otimes a+b\otimes V,\qquad \dim R=7 .
\]
非退化商九维，全迷向子空间至多四维。若 \(L\) 为九维，则 \(M=L\cap R\) 至少五维。设两种秩一方向的系数空间为
\[
 P=\{p\in U:p a^T\in M\},\qquad D=\{q\in V:bq^T\in M\}.
\]
因为 \(U\otimes a,b\otimes V\) 都在七维 \(R\) 内占四维，\(P,D\) 各至少二维。把 \(X\in R\) 写成 \(p'a^T+b(q')^T\) 时，\([p']\in U/\langle b\rangle,\ [q']\in V/\langle a\rangle\) 唯一。

## 一边的纯方向空间恰为二维

不妨 \(\dim P=2\)。\(M\to V/\langle a\rangle\) 核维二，而定义域至少五维、目标三维，故满射。全一向量 \(\mathbf1\in V\)，可取其提升写作 \(p'a^T+b\mathbf1^T\)。若 \(b_i\ne0\) 且存在 \(p\in P\) 有 \(p_i\ne0\)，向提升加适当的 \(p a^T\) 倍数后，第 \(i\) 行成为 \(b_i\mathbf1^T\)。该非零常数行经全矩阵缩放可使 \(J+X\) 出现一整行零，矛盾。因此 \(P\) 只用 \(b\) 的零格。非零、零和、平方和零的 \(b\) 至少有三个非零格。故 \(b\) 恰有三个活动格，\(P\) 是对应两个零格的完整坐标平面。

于是 \(e_3(b)\ne0\)。对秩一方向 \(bq^T\)，三次系数正比于 \(e_3(b)e_3(q)\)，故 \(D\) 包含在 \(e_3=0\) 中。[五变量 \(e_3\) 不含三维线性零空间](ZeroSumCommonNormal.md)表明 \(\dim D\le2\)，因而 \(\dim D=2\)。对称使用上一段可得 \(a\) 也恰有三个非零坐标，故 \(\sum_j a_j^3=3e_3(a)\ne0\)。

令 \(T=\operatorname{supp} b\)。在其余两个位置分别取一条仅在该行有 \(a^T\) 的方向，上段的完整坐标平面 \(P\) 保证它们独立属于 \(L\)。将此两方向与任意 \(X\in M\) 取三次混合系数，对列指标容斥，并使用 \(s(a)=a\cdot a=0\)，所得约束为
\[
 a^2\cdot\sum_{r\in T}X_{r,*}=0.
\]
对 \(X=p'a^T+b(q')^T\)，因 \(s(b)=0\)，行和向量 \(\sum_{r\in T}X_{r,*}\) 等于 \((\sum_{r\in T}p'_r)a^T\)。\(a^2\cdot a\ne0\) 迫 \(\sum_{r\in T}p'_r=0\)。这一条件在模 \(b\) 时保持。另一方面，\(\dim D=2\) 使 \(M\to U/\langle b\rangle\) 同样满射，因此允许 \([p']=[\mathbf1]\)，而在 \(T\) 上的和为三，矛盾。

## 两边纯方向空间都至少三维

由秩一三次项和 \(e_3=0\) 中没有三维线性空间，得 \(e_3(a)=e_3(b)=0\)。若 \(e_4(a)\ne0\)，则 \(e_4\) 在至少三维的 \(P\) 上恒零，[四次式的倒数和论证](ZeroSumCommonNormal.md)证明 \(P\) 恰是支撑在三个格上的完整坐标空间。因 \(P\subset b^\perp\)，\(b\) 在该三格恒零，与中心迷向向量至少三个非零坐标矛盾。因此 \(e_4(a)=e_4(b)=0\)。

\(a,b\) 的前四个初等对称式均零且两者非零；各自缩放后均为五个互异的五次单位根。\(e_5(a)e_5(b)\ne0\)，故 \(P,D\) 各有一格恒零。因 \(a,b\) 五格皆非零，维数又各至少三，我们得到
\[
  P=\{p:p_i=0,\ b\cdot p=0\},\qquad
  D=\{q:q_j=0,\ a\cdot q=0\}
\]
对某两个索引 \(i,j\) 成立。

取一份 \(pa^T\)、两份 \(bq^T\) 的三次混合系数，它除去非零常数是
\[
 \left(\sum_r p_r e_2(b_{\hat r})\right)
 \left(\sum_t a_t e_2(q_{\hat t})\right)
       =(p\cdot b^2)(a\cdot q^2).
\]
右式使用 \(s(b)=e_2(b)=s(a)=a\cdot q=0\)。第一个因子在 \(P\) 上不恒为零，因为 \(b^2\notin\langle b,e_i\rangle\)：余下四格的 \(b\) 坐标非零且互异。因此三维 \(D\) 必使 \(a\cdot q^2=0\) 恒成立。在其四个可动位置，\(\operatorname{diag}(a)\) 非退化，最大全迷向维数却仅为二，矛盾。
