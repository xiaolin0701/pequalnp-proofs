# 五阶全一矩阵 permanent 水平空间的一般复数上界为十

对 \(J=(1)_{5\times5}\)，若复矩阵线性空间 \(L_0\) 满足每个 \(X\in L_0\) 都有 \(\operatorname{per}(J+X)=120\)，则 \(\dim L_0\le10\)。

若有十一维复解，Grassmannian 上的有理系数闭条件在 \(\overline{\mathbb Q}\) 上有点，故存在数域上的十一维解。作[二进整坐标变换](RescaledMatchingAtTwo.md)，在数域的二进赋值处利用 Grassmannian 的射影性，得到可提升的特征二十一维平面 \(L\)。以下可把剩余域扩到其代数闭包 \(K\)。处理分歧使用整多项式与系数最小赋值，论证对全部分歧指数成立。

## 两侧的纯方向

在 \(H=\{a\in K^5:s(a)=0\}\) 上令 \(q=e_2\)，\(\sigma\) 为点积，记 \(\operatorname{pr}_H\) 为沿全一向量的投影。模二四次式迫至少一侧边际像全落在 \(q=0\)，交换后设为 \(b\) 侧。前置[单边秩分类](RescaledMarginalOne.md)及其[二维对侧证明](RescaledMarginalOneTwo.md)给出：\(b\) 像恰是一张二维全奇异平面 \(R\)，其中纯 \(b\) 向量恰为线 \(Kv\)，且 \(\operatorname{pr}_H(v^{\odot3})\in R\)。写 \(b=tv+\ell(c,D)z\)，\(z\) 是补基，\(\ell\ne0\)，而 \(T=\{(c,D)\}\) 是其二十维环境中的十维自对偶空间。

回顾全奇异平面的 Fourier 坐标。取五次本原根，令 \(f_i\) 在五个根 \(y\) 处的坐标为 \(y^i\)。经坐标置换可令
\[
 R=\langle A=f_1+\tau f_3, B=f_2+\tau f_4\rangle .
\]
原证明中的两族、无穷参数均由坐标置换覆盖。在 \(b=uA+hB\) 上，\(b^{\odot3}\) 与 \(A,B\) 的点积组成 \((u+\tau^2h)^2(h,u)\)，故特殊线由 \(v=\tau^2 A+B\) 生成。逐元素求和还给
\[
 e_3(uA+hB)=s((uA+hB)^{\odot3})
       =(u+\tau^2h)(\tau u^2+h^2).
\]
这里 \(s(f_i)\) 仅在 \(5\mid i\) 时非零。因此 \(e_3\) 在每张这样的平面上都是非零多项式，而在其特殊线上为零。

记 \(C\) 为 \(c\) 像。若 \(q|_C\ne0\)，[四次式的可除性](RescaledMarginalOne.md)迫 \(\bar\Phi|_L\) 被 \(q(c)\) 整除；在纯 \(b\) 线上取值得 \(e_4(v)=0\)。于是 \(s(v)=e_2(v)=e_3(v)=e_4(v)=0\)，各坐标为 \(Z^5+e_5(v)\) 的根，且 \(e_5(v)\ne0\)。特征二中这五根各异，所以 \(v^{\odot5}=d\mathbf1\)，\(d\ne0\)，并且 \(z=v^{\odot3}\) 是 \(R\) 的合法补基。五次式 \(t^2\) 系数给
\[
 (v^{\odot2}\odot z)^TDc=e_{21}(v,z)q(c)
\]
（提取后消去非零线性型 \(\ell\)）。左方因 \(D\) 零列和而为零；右方 \(e_{21}(v,z)=\sum_i v_i^2 z_i=d\ne0\)。矛盾。故 \(q|_C=0\)。对换两侧，得到 \(C\) 也是二维全奇异平面，纯 \(c\) 线 \(Kw\) 也是其特殊线。

## 全部候选的矩阵块

由于 \(T\) 自对偶且 \(C=C^\perp\)，所有纯 \(c\in C\) 都在 \(T\) 中。写 \(T=C\oplus U\)，其中 \(U\) 是八维矩阵子空间。选 \(y\) 补 \(w\) 使得在整个 \(L\) 上
\[
 b=tv+s z,\qquad c=kw+r y,\qquad s=r+\ell_U(D),\quad D\in U.
\]
理由是 \(C\) 的真纯轴恰为 \(Kw\)，所以 \(\ell|_C\) 非零，可归一化为 \(r\)。此时 \(t,k,r\) 可与 \(D\) 独立选取。

三次方程依次比较 \(t\) 系数与常数项并消去非零 \(s\)，得到 \(v^TDc=z^TDc=0\)；即 \(D(C)\subset R\) 及 \(D^T(R)\subset C\)。令
\[
 A_D=D|_C:C\longrightarrow R,\qquad B_D=D^T|_R:R\longrightarrow C.
\]
记 \(\varepsilon_R,\varepsilon_C\) 为上述各二元基下取值一的交替面积形式。由 Fourier 公式，存在非零常数 \(\kappa_R,\kappa_C\)，使得在 \(a\in R,h\in C\) 时
\[
 b^{\odot3}\cdot a=\kappa_R s^2\varepsilon_R(b,a),\qquad
 c^{\odot3}\cdot h=\kappa_C r^2\varepsilon_C(c,h).
\]
由于 \(q(b)=q(c)=0\)，五次式化为
\[
 \kappa_R s^2\varepsilon_R(b,A_D c)+
 \kappa_C r^2\varepsilon_C(c,B_D b)=0 .
\]
在自由参数 \(t,k\) 中比较 \(tk,t,k,1\) 项，再按需消去非零因子 \(r,s,rs\)，可得任意一对基向量 \(e\in\{v,z\},f\in\{w,y\}\) 都满足
\[
 \kappa_R s^2\varepsilon_R(e,A_D f)
 =\kappa_C r^2\varepsilon_C(f,B_D e).
\]
若 \(\ell_U\ne0\)，令 \(r=0\)，由参数多项式环无零因子可知 \(A_D=0\) 恒成立；再代回得 \(B_D=0\)。此时 \(U\subset\operatorname{Hom}(H/C,R)\) 至多四维，矛盾。故 \(s=r\)，且
\[
 B_D=\lambda A_D^\dagger,\qquad \lambda=\kappa_R/\kappa_C\ne0,
\]
其中 \(\dagger\) 用两个面积形式取伴随。二阶矩阵中 \(A^\dagger=\operatorname{adj}(A)\)，即 \(A A^\dagger=\det(A)I_R\)，\(A^\dagger A=\det(A)I_C\)。

各取与 \(R,C\) 成辛对偶的拉格朗日补基后，所有满足上述条件的矩阵必为
\[
 D=\begin{pmatrix}A&G\\0&\lambda(A^\dagger)^T\end{pmatrix}.
\]
上标 \(T\) 在这个分块表达中是普通二阶矩阵转置。八维 \(U\) 因而恰包含所有四参数 \(A\) 与四参数 \(G\) 的取值。以下只需 \(G=0\) 的线性截面。相对 \(H\) 原来的辛点积取伴随时，对角块交换后转置，所以此截面上
\[
 DD^T=D^TD=\lambda\det(A) I_H .
\]
将矩阵放回五坐标表示，右方是 \(\lambda\det(A)\operatorname{pr}_H\)，非对角元均等于 \(\lambda\det(A)\)。

## 四次余项无法分解

[二十四元整数系数恒等式](check_rescaled_quartic.py)给 \(f_4=q(b)q(c)+2\Phi\)，并给出 \(\bar\Phi\) 的表达。上节截面的行点积、列点积在不同指标上都等于 \(\lambda\det(A)\)，因此含两个 \(D\) 的项之和为 \(\lambda\det(A)(q(b)+q(c))=0\)。剩
\[
 P=e_4(b)+e_4(c)+F_A,\qquad
 F_A=b^{\odot2}\cdot (Ac)+\lambda c^{\odot2}\cdot (A^\dagger b),
 \quad b=t v+r z,\ c=k w+r y.
\]
在 \(r=1\) 的仿射截面，四个 \(A\) 系数的共同零点只有有限多个。事实上，若对每个 \(A:C\to R\) 都有 \(F_A=0\)，取 \(Ac=0\) 且任意指定另一基向量的像。由面积伴随的定义，\(A^\dagger b\) 此时可跑遍 \(Kc\)（\(b,c\ne0\)）；故 \(c^{\odot2}\cdot c=e_3(c)=0\)。同理固定 \(A^\dagger b=0\) 可使 \(Ac\) 跑遍 \(Kb\)，故 \(e_3(b)=0\)。在该截面上，这两个非零单变量方程分别只含 \(k,t\)；非零性来自上述 Fourier 三次式及二元齐次性。于是共同零集有限。特别地 \(F_A\) 真正依赖 \(A\)，\(P\) 关于全体 \(A\) 变量的次数恰为一。

若有整线性提升，代入提升的七个截面基向量，可知非零 \(P\) 必为两个齐次二次式的乘积，见[局部提升障碍](RescaledMarginalOneTwo.md)。次数相加迫其中一因子 \(Q(t,k,r)\) 与 \(A\) 无关；它必须整除 \(F_A\) 的全部系数以及 \(e_4(b)+e_4(c)\)。若 \(Q(t,k,1)\) 非常数，它在代数闭域中有一条零点曲线，与共同零集有限矛盾。因此由齐次性，\(Q\) 是非零标量乘 \(r^2\)。

在 \(r=0\) 上，\(t^4e_4(v)+k^4e_4(w)=0\)，所以 \(e_4(v)=e_4(w)=0\)。如首节，\(v\) 的五格是缩放的五次根，\(v^{\odot3}\) 与 \(v\) 张成 \(R\)，\(v^{\odot2}\cdot v^{\odot3}\ne0\)。选 \(A\) 使 \(Aw=v^{\odot3}\)。在同一截面上
\[
 F_A=t^2k\,(v^{\odot2}\cdot Aw)+\lambda tk^2\,(w^{\odot2}\cdot A^\dagger v).
\]
第一个单项式系数非零，与 \(r\mid F_A\) 矛盾。这排除了可提升的十一维平面，证明复数上界。
