# 五次根共面法向端点的三阶矛盾

设复九维矩阵方向空间 \(L\) 满足每个 \(X\in L\) 都有 \(\operatorname{per}(J+X)=120\) 及 \(Xa=0\)，其中 \(a=(e+v)/5\)、\(e=(1,1,1,1,1)^T\)。若 \(v_j=t r^j\)（\(0\le j<5\)，\(r\) 为本原五次单位根）且 \(24t^5=1\)，则 **五条归一化列法向不能共仿射平面**。下述矛盾取自 \(L\) 中四个已知方向的三阶 permanent 系数。

## Gram 参数的特征零轨道

记 \(B=ee^T-I\)，\(C=B^{-1}-(e-4v)(e-4v)^T/20\)，\(K_{ij}=n_i^TB^{-1}n_j\)，并设 \(\lambda\) 满足
\[
 C_{ij}K_{ij}=v_i\lambda_j+v_j\lambda_i .
\]
[单轴及零参数排除](FivePlanarColumnSingleAxis.md)使 \(\lambda\) 至少有两个活动格。若 \(m,n\) 活动，以 \(m+i(n-m)\pmod5\) 为新的第 \(i\) 格。此时 \(t'=v_m\)、\(r'=r^{n-m}\) 仍满足相同方程。于是可令前两格都活动，取 \(\lambda=k\ell\)、\(\ell_0=1,\ell_1\ne0,k\ne0\)，并记 \(K=k H\)。

令 \(\delta_{ij}=1+v_i+v_j-4v_iv_j-5\mathbf1_{i=j}=5C_{ij}\)。在这个端点，十五个 \(\delta_{ij}\ (i\le j)\) 均非零。这也可在下面的特征 \(131\) 点逐一核实，因为 \(t\) 的五个根与 \(r\) 的四个本原值组成一个有理 Galois 轨道（\(x^5-24\) 在 \(3\) Eisenstein，扩张次数五与四互素）。因此 \(H\) 由 \(C_{ij}H_{ij}=v_i\ell_j+v_j\ell_i\) 决定。共面条件迫使五乘四矩阵 \((H_{ij}-H_{i4})_{i<5,j<4}\) 的三阶子式全零，因为四个法向差张成至多二维。计算有理系统时，取这四十个子式，加入 \(24t^5-1\)、\(r^4+r^3+r^2+r+1\)、\(q\ell_1-1\)。所有 \(\delta_{ij}\) 均非零，故可乘公共分母。将 \(v_i\) 换成 \(r^i\) 计算 Gram 分子只使 \(H\) 整体除以非零的 \(t\)，所取子式的零点保持相同。

在此图上，msolve 的有理单变量表示给出二百个几何点，分离参数的二百次多项式在 \(\mathbb Q\) 上不可约。所有候选因而同属一个 Galois 轨道。模 \(131\) 的一个单根给出
\[
  t=76,\quad r=53,\quad \ell=(1,127,43,50,47).
\]
证书从有理表示还原上述各坐标，并检查分离参数的导数与所有坐标分母在该根均非零。因此下文在该点得到的非零行列式会给出二百个特征零候选上同一行列式的非零性。把图的逆元换成 \(q\ell_2=1\) 独立求解也得到同一分离多项式及同一组物理参数。

## 消去十个未知三阶矩

令 \(\Phi\) 的三行 \(\phi_0,\phi_1,\phi_2\) 分别取 \(e^T\)、\(H\) 的第零行、第一行。在上述点，\(\Phi\) 是满行秩矩阵，其前三列可逆，并有唯一非退化对称矩阵 \(M\) 满足 \(H=\Phi^T M\Phi\)。事实上 \(H\) 秩为三，归一化使 \(e^T\) 属于它的行空间。三个向量 \(w_0,w_1,w_2\) 因此可表示五个真实行因子
\[
 B^{-1}n_j=\sum_{s=0}^2\phi_{sj}w_s .
\]
这里用到 \(n_j\) 的线性张成维数至多三，而它已因 \(H\) 满三秩达到三。由 \(s(n_j)=1\) 及 \((B^{-1}n_i)^TB(B^{-1}n_j)=kH_{ij}\)，得到 \(s(w_s)=\mathbf1_{s=0}/4\) 及 \(w_s^TBw_d=k M_{sd}\)，其中 \(s(x)=\sum_i x_i\)。

对任意 \(c\in v^\perp\)，令 \(x_s=C\operatorname{diag}(\phi_s)c\) 及 \(h=\ell\cdot c\)。[切空间中的实际方向](ThreeActiveNullCut.md)给出
\[
 X(c)=\sum_{s=0}^2 w_s\otimes x_s-kh\,e\otimes v\in L .
\]
写 \(T(x,y,z)=\sum_{i,j,l\ {\rm distinct}} x_i y_j z_l\)。有 \(T(e,w_s,w_d)=3kM_{sd}\)、\(T(e,e,w_s)=3\mathbf1_{s=0}\)，且 \(T(v,v,v)=0\)，因为五次根的前三个幂和为零。对 \(X(c)\) 取 permanent 的三次系数，在 \(s,d,f\in\{0,1,2\}\) 上得到
\[
 \sum_{s,d,f} T(w_s,w_d,w_f)\,T(x_s,x_d,x_f)
 +9 k^2\left[h^2T(v,v,x_0)-h\sum_{s,d} M_{sd}T(v,x_s,x_d)\right]=0 .
\]
因此十个对称行侧三阶矩以及 \(9k^2\) 是一个十一元线性齐次系统的解，且其末坐标非零。

令 \(b_j=e_j-(v_j/v_4)e_4\ (0\le j<4)\)。按字典序列出允许重复的三元组 \(0\le i\le j\le l<4\)，取 \(c=b_i+b_j+b_l\)。同样按字典序排列十个行侧三阶矩，合并相同矩时乘上排列重数。上述二十条等式的前十一条即构成可逆方阵：在给定剩余域点上，方阵中最后一列取方括号内的量，行列式为 \(113\pmod{131}\)。因此必须 \(k^2=0\)，与 \(\lambda\) 的活动格相矛盾。

[独立复核入口](check_five_planar_endpoint_cubic.py)使用 python-flint、Singular 与 msolve，从子式重建有理单变量表示，再检查不可约性、剩余域点和三阶行列式。运行 `python check_five_planar_endpoint_cubic.py --singular /path/to/Singular --msolve /path/to/msolve`，传入 `--other-chart` 可复核另一图。
