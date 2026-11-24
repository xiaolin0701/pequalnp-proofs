# 五列法向线性无关时的调和三阶检验

设九维线性空间 \(L\subset\mathbb C^{5\times5}\) 满足 \(\operatorname{per}(J+X)=120\)，且有公共右法向 \(a=(e+v)/5\)，其中 \(v\cdot v=s(v)=0\)，\(e\) 是全一向量。假定五个归一化列法向 \(n_i\) 线性无关。下述三阶检验适用于任意这样的 \(v\)。其在五次单位根缩放族上给出非平凡的必要方程，特别排除了 \(v_i=2r^i\) 时五条单一 Fourier 模式的 Gram 参数。这里的 Gram 参数是额外的候选变量；该尺度的任意参数仍待研究。

## 从列法向 Gram 矩阵恢复尺度与中心坐标

写 \(B=ee^T-I\)，\(C\) 为 \(B|_{a^\perp}\) 的限制逆度量，\(G_{ij}=C_{ij}K_{ij}\)，其中 \(K_{ij}=n_i^TB^{-1}n_j\)。[切空间公式](ThreeActiveNullCut.md)给出 \(G=v\ell^T+\ell v^T\)。在所有 \(C_{ij}\ne0\) 的图中，给定一个射影参数 \([\ell]\) 即确定 \(K^*\) 到统一倍数。写 \(K=\mu K^*\)。置
\[
 w_i=B^{-1}n_i,\qquad h_i=w_i-e/20,\qquad H=e^\perp.
\]
由 \(s(n_i)=1\)，有 \(s(w_i)=1/4\) 与 \(h_i\in H\)。\(K_{ij}=B(w_i,w_j)=1/20-h_i\cdot h_j\)。五个 \(n_i\) 线性无关，等价于 \(K^*\) 可逆。因此 \(h_j\) 的 Gram 矩阵有秩四，而其零行列式依矩阵行列式引理给出
\[
   \mu=\tfrac1{20} e^T(K^*)^{-1}e\ne0,\qquad
   M=(h_i\cdot h_j)_{i,j}=ee^T/20-\mu K^* .
\]
实际上 \(w_j\) 为整个五维空间的基，减去其均值的投影 \(h_j\) 必张成 \(H\)，且 \(H\) 在普通点积下非退化。选四个独立的 \(h_j\) 作为基 \(h_{i_1},\dots,h_{i_4}\)，写其 Gram 为 \(g\)，五个 \(h_j\) 在该基的坐标为 \(U=g^{-1}M_{I,:}\)。至此每个所需矩阵均由 Gram 参数算出。

## 调和性的四个线性条件

任取 \(c\in v^\perp\)。消根给出实际方向
\[
 Z(c)=\sum_j c_j w_j\otimes Ce_j-(\ell\cdot c)e\otimes v
      =e\otimes m(c)+\sum_{a=1}^4 h_{i_a}\otimes x_a(c),
\quad m(c)=Cc/20-(\ell\cdot c)v,\quad x_a(c)=C\operatorname{diag}(U_{a,:})c .
\]
用 \(T(x,y,z)=\sum_{i,j,k\text{ 互异}}x_i y_j z_k\)。取 \(c\) 的四个基向量，在任意三个基向量间极化三阶 permanent 系数，得到二十个方程。它们对二十个未知量 \(F_{abc}=T(h_{i_a},h_{i_b},h_{i_c})\) 线性。单一方向的三次式为
\[
 \sum_{a,b,d} F_{abd} T(x_a,x_b,x_d)
 +60T(m,m,m)-9\sum_{a,b}g_{ab}T(m,x_a,x_b)=0 .
\]
其中 \(T(e,e,e)=60,\ T(e,e,h)=0,\ T(e,h,h')=-3h\cdot h'\)。\(F\) 还满足四个线性方程
\[
 \sum_{a,b}g^{ab} F_{abd}=0\quad(1\le d\le4).
\]
因为三个参数都中心化时 \(T(h,k,l)=2\sum_jh_jk_jl_j\)，而 \(H\) 的正交投影矩阵为 \(I-ee^T/5\)，每个对角元都是 \(4/5\)。对前两项作迹得到 \((8/5)s(h_{i_d})=0\)。因此真实三次矩只在十六维的调和三次型空间取值。把二十个三阶方程及四个迹方程合并为 \(A F+b=0\)，其必要条件是 \(\mathrm{rank}(A)=\mathrm{rank}([A\mid b])\)。在二十个三阶方程的首块非奇异时，实际只需先解线性方程，再检验其四个迹。

## 检验排除的开放集

令 \(v_i=t b_i\)，\(b_i=r^i\)，其中 \(r\) 为本原五次单位根，\(i=0,\dots,4\)。令 \(c_{ij}=5C_{ij}\)。选取 \(\lambda_i=b_i^d\) 与 \(K^*_{ij}=(b_i\lambda_j+b_j\lambda_i)/c_{ij}\)，实际参数为 \(\ell=\mu\lambda/(5t)\)。在 \(t=2\) 时，五种 \(d=0,1,2,3,4\) 皆与三阶条件不相容。

取 \(\mathbb Q(r)\) 在模 \(151\) 下 \(r=59\) 的约化。五种模式所得 \(\mu\) 依次为 \((111,126,58,15,67)\)。二十个极化方程的首块行列式依次为 \((111,49,50,144,51)\)，均非零。加入四个迹方程后，系数矩阵秩均为二十，增广矩阵秩均为二十一。所有被除数的约化非零，故所检验的二十一阶子式在特征零也非零。每种模式下，除了有限多个 \(t\) 外，三阶条件亦必失败，因为同一子式是关于 \(t\) 的非零有理函数。进一步，对一般 \((t,[\lambda])\) 这给出 \(\mathbb C^\times\times\mathbb P^4\) 中一个非空 Zariski 开集，其上的全秩候选均不可能。对一般固定 \(t\)，允许的全秩 \([\lambda]\) 的闭包因此至多三维。

[证书](check_five_full_gram_harmonic.py)用 `python-flint` 重新构造全部度量、四个实际方向和极化系数；从本目录运行 `python check_five_full_gram_harmonic.py`。各列法向线性相关、\(K\) 奇异或检验得到秩相等时需另行研究。
