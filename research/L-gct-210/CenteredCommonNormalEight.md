# 具有零和公共法向的五阶恒 permanent 空间至多八维

**定理。** 设 \(L\subset\mathbb C^{5\times5}\) 为复线性空间，\(J\) 为全一矩阵。若 \(\operatorname{per}(J+X)=120\) 且 \(Xa=0\) 对所有 \(X\in L\) 成立，其中 \(a\ne0,\ s(a)=0\)，则 \(\dim L\le8\)。左公共法向由转置得到同一结论。

当 \(a\cdot a=0\) 时，[一般中心迷向法向](CenteredIsotropicNormalOpen.md)、[四阶或三阶消去的情形](CenteredIsotropicResidual.md)和[三次单位根端点](CubicRootSingleNormal.md)给出八维界。余设 \(a\cdot a\ne0\)，若 \(\dim L\ge9\)，取一个九维水平子空间。

[相同退化行法向定理](CenteredEqualDegeneratePair.md)给出 \(w=e-4m\)，其中 \(s(w)=w\cdot w=1,\ w\cdot a=0\)，使仅在前两行放置 \(w,-w\) 的方向属于 \(L\)。[单坐标定理](CenteredPairSingleColumn.md)先排除 \(w\) 支撑于一格。记
\[
 \delta=s(w^{\odot3})-1,\qquad k=\operatorname{pr}_{a^\perp}(w^{\odot2}-w).
\]
[参数定理的最后一节](CenteredPairNormalParameters.md)排除 \(\delta=0\)，包括出现两个零根及倒数坐标和退化的情形。故可除以 \(\delta\)。由上述相同法向定理，\(k\cdot w=\delta,\ k\cdot k=-75\delta^2/4\)，且 \(L\) 包含一个顶两行相同、底三行相同的方向。将此方向除以 \(\delta\)，记顶行为 \(f\)，底行为 \(h\)，\(k'=k/\delta\)，则
\[
 h=4k'+75w-3e,\qquad f=-3h+150w-12e,
 \qquad s(h)=60,\quad w\cdot h=76.
\]
## 无条件八变量有理消元

设
\[
 w=(A,B,C,D,1-A-B-C-D),\qquad h=(E,F,G,H,60-E-F-G-H).
\]
在 \(\mathbb Q[A,B,C,D,E,F,G,H]\) 上，按前式令 \(k'=(h-75w+3e)/4\)，\(f=-3h+150w-12e\)，\(\delta=\sum_i w_i^3-1\)。先取四个必须为零的多项式
\[
 w\cdot w-1,\quad w\cdot h-76,\quad k'\cdot k'+75/4,\quad
 k'\cdot(w^{\odot2}-w-\delta k').
\]
末式为零因为括号是正交投影去掉的 \(a\) 分量。再令 \(t=1,2,3,4,5\)，分别取
\[
 \sum_{i<j}(1+tf_i)(1+tf_j)\prod_{k\ne i,j}(1+th_k)-10.
\]
这些式子是实际方向 \((f,f,h,h,h)\) 的仿射 permanent 除以 \(2!3!=12\) 并扣去常数。最后令 \(t=1,2,3\)，分别取
\[
 \sum_{i<j}w_iw_j\prod_{k\ne i,j}(1+th_k).
\]
因为可在前两行独立加入 \(+sw,-sw\)，上式是沿这一条反向行对的二次项除以非零常数。这样共有十二个有理多项式。

[可复现检验](check_centered_equal_pair_level.py)的 `--unrestricted` 选项直接由这十二式构造八变量有理多项式环及理想。Singular 4.4.1 的 `slimgb` 用有理系数返回约化 Gröbner 基 \([1]\)，一次实测 602.78 秒。整个计算允许 \(w,h\) 的各坐标互异。八变量方程在复数域无解，与这两个实际方向共存矛盾。证毕。

Singular 已在 PATH 中时，可运行 `python3 L-gct-210/check_centered_equal_pair_level.py --unrestricted`。可用 `--singular /path/to/Singular` 指定安装位置，用 `--emit /tmp/centered-eight.sing` 保存完整的有理输入。

较快的复核路径采用[三种支撑的重复坐标证明](CenteredPairNormalParameters.md)，它在 \(\delta\ne0\) 时保证 \(w,h\) 至少有同一对相等坐标。相应地，去掉 `--unrestricted` 计算六变量的同一组方程，同样给出有理基 \([1]\)。
