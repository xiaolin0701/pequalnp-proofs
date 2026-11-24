# L-meta-1343 的第 10 号搜索分片

本目录实现 `w1006` 的单调电路搜索，固定 `JUNK2=1`、`FIRSTJ=10`（门位置从零起）。项目指引所列 `notes/meta-small-exact/sat_mono_rows_junk2.py` 不在当时的上游主线，GitHub 对该路径的提交历史为空。本地程序按公开陈述重新编码。

## 输入与完备性

图的 11 个顶点、16 条边逐项取自正式 Lean 目标。输出单调，因此在 16 个两端点输入上接受、在 24 个极大独立集输入上拒绝，当且仅当它在全部 2048 个输入上恰好计算边函数。某门的函数未被边函数逐点支配，当且仅当它在至少一个极大独立集上接受。`shard.py` 以此给每个不安全的 AND 门设一标记，强制前十个标记为假、第十号为真、后续至少一个为真。

每个门选两个先前的 wire 和 AND/OR 操作。两端点按索引升序，允许相等。原始真、假常量单独建模，使空输入 AND、空输入 OR 与越界读均可表示。一输入门可重复使用同一输入。允许无用门，允许任何门作为输出。真正的图函数没有单个变量或常量输出，因此无需以原始输入作输出选项。每个至多 21 门的本分片电路都可用恒假 OR 从尾部补到正好 21 门，保留旧门编号、语义和非安全 AND 集。反过来，如找到使用免费常量的 SAT 见证，可用常量传播与直通门消除去除所有常量，得到至多同样多门的原始电路；门数和全输入的输出真值必须再核对方可按官方反命题提交。

## 运行与验证

```
mkdir -p run
python3 shard.py encode run/first10.cnf --gates 21 --first 10
cadical --lrat --report -w run/first10.model run/first10.cnf run/first10.lrat.gz
python3 shard.py decode run/first10.json run/first10.model
gzip -dc run/first10.lrat.gz | lrat-trim -S --no-trim run/first10.cnf -
```

SAT 时运行解码，它独立重算 2048 个输入及全部非安全 AND 的位置。UNSAT 时用 `lrat-trim` 检查 LRAT，必须得到 `s VERIFIED`、退出码 20；解压也必须以零退出。`lrat-trim` 源码版本是 `423194927df747528d5b7364806b5b77b2660c12`。CaDiCaL 来自 Lean 4.36.0 工具链，版本 2.1.2。

`python3 validate_search.py /path/to/cadical` 构造一个 22 门的合法覆盖电路，在第 10、11 个位置插入两道无用、不安全的 AND，以这个已知电路固定所有 SAT 选择。求解器返回 SAT，脚本得到正确的 24 门结构，并重算全部 2048 个输入。这同时测试正负极值输入的完备性。另用 `--gates 2 --first 0` 生成无解小例，CaDiCaL 的压缩 LRAT 已通过独立 `lrat-trim` 检查。

本次 `shard.py` SHA-256 为 `4daedae736eda607c2f69c45292f1b87ea58044820bbe5d8387621f414479a48`。目标 CNF 有 3549 个变量、79225 条子句，SHA-256 为 `01f130aa03f65ff6425ccb3baadb91b7944d6c6ad1ff3f804a1206a17aca4a80`。该校验值对应独立实现。


## 分段拓扑排序的辅助编码

`ordered_shard.py` 对原 CNF 增加 10,200 条排序约束与 36 个辅助变量。把第 0 至 9 门和第 11 至 20 门分别依照三元组（较大输入编号、较小输入编号、操作类型）排序。第 10 门固定在原位置。完备性的理由是，在每个分段的合法拓扑编号中取三元组序列字典序最小的排列。若相邻两门逆序，后门的较大输入编号至多为前门的较大输入编号，因而后门没有读取前门，可以交换。交换后重编号后续读取和输出，字典序严格下降，矛盾。段内重排不改变首次 junk AND 的位置或后续 junk 的存在性。

```sh
python3 ordered_shard.py run/first10.cnf /tmp/peq1343-ordered.cnf
python3 validate_search.py /path/to/cadical --ordered
```

验证器把一个 24 门、首次 junk 正好在第 10 门的已知电路重新排序，固定其全部门并求解新增约束，用原有 decoder 再次核对全部 2,048 个输入。辅助搜索与原始 LRAT 进程分别运行。

额外的 `--normalize-aliases` 开关也适用于生成器和验证器。对原电路前向传播常量、越界读取和同一操作数，遇到等价于较早 wire 的门时，把所有后续读取直接接到较早代表。需要保留的位置用不再被读取的门填充。有 junk 标记时填 `AND(x0,x0)`，没有时填 `OR(x0,x0)`；前者在独立单点上为真，后者不是 AND。真正的非恒定输出不会成为填充门。于是每个位置可以只允许相异的非恒定操作数或这种填充，并禁止读取填充门。随后按上述分段拓扑排序即可同时满足两类约束。含归一化的固定 24 门见证亦已逐输入验证。
