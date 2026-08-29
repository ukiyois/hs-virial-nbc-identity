# Research Journey / 研究历程

This document records the research motivation, the successful route, and the
routes that failed. It is a human research narrative, not part of the Lean
statement surface or the Comparator configuration.

本文记录研究动机、已经走通的路线以及没有走通的方向。它是面向人的研究叙事，
不属于 Lean 的 statement surface，也不属于 Comparator 的比较配置。

## 研究动机

实验和分子动力学模拟表明，三维硬球流体在体积分数约为 `0.49--0.55`
的范围内发生液态到晶态的相变。另一方面，流体状态方程可以用关于密度（或相应
归一化变量）的维里级数来描述。一个自然而又非常困难的问题是：这个维里级数在
复平面上的收敛半径 `R`，是否恰好与硬球体系的液-固转变尺度相联系，例如是否
接近 `0.49`？

这里的 `0.49` 是研究问题中的物理猜想尺度，不是本仓库 Lean 定理的结论。

### Research motivation

Experiments and molecular-dynamics simulations indicate that a three-dimensional
hard-sphere fluid undergoes a liquid-to-crystal transition in the approximate
volume-fraction range `0.49--0.55`. The fluid equation of state can be described
by a virial series in the density, or in a corresponding normalized variable.
A natural but extremely difficult question is whether the radius of convergence
`R` of that virial series in the complex plane is tied to the hard-sphere
liquid-solid transition scale, perhaps being close to `0.49`.

The value `0.49` is a physical scale motivating the conjectural question here;
it is not a theorem proved by this repository.

## 为什么困难

要计算 `R`，通常需要控制高阶维里系数 `B_k`。而计算 `B_k` 又要求处理大量
`k` 点双连通图及其高维积分。图的数量和积分维度同时增长，使得直接数值计算、
逐项估计或单纯依赖绝对值不等式都很快远离问题的终点。

从 1963 年 Penrose 的 fugacity 收敛结果和 1967 年的 tree-graph identity，到
2015 年提交、2017 年发表的 PY 最小生成树方向，已有工作
不断尝试通过树结构获得可用的界。然而，如果目标是接近上述猜想尺度，仅仅取
绝对值并建立 unsigned majorant，显然会损失太多结构。

### Why the problem is difficult

To compute `R`, one generally needs control of the high-order virial
coefficients `B_k`. Computing `B_k` in turn requires handling enormous numbers
of two-connected graphs on `k` vertices together with high-dimensional
integrals. Both the number of graphs and the integration dimension grow, so
direct numerical computation, term-by-term estimates, and absolute-value
inequalities quickly move far away from the conjectural target.

From Penrose's 1963 fugacity convergence result and 1967 tree-graph identity to
the Procacci--Yuhjtman preprint submitted in 2015 and published in 2017 with a
minimum-spanning-tree partition, a long line of work has tried to obtain useful
bounds from tree structures. But if the goal is to approach the conjectural
scale above, taking absolute values and building an unsigned majorant evidently
discards too much of the underlying structure.

## 走通的核心路线

因此，我们和 agent 达成了一个方向性的判断：暂时放下数值方法，也放下单纯的
绝对值不等式，改为研究代数符号消除是否能把问题推进到更接近猜想的位置。

目前得到的最强结果，就是本仓库中的精确等式。其核心可以概括为三层转换：

```text
connected Mayer graph sum
    <-> overlap graph 的 NBC/Tutte 拓扑量
    <-> 连续 hard-sphere 构型空间中的非负 NBC 体积积分
```

第一层把 connected Mayer graph sum 识别为 overlap graph 上的 signed
connected-subgraph sum。第二层通过有限 broken-circuit cancellation，把这个
带符号的拓扑量化为 NBC spanning-tree count。第三层把每个 NBC tree count
按连续构型空间中的 tree-owned regions 重新组合，得到非负体积积分。

在当前 Lean 形式化中，主结果写成

```text
(k.factorial : Real) * |hardSphereBk|
  = sum over spanning trees T of hardSphereNBCVolumeFlat T
```

这里的正式参数是 `k >= 2`，也就是粒子数 `k > 1`；物理上空间维数应为
`d >= 1`，而不是 `d > 1`，因为一维 hard-rod 情形是重要的边界案例。Lean
代码使用 `d : Nat`，因此也形式上覆盖退化的 `d = 0` 情形。

这个结果的关键不在于给出一个更强的 unsigned bound，而在于把原本大规模的
带符号 Mayer 图求和，转化为逐点非负的 NBC 计数积分。仓库同时显式证明了
anchored product-Lebesgue 构型空间与 flat Euclidean 坐标空间之间的
measure-preserving 传输。

这里需要严格区分贡献层次。有限 broken-circuit 消去、connected Mayer
展开以及 product-to-flat 坐标变换本身分别属于经典或常规工具；坐标变换
也不作为创新点。不能因此把整个结果压缩成“经典消去的直接特化和重新组合”。
本项目真正提交的桥接是：overlap graph 随连续构型变化，NBC 消去逐点成立，
然后把逐点计数组织成可测的 tree-owned regions，最终得到精确的非负体积等式，
并由 Lean kernel 检查完整的离散到连续再到测度的链条。

### The successful route

We therefore reached a strategic agreement with the agent: set numerical
methods aside for the moment, and do not rely on absolute-value inequalities
alone. Instead, investigate whether algebraic cancellation of signs can move
the problem closer to the conjectural target.

The strongest result obtained so far is the exact identity formalized in this
repository. Its structure is a three-stage conversion:

```text
connected Mayer graph sum
    <-> NBC/Tutte topological quantity of the overlap graph
    <-> nonnegative NBC volume integral on continuous hard-sphere configuration space
```

The first stage identifies the connected Mayer graph sum with a signed
connected-subgraph sum of the overlap graph. The second uses finite
broken-circuit cancellation to turn that signed quantity into an NBC spanning-
tree count. The third regroups the count over tree-owned regions in continuous
configuration space, producing a nonnegative volume integral.

In the current Lean formalization, the main result is

```text
(k.factorial : Real) * |hardSphereBk|
  = sum over spanning trees T of hardSphereNBCVolumeFlat T
```

The formal parameter condition is `k >= 2`, meaning `k > 1` particles. The
physical dimension is `d >= 1`, not `d > 1`, since the one-dimensional
hard-rod case is an important boundary case. The Lean code uses `d : Nat` and
therefore also includes the degenerate formal case `d = 0`.

The point is not merely to obtain a stronger unsigned bound. It is to convert a
large signed Mayer graph sum into a pointwise nonnegative NBC counting integral.
The repository also makes explicit the measure-preserving transport between the
anchored product-Lebesgue configuration space and flat Euclidean coordinates.

The contribution must be separated from its ingredients.  Finite
broken-circuit cancellation, the connected Mayer expansion, and the
product-to-flat coordinate map are classical or standard, and the coordinate
map is not claimed as novelty.  But the complete result is not adequately
described as only a direct specialization and recombination of those tools: the
overlap graph varies with the continuous configuration, the NBC cancellation is
used pointwise, and the resulting count is converted into measurable
tree-owned regions and an exact nonnegative volume identity.  The full bridge
from the discrete identity to the continuous integral and its measure transport
is checked by the Lean kernel.

## 额外得到的 hard-rod 结果

在研究过程中，我们还沿着另一条路线把 hard-rod 的超平面 arrangement 分成
activity cells。在每个 cell 上，activity graph 是固定的，于是可以得到连续
构型空间的 NBC 加权分解。这条结果解释了为什么在 Tonks、也就是 `d = 1` 的
Mayer cancellation 中，逐点符号可以保持固定，并把 Cayley 数解释成一个正的
体积加权总量。

不过，这个漂亮的 hard-rod 结果无法直接扩展到高维。它不在本仓库中，只作为
研究过程中得到的背景结果记录在这里。

### An additional hard-rod result

During the project we also partitioned the hard-rod hyperplane arrangement into
activity cells. On each cell the activity graph is fixed, yielding an NBC-weighted
decomposition of continuous configuration space. This explains why the Tonks,
that is, `d = 1`, Mayer cancellation preserves a fixed pointwise sign, and it
turns the Cayley count into a positive volume-weighted total.

Unfortunately, this elegant hard-rod result does not directly extend to higher
dimensions. It is not part of this repository; it is recorded here only as a
result of the broader research process.

## 走不通的路线

我们还走了很长的路，其中很多方向最终证明不足以支撑目标：

- sign alternation 经过 circle supremum 后完全消失；
- 单纯的 weight-layer 数据不能控制 volume-weighted virial rate；
- single-edge toggle 在 dense stratum-B host 上必然失败；
- 仅靠 Penrose/PY 型 unsigned majorant 不可能达到目标界。

这些失败并不只是实现层面的障碍，而是在相应抽象层次上缺少足够的控制量。
它们说明，要继续逼近收敛半径与相变尺度之间的猜想，可能需要新的组合、几何
或解析工具，而不是继续堆叠同一种绝对值估计。

### Routes that failed

We also explored many routes that ultimately did not provide enough control for
the target:

- sign alternation disappears completely after taking a circle supremum;
- weight-layer data alone cannot control the volume-weighted virial rate;
- a single-edge toggle necessarily fails on a dense stratum-B host;
- a Penrose/PY-style unsigned majorant cannot reach the target bound.

These are not merely implementation obstacles. At the corresponding level of
abstraction, the available quantities do not carry enough information. To move
closer to the conjectured relation between the convergence radius and the phase
transition scale, new combinatorial, geometric, or analytic tools may be needed
rather than more estimates of the same absolute-value type.

## 暂停

历时约一周，研究在这里暂时停止。问题依然开放：从当前结果到收敛半径以及
`0.49` 附近相变尺度之间的联系，仍然需要新的数学和新的工具。

> The work was stopped because the remaining route is a new theorem, not because a pending payload was waiting to land.

### Pausing the project

After roughly one week, the work was paused at this point. The problem remains
open: connecting the present identity to the convergence radius and to the phase
transition scale near `0.49` still requires new mathematics and new tools.

> The work was stopped because the remaining route is a new theorem, not because a pending payload was waiting to land.
