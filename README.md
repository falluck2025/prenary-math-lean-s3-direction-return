[![DOI](https://zenodo.org/badge/DOI/DOI-TBD.svg)](https://doi.org/DOI-TBD)

# 偏元数学 · Day26 · S3 方向回归（对象层 ℂ★、二态与偏元序）· Lean 4 形式化验证

## Prenary Mathematics · Day26 · S3 Direction Return (Object Layer ℂ★, Two-State, and Prenary Order) · Lean 4 Formal Verification

本文工作尚未得到独立实验验证，全部结论均为形式化验证层面的初步结果。

> **DOI**：`DOI-TBD`（**发布后回填本行与顶部徽章**）。本仓库上承 Day25 `prenary-math-lean-s3-sw-epsilon-eta`（ε↔η 映射）与 Day24 `prenary-math-lean-s3-complexification`（[10.5281/zenodo.22815027](https://doi.org/10.5281/zenodo.22815027)）。

## 摘要

本仓库把「方向」在偏元数学中的回归立为**可验证命题**：**对象层由 ℂ 修正为带一个缺陷点的 `ℂ★`，方向由「静态标签」实现为「绕行阶数」，二态实现为纤维 ≅ ℤ/2 的二重覆叠。**

**一、代数与序（Day26-01）**：动作不闭合（`ε ≠ 0` ⟹ 动作后的值不等于动作前的值）；自减留残（`a ⊖ a = ε ≠ 0`）；二态为阶 2（`ZMod 2`）；**序不变、位不精确**（格距 1、残差 ≤ 1/2 ⟹ 先后关系保持）；`ε = 0` 退化为经典。

**二、对象层与拓扑（Day26-02）**：对象层 `ℂ★ := { z : ℂ // z ≠ 0 }`，缺陷点可指认，带子空间拓扑。

**三、单值化与二态（Day26-03）**：以覆叠的**单值化（monodromy）**实现二态——沿回路给出纤维上的置换；若该置换是两个不同点的交换，则**覆叠非平凡**且**覆叠度为 2**。

**四、二态的对合性（Day26-04）**：两点交换是**对合**（交换两次回到原处），与代数侧的 `ZMod 2` 同为 `ℤ/2`。

**五、零元锚点（Day26-05）**：**偏元等号的零元是 ε，不是 0**——自减的结果即偏元零元；它与经典零元不同；`ε = 0` 时退回经典；且是唯一使 `a ⊖ a = z` 成立的 `z`。

**六、递推与偏元序（Day26-06）**：递推 `z_{n+1} = z_n + ε_n`；**走一步就留差**（位不精确）；**而序号本身不带残差**（对象层静态标记）——**序与位分层**。

**不在范围内**：不构造具体的覆叠映射；不使用基本群 `π₁` 与覆叠分类；不主张「时序即时间」；不涉及因果问题。

> **关于对象层的说明（须读）**：对象层取 `ℂ★` 是**本文的选定（定义层），不是由前文推出的定理**。其动机：若取 `ℂ`，则 `ℂ` 单连通，其上覆叠必平凡，绕行残差必然为零——与公理（`ε ≠ 0`）冲突。**「`ℂ` 单连通 ⟹ 覆叠必平凡」为标准结论（代数拓扑），本仓库引用不重证、亦不形式化。**

## Abstract

This repository makes the **return of "direction"** in Prenary Mathematics a set of **verifiable propositions**: **the object layer is revised from ℂ to `ℂ★` (one defect point), direction is realized as a winding order rather than a static label, and the two-state is realized as a double covering with fiber ≅ ℤ/2.**

**I. Algebra and Order (Day26-01)**: non-closure of actions; self-subtraction leaves a residual (`a ⊖ a = ε ≠ 0`); the two-state has order 2 (`ZMod 2`); **order is preserved while positions are inexact**; degeneration to classical at `ε = 0`.

**II. Object Layer and Topology (Day26-02)**: the object layer `ℂ★ := { z : ℂ // z ≠ 0 }`, its defect point is identifiable, with the subspace topology.

**III. Monodromy and the Two-State (Day26-03)**: the two-state is realized via the **monodromy** of a covering — a transposition on the fiber implies **non-triviality** and **covering degree 2**.

**IV. Involution (Day26-04)**: a transposition is an **involution**, the same `ℤ/2` as the algebraic-side `ZMod 2`.

**V. Zero Anchor (Day26-05)**: **the zero of prenary equality is ε, not 0** — with uniqueness and degeneration.

**VI. Recursion and Prenary Order (Day26-06)**: `z_{n+1} = z_n + ε_n`; every step leaves a residual while the index itself carries none.

**Out of scope**: no explicit covering map; no fundamental group `π₁` or covering classification; "order is not time"; causality.

> **Note on the object layer**: taking `ℂ★` is a **choice at the definition level, not a theorem**. Rationale: over `ℂ`, all coverings are trivial, so the winding residual would vanish — contradicting `ε ≠ 0`. The standard fact "`ℂ` simply connected ⟹ every covering trivial" is **cited, not re-proved or formalized**.

## 关键词

偏元数学；方向回归；二态；对象层 ℂ★；单值化；覆叠度；偏元序；残差 ε；零元锚点；退化；Lean 4；形式化验证；陈偏贞；老陈与AI的深夜实验室；PGI蛟龙；华夏思哲偏元注

## 概述

偏元数学是对经典数学的扩展尝试，ε = 0 时退化为经典。

相对于 Day25 的横向推进（ε↔η 只立共享结构），本仓库做**纵向**的一件事：**把「方向」放回对象层**。

此前「方向偏好二态」因**无可操作判据**而被移出对象层（其实现是一个"写在结构体里、但没有任何运算用到它"的静态标签）。本仓库换一个实现：**不再做成标签，而做成可数的绕行阶数**——"绕一圈不闭合、绕两圈闭合"是一个**可执行、可观测**的判定动作。

由此，对象层由 ℂ 修正为 `ℂ★`；「二态」在代数侧表现为 `ZMod 2`、在几何侧表现为纤维上的两点交换；两者是同一个 `ℤ/2`。**本仓库不宣称拓扑路线（基本群、覆叠分类）已被形式化**——该部分明确不在范围内。

## 核心定义

```lean
-- Day26-02：对象层（带一个缺陷点的复平面）
abbrev PuncturedComplex : Type := { z : ℂ // z ≠ 0 }

-- Day26-01：动作（在经典映射 op₀ 上附加固定残差 ε）
def act (op0 : ℂ → ℂ) (ε : ℂ) (a : ℂ) : ℂ := op0 a + ε

-- Day26-01：偏元减法
def psub (ε : ℂ) (a b : ℂ) : ℂ := (a - b) + ε

-- Day26-03：二态（单值化版）
def TwoState {F : Type*} [DecidableEq F] (σ : Equiv.Perm F) : Prop :=
  ∃ a b : F, a ≠ b ∧ σ = Equiv.swap a b

-- Day26-05：偏元零元
def prenaryZero (ε : ℂ) : ℂ := ε

-- Day26-06：递推
def Recur (ε z : ℤ → ℂ) : Prop := ∀ n : ℤ, z (n + 1) = z n + ε n
```

## 定理清单

> **关于验证内容的如实说明**：下列各条均已在 Lean 4（Mathlib）中通过内核检查（`All Messages (0)`），并经 Comparator 二次验证通过。**本仓库不主张这些定理之外的东西**；凡未列出的（具体覆叠的构造、基本群、覆叠分类、以及"对象层必须为 `ℂ★`"的拓扑依据）**均不在本仓库范围**。

### Day26-01 · 代数与序（7 条）

| 定理 | 命题 |
|:--|:--|
| `act_not_closed` | 残差非零 ⟹ 动作后的值 ≠ 动作前的值 |
| `self_sub_residual` | `a ⊖ a = ε ≠ 0`（不是 0） |
| `two_state_add_self` | `ℤ/2` 中 `1 + 1 = 0` |
| `two_state_nontrivial` | `ℤ/2` 中 `1 ≠ 0` |
| `order_preserved` | 格距 1、残差 ≤ 1/2 ⟹ 残差不跨格，先后关系保持 |
| `position_inexact` | 残差非零 ⟹ 序位偏离整数格点 |
| `degenerate_to_classical` | `ε = 0` ⟹ 动作闭合，回到经典 |

### Day26-02 · 对象层与拓扑（5 条 + 1 示例）

| 定理 | 命题 |
|:--|:--|
| `defect_not_in_object` | 原点不属于对象层——缺陷点可指认 |
| `punctured_nonempty` | 对象层非空 |
| `punctured_injective` | 对象层嵌入经典复平面，是单射 |
| `punctured_val_ne_zero` | 对象层任一点的经典值非零 |
| `object_layer_not_all_complex` | 存在经典点（原点）不属于对象层 |
| （示例） | `TopologicalSpace PuncturedComplex` 可用 |

### Day26-03 · 单值化与二态（3 条）

| 定理 | 命题 |
|:--|:--|
| `two_state_not_identity` | 二态 ⟹ 单值化不是恒等 ⟹ 覆叠非平凡 |
| `two_state_fiber_two` | 二态 ⟹ 纤维上存在两个不同点 |
| `two_state_orbit_size_two` | 轨道恰为两点，其余点不动 ⟹ 覆叠度为 2 |

### Day26-04 · 二态的对合性（2 条）

| 定理 | 命题 |
|:--|:--|
| `swap_swap_apply` | 两点交换是对合：交换两次回到原处 |
| `two_state_sides_agree` | 代数侧 `ZMod 2` 的非零元亦为「加两次回到零」 |

### Day26-05 · 零元锚点（5 条）

| 定理 | 命题 |
|:--|:--|
| `psub_self_is_prenary_zero` | 自减的结果即偏元零元 |
| `prenary_zero_ne_classical` | 偏元零元 ≠ 经典零元 |
| `classical_zero_ne_prenary_zero` | 经典零元 ≠ 偏元零元 |
| `prenary_zero_degenerates` | `ε = 0` ⟹ 偏元零元退回经典零元 |
| `prenary_zero_unique` | 使 `a ⊖ a = z` 成立的 `z` 唯一 |

### Day26-06 · 递推与偏元序（3 条）

| 定理 | 命题 |
|:--|:--|
| `recur_step_leaves_residual` | 走一步就留差（位不精确） |
| `recur_two_step` | 累积：两步的位变化为两步残差之和 |
| `index_has_no_residual` | 序号本身不带残差（对象层静态标记） |

## 验证记录

| 文件 | 内核 | Comparator | Challenge Hash（锁挑战） | 代码 SHA256（锁解答） |
|:--|:--|:--|:--|:--|
| Day26-01 | No goals + All Messages (0) | ✅ 通过 | `726578727856655f30e9a0803c37e1481a1c18bc5db52151b201b5110b1fb892` | 同左 |
| Day26-02 | No goals + All Messages (0) | ✅ 通过 | `35465a91ad897b2a5db8712d78750cd22afaf4705456075191f43eac5328b464` | 同左 |
| Day26-03 | No goals + All Messages (0) | ✅ 通过 | `2633e189e4cbe58ff04c89dd757f53607a3bc707611988b43708b806b67bcde2` | 同左 |
| Day26-04 | No goals + All Messages (0) | ✅ 通过 | `ca41070da3cdb49e0184839962a51c153142a8f2da27112246c512bb27853ae8` | 同左 |
| Day26-05 | No goals + All Messages (0) | ✅ 通过 | `7818f3c26e207dd40d1fbb2cf6bbb9688c47c389629973707bf79c6ecdcadd8a` | 同左 |
| Day26-06 | No goals + All Messages (0) | ✅ 通过 | `85b1eceaf8c3835765214c01e02a57b16a9f887d472b345c3d2727c59a2c3dfd` | 同左 |

- **平台**：L∃∀N Comparator Live (Experimental) · Latest Mathlib with Lean v4.35.0
- **验证时间**：2026-09-19 21:20–22:31
- **双哈希说明**：本组采用**自编 challenge** 模式（Challenge 文本 = 我方提交代码），故 **Challenge Hash 与代码 SHA256 取同一值**；已用本地 `sha256sum` 与 Comparator 显示值**逐字核对一致**。

## 文件说明

```
.
├── Day26-01_方向回归_代数与序_LEAN源码_20260919.lean
├── Day26-02_对象层与拓扑_LEAN源码_20260919.lean
├── Day26-03_单值化与二态_LEAN源码_20260919.lean
├── Day26-04_二态的对合性_LEAN源码_20260919.lean
├── Day26-05_零元锚点_LEAN源码_20260919.lean
├── Day26-06_递推与偏元序_LEAN源码_20260919.lean
├── README.md
├── LICENSE
└── evidence/                      # 验证截图（每件：内核 / Comparator）
```

## 复现方式

1. 打开 `https://comparator.live.lean-lang.org/`（Latest Mathlib with Lean v4.35.0）。
2. 将对应 `.lean` 文件**整份复制**（Ctrl+A，含 `import Mathlib` 与 `/-!` 抬头），分别贴入 **Challenge** 与 **Candidate Solution** 面板。
3. 运行内核，确认 `All Messages = 0`；再点二次验证，应显示 `Trusting challenge with hash <SHA256>` 且结果为通过。
4. 用 `sha256sum <file>.lean` 计算本地哈希，应与上表 **逐字一致**。

## 可证伪条件

本仓库的结论**可被如下任一事实推翻**：

1. 若能证明 `ℂ★` 与 `ℂ` 在本结构下等价（缺陷点可"补回"而不改结论）⟹ 对象层修正失效；
2. 若"走一圈不闭合、走两圈闭合"在底上不可判定 ⟹ 二态的单值化实现失效；
3. 若存在 `n < m` 与满足 `0 ≤ ε_k ≤ δ₀ ≤ 1/2` 的残差使 `n + ε_n ≥ m + ε_m` ⟹ 序不变失效（**已被 Lean 验证为不可能**）；
4. 若"零元不是 0"在经典结构中有实质对应物（例如某经典数系中零元本身是动作的产物）⟹ 零元锚点的"新"失效。

## 引用

陈松. 偏元数学 · Day26 · S3 方向回归 · Lean 4 形式化验证. Zenodo, 2026. DOI: 待回填.

## 许可

CC BY-NC-ND 4.0

---

老陈与AI的深夜实验室 发布 请笑纳
