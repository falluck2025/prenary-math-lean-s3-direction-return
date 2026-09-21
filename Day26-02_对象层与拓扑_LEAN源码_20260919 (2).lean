import Mathlib

/-! ================================================================
   偏元数学 · Day26-02 · S3 方向回归 · 对象层 ℂ★ 与拓扑
   ------------------------------------------------------------------
   核心：对象层 = ℂ★ := { z : ℂ // z ≠ 0 }（复平面挖去原点）；
         缺陷点是可指认的；ℂ★ 带子空间拓扑。
   本稿范围：对象层的定义与基本性质（L0）＋ 拓扑实例（L1）。
   不做：不涉及同伦等价、基本群、覆叠 —— 归 Day26-03/04。
   注：本段是 Day26-X 自足结构的 §1 基础层。
   日期：2026-09-19
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS006

-- L0：对象层 = 带一个缺陷点的复平面
/-- ℂ★：复平面挖去原点（偏元数学的对象层）。
    用 `abbrev`（而非 `def`）：使类型自动展开，coercion `(z : ℂ)` 与子空间拓扑实例均可被识别。 -/
abbrev PuncturedComplex : Type := { z : ℂ // z ≠ 0 }

-- 缺陷点可指认
/-- 原点不属于对象层 —— 缺陷点是可指认的。 -/
theorem defect_not_in_object : ¬ (∃ z : PuncturedComplex, (z : ℂ) = 0) := by
  rintro ⟨z, hz⟩
  exact z.2 hz

/-- 对象层非空。 -/
theorem punctured_nonempty : Nonempty PuncturedComplex := ⟨⟨1, by norm_num⟩⟩

/-- 对象层嵌入经典复平面，是单射。 -/
theorem punctured_injective :
    Function.Injective (fun z : PuncturedComplex => (z : ℂ)) :=
  Subtype.val_injective

/-- 对象层任一点的经典值非零。 -/
theorem punctured_val_ne_zero (z : PuncturedComplex) : (z : ℂ) ≠ 0 := z.2

/-- 对象层不是经典复平面：存在经典点（原点）不属于对象层。 -/
theorem object_layer_not_all_complex :
    ∃ w : ℂ, ∀ z : PuncturedComplex, (z : ℂ) ≠ w :=
  ⟨0, fun z hz => z.2 hz⟩

-- L1：对象层带子空间拓扑
-- 注：`ℂ` 的拓扑实例在 Mathlib 中依赖 C*-代数一支（`instCommCStarAlgebraComplex`，标 noncomputable），
--     故此处须加 `noncomputable`。
/-- ℂ★ 上的拓扑（子空间拓扑）。 -/
noncomputable example : TopologicalSpace PuncturedComplex := inferInstance

end PrenaryS006
