import Mathlib

/-! ================================================================
   偏元数学 · Day26-01 · S3 方向回归 · 代数与序
   ------------------------------------------------------------------
   核心：act(op₀,ε)(a) = op₀(a) + ε，ε ≠ 0 ⟹ 动作不闭合；a ⊖ a = ε ≠ 0；
         二态 = 阶 2；ε 落在整数格点上 ⟹ 序不变、位不精确；ε = 0 ⟹ 退化为经典。
   本稿范围：对象层 ℂ 上的动作残差代数、二态的阶、序/位分离的实数部分、退化。
   不做：不涉及覆叠空间、单值化（monodromy）与基本群 —— 归 Day26-03/04。
   注：上承 NEW(S)-005 分解式；本仓与 W-002 / SW-001 同属 S3 一体。
       下一段：Day26-02（ℂ★ 基本性质）、Day26-03（monodromy 探路）。
   日期：2026-09-19
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS006

-- ① 动作：在经典映射 op₀ 上附加固定残差 ε（地基文献公理 1 的最小模型）
/-- 动作映射：经典结果 `op0 a` 加残差 `ε`。 -/
def act (op0 : ℂ → ℂ) (ε : ℂ) (a : ℂ) : ℂ := op0 a + ε

/-- 定理 1（动作不闭合）：残差非零 ⟹ 动作后的值不等于动作前的值。 -/
theorem act_not_closed (op0 : ℂ → ℂ) {ε : ℂ} (hε : ε ≠ 0) (a : ℂ) :
    act op0 ε a ≠ op0 a := by
  intro h
  simp only [act] at h
  have h2 : (op0 a + ε) - op0 a = 0 := sub_eq_zero.mpr h
  have h1 : ε = 0 := by simpa using h2
  exact hε h1

-- ② 偏元减法：a ⊖ b := (a − b) + ε
/-- 偏元减法：差再附加残差。 -/
def psub (ε : ℂ) (a b : ℂ) : ℂ := (a - b) + ε

/-- 定理 2（自减留残）：同一对象自减，结果为 ε ≠ 0，不是 0。 -/
theorem self_sub_residual {ε : ℂ} (hε : ε ≠ 0) (a : ℂ) :
    psub ε a a ≠ 0 := by
  simp only [psub, sub_self, zero_add]
  exact hε

-- ③ 二态：非零且二阶 ⟹ ℤ/2；在 ZMod 2 中显式给出
/-- 定理 3a（二态 = 阶 2）：ℤ/2 中 1 + 1 = 0。 -/
theorem two_state_add_self : (1 : ZMod 2) + 1 = 0 := by decide

/-- 定理 3b（二态非平凡）：ℤ/2 中 1 ≠ 0。 -/
theorem two_state_nontrivial : (1 : ZMod 2) ≠ 0 := by decide

-- ④ 序：序位来自整数格点，残差落在格点上
/-- 定理 4（序不变）：格距为 1、残差 ≤ 1/2 ⟹ 残差不跨格，先后关系保持。
    条件 `δ₀ ≤ 1/2` 是显式的：残差足够小（而非仅 `ε < δ₀`）。 -/
theorem order_preserved
    {δ₀ εa εb : ℝ} (hδ : δ₀ ≤ 1 / 2)
    (_ha0 : 0 ≤ εa) (hab : εa ≤ δ₀)
    (hb0 : 0 ≤ εb) (_hbb : εb ≤ δ₀)
    {n m : ℤ} (hnm : n < m) :
    (n : ℝ) + εa < (m : ℝ) + εb := by
  have hnm_int : n + 1 ≤ m := Int.add_one_le_iff.mpr hnm
  have hnm_real : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm_int
  have h1 : (n : ℝ) + εa ≤ (n : ℝ) + δ₀ := by linarith
  have h2 : (n : ℝ) + δ₀ < (m : ℝ) + εb := by linarith
  linarith

/-- 定理 5（位不精确）：残差非零 ⟹ 带残差的序位偏离整数格点。 -/
theorem position_inexact {ε : ℝ} (hε : ε ≠ 0) (n : ℤ) :
    (n : ℝ) + ε ≠ (n : ℝ) := by
  intro h
  exact hε (by linarith)

-- ⑤ 退化：ε = 0 时回到经典
/-- 定理 6（退化）：残差为零 ⟹ 动作闭合，回到经典。 -/
theorem degenerate_to_classical (op0 : ℂ → ℂ) (a : ℂ) :
    act op0 0 a = op0 a := by
  simp only [act, add_zero]

end PrenaryS006
