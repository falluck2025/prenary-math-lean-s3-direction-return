import Mathlib

/-! ================================================================
   偏元数学 · Day26-04 · S3 方向回归 · 二态的对合性（两侧统一）
   ------------------------------------------------------------------
   核心：两点交换（几何侧的二态）是对合 —— 交换两次回到原处；
         故它与代数侧的 `ZMod 2`（Day26-01 定理 3）是同一个 ℤ/2。
   本稿范围：`Equiv.swap` 的对合性（作用形式）；两侧二态的接口。
   不做：不涉及覆叠、单值化 —— 见 Day26-03。
   注：本段是 Day26-X 自足结构的 §6 后半；上承 Day26-01（代数侧）、Day26-03（几何侧）。
       定理 10 用"作用形式"表述（等价于 `Equiv.swap a b * Equiv.swap a b = 1`）。
   日期：2026-09-19
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS006

-- 定理 10（对合）：两点交换，交换两次回到原处
/-- 定理 10：`Equiv.swap a b` 是对合 —— 等价于 `swap a b * swap a b = 1`。 -/
theorem swap_swap_apply {F : Type*} [DecidableEq F] (a b x : F) :
    Equiv.swap a b (Equiv.swap a b x) = x := by
  by_cases hx : x = a
  · rw [hx, Equiv.swap_apply_left, Equiv.swap_apply_right]
  · by_cases hx' : x = b
    · rw [hx', Equiv.swap_apply_right, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx', Equiv.swap_apply_of_ne_of_ne hx hx']

-- 定理 11（两侧同一个 ℤ/2）：代数侧的阶 2
/-- 定理 11：代数侧 `ZMod 2` 的非零元也是"加两次回到零"。 -/
theorem two_state_sides_agree :
    (2 : ZMod 2) = 0 ∧ (1 : ZMod 2) + 1 = 0 ∧ (1 : ZMod 2) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end PrenaryS006
