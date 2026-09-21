import Mathlib

/-! ================================================================
   偏元数学 · Day26-05 · S3 方向回归 · 零元锚点（ε ≜ 0）
   ------------------------------------------------------------------
   核心：偏元等号的零元是 ε，不是 0 —— 自减的结果即偏元零元；
         ε ≠ 0 时它与经典零元不同；ε = 0 时退回经典。
   本稿范围：偏元零元的定义、锚点性质、与经典零元的区分、退化、唯一性。
   不做：不涉及覆叠、单值化 —— 见 Day26-03。
   注：本段是 Day26-X 自足结构的 §1 后半（对象层的零元）。
   日期：2026-09-19
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS006

-- 偏元减法：差再附加残差
/-- 偏元减法：差再附加残差。 -/
def psub (ε : ℂ) (a b : ℂ) : ℂ := (a - b) + ε

-- 偏元零元
/-- 偏元零元：偏元等号之下的零元。 -/
def prenaryZero (ε : ℂ) : ℂ := ε

-- 定理 12（锚点的实质）：自减的结果就是偏元零元
/-- 定理 12：`a ⊖ a = 偏元零元` —— 这正是「ε ≜ 0」的含义。 -/
theorem psub_self_is_prenary_zero (ε a : ℂ) :
    psub ε a a = prenaryZero ε := by
  simp only [psub, prenaryZero, sub_self, zero_add]

-- 定理 13：偏元零元不是经典零元
/-- 定理 13：残差非零 ⟹ 偏元零元 ≠ 经典零元。 -/
theorem prenary_zero_ne_classical {ε : ℂ} (hε : ε ≠ 0) :
    prenaryZero ε ≠ (0 : ℂ) := by
  simpa only [prenaryZero] using hε

-- 定理 14：经典零元不是偏元零元
/-- 定理 14：残差非零 ⟹ 经典零元 ≠ 偏元零元。 -/
theorem classical_zero_ne_prenary_zero {ε : ℂ} (hε : ε ≠ 0) :
    (0 : ℂ) ≠ prenaryZero ε := by
  simp only [prenaryZero]
  exact fun h => hε h.symm

-- 定理 15（退化）：ε = 0 时，偏元零元退回经典零元
/-- 定理 15：残差为零 ⟹ 偏元零元即经典零元（回到经典）。 -/
theorem prenary_zero_degenerates :
    prenaryZero (0 : ℂ) = 0 := rfl

-- 定理 16（唯一性）：使 a ⊖ a = z 成立的 z 只能是偏元零元
/-- 定理 16：偏元零元是唯一使 `a ⊖ a = z` 成立的 `z`。 -/
theorem prenary_zero_unique (ε a z : ℂ) (h : psub ε a a = z) :
    z = prenaryZero ε := by
  rw [← h, psub_self_is_prenary_zero]

end PrenaryS006
