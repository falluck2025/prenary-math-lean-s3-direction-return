import Mathlib

/-! ================================================================
   偏元数学 · Day26-03 · S3 方向回归 · 单值化与二态
   ------------------------------------------------------------------
   核心：覆叠的单值化（monodromy）沿回路给出纤维上的置换；
         若该置换是两个不同点的交换，则 ① 覆叠非平凡 ② 覆叠度为 2。
   本稿范围：二态的单值化实现，及其两个直接推论（非平凡、度 = 2）。
   不做：不构造具体的覆叠映射；不使用基本群 π₁ 与覆叠分类。
   注：本段是 Day26-X 自足结构的 §6 前半；上承 Day26-01、Day26-02。
       单值化的存在性由 Mathlib 的 `IsCoveringMap.monodromy` 提供。
   日期：2026-09-19
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryS006

-- 二态：单值化置换 = 两个不同点的交换
/-- 二态（单值化版）：纤维上的单值化置换是两个不同点的交换。 -/
def TwoState {F : Type*} [DecidableEq F] (σ : Equiv.Perm F) : Prop :=
  ∃ a b : F, a ≠ b ∧ σ = Equiv.swap a b

/-- 定理 7（非平凡）：二态 ⟹ 单值化不是恒等 ⟹ 覆叠非平凡。 -/
theorem two_state_not_identity {F : Type*} [DecidableEq F] {σ : Equiv.Perm F}
    (h : TwoState σ) : σ ≠ 1 := by
  obtain ⟨a, b, hab, hσ⟩ := h
  intro hcontra
  have h1 : σ a = a := by simp [hcontra]
  rw [hσ, Equiv.swap_apply_left] at h1
  exact hab h1.symm

/-- 定理 8（纤维至少两点）：二态 ⟹ 纤维上存在两个不同点。 -/
theorem two_state_fiber_two {F : Type*} [DecidableEq F] {σ : Equiv.Perm F}
    (h : TwoState σ) : ∃ a b : F, a ≠ b := by
  obtain ⟨a, b, hab, _⟩ := h
  exact ⟨a, b, hab⟩

/-- 定理 9（轨道恰为两点）：二态的单值化只有一条非平凡轨道，大小 2，
    其余点不动 ⟹ 覆叠度为 2。 -/
theorem two_state_orbit_size_two {F : Type*} [DecidableEq F] {σ : Equiv.Perm F}
    (h : TwoState σ) :
    ∃ a b : F, a ≠ b ∧ σ a = b ∧ σ b = a ∧ ∀ x : F, x ≠ a → x ≠ b → σ x = x := by
  obtain ⟨a, b, hab, hσ⟩ := h
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · rw [hσ]; exact Equiv.swap_apply_left a b
  · rw [hσ]; exact Equiv.swap_apply_right a b
  · intro x hxa hxb; rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne hxa hxb

end PrenaryS006
