/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_11
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Helper for Proposition 2.3: on the polar cone, the pairing image of `K` has greatest element
`0`. -/
private lemma isGreatest_supportFunctionImage_zero_of_memPolarCone
    (K : Set E) (h0 : (0 : E) ∈ K) {y : Module.Dual ℝ E} (hy : y ∈ polar_cone K) :
    IsGreatest ((fun x : E ↦ (y x : EReal)) '' K) 0 := by
  constructor
  · -- The value `0` is attained at the origin, which lies in `K`.
    refine ⟨0, h0, ?_⟩
    simp
  · -- Polar-cone membership gives the universal upper bound `y x ≤ 0` on `K`.
    rintro _ ⟨x, hx, rfl⟩
    have hyx : y x ≤ 0 := (mem_polar_cone K y).mp hy x hx
    exact show ((y x : ℝ) : EReal) ≤ 0 by
      exact_mod_cast hyx

/-- Helper for Proposition 2.3: failing polar-cone membership produces a point of `K` with
strictly positive evaluation. -/
private lemma exists_pos_eval_of_not_memPolarCone
    (K : Set E) {y : Module.Dual ℝ E} (hy : y ∉ polar_cone K) :
    ∃ x ∈ K, 0 < y x := by
  -- Normalize the negated polar-cone condition to the needed existential witness.
  rw [mem_polar_cone] at hy
  push Not at hy
  simpa [not_le] using hy

/-- Helper for Proposition 2.3: a positive evaluation on a cone makes the support function equal
to `⊤`. -/
private lemma supportFunction_eq_top_of_exists_pos_eval
    (K : Set E) (hK : IsCone K) {y : Module.Dual ℝ E} (hx : ∃ x ∈ K, 0 < y x) :
    (σ_ K) y = ⊤ := by
  rcases hx with ⟨x, hxK, hxpos⟩
  rw [EReal.eq_top_iff_forall_lt]
  intro r
  -- Scale the positive witness far enough so its evaluation exceeds the chosen real bound.
  obtain ⟨n, hn⟩ := exists_nat_gt (r / y x)
  have hlarge : r < (n : ℝ) * y x := by
    have hmul : (r / y x) * y x < (n : ℝ) * y x := by
      exact mul_lt_mul_of_pos_right hn hxpos
    have hyx_ne : y x ≠ 0 := ne_of_gt hxpos
    simpa [div_eq_mul_inv, mul_assoc, hyx_ne] using hmul
  have hKreal := (isCone_iff_smul_mem (S := K)).mp hK
  have hscaled : ((n : ℝ) • x) ∈ K := by
    exact hKreal (by positivity) hxK
  have heval : y ((n : ℝ) • x) = (n : ℝ) * y x := by
    simpa only [smul_eq_mul] using y.map_smul (n : ℝ) x
  have hsupp : (((n : ℝ) * y x : ℝ) : EReal) ≤ (σ_ K) y := by
    rw [← heval]
    exact le_support_function_of_mem hscaled y
  -- Compare the chosen real bound with this scaled lower bound on the support function.
  exact lt_of_lt_of_le (by exact_mod_cast hlarge) hsupp

-- Proof sketch: if `y ∈ polar_cone K`, every pairing `y x` with `x ∈ K`
-- is at most `0`, and `0 ∈ K`, so the supremum defining `support_function K y`
-- is exactly `0`. If `y ∉ polar_cone K`, choose `x ∈ K` with `0 < y x`; since
-- `K` is closed under nonnegative scaling, every `t • x` with `t > 0` also lies
-- in `K`, so the support function dominates arbitrarily large real values and
-- therefore equals `⊤`, matching the indicator of the complement of the polar
-- cone.
/-- Proposition 2.3: if `K` is closed under nonnegative scalar multiplication and contains `0`,
then the support function `σ_K` is the indicator function of the polar cone
`Kᵒ = {y | ∀ x ∈ K, y x ≤ 0}`. -/
theorem support_function_eq_indicatorFunction_polarCone
    (K : Set E) (hK : IsCone K) (h0 : (0 : E) ∈ K) :
    σ_ K = δ_(polar_cone K) := by
  classical
  ext y
  by_cases hy : y ∈ polar_cone K
  · -- On the polar cone, the support function collapses to the attained maximum `0`.
    rw [extendedIndicator_of_mem hy]
    exact support_function_eq_of_isGreatest_image K y
      (isGreatest_supportFunctionImage_zero_of_memPolarCone K h0 hy)
  · -- Outside the polar cone, positive scaling along a witness forces the supremum to be `⊤`.
    rw [extendedIndicator_of_not_mem hy]
    exact supportFunction_eq_top_of_exists_pos_eval K hK
      (exists_pos_eval_of_not_memPolarCone K hy)

/-- On the polar cone, Proposition 2.3 specializes to the vanishing of `σ_K`. -/
@[simp] theorem support_function_of_mem_polar_cone
    (K : Set E) (hK : IsCone K) (h0 : (0 : E) ∈ K) {y : Module.Dual ℝ E}
    (hy : y ∈ polar_cone K) :
    (σ_ K) y = 0 := by
  -- Rewrite through Proposition 2.3 and evaluate the indicator on the polar cone.
  rw [support_function_eq_indicatorFunction_polarCone K hK h0]
  simpa using extendedIndicator_of_mem hy

/-- Outside the polar cone, Proposition 2.3 specializes to the value `⊤` of `σ_K`. -/
@[simp] theorem support_function_of_not_mem_polar_cone
    (K : Set E) (hK : IsCone K) (h0 : (0 : E) ∈ K) {y : Module.Dual ℝ E}
    (hy : y ∉ polar_cone K) :
    (σ_ K) y = ⊤ := by
  -- Rewrite through Proposition 2.3 and evaluate the indicator off the polar cone.
  rw [support_function_eq_indicatorFunction_polarCone K hK h0]
  simpa using extendedIndicator_of_not_mem hy

namespace PointedCone

local notation "IsCone " K:arg => _root_.IsCone (K : Set E)
local notation "σ_ " K:arg => support_function (K : Set E)

/-- A pointed cone is a cone in the source-facing sense of Definition 2.11. -/
theorem isCone (K : PointedCone ℝ E) : IsCone K := by
  intro a x hx
  exact Submodule.smul_mem K a hx

/-- The polar cone of a bundled pointed cone, viewed as a set in the dual space. -/
abbrev polarCone (K : PointedCone ℝ E) : Set (Module.Dual ℝ E) :=
  polar_cone (K : Set E)

@[simp] theorem mem_polarCone (K : PointedCone ℝ E) (y : Module.Dual ℝ E) :
    y ∈ K.polarCone ↔ y ∈ polar_cone (K : Set E) :=
  Iff.rfl

/-- Proposition 2.3 for the canonical bundled owner `PointedCone ℝ E`. -/
theorem support_function_eq_indicatorFunction_polarCone (K : PointedCone ℝ E) :
    σ_ K = δ_ K.polarCone :=
  _root_.support_function_eq_indicatorFunction_polarCone (K : Set E) K.isCone K.zero_mem

/-- On the polar cone of a pointed cone, Proposition 2.3 specializes to the vanishing of `σ_K`. -/
@[simp] theorem support_function_of_mem_polar_cone
    (K : PointedCone ℝ E) {y : Module.Dual ℝ E} (hy : y ∈ K.polarCone) :
    (σ_ K) y = 0 :=
  _root_.support_function_of_mem_polar_cone (K : Set E) K.isCone K.zero_mem hy

/-- Outside the polar cone of a pointed cone, Proposition 2.3 specializes to the value `⊤`. -/
@[simp] theorem support_function_of_not_mem_polar_cone
    (K : PointedCone ℝ E) {y : Module.Dual ℝ E} (hy : y ∉ K.polarCone) :
    (σ_ K) y = ⊤ :=
  _root_.support_function_of_not_mem_polar_cone (K : Set E) K.isCone K.zero_mem hy

end PointedCone

end
