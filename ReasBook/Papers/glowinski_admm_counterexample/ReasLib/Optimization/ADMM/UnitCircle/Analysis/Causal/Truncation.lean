/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic.Positivity

@[expose] public section

open Filter
open scoped BigOperators ENNReal

namespace ADMM.UnitCircle.Causal

variable {E : Type*} [NormedAddCommGroup E]

/-- Every finite prefix of an arbitrary sequence is canonically an `ℓ₂` vector. -/
noncomputable def truncate (T : ℕ) (v : ℕ → E) : lp (fun _ : ℕ ↦ E) 2 :=
  ⟨fun k ↦ if k < T then v k else 0, by
    apply (memℓp_zero ?_).of_exponent_ge zero_le
    apply (Set.finite_Iio T).subset
    intro k hk
    by_contra h
    change ¬ k < T at h
    simpa only [Set.mem_setOf_eq, if_neg h, ne_eq, not_true_eq_false] using hk⟩

@[simp] theorem truncate_apply (T : ℕ) (v : ℕ → E) (k : ℕ) :
    truncate T v k = if k < T then v k else 0 := rfl

theorem truncate_congr {T : ℕ} {v w : ℕ → E} (h : ∀ k < T, v k = w k) :
    truncate T v = truncate T w := by
  ext k
  by_cases hk : k < T
  · simp [hk, h k hk]
  · simp [hk]

@[simp] theorem truncate_add (T : ℕ) (v w : ℕ → E) :
    truncate T (v + w) = truncate T v + truncate T w := by
  ext k
  by_cases hk : k < T <;> simp [hk]

@[simp] theorem truncate_zero (T : ℕ) :
    truncate T (0 : ℕ → E) = 0 := by
  ext k
  simp

@[simp] theorem truncate_truncate (T : ℕ) (v : ℕ → E) :
    truncate T (truncate T v) = truncate T v := by
  ext k
  by_cases hk : k < T <;> simp [hk]

/-- Restriction to a prefix decreases the `ℓ₂` norm, whenever the full
sequence has already been shown square summable. -/
theorem truncate_norm_le (T : ℕ) (v : lp (fun _ : ℕ ↦ E) 2) :
    ‖truncate T v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  by_cases hk : k < T <;> simp [hk, norm_nonneg]

/-- Finite prefixes converge pointwise without any summability hypothesis. -/
theorem truncate_tendsto (v : ℕ → E) :
    Tendsto (fun T : ℕ ↦ (truncate T v : ℕ → E)) atTop (nhds v) := by
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop k] with T hT
  simp [hT]

/-- Uniform prefix bounds prove square summability. In particular this lemma
does not presuppose that the undiscounted or discounted orbit is in `ℓ₂`. -/
theorem memℓp_of_truncate_norm_le {v : ℕ → E} {B : ℝ}
    (hB : ∀ T : ℕ, ‖truncate T v‖ ≤ B) : Memℓp v 2 := by
  apply lp.memℓp_of_tendsto ?_ (truncate_tendsto v)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B, ?_⟩
  rintro _ ⟨T, rfl⟩
  exact hB T

/-- The full norm inherits the same uniform finite-prefix bound. -/
theorem norm_le_of_truncate_norm_le {v : ℕ → E} {B : ℝ}
    (hB : ∀ T : ℕ, ‖truncate T v‖ ≤ B) :
    ‖(⟨v, memℓp_of_truncate_norm_le hB⟩ : lp (fun _ : ℕ ↦ E) 2)‖ ≤ B := by
  exact lp.norm_le_of_tendsto (Eventually.of_forall hB) (truncate_tendsto v)

section Scalar

variable [NormedSpace ℝ E]

@[simp] theorem truncate_smul (T : ℕ) (a : ℝ) (v : ℕ → E) :
    truncate T (a • v) = a • truncate T v := by
  ext k
  by_cases hk : k < T <;> simp [hk]

end Scalar

end ADMM.UnitCircle.Causal
