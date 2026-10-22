/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {m n p : ℕ}

local notation "DualMultiplierSpace" => (Fin m → ℝ) × (Fin p → ℝ)

/- Definition 3.11 is a `source-facing` item in the affine-constrained duality API. The
`core/canonical` owners are Chapter 2's `effective_domain` for finite-valued loci and the chapter
declarations `lagrangianDualObjective` and `dualObjectiveValues` from `Theorem_3_24`. This file
therefore keeps only the source-facing `dom (-q)` and dual-value views, with `dom (-q)` defined
through the owner `effective_domain` rather than storing the derived lower-finiteness condition as
primitive data. -/
recall effective_domain
recall lagrangianDualObjective
recall dualObjectiveValues

variable (X : Set (Fin n → ℝ))
variable (f : (Fin n → ℝ) → EReal)
variable (g : Fin m → (Fin n → ℝ) → EReal)
variable (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)

local notation "q" => lagrangianDualObjective X f g A b

/-- The effective domain `dom (-q)` consists of the multiplier pairs whose inequality multiplier
is coordinatewise nonnegative and whose dual objective is strictly greater than `-∞`. -/
def affine_constrained_dual_effective_domain :
    Set DualMultiplierSpace :=
  {yz : DualMultiplierSpace | ∀ i : Fin m, 0 ≤ yz.1 i} ∩
    effective_domain (fun yz : DualMultiplierSpace ↦ -q yz.1 yz.2)

-- Proof sketch: unfold `affine_constrained_dual_effective_domain` to the owner
-- `effective_domain (-q)` and rewrite `-q(y, z) < ⊤` as `q(y, z) ≠ ⊥`, equivalently
-- `⊥ < q(y, z)`.
/-- A multiplier pair belongs to `dom (-q)` exactly when `y` is coordinatewise nonnegative and the
dual objective at `(y, z)` is greater than `-∞`. -/
@[simp] theorem mem_affine_constrained_dual_effective_domain
    (yz : DualMultiplierSpace) :
    yz ∈ affine_constrained_dual_effective_domain X f g A b ↔
      (∀ i : Fin m, 0 ≤ yz.1 i) ∧ ⊥ < q yz.1 yz.2 := by
  simp [affine_constrained_dual_effective_domain, effective_domain, lt_top_iff_ne_top,
    EReal.neg_eq_top_iff, bot_lt_iff_ne_bot]

/-- The dual optimal value is the supremum of the attained dual objective values. -/
def affine_constrained_dual_problem_value : EReal :=
  sSup (dualObjectiveValues X f g A b)

-- Proof sketch: values attained on `dom (-q)` are attained dual objective values, so the
-- `dom (-q)` supremum is bounded above by `sSup (dualObjectiveValues X f g A b)`. Conversely, any
-- attained value is either `⊥`, which is automatically below that supremum, or it comes from a
-- multiplier pair in `dom (-q)`.
/-- The textbook `sup_{(y,z) ∈ dom (-q)} q(y,z)` presentation of the dual value agrees with the
canonical supremum over the owner set `dualObjectiveValues`. -/
theorem affine_constrained_dual_problem_value_eq_sSup_image_effective_domain :
    affine_constrained_dual_problem_value X f g A b =
      sSup
        ((fun yz : DualMultiplierSpace ↦ q yz.1 yz.2) ''
          affine_constrained_dual_effective_domain X f g A b) := by
  rw [affine_constrained_dual_problem_value]
  apply le_antisymm
  · refine sSup_le ?_
    intro qValue hqValue
    rcases hqValue with ⟨y, z, hy, rfl⟩
    by_cases hbot : q y z = ⊥
    · simp [hbot]
    · exact le_sSup <| by
        refine ⟨(y, z), ?_, rfl⟩
        exact (mem_affine_constrained_dual_effective_domain X f g A b (y, z)).2
          ⟨hy, bot_lt_iff_ne_bot.mpr hbot⟩
  · refine sSup_le ?_
    intro qValue hqValue
    rcases hqValue with ⟨yz, hyz, rfl⟩
    exact le_sSup <| by
      exact ⟨yz.1, yz.2, hyz.1, rfl⟩

end
