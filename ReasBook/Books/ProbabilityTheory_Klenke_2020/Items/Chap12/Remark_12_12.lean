/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration (OrderDual ℕ) mΩ}
variable {X : OrderDual ℕ → Ω → ℝ}

/- Remark 12.12 is `source-facing`: it records the textbook consequence for a backward martingale.
Its `core/canonical` owner layer is the martingale API on `OrderDual ℕ` together with the owner
uniform-integrability theorem `Integrable.uniformIntegrable_condExp_filtration`. The source-facing
remark below is proved directly from that owner theorem, while the textbook conditional-
expectation description of the reversed process is used only internally as a bridge. -/

variable [IsFiniteMeasure μ]

-- Proof sketch: use the previous conditional-expectation representation to identify `X` almost
-- everywhere with the family `fun n ↦ μ[X 0 | ℱ n]`, then apply uniform integrability of
-- conditional expectations of the integrable variable `X 0`.
/-- Remark 12.12: a backward martingale `(X_{-n})` is uniformly integrable, since each
`X_{-n}` is almost surely the conditional expectation of `X₀` with respect to `ℱ_{-n}`. -/
theorem backward_martingale_uniformIntegrable (hX : Martingale X ℱ μ) :
    UniformIntegrable X 1 μ := by
  have hUI : UniformIntegrable (fun n : OrderDual ℕ ↦ μ[X 0 | ℱ n]) 1 μ := by
    simpa using
      (show UniformIntegrable (fun n : OrderDual ℕ ↦ μ[X 0 | ℱ n]) 1 μ from
        (hX.integrable 0).uniformIntegrable_condExp_filtration)
  refine hUI.ae_eq fun n ↦ ?_
  simpa using hX.2 n 0 (show (0 : ℕ) ≤ n by exact Nat.zero_le _)
