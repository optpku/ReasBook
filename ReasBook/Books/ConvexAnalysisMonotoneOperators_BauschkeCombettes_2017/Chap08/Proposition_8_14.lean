/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: apply `MonotoneOn.convexOn_of_deriv` to the open convex set `I`; differentiability
-- on `I` gives continuity on `I`, and openness identifies `interior I` with `I`.
/-- Proposition 8.14 (1): if the derivative of a real-valued function is increasing on an open
convex subset `I ⊆ ℝ` (the formalization of the textbook's open interval), then the function is
convex on `I`. This is the canonical `ConvexOn` formulation of the textbook Jensen inequality for
the finite restriction of the proper `]-∞,+∞]`-valued function to `I`. -/
theorem convexOn_of_monotoneOn_deriv_openInterval (I : Set ℝ) (φ : ℝ → ℝ)
    (hI_convex : Convex ℝ I) (hI_open : IsOpen I) (hφ_diff : DifferentiableOn ℝ φ I)
    (hφ'_mono : MonotoneOn (deriv φ) I) :
    ConvexOn ℝ I φ := by
  -- Re-express the derivative hypotheses on `interior I`, which is the domain expected by mathlib.
  have hφ_diff_interior : DifferentiableOn ℝ φ (interior I) := by
    simpa [hI_open.interior_eq] using hφ_diff
  have hφ'_mono_interior : MonotoneOn (deriv φ) (interior I) := by
    simpa [hI_open.interior_eq] using hφ'_mono
  -- Then apply the standard convexity criterion from monotonicity of the derivative.
  exact hφ'_mono_interior.convexOn_of_deriv hI_convex hφ_diff.continuousOn hφ_diff_interior

-- Proof sketch: use `StrictMonoOn.strictConvexOn_of_deriv` on the open convex set `I`;
-- differentiability on `I` gives continuity on `I`, and openness turns the interior condition into
-- a statement on `I` itself.
/-- Proposition 8.14 (2): if the derivative of a real-valued function is strictly increasing on an
open convex subset `I ⊆ ℝ` (the formalization of the textbook's open interval), then the function
is strictly convex on `I`. This is the canonical `StrictConvexOn` formulation of the textbook's
strict Jensen inequality for the finite restriction of the proper `]-∞,+∞]`-valued function to
`I`. -/
theorem strictConvexOn_of_strictMonoOn_deriv_openInterval (I : Set ℝ) (φ : ℝ → ℝ)
    (hI_convex : Convex ℝ I) (hI_open : IsOpen I) (hφ_diff : DifferentiableOn ℝ φ I)
    (hφ'_strictMono : StrictMonoOn (deriv φ) I) :
    StrictConvexOn ℝ I φ := by
  -- Re-express the strict derivative monotonicity on `interior I`, which equals `I` by openness.
  have hφ'_strictMono_interior : StrictMonoOn (deriv φ) (interior I) := by
    simpa [hI_open.interior_eq] using hφ'_strictMono
  -- The strict convexity criterion only needs continuity of `φ` and strict monotonicity of `φ'`.
  exact hφ'_strictMono_interior.strictConvexOn_of_deriv hI_convex hφ_diff.continuousOn
