/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 15.55: in the multidimensional setting, degenerate normal laws with positive
semidefinite covariance matrix `C` are the canonical measures `multivariateGaussian μ C`. -/
recall ProbabilityTheory.multivariateGaussian

/- Their characteristic function is
`t ↦ exp (⟪t, μ⟫ * I - t ⬝ᵥ C *ᵥ t / 2)`. -/
recall ProbabilityTheory.charFun_multivariateGaussian
