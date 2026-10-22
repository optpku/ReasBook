/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ProbabilityTheory

/- Definition 14.25: In the textbook's substochastic setting, the composition of kernels is the
canonical kernel composition `Kernel.comp`, written `κ₂ ∘ₖ κ₁`. -/
recall Kernel.comp

/- On measurable sets `A₂`, the composed kernel satisfies the textbook formula
`(κ₂ ∘ₖ κ₁) ω₀ A₂ = ∫⁻ ω₁, κ₂ ω₁ A₂ ∂(κ₁ ω₀)`. -/
recall Kernel.comp_apply'
