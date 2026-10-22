/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_14

open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

namespace ProbabilityTheory

variable {E : Type u} [Fintype E]

/- `source-facing`: Definition 19.21 is the owner declaration for the quadratic energy functional
of a finite electrical flow/current. Its primitive data are exactly a resistance function `R` and a
flow/current `I`; the double-sum formula is the definition itself, not a bridge to an earlier
owner. Definitions 19.13 and 19.14 provide the ambient flow/current notions, while
Theorem 19.20 is the bridge that rewrites boundary data into this same quadratic expression. Lean
uses the script notation `ℒ(I; R)` as a thin source-facing stand-in for the textbook symbol
`L_I^R`. -/

/-- Definition 19.21: the energy dissipation of a flow `I` with resistance function `R`, namely
`L_I = (1 / 2) * ∑ x, ∑ y, I x y ^ 2 * R x y`. -/
def energyDissipation (R I : E → E → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, I x y ^ 2 * R x y

scoped[ProbabilityTheory] notation "ℒ(" I "; " R ")" => energyDissipation R I

-- Proof sketch: unfold `energyDissipation`; this is exactly the finite double sum from the
-- definition, written as iterated sums over `E`.
/-- The source notation `ℒ(I; R)`, formalizing the textbook energy symbol `L_I^R`, is the
half-weighted double sum of `I x y ^ 2 * R x y` over all ordered pairs of vertices. -/
theorem energyDissipation_def (R I : E → E → ℝ) :
    ℒ(I; R) = (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, I x y ^ 2 * R x y := rfl

end ProbabilityTheory
