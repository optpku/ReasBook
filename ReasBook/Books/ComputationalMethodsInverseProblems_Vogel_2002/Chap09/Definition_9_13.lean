/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-
Definition 9.13. Let `𝒞` be given in `(9.21)`. The projected gradient,
`∇_𝒞 J`, is the mapping from `𝒞` into `ℝ^n` with components
`[NonnegativeOrthant.projectedGradient J ⟨f, hf⟩] i = if 0 < f i then gradient J f i
else min (0 : ℝ) (gradient J f i)`, for `hf : f ∈ NonnegativeOrthant.feasibleSet n`.
-/
/-- Definition 9.13. The projected gradient on the nonnegative orthant is the
coordinatewise clipped gradient vector associated to a feasible point `f`. -/
def projectedGradient
    (J : EuclideanSpace ℝ (Fin n) → ℝ) :
    feasibleSet n → EuclideanSpace ℝ (Fin n) := fun ⟨f, _⟩ ↦
  WithLp.toLp 2
    (fun i ↦ if 0 < f i then gradient J f i else min (0 : ℝ) (gradient J f i))

/-- Helper for Definition 9.13: the `i`-th coordinate of `projectedGradient J ⟨f, hf⟩`
is given by the coordinatewise clipped gradient formula. -/
theorem projectedGradient_apply
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n))
    (hf : f ∈ feasibleSet n)
    (i : Fin n) :
    projectedGradient J ⟨f, hf⟩ i =
      if 0 < f i then gradient J f i else min (0 : ℝ) (gradient J f i) := by
  -- Unfold the definition and read off the `i`-th coordinate of `WithLp.toLp`.
  simp only [projectedGradient, PiLp.toLp_apply]

/-- Helper for Definition 9.13: at a strictly positive coordinate,
`projectedGradient J ⟨f, hf⟩` agrees with the ordinary gradient. -/
theorem projectedGradient_apply_of_pos
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n))
    (hf : f ∈ feasibleSet n)
    (i : Fin n)
    (hi : 0 < f i) :
    projectedGradient J ⟨f, hf⟩ i = gradient J f i := by
  -- Reduce to the coordinate formula and simplify the positive branch.
  simp [projectedGradient_apply, hi]

/-- Helper for Definition 9.13: at a vanishing coordinate,
`projectedGradient J ⟨f, hf⟩` is the minimum of `0` and the corresponding
gradient entry. -/
theorem projectedGradient_apply_of_eq_zero
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n))
    (hf : f ∈ feasibleSet n)
    (i : Fin n)
    (hi : f i = 0) :
    projectedGradient J ⟨f, hf⟩ i = min (0 : ℝ) (gradient J f i) := by
  -- Rewrite the coordinate to zero so the clipped branch becomes the minimum.
  simp [projectedGradient_apply, hi]

end NonnegativeOrthant

#check NonnegativeOrthant.projectedGradient
