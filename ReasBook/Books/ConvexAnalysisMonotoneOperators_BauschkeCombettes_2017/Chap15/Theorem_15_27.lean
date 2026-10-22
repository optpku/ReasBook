/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Fact_15_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_26
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 15.27 is the chapter's conjugation identity and attained infimum
  formula under the three textbook regularity branches:
  (i) `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`;
  (ii) `K` is finite-dimensional, `g` is polyhedral, and
  `effectiveDomain g ∩ ri (L '' effectiveDomain f) ≠ ∅`;
  (iii) `H` and `K` are finite-dimensional, both `f` and `g` are polyhedral, and
  `effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅`.
- `core/canonical`: the owner objects are `compositePrimalObjective`, `compositeDualObjective`,
  `compositeDualOptimalValue`, and the dual infimal convolution
  `f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)`.
- `bridge/view`: Theorem 15.23 and Fact 15.25 are the branch-specific attainment engines for the
  owner dual objective, while `shiftedCompositeDualObjective f g L u` is only the fiberwise
  translated minimand whose infimum at `u` computes the owner dual infimal convolution. In the
  zero-shift case, downstream files should use `compositeDualObjective f g L` directly.
-/

/-- The dual minimization functional from formula `(15.43)` at a fixed dual point `u`. This is
the source-facing fiberwise view of the owner dual infimal convolution
`f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗)` at `u`. -/
def shiftedCompositeDualObjective
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) : K → EReal :=
  fun v ↦
    f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v

/-- Evaluating `shiftedCompositeDualObjective` gives the explicit minimand
`f^*(u - L^* v) + g^*(v)`. -/
@[simp] theorem shiftedCompositeDualObjective_apply
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (u : H) (v : K) :
    shiftedCompositeDualObjective f g L u v =
      f.asEReal∗ (u - L.adjoint v) + g.asEReal∗ v := rfl

/-- At `u = 0`, the shifted dual minimand is exactly the owner dual objective from
Definition 15.19. -/
@[simp] theorem shiftedCompositeDualObjective_zero
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) :
    shiftedCompositeDualObjective f g L 0 = compositeDualObjective f g L := by
  funext v
  simp [shiftedCompositeDualObjective, compositeDualObjective]

variable
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty))

-- Proof sketch: combine Proposition 15.26 with the source-facing regularity split. Branch `(i)`
-- uses Theorem 15.23, while branches `(ii)` and `(iii)` route through Fact 15.25.
/-- Theorem 15.27: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, and
either (i) `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`, or (ii) `K` is
finite-dimensional, `g` is polyhedral, and `effectiveDomain g ∩ ri (L '' effectiveDomain f)` is
nonempty, or (iii) `H` and `K` are finite-dimensional, `f` and `g` are polyhedral, and
`effectiveDomain g ∩ L '' effectiveDomain f` is nonempty, then
`(compositePrimalObjective f g L)∗ = f^* □ (L^* ▷ g^*)`. -/
theorem conjugate_addComp_eq_dualInfimalConvolution_of_regular
    :
    (compositePrimalObjective f g L)∗ =
      f.asEReal∗ □ (L.adjoint ▷ g.asEReal∗) := sorry

-- Proof sketch: evaluate Theorem 15.27 at `u` and rewrite the infimal postcomposition along
-- `L.adjoint` fiberwise. This turns the infimal convolution formula into the displayed infimum
-- over `v : K` of `f^*(u - L^* v) + g^*(v)`.
/-- Evaluating the composite conjugation formula at `u` yields the infimum form of `(15.43)`. -/
theorem conjugate_addComp_eq_sInf_range_shiftedCompositeDualObjective_of_regular
    (u : H) :
    (compositePrimalObjective f g L)∗ u =
      sInf (Set.range (shiftedCompositeDualObjective f g L u)) := sorry

-- Proof sketch: fix `u` and tilt the primal objective by the affine functional
-- `x ↦ -⟪x, u⟫_ℝ`. The same regularity branch split remains available for the tilted problem, so
-- Theorem 15.23 or Fact 15.25 yields a minimizer `v` of the dual objective; rewriting that dual
-- objective gives exactly `shiftedCompositeDualObjective f g L u`.
/-- The explicit minimization formula `(15.43)` is attained at some `v`, so the conjugate value is
the minimum of `v ↦ f^*(u - L^* v) + g^*(v)`. -/
theorem exists_mem_argmin_shiftedCompositeDualObjective_eq_conjugate_addComp_of_regular
    (u : H) :
    ∃ v ∈ Argmin (shiftedCompositeDualObjective f g L u),
      (compositePrimalObjective f g L)∗ u =
        shiftedCompositeDualObjective f g L u v := sorry

end FenchelRockafellarDuality

end ERealFunction
