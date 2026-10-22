/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Remark_9_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ERealFunction InnerProductSpace

noncomputable section

universe u v

namespace ContinuousLinearMap

section HilbertFamily

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, NormedSpace ℝ (K i)]

section Finite

variable [Fintype I]

/-- The canonical `lp`-valued operator attached to a finite family `(Lᵢ)`. This is the standard
bridge from the coordinatewise `ContinuousLinearMap.pi` into the `lp` owner. -/
abbrev toLpOperator (L : ∀ i, H →L[ℝ] K i) : H →L[ℝ] lp K 2 :=
    (((PiLp.continuousLinearEquiv 2 ℝ K).symm.trans
        ((lpPiLpₗᵢ K ℝ).symm.toContinuousLinearEquiv)).toContinuousLinearMap).comp
      (ContinuousLinearMap.pi L)

/-- The `i`th coordinate of the canonical finite-family operator `toLpOperator L` is `Lᵢ x`. -/
@[simp] theorem toLpOperator_apply
    (L : ∀ i, H →L[ℝ] K i) (x : H) (i : I) :
    toLpOperator L x i = L i x := by
  change ((lpPiLpₗᵢ K ℝ).symm (WithLp.toLp 2 fun j ↦ L j x)) i = L i x
  rw [coe_lpPiLpₗᵢ_symm (WithLp.toLp 2 fun j ↦ L j x)]

end Finite

end HilbertFamily

end ContinuousLinearMap

namespace ERealFunction

open ContinuousLinearMap

section Basic

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]

-- Proof sketch: `h x` lies in `]-∞,+∞]`, and subtracting the finite linear term `⟪x, z⟫`
-- preserves the strict inequality above `⊥`.
/-- The linear tilt `x ↦ h(x) - ⟪x, z⟫` stays in `]-∞,+∞]`. -/
theorem linearTilt_value_mem_Ioi_bot
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (x : H) :
    (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) ∈ Set.Ioi (⊥ : EReal) := sorry

/-- The source-facing linear tilt `x ↦ h(x) - ⟪x, z⟫` from Example 19.3. -/
def linearTilt
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨(h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal),
      linearTilt_value_mem_Ioi_bot z h x⟩

/-- Evaluating `linearTilt z h` gives `h(x) - ⟪x, z⟫`. -/
@[simp] theorem linearTilt_apply
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (x : H) :
    (linearTilt z h x : EReal) =
      (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) :=
  rfl

-- Proof sketch: each coordinate term `gᵢ(yᵢ - rᵢ)` lies in `]-∞,+∞]`, and the Hilbert direct sum
-- of such values again stays strictly above `⊥`.
/-- The shifted Hilbert sum `y ↦ ⨁ i, gᵢ(yᵢ - rᵢ)` stays in `]-∞,+∞]`. -/
theorem shiftedHilbertSum_value_mem_Ioi_bot
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (y : lp K 2) :
    (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) y ∈ Set.Ioi (⊥ : EReal) := sorry

/-- The source-facing separable penalty `y ↦ ⨁ i, gᵢ(yᵢ - rᵢ)` from Example 19.3. -/
def shiftedHilbertSum
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) :
    lp K 2 → Set.Ioi (⊥ : EReal) :=
  fun y ↦
    ⟨(⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) y,
      shiftedHilbertSum_value_mem_Ioi_bot r g y⟩

/-- Evaluating `shiftedHilbertSum r g` gives the Hilbert-sum formula
`⨁ i, gᵢ(yᵢ - rᵢ)`. -/
@[simp] theorem shiftedHilbertSum_apply
    (r : lp K 2) (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (y : lp K 2) :
    (shiftedHilbertSum r g y : EReal) =
      (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) y :=
  rfl

section FiniteFamilyBridge

variable [Fintype I]

-- Proof sketch: rewrite the canonical direct-sum operator `toLpOperator L` coordinatewise and
-- use the finite-branch formula for `⨁ i`.
/-- Finite-index specialization of
`compositePerturbationFunction_linearTilt_shiftedHilbertSum_apply`: for a finite family
`(Lᵢ)`, the perturbation value is `h(x) - ⟪x, z⟫ + ∑ᵢ gᵢ(Lᵢ x + yᵢ - rᵢ)`. -/
@[simp] theorem compositePerturbationFunction_linearTilt_shiftedHilbertSum_family_apply_eq_sum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : ∀ i, H →L[ℝ] K i) (x : H) (y : lp K 2) :
    (compositePerturbationFunction (linearTilt z h) (shiftedHilbertSum r g)
        (toLpOperator L) (x, y) : EReal) =
      (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
        ∑ i, (g i (L i x + y i - r i) : EReal) := by
  sorry

-- Proof sketch: evaluate the perturbation at the zero fiber and use the source-facing family
-- formula above.
/-- Finite-index specialization of
`perturbationPrimalObjective_compositePerturbationFunction_linearTilt_shiftedHilbertSum`: the
primal objective is
`x ↦ h(x) - ⟪x, z⟫ + ∑ᵢ gᵢ(Lᵢ x - rᵢ)`. -/
theorem perturbationPrimalObjective_linearTilt_shiftedHilbertSum_family_eq_sum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : ∀ i, H →L[ℝ] K i) :
    perturbationPrimalObjective
        (compositePerturbationFunction (linearTilt z h) (shiftedHilbertSum r g)
          (toLpOperator L)) =
      fun x : H ↦
        (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
          ∑ i, (g i (L i x - r i) : EReal) := sorry

end FiniteFamilyBridge

-- Proof sketch: specialize the canonical owner `compositePerturbationFunction` from
-- Proposition 19.20 to `f = linearTilt z h` and `g = shiftedHilbertSum r g`, then unfold the two
-- source-facing component functions.
/-- Example 19.3: the textbook perturbation is the specialization of the canonical composite
perturbation to `f = h - ⟪·, z⟫` and `g = ⨁ i, gᵢ(· - rᵢ)`. -/
@[simp] theorem compositePerturbationFunction_linearTilt_shiftedHilbertSum_apply
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] lp K 2) (x : H) (y : lp K 2) :
    (compositePerturbationFunction (linearTilt z h) (shiftedHilbertSum r g) L (x, y) : EReal) =
      (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
        (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) (L x + y) := by
  rw [compositePerturbationFunction_apply, linearTilt_apply, shiftedHilbertSum_apply]

-- Proof sketch: specialize Proposition 19.20 (2) to the linear tilt and shifted Hilbert sum, and
-- then unfold the source-facing component functions.
/-- Example 19.3, primal form: the primal objective of the canonical composite perturbation
specialized to `h - ⟪·, z⟫` and `⨁ i, gᵢ(· - rᵢ)` is exactly the textbook objective
`x ↦ h(x) - ⟪x, z⟫ + ⨁ i gᵢ((Lx)ᵢ - rᵢ)`. -/
theorem perturbationPrimalObjective_compositePerturbationFunction_linearTilt_shiftedHilbertSum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] lp K 2) :
    perturbationPrimalObjective
        (compositePerturbationFunction (linearTilt z h) (shiftedHilbertSum r g) L) =
      fun x : H ↦
        (h x : EReal) - ((⟪x, z⟫_ℝ : ℝ) : EReal) +
          (⨁ i, fun yi ↦ (g i (yi - r i) : EReal)) (L x) := by
  ext x
  rw [perturbationPrimalObjective_apply, compositePerturbationFunction_apply,
    linearTilt_apply, shiftedHilbertSum_apply]
  simp

end Basic

end ERealFunction

namespace ContinuousLinearMap

section DualFormula

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

section FiniteFamilyBridge

variable [Fintype I]

/-- For a finite family, the adjoint of `toLpOperator L` is the ordinary sum
`v ↦ ∑ᵢ Lᵢ^* vᵢ`. -/
@[simp] theorem toLpOperator_adjoint_apply_eq_sum
    (L : ∀ i, H →L[ℝ] K i) (v : lp K 2) :
    (toLpOperator L).adjoint v = ∑ i, (L i).adjoint (v i) := by
  sorry

end FiniteFamilyBridge

end DualFormula

end ContinuousLinearMap

namespace ERealFunction

open ContinuousLinearMap

section DualFormula

variable {I : Type v}
variable {H : Type u} {K : I → Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

-- Proof sketch: specialize Proposition 19.20 (3) to `f = linearTilt z h` and
-- `g = shiftedHilbertSum r g`, then rewrite the two conjugates using the affine-tilt conjugation
-- identity and the Hilbert-direct-sum conjugation formula.
/-- Example 19.3, dual form: the dual objective of the canonical composite perturbation
specialized to `h - ⟪·, z⟫` and `⨁ i, gᵢ(· - rᵢ)` is
`v ↦ h^*(z - L^* v) + ⨁ i (gᵢ^*(vᵢ) + ⟪vᵢ, rᵢ⟫)`. -/
theorem perturbationDualObjective_compositePerturbationFunction_linearTilt_shiftedHilbertSum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] lp K 2) :
    perturbationDualObjective
        (compositePerturbationFunction (linearTilt z h) (shiftedHilbertSum r g) L) =
      fun v : lp K 2 ↦
        h.asEReal∗ (z - L.adjoint v) +
          (⨁ i, fun vi ↦ (g i).asEReal∗ vi + ((⟪vi, r i⟫_ℝ : ℝ) : EReal)) v := sorry

section FiniteFamilyBridge

variable [Fintype I]

-- Proof sketch: specialize the canonical dual formula to the canonical finite-family operator
-- `toLpOperator L`, then use the finite-branch formulas for the adjoint and the Hilbert sum.
/-- Example 19.3, dual form in source-facing finite-family coordinates: the dual objective is
`v ↦ h^*(z - ∑ᵢ Lᵢ^* vᵢ) + ∑ᵢ (gᵢ^*(vᵢ) + ⟪vᵢ, rᵢ⟫)`. -/
theorem perturbationDualObjective_linearTilt_shiftedHilbertSum_family_eq_sum
    (z : H) (h : H → Set.Ioi (⊥ : EReal)) (r : lp K 2)
    (g : ∀ i, K i → Set.Ioi (⊥ : EReal)) (L : ∀ i, H →L[ℝ] K i) :
    perturbationDualObjective
        (compositePerturbationFunction (linearTilt z h) (shiftedHilbertSum r g)
          (toLpOperator L)) =
      fun v : lp K 2 ↦
        h.asEReal∗ (z - ∑ i, (L i).adjoint (v i)) +
          ∑ i, ((g i).asEReal∗ (v i) + ((⟪v i, r i⟫_ℝ : ℝ) : EReal)) := by
  sorry

end FiniteFamilyBridge

end DualFormula

end ERealFunction
