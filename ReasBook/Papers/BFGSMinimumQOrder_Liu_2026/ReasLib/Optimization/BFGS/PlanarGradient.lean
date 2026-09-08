module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.Normed.Module.Normalize
public import ReasLib.Geometry.Euclidean.Plane.Rotation

public section

noncomputable section

open scoped EuclideanSpace

universe u

namespace PlanarGradient

section OrientedPlane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- The oriented unit tangent obtained by rotating the normalized radial direction. -/
def tangent (o : Orientation ℝ E (Fin 2)) (g : E) : E :=
  o.rightAngleRotation (NormedSpace.normalize g)

/-- The defining formula for the oriented unit tangent. -/
theorem tangent_apply (o : Orientation ℝ E (Fin 2)) (g : E) :
    tangent o g = o.rightAngleRotation (NormedSpace.normalize g) := by
  -- Expose the defining oriented quarter-turn.
  rfl

/-- A nonzero radial direction and its oriented tangent form an orthonormal pair. -/
theorem orthonormal_tangent (o : Orientation ℝ E (Fin 2)) {g : E} (hg : g ≠ 0) :
    Orthonormal ℝ ![NormedSpace.normalize g, tangent o g] := by
  -- Reduce orthonormality to the four inner products of the radial/tangent frame.
  rw [orthonormal_iff_ite]
  intro i j
  rw [tangent_apply]
  fin_cases i <;> fin_cases j
  · simp [NormedSpace.norm_normalize hg]
  · simp
  · simp
  · simp [NormedSpace.norm_normalize hg]

/-- A nonzero radial direction and its oriented tangent span the plane. -/
theorem span_tangent_eq_top (o : Orientation ℝ E (Fin 2)) {g : E} (hg : g ≠ 0) :
    Submodule.span ℝ (Set.range ![NormedSpace.normalize g, tangent o g]) = ⊤ := by
  -- The orthonormal frame is independent and has the full ambient cardinality.
  have hlin := (orthonormal_tangent o hg).linearIndependent
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ E := by
    simpa using (Fact.out : Module.finrank ℝ E = 2).symm
  exact hlin.span_eq_top_of_card_eq_finrank hcard

/-- The tangential perturbation with signed magnitude `δ`. -/
def perturbation (o : Orientation ℝ E (Fin 2)) (g : E) (δ : ℝ) : E :=
  δ • tangent o g

/-- The defining formula for a tangential perturbation. -/
theorem perturbation_apply (o : Orientation ℝ E (Fin 2)) (g : E) (δ : ℝ) :
    perturbation o g δ = δ • tangent o g := by
  -- Expose the signed scalar multiple defining the perturbation.
  rfl

/-- Every tangential perturbation is orthogonal to its radial vector. -/
theorem inner_perturbation (o : Orientation ℝ E (Fin 2)) (g : E) (δ : ℝ) :
    inner ℝ g (perturbation o g δ) = 0 := by
  -- Expand normalization as a scalar multiple, then use alternation of the area form.
  rw [perturbation_apply, tangent_apply, inner_smul_right,
    o.inner_rightAngleRotation_right]
  simp [NormedSpace.normalize]

/-- For a nonzero radial vector, the perturbation has norm `|δ|`. -/
theorem norm_perturbation (o : Orientation ℝ E (Fin 2)) {g : E} (δ : ℝ) (hg : g ≠ 0) :
    ‖perturbation o g δ‖ = |δ| := by
  -- Read the tangent's unit norm from the orthonormal frame.
  have htangent : ‖tangent o g‖ = 1 := (orthonormal_tangent o hg).norm_eq_one 1
  rw [perturbation_apply, norm_smul, htangent, mul_one, Real.norm_eq_abs]

/-- The candidate iterate obtained from a gradient and its tangential perturbation. -/
def candidate (o : Orientation ℝ E (Fin 2)) (g : E) (δ : ℝ) : E :=
  g + perturbation o g δ

/-- The defining formula for the candidate iterate. -/
theorem candidate_apply (o : Orientation ℝ E (Fin 2)) (g : E) (δ : ℝ) :
    candidate o g δ = g + perturbation o g δ := by
  -- Expose the candidate's defining sum.
  rfl

/-- The candidate displacement is exactly its tangential perturbation. -/
theorem candidate_sub (o : Orientation ℝ E (Fin 2)) (g : E) (δ : ℝ) :
    candidate o g δ - g = perturbation o g δ := by
  -- Cancel the radial component in the defining sum.
  rw [candidate_apply, add_sub_cancel_left]

/-- The normalized direction of the difference between consecutive gradients. -/
def stepDirection (gPrev g : E) : E :=
  NormedSpace.normalize (g - gPrev)

/-- The defining formula for the normalized gradient-difference direction. -/
theorem stepDirection_apply (gPrev g : E) :
    stepDirection gPrev g = NormedSpace.normalize (g - gPrev) := by
  -- Expose normalization of the gradient difference.
  rfl

/-- Distinct consecutive gradients have a unit gradient-difference direction. -/
theorem norm_stepDirection {gPrev g : E} (h : g ≠ gPrev) :
    ‖stepDirection gPrev g‖ = 1 := by
  -- Distinct gradients have a nonzero difference, whose normalization is unit.
  have hsub : g - gPrev ≠ 0 := sub_ne_zero_of_ne h
  rw [stepDirection_apply, NormedSpace.norm_normalize hsub]

/-- The component of the current gradient parallel to its step direction. -/
def parallelCoefficient (gPrev g : E) : ℝ :=
  inner ℝ (stepDirection gPrev g) g

/-- The defining formula for the parallel coefficient. -/
theorem parallelCoefficient_apply (gPrev g : E) :
    parallelCoefficient gPrev g = inner ℝ (stepDirection gPrev g) g := by
  -- Expose the parallel inner-product coefficient.
  rfl

/-- The component of the current oriented tangent parallel to its step direction. -/
def tangentCoefficient (o : Orientation ℝ E (Fin 2)) (gPrev g : E) : ℝ :=
  inner ℝ (stepDirection gPrev g) (tangent o g)

/-- The defining formula for the tangent coefficient. -/
theorem tangentCoefficient_apply (o : Orientation ℝ E (Fin 2)) (gPrev g : E) :
    tangentCoefficient o gPrev g = inner ℝ (stepDirection gPrev g) (tangent o g) := by
  -- Expose the tangential inner-product coefficient.
  rfl

/-- The unsigned oriented area between two normalized gradients. -/
def angularSeparation (o : Orientation ℝ E (Fin 2)) (gPrev g : E) : ℝ :=
  |o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g)|

/-- The defining formula for angular separation. -/
theorem angularSeparation_apply (o : Orientation ℝ E (Fin 2)) (gPrev g : E) :
    angularSeparation o gPrev g =
      |o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g)| := by
  -- Expose the absolute oriented-area formula.
  rfl

/-- Angular separation of two nonzero gradients lies in the unit interval. -/
theorem angularSeparation_mem_Icc (o : Orientation ℝ E (Fin 2))
    {gPrev g : E} (hPrev : gPrev ≠ 0) (hg : g ≠ 0) :
    angularSeparation o gPrev g ∈ Set.Icc 0 1 := by
  -- Bound the area below by zero and above by the product of the two unit norms.
  rw [angularSeparation_apply]
  constructor
  · exact abs_nonneg _
  · calc
      |o.areaForm (NormedSpace.normalize gPrev) (NormedSpace.normalize g)| ≤
          ‖NormedSpace.normalize gPrev‖ * ‖NormedSpace.normalize g‖ :=
        o.abs_areaForm_le _ _
      _ = 1 := by
        rw [NormedSpace.norm_normalize hPrev, NormedSpace.norm_normalize hg, one_mul]

/-- The scalar coefficient in the parameterized next-gradient recurrence. -/
def scale (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δ : ℝ) : ℝ :=
  parallelCoefficient gPrev g + tangentCoefficient o gPrev g * δ

/-- The defining formula for the recurrence scale. -/
theorem scale_apply (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δ : ℝ) :
    scale o gPrev g δ =
      parallelCoefficient gPrev g + tangentCoefficient o gPrev g * δ := by
  -- Expose the affine recurrence coefficient.
  rfl

/-- The next gradient in the parameterized planar recurrence. -/
def next (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δ : ℝ) : E :=
  scale o gPrev g δ • stepDirection gPrev g

/-- The parameterized recurrence equation for the next gradient. -/
theorem next_apply (o : Orientation ℝ E (Fin 2)) (gPrev g : E) (δ : ℝ) :
    next o gPrev g δ = scale o gPrev g δ • stepDirection gPrev g := by
  -- Expose the scaled normalized direction defining the next gradient.
  rfl

end OrientedPlane

end PlanarGradient
