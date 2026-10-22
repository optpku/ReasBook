/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Notation_6_1
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus

public section

namespace OutputLeastSquares

universe u v

variable {U : Type u} {Y : Type v}

noncomputable section

/- Exercise 6.3. Suppose `f = f(q)` in equation `(6.6)`. Use adjoint computations
to obtain a formula for the components of the gradient of `(6.13)` in this case. -/
/-- The Chapter 6 parameter-to-observation map inherits the derivative of the
state map by composition with the observation operator. -/
private theorem hasFDerivAt_parameterToObservation {n : ℕ}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : U →L[ℝ] Y) (solve : EuclideanSpace ℝ (Fin n) → U)
    {q : EuclideanSpace ℝ (Fin n)} {Dsolve : EuclideanSpace ℝ (Fin n) →L[ℝ] U}
    (hsolve : HasFDerivAt solve Dsolve q) :
    HasFDerivAt (parameterToObservation C solve) (C.comp Dsolve) q := by
  -- Rewrite the observation map as a composition and apply the chain rule once.
  simpa [parameterToObservation_eq_comp] using C.hasFDerivAt.comp q hsolve

/-- Helper for Exercise 6.3: the directional derivative of the Chapter 6
output-least-squares objective is the residual pairing induced by the
parameter-to-observation derivative plus the regularization derivative. -/
private theorem objectiveDirectionalDerivative
    {n : ℕ} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y]
    (C : U →L[ℝ] Y) (solve : EuclideanSpace ℝ (Fin n) → U) (d : Y)
    (J : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    {q v : EuclideanSpace ℝ (Fin n)}
    (hsolve : DifferentiableAt ℝ solve q) (hJ : DifferentiableAt ℝ J q) :
    fderiv ℝ (objective (parameterToObservation C solve) d J α) q v =
      inner ℝ (C ((fderiv ℝ solve q) v)) (parameterToObservation C solve q - d) +
        α * fderiv ℝ J q v := by
  have hparam :
      HasFDerivAt (parameterToObservation C solve) (C.comp (fderiv ℝ solve q)) q :=
    hasFDerivAt_parameterToObservation C solve hsolve.hasFDerivAt
  have hresSq :
      HasFDerivAt
        (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖parameterToObservation C solve x - d‖ ^ 2)
        (2 • (innerSL ℝ (parameterToObservation C solve q - d)).comp
          (C.comp (fderiv ℝ solve q))) q := by
    -- Differentiate the squared residual by chaining the observation map with `‖·‖^2`.
    simpa using (hparam.sub_const d).norm_sq
  have hres :
      HasFDerivAt
        (fun x : EuclideanSpace ℝ (Fin n) ↦
          (1 / 2 : ℝ) * ‖parameterToObservation C solve x - d‖ ^ 2)
        ((innerSL ℝ (parameterToObservation C solve q - d)).comp
          (C.comp (fderiv ℝ solve q))) q := by
    -- Scale the squared-residual derivative by `1 / 2` and simplify the factor `2`.
    have hresHalf :
        HasFDerivAt
          (fun x : EuclideanSpace ℝ (Fin n) ↦
            (1 / 2 : ℝ) * ‖parameterToObservation C solve x - d‖ ^ 2)
          (((1 / 2 : ℝ)) •
            (2 • (innerSL ℝ (parameterToObservation C solve q - d)).comp
              (C.comp (fderiv ℝ solve q)))) q :=
      hresSq.const_mul (1 / 2 : ℝ)
    exact hresHalf.congr_fderiv <| by
      ext w
      simp [innerSL_apply_apply]
  have hobj :
      HasFDerivAt (objective (parameterToObservation C solve) d J α)
        (((innerSL ℝ (parameterToObservation C solve q - d)).comp
            (C.comp (fderiv ℝ solve q))) +
          α • fderiv ℝ J q) q := by
    -- Differentiate the residual and regularizer separately, then reassemble the objective.
    refine (hres.add (hJ.hasFDerivAt.const_mul α)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [objective]
  -- Evaluate the computed Fréchet derivative on the requested direction.
  calc
    fderiv ℝ (objective (parameterToObservation C solve) d J α) q v =
        ((((innerSL ℝ (parameterToObservation C solve q - d)).comp
            (C.comp (fderiv ℝ solve q))) +
          α • fderiv ℝ J q) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v := by
      simpa using congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hobj.fderiv
    _ =
        inner ℝ (parameterToObservation C solve q - d) (C ((fderiv ℝ solve q) v)) +
          α * fderiv ℝ J q v := by
      simp [add_apply, ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
        inner_sub_left]
    _ =
        inner ℝ (C ((fderiv ℝ solve q) v)) (parameterToObservation C solve q - d) +
          α * fderiv ℝ J q v := by
      rw [real_inner_comm]

namespace ObjectiveGradient

/-- Exercise 6.3. The `i`th coordinate of the gradient of the Chapter 6
output-least-squares objective is the residual paired with the `i`th
parameter-direction derivative `fderiv ℝ solve q (e_i)`, composed with the
observation operator, plus the regularization contribution `α * gradient J q i`. -/

theorem component_eq_inner_parameterToObservationDeriv
    {n : ℕ} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y]
    (C : U →L[ℝ] Y) (solve : EuclideanSpace ℝ (Fin n) → U) (d : Y)
    (J : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    {q : EuclideanSpace ℝ (Fin n)}
    (hsolve : DifferentiableAt ℝ solve q) (hJ : DifferentiableAt ℝ J q)
    (i : Fin n) :
    gradient (objective (parameterToObservation C solve) d J α) q i =
      inner ℝ (C ((fderiv ℝ solve q) (EuclideanSpace.single i (1 : ℝ))))
        (parameterToObservation C solve q - d) + α * gradient J q i := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  -- Rewrite the target coordinate as the directional derivative along the `i`th basis vector.
  calc
    gradient (objective (parameterToObservation C solve) d J α) q i =
        fderiv ℝ (objective (parameterToObservation C solve) d J α) q e := by
      calc
        gradient (objective (parameterToObservation C solve) d J α) q i =
            inner ℝ (gradient (objective (parameterToObservation C solve) d J α) q) e := by
          simpa [e] using
            (EuclideanSpace.inner_single_right i (1 : ℝ)
              (gradient (objective (parameterToObservation C solve) d J α) q)).symm
        _ = fderiv ℝ (objective (parameterToObservation C solve) d J α) q e := by
          simpa [e] using
            (inner_gradient_left
              (f := objective (parameterToObservation C solve) d J α)
              (x := q) (y := e))
    _ =
        inner ℝ (C ((fderiv ℝ solve q) e))
          (parameterToObservation C solve q - d) +
          α * fderiv ℝ J q e := by
      -- Invoke the directional-derivative formula for the objective.
      simpa [e] using objectiveDirectionalDerivative C solve d J α hsolve hJ (v := e)
    _ =
        inner ℝ (C ((fderiv ℝ solve q) (EuclideanSpace.single i (1 : ℝ))))
          (parameterToObservation C solve q - d) +
          α * gradient J q i := by
      -- Convert the regularizer directional derivative back into the `i`th gradient coordinate.
      have hgradJ : fderiv ℝ J q e = gradient J q i := by
        calc
          fderiv ℝ J q e = inner ℝ (gradient J q) e := by
            simpa [e] using (inner_gradient_left (f := J) (x := q) (y := e)).symm
          _ = gradient J q i := by
            simpa [e] using EuclideanSpace.inner_single_right i (1 : ℝ) (gradient J q)
      rw [hgradJ]

/-- Exercise 6.3 in adjoint form. The residual pairing from the previous theorem
can be rewritten through `C.adjoint`, so the `i`th gradient coordinate is the
inner product of the `i`th state-direction derivative with the adjoint residual,
plus the regularization contribution. -/
theorem component_eq_inner_solveDeriv_adjointResidual
    {n : ℕ} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (C : U →L[ℝ] Y) (solve : EuclideanSpace ℝ (Fin n) → U) (d : Y)
    (J : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ)
    {q : EuclideanSpace ℝ (Fin n)}
    (hsolve : DifferentiableAt ℝ solve q) (hJ : DifferentiableAt ℝ J q)
    (i : Fin n) :
    gradient (objective (parameterToObservation C solve) d J α) q i =
      inner ℝ ((fderiv ℝ solve q) (EuclideanSpace.single i (1 : ℝ)))
        (C.adjoint (parameterToObservation C solve q - d)) + α * gradient J q i := by
  rw [component_eq_inner_parameterToObservationDeriv C solve d J α hsolve hJ i]
  rw [ContinuousLinearMap.adjoint_inner_right]

end ObjectiveGradient

end

end OutputLeastSquares
