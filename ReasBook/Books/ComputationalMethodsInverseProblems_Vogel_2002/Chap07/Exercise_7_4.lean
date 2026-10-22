/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_12.Operator
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_8.Deblurring

public section

noncomputable section

open scoped Matrix

section

/- Exercise 7.4. In the Section 7.2.1 image-deblurring model, the source
compares the randomized trace-estimate versions of UPRE and GCV from §7.1.3
with the corresponding exact computations. The source-facing owners here are
therefore the estimated image-deblurring objectives, parameterized by trace
estimate families, together with specialization theorems recovering the exact
UPRE/GCV objectives when those estimates equal the actual trace terms.
-/

/-- The influence matrix for the Section 7.2.1 Tikhonov image-deblurring model,
built from the canonical Chapter 1 operator `Tikhonov.operator`. -/
def imageDeblurringInfluenceMatrix {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (α : ℝ) :
    Matrix (Fin n_x × Fin n_y) (Fin n_x × Fin n_y) ℝ :=
  influenceMatrix (imageDeblurringBlurMatrix psf)
    (Tikhonov.operator (imageDeblurringBlurMatrix psf) α)

/-- The exact trace family `α ↦ trace A_α` for the Section 7.2.1
image-deblurring influence matrices. -/
def imageDeblurringInfluenceTrace {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    : ℝ → ℝ :=
  fun α ↦ Matrix.trace (imageDeblurringInfluenceMatrix psf α)

/-- The exact complement-trace family `α ↦ trace (1 - A_α)` for the Section
7.2.1 image-deblurring influence matrices. -/
def imageDeblurringComplementTrace {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    : ℝ → ℝ :=
  fun α ↦ Matrix.trace (1 - imageDeblurringInfluenceMatrix psf α)

/-- The estimated UPRE objective for the Section 7.2.1 discrete
image-deblurring model, obtained by replacing the exact trace term by a
trace-estimate family. -/
def imageDeblurringEstimatedUPRE {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    ℝ → ℝ :=
  fun α ↦
    predictiveRisk (imageDeblurringResidualFamily psf dObs α) +
      (2 * σ ^ 2 / (Fintype.card (Fin n_x × Fin n_y) : ℝ)) * traceEstimate α - σ ^ 2

/-- The estimated GCV objective for the Section 7.2.1 discrete image-deblurring
model, obtained by replacing the exact denominator trace term by a
trace-estimate family. -/
def imageDeblurringEstimatedGCV {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    ℝ → ℝ :=
  fun α ↦
    predictiveRisk (imageDeblurringResidualFamily psf dObs α) /
      ((traceEstimate α / (Fintype.card (Fin n_x × Fin n_y) : ℝ)) ^ 2)

/-- A parameter is an estimated image-deblurring UPRE parameter when it
minimizes the estimated objective on `Set.univ`. -/
def IsImageDeblurringEstimatedUPREParameter {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ) : Prop :=
  IsMinOn (imageDeblurringEstimatedUPRE psf traceEstimate σ dObs) Set.univ α

/-- A parameter is an estimated image-deblurring GCV parameter when it
minimizes the estimated objective on `Set.univ`. -/
def IsImageDeblurringEstimatedGCVParameter {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ) : Prop :=
  IsMinOn (imageDeblurringEstimatedGCV psf traceEstimate dObs) Set.univ α

@[simp] theorem imageDeblurringInfluenceTrace_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (α : ℝ) :
    imageDeblurringInfluenceTrace psf α =
      Matrix.trace (imageDeblurringInfluenceMatrix psf α) := by
  simp [imageDeblurringInfluenceTrace]

@[simp] theorem imageDeblurringComplementTrace_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (α : ℝ) :
    imageDeblurringComplementTrace psf α =
      Matrix.trace (1 - imageDeblurringInfluenceMatrix psf α) := by
  simp [imageDeblurringComplementTrace]

@[simp] theorem IsImageDeblurringEstimatedUPREParameter_iff {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ) :
    IsImageDeblurringEstimatedUPREParameter psf traceEstimate σ dObs α ↔
      IsMinOn (imageDeblurringEstimatedUPRE psf traceEstimate σ dObs) Set.univ α := Iff.rfl

@[simp] theorem IsImageDeblurringEstimatedGCVParameter_iff {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ) :
    IsImageDeblurringEstimatedGCVParameter psf traceEstimate dObs α ↔
      IsMinOn (imageDeblurringEstimatedGCV psf traceEstimate dObs) Set.univ α := Iff.rfl

/-- Specializing `regularizedResidual_influenceMatrix` to the Section 7.2.1
discrete image-deblurring model recovers the existing deblurring residual
family from `Book.Ch7.Exercise_7_8.Deblurring`. -/
theorem imageDeblurringRegularizedResidual_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ) :
    regularizedResidual (imageDeblurringInfluenceMatrix psf α) (imageAsVector dObs) =
      imageDeblurringResidualFamily psf dObs α := by
  have hRecon :
      regularizedSolution
          (Tikhonov.operator (imageDeblurringBlurMatrix psf) α)
          (imageAsVector dObs) =
        Tikhonov.reconstruction (imageDeblurringBlurMatrix psf) α (imageAsVector dObs) := by
    rw [regularizedSolution_eq, Tikhonov.reconstruction_eq]
    rw [Tikhonov.operator_def]
  calc
    regularizedResidual (imageDeblurringInfluenceMatrix psf α) (imageAsVector dObs) =
        (imageDeblurringBlurMatrix psf).toEuclideanLin
            (regularizedSolution
              (Tikhonov.operator (imageDeblurringBlurMatrix psf) α)
              (imageAsVector dObs)) -
          imageAsVector dObs := by
          rw [imageDeblurringInfluenceMatrix]
          exact regularizedResidual_influenceMatrix
            (imageDeblurringBlurMatrix psf)
            (Tikhonov.operator (imageDeblurringBlurMatrix psf) α)
            (imageAsVector dObs)
    _ =
        (imageDeblurringBlurMatrix psf).toEuclideanLin
            (Tikhonov.reconstruction (imageDeblurringBlurMatrix psf) α (imageAsVector dObs)) -
          imageAsVector dObs := by rw [hRecon]
    _ = imageDeblurringResidualFamily psf dObs α := by
          symm
          exact imageDeblurringResidualFamily_eq psf dObs α

/-- Evaluating the estimated image-deblurring UPRE objective gives the source
formula with the residual family and the supplied trace estimate. -/
@[simp] theorem imageDeblurringEstimatedUPRE_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (σ α : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    imageDeblurringEstimatedUPRE psf traceEstimate σ dObs α =
      predictiveRisk (imageDeblurringResidualFamily psf dObs α) +
        (2 * σ ^ 2 / (Fintype.card (Fin n_x × Fin n_y) : ℝ)) *
          traceEstimate α - σ ^ 2 := by
  simp [imageDeblurringEstimatedUPRE]

/-- Evaluating the estimated image-deblurring GCV objective gives the source
formula with the residual family and the supplied denominator trace estimate. -/
@[simp] theorem imageDeblurringEstimatedGCV_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (α : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    imageDeblurringEstimatedGCV psf traceEstimate dObs α =
      predictiveRisk (imageDeblurringResidualFamily psf dObs α) /
        ((traceEstimate α / (Fintype.card (Fin n_x × Fin n_y) : ℝ)) ^ 2) := by
  simp [imageDeblurringEstimatedGCV]

/-- If the estimated trace equals the exact influence-matrix trace at `α`, then
the estimated image-deblurring UPRE value agrees with the exact computation. -/
theorem imageDeblurringEstimatedUPRE_eq_upre_of_trace {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (σ α : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (hTrace : traceEstimate α = imageDeblurringInfluenceTrace psf α) :
    imageDeblurringEstimatedUPRE psf traceEstimate σ dObs α =
      upre (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) α := by
  rw [imageDeblurringEstimatedUPRE_eq, hTrace, imageDeblurringInfluenceTrace_eq]
  rw [upre_eq_upreValue, upreValue_def, imageDeblurringRegularizedResidual_eq]

/-- If the estimated complement trace equals the exact denominator trace at
`α`, then the estimated image-deblurring GCV value agrees with the exact
computation. -/
theorem imageDeblurringEstimatedGCV_eq_gcv_of_trace {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (α : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (hTrace : traceEstimate α = imageDeblurringComplementTrace psf α) :
    imageDeblurringEstimatedGCV psf traceEstimate dObs α =
      gcv (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) α := by
  rw [imageDeblurringEstimatedGCV_eq, hTrace, imageDeblurringComplementTrace_eq]
  rw [gcv_eq_gcvValue, gcvValue_def, imageDeblurringRegularizedResidual_eq]

/-- If the estimated trace family agrees with the exact influence-matrix trace,
then the estimated image-deblurring UPRE objective is the exact objective. -/
theorem imageDeblurringEstimatedUPRE_eq_upre {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (hTrace : ∀ α, traceEstimate α = imageDeblurringInfluenceTrace psf α) :
    imageDeblurringEstimatedUPRE psf traceEstimate σ dObs =
      upre (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) := by
  funext α
  exact imageDeblurringEstimatedUPRE_eq_upre_of_trace psf traceEstimate σ α dObs (hTrace α)

/-- Helper for Exercise 7.4: plugging the exact influence-matrix trace into the
estimated image-deblurring UPRE objective recovers the canonical exact `upre`
family. -/
theorem imageDeblurringEstimatedUPRE_exactTrace_eq_upre {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    imageDeblurringEstimatedUPRE psf (imageDeblurringInfluenceTrace psf) σ dObs =
      upre (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) := by
  -- With the exact trace family, the generic comparison theorem specializes immediately.
  exact imageDeblurringEstimatedUPRE_eq_upre psf (imageDeblurringInfluenceTrace psf) σ dObs
    (fun α ↦ rfl)

/-- If the estimated complement-trace family agrees with the exact denominator
trace family, then the estimated image-deblurring GCV objective is the exact
objective. -/
theorem imageDeblurringEstimatedGCV_eq_gcv {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (hTrace : ∀ α, traceEstimate α = imageDeblurringComplementTrace psf α) :
    imageDeblurringEstimatedGCV psf traceEstimate dObs =
      gcv (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) := by
  funext α
  exact imageDeblurringEstimatedGCV_eq_gcv_of_trace psf traceEstimate α dObs (hTrace α)

/-- Helper for Exercise 7.4: plugging the exact complement trace into the
estimated image-deblurring GCV objective recovers the canonical exact `gcv`
family. -/
theorem imageDeblurringEstimatedGCV_exactTrace_eq_gcv {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    imageDeblurringEstimatedGCV psf (imageDeblurringComplementTrace psf) dObs =
      gcv (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) := by
  -- The exact complement-trace family is precisely the denominator trace needed by `gcv`.
  exact imageDeblurringEstimatedGCV_eq_gcv psf (imageDeblurringComplementTrace psf) dObs
    (fun α ↦ rfl)

/-- Evaluating the exact image-deblurring UPRE objective gives the pointwise
UPRE formula built from the canonical deblurring residual family and the
Section 7.2.1 influence matrix. -/
theorem imageDeblurringUPRE_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (σ α : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    upre (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) α =
      predictiveRisk (imageDeblurringResidualFamily psf dObs α) +
        (2 * σ ^ 2 / (Fintype.card (Fin n_x × Fin n_y) : ℝ)) *
          Matrix.trace (imageDeblurringInfluenceMatrix psf α) - σ ^ 2 := by
  rw [upre_eq_upreValue, upreValue_def, imageDeblurringRegularizedResidual_eq]

/-- Evaluating the exact image-deblurring GCV objective gives the pointwise GCV
formula built from the canonical deblurring residual family and the Section
7.2.1 influence matrix. -/
theorem imageDeblurringGCV_eq {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (α : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    gcv (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) α =
      predictiveRisk (imageDeblurringResidualFamily psf dObs α) /
        ((Matrix.trace
              (1 - imageDeblurringInfluenceMatrix psf α) /
            (Fintype.card (Fin n_x × Fin n_y) : ℝ)) ^ 2) := by
  rw [gcv_eq_gcvValue, gcvValue_def, imageDeblurringRegularizedResidual_eq]

/-- The exact image-deblurring UPRE-selected parameters are exactly the
minimizers of the canonical exact `upre` objective on `Set.univ`. -/
@[simp] theorem IsImageDeblurringUPREParameter_iff {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ) :
    IsUPREParameter (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) α ↔
      IsMinOn
        (fun β ↦
          predictiveRisk (imageDeblurringResidualFamily psf dObs β) +
            (2 * σ ^ 2 / (Fintype.card (Fin n_x × Fin n_y) : ℝ)) *
              Matrix.trace (imageDeblurringInfluenceMatrix psf β) - σ ^ 2)
        Set.univ α := by
  rw [IsUPREParameter_iff]
  let F : ℝ → ℝ := fun β ↦
    predictiveRisk (imageDeblurringResidualFamily psf dObs β) +
      (2 * σ ^ 2 / (Fintype.card (Fin n_x × Fin n_y) : ℝ)) *
        Matrix.trace (imageDeblurringInfluenceMatrix psf β) - σ ^ 2
  have hF : upre (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) = F := by
    funext β
    exact imageDeblurringUPRE_eq psf σ β dObs
  simp [F, hF]

/-- The exact image-deblurring GCV-selected parameters are exactly the
minimizers of the canonical exact `gcv` objective on `Set.univ`. -/
@[simp] theorem IsImageDeblurringGCVParameter_iff {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ) :
    IsGCVParameter (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) α ↔
      IsMinOn
        (fun β ↦
          predictiveRisk (imageDeblurringResidualFamily psf dObs β) /
            ((Matrix.trace
                  (1 - imageDeblurringInfluenceMatrix psf β) /
                (Fintype.card (Fin n_x × Fin n_y) : ℝ)) ^ 2))
        Set.univ α := by
  rw [IsGCVParameter_iff]
  let F : ℝ → ℝ := fun β ↦
    predictiveRisk (imageDeblurringResidualFamily psf dObs β) /
      ((Matrix.trace
            (1 - imageDeblurringInfluenceMatrix psf β) /
          (Fintype.card (Fin n_x × Fin n_y) : ℝ)) ^ 2)
  have hF : gcv (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) = F := by
    funext β
    exact imageDeblurringGCV_eq psf β dObs
  simp [F, hF]

/-- If the estimated trace family agrees with the exact influence-matrix trace,
then the estimated UPRE minimizers are exactly the exact UPRE minimizers. -/
theorem IsImageDeblurringEstimatedUPREParameter_iff_exact {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ)
    (hTrace : ∀ β, traceEstimate β = imageDeblurringInfluenceTrace psf β) :
    IsImageDeblurringEstimatedUPREParameter psf traceEstimate σ dObs α ↔
      IsUPREParameter (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) α := by
  -- First replace the estimated trace family by the exact influence trace pointwise.
  have hTraceFun : traceEstimate = imageDeblurringInfluenceTrace psf := funext hTrace
  rw [IsImageDeblurringEstimatedUPREParameter_iff, IsUPREParameter_iff]
  -- Then rewrite to the exact-trace specialization, which is already the canonical `upre`.
  simp [hTraceFun, imageDeblurringEstimatedUPRE_exactTrace_eq_upre]

/-- If the estimated complement-trace family agrees with the exact denominator
trace family, then the estimated GCV minimizers are exactly the exact GCV
minimizers. -/
theorem IsImageDeblurringEstimatedGCVParameter_iff_exact {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (traceEstimate : ℝ → ℝ)
    (dObs : Matrix (Fin n_x) (Fin n_y) ℝ)
    (α : ℝ)
    (hTrace : ∀ β, traceEstimate β = imageDeblurringComplementTrace psf β) :
    IsImageDeblurringEstimatedGCVParameter psf traceEstimate dObs α ↔
      IsGCVParameter (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) α := by
  -- First replace the estimated denominator trace family by the exact complement trace.
  have hTraceFun : traceEstimate = imageDeblurringComplementTrace psf := funext hTrace
  rw [IsImageDeblurringEstimatedGCVParameter_iff, IsGCVParameter_iff]
  -- Then rewrite to the exact-trace specialization, which is already the canonical `gcv`.
  simp [hTraceFun, imageDeblurringEstimatedGCV_exactTrace_eq_gcv]

/-- Exercise 7.4. In the Section 7.2.1 image-deblurring model, replacing the
randomized trace estimates by the exact influence and complement traces
recovers exactly the canonical `upre` and `gcv` computations. -/
theorem imageDeblurringRandomizedTraceEstimates_compareWithExactComputations
    {n_x n_y : ℕ}
    (psf : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (σ : ℝ) (dObs : Matrix (Fin n_x) (Fin n_y) ℝ) :
    imageDeblurringEstimatedUPRE psf (imageDeblurringInfluenceTrace psf) σ dObs =
        upre (imageDeblurringInfluenceMatrix psf) σ (imageAsVector dObs) ∧
      imageDeblurringEstimatedGCV psf (imageDeblurringComplementTrace psf) dObs =
        gcv (imageDeblurringInfluenceMatrix psf) (imageAsVector dObs) := by
  constructor
  · -- The exact influence trace specializes the estimated UPRE to the canonical exact one.
    exact imageDeblurringEstimatedUPRE_exactTrace_eq_upre psf σ dObs
  · -- The exact complement trace specializes the estimated GCV to the canonical exact one.
    exact imageDeblurringEstimatedGCV_exactTrace_eq_gcv psf dObs

end
