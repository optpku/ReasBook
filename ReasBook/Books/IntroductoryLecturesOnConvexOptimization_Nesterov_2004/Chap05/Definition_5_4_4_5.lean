/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped MatrixOrder RealSymmetricMatrixSpace

/- Definition 5.4.4.5 lies in the positive-definite-matrix / logarithmic-barrier domain.

Sampled owner-style declarations in this domain:
* Chapter 5 `𝕊^n` in `Chap05/Definition_5_4_4_1`, the symmetric-matrix carrier owner;
* `𝕊^n₊` in `Chap05/Definition_5_4_4_3`, the chapter owner for the positive-semidefinite cone;
* `Matrix.PosDef` in `Chap01/Definition_1_4_18`, the canonical owner predicate for positive
  definite matrices;
* `analyticBarrier` in `Chap03/Definition_3_62`, the chapter precedent for keeping a logarithmic
  barrier on its intrinsic strict-domain subtype and any ambient formula only as a bridge;
* `epigraphLogarithmicBarrier` in `Chap05/Definition_5_4_3_5`, the chapter owner style for a
  source-facing barrier together with an ambient view.

Best owner abstraction:
* source-facing: the strict cone notation `𝕊^n₊₊` and the log-determinant barrier
  `logDetBarrier n`;
* core/canonical: `Matrix.PosDef`;
* bridge/view: the interior domain `interior (𝕊^n₊ : Set (𝕊^n))`, together with the ambient
  formula `logDetBarrierAmbient n`.

Primitive data:
* `n : ℕ`.

Derived API:
* the strict cone `𝕊^n₊₊`;
* the owner equality `𝕊^n₊₊ = interior (𝕊^n₊)`;
* the intrinsic bridges `StrictPositiveSemidefiniteCone.inv X` and
  `StrictPositiveSemidefiniteCone.sqrtInv X` back to `𝕊^n`;
* the ambient formula `logDetBarrierAmbient n`;
* the source-facing barrier `logDetBarrier n`.

This file therefore keeps the textbook strict cone `𝕊^n₊₊ = int(𝕊^n₊)` on the Chapter 5
symmetric carrier `𝕊^n`, while retaining `Matrix.PosDef` only as the canonical matrix-level bridge
used by later derivative and volumetric-barrier files.
-/

set_option quotPrecheck false in
scoped[RealSymmetricMatrixSpace] notation:arg "𝕊^" n:arg "₊₊" =>
  (interior (𝕊^n₊ : Set (𝕊^n)))

section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

namespace StrictPositiveSemidefiniteCone

/-- The ambient matrix realization of a strict-cone point. -/
def toMatrix (X : 𝕊^n₊₊) : Mat :=
  ((X : SymmMat) : Mat)

attribute [irreducible] StrictPositiveSemidefiniteCone.toMatrix

@[simp] theorem toMatrix_def (X : 𝕊^n₊₊) :
    toMatrix X = ((X : SymmMat) : Mat) :=
  by
    delta toMatrix
    rfl

end StrictPositiveSemidefiniteCone

/-- The strict cone `𝕊ⁿ₊₊` is definitionally the interior of the positive-semidefinite cone
`𝕊ⁿ₊` in the symmetric carrier `𝕊ⁿ`. -/
@[simp] theorem strictPositiveSemidefiniteCone_eq_interior :
    (𝕊^n₊₊ : Set SymmMat) = interior (𝕊^n₊ : Set SymmMat) :=
  rfl

/-- Membership in `𝕊ⁿ₊₊` is exactly membership in the interior of `𝕊ⁿ₊`. -/
@[simp] theorem mem_strictPositiveSemidefiniteCone_iff
    (X : SymmMat) :
    X ∈ 𝕊^n₊₊ ↔ X ∈ interior (𝕊^n₊ : Set SymmMat) :=
  Iff.rfl

/-- A strict-cone point is symmetric as a matrix. -/
theorem strictPositiveSemidefiniteCone_isSymm
    (X : 𝕊^n₊₊) :
    (((X : SymmMat) : Mat)).IsSymm := by
  simpa using
    (RealSymmetricMatrixSpace.mem_iff_isSymm).mp X.1.2

/-- A strict-cone point is Hermitian as a real matrix. -/
theorem strictPositiveSemidefiniteCone_isHermitian
    (X : 𝕊^n₊₊) :
    (((X : SymmMat) : Mat)).IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using strictPositiveSemidefiniteCone_isSymm X

/-- Helper for Definition 5.4.4.5: subtracting a scalar multiple of the identity keeps a real
symmetric matrix inside `𝕊^n`. -/
private theorem sub_scalar_mem_symm
    (X : SymmMat) (r : ℝ) :
    (((X : Mat) - r • (1 : Mat)) : Mat) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Algebra.smul_def] using
    (RealSymmetricMatrixSpace.isSymm X).sub ((Matrix.isSymm_one : (1 : Mat).IsSymm).smul r)

/-- Helper for Definition 5.4.4.5: the scalar-identity line through `X` inside `𝕊^n`. -/
private def scalarShift
    (X : SymmMat) (r : ℝ) : SymmMat :=
  ⟨((X : Mat) - r • (1 : Mat)), sub_scalar_mem_symm X r⟩

@[simp] private theorem coe_scalarShift
    (X : SymmMat) (r : ℝ) :
    ((scalarShift X r : SymmMat) : Mat) = (X : Mat) - r • (1 : Mat) :=
  rfl

/-- Positive definiteness is the canonical matrix-level view of a strict-cone point. -/
theorem strictPositiveSemidefiniteCone_posDef
    (X : 𝕊^n₊₊) :
    (((X : SymmMat) : Mat)).PosDef := by
  -- Move slightly in the negative identity direction while staying inside the interior cone.
  have hcont : Continuous fun t : ℝ ↦ scalarShift (X : SymmMat) t :=
    Continuous.subtype_mk (by fun_prop) fun t ↦ sub_scalar_mem_symm (X : SymmMat) t
  have hnhds :
      {t : ℝ | scalarShift (X : SymmMat) t ∈ interior (𝕊^n₊ : Set SymmMat)} ∈ nhds (0 : ℝ) := by
    have hpre : interior (𝕊^n₊ : Set SymmMat) ∈ nhds (scalarShift (X : SymmMat) 0) := by
      simpa [scalarShift] using (IsOpen.mem_nhds isOpen_interior X.2 :
        interior (𝕊^n₊ : Set SymmMat) ∈ nhds (X : SymmMat))
    simpa [scalarShift] using hcont.continuousAt.preimage_mem_nhds hpre
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨ε, hε, hεball⟩ := hnhds
  have hhalf_ball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    calc
      |ε / 2 - 0| = ε / 2 := by
        rw [sub_zero, abs_of_pos (half_pos hε)]
      _ < ε := by
        linarith
  have hshift_mem : scalarShift (X : SymmMat) (ε / 2) ∈ 𝕊^n₊ := by
    exact interior_subset (hεball hhalf_ball)
  -- The shifted point is positive semidefinite, so `(ε / 2) • I ≤ X`.
  have hshift_posSemidef : (scalarShift (X : SymmMat) (ε / 2) : Mat).PosSemidef := by
    simpa [mem_positiveSemidefiniteCone_iff] using hshift_mem
  have hshift_nonneg : 0 ≤ (scalarShift (X : SymmMat) (ε / 2) : Mat) := by
    exact (Matrix.nonneg_iff_posSemidef).2 hshift_posSemidef
  have hlower : (ε / 2) • (1 : Mat) ≤ ((X : SymmMat) : Mat) := by
    simpa using (sub_nonneg.mp hshift_nonneg)
  -- Add the positive-definite scalar part back to recover `X`.
  have hscalar_posDef : ((ε / 2) • (1 : Mat)).PosDef :=
    (Matrix.PosDef.one : (1 : Mat).PosDef).smul (half_pos hε)
  have hX_posDef : (((ε / 2) • (1 : Mat)) + (scalarShift (X : SymmMat) (ε / 2) : Mat)).PosDef :=
    hscalar_posDef.add_posSemidef hshift_posSemidef
  simpa [scalarShift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hX_posDef

namespace StrictPositiveSemidefiniteCone

private theorem inv_mem (X : 𝕊^n₊₊) :
    ((((X : SymmMat) : Mat)⁻¹)) ∈ 𝕊^n := by
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  exact (strictPositiveSemidefiniteCone_isSymm X).inv

/-- The matrix inverse of a strict-cone point, viewed back in `𝕊^n`. -/
def inv (X : 𝕊^n₊₊) : SymmMat :=
  ⟨(((X : SymmMat) : Mat)⁻¹), inv_mem X⟩

@[simp] theorem coe_inv (X : 𝕊^n₊₊) :
    ((StrictPositiveSemidefiniteCone.inv X : SymmMat) : Mat) =
      (((X : SymmMat) : Mat)⁻¹) :=
  rfl

private theorem sqrtInv_mem (X : 𝕊^n₊₊) :
    CFC.sqrt ((((X : SymmMat) : Mat)⁻¹)) ∈ 𝕊^n := by
  -- The continuous-functional-calculus square root is always nonnegative, hence Hermitian.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  have hsqrt_nonneg : 0 ≤ CFC.sqrt ((((X : SymmMat) : Mat)⁻¹)) :=
    CFC.sqrt_nonneg _
  have hsqrt_posSemidef : (CFC.sqrt ((((X : SymmMat) : Mat)⁻¹))).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef).mp hsqrt_nonneg
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using hsqrt_posSemidef.isHermitian

/-- The inverse square root of a strict-cone point, viewed back in `𝕊^n`. -/
def sqrtInv (X : 𝕊^n₊₊) : SymmMat :=
  ⟨CFC.sqrt ((((X : SymmMat) : Mat)⁻¹)), sqrtInv_mem X⟩

@[simp] theorem coe_sqrtInv (X : 𝕊^n₊₊) :
    ((StrictPositiveSemidefiniteCone.sqrtInv X : SymmMat) : Mat) =
      CFC.sqrt ((((X : SymmMat) : Mat)⁻¹)) :=
  rfl

end StrictPositiveSemidefiniteCone

namespace RealSymmetricMatrixSpace

/-- The intrinsic eigenvalues of a strict-cone point are positive. -/
theorem eigenvalues_pos
    (X : 𝕊^n₊₊) (i : Fin n) :
    0 < eigenvalues (X : SymmMat) i := by
  simpa [eigenvalues] using
    (strictPositiveSemidefiniteCone_posDef X).eigenvalues_pos i

end RealSymmetricMatrixSpace

/-- Helper for Definition 5.4.4.5: a positive-definite symmetric matrix belongs to
`interior (𝕊^n₊ : Set (𝕊^n))`. -/
private lemma posDef_existsScalarLowerBound
    {X : SymmMat} (hX : (X : Mat).PosDef) :
    ∃ r : ℝ, 0 < r ∧ r • (1 : Mat) ≤ (X : Mat) := by
  by_cases hnontriv : Nontrivial Mat
  · letI : Nontrivial Mat := hnontriv
    -- Use strict positivity to move the matrix-order lower bound to a scalar multiple of `I`.
    have hstrict : IsStrictlyPositive (X : Mat) := hX.isStrictlyPositive
    have hself : IsSelfAdjoint (X : Mat) := by
      simpa [Matrix.IsHermitian] using RealSymmetricMatrixSpace.isHermitian X
    obtain ⟨r, hr, hrX⟩ :=
      (CFC.exists_pos_algebraMap_le_iff (a := (X : Mat)) hself).2
        (fun x hx ↦ hstrict.spectrum_pos hx)
    exact ⟨r, hr, by simpa [Algebra.algebraMap_eq_smul_one] using hrX⟩
  · haveI : Subsingleton Mat := not_nontrivial_iff_subsingleton.mp hnontriv
    have hone : (1 : Mat) = 0 := Subsingleton.elim _ _
    have hzero : (X : Mat) = 0 := Subsingleton.elim _ _
    refine ⟨1, zero_lt_one, ?_⟩
    simp [hone, hzero]

/-- Helper for Definition 5.4.4.5: a positive scalar multiple of the identity matrix is an
interior point of `𝕊^n₊`. -/
private lemma scalarMemInterior_positiveSemidefiniteCone
    {r : ℝ} (hr : 0 < r) :
    (r • (1 : SymmMat)) ∈ interior (𝕊^n₊ : Set SymmMat) := by
  letI : NormedAddCommGroup Mat := Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℝ Mat := Matrix.instL2OpNormedSpace
  let coeLin : SymmMat →ₗ[ℝ] Mat :=
    { toFun := fun Y ↦ (Y : Mat)
      map_add' := by intro X Y; rfl
      map_smul' := by intro a Y; rfl }
  let W : Set Mat := Metric.ball (r • (1 : Mat)) r
  let V : Set SymmMat := {Y : SymmMat | (Y : Mat) ∈ W}
  have hVopen : IsOpen V := by
    -- The candidate neighborhood is a norm-open sublevel set in the symmetric carrier.
    have hWopen : IsOpen W := by
      simp [W]
    have hcoe_cont : Continuous fun Y : SymmMat ↦ (Y : Mat) :=
      LinearMap.continuous_of_finiteDimensional coeLin
    simpa [V, W, coeLin] using hWopen.preimage hcoe_cont
  have hVsubset : V ⊆ (𝕊^n₊ : Set SymmMat) := by
    intro Y hY
    let Δ : Mat := (Y : Mat) - r • (1 : Mat)
    have hΔnorm : ‖Δ‖ < r := by
      simpa [V, W, Δ, Metric.mem_ball, dist_eq_norm] using hY
    rw [mem_positiveSemidefiniteCone_iff_inner_nonneg]
    intro u
    have hΔmulVec : ‖Δ.toEuclideanLin u‖ ≤ ‖Δ‖ * ‖u‖ := by
      simpa using Matrix.l2_opNorm_mulVec Δ u
    have hΔquad_abs : |inner ℝ (Δ.toEuclideanLin u) u| ≤ ‖Δ‖ * ‖u‖ ^ 2 := by
      calc
        |inner ℝ (Δ.toEuclideanLin u) u| ≤ ‖Δ.toEuclideanLin u‖ * ‖u‖ := by
          exact abs_real_inner_le_norm _ _
        _ ≤ (‖Δ‖ * ‖u‖) * ‖u‖ := by
          gcongr
        _ = ‖Δ‖ * ‖u‖ ^ 2 := by
          ring
    have hΔquad : -(‖Δ‖ * ‖u‖ ^ 2) ≤ inner ℝ (Δ.toEuclideanLin u) u :=
      neg_le_of_abs_le hΔquad_abs
    have hrΔ_nonneg : 0 ≤ r - ‖Δ‖ := by
      linarith
    have hsplit : (Y : Mat).toEuclideanLin u = r • u + Δ.toEuclideanLin u := by
      simp [Δ, sub_eq_add_neg, add_comm]
    calc
      0 ≤ (r - ‖Δ‖) * ‖u‖ ^ 2 := by
        positivity
      _ = r * ‖u‖ ^ 2 - (‖Δ‖ * ‖u‖ ^ 2) := by
        ring
      _ ≤ r * ‖u‖ ^ 2 + inner ℝ (Δ.toEuclideanLin u) u := by
        linarith
      _ = inner ℝ ((r : ℝ) • u + Δ.toEuclideanLin u) u := by
        simp [inner_add_left, real_inner_smul_left]
      _ = inner ℝ ((Y : Mat).toEuclideanLin u) u := by
        rw [hsplit]
  have hcenter : (r • (1 : SymmMat)) ∈ V := by
    simpa [V, W, Metric.mem_ball, dist_eq_norm] using hr
  exact interior_mono hVsubset <|
    (subset_interior_iff_isOpen.mpr hVopen) hcenter

/-- Helper for Definition 5.4.4.5: a symmetric matrix with a positive scalar lower bound lies in
`interior (𝕊^n₊ : Set (𝕊^n))`. -/
private lemma symmMemInterior_positiveSemidefiniteCone_of_scalarLowerBound
    {X : SymmMat}
    (hX : ∃ r : ℝ, 0 < r ∧ r • (1 : Mat) ≤ (X : Mat)) :
    X ∈ interior (𝕊^n₊ : Set SymmMat) := by
  rcases hX with ⟨r, hr, hrX⟩
  let Z : SymmMat := ((2 : ℝ) * r) • (1 : SymmMat)
  let Y : SymmMat := (2 : ℝ) • (X - r • (1 : SymmMat))
  have hZ : Z ∈ interior (𝕊^n₊ : Set SymmMat) := by
    -- The interior base point is the scalar identity matrix.
    simpa [Z] using scalarMemInterior_positiveSemidefiniteCone (r := 2 * r) (by positivity)
  have hY : Y ∈ 𝕊^n₊ := by
    -- The slack matrix remains positive semidefinite after scaling by a nonnegative scalar.
    have hslack_nonneg : 0 ≤ (X : Mat) - r • (1 : Mat) := sub_nonneg.mpr hrX
    have hslack_psd : ((X : Mat) - r • (1 : Mat)).PosSemidef :=
      (Matrix.nonneg_iff_posSemidef).mp hslack_nonneg
    rw [mem_positiveSemidefiniteCone_iff]
    simpa [Y] using hslack_psd.smul (show 0 ≤ (2 : ℝ) by norm_num)
  have hdecomp : (1 / 2 : ℝ) • Z + (1 / 2 : ℝ) • Y = X := by
    -- Route correction: compare both sides entrywise in the symmetric carrier instead of
    -- expanding a neighborhood argument around an arbitrary `X`.
    ext i j
    simp [Z, Y, sub_eq_add_neg]
    ring
  have hconv : Convex ℝ (𝕊^n₊ : Set SymmMat) := positiveSemidefiniteCone_convex n
  exact hdecomp ▸
    hconv.combo_interior_self_mem_interior hZ hY
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)

private lemma posDef_mem_interior_positiveSemidefiniteCone
    {X : SymmMat} (hX : (X : Mat).PosDef) :
    X ∈ interior (𝕊^n₊ : Set SymmMat) := by
  -- Route correction: instead of perturbing an arbitrary `X`, reduce to a scalar interior point
  -- and recover `X` by a convex combination with a positive-semidefinite slack matrix.
  exact symmMemInterior_positiveSemidefiniteCone_of_scalarLowerBound <|
    posDef_existsScalarLowerBound hX

/-- A positive-definite symmetric matrix lies in the strict cone `𝕊ⁿ₊₊`. -/
theorem mem_strictPositiveSemidefiniteCone_of_posDef
    {X : SymmMat} (hX : (X : Mat).PosDef) :
    X ∈ 𝕊^n₊₊ := by
  -- Rewrite the strict cone to the interior bridge proved above.
  simpa [strictPositiveSemidefiniteCone_eq_interior] using
    posDef_mem_interior_positiveSemidefiniteCone hX

end

section

variable (n : ℕ)

/- Definition 5.4.4.5 uses the strict positive-definite cone `𝕊ⁿ₊₊ = int(𝕊ⁿ₊)` as the
intrinsic domain of the log-determinant barrier. -/
#check (𝕊^n₊₊ : Set (𝕊^n))

end

/-
The SDP strict-feasibility owner extends `SemidefiniteOptimizationProblem` by replacing the weak
cone condition `X ∈ 𝕊ⁿ₊` with the strict cone condition `X ∈ 𝕊ⁿ₊₊` while keeping the equality
constraints unchanged. This matches the chapter LP/QCQP owner style for strict feasible sets.
-/
namespace SemidefiniteOptimizationProblem

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n

/-- The strict feasible set `{X | X ∈ 𝕊ⁿ₊₊ ∧ ∀ i, ⟪Aᵢ, X⟫_F = bᵢ}` of a semidefinite
optimization problem. The objective matrix does not enter this owner because strict feasibility
depends only on the constraints and strict positive definiteness. -/
def strictFeasibleSet
    (problem : SemidefiniteOptimizationProblem n m) : Set SymmMat :=
  (𝕊^n₊₊ : Set SymmMat) ∩ (problem.affineSlice : Set SymmMat)

/-- Membership in `problem.strictFeasibleSet` means satisfying all Frobenius equality constraints
and lying in the strict positive-semidefinite cone `𝕊ⁿ₊₊`. -/
@[simp] theorem mem_strictFeasibleSet_iff
    (problem : SemidefiniteOptimizationProblem n m) (X : SymmMat) :
    X ∈ problem.strictFeasibleSet ↔
      X ∈ 𝕊^n₊₊ ∧
        ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i := by
  rw [strictFeasibleSet, Set.mem_inter_iff]
  change X ∈ 𝕊^n₊₊ ∧ X ∈ problem.affineSlice ↔
    X ∈ 𝕊^n₊₊ ∧ ∀ i : Fin m, ⟪problem.constraintMatrices i, X⟫_F = problem.rhs i
  rw [problem.mem_affineSlice_iff]

/-- The subtype of strict feasible matrices for an SDP. -/
abbrev StrictFeasiblePoint
    (problem : SemidefiniteOptimizationProblem n m) :=
  {X : SymmMat // X ∈ problem.strictFeasibleSet}

end SemidefiniteOptimizationProblem

/-- The ambient formula `X ↦ -log det X` on the intrinsic symmetric-matrix carrier `𝕊ⁿ`. It is
only a bridge view; the source-facing owner barrier is `logDetBarrier n` on `𝕊ⁿ₊₊`. -/
def logDetBarrierAmbient (n : ℕ) :
    𝕊^n → ℝ :=
  fun X ↦ -Real.log ((X : Matrix (Fin n) (Fin n) ℝ)).det

/-- Evaluating the ambient log-determinant formula gives `-log (det X)`. -/
@[simp] theorem logDetBarrierAmbient_apply (n : ℕ)
    (X : 𝕊^n) :
    logDetBarrierAmbient n X = -Real.log ((X : Matrix (Fin n) (Fin n) ℝ)).det :=
  rfl

/-- Definition 5.4.4.5: the log-determinant barrier on `int(𝕊ⁿ₊)`, modeled in Lean by the
strict cone `𝕊ⁿ₊₊`. -/
def logDetBarrier (n : ℕ) :
    𝕊^n₊₊ → ℝ :=
  fun X ↦ logDetBarrierAmbient n X.1

/-- Expanding `logDetBarrier n` recovers the ambient bridge formula restricted to the strict
cone `𝕊ⁿ₊₊`. -/
theorem logDetBarrier_def (n : ℕ) :
    logDetBarrier n = fun X ↦ logDetBarrierAmbient n X.1 :=
  rfl

-- Proof sketch: unfold `logDetBarrier`; the definition is exactly the textbook formula
-- `F(X) = -\ln \det X` evaluated on the canonical Lean domain for `int(𝕊ⁿ₊)`.
/-- Evaluating the log-determinant barrier at a positive-definite matrix returns
`-log (det X)`. -/
@[simp] theorem logDetBarrier_apply (n : ℕ)
    (X : 𝕊^n₊₊) :
    logDetBarrier n X = -Real.log ((X : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ).det :=
  rfl

namespace SemidefiniteOptimizationProblem

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n

/-- The affine translation from the direction space of the canonical affine constraint slice to
the slice itself, based at a strict feasible point. -/
def affineSliceMap
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    problem.affineSlice.direction →ᵃ[ℝ] SymmMat :=
  ((Submodule.subtype problem.affineSlice.direction :
      problem.affineSlice.direction →ₗ[ℝ] SymmMat).toAffineMap) +ᵥ
    AffineMap.const ℝ problem.affineSlice.direction (xRef : SymmMat)

/-- The strict pullback of `𝕊ⁿ₊₊` to the direction space of the canonical affine constraint
slice, based at a strict feasible point. -/
def affineSliceStrictDomain
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    Set problem.affineSlice.direction :=
  problem.affineSliceMap xRef ⁻¹' (𝕊^n₊₊ : Set SymmMat)

/-- The log-determinant barrier pulled back from the affine slice to its direction space via a
strict feasible base point. -/
def affineSliceLogDetBarrier
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint) :
    problem.affineSlice.direction → ℝ :=
  fun Δ ↦ logDetBarrierAmbient n (problem.affineSliceMap xRef Δ)

/-- The orthogonal projection of the SDP cost matrix to the direction space of the canonical
affine constraint slice. -/
def affineSliceProjectedCost
    (problem : SemidefiniteOptimizationProblem n m) :
    problem.affineSlice.direction :=
  problem.affineSlice.direction.orthogonalProjection problem.costMatrix

@[simp] theorem affineSliceMap_apply
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    (Δ : problem.affineSlice.direction) :
    problem.affineSliceMap xRef Δ = (Δ : SymmMat) +ᵥ (xRef : SymmMat) :=
  rfl

@[simp] theorem affineSliceLogDetBarrier_apply
    (problem : SemidefiniteOptimizationProblem n m)
    (xRef : problem.StrictFeasiblePoint)
    (Δ : problem.affineSlice.direction) :
    problem.affineSliceLogDetBarrier xRef Δ =
      logDetBarrierAmbient n (problem.affineSliceMap xRef Δ) :=
  rfl

end SemidefiniteOptimizationProblem

end
