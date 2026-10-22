/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_19
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_33
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_9
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Definition_7_15
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Proposition_7_5
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_5
import FirstOrderMethodsOptimization_Beck_2017.Chap07.Theorem_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

local notation "𝕄" => Matrix (Fin m) (Fin n) ℝ
local notation "Mₘ" => Matrix (Fin m) (Fin m) ℝ
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/-- The ambient real matrix space is equipped with its Frobenius norm. -/
local instance : NormedAddCommGroup 𝕄 := Matrix.frobeniusNormedAddCommGroup

/-- The ambient real matrix space is a normed real vector space. -/
local instance : NormedSpace ℝ 𝕄 := Matrix.frobeniusNormedSpace

/-- The ambient real matrix space is equipped with its Frobenius inner product. -/
local instance : InnerProductSpace ℝ 𝕄 := Matrix.frobeniusInnerProductSpace

/-- The rectangular diagonal reconstruction map with a Euclidean singular-value vector input. -/
def orthogonalRectangularDiagonalMapEuclidean
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin (min m n)) → 𝕄 :=
  fun x ↦ orthogonalRectangularDiagonalMap U V x.ofLp

/-- Helper for Theorem 7.7: the local rectangular diagonal model agrees with the Chapter 7
rectangular profile map. -/
private lemma theorem7_7_rectangularDiagonal_eq_profile (x : Fin (min m n) → ℝ) :
    rectangularDiagonal x = rectangularDiagonalProfile x := by
  -- Both rectangular diagonal owners are defined by the same entrywise formula.
  rfl

/-- Helper for Theorem 7.7: the local orthogonal rectangular diagonal map agrees with the Chapter
7 profile-map owner. -/
private lemma theorem7_7_orthogonalRectangularDiagonalMap_eq_profileMap
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalMap U V x =
      orthogonalRectangularDiagonalProfileMap U V x := by
  -- Rewrite the local map through the already-proved profile-map API.
  rw [orthogonalRectangularDiagonalMap_apply,
    orthogonalRectangularDiagonalProfileMap_apply, theorem7_7_rectangularDiagonal_eq_profile]

/-- Helper for Theorem 7.7: the matrix spectral lift of an absolutely permutation symmetric,
closed, convex profile is proper, closed, and convex on the ambient matrix space. -/
lemma matrixSpectralLift_proper_closed_convex
    (f : (Fin (min m n) → ℝ) → EReal) (hf_symm : Function.IsAbsolutelyPermutationSymmetric f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    IsProperExtendedRealFunction (f ∘ singular_value_function) ∧
      LowerSemicontinuous (f ∘ singular_value_function) ∧
      is_convex_function (f ∘ singular_value_function) := by
  have hproper : IsProperExtendedRealFunction (f ∘ singular_value_function) := by
    refine ⟨?_, ?_⟩
    · intro X
      exact hf_symm.ne_bot (singular_value_function X)
    · rcases hf_symm.effective_domain_nonempty with ⟨x, hx⟩
      refine ⟨rectangularDiagonal x, ?_⟩
      have hpull : (f ∘ singular_value_function) (rectangularDiagonal x) = f x := by
        simpa [theorem7_7_rectangularDiagonal_eq_profile, Function.comp] using
          absolutely_symmetric_rectangular_diagonal_pullback_eq f hf_symm x
      rw [mem_effective_domain, hpull]
      simpa [mem_effective_domain] using hx
  have hclosedconv :=
    (absolutely_symmetric_spectral_function_closed_convex_iff f hf_symm).2
      ⟨hf_closed, hf_convex⟩
  -- Properness comes from the singular-value factorization, and Theorem 7.6 supplies closedness
  -- and convexity of the spectral lift.
  exact ⟨hproper, hclosedconv.1, hclosedconv.2⟩

/-- Helper for Theorem 7.7: the Euclidean pullback `y ↦ f y.ofLp` is proper, closed, and convex. -/
private lemma euclidean_pullback_proper_closed_convex
    (f : (Fin (min m n) → ℝ) → EReal) (hf_symm : Function.IsAbsolutelyPermutationSymmetric f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    IsProperExtendedRealFunction (fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp) ∧
      LowerSemicontinuous (fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp) ∧
      is_convex_function (fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp) := by
  let hproper : IsProperExtendedRealFunction f :=
    ⟨hf_symm.ne_bot, hf_symm.effective_domain_nonempty⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro y
      exact hproper.ne_bot y.ofLp
    · rcases hproper.effective_domain_nonempty with ⟨x, hx⟩
      refine ⟨WithLp.toLp (p := (2 : ENNReal)) x, ?_⟩
      simpa using hx
  · -- Closedness is preserved by continuous precomposition along `ofLp`.
    simpa using hf_closed.comp
      (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin (min m n) ↦ ℝ))
  · -- Convexity is preserved by the affine pullback `y ↦ y.ofLp`.
    simpa using
      is_convex_function_precompose_affineMap hf_convex
        ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin (min m n) → ℝ)).toAffineMap)

/-- Helper for Theorem 7.7: transporting a rectangular diagonal model by fixed left/right
orthogonal changes of coordinates only changes the orthogonal factors. -/
private lemma theorem7_7_orthogonal_transport_orthogonalRectangularDiagonalMap_eq
    (U U1 : Matrix.orthogonalGroup (Fin m) ℝ)
    (V V1 : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U1 V1 x * (V : Mₙ) =
      orthogonalRectangularDiagonalMap (U⁻¹ * U1) (V⁻¹ * V1) x := by
  let U' : Matrix.orthogonalGroup (Fin m) ℝ := U⁻¹ * U1
  let V' : Matrix.orthogonalGroup (Fin n) ℝ := V⁻¹ * V1
  -- Route correction: normalize the transported rectangular SVD coordinates once at the level of
  -- `orthogonalRectangularDiagonalMap`, so the outer spectral and proximal wrappers only see the
  -- new orthogonal factors.
  calc
    ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U1 V1 x * (V : Mₙ)
        = ((U : Mₘ)ᵀ) * (((U1 : Mₘ) * rectangularDiagonal x * ((V1 : Mₙ)ᵀ))) * (V : Mₙ) := by
            rw [orthogonalRectangularDiagonalMap_apply]
    _ = ((U : Mₘ)ᵀ) * ((((U1 : Mₘ) * rectangularDiagonal x * ((V1 : Mₙ)ᵀ))) * (V : Mₙ)) := by
          simpa using
            Matrix.mul_assoc ((U : Mₘ)ᵀ)
              (((U1 : Mₘ) * rectangularDiagonal x * ((V1 : Mₙ)ᵀ))) (V : Mₙ)
    _ = (U : Mₘ)ᵀ * (((U1 : Mₘ) * rectangularDiagonal x) * (((V1 : Mₙ)ᵀ) * (V : Mₙ))) := by
          simpa [mul_assoc] using
            congrArg
              (fun M : Matrix (Fin m) (Fin n) ℝ ↦ (U : Mₘ)ᵀ * M)
              (Matrix.mul_assoc ((U1 : Mₘ) * rectangularDiagonal x) ((V1 : Mₙ)ᵀ) (V : Mₙ))
    _ = (U : Mₘ)ᵀ * ((U1 : Mₘ) * (rectangularDiagonal x * (((V1 : Mₙ)ᵀ) * (V : Mₙ)))) := by
          exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ (U : Mₘ)ᵀ * M)
            (Matrix.mul_assoc (U1 : Mₘ) (rectangularDiagonal x) (((V1 : Mₙ)ᵀ) * (V : Mₙ)))
    _ = ((U : Mₘ)ᵀ * (U1 : Mₘ)) * (rectangularDiagonal x * (((V1 : Mₙ)ᵀ) * (V : Mₙ))) := by
          exact (Matrix.mul_assoc (U : Mₘ)ᵀ (U1 : Mₘ)
            (rectangularDiagonal x * (((V1 : Mₙ)ᵀ) * (V : Mₙ)))).symm
    _ = (((U : Mₘ)ᵀ * (U1 : Mₘ)) * rectangularDiagonal x) * (((V1 : Mₙ)ᵀ) * (V : Mₙ)) := by
          exact (Matrix.mul_assoc ((U : Mₘ)ᵀ * (U1 : Mₘ)) (rectangularDiagonal x)
            (((V1 : Mₙ)ᵀ) * (V : Mₙ))).symm
    _ = (U' : Mₘ) * rectangularDiagonal x * ((V' : Mₙ)ᵀ) := by
          simp [U', V', Matrix.star_eq_conjTranspose,
            Matrix.conjTranspose_eq_transpose_of_trivial]
    _ = orthogonalRectangularDiagonalMap U' V' x := by
          rw [orthogonalRectangularDiagonalMap_apply]

/-- Helper for Theorem 7.7: conjugating the rectangular diagonal model back by the same orthogonal
factors recovers the bare rectangular diagonal matrix. -/
private lemma theorem7_7_orthogonal_conjugate_orthogonalRectangularDiagonalMap_eq_rectangularDiagonal
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (x : Fin (min m n) → ℝ) :
    ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V x * (V : Mₙ) =
      rectangularDiagonal x := by
  -- Specialize the transport normalization to the same left/right factors and simplify the
  -- identity orthogonal action on the diagonal model.
  simpa [orthogonalRectangularDiagonalMap_apply] using
    theorem7_7_orthogonal_transport_orthogonalRectangularDiagonalMap_eq
      (U := U) (U1 := U) (V := V) (V1 := V) x

/-- Helper for Theorem 7.7: orthogonal transport on the left and right preserves the singular-value
profile of a rectangular matrix. -/
private lemma theorem7_7_singular_value_function_orthogonal_rectangular_eq
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (Z : 𝕄) :
    singular_value_function (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) = singular_value_function Z := by
  obtain ⟨U1, V1, hZ⟩ :=
    exists_orthogonal_rectangular_diagonalization_with_singular_value_function Z
  have htransport :
      ((U : Mₘ)ᵀ) * Z * (V : Mₙ) =
        orthogonalRectangularDiagonalMap (U⁻¹ * U1) (V⁻¹ * V1) (singular_value_function Z) := by
    -- Rewrite the transported matrix by the ordered singular-value decomposition of `Z`, then
    -- absorb the extra left/right orthogonal factors into the model parameters.
    calc
      ((U : Mₘ)ᵀ) * Z * (V : Mₙ)
          = ((U : Mₘ)ᵀ) *
              orthogonalRectangularDiagonalProfileMap U1 V1 (singular_value_function Z) *
              (V : Mₙ) := by
                simpa using
                  congrArg
                    (fun M : 𝕄 ↦ ((U : Mₘ)ᵀ) * M * (V : Mₙ))
                    hZ
      _ = ((U : Mₘ)ᵀ) *
            orthogonalRectangularDiagonalMap U1 V1 (singular_value_function Z) *
            (V : Mₙ) := by
              simpa using
                congrArg
                  (fun M : 𝕄 ↦ ((U : Mₘ)ᵀ) * M * (V : Mₙ))
                  (theorem7_7_orthogonalRectangularDiagonalMap_eq_profileMap U1 V1
                    (singular_value_function Z)).symm
      _ = orthogonalRectangularDiagonalMap (U⁻¹ * U1) (V⁻¹ * V1) (singular_value_function Z) := by
            exact theorem7_7_orthogonal_transport_orthogonalRectangularDiagonalMap_eq
              (U := U) (U1 := U1) (V := V) (V1 := V1) (singular_value_function Z)
  -- The transported matrix is still an orthogonal image of the same ordered singular-value
  -- vector, so the Chapter 7 rectangular diagonal characterization reads off the same profile.
  rw [htransport, theorem7_7_orthogonalRectangularDiagonalMap_eq_profileMap]
  exact singular_value_function_orthogonalRectangularDiagonalMap_eq_of_nonneg_antitone
    (U⁻¹ * U1) (V⁻¹ * V1) (singular_value_function Z)
    (singular_value_function_nonneg Z) (singular_value_function_antitone Z)

/-- Helper for Theorem 7.7: the Frobenius norm is invariant under left/right orthogonal transport
of a rectangular matrix. -/
private lemma theorem7_7_frobenius_norm_orthogonal_rectangular_eq
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : 𝕄) :
    ‖((U : Mₘ)ᵀ) * A * (V : Mₙ)‖ = ‖A‖ := by
  have hUUt : (U : Mₘ) * (U : Mₘ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₘ)) (R := ℝ)).1 U.2
  have hVUt : (V : Mₙ) * (V : Mₙ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (V : Mₙ)) (R := ℝ)).1 V.2
  -- Copy the square-case trace-cycling argument, now with the rectangular Gram matrix living on
  -- the `n × n` side after the left orthogonal factor cancels.
  rw [frobenius_norm_eq_sqrt_trace_transpose_mul, frobenius_norm_eq_sqrt_trace_transpose_mul]
  congr 1
  calc
    Matrix.trace ((((U : Mₘ)ᵀ * A * (V : Mₙ))ᵀ) * ((U : Mₘ)ᵀ * A * (V : Mₙ)))
      = Matrix.trace ((V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ)) := by
            have hinner :
                (U : Mₘ) * ((U : Mₘ)ᵀ * A * (V : Mₙ)) =
                  (((U : Mₘ) * (U : Mₘ)ᵀ) * A) * (V : Mₙ) := by
              calc
                (U : Mₘ) * ((U : Mₘ)ᵀ * A * (V : Mₙ))
                    = (U : Mₘ) * (((U : Mₘ)ᵀ * A) * (V : Mₙ)) := by
                        rfl
                _ = ((U : Mₘ) * ((U : Mₘ)ᵀ * A)) * (V : Mₙ) := by
                      exact (Matrix.mul_assoc (U : Mₘ) ((U : Mₘ)ᵀ * A) (V : Mₙ)).symm
                _ = (((U : Mₘ) * (U : Mₘ)ᵀ) * A) * (V : Mₙ) := by
                      exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ M * (V : Mₙ))
                        (Matrix.mul_assoc (U : Mₘ) (U : Mₘ)ᵀ A).symm
            have hmat :
                (V : Mₙ)ᵀ * (Aᵀ * (U : Mₘ)) * ((U : Mₘ)ᵀ * A * (V : Mₙ)) =
                  (V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ) := by
              calc
                (V : Mₙ)ᵀ * (Aᵀ * (U : Mₘ)) * ((U : Mₘ)ᵀ * A * (V : Mₙ))
                    = (((V : Mₙ)ᵀ * Aᵀ) * (U : Mₘ)) * ((U : Mₘ)ᵀ * A * (V : Mₙ)) := by
                        exact congrArg
                          (fun M : Matrix (Fin n) (Fin m) ℝ ↦ M * ((U : Mₘ)ᵀ * A * (V : Mₙ)))
                          (Matrix.mul_assoc (V : Mₙ)ᵀ Aᵀ (U : Mₘ)).symm
                _ = ((V : Mₙ)ᵀ * Aᵀ) * ((U : Mₘ) * ((U : Mₘ)ᵀ * A * (V : Mₙ))) := by
                      exact Matrix.mul_assoc ((V : Mₙ)ᵀ * Aᵀ) (U : Mₘ)
                        ((U : Mₘ)ᵀ * A * (V : Mₙ))
                _ = ((V : Mₙ)ᵀ * Aᵀ) * ((((U : Mₘ) * (U : Mₘ)ᵀ) * A) * (V : Mₙ)) := by
                      exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ ((V : Mₙ)ᵀ * Aᵀ) * M)
                        hinner
                _ = (((V : Mₙ)ᵀ * Aᵀ) * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ) := by
                      exact (Matrix.mul_assoc ((V : Mₙ)ᵀ * Aᵀ) (((U : Mₘ) * (U : Mₘ)ᵀ) * A)
                        (V : Mₙ)).symm
                _ = (V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) * (V : Mₙ) := by
                      exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M * (V : Mₙ))
                        (Matrix.mul_assoc (V : Mₙ)ᵀ Aᵀ (((U : Mₘ) * (U : Mₘ)ᵀ) * A))
            simpa [Matrix.transpose_mul, mul_assoc] using congrArg Matrix.trace hmat
    _ = Matrix.trace ((V : Mₙ) * (V : Mₙ)ᵀ * (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A))) := by
          exact Matrix.trace_mul_cycle ((V : Mₙ)ᵀ)
            (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) (V : Mₙ)
    _ = Matrix.trace (Aᵀ * (((U : Mₘ) * (U : Mₘ)ᵀ) * A)) := by
          rw [hVUt]
          simp
    _ = Matrix.trace (Aᵀ * A) := by
          have hleft : ((U : Mₘ) * (U : Mₘ)ᵀ) * A = A := by
            rw [hUUt]
            simp
          simp [hleft]

/-- Helper for Theorem 7.7: orthogonal transport normalizes the matrix spectral proximal
objective to the rectangular diagonal basis. -/
lemma proximal_objective_matrixSpectralLift_orthogonal_rectangular_eq
    (f : (Fin (min m n) → ℝ) → EReal)
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (d : Fin (min m n) → ℝ) (Z : 𝕄) :
    proximal_objective (f ∘ singular_value_function) (orthogonalRectangularDiagonalMap U V d) Z =
      proximal_objective (f ∘ singular_value_function) (rectangularDiagonal d)
        (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) := by
  have hsub :
      (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) - rectangularDiagonal d =
        ((U : Mₘ)ᵀ) * (Z - orthogonalRectangularDiagonalMap U V d) * (V : Mₙ) := by
    -- The orthogonal conjugation sends the base matrix back to the diagonal model, so the whole
    -- difference transports linearly under the same left/right action.
    calc
      (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) - rectangularDiagonal d
          = (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) -
              (((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V d * (V : Mₙ)) := by
                rw [theorem7_7_orthogonal_conjugate_orthogonalRectangularDiagonalMap_eq_rectangularDiagonal]
      _ = (((U : Mₘ)ᵀ) * Z - ((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V d) * (V : Mₙ) := by
            exact
              (Matrix.sub_mul (((U : Mₘ)ᵀ) * Z) (((U : Mₘ)ᵀ) * orthogonalRectangularDiagonalMap U V d)
                (V : Mₙ)).symm
      _ = ((U : Mₘ)ᵀ) * (Z - orthogonalRectangularDiagonalMap U V d) * (V : Mₙ) := by
            exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ M * (V : Mₙ))
              (Matrix.mul_sub ((U : Mₘ)ᵀ) Z (orthogonalRectangularDiagonalMap U V d)).symm
  have hnorm :
      ‖((U : Mₘ)ᵀ * Z * (V : Mₙ)) - rectangularDiagonal d‖ =
        ‖Z - orthogonalRectangularDiagonalMap U V d‖ := by
    rw [hsub,
      theorem7_7_frobenius_norm_orthogonal_rectangular_eq U V
        (Z - orthogonalRectangularDiagonalMap U V d)]
  -- Rewrite both the spectral term and the quadratic penalty through the orthogonal transport.
  rw [proximal_objective_apply, proximal_objective_apply,
    Function.comp_apply, Function.comp_apply,
    theorem7_7_singular_value_function_orthogonal_rectangular_eq U V Z, hnorm]

/-- Helper for Theorem 7.7: the trace of the Gram matrix of a rectangular diagonal matrix is the
sum of the squares of its diagonal profile. -/
private lemma theorem7_7_rectangularDiagonal_trace_sum_sq (x : Fin (min m n) → ℝ) :
    Matrix.trace ((rectangularDiagonal x)ᵀ * rectangularDiagonal x) = ∑ i, x i ^ 2 := by
  let f : ℕ → ℝ := fun j ↦ if h : j < min m n then x ⟨j, h⟩ ^ 2 else 0
  -- Rewrite the Gram matrix through the existing rectangular profile API, then split the trace
  -- into the genuine diagonal block and the zero tail.
  rw [theorem7_7_rectangularDiagonal_eq_profile]
  have hgram :
      (rectangularDiagonalProfile x)ᵀ * rectangularDiagonalProfile x =
        Matrix.diagonal (fun j : Fin n ↦ if h : j.1 < min m n then x ⟨j.1, h⟩ ^ 2 else 0) := by
    simpa using rectangularDiagonalProfile_conjTranspose_mul_eq_squared_tail
      (m := m) (n := n) x
  rw [hgram, Matrix.trace_diagonal]
  have hmin : min m n ≤ n := Nat.min_le_right _ _
  have hhead :
      (∑ j ∈ Finset.range (min m n), f j) = ∑ i : Fin (min m n), x i ^ 2 := by
    have hfin : (∑ i : Fin (min m n), f i) = ∑ i : Fin (min m n), x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      show f i = x i ^ 2
      dsimp [f]
      rw [if_pos i.2]
    calc
      (∑ j ∈ Finset.range (min m n), f j) = ∑ i : Fin (min m n), f i := by
        exact (Fin.sum_univ_eq_sum_range f (min m n)).symm
      _ = ∑ i : Fin (min m n), x i ^ 2 := hfin
  have htail :
      (∑ j ∈ Finset.Ico (min m n) n, f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : ¬ j < min m n := by
      exact not_lt_of_ge (Finset.mem_Ico.mp hj).1
    change (if h : j < min m n then x ⟨j, h⟩ ^ 2 else 0) = 0
    simpa [f] using
      (dif_neg hj' :
        (if h : j < min m n then x ⟨j, h⟩ ^ 2 else 0) = 0)
  calc
    (∑ i : Fin n, if h : i.1 < min m n then x ⟨i.1, h⟩ ^ 2 else 0)
      = ∑ j ∈ Finset.range n, f j := by
          exact Fin.sum_univ_eq_sum_range f n
    _ = (∑ j ∈ Finset.range (min m n), f j) + (∑ j ∈ Finset.Ico (min m n) n, f j) := by
          symm
          exact Finset.sum_range_add_sum_Ico _ hmin
    _ = ∑ i : Fin (min m n), x i ^ 2 := by
          rw [hhead, htail, add_zero]

/-- Helper for Theorem 7.7: the Frobenius norm of a rectangular diagonal matrix is the Euclidean
`L²` norm of its diagonal profile. -/
lemma frobenius_norm_rectangularDiagonal_eq_toLp
    (x : Fin (min m n) → ℝ) :
    ‖rectangularDiagonal x‖ =
      ‖(WithLp.toLp (p := (2 : ENNReal)) x : EuclideanSpace ℝ (Fin (min m n)))‖ := by
  -- Rewrite both norms to the same square-root-of-sum-of-squares normal form.
  rw [frobenius_norm_eq_sqrt_trace_transpose_mul,
    theorem7_7_rectangularDiagonal_trace_sum_sq]
  rw [PiLp.norm_eq_of_L2]
  simp

/-- Helper for Theorem 7.7: the Frobenius distance between two rectangular diagonal matrices is
the Euclidean distance between their diagonal profiles. -/
private lemma theorem7_7_frobenius_norm_rectangularDiagonal_sub_eq
    (x y : Fin (min m n) → ℝ) :
    ‖rectangularDiagonal x - rectangularDiagonal y‖ =
      ‖(WithLp.toLp (p := (2 : ENNReal)) (x - y) :
          EuclideanSpace ℝ (Fin (min m n)))‖ := by
  -- The rectangular diagonal embedding is entrywise linear, so the distance is the norm of a
  -- single rectangular diagonal profile.
  rw [← frobenius_norm_rectangularDiagonal_eq_toLp (x := x - y)]
  congr 1
  ext i j
  by_cases h : i.1 = j.1
  · simp [rectangularDiagonal_apply, h, sub_eq_add_neg]
  · simp [rectangularDiagonal_apply, h, sub_eq_add_neg]

/-- Helper for Theorem 7.7: proximal membership is invariant under orthogonal transport to the
rectangular diagonal basis. -/
lemma mem_prox_matrixSpectralLift_orthogonal_rectangular_iff
    (f : (Fin (min m n) → ℝ) → EReal)
    (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (d : Fin (min m n) → ℝ) (Z : 𝕄) :
    Z ∈ prox[f ∘ singular_value_function] (orthogonalRectangularDiagonalMap U V d) ↔
      (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) ∈
        prox[f ∘ singular_value_function] (rectangularDiagonal d) := by
  have hUtU : (U : Mₘ)ᵀ * (U : Mₘ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).1 U.2
  have hVtV : (V : Mₙ)ᵀ * (V : Mₙ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 V.2
  rw [mem_proximal_mapping_iff, mem_proximal_mapping_iff, isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro h W
    have hcomp := h ((U : Mₘ) * W * (V : Mₙ)ᵀ)
    have hback :
        ((U : Mₘ)ᵀ) * (((U : Mₘ) * W * (V : Mₙ)ᵀ)) * (V : Mₙ) = W := by
      calc
        ((U : Mₘ)ᵀ) * (((U : Mₘ) * W * (V : Mₙ)ᵀ)) * (V : Mₙ)
            = (((U : Mₘ)ᵀ) * (((U : Mₘ) * W * (V : Mₙ)ᵀ) * (V : Mₙ))) := by
                simpa using
                  Matrix.mul_assoc ((U : Mₘ)ᵀ) (((U : Mₘ) * W * (V : Mₙ)ᵀ)) (V : Mₙ)
        _ = ((U : Mₘ)ᵀ) * ((U : Mₘ) * W * ((V : Mₙ)ᵀ * (V : Mₙ))) := by
              simpa [mul_assoc] using
                congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ (U : Mₘ)ᵀ * M)
                  (Matrix.mul_assoc ((U : Mₘ) * W) (V : Mₙ)ᵀ (V : Mₙ))
        _ = ((U : Mₘ)ᵀ) * ((U : Mₘ) * (W * ((V : Mₙ)ᵀ * (V : Mₙ)))) := by
              simpa [mul_assoc] using
                congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ (U : Mₘ)ᵀ * M)
                  (Matrix.mul_assoc (U : Mₘ) W ((V : Mₙ)ᵀ * (V : Mₙ)))
        _ = (((U : Mₘ)ᵀ) * (U : Mₘ)) * (W * ((V : Mₙ)ᵀ * (V : Mₙ))) := by
              exact (Matrix.mul_assoc ((U : Mₘ)ᵀ) (U : Mₘ) (W * ((V : Mₙ)ᵀ * (V : Mₙ)))).symm
        _ = (((U : Mₘ)ᵀ) * (U : Mₘ)) * W * ((V : Mₙ)ᵀ * (V : Mₙ)) := by
              exact (Matrix.mul_assoc (((U : Mₘ)ᵀ) * (U : Mₘ)) W
                ((V : Mₙ)ᵀ * (V : Mₙ))).symm
        _ = W := by
              simp [hUtU, hVtV]
    -- Compare the transported proximal objective against the inverse-changed competitor.
    calc
      proximal_objective (f ∘ singular_value_function) (rectangularDiagonal d)
          (((U : Mₘ)ᵀ) * Z * (V : Mₙ))
          = proximal_objective (f ∘ singular_value_function)
              (orthogonalRectangularDiagonalMap U V d) Z := by
                symm
                exact proximal_objective_matrixSpectralLift_orthogonal_rectangular_eq f U V d Z
      _ ≤ proximal_objective (f ∘ singular_value_function)
            (orthogonalRectangularDiagonalMap U V d) ((U : Mₘ) * W * (V : Mₙ)ᵀ) := hcomp
      _ = proximal_objective (f ∘ singular_value_function) (rectangularDiagonal d) W := by
            rw [proximal_objective_matrixSpectralLift_orthogonal_rectangular_eq f U V d
              ((U : Mₘ) * W * (V : Mₙ)ᵀ), hback]
  · intro h W
    have hcomp := h (((U : Mₘ)ᵀ) * W * (V : Mₙ))
    -- Use the same objective normalization in the forward orthogonal change of variables.
    calc
      proximal_objective (f ∘ singular_value_function)
          (orthogonalRectangularDiagonalMap U V d) Z
          = proximal_objective (f ∘ singular_value_function) (rectangularDiagonal d)
              (((U : Mₘ)ᵀ) * Z * (V : Mₙ)) := by
                exact proximal_objective_matrixSpectralLift_orthogonal_rectangular_eq f U V d Z
      _ ≤ proximal_objective (f ∘ singular_value_function) (rectangularDiagonal d)
            (((U : Mₘ)ᵀ) * W * (V : Mₙ)) := hcomp
      _ = proximal_objective (f ∘ singular_value_function)
            (orthogonalRectangularDiagonalMap U V d) W := by
            exact
              (proximal_objective_matrixSpectralLift_orthogonal_rectangular_eq f U V d W).symm

/-- Helper for Theorem 7.7: the row-side sign pattern that flips only the common-diagonal
coordinate `i`. -/
def row_coordinate_sign_pattern (i : Fin (min m n)) : Fin m → ℝ :=
  fun j ↦ if j.1 = i.1 then -1 else 1

/-- Helper for Theorem 7.7: the column-side sign pattern that flips only the common-diagonal
coordinate `i`. -/
def column_coordinate_sign_pattern (i : Fin (min m n)) : Fin n → ℝ :=
  fun j ↦ if j.1 = i.1 then -1 else 1

/-- Helper for Theorem 7.7: the row-side coordinate sign pattern defines an orthogonal matrix. -/
lemma rowCoordinateSignFlip_mem_orthogonalGroup
    (i : Fin (min m n)) :
    Matrix.diagonal (row_coordinate_sign_pattern (m := m) (n := n) i) ∈
      Matrix.orthogonalGroup (Fin m) ℝ := by
  let s : Fin m → ℝ := row_coordinate_sign_pattern (m := m) (n := n) i
  have hsq : ∀ j : Fin m, s j * s j = 1 := by
    -- Every row sign is either `-1` or `1`, so its square is `1`.
    intro j
    by_cases hj : j.1 = i.1
    · simp [s, row_coordinate_sign_pattern, hj]
    · simp [s, row_coordinate_sign_pattern, hj]
  refine (Matrix.mem_orthogonalGroup_iff
      (A := Matrix.diagonal s) (R := ℝ)).2 ?_
  calc
    Matrix.diagonal s * (Matrix.diagonal s)ᵀ = Matrix.diagonal s * Matrix.diagonal s := by
      simp
    _ = Matrix.diagonal (fun j ↦ s j * s j) := by
          rw [Matrix.diagonal_mul_diagonal]
    _ = 1 := by
          ext j k
          by_cases hjk : j = k
          · subst hjk
            simp [hsq]
          · simp [hjk]

/-- Helper for Theorem 7.7: the row-side coordinate sign pattern defines an orthogonal matrix. -/
noncomputable def rowCoordinateSignFlip
    (i : Fin (min m n)) : Matrix.orthogonalGroup (Fin m) ℝ :=
  ⟨Matrix.diagonal (row_coordinate_sign_pattern (m := m) (n := n) i),
    rowCoordinateSignFlip_mem_orthogonalGroup (m := m) (n := n) i⟩

/-- Helper for Theorem 7.7: the column-side coordinate sign pattern defines an orthogonal
matrix. -/
lemma columnCoordinateSignFlip_mem_orthogonalGroup
    (i : Fin (min m n)) :
    Matrix.diagonal (column_coordinate_sign_pattern (m := m) (n := n) i) ∈
      Matrix.orthogonalGroup (Fin n) ℝ := by
  let s : Fin n → ℝ := column_coordinate_sign_pattern (m := m) (n := n) i
  have hsq : ∀ j : Fin n, s j * s j = 1 := by
    -- Every column sign is either `-1` or `1`, so its square is `1`.
    intro j
    by_cases hj : j.1 = i.1
    · simp [s, column_coordinate_sign_pattern, hj]
    · simp [s, column_coordinate_sign_pattern, hj]
  refine (Matrix.mem_orthogonalGroup_iff
      (A := Matrix.diagonal s) (R := ℝ)).2 ?_
  calc
    Matrix.diagonal s * (Matrix.diagonal s)ᵀ = Matrix.diagonal s * Matrix.diagonal s := by
      simp
    _ = Matrix.diagonal (fun j ↦ s j * s j) := by
          rw [Matrix.diagonal_mul_diagonal]
    _ = 1 := by
          ext j k
          by_cases hjk : j = k
          · subst hjk
            simp [hsq]
          · simp [hjk]

/-- Helper for Theorem 7.7: the column-side coordinate sign pattern defines an orthogonal
matrix. -/
noncomputable def columnCoordinateSignFlip
    (i : Fin (min m n)) : Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨Matrix.diagonal (column_coordinate_sign_pattern (m := m) (n := n) i),
    columnCoordinateSignFlip_mem_orthogonalGroup (m := m) (n := n) i⟩

/-- Helper for Theorem 7.7: paired row/column coordinate sign flips act entrywise by multiplying
the corresponding row and column signs. -/
lemma pairedCoordinateSignFlip_conjugate_apply
    (i : Fin (min m n)) (W : 𝕄) (j : Fin m) (k : Fin n) :
    (((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) * W *
      ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ)) j k) =
      row_coordinate_sign_pattern (m := m) (n := n) i j * W j k *
        column_coordinate_sign_pattern (m := m) (n := n) i k := by
  -- Both sign-flip matrices are diagonal, so left multiplication rescales rows and right
  -- multiplication rescales columns.
  calc
    (((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) * W *
        ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ)) j k)
      = (((Matrix.diagonal (row_coordinate_sign_pattern (m := m) (n := n) i)) * W) *
          Matrix.diagonal (column_coordinate_sign_pattern (m := m) (n := n) i)) j k := by
            simp [rowCoordinateSignFlip, columnCoordinateSignFlip]
    _ = (((Matrix.diagonal (row_coordinate_sign_pattern (m := m) (n := n) i)) * W) j k) *
          column_coordinate_sign_pattern (m := m) (n := n) i k := by
            rw [Matrix.mul_diagonal]
    _ = row_coordinate_sign_pattern (m := m) (n := n) i j * W j k *
          column_coordinate_sign_pattern (m := m) (n := n) i k := by
            rw [Matrix.diagonal_mul]

/-- Helper for Theorem 7.7: the paired coordinate sign flips fix every rectangular diagonal
matrix. -/
lemma pairedCoordinateSignFlip_fixes_rectangularDiagonal
    (i : Fin (min m n)) (d : Fin (min m n) → ℝ) :
    orthogonalRectangularDiagonalMap
        (rowCoordinateSignFlip (m := m) (n := n) i)
        (columnCoordinateSignFlip (m := m) (n := n) i) d =
      rectangularDiagonal d := by
  ext j k
  by_cases hjk : j.1 = k.1
  · -- On the common diagonal, the paired row and column signs cancel.
    rw [orthogonalRectangularDiagonalMap_apply, pairedCoordinateSignFlip_conjugate_apply]
    by_cases hji : j.1 = i.1
    · have hki : k.1 = i.1 := by
          simpa [hjk] using hji
      simp [rectangularDiagonal_apply, row_coordinate_sign_pattern,
        column_coordinate_sign_pattern, hjk, hki]
    · have hki : ¬ k.1 = i.1 := by
          simpa [hjk] using hji
      simp [rectangularDiagonal_apply, row_coordinate_sign_pattern,
        column_coordinate_sign_pattern, hjk, hki]
  · -- Away from the common diagonal, the rectangular diagonal profile is already zero.
    rw [orthogonalRectangularDiagonalMap_apply, pairedCoordinateSignFlip_conjugate_apply]
    simp [rectangularDiagonal_apply, row_coordinate_sign_pattern,
      column_coordinate_sign_pattern, hjk]

/-- Helper for Theorem 7.7: if a rectangular matrix is fixed by every paired row/column coordinate
sign flip, then it is rectangular diagonal. -/
lemma eq_rectangularDiagonal_of_fixed_by_pairedCoordinateSignFlip
    (W : 𝕄)
    (hfix : ∀ i : Fin (min m n),
      ((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) * W *
        ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ)) = W) :
    ∃ w : Fin (min m n) → ℝ, W = rectangularDiagonal w := by
  let w : Fin (min m n) → ℝ :=
    fun i ↦
      W ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩
        ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_right m n)⟩
  refine ⟨w, ?_⟩
  ext j k
  by_cases hjk : j.1 = k.1
  · let i : Fin (min m n) := ⟨j.1, Nat.lt_min.mpr ⟨j.2, hjk ▸ k.2⟩⟩
    have hj :
        (⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩ : Fin m) = j := by
      ext
      rfl
    have hk :
        (⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_right m n)⟩ : Fin n) = k := by
      ext
      exact hjk
    -- On the common diagonal, the surviving entry is exactly the corresponding profile entry of `w`.
    calc
      W j k
          = W ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩ k := by
              have hleft :
                  W j k = W ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩ k := by
                simpa using congrArg (fun jj : Fin m ↦ W jj k) hj.symm
              exact hleft
      _ = W ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩
            ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_right m n)⟩ := by
              have hright :
                  W ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩ k =
                    W ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩
                      ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_right m n)⟩ := by
                simpa using
                  congrArg
                    (fun kk : Fin n ↦
                      W ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left m n)⟩ kk)
                    hk.symm
              exact hright
      _ = rectangularDiagonal w j k := by
            simp [w, rectangularDiagonal_apply, hjk, i]
  · have hchoice : j.1 < min m n ∨ k.1 < min m n := by
      by_cases hmn : m ≤ n
      · rw [Nat.min_eq_left hmn]
        exact Or.inl j.2
      · have hnm : n ≤ m := Nat.le_of_not_ge hmn
        rw [Nat.min_eq_right hnm]
        exact Or.inr k.2
    have hzero : W j k = 0 := by
      rcases hchoice with hjlt | hklt
      · let i : Fin (min m n) := ⟨j.1, hjlt⟩
        have hentry := congrArg (fun A : 𝕄 ↦ A j k) (hfix i)
        have hk_ne : ¬ k.1 = j.1 := by
          simpa [eq_comm] using hjk
        have hneg : -W j k = W j k := by
          simpa [i, pairedCoordinateSignFlip_conjugate_apply, row_coordinate_sign_pattern,
            column_coordinate_sign_pattern, hk_ne] using hentry
        linarith
      · let i : Fin (min m n) := ⟨k.1, hklt⟩
        have hentry := congrArg (fun A : 𝕄 ↦ A j k) (hfix i)
        have hj_ne : ¬ j.1 = k.1 := hjk
        have hneg : -W j k = W j k := by
          simpa [i, pairedCoordinateSignFlip_conjugate_apply, row_coordinate_sign_pattern,
            column_coordinate_sign_pattern, hj_ne] using hentry
        linarith
    -- Away from the common diagonal, the fixed-point condition forces the entry to vanish.
    simp [rectangularDiagonal_apply, hjk, hzero]

/-- Helper for Theorem 7.7: every proximal point at a rectangular diagonal base matrix is itself a
rectangular diagonal matrix. -/
lemma rectangular_basis_prox_is_rectangularDiagonal
    (f : (Fin (min m n) → ℝ) → EReal)
    (hf_symm : Function.IsAbsolutelyPermutationSymmetric f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (d : Fin (min m n) → ℝ) {W : 𝕄}
    (hW : W ∈ prox[f ∘ singular_value_function] (rectangularDiagonal d)) :
    ∃ w : Fin (min m n) → ℝ, W = rectangularDiagonal w := by
  have hclosedconv :=
    matrixSpectralLift_proper_closed_convex f hf_symm hf_closed hf_convex
  rcases prox_eq_singleton_of_proper_closed_convex
      (f ∘ singular_value_function) hclosedconv.1 hclosedconv.2.1 hclosedconv.2.2
      (rectangularDiagonal d) with ⟨W0, hsingleton⟩
  have hWeq : W = W0 := by
    have hmem := hW
    rw [hsingleton] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have hfix :
      ∀ i : Fin (min m n),
        ((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) * W *
          ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ)) = W := by
    intro i
    have hrow :
        ((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ)ᵀ) *
            (rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).1 (rowCoordinateSignFlip (m := m) (n := n) i).2
    have hcol :
        ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ) *
            (columnCoordinateSignFlip (m := m) (n := n) i : Mₙ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1
        (columnCoordinateSignFlip (m := m) (n := n) i).2
    have hflip_mem :
        ((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) * W *
          ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ)) ∈
          prox[f ∘ singular_value_function] (rectangularDiagonal d) := by
      have hflip_mem' :
          ((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) * W *
            ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ)) ∈
            prox[f ∘ singular_value_function]
              (orthogonalRectangularDiagonalMap
                (rowCoordinateSignFlip (m := m) (n := n) i)
                (columnCoordinateSignFlip (m := m) (n := n) i) d) := by
        refine (mem_prox_matrixSpectralLift_orthogonal_rectangular_iff f
            (rowCoordinateSignFlip (m := m) (n := n) i)
            (columnCoordinateSignFlip (m := m) (n := n) i) d _).2 ?_
        have hback :
            ((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ)ᵀ) *
                (((rowCoordinateSignFlip (m := m) (n := n) i : Mₘ) * W *
                  ((columnCoordinateSignFlip (m := m) (n := n) i : Mₙ)ᵀ))) *
                (columnCoordinateSignFlip (m := m) (n := n) i : Mₙ) = W := by
          let R : Mₘ := rowCoordinateSignFlip (m := m) (n := n) i
          let C : Mₙ := columnCoordinateSignFlip (m := m) (n := n) i
          calc
            Rᵀ * (R * W * Cᵀ) * C = (Rᵀ * (R * W * Cᵀ)) * C := by
              rfl
            _ = Rᵀ * ((R * W * Cᵀ) * C) := by
                  simpa using Matrix.mul_assoc Rᵀ (R * W * Cᵀ) C
            _ = Rᵀ * (R * W * (Cᵀ * C)) := by
                  simpa [mul_assoc] using
                    congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ Rᵀ * M)
                      (Matrix.mul_assoc (R * W) Cᵀ C)
            _ = Rᵀ * (R * (W * (Cᵀ * C))) := by
                  simpa [mul_assoc] using
                    congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ Rᵀ * M)
                      (Matrix.mul_assoc R W (Cᵀ * C))
            _ = (Rᵀ * R) * (W * (Cᵀ * C)) := by
                  exact (Matrix.mul_assoc Rᵀ R (W * (Cᵀ * C))).symm
            _ = (Rᵀ * R) * W * (Cᵀ * C) := by
                  exact (Matrix.mul_assoc (Rᵀ * R) W (Cᵀ * C)).symm
            _ = W := by
                  simp [hrow, hcol, R, C]
        simpa [hback] using hW
      rw [pairedCoordinateSignFlip_fixes_rectangularDiagonal i d] at hflip_mem'
      exact hflip_mem'
    have hflip_mem_singleton := hflip_mem
    rw [hsingleton] at hflip_mem_singleton
    exact (Set.mem_singleton_iff.mp hflip_mem_singleton).trans hWeq.symm
  exact eq_rectangularDiagonal_of_fixed_by_pairedCoordinateSignFlip W hfix

/-- Helper for Theorem 7.7: a rectangular diagonal proximal point in the matrix problem induces
the corresponding Euclidean proximal point of the vector profile. -/
lemma rectangularDiagonal_mem_prox_euclidean_of_mem_prox_matrixSpectralLift
    (f : (Fin (min m n) → ℝ) → EReal)
    (hf_symm : Function.IsAbsolutelyPermutationSymmetric f)
    (d w : Fin (min m n) → ℝ)
    (hdiag :
      rectangularDiagonal w ∈ prox[f ∘ singular_value_function] (rectangularDiagonal d)) :
    WithLp.toLp (p := (2 : ENNReal)) w ∈
      prox[fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp]
        (WithLp.toLp (p := (2 : ENNReal)) d) := by
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hdiag
  intro y
  have hcmp := hdiag (rectangularDiagonal y.ofLp)
  have hw_pull : (f ∘ singular_value_function) (rectangularDiagonal w) = f w := by
    simpa [theorem7_7_rectangularDiagonal_eq_profile, Function.comp] using
      absolutely_symmetric_rectangular_diagonal_pullback_eq f hf_symm w
  have hy_pull : (f ∘ singular_value_function) (rectangularDiagonal y.ofLp) = f y.ofLp := by
    simpa [theorem7_7_rectangularDiagonal_eq_profile, Function.comp] using
      absolutely_symmetric_rectangular_diagonal_pullback_eq f hf_symm y.ofLp
  -- Restrict the ambient minimizing inequality to rectangular diagonal competitors and rewrite the
  -- spectral and quadratic terms through the diagonal model.
  rw [proximal_objective_apply, proximal_objective_apply, hw_pull, hy_pull,
    theorem7_7_frobenius_norm_rectangularDiagonal_sub_eq w d,
    theorem7_7_frobenius_norm_rectangularDiagonal_sub_eq y.ofLp d] at hcmp
  simpa [proximal_objective_apply] using hcmp

-- Proof sketch: conjugate the proximal objective for `f ∘ singular_value_function` by the fixed
-- left and right orthogonal factors `U` and `V`. Absolute permutation symmetry makes the spectral
-- term depend only on the singular-value vector, while Frobenius-norm invariance turns the matrix
-- minimization problem into the vector-side proximal problem at `singular_value_function X`.
/-- Theorem 7.7: if `f : ℝ^(min(m,n)) → (-∞, ∞]` is absolutely permutation symmetric, closed, and
convex, and if
`X = U * rectangularDiagonal (singular_value_function X) * Vᵀ`, then the proximal set of the
matrix spectral lift `f ∘ singular_value_function` at `X` is the orthogonal image of the Euclidean
vector proximal set of `f` at `σ(X) = singular_value_function X`. The vector-side proximal problem
is stated on `EuclideanSpace ℝ (Fin (min m n))`, matching the Frobenius geometry of rectangular
diagonal matrices. -/
theorem prox_matrixSpectralLift_eq_image_orthogonalRectangularDiagonalMap
    (f : (Fin (min m n) → ℝ) → EReal) (hf_symm : Function.IsAbsolutelyPermutationSymmetric f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (X : 𝕄) (U : Matrix.orthogonalGroup (Fin m) ℝ)
    (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (hsvd : X = orthogonalRectangularDiagonalMap U V (singular_value_function X)) :
    prox[f ∘ singular_value_function] X =
      orthogonalRectangularDiagonalMapEuclidean U V ''
        prox[fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp]
          (WithLp.toLp (p := (2 : ENNReal)) (singular_value_function X)) := by
  let σ : Fin (min m n) → ℝ := singular_value_function X
  let σLp : EuclideanSpace ℝ (Fin (min m n)) := WithLp.toLp (p := (2 : ENNReal)) σ
  have hclosedconv :=
    matrixSpectralLift_proper_closed_convex f hf_symm hf_closed hf_convex
  rcases prox_eq_singleton_of_proper_closed_convex
      (f ∘ singular_value_function) hclosedconv.1 hclosedconv.2.1 hclosedconv.2.2 X with
      ⟨Y0, hsingleton⟩
  have hpullback := euclidean_pullback_proper_closed_convex f hf_symm hf_closed hf_convex
  rcases prox_eq_singleton_of_proper_closed_convex
      (fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp)
      hpullback.1 hpullback.2.1 hpullback.2.2 σLp with ⟨x0, hvecsingleton⟩
  have hY0_mem : Y0 ∈ prox[f ∘ singular_value_function] X := by
    simp [hsingleton]
  have hdiag_mem :
      ((U : Mₘ)ᵀ * Y0 * (V : Mₙ)) ∈
        prox[f ∘ singular_value_function] (rectangularDiagonal σ) := by
    have hbase :
        Y0 ∈ prox[f ∘ singular_value_function] (orthogonalRectangularDiagonalMap U V σ) := by
      change Y0 ∈ prox[f ∘ singular_value_function]
        (orthogonalRectangularDiagonalMap U V (singular_value_function X))
      exact hsvd ▸ hY0_mem
    exact (mem_prox_matrixSpectralLift_orthogonal_rectangular_iff f U V σ Y0).1 hbase
  rcases rectangular_basis_prox_is_rectangularDiagonal f hf_symm hf_closed hf_convex σ hdiag_mem with
    ⟨w, hwdiag⟩
  have hdiag_mem' :
      rectangularDiagonal w ∈ prox[f ∘ singular_value_function] (rectangularDiagonal σ) := by
    simpa [hwdiag] using hdiag_mem
  have hw_euclidean :
      WithLp.toLp (p := (2 : ENNReal)) w ∈
        prox[fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp] σLp :=
    rectangularDiagonal_mem_prox_euclidean_of_mem_prox_matrixSpectralLift f hf_symm σ w hdiag_mem'
  have hw_eq_x0 : WithLp.toLp (p := (2 : ENNReal)) w = x0 := by
    have hmem : WithLp.toLp (p := (2 : ENNReal)) w ∈ ({x0} : Set (EuclideanSpace ℝ (Fin (min m n)))) := by
      simpa [hvecsingleton, σLp] using hw_euclidean
    simpa using hmem
  have hx0_ofLp : x0.ofLp = w := by
    simpa using (congrArg (fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ y.ofLp) hw_eq_x0).symm
  have hUUt : (U : Mₘ) * (U : Mₘ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (U : Mₘ)) (R := ℝ)).1 U.2
  have hVUt : (V : Mₙ) * (V : Mₙ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (A := (V : Mₙ)) (R := ℝ)).1 V.2
  have hY0_eq :
      Y0 = orthogonalRectangularDiagonalMapEuclidean U V x0 := by
    -- Reinsert the left/right orthogonal factors around the transported diagonal proximal point.
    calc
      Y0 = (((U : Mₘ) * (U : Mₘ)ᵀ) * Y0) * ((V : Mₙ) * (V : Mₙ)ᵀ) := by
            simp [hUUt, hVUt]
      _ = ((((U : Mₘ) * (U : Mₘ)ᵀ) * Y0) * (V : Mₙ)) * (V : Mₙ)ᵀ := by
            exact (Matrix.mul_assoc (((U : Mₘ) * (U : Mₘ)ᵀ) * Y0) (V : Mₙ) ((V : Mₙ)ᵀ)).symm
      _ = (((U : Mₘ) * ((U : Mₘ)ᵀ * Y0)) * (V : Mₙ)) * (V : Mₙ)ᵀ := by
            exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ M * (V : Mₙ) * (V : Mₙ)ᵀ)
              (Matrix.mul_assoc (U : Mₘ) (U : Mₘ)ᵀ Y0)
      _ = ((U : Mₘ) * (((U : Mₘ)ᵀ * Y0) * (V : Mₙ))) * (V : Mₙ)ᵀ := by
            exact congrArg (fun M : Matrix (Fin m) (Fin n) ℝ ↦ M * (V : Mₙ)ᵀ)
              (Matrix.mul_assoc (U : Mₘ) ((U : Mₘ)ᵀ * Y0) (V : Mₙ))
      _ = (U : Mₘ) * ((((U : Mₘ)ᵀ * Y0) * (V : Mₙ)) * (V : Mₙ)ᵀ) := by
            exact Matrix.mul_assoc (U : Mₘ) (((U : Mₘ)ᵀ * Y0) * (V : Mₙ)) ((V : Mₙ)ᵀ)
      _ = (U : Mₘ) * (((U : Mₘ)ᵀ * Y0 * (V : Mₙ)) * (V : Mₙ)ᵀ) := by
            rfl
      _ = (U : Mₘ) * rectangularDiagonal w * (V : Mₙ)ᵀ := by
            rw [hwdiag]
            exact (Matrix.mul_assoc (U : Mₘ) (rectangularDiagonal w) ((V : Mₙ)ᵀ)).symm
      _ = orthogonalRectangularDiagonalMapEuclidean U V x0 := by
            simp [orthogonalRectangularDiagonalMapEuclidean, orthogonalRectangularDiagonalMap_apply,
              hx0_ofLp]
  -- Both the matrix-side and vector-side proximal sets are now identified as singletons.
  calc
    prox[f ∘ singular_value_function] X = {Y0} := hsingleton
    _ = {orthogonalRectangularDiagonalMapEuclidean U V x0} := by rw [hY0_eq]
    _ = orthogonalRectangularDiagonalMapEuclidean U V ''
          prox[fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp] σLp := by
            rw [hvecsingleton, Set.image_singleton]

-- Proof sketch: apply
-- `prox_matrixSpectralLift_eq_image_orthogonalRectangularDiagonalMap` and rewrite the image of
-- the singleton set `{x}` under `orthogonalRectangularDiagonalMapEuclidean U V`.
/-- If the Euclidean vector proximal set of `f` at the singular-value vector of `X` is the singleton
`{x}`, then the proximal set of the matrix spectral lift at `X` is the singleton
`{U * rectangularDiagonal x.ofLp * Vᵀ}`. -/
theorem prox_matrixSpectralLift_eq_singleton_orthogonalRectangularDiagonalMap
    {f : (Fin (min m n) → ℝ) → EReal} (hf_symm : Function.IsAbsolutelyPermutationSymmetric f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    {X : 𝕄} {U : Matrix.orthogonalGroup (Fin m) ℝ}
    {V : Matrix.orthogonalGroup (Fin n) ℝ}
    (hsvd : X = orthogonalRectangularDiagonalMap U V (singular_value_function X))
    {x : EuclideanSpace ℝ (Fin (min m n))}
    (hprox : prox[fun y : EuclideanSpace ℝ (Fin (min m n)) ↦ f y.ofLp]
        (WithLp.toLp (p := (2 : ENNReal)) (singular_value_function X)) = {x}) :
    prox[f ∘ singular_value_function] X = {orthogonalRectangularDiagonalMapEuclidean U V x} := by
  -- Rewrite the matrix proximal set via the main image formula and collapse the singleton image.
  rw [prox_matrixSpectralLift_eq_image_orthogonalRectangularDiagonalMap f hf_symm hf_closed
    hf_convex X U V hsvd, hprox, Set.image_singleton]

end
