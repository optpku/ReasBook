/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_1
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Matrix.Spectrum

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (ofLp toLp)
open scoped MatrixOrder RealInnerProductSpace

noncomputable section

section

variable {n : ℕ}

local notation "X" => Fin n → ℝ

/- Proposition 5.11 is `source-facing`: it specializes the Chapter 4 quadratic owner
`quadratic_affine_function_on_lp p A b c` to the canonical `ℓ₂` model of `ℝ^n` by taking
`p = 2`, and studies strong convexity for a symmetric quadratic form. The canonical matrix-side
owner abstractions are `Matrix.PosSemidef`, `Matrix.PosDef`, and the ordered Hermitian
spectrum. -/

-- Semantic recall: mathlib exposes `StrongConvexOn` and `strongConvexOn_iff_convex`; the
-- `ℓ₂` quadratic owner itself is already Proposition 5.1's specialization
-- `quadratic_affine_function_on_lp (2 : ENNReal)`.

recall quadratic_affine_function_on_lp

-- Semantic recall: local precedent `hessian_max_eigenvalue` and mathlib's
-- `Matrix.IsHermitian.eigenvalues₀_antitone` use the canonical descending Hermitian spectrum, so
-- index `0` is `λ_max` and, when `n > 0`, index `⊤` is `λ_min`.
/-- The smallest eigenvalue of a real symmetric `n × n` matrix, using the canonical descending
Hermitian spectrum endpoint `⊤` when `n > 0`. -/
noncomputable def symmetric_matrix_min_eigenvalue (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hn : 0 < n) : ℝ :=
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let hHerm : A.IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  hHerm.eigenvalues₀ ⊤

/-- Companion bridge: a positive-definite real matrix is symmetric, so the source-facing
`symmetric_matrix_min_eigenvalue` applies without an extra symmetry hypothesis. -/
theorem Matrix.PosDef.isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) : A.IsSymm := by
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian

/-- Helper for Proposition 5.11: a real symmetric matrix is Hermitian. -/
private theorem matrixIsHermitianOfIsSymmReal
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA

/-- Helper for Proposition 5.11: subtracting `(σ / 2) * ‖x‖²` from the `ℓ₂` quadratic replaces
`A` by the shifted matrix `A - σ I`. -/
private theorem quadraticAffineFunctionOnL2SubHalfSigmaNormSq
    (A : Matrix (Fin n) (Fin n) ℝ) (b : X) (c σ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    quadratic_affine_function_on_lp (2 : ENNReal) A b c x - σ / 2 * ‖x‖ ^ (2 : ℕ) =
      quadratic_affine_function_on_lp (2 : ENNReal) (A - σ • 1) b c x := by
  -- Rewrite both quadratic owners in coordinates and isolate the `σ ‖x‖² / 2` correction.
  have hnormSq : ‖x‖ ^ (2 : ℕ) = dotProduct x.ofLp x.ofLp := by
    simpa [dotProduct, pow_two] using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin n ↦ ℝ) x)
  rw [quadratic_affine_function_on_lp_apply, quadratic_affine_function_apply]
  rw [quadratic_affine_function_on_lp_apply, quadratic_affine_function_apply]
  rw [hnormSq, Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, dotProduct_sub]
  have hsmul : dotProduct x.ofLp (σ • x.ofLp) = σ * dotProduct x.ofLp x.ofLp := by
    rw [dotProduct_smul, smul_eq_mul]
  rw [hsmul]
  ring_nf

/-- Helper for Proposition 5.11: the weighted Jensen gap of the Euclidean quadratic owner is the
quadratic form of `A` evaluated on `x - y`. -/
private theorem quadraticAffineFunctionOnL2Gap
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (b : X) (c α β : ℝ)
    (hab : α + β = 1) (x y : EuclideanSpace ℝ (Fin n)) :
    α * quadratic_affine_function_on_lp (2 : ENNReal) A b c x +
        β * quadratic_affine_function_on_lp (2 : ENNReal) A b c y -
        quadratic_affine_function_on_lp (2 : ENNReal) A b c (α • x + β • y) =
      (α * β / 2) * dotProduct (x - y).ofLp (A *ᵥ (x - y).ofLp) := by
  have hHerm : A.IsHermitian := matrixIsHermitianOfIsSymmReal hA
  have hswap : dotProduct x.ofLp (A *ᵥ y.ofLp) = dotProduct y.ofLp (A *ᵥ x.ofLp) := by
    calc
      dotProduct x.ofLp (A *ᵥ y.ofLp) = dotProduct (A *ᵥ x.ofLp) y.ofLp := by
        rw [dotProduct_mulVec_swap_of_isHermitian A hHerm x.ofLp y.ofLp]
      _ = dotProduct y.ofLp (A *ᵥ x.ofLp) := by
        rw [dotProduct_comm]
  obtain rfl := eq_sub_of_add_eq hab
  -- Expand the three quadratic values once, then use symmetry to merge the mixed terms.
  rw [quadratic_affine_function_on_lp_apply, quadratic_affine_function_apply]
  rw [quadratic_affine_function_on_lp_apply, quadratic_affine_function_apply]
  rw [quadratic_affine_function_on_lp_apply, quadratic_affine_function_apply]
  simp [WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_eq_mul]
  ring_nf
  rw [Matrix.mulVec_sub, dotProduct_sub, dotProduct_sub]
  rw [hswap]
  ring_nf

/-- Helper for Proposition 5.11: the Euclidean quadratic owner is convex exactly when its
Hessian matrix is positive semidefinite. -/
private theorem quadraticAffineFunctionOnL2ConvexOn_iff_posSemidef
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (b : X) (c : ℝ) :
    ConvexOn ℝ Set.univ (quadratic_affine_function_on_lp (2 : ENNReal) A b c) ↔ A.PosSemidef := by
  constructor
  · intro hconv
    have hHerm : A.IsHermitian := matrixIsHermitianOfIsSymmReal hA
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
    intro d
    let x : EuclideanSpace ℝ (Fin n) := toLp 2 d
    have hmid :=
      hconv.2 (show x ∈ Set.univ by simp) (show (0 : EuclideanSpace ℝ (Fin n)) ∈ Set.univ by simp)
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by ring)
    have hgap :=
      quadraticAffineFunctionOnL2Gap A hA b c (1 / 2) (1 / 2) (by ring) x 0
    have hgapNonneg :
        0 ≤ (1 / 2 : ℝ) * quadratic_affine_function_on_lp (2 : ENNReal) A b c x +
            (1 / 2 : ℝ) * quadratic_affine_function_on_lp (2 : ENNReal) A b c 0 -
            quadratic_affine_function_on_lp (2 : ENNReal) A b c
              ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (0 : EuclideanSpace ℝ (Fin n))) := by
      simpa [smul_eq_mul] using sub_nonneg.mpr hmid
    have hdotNonneg :
        0 ≤ (1 / 8 : ℝ) * dotProduct d (A *ᵥ d) := by
      rw [hgap] at hgapNonneg
      simpa [x] using hgapNonneg
    have hmulNonneg : 0 ≤ (8 : ℝ) * ((1 / 8 : ℝ) * dotProduct d (A *ᵥ d)) := by
      exact mul_nonneg (by norm_num) hdotNonneg
    ring_nf at hmulNonneg
    simpa using hmulNonneg
  · intro hApsd
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy α β hα hβ hab
    have hgap := quadraticAffineFunctionOnL2Gap A hA b c α β hab x y
    have hquadNonneg : 0 ≤ dotProduct (x - y).ofLp (A *ᵥ (x - y).ofLp) := by
      simpa using hApsd.dotProduct_mulVec_nonneg ((x - y).ofLp)
    have hscaledNonneg :
        0 ≤ (α * β / 2) * dotProduct (x - y).ofLp (A *ᵥ (x - y).ofLp) := by
      have hcoeff : 0 ≤ α * β / 2 := by positivity
      exact mul_nonneg hcoeff hquadNonneg
    have hdiff :
        0 ≤ α * quadratic_affine_function_on_lp (2 : ENNReal) A b c x +
            β * quadratic_affine_function_on_lp (2 : ENNReal) A b c y -
            quadratic_affine_function_on_lp (2 : ENNReal) A b c (α • x + β • y) := by
      rwa [hgap]
    have hineq :
        quadratic_affine_function_on_lp (2 : ENNReal) A b c (α • x + β • y) ≤
          α * quadratic_affine_function_on_lp (2 : ENNReal) A b c x +
            β * quadratic_affine_function_on_lp (2 : ENNReal) A b c y :=
      sub_nonneg.mp hdiff
    simpa [smul_eq_mul] using hineq

/-- Helper for Proposition 5.11: under matrix order, `σ I ≤ A` is equivalent to the smallest
ordered Hermitian eigenvalue of `A` being at least `σ`. -/
private theorem scalarMatrixLe_iff_le_symmetricMatrixMinEigenvalue
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hn : 0 < n) (σ : ℝ) :
    σ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A ↔ σ ≤ symmetric_matrix_min_eigenvalue A hA hn := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let hHerm : A.IsHermitian := matrixIsHermitianOfIsSymmReal hA
  constructor
  · intro hle
    have hspec : ∀ x ∈ spectrum ℝ A, σ ≤ x := by
      exact (algebraMap_le_iff_le_spectrum (a := A)).1 (by
        simpa [Algebra.algebraMap_eq_smul_one] using hle)
    have hall : ∀ i : Fin n, σ ≤ hHerm.eigenvalues i := by
      intro i
      exact hspec _ (hHerm.eigenvalues_mem_spectrum_real i)
    have hall₀ : ∀ j : Fin (Fintype.card (Fin n)), σ ≤ hHerm.eigenvalues₀ j := by
      intro j
      let i : Fin n :=
        Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))) j
      simpa [Matrix.IsHermitian.eigenvalues, i] using hall i
    -- The source-facing `λ_min` is the `⊤`-endpoint of the descending eigenvalue chain.
    simpa [symmetric_matrix_min_eigenvalue, hHerm] using hall₀ ⊤
  · intro hσ
    have hmin_le : ∀ i : Fin n, symmetric_matrix_min_eigenvalue A hA hn ≤ hHerm.eigenvalues i := by
      intro i
      let j : Fin (Fintype.card (Fin n)) :=
        (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm i
      have hanti : hHerm.eigenvalues₀ ⊤ ≤ hHerm.eigenvalues₀ j :=
        hHerm.eigenvalues₀_antitone (show j ≤ ⊤ from le_top)
      simpa [symmetric_matrix_min_eigenvalue, hHerm, Matrix.IsHermitian.eigenvalues, j] using hanti
    have hspec : ∀ x ∈ spectrum ℝ A, σ ≤ x := by
      intro x hx
      rw [hHerm.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hσ.trans (hmin_le i)
    have hle : algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) σ ≤ A :=
      (algebraMap_le_iff_le_spectrum (a := A)).2 hspec
    simpa [Algebra.algebraMap_eq_smul_one] using hle

/-- Helper for Proposition 5.11: on a subsingleton real inner product space, every real-valued
function is strongly convex with any modulus because every segment is constant. -/
private theorem strongConvexOn_univ_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Subsingleton E]
    (σ : ℝ) (f : E → ℝ) : StrongConvexOn Set.univ σ f := by
  refine (strongConvexOn_iff_convex (E := E) (s := Set.univ) (m := σ) (f := f)).2 ?_
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : x = y := Subsingleton.elim x y
  subst hxy
  have hsmul : a • x + b • x = x := by
    calc
      a • x + b • x = (a + b) • x := by rw [add_smul]
      _ = x := by simp [hab]
  rw [hsmul]
  have hcoeff :
      a * (f x - σ / 2 * ‖x‖ ^ (2 : ℕ)) + b * (f x - σ / 2 * ‖x‖ ^ (2 : ℕ)) =
        f x - σ / 2 * ‖x‖ ^ (2 : ℕ) := by
    rw [← add_mul, hab, one_mul]
  simp [hcoeff]

/-- Helper for Proposition 5.11: in dimension `0`, positive-modulus strong convexity and matrix
positive definiteness are both vacuous. -/
private theorem subsingletonQuadraticStrongConvexExists_iff_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (b : X) (c : ℝ) (hn : ¬ 0 < n) :
    (∃ σ : ℝ, 0 < σ ∧
      StrongConvexOn Set.univ σ (quadratic_affine_function_on_lp (2 : ENNReal) A b c)) ↔
      A.PosDef := by
  have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
  subst hzero
  constructor
  · intro _
    refine ⟨?_, ?_⟩
    · change Aᴴ = A
      exact Subsingleton.elim _ _
    · intro x hx
      exact False.elim (hx (Subsingleton.elim x 0))
  · intro _
    refine ⟨1, zero_lt_one, ?_⟩
    -- Every function on the zero-dimensional Euclidean space is strongly convex.
    simpa using
      (strongConvexOn_univ_of_subsingleton (E := EuclideanSpace ℝ (Fin 0)) 1
        (quadratic_affine_function_on_lp (2 : ENNReal) A b c))

-- Proof sketch: apply the inner-product-space characterization
-- `strongConvexOn_iff_convex` to `quadratic_affine_function_on_lp (2 : ENNReal) A b c`, expand
-- the quadratic correction, and identify convexity of the remaining quadratic form with positive
-- semidefiniteness of `A - σ • 1`.
/-- Proposition 5.11 (1): for the quadratic function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on `ℝ^n`
equipped with the `ℓ₂` norm, strong convexity with parameter `σ` is equivalent to the shifted
symmetric matrix `A - σ I` being positive semidefinite. -/
theorem quadratic_affine_function_on_l2_strongConvexOn_iff_posSemidef_shift
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (b : X) (c σ : ℝ) :
    StrongConvexOn Set.univ σ (quadratic_affine_function_on_lp (2 : ENNReal) A b c) ↔
      (A - σ • 1).PosSemidef := by
  -- Route correction: first rewrite strong convexity as convexity of the shifted quadratic owner,
  -- then use the Jensen-gap characterization for convex quadratics.
  rw [strongConvexOn_iff_convex]
  have hShiftSymm : (A - σ • 1).IsSymm := by
    simpa using hA.sub ((Matrix.isSymm_one : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm).smul σ)
  constructor
  · intro hconv
    have hconvShift :
        ConvexOn ℝ Set.univ
          (quadratic_affine_function_on_lp (2 : ENNReal) (A - σ • 1) b c) :=
      hconv.congr fun x hx ↦ quadraticAffineFunctionOnL2SubHalfSigmaNormSq A b c σ x
    exact (quadraticAffineFunctionOnL2ConvexOn_iff_posSemidef (A - σ • 1) hShiftSymm b c).1
      hconvShift
  · intro hpsd
    have hconvShift :
        ConvexOn ℝ Set.univ
          (quadratic_affine_function_on_lp (2 : ENNReal) (A - σ • 1) b c) :=
      (quadraticAffineFunctionOnL2ConvexOn_iff_posSemidef (A - σ • 1) hShiftSymm b c).2 hpsd
    exact hconvShift.congr fun x hx ↦ (quadraticAffineFunctionOnL2SubHalfSigmaNormSq A b c σ x).symm

-- Proof sketch: combine the shifted-matrix criterion above with the Hermitian spectral theorem:
-- for a real symmetric matrix, `A - σ • 1` is positive semidefinite iff all entries of the
-- canonical descending spectrum `eigenvalues₀` are nonnegative, equivalently iff its `⊤`-endpoint
-- `λ_min(A)` is at least `σ`.
/-- Proposition 5.11 (2): for a real symmetric quadratic form, the strong-convexity modulus `σ`
is admissible exactly when it does not exceed the smallest eigenvalue of the Hessian matrix `A`. -/
theorem quadratic_affine_function_on_l2_strongConvexOn_iff_le_min_eigenvalue
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hn : 0 < n) (b : X) (c σ : ℝ) :
    StrongConvexOn Set.univ σ (quadratic_affine_function_on_lp (2 : ENNReal) A b c) ↔
      σ ≤ symmetric_matrix_min_eigenvalue A hA hn := by
  -- Replace the shifted PSD condition by the matrix-order inequality `σ I ≤ A`, then read that
  -- inequality on the ordered Hermitian spectrum.
  rw [quadratic_affine_function_on_l2_strongConvexOn_iff_posSemidef_shift A hA b c σ]
  have horder :
      (A - σ • 1).PosSemidef ↔ σ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A := by
    exact (Matrix.le_iff (A := σ • (1 : Matrix (Fin n) (Fin n) ℝ)) (B := A)).symm
  rw [horder]
  exact scalarMatrixLe_iff_le_symmetricMatrixMinEigenvalue A hA hn σ

-- Proof sketch: translate existence of a positive strong-convexity modulus into existence of
-- `σ > 0` with `(A - σ • 1).PosSemidef`, then use the Hermitian eigenvalue criterion to identify
-- this with positivity of every eigenvalue of `A`, i.e. positive definiteness.
/-- Proposition 5.11 (3): the quadratic function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on `ℝ^n` is
strongly convex for some positive modulus if and only if its symmetric Hessian matrix `A` is
positive definite. -/
theorem quadratic_affine_function_on_l2_exists_pos_strongConvexOn_iff_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (b : X) (c : ℝ) :
    (∃ σ : ℝ, 0 < σ ∧
      StrongConvexOn Set.univ σ (quadratic_affine_function_on_lp (2 : ENNReal) A b c)) ↔
      A.PosDef := by
  by_cases hn : 0 < n
  · have horderPos :
        (∃ σ : ℝ, 0 < σ ∧ σ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A) ↔ A.PosDef := by
      -- Positive scalar lower bounds are exactly matrix strict positivity, hence positive
      -- definiteness for Hermitian real matrices.
      simpa [Algebra.algebraMap_eq_smul_one] using
        (letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
         ((CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin n) (Fin n) ℝ) (a := A)).trans
          ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (a := A)).symm.trans
            Matrix.isStrictlyPositive_iff_posDef)))
    constructor
    · rintro ⟨σ, hσ, hstrong⟩
      have hshift :
          (A - σ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
        (quadratic_affine_function_on_l2_strongConvexOn_iff_posSemidef_shift A hA b c σ).1 hstrong
      have hle : σ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A := by
        simpa using (Matrix.le_iff (A := σ • (1 : Matrix (Fin n) (Fin n) ℝ)) (B := A)).2 hshift
      exact horderPos.1 ⟨σ, hσ, hle⟩
    · intro hApos
      rcases horderPos.2 hApos with ⟨σ, hσ, hle⟩
      have hshift :
          (A - σ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
        simpa using (Matrix.le_iff (A := σ • (1 : Matrix (Fin n) (Fin n) ℝ)) (B := A)).1 hle
      exact
        ⟨σ, hσ,
          (quadratic_affine_function_on_l2_strongConvexOn_iff_posSemidef_shift A hA b c σ).2
            hshift⟩
  · exact subsingletonQuadraticStrongConvexExists_iff_posDef A b c hn

-- Proof sketch: use the previous eigenvalue characterization to show that the admissible positive
-- moduli are exactly the interval `(0, λ_min(A)]`; positive definiteness ensures this interval is
-- nonempty and that its greatest element is `λ_min(A)`.
/-- Proposition 5.11 (4): if the quadratic Hessian matrix `A` is positive definite, then its
smallest eigenvalue is the largest positive strong-convexity parameter of the associated quadratic
function on `ℝ^n` with the `ℓ₂` norm. -/
theorem symmetric_matrix_min_eigenvalue_isGreatest_strongConvexity_parameter
    (A : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n) (hApos : A.PosDef) (b : X) (c : ℝ) :
    IsGreatest
      {σ : ℝ | 0 < σ ∧
        StrongConvexOn Set.univ σ (quadratic_affine_function_on_lp (2 : ENNReal) A b c)}
      (symmetric_matrix_min_eigenvalue A hApos.isSymm hn) := by
  refine ⟨?_, ?_⟩
  · have hstrongAtMin :
        StrongConvexOn Set.univ (symmetric_matrix_min_eigenvalue A hApos.isSymm hn)
          (quadratic_affine_function_on_lp (2 : ENNReal) A b c) :=
      (quadratic_affine_function_on_l2_strongConvexOn_iff_le_min_eigenvalue
        A hApos.isSymm hn b c (symmetric_matrix_min_eigenvalue A hApos.isSymm hn)).2 le_rfl
    have hminPos :
        0 < symmetric_matrix_min_eigenvalue A hApos.isSymm hn := by
      rcases
          (quadratic_affine_function_on_l2_exists_pos_strongConvexOn_iff_posDef
            A hApos.isSymm b c).2 hApos with
        ⟨σ, hσ, hstrongσ⟩
      have hσle :
          σ ≤ symmetric_matrix_min_eigenvalue A hApos.isSymm hn :=
        (quadratic_affine_function_on_l2_strongConvexOn_iff_le_min_eigenvalue
          A hApos.isSymm hn b c σ).1 hstrongσ
      exact lt_of_lt_of_le hσ hσle
    exact ⟨hminPos, hstrongAtMin⟩
  · intro σ hσ
    -- Every admissible modulus is bounded above by `λ_min(A)` by Proposition 5.11 (2).
    exact
      (quadratic_affine_function_on_l2_strongConvexOn_iff_le_min_eigenvalue
        A hApos.isSymm hn b c σ).1 hσ.2

end
