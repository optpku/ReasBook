module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.WithLp
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import ReasLib.Geometry.Euclidean.Plane.Rotation

public section

noncomputable section

namespace RealSymmetric2

open scoped Matrix Topology

/-- The real symmetric matrix with diagonal entries `a`, `d` and off-diagonal entry `b`. -/
def matrix (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, b; b, d]

/-- The entries of `matrix a b d` are the displayed symmetric matrix. -/
theorem matrix_eq (a b d : ℝ) :
    matrix a b d = !![a, b; b, d] := by
  rfl

/-- The spectral gap `√((d - a) ^ 2 + 4 * b ^ 2)` of a real symmetric `2 × 2` matrix. -/
def gap (a b d : ℝ) : ℝ :=
  √((d - a) ^ 2 + 4 * b ^ 2)

/-- Evaluation formula for the explicit spectral gap. -/
theorem gap_apply (a b d : ℝ) :
    gap a b d = √((d - a) ^ 2 + 4 * b ^ 2) := by
  rfl

/-- The lower eigenvalue in the explicit quadratic formula. -/
def low (a b d : ℝ) : ℝ :=
  (a + d - gap a b d) / 2

/-- Evaluation formula for the lower eigenvalue branch. -/
theorem low_apply (a b d : ℝ) :
    low a b d = (a + d - gap a b d) / 2 := by
  rfl

/-- The upper eigenvalue in the explicit quadratic formula. -/
def high (a b d : ℝ) : ℝ :=
  (a + d + gap a b d) / 2

/-- Evaluation formula for the upper eigenvalue branch. -/
theorem high_apply (a b d : ℝ) :
    high a b d = (a + d + gap a b d) / 2 := by
  rfl

/-- The unnormalized, positively oriented low-eigenvector branch near `matrix 0 0 1`. -/
def lowRaw (a b d : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![d - low a b d, -b]

/-- The normalization denominator of `lowRaw`. -/
def lowDenom (a b d : ℝ) : ℝ :=
  √((d - low a b d) ^ 2 + b ^ 2)

/-- Evaluation formula for the normalization denominator of the low eigenvector. -/
theorem lowDenom_apply (a b d : ℝ) :
    lowDenom a b d = √((d - low a b d) ^ 2 + b ^ 2) := by
  rfl

/-- The normalization denominator of the fixed low-eigenvector branch is
nonnegative. -/
theorem lowDenom_nonneg (a b d : ℝ) : 0 ≤ lowDenom a b d := by
  rw [lowDenom_apply]
  positivity

/-- The explicit normalized low-eigenvector branch near `matrix 0 0 1`. -/
def lowVector (a b d : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (lowDenom a b d)⁻¹ • lowRaw a b d

/-- Evaluation formula for the normalized low-eigenvector branch. -/
theorem lowVector_apply (a b d : ℝ) :
    lowVector a b d = (lowDenom a b d)⁻¹ • lowRaw a b d := by
  rfl

/-- The explicit perpendicular high-eigenvector branch near `matrix 0 0 1`. -/
def highVector (a b d : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (lowDenom a b d)⁻¹ • WithLp.toLp 2 ![b, d - low a b d]

/-- The coordinate chart `a < d` containing the diagonal matrix `matrix 0 0 1`. -/
def lowChart : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 < p.2.2}

/-- The explicit matrix is Hermitian. -/
theorem matrix_isHermitian (a b d : ℝ) : (matrix a b d).IsHermitian := by
  -- Compare the matrix with its conjugate transpose entry by entry.
  ext i j
  -- The four entries agree because the off-diagonal entries are both `b`.
  fin_cases i
  · fin_cases j
    · simp [matrix]
    · simp [matrix]
  · fin_cases j
    · simp [matrix]
    · simp [matrix]

/-- Squaring the spectral gap recovers the discriminant. -/
theorem gap_sq (a b d : ℝ) :
    gap a b d ^ 2 = (d - a) ^ 2 + 4 * b ^ 2 := by
  -- The discriminant is nonnegative, so squaring its square root is exact.
  rw [gap, Real.sq_sqrt]
  positivity

/-- The explicit eigenvalues add to the trace. -/
theorem low_add_high (a b d : ℝ) :
    low a b d + high a b d = a + d := by
  -- The two square-root contributions cancel.
  simp only [low, high]
  ring

/-- The explicit eigenvalues multiply to the determinant. -/
theorem low_mul_high (a b d : ℝ) :
    low a b d * high a b d = a * d - b ^ 2 := by
  -- Expand the quadratic formula and replace the squared gap by the discriminant.
  rw [low, high]
  nlinarith [gap_sq a b d]

/-- The zeroth ordered Hermitian eigenvalue is the explicit upper eigenvalue. -/
theorem eigenvalues_zero (a b d : ℝ) :
    (matrix_isHermitian a b d).eigenvalues₀ 0 = high a b d := by
  -- Sort the two explicit roots of the characteristic polynomial in decreasing order.
  have hcharpoly : (matrix a b d).charpoly =
      (Polynomial.X - Polynomial.C (low a b d)) *
        (Polynomial.X - Polynomial.C (high a b d)) := by
    symm
    calc
      (Polynomial.X - Polynomial.C (low a b d)) *
          (Polynomial.X - Polynomial.C (high a b d)) =
        Polynomial.X ^ 2 - Polynomial.C (low a b d + high a b d) * Polynomial.X +
          Polynomial.C (low a b d * high a b d) := by
            simp only [map_add, map_mul]
            ring
      _ = Polynomial.X ^ 2 - Polynomial.C (a + d) * Polynomial.X +
          Polynomial.C (a * d - b ^ 2) := by
            rw [low_add_high, low_mul_high]
      _ = (matrix a b d).charpoly := by
            rw [Matrix.charpoly_fin_two]
            simp [matrix]
            ring
  have hlow : low a b d ≤ high a b d := by
    simp only [low, high, gap]
    linarith [Real.sqrt_nonneg ((d - a) ^ 2 + 4 * b ^ 2)]
  have hsorted := (matrix_isHermitian a b d).sort_roots_charpoly_eq_eigenvalues₀
  rw [hcharpoly] at hsorted
  rw [Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.X_sub_C_ne_zero _))] at hsorted
  simp only [Polynomial.roots_X_sub_C, Multiset.singleton_add, RCLike.re_to_real,
    Multiset.map_cons, Multiset.map_singleton, ge_iff_le, Fintype.card_fin,
    List.ofFn_succ, Fin.isValue, Fin.cast_zero, Fin.succ_zero_eq_one,
    List.ofFn_zero] at hsorted
  have hsort : (low a b d ::ₘ {high a b d}).sort (· ≥ ·) =
      [high a b d, low a b d] := by
    have hswap : low a b d ::ₘ {high a b d} = high a b d ::ₘ {low a b d} := by
      simpa only [Multiset.cons_zero] using
        Multiset.cons_swap (low a b d) (high a b d) 0
    have horder : ∀ x ∈ ({low a b d} : Multiset ℝ), high a b d ≥ x := by
      simpa using hlow
    calc
      (low a b d ::ₘ {high a b d}).sort (· ≥ ·) =
          (high a b d ::ₘ {low a b d}).sort (· ≥ ·) := by
            rw [hswap]
      _ = high a b d :: ({low a b d} : Multiset ℝ).sort (· ≥ ·) :=
        Multiset.sort_cons _ _ _ horder
      _ = [high a b d, low a b d] := by rw [Multiset.sort_singleton]
  rw [hsort] at hsorted
  have hzero := congrArg (fun l : List ℝ ↦ l[0]?) hsorted
  simpa using hzero.symm

/-- The first ordered Hermitian eigenvalue is the explicit lower eigenvalue. -/
theorem eigenvalues_one (a b d : ℝ) :
    (matrix_isHermitian a b d).eigenvalues₀ 1 = low a b d := by
  -- The second entry of the decreasingly sorted root list is the lower root.
  have hcharpoly : (matrix a b d).charpoly =
      (Polynomial.X - Polynomial.C (low a b d)) *
        (Polynomial.X - Polynomial.C (high a b d)) := by
    symm
    calc
      (Polynomial.X - Polynomial.C (low a b d)) *
          (Polynomial.X - Polynomial.C (high a b d)) =
        Polynomial.X ^ 2 - Polynomial.C (low a b d + high a b d) * Polynomial.X +
          Polynomial.C (low a b d * high a b d) := by
            simp only [map_add, map_mul]
            ring
      _ = Polynomial.X ^ 2 - Polynomial.C (a + d) * Polynomial.X +
          Polynomial.C (a * d - b ^ 2) := by
            rw [low_add_high, low_mul_high]
      _ = (matrix a b d).charpoly := by
            rw [Matrix.charpoly_fin_two]
            simp [matrix]
            ring
  have hlow : low a b d ≤ high a b d := by
    simp only [low, high, gap]
    linarith [Real.sqrt_nonneg ((d - a) ^ 2 + 4 * b ^ 2)]
  have hsorted := (matrix_isHermitian a b d).sort_roots_charpoly_eq_eigenvalues₀
  rw [hcharpoly] at hsorted
  rw [Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.X_sub_C_ne_zero _))] at hsorted
  simp only [Polynomial.roots_X_sub_C, Multiset.singleton_add, RCLike.re_to_real,
    Multiset.map_cons, Multiset.map_singleton, ge_iff_le, Fintype.card_fin,
    List.ofFn_succ, Fin.isValue, Fin.cast_zero, Fin.succ_zero_eq_one,
    List.ofFn_zero] at hsorted
  have hsort : (low a b d ::ₘ {high a b d}).sort (· ≥ ·) =
      [high a b d, low a b d] := by
    have hswap : low a b d ::ₘ {high a b d} = high a b d ::ₘ {low a b d} := by
      simpa only [Multiset.cons_zero] using
        Multiset.cons_swap (low a b d) (high a b d) 0
    have horder : ∀ x ∈ ({low a b d} : Multiset ℝ), high a b d ≥ x := by
      simpa using hlow
    calc
      (low a b d ::ₘ {high a b d}).sort (· ≥ ·) =
          (high a b d ::ₘ {low a b d}).sort (· ≥ ·) := by
            rw [hswap]
      _ = high a b d :: ({low a b d} : Multiset ℝ).sort (· ≥ ·) :=
        Multiset.sort_cons _ _ _ horder
      _ = [high a b d, low a b d] := by rw [Multiset.sort_singleton]
  rw [hsort] at hsorted
  have hone := congrArg (fun l : List ℝ ↦ l[1]?) hsorted
  simp at hone
  have hexists : ∃ i : Fin 2,
      (matrix_isHermitian a b d).eigenvalues₀ i = low a b d ∧ i.val = 1 := by
    refine ⟨_, hone.symm, rfl⟩
  obtain ⟨i, hieigen, hi⟩ := hexists
  have hindex : i = 1 := Fin.ext hi
  subst i
  exact hieigen

/-- The explicit lower eigenvalue is at most the explicit upper eigenvalue. -/
theorem low_le_high (a b d : ℝ) : low a b d ≤ high a b d := by
  -- Their difference is the nonnegative spectral gap.
  simp only [low, high]
  rw [gap]
  linarith [Real.sqrt_nonneg ((d - a) ^ 2 + 4 * b ^ 2)]

/-- The explicit eigenvalues are strictly ordered exactly when the gap is positive. -/
theorem low_lt_high_iff_gap_pos (a b d : ℝ) :
    low a b d < high a b d ↔ 0 < gap a b d := by
  -- Clearing the common denominator leaves precisely positivity of the gap.
  simp only [low, high]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- A positive spectral gap makes the two explicit eigenvalues distinct. -/
theorem low_ne_high (a b d : ℝ) (hgap : 0 < gap a b d) :
    low a b d ≠ high a b d := by
  -- Strict ordering immediately gives distinctness.
  exact ne_of_lt ((low_lt_high_iff_gap_pos a b d).2 hgap)

/-- With positive spectral gap, the lower eigenvalue has algebraic multiplicity one. -/
theorem rootMultiplicity_low (a b d : ℝ) (hgap : 0 < gap a b d) :
    (Matrix.toLin' (matrix a b d)).charpoly.rootMultiplicity (low a b d) = 1 := by
  -- Factor the quadratic characteristic polynomial into its two distinct linear factors.
  rw [Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
  have hfactor : Polynomial.X ^ 2 - Polynomial.C (matrix a b d).trace * Polynomial.X +
      Polynomial.C (matrix a b d).det =
        (Polynomial.X - Polynomial.C (low a b d)) *
          (Polynomial.X - Polynomial.C (high a b d)) := by
    calc
      _ = Polynomial.X ^ 2 - Polynomial.C (a + d) * Polynomial.X +
          Polynomial.C (a * d - b ^ 2) := by
            simp [matrix]
            ring
      _ = Polynomial.X ^ 2 - Polynomial.C (low a b d + high a b d) * Polynomial.X +
          Polynomial.C (low a b d * high a b d) := by
            rw [low_add_high, low_mul_high]
      _ = _ := by
            simp only [map_add, map_mul]
            ring
  rw [hfactor, Polynomial.rootMultiplicity_mul]
  · rw [Polynomial.rootMultiplicity_X_sub_C_self,
      Polynomial.rootMultiplicity_X_sub_C]
    simp [low_ne_high a b d hgap]
  · exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)

/-- With positive spectral gap, the upper eigenvalue has algebraic multiplicity one. -/
theorem rootMultiplicity_high (a b d : ℝ) (hgap : 0 < gap a b d) :
    (Matrix.toLin' (matrix a b d)).charpoly.rootMultiplicity (high a b d) = 1 := by
  -- The same factorization gives multiplicity one for the other distinct root.
  rw [Matrix.charpoly_toLin', Matrix.charpoly_fin_two]
  have hfactor : Polynomial.X ^ 2 - Polynomial.C (matrix a b d).trace * Polynomial.X +
      Polynomial.C (matrix a b d).det =
        (Polynomial.X - Polynomial.C (low a b d)) *
          (Polynomial.X - Polynomial.C (high a b d)) := by
    calc
      _ = Polynomial.X ^ 2 - Polynomial.C (a + d) * Polynomial.X +
          Polynomial.C (a * d - b ^ 2) := by
            simp [matrix]
            ring
      _ = Polynomial.X ^ 2 - Polynomial.C (low a b d + high a b d) * Polynomial.X +
          Polynomial.C (low a b d * high a b d) := by
            rw [low_add_high, low_mul_high]
      _ = _ := by
            simp only [map_add, map_mul]
            ring
  rw [hfactor, Polynomial.rootMultiplicity_mul]
  · rw [Polynomial.rootMultiplicity_X_sub_C,
      Polynomial.rootMultiplicity_X_sub_C_self]
    simp [Ne.symm (low_ne_high a b d hgap)]
  · exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)

/-- The explicit normalization denominator is the norm of the raw low eigenvector. -/
theorem lowDenom_eq_norm_lowRaw (a b d : ℝ) :
    lowDenom a b d = ‖lowRaw a b d‖ := by
  -- The Euclidean norm is the square root of the sum of the two coordinate squares.
  simp [lowDenom, lowRaw, EuclideanSpace.norm_eq, Fin.sum_univ_two]

/-- The explicit low vector satisfies the low-eigenvalue equation. -/
theorem lowVector_eigen (a b d : ℝ) :
    (Matrix.toEuclideanCLM :
      Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (matrix a b d) (lowVector a b d) =
      low a b d • lowVector a b d := by
  -- Factor out the normalization and verify the raw-vector equation coordinatewise.
  have hhigh : high a b d = a + d - low a b d := by
    linarith [low_add_high a b d]
  rw [lowVector, map_smul, smul_smul, mul_comm (low a b d), ← smul_smul]
  congr 1
  apply PiLp.ext
  intro i
  fin_cases i
  · suffices (d - low a b d) * a - b * b =
        low a b d * (d - low a b d) by
      simpa [lowRaw, matrix]
    calc
      (d - low a b d) * a - b * b =
          a * d - b ^ 2 - a * low a b d := by ring
      _ = low a b d * high a b d - a * low a b d := by
        rw [low_mul_high]
      _ = low a b d * (d - low a b d) := by
        rw [hhigh]
        ring
  · simp [lowRaw, matrix]
    ring

/-- On the chart `a < d`, the explicit low vector is a nonzero eigenvector. -/
theorem lowVector_hasEigenvector (a b d : ℝ) (hchart : a < d) :
    Module.End.HasEigenvector ((Matrix.toEuclideanCLM :
      Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (matrix a b d)).toLinearMap (low a b d) (lowVector a b d) := by
  -- The eigen-equation is already established; chart positivity makes the vector nonzero.
  rw [Module.End.hasEigenvector_iff]
  constructor
  · exact Module.End.mem_eigenspace_iff.2 (lowVector_eigen a b d)
  · have hgap_nonneg : 0 ≤ gap a b d := by
      exact Real.sqrt_nonneg _
    have hfirst : 0 < d - low a b d := by
      rw [low]
      nlinarith [gap_sq a b d, sq_nonneg b]
    have hdenom : 0 < lowDenom a b d := by
      rw [lowDenom]
      apply Real.sqrt_pos.2
      nlinarith [sq_pos_of_pos hfirst, sq_nonneg b]
    intro hzero
    have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hzero
    have hproduct : (lowDenom a b d)⁻¹ * (d - low a b d) ≠ 0 :=
      mul_ne_zero (inv_ne_zero hdenom.ne') hfirst.ne'
    apply hproduct
    simpa [lowVector, lowRaw] using hcoord

/-- On the chart `a < d`, the explicit low eigenvector has unit norm. -/
theorem norm_lowVector (a b d : ℝ) (hchart : a < d) :
    ‖lowVector a b d‖ = 1 := by
  -- On the chart the first raw coordinate is positive, hence its norm is nonzero.
  have hgap_nonneg : 0 ≤ gap a b d := by
    exact Real.sqrt_nonneg _
  have hfirst : 0 < d - low a b d := by
    rw [low]
    nlinarith [gap_sq a b d, sq_nonneg b]
  have hdenom : 0 < lowDenom a b d := by
    rw [lowDenom]
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos hfirst, sq_nonneg b]
  have hraw : ‖lowRaw a b d‖ ≠ 0 := by
    rw [← lowDenom_eq_norm_lowRaw]
    exact hdenom.ne'
  rw [lowVector, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hdenom,
    lowDenom_eq_norm_lowRaw]
  exact inv_mul_cancel₀ hraw

/-- On the chart `a < d`, the first coordinate fixes the sign of the low eigenvector. -/
theorem firstCoordinate_lowVector_pos (a b d : ℝ) (hchart : a < d) :
    0 < lowVector a b d 0 := by
  -- Both the normalization factor and the first raw coordinate are positive on the chart.
  have hgap_nonneg : 0 ≤ gap a b d := by
    exact Real.sqrt_nonneg _
  have hfirst : 0 < d - low a b d := by
    rw [low]
    nlinarith [gap_sq a b d, sq_nonneg b]
  have hdenom : 0 < lowDenom a b d := by
    rw [lowDenom]
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos hfirst, sq_nonneg b]
  simp only [lowVector, PiLp.smul_apply, lowRaw, Matrix.cons_val_zero, smul_eq_mul]
  exact mul_pos (inv_pos.2 hdenom) hfirst

/-- The explicit perpendicular vector satisfies the high-eigenvalue equation. -/
theorem highVector_eigen (a b d : ℝ) :
    (Matrix.toEuclideanCLM :
      Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
      (matrix a b d) (highVector a b d) =
      high a b d • highVector a b d := by
  -- Factor out the normalization and verify the perpendicular raw-vector equation.
  have hhigh : high a b d = a + d - low a b d := by
    linarith [low_add_high a b d]
  rw [highVector, map_smul, smul_smul, mul_comm (high a b d), ← smul_smul]
  congr 1
  apply PiLp.ext
  intro i
  fin_cases i
  · suffices b * a + (d - low a b d) * b = high a b d * b by
      simpa [matrix]
    calc
      b * a + (d - low a b d) * b = b * (a + d - low a b d) := by ring
      _ = b * high a b d := by
        rw [hhigh]
      _ = high a b d * b := by ring
  · suffices b * b + (d - low a b d) * d =
        high a b d * (d - low a b d) by
      simpa [matrix]
    calc
      b * b + (d - low a b d) * d =
          a * d - low a b d * high a b d + (d - low a b d) * d := by
        rw [low_mul_high]
        ring
      _ = high a b d * (d - low a b d) := by
        rw [hhigh]
        ring

/-- On the chart `a < d`, the explicit high eigenvector has unit norm. -/
theorem norm_highVector (a b d : ℝ) (hchart : a < d) :
    ‖highVector a b d‖ = 1 := by
  -- The perpendicular raw vector has the same positive normalization denominator.
  have hgap_nonneg : 0 ≤ gap a b d := by
    exact Real.sqrt_nonneg _
  have hfirst : 0 < d - low a b d := by
    rw [low]
    nlinarith [gap_sq a b d, sq_nonneg b]
  have hdenom : 0 < lowDenom a b d := by
    rw [lowDenom]
    apply Real.sqrt_pos.2
    nlinarith [sq_pos_of_pos hfirst, sq_nonneg b]
  have hrawnorm : ‖WithLp.toLp 2 ![b, d - low a b d]‖ = lowDenom a b d := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, lowDenom, add_comm]
  rw [highVector, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hdenom, hrawnorm]
  exact inv_mul_cancel₀ hdenom.ne'

/-- The explicit low and high vectors are orthogonal. -/
theorem inner_lowVector_highVector (a b d : ℝ) :
    inner ℝ (lowVector a b d) (highVector a b d) = 0 := by
  -- The two raw coordinate pairs are perpendicular, and scaling preserves this.
  simp [lowVector, highVector, lowRaw, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The explicit high vector has the coordinate pair obtained by positively rotating the low
vector through a right angle. -/
theorem highVector_eq_coordinatePerp (a b d : ℝ) :
    highVector a b d = !₂[-lowVector a b d 1, lowVector a b d 0] := by
  -- Expand the common normalization and compare the two rotated coordinates.
  ext i
  fin_cases i <;> simp [highVector, lowVector, lowRaw]

/-- Membership in the low-eigenvector chart is the inequality `a < d`. -/
theorem mem_lowChart (p : ℝ × ℝ × ℝ) :
    p ∈ lowChart ↔ p.1 < p.2.2 := by
  -- Membership unfolds to the defining coordinate inequality.
  rfl

/-- The low-eigenvector coordinate chart is open. -/
theorem isOpen_lowChart : IsOpen lowChart := by
  -- The chart is the strict comparison locus of two continuous coordinate maps.
  exact isOpen_lt continuous_fst (continuous_snd.snd)

/-- The coordinates of `matrix 0 0 1` belong to the low-eigenvector chart. -/
theorem diag_mem_lowChart : ((0, 0, 1) : ℝ × ℝ × ℝ) ∈ lowChart := by
  -- At the reference diagonal matrix the defining inequality is `0 < 1`.
  norm_num [lowChart]

/-- The spectral gap is analytic throughout the chart `a < d`. -/
theorem analyticOnNhd_gap :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ ↦ gap p.1 p.2.1 p.2.2) lowChart := by
  -- The discriminant is positive on the chart, where the positive square-root branch is analytic.
  intro p hp
  have ha : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.1) p := analyticAt_fst
  have hb : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hd : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hdisc : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ (q.2.2 - q.1) ^ 2 + 4 * q.2.1 ^ 2) p := by
    have hleft : AnalyticAt ℝ
        (fun q : ℝ × ℝ × ℝ ↦ (q.2.2 - q.1) ^ 2) p := by
      have hsub := hd.sub ha
      apply (hsub.smul hsub).congr
      filter_upwards [] with q
      simp only [Pi.smul_apply', Pi.sub_apply, smul_eq_mul, pow_two]
    have hright : AnalyticAt ℝ
        (fun q : ℝ × ℝ × ℝ ↦ 4 * q.2.1 ^ 2) p := by
      have hbsq : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.1 ^ 2) p := by
        apply (hb.smul hb).congr
        filter_upwards [] with q
        simp only [Pi.smul_apply', smul_eq_mul, pow_two]
      apply (hbsq.const_smul (c := (4 : ℝ))).congr
      filter_upwards [] with q
      simp only [Pi.smul_apply, smul_eq_mul]
    apply (hleft.add hright).congr
    filter_upwards [] with q
    rfl
  have hdisc_pos : 0 < (p.2.2 - p.1) ^ 2 + 4 * p.2.1 ^ 2 := by
    rw [mem_lowChart] at hp
    nlinarith [sq_pos_of_pos (sub_pos.2 hp), sq_nonneg p.2.1]
  have hsqrt : AnalyticAt ℝ Real.sqrt ((p.2.2 - p.1) ^ 2 + 4 * p.2.1 ^ 2) := by
    have hformula : AnalyticAt ℝ
        (fun x : ℝ ↦ NormedSpace.exp (Real.log x * (1 / 2 : ℝ)))
        ((p.2.2 - p.1) ^ 2 + 4 * p.2.1 ^ 2) :=
      (NormedSpace.exp_analytic _).comp ((analyticAt_log hdisc_pos).mul analyticAt_const)
    apply hformula.congr
    filter_upwards [eventually_gt_nhds hdisc_pos] with x hx
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Real.exp_eq_exp_ℝ]
  have hcomposition : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ √((q.2.2 - q.1) ^ 2 + 4 * q.2.1 ^ 2)) p :=
    hsqrt.comp (f := fun q : ℝ × ℝ × ℝ ↦
      (q.2.2 - q.1) ^ 2 + 4 * q.2.1 ^ 2) hdisc
  simpa only [gap] using hcomposition

/-- The lower eigenvalue is analytic throughout the chart `a < d`. -/
theorem analyticOnNhd_low :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ ↦ low p.1 p.2.1 p.2.2) lowChart := by
  -- The lower branch is obtained from analytic coordinates and the analytic gap by arithmetic.
  intro p hp
  have ha : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.1) p := analyticAt_fst
  have hd : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hlinear : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.1 + q.2.2) p := by
    apply (ha.add hd).congr
    filter_upwards [] with q
    rfl
  have hresult : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦
        (q.1 + q.2.2 - gap q.1 q.2.1 q.2.2) / 2) p := by
    apply ((hlinear.sub (analyticOnNhd_gap p hp)).const_smul (c := (2 : ℝ)⁻¹)).congr
    filter_upwards [] with q
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simpa only [low] using hresult

/-- The upper eigenvalue is analytic throughout the chart `a < d`. -/
theorem analyticOnNhd_high :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ ↦ high p.1 p.2.1 p.2.2) lowChart := by
  -- The upper branch is obtained by adding the same analytic gap.
  intro p hp
  have ha : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.1) p := analyticAt_fst
  have hd : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hlinear : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.1 + q.2.2) p := by
    apply (ha.add hd).congr
    filter_upwards [] with q
    rfl
  have hresult : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦
        (q.1 + q.2.2 + gap q.1 q.2.1 q.2.2) / 2) p := by
    apply ((hlinear.add (analyticOnNhd_gap p hp)).const_smul (c := (2 : ℝ)⁻¹)).congr
    filter_upwards [] with q
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  simpa only [high] using hresult

/-- The normalized low-eigenvector branch is analytic throughout the chart `a < d`. -/
theorem analyticOnNhd_lowVector :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ ↦ lowVector p.1 p.2.1 p.2.2) lowChart := by
  -- The raw coordinates and the reciprocal positive normalization are analytic on the chart.
  intro p hp
  have hb : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hd : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hlow := analyticOnNhd_low p hp
  have hfirst : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ q.2.2 - low q.1 q.2.1 q.2.2) p := by
    apply (hd.sub hlow).congr
    filter_upwards [] with q
    rfl
  have hfirst_pos : 0 < p.2.2 - low p.1 p.2.1 p.2.2 := by
    have hgap_nonneg : 0 ≤ gap p.1 p.2.1 p.2.2 := Real.sqrt_nonneg _
    have hchart := (mem_lowChart p).1 hp
    rw [low]
    nlinarith [gap_sq p.1 p.2.1 p.2.2, sq_nonneg p.2.1]
  have hradicand : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦
        (q.2.2 - low q.1 q.2.1 q.2.2) ^ 2 + q.2.1 ^ 2) p := by
    have hfirst_sq : AnalyticAt ℝ
        (fun q : ℝ × ℝ × ℝ ↦ (q.2.2 - low q.1 q.2.1 q.2.2) ^ 2) p := by
      apply (hfirst.smul hfirst).congr
      filter_upwards [] with q
      simp only [Pi.smul_apply', smul_eq_mul, pow_two]
    have hb_sq : AnalyticAt ℝ (fun q : ℝ × ℝ × ℝ ↦ q.2.1 ^ 2) p := by
      apply (hb.smul hb).congr
      filter_upwards [] with q
      simp only [Pi.smul_apply', smul_eq_mul, pow_two]
    apply (hfirst_sq.add hb_sq).congr
    filter_upwards [] with q
    rfl
  have hradicand_pos :
      0 < (p.2.2 - low p.1 p.2.1 p.2.2) ^ 2 + p.2.1 ^ 2 := by
    nlinarith [sq_pos_of_pos hfirst_pos, sq_nonneg p.2.1]
  have hsqrt : AnalyticAt ℝ Real.sqrt
      ((p.2.2 - low p.1 p.2.1 p.2.2) ^ 2 + p.2.1 ^ 2) := by
    have hformula : AnalyticAt ℝ
        (fun x : ℝ ↦ NormedSpace.exp (Real.log x * (1 / 2 : ℝ)))
        ((p.2.2 - low p.1 p.2.1 p.2.2) ^ 2 + p.2.1 ^ 2) :=
      (NormedSpace.exp_analytic _).comp
        ((analyticAt_log hradicand_pos).mul analyticAt_const)
    apply hformula.congr
    filter_upwards [eventually_gt_nhds hradicand_pos] with x hx
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Real.exp_eq_exp_ℝ]
  have hdenom : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ lowDenom q.1 q.2.1 q.2.2) p := by
    have hcomposition : AnalyticAt ℝ
        (fun q : ℝ × ℝ × ℝ ↦
          √((q.2.2 - low q.1 q.2.1 q.2.2) ^ 2 + q.2.1 ^ 2)) p :=
      hsqrt.comp (f := fun q : ℝ × ℝ × ℝ ↦
        (q.2.2 - low q.1 q.2.1 q.2.2) ^ 2 + q.2.1 ^ 2) hradicand
    simpa only [lowDenom] using hcomposition
  have hdenom_pos : 0 < lowDenom p.1 p.2.1 p.2.2 := by
    rw [lowDenom]
    exact Real.sqrt_pos.2 hradicand_pos
  have hinv : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ (lowDenom q.1 q.2.1 q.2.2)⁻¹) p := by
    with_reducible_and_instances
      exact hdenom.inv hdenom_pos.ne'
  have hcoordinates : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ ![q.2.2 - low q.1 q.2.1 q.2.2, -q.2.1]) p := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · simpa using hfirst
    · apply hb.neg.congr
      filter_upwards [] with q
      rfl
  have htoLp : AnalyticAt ℝ (WithLp.toLp 2)
      (![p.2.2 - low p.1 p.2.1 p.2.2, -p.2.1] : Fin 2 → ℝ) := by
    simpa only [analyticWithinAt_univ] using
      (PiLp.analyticOn_toLp (𝕜 := ℝ) 2 Set.univ
        (![p.2.2 - low p.1 p.2.1 p.2.2, -p.2.1] : Fin 2 → ℝ) (Set.mem_univ _))
  have hraw : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ lowRaw q.1 q.2.1 q.2.2) p := by
    have hcomposition := htoLp.comp (f := fun q : ℝ × ℝ × ℝ ↦
      ![q.2.2 - low q.1 q.2.1 q.2.2, -q.2.1]) hcoordinates
    apply hcomposition.congr
    filter_upwards [] with q
    rfl
  apply (hinv.smul hraw).congr
  filter_upwards [] with q
  simp only [Pi.smul_apply', lowVector]

/-- The perpendicular high-eigenvector branch is analytic throughout the chart `a < d`. -/
theorem analyticOnNhd_highVector :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ ↦ highVector p.1 p.2.1 p.2.2) lowChart := by
  -- Rotate the analytic low-vector coordinates by a fixed quarter turn.
  intro p hp
  have hlowVector := analyticOnNhd_lowVector p hp
  have hprojZero : AnalyticAt ℝ
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) (lowVector p.1 p.2.1 p.2.2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).analyticAt _
  have hprojOne : AnalyticAt ℝ
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) (lowVector p.1 p.2.1 p.2.2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).analyticAt _
  have hzero : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ lowVector q.1 q.2.1 q.2.2 0) p :=
    hprojZero.comp (f := fun q : ℝ × ℝ × ℝ ↦ lowVector q.1 q.2.1 q.2.2) hlowVector
  have hone : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦ lowVector q.1 q.2.1 q.2.2 1) p :=
    hprojOne.comp (f := fun q : ℝ × ℝ × ℝ ↦ lowVector q.1 q.2.1 q.2.2) hlowVector
  have hcoordinates : AnalyticAt ℝ
      (fun q : ℝ × ℝ × ℝ ↦
        ![-lowVector q.1 q.2.1 q.2.2 1, lowVector q.1 q.2.1 q.2.2 0]) p := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · apply hone.neg.congr
      filter_upwards [] with q
      rfl
    · simpa using hzero
  have htoLp : AnalyticAt ℝ (WithLp.toLp 2)
      (![-lowVector p.1 p.2.1 p.2.2 1, lowVector p.1 p.2.1 p.2.2 0] : Fin 2 → ℝ) := by
    simpa only [analyticWithinAt_univ] using
      (PiLp.analyticOn_toLp (𝕜 := ℝ) 2 Set.univ
        (![-lowVector p.1 p.2.1 p.2.2 1, lowVector p.1 p.2.1 p.2.2 0] : Fin 2 → ℝ)
        (Set.mem_univ _))
  have hcomposition := htoLp.comp (f := fun q : ℝ × ℝ × ℝ ↦
    ![-lowVector q.1 q.2.1 q.2.2 1, lowVector q.1 q.2.1 q.2.2 0]) hcoordinates
  apply hcomposition.congr
  filter_upwards [] with q
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [highVector, lowVector, lowRaw]

/-- At `matrix 0 0 1`, the low eigenvector is the first standard basis vector. -/
theorem lowVector_diag :
    lowVector 0 0 1 = WithLp.toLp 2 ![(1 : ℝ), 0] := by
  -- The formulas reduce to the first standard basis vector at the diagonal base point.
  ext i
  fin_cases i <;> norm_num [lowVector, lowDenom, lowRaw, low, gap]


end RealSymmetric2
