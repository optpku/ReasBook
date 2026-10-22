/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_6

noncomputable section

open scoped Matrix.Norms.Elementwise

-- Owner reuse: `Theorem_7_2_2` already owns the Chapter 7 least-squares objective, Jacobian,
-- correction matrix, and Gauss-Newton normal matrix. This exercise keeps only the local estimate
-- predicates and the source-facing statements that use those canonical owners.

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)

/-- `F` satisfies a local first-order difference estimate at `xStar` when some positive-radius
ball around `xStar` carries a positive linear bound for `‖F x - F xStar‖`. -/
def LocalDifferenceEstimateAt {E : Type _} [NormedAddCommGroup E] (F : Point → E) (xStar : Point) :
    Prop :=
  ∃ δ : {δ : ℝ // 0 < δ}, ∃ c : {c : ℝ // 0 < c},
    ∀ x : Point,
      x ∈ Metric.ball xStar δ.1 →
        ‖F x - F xStar‖ ≤ c.1 * ‖x - xStar‖

/-- `F` is locally Lipschitz on a ball around `xStar` when nearby points satisfy a positive
linear difference bound. -/
def NeighborhoodLipschitzEstimateAt {E : Type _} [NormedAddCommGroup E]
    (F : Point → E) (xStar : Point) : Prop :=
  ∃ δ : {δ : ℝ // 0 < δ}, ∃ c : {c : ℝ // 0 < c},
    ∀ x y : Point,
      x ∈ Metric.ball xStar δ.1 →
        y ∈ Metric.ball xStar δ.1 →
          ‖F x - F y‖ ≤ c.1 * ‖x - y‖

/-- A neighborhood Lipschitz estimate yields the corresponding one-point difference estimate by
specializing one argument to `xStar`. -/
theorem NeighborhoodLipschitzEstimateAt.localDifferenceEstimateAt
    {E : Type _} [NormedAddCommGroup E] {F : Point → E} {xStar : Point}
    (hF : NeighborhoodLipschitzEstimateAt F xStar) :
    LocalDifferenceEstimateAt F xStar := by
  rcases hF with ⟨δ, c, hF⟩
  refine ⟨δ, c, ?_⟩
  intro x hx
  simpa [Metric.mem_ball] using hF x xStar hx (by simpa [Metric.mem_ball] using δ.2)

/-- Helper for Chapter07 Exercise 7.3: a local max-entry matrix estimate upgrades to a local
`ℓ₂`-operator-norm estimate on the same ball after scaling the constant by the standard
`sqrt (m n)` comparison factor. -/
theorem localDifferenceEstimateAt_l2OperatorNorm
    {F : Point → Matrix (Fin m) (Fin n) ℝ} {xStar : Point}
    (hF : LocalDifferenceEstimateAt F xStar) :
    ∃ δ : {δ : ℝ // 0 < δ}, ∃ c : {c : ℝ // 0 < c},
      ∀ x : Point,
        x ∈ Metric.ball xStar δ.1 →
          ‖F x - F xStar‖₂ ≤ c.1 * ‖x - xStar‖ := by
  rcases hF with ⟨δ, c, hF⟩
  let κ : ℝ := max (Real.sqrt ((m * n : ℕ) : ℝ)) 1
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨δ, ⟨κ * c.1, mul_pos hκ_pos c.2⟩, ?_⟩
  intro x hx
  -- Route correction: cross from the elementwise norm to `‖·‖₂` once and keep the rest scalar.
  calc
    ‖F x - F xStar‖₂
        ≤ Real.sqrt ((m * n : ℕ) : ℝ) * ‖F x - F xStar‖ := by
          simpa [matrixMaxEntryNorm] using
            matrixL2OperatorNorm_le_sqrt_mul_matrixMaxEntryNorm (F x - F xStar)
    _ ≤ κ * ‖F x - F xStar‖ := by
          gcongr
          exact le_max_left _ _
    _ ≤ κ * (c.1 * ‖x - xStar‖) := by
          gcongr
          exact hF x hx
    _ = (κ * c.1) * ‖x - xStar‖ := by
          ring

/-- Helper for Chapter07 Exercise 7.3: expand a Gram-matrix difference into the two product terms
that isolate the perturbation `J x - J xStar`. -/
theorem gramMatrixDifferenceSplit
    {J : Point → Matrix (Fin m) (Fin n) ℝ} (x xStar : Point) :
    (J x).transpose * J x - (J xStar).transpose * J xStar =
      (J x).transpose * (J x - J xStar) +
        (J x - J xStar).transpose * J xStar := by
  -- Split the Gram difference at the mixed term `J xᵀ * J xStar`.
  calc
    (J x).transpose * J x - (J xStar).transpose * J xStar
        = ((J x).transpose * J x - (J x).transpose * J xStar) +
            ((J x).transpose * J xStar - (J xStar).transpose * J xStar) := by
              abel
    _ = (J x).transpose * (J x - J xStar) +
          ((J x).transpose - (J xStar).transpose) * J xStar := by
            rw [← Matrix.mul_sub, ← Matrix.sub_mul]
    _ = (J x).transpose * (J x - J xStar) +
          (J x - J xStar).transpose * J xStar := by
            rw [Matrix.transpose_sub]

/-- Helper for Chapter07 Exercise 7.3: the `ℓ₂` operator norm of a matrix is nonnegative. -/
theorem matrixL2OperatorNorm_nonneg
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ ‖A‖₂ := by
  -- Rewrite to the Euclidean operator norm of the associated continuous linear map.
  rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
  exact norm_nonneg _

/-- Helper for Chapter07 Exercise 7.3: the `ℓ₂` operator norm satisfies the triangle inequality. -/
theorem matrixL2OperatorNorm_add_le
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    ‖A + B‖₂ ≤ ‖A‖₂ + ‖B‖₂ := by
  let Φ :
      Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin n)).trans
      LinearMap.toContinuousLinearMap
  -- Transport the triangle inequality along the matrix-to-operator identification.
  repeat rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
  change ‖Φ (A + B)‖ ≤ ‖Φ A‖ + ‖Φ B‖
  simpa [Φ] using (norm_add_le (Φ A) (Φ B))

/-- Helper for Chapter07 Exercise 7.3: reversing a matrix difference does not change its
`ℓ₂` operator norm. -/
theorem matrixL2OperatorNorm_sub_rev
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    ‖A - B‖₂ = ‖B - A‖₂ := by
  let Φ :
      Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin n)).trans
      LinearMap.toContinuousLinearMap
  -- Rewrite the reversed difference as multiplication by `-1` after passing to operators.
  repeat rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
  change ‖Φ (A - B)‖ = ‖Φ (B - A)‖
  have hRevMap : (-1 : ℝ) • Φ (A - B) = Φ (B - A) := by
    ext x j
    simp [Φ, sub_eq_add_neg]
    ring
  calc
    ‖Φ (A - B)‖ = ‖(-1 : ℝ) • Φ (A - B)‖ := by
      simpa using (norm_smul (-1 : ℝ) (Φ (A - B))).symm
    _ = ‖Φ (B - A)‖ := by
      rw [hRevMap]

/-- Helper for Chapter07 Exercise 7.3: a fixed-basepoint estimate for a matrix field implies the
same kind of estimate for its Gram field `x ↦ (J x)ᵀ * J x`. -/
theorem gramMatrixLocalDifferenceEstimateAt
    {J : Point → Matrix (Fin m) (Fin n) ℝ} {xStar : Point}
    (hJ : LocalDifferenceEstimateAt J xStar) :
    LocalDifferenceEstimateAt (fun x ↦ (J x).transpose * J x) xStar := by
  rcases localDifferenceEstimateAt_l2OperatorNorm hJ with ⟨δ, c, hJdiff⟩
  let C : ℝ := (2 * ‖J xStar‖₂ + c.1) * c.1
  have hC_pos : 0 < C := by
    -- The Gram coefficient is positive because the local Jacobian bound has positive slope.
    dsimp [C]
    have hFront : 0 < 2 * ‖J xStar‖₂ + c.1 := by
      have hNorm : 0 ≤ ‖J xStar‖₂ := matrixL2OperatorNorm_nonneg (J xStar)
      linarith [c.2, hNorm]
    exact mul_pos hFront c.2
  refine ⟨⟨min δ.1 1, lt_min δ.2 zero_lt_one⟩, ⟨C, hC_pos⟩, ?_⟩
  intro x hx
  have hxδ : x ∈ Metric.ball xStar δ.1 := by
    -- Shrinking to `min δ 1` keeps the original local perturbation witness available.
    have hx' : dist x xStar < min δ.1 1 := by
      simpa [Metric.mem_ball] using hx
    simpa [Metric.mem_ball] using lt_of_lt_of_le hx' (min_le_left _ _)
  have hxOne : ‖x - xStar‖ ≤ 1 := by
    -- The extra `1` in the radius makes the perturbation itself uniformly bounded by `c`.
    have hx' : ‖x - xStar‖ < min δ.1 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    exact (le_of_lt hx').trans (min_le_right _ _)
  have hDelta :
      ‖J x - J xStar‖₂ ≤ c.1 * ‖x - xStar‖ := hJdiff x hxδ
  have hDeltaBound : ‖J x - J xStar‖₂ ≤ c.1 := by
    -- On the unit-shrunk ball, the perturbation estimate yields an absolute `ℓ₂` bound.
    calc
      ‖J x - J xStar‖₂ ≤ c.1 * ‖x - xStar‖ := hDelta
      _ ≤ c.1 * 1 := by
            exact mul_le_mul_of_nonneg_left hxOne (le_of_lt c.2)
      _ = c.1 := by ring
  have hJStarNonneg : 0 ≤ ‖J xStar‖₂ := matrixL2OperatorNorm_nonneg (J xStar)
  have hDeltaNonneg : 0 ≤ ‖J x - J xStar‖₂ :=
    matrixL2OperatorNorm_nonneg (J x - J xStar)
  have hJStarPlusCNonneg : 0 ≤ ‖J xStar‖₂ + c.1 := by
    linarith [hJStarNonneg, c.2]
  have hJxBound : ‖J x‖₂ ≤ ‖J xStar‖₂ + c.1 := by
    -- Rewrite `J x` as perturbation plus base value and apply the triangle inequality once.
    have hDecomp : (J x - J xStar) + J xStar = J x := by
      exact sub_add_cancel (J x) (J xStar)
    calc
      ‖J x‖₂ = ‖(J x - J xStar) + J xStar‖₂ := by rw [hDecomp]
      _ ≤ ‖J x - J xStar‖₂ + ‖J xStar‖₂ :=
            matrixL2OperatorNorm_add_le (J x - J xStar) (J xStar)
      _ ≤ c.1 + ‖J xStar‖₂ := by
            exact add_le_add hDeltaBound le_rfl
      _ = ‖J xStar‖₂ + c.1 := by ring
  have hTransposeJx : ‖(J x).transpose‖₂ = ‖J x‖₂ := by
    -- The spectral norm is invariant under transpose over `ℝ`.
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (J x)
  have hTransposeDelta : ‖(J x - J xStar).transpose‖₂ = ‖J x - J xStar‖₂ := by
    -- The same transpose invariance applies to the perturbation matrix.
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (J x - J xStar)
  have hTerm1 :
      ‖(J x).transpose * (J x - J xStar)‖₂ ≤
        (‖J xStar‖₂ + c.1) * (c.1 * ‖x - xStar‖) := by
    -- Bound the first Gram term by the local Jacobian bound times the perturbation size.
    calc
      ‖(J x).transpose * (J x - J xStar)‖₂
          ≤ ‖(J x).transpose‖₂ * ‖J x - J xStar‖₂ := by
            simpa using Matrix.l2_opNorm_mul (J x).transpose (J x - J xStar)
      _ = ‖J x‖₂ * ‖J x - J xStar‖₂ := by rw [hTransposeJx]
      _ ≤ (‖J xStar‖₂ + c.1) * ‖J x - J xStar‖₂ := by
            exact mul_le_mul_of_nonneg_right hJxBound hDeltaNonneg
      _ ≤ (‖J xStar‖₂ + c.1) * (c.1 * ‖x - xStar‖) := by
            exact mul_le_mul_of_nonneg_left hDelta hJStarPlusCNonneg
  have hTerm2 :
      ‖(J x - J xStar).transpose * J xStar‖₂ ≤
        ‖J xStar‖₂ * (c.1 * ‖x - xStar‖) := by
    -- Bound the second Gram term with the fixed base Jacobian norm.
    calc
      ‖(J x - J xStar).transpose * J xStar‖₂
          ≤ ‖(J x - J xStar).transpose‖₂ * ‖J xStar‖₂ := by
            simpa using Matrix.l2_opNorm_mul (J x - J xStar).transpose (J xStar)
      _ = ‖J x - J xStar‖₂ * ‖J xStar‖₂ := by rw [hTransposeDelta]
      _ ≤ (c.1 * ‖x - xStar‖) * ‖J xStar‖₂ := by
            exact mul_le_mul_of_nonneg_right hDelta hJStarNonneg
      _ = ‖J xStar‖₂ * (c.1 * ‖x - xStar‖) := by ring
  -- Route correction: keep the Gram estimate in `‖·‖₂` until the last step back to the
  -- source-facing max-entry norm.
  calc
    ‖(J x).transpose * J x - (J xStar).transpose * J xStar‖
        ≤ ‖(J x).transpose * J x - (J xStar).transpose * J xStar‖₂ := by
          simpa [matrixMaxEntryNorm] using
            matrixMaxEntryNorm_le_matrixL2OperatorNorm
              ((J x).transpose * J x - (J xStar).transpose * J xStar)
    _ = ‖(J x).transpose * (J x - J xStar) +
          (J x - J xStar).transpose * J xStar‖₂ := by
          rw [gramMatrixDifferenceSplit]
    _ ≤ ‖(J x).transpose * (J x - J xStar)‖₂ +
          ‖(J x - J xStar).transpose * J xStar‖₂ := by
          exact
            matrixL2OperatorNorm_add_le
              ((J x).transpose * (J x - J xStar))
              ((J x - J xStar).transpose * J xStar)
    _ ≤ (‖J xStar‖₂ + c.1) * (c.1 * ‖x - xStar‖) +
          ‖J xStar‖₂ * (c.1 * ‖x - xStar‖) := by
          exact add_le_add hTerm1 hTerm2
    _ = C * ‖x - xStar‖ := by
          dsimp [C]
          ring

/-- Helper for Chapter07 Exercise 7.3: a local max-entry estimate and base-point positive
definiteness yield a uniform nearby `ℓ₂` bound for inverse matrices. -/
theorem localInverseL2NormBoundOfLocalDifferenceEstimateAt
    {A : Point → Matrix (Fin n) (Fin n) ℝ} {xStar : Point}
    (hA : LocalDifferenceEstimateAt A xStar)
    (hPosDef :
      ∃ δ : {δ : ℝ // 0 < δ},
        ∀ x : Point,
          x ∈ Metric.ball xStar δ.1 →
            (A x).PosDef) :
    ∃ δ : {δ : ℝ // 0 < δ}, ∃ M : {M : ℝ // 0 < M},
      ∀ x : Point,
        x ∈ Metric.ball xStar δ.1 →
          IsUnit (A x) ∧ ‖(A x)⁻¹‖₂ ≤ M.1 := by
  classical
  rcases localDifferenceEstimateAt_l2OperatorNorm hA with ⟨δA, c, hADiff⟩
  rcases hPosDef with ⟨δPos, hPosDef⟩
  have hxStarPos : xStar ∈ Metric.ball xStar δPos.1 := by
    simpa [Metric.mem_ball] using δPos.2
  have hRootPosDef : (A xStar).PosDef := hPosDef xStar hxStarPos
  have hRootUnit : IsUnit (A xStar) := hRootPosDef.isUnit
  by_cases hne : Nonempty (Fin n)
  · letI : Nonempty (Fin n) := hne
    let α : ℝ := ‖(A xStar)⁻¹‖₂
    let β : ℝ := 1 / (α + 1)
    let ε : ℝ := min δA.1 (min δPos.1 (β / max c.1 1))
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact matrixL2OperatorNorm_nonneg ((A xStar)⁻¹)
    have hβ_pos : 0 < β := by
      dsimp [β]
      have hα1_pos : 0 < α + 1 := by linarith
      exact one_div_pos.mpr hα1_pos
    have hε_pos : 0 < ε := by
      have hmax_pos : 0 < max c.1 1 := by
        exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      dsimp [ε]
      refine lt_min δA.2 ?_
      refine lt_min δPos.2 ?_
      exact div_pos hβ_pos hmax_pos
    letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
    have hNormL2 :
        IsMatrixNorm (lpMatrixNorm (2 : ENNReal) : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
      -- Use the Chapter 1 induced `ℓ₂` matrix norm interface for the Neumann step.
      simpa [lpMatrixNorm] using
        (inducedMatrixNorm_isMatrixNorm
          (domainNorm := lpNorm (2 : ENNReal))
          (codomainNorm := lpNorm (2 : ENNReal)))
    have hSubL2 :
        MatrixNormSubmultiplicative
          (lpMatrixNorm (2 : ENNReal) : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
      simpa using (lpMatrixNorm_isSubmultiplicative (n := n) (p := (2 : ENNReal)))
    have hOneL2 :
        lpMatrixNorm (2 : ENNReal) (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      -- The identity matrix has operator norm one in the `ℓ₂` world.
      have hIdMap :
          ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n)).trans
              LinearMap.toContinuousLinearMap) (1 : Matrix (Fin n) (Fin n) ℝ) =
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
        ext x i
        simp
      have hOneOp : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖₂ = 1 := by
        calc
          ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖₂ =
              ‖((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n)).trans
                  LinearMap.toContinuousLinearMap) (1 : Matrix (Fin n) (Fin n) ℝ)‖ := by
                exact
                  matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm
                    (1 : Matrix (Fin n) (Fin n) ℝ)
          _ = ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ := by
                rw [hIdMap]
          _ = 1 := by
                exact ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
      calc
        lpMatrixNorm (2 : ENNReal) (1 : Matrix (Fin n) (Fin n) ℝ) =
            ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖₂ := by
              simpa using
                (l2MatrixNorm_eq_l2OperatorNorm
                  (1 : Matrix (Fin n) (Fin n) ℝ))
        _ = 1 := hOneOp
    have hRootInvLp :
        lpMatrixNorm (2 : ENNReal) (A xStar)⁻¹ ≤ α := by
      -- Return to `lpMatrixNorm (2)` only at the Neumann call site.
      simp [l2MatrixNorm_eq_l2OperatorNorm, α]
    have hαβ : α * β < 1 := by
      -- The standard perturbation threshold `β = 1 / (α + 1)` is strictly admissible.
      have hα1_pos : 0 < α + 1 := by linarith
      dsimp [β]
      rw [mul_one_div]
      exact (div_lt_iff₀ hα1_pos).2 (by linarith)
    have hM_pos : 0 < α / (1 - α * β) + 1 := by
      -- Add `1` to the Neumann bound so the existential constant is manifestly positive.
      have hden_pos : 0 < 1 - α * β := sub_pos.mpr hαβ
      have hfrac_nonneg : 0 ≤ α / (1 - α * β) := by
        exact div_nonneg hα_nonneg hden_pos.le
      linarith
    refine ⟨⟨ε, hε_pos⟩, ⟨α / (1 - α * β) + 1, hM_pos⟩, ?_⟩
    intro x hx
    have hε_le_A : ε ≤ δA.1 := by
      dsimp [ε]
      exact min_le_left _ _
    have hε_le_small : ε ≤ β / max c.1 1 := by
      dsimp [ε]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hxε : dist x xStar < ε := by
      simpa [Metric.mem_ball] using hx
    have hxA : x ∈ Metric.ball xStar δA.1 := by
      simpa [Metric.mem_ball] using lt_of_lt_of_le hxε hε_le_A
    have hxnorm : ‖x - xStar‖ < ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hxnorm_le : ‖x - xStar‖ ≤ ε := le_of_lt hxnorm
    have hmax_ne : max c.1 1 ≠ 0 := by
      positivity
    have hpert : ‖A xStar - A x‖₂ ≤ β := by
      -- Route correction: keep the perturbation estimate in `‖·‖₂` and reverse subtraction only
      -- once before entering the Chapter 1 Neumann theorem.
      calc
        ‖A xStar - A x‖₂ = ‖A x - A xStar‖₂ := by
          rw [matrixL2OperatorNorm_sub_rev]
        _ ≤ c.1 * ‖x - xStar‖ := hADiff x hxA
        _ ≤ c.1 * ε := by
              exact mul_le_mul_of_nonneg_left hxnorm_le (le_of_lt c.2)
        _ ≤ c.1 * (β / max c.1 1) := by
              exact mul_le_mul_of_nonneg_left hε_le_small (le_of_lt c.2)
        _ ≤ max c.1 1 * (β / max c.1 1) := by
              refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
              positivity
        _ = β := by
              field_simp [hmax_ne]
    have hpertLp :
        lpMatrixNorm (2 : ENNReal) (A xStar - A x) ≤ β := by
      rw [l2MatrixNorm_eq_l2OperatorNorm]
      exact hpert
    have hneumann :=
      vonNeumannLemma_isUnit_and_inv_norm_le_of_norm_sub_le
        (N := lpMatrixNorm (2 : ENNReal))
        hNormL2 hSubL2 hOneL2
        (A := A xStar) (B := A x)
        (α := α) (β := β)
        hRootUnit hRootInvLp hpertLp hαβ
    refine ⟨hneumann.1, ?_⟩
    have hboundLp :
        lpMatrixNorm (2 : ENNReal) (A x)⁻¹ ≤ α / (1 - α * β) := hneumann.2
    rw [l2MatrixNorm_eq_l2OperatorNorm] at hboundLp
    calc
      ‖(A x)⁻¹‖₂ ≤ α / (1 - α * β) := hboundLp
      _ ≤ α / (1 - α * β) + 1 := by linarith
  · letI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
    refine ⟨⟨1, by norm_num⟩, ⟨‖(A xStar)⁻¹‖₂ + 1, by
      have hnonneg : 0 ≤ ‖(A xStar)⁻¹‖₂ := matrixL2OperatorNorm_nonneg ((A xStar)⁻¹)
      linarith⟩, ?_⟩
    intro x _hx
    -- In the zero-dimensional case every point and matrix is definitionally unique.
    have hx : x = xStar := Subsingleton.elim _ _
    subst x
    refine ⟨by simpa using hRootUnit, ?_⟩
    have hBound :
        ‖(A xStar)⁻¹‖₂ ≤ ‖(A xStar)⁻¹‖₂ + 1 := by
      exact le_add_of_nonneg_right (by norm_num)
    exact hBound

/-- Helper for Chapter07 Exercise 7.3: the inverse of a locally controlled positive-definite
matrix field satisfies the same local first-order estimate. -/
theorem matrixInverseLocalDifferenceEstimateAt
    {A : Point → Matrix (Fin n) (Fin n) ℝ} {xStar : Point}
    (hA : LocalDifferenceEstimateAt A xStar)
    (hPosDef :
      ∃ δ : {δ : ℝ // 0 < δ},
        ∀ x : Point,
          x ∈ Metric.ball xStar δ.1 →
            (A x).PosDef) :
    LocalDifferenceEstimateAt (fun x : Point ↦ (A x)⁻¹) xStar := by
  rcases localDifferenceEstimateAt_l2OperatorNorm hA with ⟨δA, c, hADiff⟩
  rcases localInverseL2NormBoundOfLocalDifferenceEstimateAt hA hPosDef with ⟨δInv, M, hInvCtl⟩
  let ε : ℝ := min δA.1 δInv.1
  let C : ℝ := M.1 * M.1 * c.1
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos M.2 M.2) c.2
  refine ⟨⟨ε, by
    dsimp [ε]
    exact lt_min δA.2 δInv.2⟩, ⟨C, hC_pos⟩, ?_⟩
  intro x hx
  have hε_le_A : ε ≤ δA.1 := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le_inv : ε ≤ δInv.1 := by
    dsimp [ε]
    exact min_le_right _ _
  have hxε : dist x xStar < ε := by
    simpa [Metric.mem_ball] using hx
  have hxA : x ∈ Metric.ball xStar δA.1 := by
    simpa [Metric.mem_ball] using lt_of_lt_of_le hxε hε_le_A
  have hxInv : x ∈ Metric.ball xStar δInv.1 := by
    simpa [Metric.mem_ball] using lt_of_lt_of_le hxε hε_le_inv
  have hxStarInv : xStar ∈ Metric.ball xStar δInv.1 := by
    simpa [Metric.mem_ball] using δInv.2
  rcases hInvCtl x hxInv with ⟨hUnitx, hInvNormx⟩
  rcases hInvCtl xStar hxStarInv with ⟨hUnitStar, hInvNormStar⟩
  have hUnitIff : IsUnit (A x) ↔ IsUnit (A xStar) := by
    exact ⟨fun _ ↦ hUnitStar, fun _ ↦ hUnitx⟩
  have hDiffRev : ‖A xStar - A x‖₂ ≤ c.1 * ‖x - xStar‖ := by
    -- Fix the subtraction orientation once so `Matrix.inv_sub_inv` matches the middle factor.
    calc
      ‖A xStar - A x‖₂ = ‖A x - A xStar‖₂ := by
        rw [matrixL2OperatorNorm_sub_rev]
      _ ≤ c.1 * ‖x - xStar‖ := hADiff x hxA
  have hFirstMul :
      ‖(A x)⁻¹‖₂ * ‖A xStar - A x‖₂ ≤ M.1 * (c.1 * ‖x - xStar‖) := by
    have hStep1 :
        ‖(A x)⁻¹‖₂ * ‖A xStar - A x‖₂ ≤ M.1 * ‖A xStar - A x‖₂ := by
      exact mul_le_mul_of_nonneg_right hInvNormx (matrixL2OperatorNorm_nonneg _)
    have hStep2 :
        M.1 * ‖A xStar - A x‖₂ ≤ M.1 * (c.1 * ‖x - xStar‖) := by
      exact mul_le_mul_of_nonneg_left hDiffRev (le_of_lt M.2)
    exact hStep1.trans hStep2
  have hMulNorm :
      ‖(A x)⁻¹ * (A xStar - A x)‖₂ ≤ ‖(A x)⁻¹‖₂ * ‖A xStar - A x‖₂ := by
    simpa using Matrix.l2_opNorm_mul (A x)⁻¹ (A xStar - A x)
  have hScaledNonneg : 0 ≤ M.1 * (c.1 * ‖x - xStar‖) := by
    have hInnerNonneg : 0 ≤ c.1 * ‖x - xStar‖ := by
      exact mul_nonneg (le_of_lt c.2) (norm_nonneg _)
    exact mul_nonneg (le_of_lt M.2) hInnerNonneg
  -- Route correction: stay in `‖·‖₂` for the inverse-difference estimate and return to the
  -- source-facing matrix max-entry norm only in the final line.
  calc
    ‖(A x)⁻¹ - (A xStar)⁻¹‖
        ≤ ‖(A x)⁻¹ - (A xStar)⁻¹‖₂ := by
          simpa [matrixMaxEntryNorm] using
            matrixMaxEntryNorm_le_matrixL2OperatorNorm ((A x)⁻¹ - (A xStar)⁻¹)
    _ = ‖(A x)⁻¹ * (A xStar - A x) * (A xStar)⁻¹‖₂ := by
          rw [Matrix.inv_sub_inv hUnitIff]
    _ = ‖((A x)⁻¹ * (A xStar - A x)) * (A xStar)⁻¹‖₂ := by
          rw [Matrix.mul_assoc]
    _ ≤ ‖(A x)⁻¹ * (A xStar - A x)‖₂ * ‖(A xStar)⁻¹‖₂ := by
          simpa using Matrix.l2_opNorm_mul ((A x)⁻¹ * (A xStar - A x)) ((A xStar)⁻¹)
    _ ≤ (‖(A x)⁻¹‖₂ * ‖A xStar - A x‖₂) * ‖(A xStar)⁻¹‖₂ := by
          exact mul_le_mul_of_nonneg_right hMulNorm (matrixL2OperatorNorm_nonneg _)
    _ ≤ (M.1 * (c.1 * ‖x - xStar‖)) * ‖(A xStar)⁻¹‖₂ := by
          exact mul_le_mul_of_nonneg_right hFirstMul (matrixL2OperatorNorm_nonneg _)
    _ ≤ (M.1 * (c.1 * ‖x - xStar‖)) * M.1 := by
          exact mul_le_mul_of_nonneg_left hInvNormStar hScaledNonneg
    _ = C * ‖x - xStar‖ := by
          dsimp [C]
          ring

/-- Chapter07 Exercise 7.3 (3): estimate `(7.2.9)` for the inverse Gram field
`x ↦ (gaussNewtonNormalMatrix r x)⁻¹` at `xStar`, assuming `(7.2.7)` plus neighborhood positive
definiteness of `gaussNewtonNormalMatrix r x`. -/
theorem exercise73_inverseJacobianGram_localEstimate
    (r : Point → Residual) (xStar : Point)
    (hRegular : LocalDifferenceEstimateAt (gaussNewtonNormalMatrix r) xStar)
    (hPosDef :
      ∃ δ : {δ : ℝ // 0 < δ},
        ∀ x : Point,
          x ∈ Metric.ball xStar δ.1 →
            (gaussNewtonNormalMatrix r x).PosDef) :
    LocalDifferenceEstimateAt (fun x : Point ↦ (gaussNewtonNormalMatrix r x)⁻¹) xStar := by
  -- Route correction: prove the inverse estimate generically for a locally controlled
  -- positive-definite matrix field, then instantiate it with `gaussNewtonNormalMatrix r`.
  exact matrixInverseLocalDifferenceEstimateAt hRegular hPosDef

/-- Chapter07 Exercise 7.3 (1): estimate `(7.2.7)` for
`A(x) = gaussNewtonNormalMatrix r x = J(x)ᵀ * J(x)` at `xStar`, assuming the residual Jacobian
field is locally Lipschitz near `xStar`. -/
theorem exercise73_jacobianGram_localEstimate
    (r : Point → Residual) (xStar : Point)
    (hRegular : NeighborhoodLipschitzEstimateAt (residualJacobianMatrix r) xStar) :
    LocalDifferenceEstimateAt (gaussNewtonNormalMatrix r) xStar := by
  -- First reduce the neighborhood hypothesis to a fixed-basepoint estimate for `J`.
  change LocalDifferenceEstimateAt
    (fun x : Point ↦ (residualJacobianMatrix r x).transpose * residualJacobianMatrix r x) xStar
  simpa using gramMatrixLocalDifferenceEstimateAt hRegular.localDifferenceEstimateAt

/-- Chapter07 Exercise 7.3 (2): estimate `(7.2.8)` for
`S(x) = leastSquaresCorrectionMatrix r x` at `xStar`, assuming the correction matrix field is
locally Lipschitz near `xStar`. -/
theorem exercise73_secondOrderTerm_localEstimate
    (r : Point → Residual) (xStar : Point)
    (hRegular : NeighborhoodLipschitzEstimateAt (leastSquaresCorrectionMatrix r) xStar) :
    LocalDifferenceEstimateAt (leastSquaresCorrectionMatrix r) xStar :=
  hRegular.localDifferenceEstimateAt

end
