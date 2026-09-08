module

public import ReasLib.Analysis.Asymptotics.Interleave
public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.StepBounds
public import ReasLib.Optimization.BFGS.PlanarGradient.SeparationBounds
public import Mathlib.Data.Nat.EvenOddRec

public section

noncomputable section

open scoped EuclideanSpace Topology

namespace PlanarGradient

/-- A nonconstant affine expression admits a nonzero value satisfying prescribed size and
logarithmic error bounds. -/
private theorem existsNearCancellationWithLogControl
    (P D ε x : ℝ) (j : ℕ) (hP : P ≠ 0) (hD : D ≠ 0) (hε : 0 < ε) :
    ∃ τ δ : ℝ, 0 < |τ| ∧ |τ| < min (min ε (|P| / 2)) 1 ∧
      δ = (τ - P) / D ∧ P + D * δ = τ ∧
        (1 + |Real.log x|) / |Real.log (|τ|)| ≤ 1 / (j + 1 : ℝ) := by
  -- Approach zero from the right until both the algebraic and logarithmic caps hold.
  have hPabs : 0 < |P| := abs_pos.mpr hP
  have hBound : 0 < min (min ε (|P| / 2)) 1 := by
    exact lt_min (lt_min hε (half_pos hPabs)) zero_lt_one
  have hLogEventually :
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        Real.log t < -((1 + |Real.log x|) * (j + 1 : ℝ)) :=
    Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot
      (-((1 + |Real.log x|) * (j + 1 : ℝ)))
  have hBoundEventually : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < min (min ε (|P| / 2)) 1 := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hBound)
  obtain ⟨τ, ⟨hτLog, hτBound⟩, hτPos⟩ :=
    (hLogEventually.and hBoundEventually).and self_mem_nhdsWithin |>.exists
  have hτAbs : |τ| = τ := abs_of_pos hτPos
  have hτOne : τ < 1 := hτBound.trans_le (min_le_right _ _)
  have hLogNeg : Real.log τ < 0 := Real.log_neg hτPos hτOne
  have hDenominatorPos : 0 < |Real.log (|τ|)| := by
    rw [hτAbs, abs_pos]
    exact ne_of_lt hLogNeg
  have hNatPos : 0 < (j + 1 : ℝ) := by positivity
  have hLogControl :
      (1 + |Real.log x|) / |Real.log (|τ|)| ≤ 1 / (j + 1 : ℝ) := by
    rw [div_le_div_iff₀ hDenominatorPos hNatPos, one_mul, hτAbs,
      abs_of_neg hLogNeg]
    linarith
  refine ⟨τ, (τ - P) / D, ?_, ?_, rfl, ?_, hLogControl⟩
  · simpa only [hτAbs] using hτPos
  · simpa only [hτAbs] using hτBound
  -- Solving the affine equation is now a field calculation.
  · field_simp [hD]
    ring

/-- A nondegenerate recurrence step preserves the adjacent-pair inner-product relation. -/
private theorem preStep_next {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0) :
    inner ℝ (next o gPrev g δ - g) (next o gPrev g δ) =
      inner ℝ (next o gPrev g δ) (perturbation o g δ) := by
  -- Orthogonality of the recurrence candidate is rearranged into the next pre-step law.
  have hOrthogonal := next_candidate_orthogonal o gPrev g δPrev δ
    (perturbation o (next o gPrev g δ) 0) hPrev hg hDistinct hPre hScale
    (inner_perturbation o (next o gPrev g δ) 0)
  rw [perturbation_apply, zero_smul, add_zero, candidate_apply,
    inner_sub_right, inner_add_right] at hOrthogonal
  rw [inner_sub_left, real_inner_comm (next o gPrev g δ) g]
  linarith

/-- Planar vectors with positive angular separation are distinct. -/
private theorem ne_of_angularSeparation_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) {x y : E} (h : 0 < angularSeparation o x y) : y ≠ x := by
  -- Equal vectors have zero alternating area, contradicting positive separation.
  intro heq
  subst y
  rw [angularSeparation_apply, o.areaForm_apply_self, abs_zero] at h
  exact lt_irrefl 0 h

/-- The norm of a nondegenerate next gradient equals the absolute recurrence scale. -/
private theorem norm_next_eq_abs_scale {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (x y : E) (δ : ℝ) (hDistinct : y ≠ x) :
    ‖next o x y δ‖ = |scale o x y δ| := by
  -- The normalized secant has unit norm, so only the scalar factor remains.
  rw [next_apply, norm_smul, norm_stepDirection hDistinct, mul_one, Real.norm_eq_abs]

/-- The absolute parallel coefficient is at most the norm of the current vector. -/
private theorem abs_parallelCoefficient_le_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
    (x y : E) (hDistinct : y ≠ x) : |parallelCoefficient x y| ≤ ‖y‖ := by
  -- Cauchy--Schwarz and the unit secant norm give the estimate.
  rw [parallelCoefficient_apply, ← Real.norm_eq_abs]
  calc
    ‖inner ℝ (stepDirection x y) y‖ ≤ ‖stepDirection x y‖ * ‖y‖ := norm_inner_le_norm _ _
    _ = ‖y‖ := by rw [norm_stepDirection hDistinct, one_mul]

/-- The absolute tangent coefficient is at most one for distinct adjacent vectors. -/
private theorem abs_tangentCoefficient_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (x y : E) (hy : y ≠ 0) (hDistinct : y ≠ x) :
    |tangentCoefficient o x y| ≤ 1 := by
  -- Both the normalized secant and the oriented tangent are unit vectors.
  have hTangentNorm : ‖tangent o y‖ = 1 := (orthonormal_tangent o hy).norm_eq_one 1
  rw [tangentCoefficient_apply, ← Real.norm_eq_abs]
  calc
    ‖inner ℝ (stepDirection x y) (tangent o y)‖ ≤
        ‖stepDirection x y‖ * ‖tangent o y‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [norm_stepDirection hDistinct, hTangentNorm, one_mul]

/-- Planar gradient data and quantitative invariants at an even cancellation boundary. -/
private structure EvenCancellationState (η : ℕ → ℝ) (a : ℝ) (j : ℕ) where
  previous : EuclideanSpace ℝ (Fin 2)
  current : EuclideanSpace ℝ (Fin 2)
  previousPerturbation : ℝ
  previous_ne : previous ≠ 0
  current_ne : current ≠ 0
  distinct : current ≠ previous
  preStep : inner ℝ (current - previous) current =
    inner ℝ current (perturbation EuclideanPlane.orientation previous previousPerturbation)
  separation_pos : 0 < angularSeparation EuclideanPlane.orientation previous current
  previousPerturbation_ne : previousPerturbation ≠ 0
  previous_norm_le : ‖previous‖ ≤ a
  current_norm_le : ‖current‖ ≤ a
  cancellation_pos :
    0 < |parallelCoefficient previous current /
      tangentCoefficient EuclideanPlane.orientation previous current|
  cancellation_le :
    |parallelCoefficient previous current /
        tangentCoefficient EuclideanPlane.orientation previous current| ≤
      min (‖current‖ ^ (j + 4))
        ((4 / 9 : ℝ) * η (2 * j + 3) * ‖current‖)

/-- A cancellation-retention pair extending an even cancellation state. -/
private structure EvenCancellationStep (η : ℕ → ℝ) (a : ℝ) (j : ℕ)
    (state : EvenCancellationState η a j) where
  evenPerturbation : ℝ
  nextState : EvenCancellationState η a (j + 1)
  previous_eq : nextState.previous =
    next EuclideanPlane.orientation state.previous state.current evenPerturbation
  current_eq : nextState.current =
    next EuclideanPlane.orientation state.current nextState.previous
      nextState.previousPerturbation
  previousPreStep :
    inner ℝ (nextState.previous - state.current) nextState.previous =
      inner ℝ nextState.previous
        (perturbation EuclideanPlane.orientation state.current evenPerturbation)
  evenPerturbation_ne : evenPerturbation ≠ 0
  evenPerturbation_bounds :
    |evenPerturbation| ∈ Set.Icc
      ((1 / 2 : ℝ) *
        |parallelCoefficient state.previous state.current /
          tangentCoefficient EuclideanPlane.orientation state.previous state.current|)
      ((3 / 2 : ℝ) *
        |parallelCoefficient state.previous state.current /
          tangentCoefficient EuclideanPlane.orientation state.previous state.current|)
  odd_ratio_le : ‖nextState.previous‖ / ‖state.current‖ ≤ η (2 * j + 2)
  even_ratio_le : ‖nextState.current‖ / ‖nextState.previous‖ ≤ η (2 * j + 3)
  oddPerturbation_power_le :
    |nextState.previousPerturbation| ≤ ‖nextState.previous‖ ^ (j + 3)
  retainedRadius_bounds :
    ‖nextState.current‖ ∈ Set.Icc
      (|parallelCoefficient state.current nextState.previous| / 2)
      ((3 / 2 : ℝ) * |parallelCoefficient state.current nextState.previous|)
  retainedCoefficient_eq :
    |parallelCoefficient state.current nextState.previous| =
      |tangentCoefficient EuclideanPlane.orientation state.current nextState.previous| *
        (|evenPerturbation| * ‖nextState.previous‖ / ‖state.current‖)
  logControl :
    (1 + |Real.log
      (|parallelCoefficient state.previous state.current /
        tangentCoefficient EuclideanPlane.orientation state.previous state.current| /
          ‖state.current‖)|) /
      |Real.log ‖nextState.previous‖| ≤ 1 / (j + 1 : ℝ)

/-- Every even cancellation state extends by a pair satisfying the prescribed geometric bounds. -/
private theorem EvenCancellationState.existsNext (η : ℕ → ℝ) (a : ℝ) (j : ℕ)
    (state : EvenCancellationState η a j)
    (hηPos : ∀ n, 0 < η n) (hηLe : ∀ n, η n ≤ (1 : ℝ) / 4) :
    Nonempty (EvenCancellationStep η a j state) := by
  -- The state hypotheses make both coefficients at the cancellation boundary nonzero.
  have hTangent :
      tangentCoefficient EuclideanPlane.orientation state.previous state.current ≠ 0 :=
    tangentCoefficient_ne_zero EuclideanPlane.orientation state.previous state.current
      state.previousPerturbation state.previous_ne state.current_ne state.distinct
      state.preStep state.separation_pos
  have hParallel : parallelCoefficient state.previous state.current ≠ 0 :=
    parallelCoefficient_ne_zero_of_perturbation EuclideanPlane.orientation
      state.previous state.current state.previousPerturbation state.previous_ne
      state.current_ne state.distinct state.preStep state.separation_pos
      state.previousPerturbation_ne
  have hCurrentPos : 0 < ‖state.current‖ := norm_pos_iff.mpr state.current_ne
  have hCancellationPos := state.cancellation_pos
  have hEvenBudgetPos :
      0 < min (‖state.current‖ ^ (j + 3))
        (η (2 * j + 2) * ‖state.current‖) := by
    exact lt_min (pow_pos hCurrentPos _) (mul_pos (hηPos _) hCurrentPos)
  obtain ⟨τ, δEven, hτPos, hτBound, hδEvenEq, hAffineEven, hLogControl⟩ :=
    existsNearCancellationWithLogControl
      (parallelCoefficient state.previous state.current)
      (tangentCoefficient EuclideanPlane.orientation state.previous state.current)
      (min (‖state.current‖ ^ (j + 3))
        (η (2 * j + 2) * ‖state.current‖))
      (|parallelCoefficient state.previous state.current /
          tangentCoefficient EuclideanPlane.orientation state.previous state.current| /
        ‖state.current‖)
      j hParallel hTangent hEvenBudgetPos
  have hτLtOuter :
      |τ| < min
        (min (‖state.current‖ ^ (j + 3))
          (η (2 * j + 2) * ‖state.current‖))
        (|parallelCoefficient state.previous state.current| / 2) :=
    hτBound.trans_le (min_le_left _ _)
  have hτLtBudget :
      |τ| < min (‖state.current‖ ^ (j + 3))
        (η (2 * j + 2) * ‖state.current‖) :=
    hτLtOuter.trans_le (min_le_left _ _)
  have hτLtRatioBudget :
      |τ| < η (2 * j + 2) * ‖state.current‖ :=
    hτLtBudget.trans_le (min_le_right _ _)
  have hτHalfParallel :
      |τ| ≤ |parallelCoefficient state.previous state.current| / 2 :=
    (hτLtOuter.trans_le (min_le_right _ _)).le
  have hScaleEven :
      scale EuclideanPlane.orientation state.previous state.current δEven = τ := by
    rw [scale_apply]
    exact hAffineEven
  have hScaleEvenNe :
      scale EuclideanPlane.orientation state.previous state.current δEven ≠ 0 := by
    rw [hScaleEven]
    exact abs_pos.mp hτPos
  let odd := next EuclideanPlane.orientation state.previous state.current δEven
  have hOddNorm : ‖odd‖ = |τ| := by
    dsimp only [odd]
    rw [norm_next_eq_abs_scale EuclideanPlane.orientation state.previous state.current
      δEven state.distinct, hScaleEven]
  have hOddPos : 0 < ‖odd‖ := by rw [hOddNorm]; exact hτPos
  have hOddNe : odd ≠ 0 := by
    exact next_ne_zero EuclideanPlane.orientation state.previous state.current
      state.previousPerturbation δEven state.previous_ne state.current_ne state.distinct
      state.preStep hScaleEvenNe
  have hOddSeparation :
      0 < angularSeparation EuclideanPlane.orientation state.current odd := by
    dsimp only [odd]
    rw [angularSeparation_next EuclideanPlane.orientation state.previous state.current
      state.previousPerturbation δEven state.previous_ne state.current_ne state.distinct
      state.preStep hScaleEvenNe]
    exact div_pos (mul_pos (norm_pos_iff.mpr state.previous_ne) state.separation_pos)
      (norm_pos_iff.mpr (sub_ne_zero_of_ne state.distinct))
  have hOddDistinct : odd ≠ state.current :=
    ne_of_angularSeparation_pos EuclideanPlane.orientation hOddSeparation
  have hOddPreStep :
      inner ℝ (odd - state.current) odd =
        inner ℝ odd (perturbation EuclideanPlane.orientation state.current δEven) := by
    exact preStep_next EuclideanPlane.orientation state.previous state.current
      state.previousPerturbation δEven state.previous_ne state.current_ne state.distinct
      state.preStep hScaleEvenNe
  have hEvenPerturbationBounds :
      |δEven| ∈ Set.Icc
        ((1 / 2 : ℝ) *
          |parallelCoefficient state.previous state.current /
            tangentCoefficient EuclideanPlane.orientation state.previous state.current|)
        ((3 / 2 : ℝ) *
          |parallelCoefficient state.previous state.current /
            tangentCoefficient EuclideanPlane.orientation state.previous state.current|) := by
    rw [hδEvenEq]
    exact nearCancellation_abs_mem_Icc
      (parallelCoefficient state.previous state.current)
      (tangentCoefficient EuclideanPlane.orientation state.previous state.current) τ
      hParallel hTangent hτHalfParallel
  have hEvenPerturbationNe : δEven ≠ 0 := by
    rw [← abs_pos]
    exact (mul_pos (by norm_num) hCancellationPos).trans_le hEvenPerturbationBounds.1
  -- At the following boundary the nonzero even perturbation supplies a nonzero leading term.
  have hOddParallel : parallelCoefficient state.current odd ≠ 0 :=
    parallelCoefficient_ne_zero_of_perturbation EuclideanPlane.orientation state.current odd
      δEven state.current_ne hOddNe hOddDistinct hOddPreStep hOddSeparation
      hEvenPerturbationNe
  have hOddTangent :
      tangentCoefficient EuclideanPlane.orientation state.current odd ≠ 0 :=
    tangentCoefficient_ne_zero EuclideanPlane.orientation state.current odd δEven
      state.current_ne hOddNe hOddDistinct hOddPreStep hOddSeparation
  let T := |parallelCoefficient state.current odd|
  have hTPos : 0 < T := abs_pos.mpr hOddParallel
  have hTNonneg : 0 ≤ T := hTPos.le
  have hTLeOdd : T ≤ ‖odd‖ := by
    exact abs_parallelCoefficient_le_norm state.current odd hOddDistinct
  have hτLtOne : |τ| < 1 := hτBound.trans_le (min_le_right _ _)
  have hOddLtOne : ‖odd‖ < 1 := by rwa [hOddNorm]
  have hTLtOne : T < 1 := hTLeOdd.trans_lt hOddLtOne
  let c : ℝ := min (((2 : ℝ) ^ ((j + 1) + 3))⁻¹)
    ((4 / 9 : ℝ) * η (2 * (j + 1) + 3)) / 2
  have hCoefficientCapPos :
      0 < min (((2 : ℝ) ^ ((j + 1) + 3))⁻¹)
        ((4 / 9 : ℝ) * η (2 * (j + 1) + 3)) := by
    exact lt_min (inv_pos.mpr (pow_pos (by norm_num) _))
      (mul_pos (by norm_num) (hηPos _))
  have hcPos : 0 < c := half_pos hCoefficientCapPos
  have hcNonneg : 0 ≤ c := hcPos.le
  have hcBound :
      c ≤ min (((2 : ℝ) ^ ((j + 1) + 3))⁻¹)
        ((4 / 9 : ℝ) * η (2 * (j + 1) + 3)) := by
    exact half_le_self hCoefficientCapPos.le
  have hOddChoicePos :
      0 < min (‖odd‖ ^ (j + 3)) (c * ‖odd‖ * T ^ ((j + 1) + 3)) := by
    exact lt_min (pow_pos hOddPos _)
      (mul_pos (mul_pos hcPos hOddPos) (pow_pos hTPos _))
  obtain ⟨δOdd, hδOddPos, hδOddLt, hCorrection⟩ :=
    exists_retainingPerturbation (parallelCoefficient state.current odd)
      (tangentCoefficient EuclideanPlane.orientation state.current odd)
      (min (‖odd‖ ^ (j + 3)) (c * ‖odd‖ * T ^ ((j + 1) + 3)))
      hOddParallel hOddChoicePos
  have hδOddPower : |δOdd| ≤ ‖odd‖ ^ (j + 3) :=
    (hδOddLt.trans_le (min_le_left _ _)).le
  have hδOddInvariant : |δOdd| ≤ c * ‖odd‖ * T ^ ((j + 1) + 3) :=
    (hδOddLt.trans_le (min_le_right _ _)).le
  have hRetained := retainingPerturbation_abs_mem_Icc
    (parallelCoefficient state.current odd)
    (tangentCoefficient EuclideanPlane.orientation state.current odd) δOdd
    hOddParallel hCorrection
  have hScaleOddAbsPos :
      0 < |scale EuclideanPlane.orientation state.current odd δOdd| := by
    rw [scale_apply]
    exact (half_pos hTPos).trans_le hRetained.1
  have hScaleOddNe : scale EuclideanPlane.orientation state.current odd δOdd ≠ 0 :=
    abs_pos.mp hScaleOddAbsPos
  let nextEven := next EuclideanPlane.orientation state.current odd δOdd
  have hNextNorm :
      ‖nextEven‖ =
        |parallelCoefficient state.current odd +
          tangentCoefficient EuclideanPlane.orientation state.current odd * δOdd| := by
    dsimp only [nextEven]
    rw [norm_next_eq_abs_scale EuclideanPlane.orientation state.current odd
      δOdd hOddDistinct, scale_apply]
  have hNextPos : 0 < ‖nextEven‖ := by
    rw [hNextNorm]
    exact (half_pos hTPos).trans_le hRetained.1
  have hNextNe : nextEven ≠ 0 := by
    exact next_ne_zero EuclideanPlane.orientation state.current odd δEven δOdd
      state.current_ne hOddNe hOddDistinct hOddPreStep hScaleOddNe
  have hNextSeparation :
      0 < angularSeparation EuclideanPlane.orientation odd nextEven := by
    dsimp only [nextEven]
    rw [angularSeparation_next EuclideanPlane.orientation state.current odd
      δEven δOdd state.current_ne hOddNe hOddDistinct hOddPreStep hScaleOddNe]
    exact div_pos (mul_pos hCurrentPos hOddSeparation)
      (norm_pos_iff.mpr (sub_ne_zero_of_ne hOddDistinct))
  have hNextDistinct : nextEven ≠ odd :=
    ne_of_angularSeparation_pos EuclideanPlane.orientation hNextSeparation
  have hNextPreStep :
      inner ℝ (nextEven - odd) nextEven =
        inner ℝ nextEven (perturbation EuclideanPlane.orientation odd δOdd) := by
    exact preStep_next EuclideanPlane.orientation state.current odd δEven δOdd
      state.current_ne hOddNe hOddDistinct hOddPreStep hScaleOddNe
  have hRetainedNorm :
      ‖nextEven‖ ∈ Set.Icc (T / 2) ((3 / 2 : ℝ) * T) := by
    rw [hNextNorm]
    exact hRetained
  -- The coefficient-ratio identity turns the cancellation invariant into a radius estimate.
  have hOddCoefficientRatio :
      |parallelCoefficient state.current odd /
          tangentCoefficient EuclideanPlane.orientation state.current odd| =
        |δEven| * ‖odd‖ / ‖state.current‖ :=
    abs_coefficientRatio EuclideanPlane.orientation state.current odd δEven
      state.current_ne hOddNe hOddDistinct hOddPreStep hOddSeparation
  have hOddTangentLe :
      |tangentCoefficient EuclideanPlane.orientation state.current odd| ≤ 1 :=
    abs_tangentCoefficient_le_one EuclideanPlane.orientation state.current odd
      hOddNe hOddDistinct
  have hTFormula :
      T = |tangentCoefficient EuclideanPlane.orientation state.current odd| *
        (|δEven| * ‖odd‖ / ‖state.current‖) := by
    calc
      T = |parallelCoefficient state.current odd| := rfl
      _ = |tangentCoefficient EuclideanPlane.orientation state.current odd| *
          |parallelCoefficient state.current odd /
            tangentCoefficient EuclideanPlane.orientation state.current odd| := by
        rw [abs_div]
        field_simp [abs_ne_zero.mpr hOddTangent]
      _ = |tangentCoefficient EuclideanPlane.orientation state.current odd| *
          (|δEven| * ‖odd‖ / ‖state.current‖) := by rw [hOddCoefficientRatio]
  have hRadiusRatioNonneg : 0 ≤ ‖odd‖ / ‖state.current‖ :=
    div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCancellationBudget :
      |parallelCoefficient state.previous state.current /
          tangentCoefficient EuclideanPlane.orientation state.previous state.current| ≤
        (4 / 9 : ℝ) * η (2 * j + 3) * ‖state.current‖ :=
    state.cancellation_le.trans (min_le_right _ _)
  have hTBound : T ≤ (2 / 3 : ℝ) * η (2 * j + 3) * ‖odd‖ := by
    calc
      T = |tangentCoefficient EuclideanPlane.orientation state.current odd| *
          (|δEven| * ‖odd‖ / ‖state.current‖) := hTFormula
      _ ≤ 1 * (|δEven| * ‖odd‖ / ‖state.current‖) :=
        mul_le_mul_of_nonneg_right hOddTangentLe
          (div_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      _ ≤ ((3 / 2 : ℝ) *
            |parallelCoefficient state.previous state.current /
              tangentCoefficient EuclideanPlane.orientation state.previous state.current|) *
            (‖odd‖ / ‖state.current‖) := by
        rw [one_mul, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hEvenPerturbationBounds.2 hRadiusRatioNonneg
      _ ≤ ((3 / 2 : ℝ) *
            ((4 / 9 : ℝ) * η (2 * j + 3) * ‖state.current‖)) *
            (‖odd‖ / ‖state.current‖) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCancellationBudget (by norm_num))
          hRadiusRatioNonneg
      _ = (2 / 3 : ℝ) * η (2 * j + 3) * ‖odd‖ := by
        field_simp [ne_of_gt hCurrentPos]
        ring
  have hOddRatioLe : ‖odd‖ / ‖state.current‖ ≤ η (2 * j + 2) := by
    rw [div_le_iff₀ hCurrentPos]
    rw [hOddNorm]
    exact hτLtRatioBudget.le
  have hEvenRatioLe : ‖nextEven‖ / ‖odd‖ ≤ η (2 * j + 3) := by
    rw [div_le_iff₀ hOddPos]
    exact hRetainedNorm.2.trans (by linarith [hTBound])
  have hOddNormLe : ‖odd‖ ≤ a := by
    have hQuarter := (hOddRatioLe.trans (hηLe _))
    rw [div_le_iff₀ hCurrentPos] at hQuarter
    calc
      ‖odd‖ ≤ ‖state.current‖ / 4 := by linarith
      _ ≤ ‖state.current‖ := by linarith [norm_nonneg state.current]
      _ ≤ a := state.current_norm_le
  have hNextNormLe : ‖nextEven‖ ≤ a := by
    have hQuarter := hEvenRatioLe.trans (hηLe _)
    rw [div_le_iff₀ hOddPos] at hQuarter
    calc
      ‖nextEven‖ ≤ ‖odd‖ / 4 := by linarith
      _ ≤ ‖odd‖ := by linarith [norm_nonneg odd]
      _ ≤ a := hOddNormLe
  have hTLeTwoNext : T ≤ 2 * ‖nextEven‖ := by linarith [hRetainedNorm.1]
  have hNextCancellationBound :
      |δOdd| * ‖nextEven‖ / ‖odd‖ ≤
        min (‖nextEven‖ ^ ((j + 1) + 4))
          ((4 / 9 : ℝ) * η (2 * (j + 1) + 3) * ‖nextEven‖) :=
    nextCancellationScale_le_min (j + 1) (η (2 * (j + 1) + 3)) c T
      ‖odd‖ ‖nextEven‖ δOdd hOddPos hNextPos hTNonneg hTLeTwoNext hTLtOne
      hδOddInvariant hcNonneg hcBound
  have hNextCancellationRatio :
      |parallelCoefficient odd nextEven /
          tangentCoefficient EuclideanPlane.orientation odd nextEven| =
        |δOdd| * ‖nextEven‖ / ‖odd‖ :=
    abs_coefficientRatio EuclideanPlane.orientation odd nextEven δOdd hOddNe hNextNe
      hNextDistinct hNextPreStep hNextSeparation
  have hNextCancellationPos :
      0 < |parallelCoefficient odd nextEven /
        tangentCoefficient EuclideanPlane.orientation odd nextEven| := by
    rw [hNextCancellationRatio]
    exact div_pos (mul_pos hδOddPos hNextPos) hOddPos
  have hNextCancellationLe :
      |parallelCoefficient odd nextEven /
          tangentCoefficient EuclideanPlane.orientation odd nextEven| ≤
        min (‖nextEven‖ ^ ((j + 1) + 4))
          ((4 / 9 : ℝ) * η (2 * (j + 1) + 3) * ‖nextEven‖) := by
    rw [hNextCancellationRatio]
    exact hNextCancellationBound
  let successor : EvenCancellationState η a (j + 1) :=
    { previous := odd
      current := nextEven
      previousPerturbation := δOdd
      previous_ne := hOddNe
      current_ne := hNextNe
      distinct := hNextDistinct
      preStep := hNextPreStep
      separation_pos := hNextSeparation
      previousPerturbation_ne := abs_pos.mp hδOddPos
      previous_norm_le := hOddNormLe
      current_norm_le := hNextNormLe
      cancellation_pos := hNextCancellationPos
      cancellation_le := hNextCancellationLe }
  -- Package the two recurrence equations and all quantitative facts behind the state interface.
  refine ⟨{
    evenPerturbation := δEven
    nextState := successor
    previous_eq := ?_
    current_eq := ?_
    previousPreStep := ?_
    evenPerturbation_ne := hEvenPerturbationNe
    evenPerturbation_bounds := hEvenPerturbationBounds
    odd_ratio_le := ?_
    even_ratio_le := ?_
    oddPerturbation_power_le := ?_
    retainedRadius_bounds := ?_
    retainedCoefficient_eq := ?_
    logControl := ?_ }⟩
  · rfl
  · rfl
  · exact hOddPreStep
  · exact hOddRatioLe
  · exact hEvenRatioLe
  · exact hδOddPower
  · exact hRetainedNorm
  · exact hTFormula
  · simpa only [successor, hOddNorm] using hLogControl

/-- Initial scales and the first retained recurrence step of an alternating-scale sequence. -/
private structure AlternatingScaleSeed (η : ℕ → ℝ) (σ : ℝ) where
  a : ℝ
  b : ℝ
  state : EvenCancellationState η a 0
  a_pos : 0 < a
  b_pos : 0 < b
  a_lt_one : a < 1
  a_sq_le : a ^ 2 ≤ σ
  previous_eq : state.previous = !₂[0, b]
  current_eq : state.current =
    next EuclideanPlane.orientation !₂[a, 0] !₂[0, b] state.previousPerturbation
  initial_ratio_le : b / a ≤ (1 : ℝ) / 4
  initial_perturbation_ratio_le : b / a ≤ σ
  first_ratio_le : ‖state.current‖ / ‖state.previous‖ ≤ (1 : ℝ) / 4
  first_perturbation_ratio_le : |state.previousPerturbation| / b ≤ σ
  first_perturbation_lt : |state.previousPerturbation| < a / 2
  initialPreStep :
    inner ℝ (!₂[0, b] - !₂[a, 0]) !₂[0, b] =
      inner ℝ !₂[0, b] (perturbation EuclideanPlane.orientation !₂[a, 0] b)
  initialSeparationPos :
    0 < angularSeparation EuclideanPlane.orientation !₂[a, 0] !₂[0, b]

/-- Positive smallness and geometric budgets determine an initial alternating-scale seed. -/
private theorem existsAlternatingScaleSeed (η : ℕ → ℝ) (σ : ℝ)
    (hσPos : 0 < σ) (hσLt : σ < 1) (hηPos : ∀ n, 0 < η n) :
    Nonempty (AlternatingScaleSeed η σ) := by
  -- Explicit nested scales make the first radius ratio uniformly small.
  let a := σ / 2
  let b := a * σ / 16
  have haPos : 0 < a := div_pos hσPos (by norm_num)
  have haLt : a < 1 := by dsimp only [a]; linarith
  have haSq : a ^ 2 ≤ σ := by
    dsimp only [a]
    nlinarith [mul_pos hσPos (sub_pos.mpr hσLt)]
  have hbPos : 0 < b := by
    dsimp only [b]
    positivity
  have hbLtA : b < a := by
    dsimp only [b]
    nlinarith [hσLt, haPos]
  let gZero : EuclideanSpace ℝ (Fin 2) := !₂[a, 0]
  let gOne : EuclideanSpace ℝ (Fin 2) := !₂[0, b]
  have hZeroNorm : ‖gZero‖ = a := by
    dsimp only [gZero]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs,
      abs_of_pos haPos]
  have hOneNorm : ‖gOne‖ = b := by
    dsimp only [gOne]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_sq_eq_abs,
      abs_of_pos hbPos]
  have hZeroNe : gZero ≠ 0 := by rw [← norm_ne_zero_iff, hZeroNorm]; exact ne_of_gt haPos
  have hOneNe : gOne ≠ 0 := by rw [← norm_ne_zero_iff, hOneNorm]; exact ne_of_gt hbPos
  have hInitialArea :
      EuclideanPlane.orientation.areaForm (NormedSpace.normalize gZero)
        (NormedSpace.normalize gOne) = 1 := by
    rw [EuclideanPlane.standardAreaForm_apply, NormedSpace.normalize, hZeroNorm,
      NormedSpace.normalize, hOneNorm]
    dsimp only [gZero, gOne]
    simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, sub_zero]
    field_simp [haPos.ne', hbPos.ne', abs_of_pos haPos, abs_of_pos hbPos]
  have hInitialSeparation :
      angularSeparation EuclideanPlane.orientation gZero gOne = 1 := by
    rw [angularSeparation_apply, hInitialArea, abs_one]
  have hInitialSeparationPos :
      0 < angularSeparation EuclideanPlane.orientation gZero gOne := by
    rw [hInitialSeparation]
    norm_num
  have hInitialDistinct : gOne ≠ gZero :=
    ne_of_angularSeparation_pos EuclideanPlane.orientation hInitialSeparationPos
  have hInitialPerturbationInner :
      inner ℝ gOne (perturbation EuclideanPlane.orientation gZero b) = b ^ 2 := by
    rw [perturbation_apply, inner_smul_right, tangent_apply,
      EuclideanPlane.orientation.inner_rightAngleRotation_right,
      EuclideanPlane.orientation.areaForm_swap]
    simp only [neg_neg]
    calc
      b * EuclideanPlane.orientation.areaForm (NormedSpace.normalize gZero) gOne =
          b * EuclideanPlane.orientation.areaForm (NormedSpace.normalize gZero)
            (‖gOne‖ • NormedSpace.normalize gOne) := by
        rw [NormedSpace.norm_smul_normalize]
      _ = b * (‖gOne‖ * EuclideanPlane.orientation.areaForm
          (NormedSpace.normalize gZero) (NormedSpace.normalize gOne)) := by
        rw [map_smul]
        rfl
      _ = b ^ 2 := by rw [hOneNorm, hInitialArea]; ring
  have hInitialPreStep :
      inner ℝ (gOne - gZero) gOne =
        inner ℝ gOne (perturbation EuclideanPlane.orientation gZero b) := by
    have hOrthogonal : inner ℝ gZero gOne = 0 := by
      dsimp only [gZero, gOne]
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hOneNorm, hOrthogonal,
      sub_zero, hInitialPerturbationInner, sq]
  have hInitialParallel : parallelCoefficient gZero gOne ≠ 0 :=
    parallelCoefficient_ne_zero_of_perturbation EuclideanPlane.orientation gZero gOne b
      hZeroNe hOneNe hInitialDistinct hInitialPreStep hInitialSeparationPos hbPos.ne'
  have hInitialTangent :
      tangentCoefficient EuclideanPlane.orientation gZero gOne ≠ 0 :=
    tangentCoefficient_ne_zero EuclideanPlane.orientation gZero gOne b hZeroNe hOneNe
      hInitialDistinct hInitialPreStep hInitialSeparationPos
  let T := |parallelCoefficient gZero gOne|
  have hTPos : 0 < T := abs_pos.mpr hInitialParallel
  have hTNonneg : 0 ≤ T := hTPos.le
  have hDifferenceNormLower : a ≤ ‖gOne - gZero‖ := by
    dsimp only [gZero, gOne]
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [PiLp.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, zero_sub]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_pos haPos, abs_of_pos hbPos]
    exact (Real.le_sqrt haPos.le (by positivity)).2 (by nlinarith)
  have hParallelFormula :
      parallelCoefficient gZero gOne = b ^ 2 / ‖gOne - gZero‖ := by
    rw [parallelCoefficient_apply, stepDirection_apply, NormedSpace.normalize,
      inner_smul_left, hInitialPreStep, hInitialPerturbationInner]
    simp only [conj_trivial, sq, div_eq_mul_inv]
    ring
  have hTBound : T ≤ b ^ 2 / a := by
    dsimp only [T]
    rw [hParallelFormula, abs_div, abs_of_nonneg (sq_nonneg b),
      abs_of_nonneg (norm_nonneg _)]
    exact div_le_div_of_nonneg_left (sq_nonneg b) haPos hDifferenceNormLower
  have hbRatioQuarter : b / a ≤ (1 : ℝ) / 16 := by
    dsimp only [b]
    field_simp [haPos.ne']
    linarith
  have hbRatioSigma : b / a ≤ σ := by
    calc
      b / a = σ / 16 := by dsimp only [b]; field_simp [haPos.ne']
      _ ≤ σ := by nlinarith
  have hTLtOne : T < 1 := by
    have hTLeB : T ≤ b := by
      calc
        T ≤ b ^ 2 / a := hTBound
        _ = (b / a) * b := by ring
        _ ≤ b := by
          exact mul_le_of_le_one_left hbPos.le (by linarith [hbRatioQuarter])
    exact hTLeB.trans_lt (hbLtA.trans haLt)
  let c : ℝ := min (((2 : ℝ) ^ 3)⁻¹) ((4 / 9 : ℝ) * η 3) / 2
  have hCapPos : 0 < min (((2 : ℝ) ^ 3)⁻¹) ((4 / 9 : ℝ) * η 3) := by
    exact lt_min (inv_pos.mpr (pow_pos (by norm_num) _))
      (mul_pos (by norm_num) (hηPos 3))
  have hcPos : 0 < c := half_pos hCapPos
  have hcNonneg : 0 ≤ c := hcPos.le
  have hcBound : c ≤ min (((2 : ℝ) ^ 3)⁻¹) ((4 / 9 : ℝ) * η 3) :=
    half_le_self hCapPos.le
  have hChoicePos :
      0 < min (a / 2) (min (σ * b) (c * b * T ^ 3)) := by
    exact lt_min (half_pos haPos)
      (lt_min (mul_pos hσPos hbPos) (mul_pos (mul_pos hcPos hbPos) (pow_pos hTPos _)))
  obtain ⟨δOne, hδOnePos, hδOneLt, hCorrection⟩ :=
    exists_retainingPerturbation (parallelCoefficient gZero gOne)
      (tangentCoefficient EuclideanPlane.orientation gZero gOne)
      (min (a / 2) (min (σ * b) (c * b * T ^ 3))) hInitialParallel hChoicePos
  have hδOneLtA : |δOne| < a / 2 := hδOneLt.trans_le (min_le_left _ _)
  have hδOneLeSigmaB : |δOne| ≤ σ * b :=
    (hδOneLt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδOneInvariant : |δOne| ≤ c * b * T ^ 3 :=
    (hδOneLt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hRetained := retainingPerturbation_abs_mem_Icc
    (parallelCoefficient gZero gOne)
    (tangentCoefficient EuclideanPlane.orientation gZero gOne) δOne
    hInitialParallel hCorrection
  have hScaleAbsPos : 0 < |scale EuclideanPlane.orientation gZero gOne δOne| := by
    rw [scale_apply]
    exact (half_pos hTPos).trans_le hRetained.1
  have hScaleNe : scale EuclideanPlane.orientation gZero gOne δOne ≠ 0 :=
    abs_pos.mp hScaleAbsPos
  let gTwo := next EuclideanPlane.orientation gZero gOne δOne
  have hTwoNorm :
      ‖gTwo‖ = |parallelCoefficient gZero gOne +
        tangentCoefficient EuclideanPlane.orientation gZero gOne * δOne| := by
    dsimp only [gTwo]
    rw [norm_next_eq_abs_scale EuclideanPlane.orientation gZero gOne δOne
      hInitialDistinct, scale_apply]
  have hTwoPos : 0 < ‖gTwo‖ := by
    rw [hTwoNorm]
    exact (half_pos hTPos).trans_le hRetained.1
  have hTwoNe : gTwo ≠ 0 :=
    next_ne_zero EuclideanPlane.orientation gZero gOne b δOne hZeroNe hOneNe
      hInitialDistinct hInitialPreStep hScaleNe
  have hTwoSeparation :
      0 < angularSeparation EuclideanPlane.orientation gOne gTwo := by
    dsimp only [gTwo]
    rw [angularSeparation_next EuclideanPlane.orientation gZero gOne b δOne hZeroNe
      hOneNe hInitialDistinct hInitialPreStep hScaleNe, hInitialSeparation]
    exact div_pos (mul_pos (norm_pos_iff.mpr hZeroNe) zero_lt_one) (norm_pos_iff.mpr
      (sub_ne_zero_of_ne hInitialDistinct))
  have hTwoDistinct : gTwo ≠ gOne :=
    ne_of_angularSeparation_pos EuclideanPlane.orientation hTwoSeparation
  have hTwoPreStep :
      inner ℝ (gTwo - gOne) gTwo =
        inner ℝ gTwo (perturbation EuclideanPlane.orientation gOne δOne) :=
    preStep_next EuclideanPlane.orientation gZero gOne b δOne hZeroNe hOneNe
      hInitialDistinct hInitialPreStep hScaleNe
  have hTwoRetained : ‖gTwo‖ ∈ Set.Icc (T / 2) ((3 / 2 : ℝ) * T) := by
    rw [hTwoNorm]
    exact hRetained
  have hTLeTwoTwo : T ≤ 2 * ‖gTwo‖ := by linarith [hTwoRetained.1]
  have hCancellationBound :
      |δOne| * ‖gTwo‖ / b ≤
        min (‖gTwo‖ ^ 4) ((4 / 9 : ℝ) * η 3 * ‖gTwo‖) := by
    simpa only [Nat.zero_add] using nextCancellationScale_le_min 0 (η 3) c T b ‖gTwo‖
      δOne hbPos hTwoPos hTNonneg hTLeTwoTwo hTLtOne hδOneInvariant hcNonneg hcBound
  have hCancellationRatio :
      |parallelCoefficient gOne gTwo /
          tangentCoefficient EuclideanPlane.orientation gOne gTwo| =
        |δOne| * ‖gTwo‖ / b := by
    rw [← hOneNorm]
    exact abs_coefficientRatio EuclideanPlane.orientation gOne gTwo δOne hOneNe hTwoNe
      hTwoDistinct hTwoPreStep hTwoSeparation
  have hCancellationPos :
      0 < |parallelCoefficient gOne gTwo /
        tangentCoefficient EuclideanPlane.orientation gOne gTwo| := by
    rw [hCancellationRatio]
    exact div_pos (mul_pos hδOnePos hTwoPos) hbPos
  have hCancellationLe :
      |parallelCoefficient gOne gTwo /
          tangentCoefficient EuclideanPlane.orientation gOne gTwo| ≤
        min (‖gTwo‖ ^ (0 + 4)) ((4 / 9 : ℝ) * η (2 * 0 + 3) * ‖gTwo‖) := by
    simpa only [Nat.zero_add, Nat.reduceMul] using hCancellationRatio.le.trans hCancellationBound
  have hFirstRatio : ‖gTwo‖ / ‖gOne‖ ≤ (1 : ℝ) / 4 := by
    rw [hOneNorm, div_le_iff₀ hbPos]
    have hUpper := hTwoRetained.2
    have hTBudget : T ≤ (1 / 16 : ℝ) * b := by
      calc
        T ≤ b ^ 2 / a := hTBound
        _ = (b / a) * b := by ring
        _ ≤ (1 / 16 : ℝ) * b :=
          mul_le_mul_of_nonneg_right hbRatioQuarter hbPos.le
    nlinarith
  have hTwoNormLe : ‖gTwo‖ ≤ a := by
    rw [hOneNorm, div_le_iff₀ hbPos] at hFirstRatio
    calc
      ‖gTwo‖ ≤ b / 4 := by linarith
      _ ≤ b := by linarith
      _ ≤ a := hbLtA.le
  have hFirstPerturbationRatio : |δOne| / b ≤ σ := by
    exact (div_le_iff₀ hbPos).2 hδOneLeSigmaB
  let initialState : EvenCancellationState η a 0 :=
    { previous := gOne
      current := gTwo
      previousPerturbation := δOne
      previous_ne := hOneNe
      current_ne := hTwoNe
      distinct := hTwoDistinct
      preStep := hTwoPreStep
      separation_pos := hTwoSeparation
      previousPerturbation_ne := abs_pos.mp hδOnePos
      previous_norm_le := hOneNorm.le.trans hbLtA.le
      current_norm_le := hTwoNormLe
      cancellation_pos := hCancellationPos
      cancellation_le := hCancellationLe }
  -- The seed exposes exactly the initial values and estimates used by the global recursion.
  refine ⟨{
    a := a
    b := b
    state := initialState
    a_pos := haPos
    b_pos := hbPos
    a_lt_one := haLt
    a_sq_le := haSq
    previous_eq := ?_
    current_eq := ?_
    initial_ratio_le := ?_
    initial_perturbation_ratio_le := hbRatioSigma
    first_ratio_le := ?_
    first_perturbation_ratio_le := ?_
    first_perturbation_lt := ?_
    initialPreStep := hInitialPreStep
    initialSeparationPos := hInitialSeparationPos }⟩
  · rfl
  · rfl
  · exact hbRatioQuarter.trans (by norm_num)
  · exact hFirstRatio
  · exact hFirstPerturbationRatio
  · exact hδOneLtA

/-- Prepends a distinguished value to the interleaving of two sequences. -/
private def prependInterleave {α : Type*} (zero : α) (odd even : ℕ → α) (n : ℕ) : α :=
  Nat.evenOddRec zero (fun j _ ↦ if j = 0 then zero else even (j - 1))
    (fun j _ ↦ odd j) n

/-- A prepended interleaving takes its distinguished value at index zero. -/
private theorem prependInterleave_zero {α : Type*} (zero : α) (odd even : ℕ → α) :
    prependInterleave zero odd even 0 = zero := by
  -- This is the zero computation rule of binary even-odd recursion.
  simp only [prependInterleave, Nat.evenOddRec_zero]

/-- The odd entries of a prepended interleaving come from its odd sequence. -/
private theorem prependInterleave_odd {α : Type*} (zero : α) (odd even : ℕ → α) (j : ℕ) :
    prependInterleave zero odd even (2 * j + 1) = odd j := by
  -- The even branch fixes zero, enabling the odd computation rule.
  rw [prependInterleave, Nat.evenOddRec_odd]
  all_goals simp only [if_pos]

/-- The positive even entries of a prepended interleaving come from its even sequence. -/
private theorem prependInterleave_evenSucc {α : Type*} (zero : α)
    (odd even : ℕ → α) (j : ℕ) :
    prependInterleave zero odd even (2 * j + 2) = even j := by
  -- Write the index as twice a successor and use the even computation rule.
  rw [show 2 * j + 2 = 2 * (j + 1) by omega, prependInterleave,
    Nat.evenOddRec_even]
  all_goals simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, if_false, if_pos]

/-- The laws satisfied by an alternating-scale planar gradient construction with
smallness parameter `σ`. -/
structure IsAlternatingScale (σ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin 2))
    (δ : ℕ → ℝ) (a b : ℝ) : Prop where
  nonzero : ∀ k, g k ≠ 0
  aPos : 0 < a
  bPos : 0 < b
  initialZero : g 0 = ![a, 0]
  initialOne : g 1 = ![0, b]
  deltaZero : δ 0 = b
  deltaOnePos : 0 < |δ 1|
  deltaOneLt : |δ 1| < a / 2
  recurrence : ∀ k, 0 < k →
    g (k + 1) = next EuclideanPlane.orientation (g (k - 1)) (g k) (δ k)
  radiusStrictAnti : StrictAnti (fun k ↦ ‖g k‖)
  radiusTendsto : Filter.Tendsto (fun k ↦ ‖g k‖) Filter.atTop (𝓝 0)
  ratioTendsto : Filter.Tendsto (fun k ↦ ‖g (k + 1)‖ / ‖g k‖)
    Filter.atTop (𝓝 0)
  ratioSummable : Summable (fun k ↦ ‖g (k + 1)‖ / ‖g k‖)
  flat : ∀ m : ℕ, (fun k ↦ |δ k|) =o[Filter.atTop] (fun k ↦ ‖g k‖ ^ m)
  oddLogRatioTendsto :
    Filter.Tendsto
      (fun j ↦ (-Real.log ‖g (2 * j + 2)‖) / (-Real.log ‖g (2 * j + 1)‖))
      Filter.atTop (𝓝 1)
  ratioLeQuarter : ∀ k, ‖g (k + 1)‖ / ‖g k‖ ≤ (1 : ℝ) / 4
  perturbationRatioLe : ∀ k, |δ k| / ‖g k‖ ≤ σ

/-- Construct an alternating-scale certificate from its recurrence, initial-value,
asymptotic, and uniform-bound laws. -/
theorem IsAlternatingScale.ofConditions
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (nonzero : ∀ k, g k ≠ 0) (aPos : 0 < a) (bPos : 0 < b)
    (initialZero : g 0 = ![a, 0]) (initialOne : g 1 = ![0, b])
    (deltaZero : δ 0 = b) (deltaOnePos : 0 < |δ 1|) (deltaOneLt : |δ 1| < a / 2)
    (recurrence : ∀ k, 0 < k →
      g (k + 1) = next EuclideanPlane.orientation (g (k - 1)) (g k) (δ k))
    (radiusStrictAnti : StrictAnti (fun k ↦ ‖g k‖))
    (radiusTendsto : Filter.Tendsto (fun k ↦ ‖g k‖) Filter.atTop (𝓝 0))
    (ratioTendsto : Filter.Tendsto (fun k ↦ ‖g (k + 1)‖ / ‖g k‖)
      Filter.atTop (𝓝 0))
    (ratioSummable : Summable (fun k ↦ ‖g (k + 1)‖ / ‖g k‖))
    (flat : ∀ m : ℕ, (fun k ↦ |δ k|) =o[Filter.atTop] (fun k ↦ ‖g k‖ ^ m))
    (oddLogRatioTendsto :
      Filter.Tendsto
        (fun j ↦ (-Real.log ‖g (2 * j + 2)‖) / (-Real.log ‖g (2 * j + 1)‖))
        Filter.atTop (𝓝 1))
    (ratioLeQuarter : ∀ k, ‖g (k + 1)‖ / ‖g k‖ ≤ (1 : ℝ) / 4)
    (perturbationRatioLe : ∀ k, |δ k| / ‖g k‖ ≤ σ) :
    IsAlternatingScale σ g δ a b :=
  { nonzero := nonzero
    aPos := aPos
    bPos := bPos
    initialZero := initialZero
    initialOne := initialOne
    deltaZero := deltaZero
    deltaOnePos := deltaOnePos
    deltaOneLt := deltaOneLt
    recurrence := recurrence
    radiusStrictAnti := radiusStrictAnti
    radiusTendsto := radiusTendsto
    ratioTendsto := ratioTendsto
    ratioSummable := ratioSummable
    flat := flat
    oddLogRatioTendsto := oddLogRatioTendsto
    ratioLeQuarter := ratioLeQuarter
    perturbationRatioLe := perturbationRatioLe }

/-- Fixed multiplicative bounds and vanishing logarithmic error force logarithmic scale ratios
to tend to one. -/
private theorem tendsto_logRatio_one_of_multiplicativeBounds
    (r s x : ℕ → ℝ) (c C : ℝ)
    (hrPos : ∀ j, 0 < r j) (hsPos : ∀ j, 0 < s j) (hxPos : ∀ j, 0 < x j)
    (hrLtOne : ∀ j, r j < 1) (hcPos : 0 < c) (hCPos : 0 < C)
    (hBounds : ∀ j, c * r j * x j ≤ s j ∧ s j ≤ C * r j * x j)
    (hLogControl : ∀ j,
      (1 + |Real.log (x j)|) / |Real.log (r j)| ≤ 1 / (j + 1 : ℝ)) :
    Filter.Tendsto (fun j ↦ (-Real.log (s j)) / (-Real.log (r j)))
      Filter.atTop (nhds 1) := by
  -- A uniform logarithmic constant absorbs both fixed comparison factors.
  let B := max 1 (max |Real.log c| |Real.log C|)
  have hBNonneg : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hDistanceBound (j : ℕ) :
      dist ((-Real.log (s j)) / (-Real.log (r j))) 1 ≤ B / (j + 1 : ℝ) := by
    have hrLogNeg : Real.log (r j) < 0 := Real.log_neg (hrPos j) (hrLtOne j)
    have hrLogAbsPos : 0 < |Real.log (r j)| := abs_pos.mpr (ne_of_lt hrLogNeg)
    have hLowerLog :
        Real.log c + Real.log (r j) + Real.log (x j) ≤ Real.log (s j) := by
      have h := Real.log_le_log
        (mul_pos (mul_pos hcPos (hrPos j)) (hxPos j)) (hBounds j).1
      simpa only [Real.log_mul hcPos.ne' (hrPos j).ne',
        Real.log_mul (mul_pos hcPos (hrPos j)).ne' (hxPos j).ne'] using h
    have hUpperLog :
        Real.log (s j) ≤ Real.log C + Real.log (r j) + Real.log (x j) := by
      have h := Real.log_le_log (hsPos j) (hBounds j).2
      simpa only [Real.log_mul hCPos.ne' (hrPos j).ne',
        Real.log_mul (mul_pos hCPos (hrPos j)).ne' (hxPos j).ne'] using h
    have hLogError :
        |Real.log (s j) - Real.log (r j)| ≤
          |Real.log (x j)| + max |Real.log c| |Real.log C| := by
      rw [abs_le]
      constructor
      · have hcLower := neg_abs_le (Real.log c)
        have hxLower := neg_abs_le (Real.log (x j))
        have hcMax := le_max_left |Real.log c| |Real.log C|
        linarith
      · have hCUpper := le_abs_self (Real.log C)
        have hxUpper := le_abs_self (Real.log (x j))
        have hCMax := le_max_right |Real.log c| |Real.log C|
        linarith
    have hLogErrorB :
        |Real.log (s j) - Real.log (r j)| ≤
          B * (1 + |Real.log (x j)|) := by
      have hBOne : 1 ≤ B := le_max_left _ _
      have hBFixed : max |Real.log c| |Real.log C| ≤ B := le_max_right _ _
      have hBLog : |Real.log (x j)| ≤ B * |Real.log (x j)| := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hBOne (abs_nonneg (Real.log (x j)))
      calc
        |Real.log (s j) - Real.log (r j)| ≤
            |Real.log (x j)| + max |Real.log c| |Real.log C| := hLogError
        _ ≤ B * |Real.log (x j)| + B := add_le_add hBLog hBFixed
        _ = B * (1 + |Real.log (x j)|) := by ring
    have hRatioIdentity :
        (-Real.log (s j)) / (-Real.log (r j)) - 1 =
          (Real.log (s j) - Real.log (r j)) / Real.log (r j) := by
      field_simp [ne_of_lt hrLogNeg]
    rw [Real.dist_eq, hRatioIdentity, abs_div]
    calc
      |Real.log (s j) - Real.log (r j)| / |Real.log (r j)| ≤
          (B * (1 + |Real.log (x j)|)) / |Real.log (r j)| :=
        (div_le_div_iff_of_pos_right hrLogAbsPos).2 hLogErrorB
      _ = B * ((1 + |Real.log (x j)|) / |Real.log (r j)|) := by ring
      _ ≤ B * (1 / (j + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hLogControl j) hBNonneg
      _ = B / (j + 1 : ℝ) := by ring
  have hUpperTendsto :
      Filter.Tendsto (fun j : ℕ ↦ B / (j + 1 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, one_mul] using
      ((tendsto_const_nhds (x := B)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) Filter.atTop (nhds 0)))
  -- The metric error is squeezed by the shifted reciprocal sequence.
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ dist_nonneg))
    (Filter.Eventually.of_forall hDistanceBound) hUpperTendsto

/-- PlanarGradient.exists_alternatingScale: For every `σ ∈ Set.Ioo 0 1`, there are
planar gradients, scalar perturbations, and positive initial scales satisfying the
alternating-scale recurrence, asymptotic, initial-value, and uniform-smallness laws. -/
theorem exists_alternatingScale (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∃ (g : ℕ → EuclideanSpace ℝ (Fin 2)) (δ : ℕ → ℝ) (a b : ℝ),
      IsAlternatingScale σ g δ a b := by
  classical
  rcases hσ with ⟨hσPos, hσLt⟩
  -- A geometric budget controls every ratio after the two initial transitions.
  let η : ℕ → ℝ := fun n ↦ (σ / 16) * (1 / 2 : ℝ) ^ n
  have hηPos (n : ℕ) : 0 < η n := by
    dsimp only [η]
    positivity
  have hηLe (n : ℕ) : η n ≤ (1 : ℝ) / 4 := by
    have hPowLe : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      η n ≤ (σ / 16) * 1 := by
        exact mul_le_mul_of_nonneg_left hPowLe (div_nonneg hσPos.le (by norm_num))
      _ ≤ (1 : ℝ) / 4 := by nlinarith
  obtain ⟨seed⟩ := existsAlternatingScaleSeed η σ hσPos hσLt hηPos
  let advance (j : ℕ) (state : EvenCancellationState η seed.a j) :
      EvenCancellationStep η seed.a j state :=
    Classical.choice (state.existsNext η seed.a j hηPos hηLe)
  let stateAt : (j : ℕ) → EvenCancellationState η seed.a j := fun j ↦
    Nat.rec seed.state (fun n state ↦ (advance n state).nextState) j
  let stepAt (j : ℕ) : EvenCancellationStep η seed.a j (stateAt j) :=
    advance j (stateAt j)
  have hStateZero : stateAt 0 = seed.state := by rfl
  have hStateSucc (j : ℕ) : stateAt (j + 1) = (stepAt j).nextState := by rfl
  have hStatePreviousSucc (j : ℕ) :
      (stateAt (j + 1)).previous =
        next EuclideanPlane.orientation (stateAt j).previous (stateAt j).current
          (stepAt j).evenPerturbation := by
    rw [hStateSucc]
    exact (stepAt j).previous_eq
  have hStateCurrentZero :
      (stateAt 0).current = next EuclideanPlane.orientation !₂[seed.a, 0]
        (stateAt 0).previous (stateAt 0).previousPerturbation := by
    rw [hStateZero, seed.current_eq, seed.previous_eq]
  have hStateCurrentSucc (j : ℕ) :
      (stateAt (j + 1)).current =
        next EuclideanPlane.orientation (stateAt j).current (stateAt (j + 1)).previous
          (stateAt (j + 1)).previousPerturbation := by
    rw [hStateSucc]
    exact (stepAt j).current_eq
  let g : ℕ → EuclideanSpace ℝ (Fin 2) :=
    prependInterleave !₂[seed.a, 0] (fun j ↦ (stateAt j).previous)
      (fun j ↦ (stateAt j).current)
  let δ : ℕ → ℝ :=
    prependInterleave seed.b (fun j ↦ (stateAt j).previousPerturbation)
      (fun j ↦ (stepAt j).evenPerturbation)
  have hgZero : g 0 = !₂[seed.a, 0] := by
    exact prependInterleave_zero _ _ _
  have hgOdd (j : ℕ) : g (2 * j + 1) = (stateAt j).previous := by
    exact prependInterleave_odd _ _ _ j
  have hgEven (j : ℕ) : g (2 * j + 2) = (stateAt j).current := by
    exact prependInterleave_evenSucc _ _ _ j
  have hδZero : δ 0 = seed.b := by
    exact prependInterleave_zero _ _ _
  have hδOdd (j : ℕ) : δ (2 * j + 1) = (stateAt j).previousPerturbation := by
    exact prependInterleave_odd _ _ _ j
  have hδEven (j : ℕ) : δ (2 * j + 2) = (stepAt j).evenPerturbation := by
    exact prependInterleave_evenSucc _ _ _ j
  have hgOne : g 1 = (stateAt 0).previous := by simpa using hgOdd 0
  have hgTwo : g 2 = (stateAt 0).current := by simpa using hgEven 0
  have hδOne : δ 1 = (stateAt 0).previousPerturbation := by simpa using hδOdd 0
  -- The state projections give nonzeroness and both parity cases of the recurrence.
  have hgNonzero (k : ℕ) : g k ≠ 0 := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · cases j with
      | zero =>
          rw [hgZero]
          intro h
          have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) h
          simp only [PiLp.zero_apply, Matrix.cons_val_zero] at hcoord
          exact seed.a_pos.ne' hcoord
      | succ j =>
          rw [show 2 * (j + 1) = 2 * j + 2 by omega, hgEven]
          exact (stateAt j).current_ne
    · rw [hgOdd]
      exact (stateAt j).previous_ne
  have hRecurrence (k : ℕ) (hk : 0 < k) :
      g (k + 1) = next EuclideanPlane.orientation (g (k - 1)) (g k) (δ k) := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · cases j with
      | zero => simp only [lt_self_iff_false] at hk
      | succ j =>
          rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
            show 2 * (j + 1) = 2 * j + 2 by omega]
          rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by omega,
            hgOdd (j + 1), hgOdd j, hgEven j, hδEven j]
          exact hStatePreviousSucc j
    · cases j with
      | zero =>
          rw [show 2 * 0 + 1 + 1 = 2 by norm_num,
            show 2 * 0 + 1 - 1 = 0 by norm_num,
            show 2 * 0 + 1 = 1 by norm_num, hgTwo, hgZero, hgOne, hδOne]
          exact hStateCurrentZero
      | succ j =>
          rw [show 2 * (j + 1) + 1 + 1 = 2 * (j + 1) + 2 by omega,
            show 2 * (j + 1) + 1 - 1 = 2 * j + 2 by omega,
            hgEven (j + 1), hgEven j, hgOdd (j + 1), hδOdd (j + 1)]
          exact hStateCurrentSucc j
  have hStateRatioQuarter (j : ℕ) :
      ‖(stateAt j).current‖ / ‖(stateAt j).previous‖ ≤ (1 : ℝ) / 4 := by
    cases j with
    | zero =>
        rw [hStateZero]
        exact seed.first_ratio_le
    | succ j =>
        rw [hStateSucc]
        exact (stepAt j).even_ratio_le.trans (hηLe _)
  have hRatioQuarter (k : ℕ) : ‖g (k + 1)‖ / ‖g k‖ ≤ (1 : ℝ) / 4 := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · cases j with
      | zero =>
          rw [show 2 * 0 + 1 = 1 by norm_num, show 2 * 0 = 0 by norm_num,
            hgOne, hgZero, hStateZero, seed.previous_eq]
          simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
            Real.sqrt_sq_eq_abs, abs_of_pos seed.a_pos, abs_of_pos seed.b_pos]
            using seed.initial_ratio_le
      | succ j =>
          rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega,
            show 2 * (j + 1) = 2 * j + 2 by omega,
            show 2 * j + 3 = 2 * (j + 1) + 1 by omega,
            hgOdd (j + 1), hgEven j, hStateSucc]
          exact (stepAt j).odd_ratio_le.trans (hηLe _)
    · rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega, hgEven j, hgOdd j]
      exact hStateRatioQuarter j
  have hRadiusSuccLt (k : ℕ) : ‖g (k + 1)‖ < ‖g k‖ := by
    have hCurrentPos : 0 < ‖g k‖ := norm_pos_iff.mpr (hgNonzero k)
    have hScaled := (div_le_iff₀ hCurrentPos).mp (hRatioQuarter k)
    nlinarith [norm_pos_iff.mpr (hgNonzero (k + 1))]
  have hRadiusStrictAnti : StrictAnti (fun k ↦ ‖g k‖) :=
    strictAnti_nat_of_succ_lt hRadiusSuccLt
  have hInitialRadius : ‖g 0‖ = seed.a := by
    rw [hgZero]
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
      Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero]
    rw [abs_of_pos seed.a_pos, zero_pow (by norm_num), add_zero]
    exact Real.sqrt_sq seed.a_pos.le
  have hGeometricRadius (k : ℕ) : ‖g k‖ ≤ seed.a * ((1 : ℝ) / 4) ^ k := by
    induction k with
    | zero => rw [pow_zero, mul_one, hInitialRadius]
    | succ k ih =>
        have hCurrentPos : 0 < ‖g k‖ := norm_pos_iff.mpr (hgNonzero k)
        have hStep := (div_le_iff₀ hCurrentPos).mp (hRatioQuarter k)
        calc
          ‖g (k + 1)‖ ≤ ‖g k‖ * ((1 : ℝ) / 4) := by
            simpa only [mul_comm] using hStep
          _ ≤ (seed.a * ((1 : ℝ) / 4) ^ k) * ((1 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right ih (by norm_num)
          _ = seed.a * ((1 : ℝ) / 4) ^ (k + 1) := by rw [pow_succ]; ring
  have hGeometricTendsto :
      Filter.Tendsto (fun k : ℕ ↦ seed.a * ((1 : ℝ) / 4) ^ k)
        Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)))
  have hRadiusTendsto : Filter.Tendsto (fun k ↦ ‖g k‖) Filter.atTop (𝓝 0) := by
    exact squeeze_zero' (Filter.Eventually.of_forall (fun k ↦ norm_nonneg (g k)))
      (Filter.Eventually.of_forall hGeometricRadius) hGeometricTendsto
  have hRatioTail (k : ℕ) (hk : 2 ≤ k) : ‖g (k + 1)‖ / ‖g k‖ ≤ η k := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · cases j with
      | zero => omega
      | succ j =>
          rw [show 2 * (j + 1) + 1 = 2 * (j + 1) + 1 by rfl,
            show 2 * (j + 1) = 2 * j + 2 by omega]
          rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by omega,
            hgOdd (j + 1), hgEven j, hStateSucc]
          exact (stepAt j).odd_ratio_le
    · cases j with
      | zero => omega
      | succ j =>
          rw [show 2 * (j + 1) + 1 + 1 = 2 * (j + 1) + 2 by omega,
            hgEven (j + 1), hgOdd (j + 1), hStateSucc]
          exact (stepAt j).even_ratio_le
  have hηSummable : Summable η := by
    have hGeometric : Summable (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    simpa only [η] using hGeometric.mul_left (σ / 16)
  have hRatioSummable : Summable (fun k ↦ ‖g (k + 1)‖ / ‖g k‖) := by
    have hTail : Summable (fun k ↦ ‖g (k + 2 + 1)‖ / ‖g (k + 2)‖) := by
      apply Summable.of_nonneg_of_le
      · exact fun k ↦ div_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact fun k ↦ hRatioTail (k + 2) (by omega)
      · exact (summable_nat_add_iff 2).mpr hηSummable
    exact (summable_nat_add_iff 2).mp hTail
  have hRatioTendsto :
      Filter.Tendsto (fun k ↦ ‖g (k + 1)‖ / ‖g k‖) Filter.atTop (𝓝 0) :=
    hRatioSummable.tendsto_atTop_zero
  have hηLeSigma (n : ℕ) : η n ≤ σ := by
    have hPowLe : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      η n ≤ (σ / 16) * 1 := by
        exact mul_le_mul_of_nonneg_left hPowLe (div_nonneg hσPos.le (by norm_num))
      _ ≤ σ := by nlinarith
  have hEvenPerturbationRatio (j : ℕ) :
      |(stepAt j).evenPerturbation| / ‖(stateAt j).current‖ ≤ σ := by
    have hCurrentPos : 0 < ‖(stateAt j).current‖ :=
      norm_pos_iff.mpr (stateAt j).current_ne
    have hCancellationBudget :=
      (stateAt j).cancellation_le.trans (min_le_right _ _)
    have hPerturbationUpper := (stepAt j).evenPerturbation_bounds.2
    have hRaw :
        |(stepAt j).evenPerturbation| ≤
          (2 / 3 : ℝ) * η (2 * j + 3) * ‖(stateAt j).current‖ := by
      calc
        |(stepAt j).evenPerturbation| ≤
            (3 / 2 : ℝ) *
              |parallelCoefficient (stateAt j).previous (stateAt j).current /
                tangentCoefficient EuclideanPlane.orientation (stateAt j).previous
                  (stateAt j).current| := hPerturbationUpper
        _ ≤ (3 / 2 : ℝ) *
            ((4 / 9 : ℝ) * η (2 * j + 3) * ‖(stateAt j).current‖) :=
          mul_le_mul_of_nonneg_left hCancellationBudget (by norm_num)
        _ = (2 / 3 : ℝ) * η (2 * j + 3) * ‖(stateAt j).current‖ := by ring
    rw [div_le_iff₀ hCurrentPos]
    exact hRaw.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [hηLeSigma (2 * j + 3)]) hCurrentPos.le)
  have hOddPerturbationRatio (j : ℕ) :
      |(stateAt (j + 1)).previousPerturbation| /
          ‖(stateAt (j + 1)).previous‖ ≤ σ := by
    have hPreviousPos : 0 < ‖(stateAt (j + 1)).previous‖ :=
      norm_pos_iff.mpr (stateAt (j + 1)).previous_ne
    have hPowerBound :
        |(stateAt (j + 1)).previousPerturbation| ≤
          ‖(stateAt (j + 1)).previous‖ ^ (j + 3) := by
      rw [hStateSucc]
      exact (stepAt j).oddPerturbation_power_le
    have hDivBound :
        |(stateAt (j + 1)).previousPerturbation| /
            ‖(stateAt (j + 1)).previous‖ ≤
          ‖(stateAt (j + 1)).previous‖ ^ (j + 2) := by
      rw [div_le_iff₀ hPreviousPos]
      calc
        |(stateAt (j + 1)).previousPerturbation| ≤
            ‖(stateAt (j + 1)).previous‖ ^ (j + 3) := hPowerBound
        _ = ‖(stateAt (j + 1)).previous‖ ^ (j + 2) *
            ‖(stateAt (j + 1)).previous‖ := by
          rw [show j + 3 = (j + 2) + 1 by omega, pow_succ]
    have hBasePower :
        ‖(stateAt (j + 1)).previous‖ ^ (j + 2) ≤ seed.a ^ (j + 2) :=
      pow_le_pow_left₀ (norm_nonneg _) (stateAt (j + 1)).previous_norm_le _
    have hExponentPower : seed.a ^ (j + 2) ≤ seed.a ^ 2 :=
      pow_le_pow_of_le_one seed.a_pos.le seed.a_lt_one.le (by omega)
    exact hDivBound.trans (hBasePower.trans (hExponentPower.trans seed.a_sq_le))
  have hPerturbationRatio (k : ℕ) : |δ k| / ‖g k‖ ≤ σ := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · cases j with
      | zero =>
          rw [show 2 * 0 = 0 by norm_num, hδZero, hInitialRadius,
            abs_of_pos seed.b_pos]
          exact seed.initial_perturbation_ratio_le
      | succ j =>
          rw [show 2 * (j + 1) = 2 * j + 2 by omega, hδEven j, hgEven j]
          exact hEvenPerturbationRatio j
    · cases j with
      | zero =>
          rw [show 2 * 0 + 1 = 1 by norm_num, hδOne, hgOne, hStateZero]
          rw [seed.previous_eq]
          simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
            Real.sqrt_sq_eq_abs, abs_of_pos seed.b_pos]
            using seed.first_perturbation_ratio_le
      | succ j =>
          rw [hδOdd (j + 1), hgOdd (j + 1)]
          exact hOddPerturbationRatio j
  have hEvenPerturbationPower (j : ℕ) :
      |(stepAt j).evenPerturbation| ≤
        (3 / 2 : ℝ) * ‖(stateAt j).current‖ ^ (j + 4) := by
    exact (stepAt j).evenPerturbation_bounds.2.trans
      (mul_le_mul_of_nonneg_left
        ((stateAt j).cancellation_le.trans (min_le_left _ _)) (by norm_num))
  have hOddPerturbationPower (j : ℕ) :
      |(stateAt (j + 1)).previousPerturbation| ≤
        ‖(stateAt (j + 1)).previous‖ ^ (j + 3) := by
    rw [hStateSucc]
    exact (stepAt j).oddPerturbation_power_le
  have hEvenRadiusTendsto :
      Filter.Tendsto (fun n ↦ ‖g (2 * n)‖) Filter.atTop (𝓝 0) := by
    apply hRadiusTendsto.comp
    apply Filter.tendsto_atTop.2
    intro N
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by omega⟩
  have hOddRadiusTendsto :
      Filter.Tendsto (fun n ↦ ‖g (2 * n + 1)‖) Filter.atTop (𝓝 0) := by
    apply hRadiusTendsto.comp
    apply Filter.tendsto_atTop.2
    intro N
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by omega⟩
  have hFlat (m : ℕ) :
      (fun k ↦ |δ k|) =o[Filter.atTop] (fun k ↦ ‖g k‖ ^ m) := by
    have hEvenBigO :
        (fun n ↦ |δ (2 * n)|) =O[Filter.atTop]
          (fun n ↦ ‖g (2 * n)‖ ^ (m + 1)) := by
      apply Asymptotics.IsBigO.of_bound (3 / 2 : ℝ)
      apply Filter.eventually_atTop.mpr
      refine ⟨m + 1, ?_⟩
      intro n hn
      cases n with
      | zero => omega
      | succ j =>
          have hBaseLeOne : ‖(stateAt j).current‖ ≤ 1 :=
            (stateAt j).current_norm_le.trans seed.a_lt_one.le
          have hPowerLe :
              ‖(stateAt j).current‖ ^ (j + 4) ≤
                ‖(stateAt j).current‖ ^ (m + 1) :=
            pow_le_pow_of_le_one (norm_nonneg _) hBaseLeOne (by omega)
          rw [show 2 * (j + 1) = 2 * j + 2 by omega, hδEven j, hgEven j]
          simpa only [Real.norm_eq_abs, abs_abs, abs_pow, abs_norm] using
            hEvenPerturbationPower j |>.trans
              (mul_le_mul_of_nonneg_left hPowerLe (by norm_num))
    have hOddBigO :
        (fun n ↦ |δ (2 * n + 1)|) =O[Filter.atTop]
          (fun n ↦ ‖g (2 * n + 1)‖ ^ (m + 1)) := by
      apply Asymptotics.IsBigO.of_bound 1
      apply Filter.eventually_atTop.mpr
      refine ⟨m + 1, ?_⟩
      intro n hn
      cases n with
      | zero => omega
      | succ j =>
          have hBaseLeOne : ‖(stateAt (j + 1)).previous‖ ≤ 1 :=
            (stateAt (j + 1)).previous_norm_le.trans seed.a_lt_one.le
          have hPowerLe :
              ‖(stateAt (j + 1)).previous‖ ^ (j + 3) ≤
                ‖(stateAt (j + 1)).previous‖ ^ (m + 1) :=
            pow_le_pow_of_le_one (norm_nonneg _) hBaseLeOne (by omega)
          rw [hδOdd (j + 1), hgOdd (j + 1)]
          simpa only [one_mul, Real.norm_eq_abs, abs_abs, abs_pow, abs_norm] using
            (hOddPerturbationPower j).trans hPowerLe
    have hEvenPowerLittleO :
        (fun n ↦ ‖g (2 * n)‖ ^ (m + 1)) =o[Filter.atTop]
          (fun n ↦ ‖g (2 * n)‖ ^ m) :=
      (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self m)).comp_tendsto hEvenRadiusTendsto
    have hOddPowerLittleO :
        (fun n ↦ ‖g (2 * n + 1)‖ ^ (m + 1)) =o[Filter.atTop]
          (fun n ↦ ‖g (2 * n + 1)‖ ^ m) :=
      (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self m)).comp_tendsto hOddRadiusTendsto
    exact Asymptotics.IsLittleO.of_even_odd
      (hEvenBigO.trans_isLittleO hEvenPowerLittleO)
      (hOddBigO.trans_isLittleO hOddPowerLittleO)
  -- The strict radius drop supplies the distinctness required by the separation API.
  have hDistinct (k : ℕ) (hk : 0 < k) : g k ≠ g (k - 1) := by
    intro heq
    have hDrop := hRadiusSuccLt (k - 1)
    have hkSucc : k - 1 + 1 = k := by omega
    rw [hkSucc, heq] at hDrop
    exact lt_irrefl _ hDrop
  have hPreStep (k : ℕ) (hk : 0 < k) :
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (perturbation EuclideanPlane.orientation (g (k - 1)) (δ (k - 1))) := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · cases j with
      | zero => simp only [lt_self_iff_false] at hk
      | succ j =>
          rw [show 2 * (j + 1) = 2 * j + 2 by omega,
            show 2 * j + 2 - 1 = 2 * j + 1 by omega, hgEven j, hgOdd j, hδOdd j]
          exact (stateAt j).preStep
    · cases j with
      | zero =>
          rw [show 2 * 0 + 1 = 1 by norm_num, show 1 - 1 = 0 by norm_num,
            hgOne, hStateZero, seed.previous_eq, hgZero, hδZero]
          exact seed.initialPreStep
      | succ j =>
          rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega,
            show 2 * j + 3 - 1 = 2 * j + 2 by omega,
            show 2 * j + 3 = 2 * (j + 1) + 1 by omega,
            hgOdd (j + 1), hgEven j, hδEven j, hStateSucc]
          exact (stepAt j).previousPreStep
  have hScaleNonzero (k : ℕ) (hk : 0 < k) :
      scale EuclideanPlane.orientation (g (k - 1)) (g k) (δ k) ≠ 0 := by
    intro hScale
    apply hgNonzero (k + 1)
    rw [hRecurrence k hk, next_apply, hScale, zero_smul]
  have hInitialSeparation :
      0 < angularSeparation EuclideanPlane.orientation (g 0) (g 1) := by
    rw [hgZero, hgOne, hStateZero, seed.previous_eq]
    exact seed.initialSeparationPos
  let Dmin := angleLowerBound EuclideanPlane.orientation g
  have hDminPos : 0 < Dmin := by
    exact angleLowerBound_pos EuclideanPlane.orientation g hgNonzero hRatioSummable
      hInitialSeparation
  have hTangentLower (k : ℕ) (hk : 0 < k) :
      Dmin ≤ |tangentCoefficient EuclideanPlane.orientation (g (k - 1)) (g k)| := by
    exact angleLowerBound_le_abs_tangentCoefficient EuclideanPlane.orientation g δ
      hgNonzero hDistinct hPreStep hScaleNonzero hRecurrence hInitialSeparation
      hRatioSummable k hk
  let cancellationRatio : ℕ → ℝ := fun j ↦
    |parallelCoefficient (stateAt j).previous (stateAt j).current /
      tangentCoefficient EuclideanPlane.orientation (stateAt j).previous
        (stateAt j).current| / ‖(stateAt j).current‖
  have hCancellationRatioPos (j : ℕ) : 0 < cancellationRatio j := by
    exact div_pos (stateAt j).cancellation_pos
      (norm_pos_iff.mpr (stateAt j).current_ne)
  have hLogMultiplicativeBounds (j : ℕ) :
      (Dmin / 4) * ‖(stateAt (j + 1)).previous‖ * cancellationRatio j ≤
          ‖(stateAt (j + 1)).current‖ ∧
        ‖(stateAt (j + 1)).current‖ ≤
          (9 / 4 : ℝ) * ‖(stateAt (j + 1)).previous‖ * cancellationRatio j := by
    have hEvenBounds := (stepAt j).evenPerturbation_bounds
    have hRetainedBounds :
        ‖(stateAt (j + 1)).current‖ ∈ Set.Icc
          (|parallelCoefficient (stateAt j).current (stateAt (j + 1)).previous| / 2)
          ((3 / 2 : ℝ) *
            |parallelCoefficient (stateAt j).current (stateAt (j + 1)).previous|) := by
      rw [hStateSucc]
      exact (stepAt j).retainedRadius_bounds
    have hCoefficientFormula :
        |parallelCoefficient (stateAt j).current (stateAt (j + 1)).previous| =
          |tangentCoefficient EuclideanPlane.orientation (stateAt j).current
              (stateAt (j + 1)).previous| *
            (|(stepAt j).evenPerturbation| * ‖(stateAt (j + 1)).previous‖ /
              ‖(stateAt j).current‖) := by
      rw [hStateSucc]
      exact (stepAt j).retainedCoefficient_eq
    have hTangentLowerState :
        Dmin ≤ |tangentCoefficient EuclideanPlane.orientation (stateAt j).current
          (stateAt (j + 1)).previous| := by
      have h := hTangentLower (2 * j + 3) (by omega)
      rw [show 2 * j + 3 - 1 = 2 * j + 2 by omega,
        show 2 * j + 3 = 2 * (j + 1) + 1 by omega, hgEven j, hgOdd (j + 1)] at h
      exact h
    have hOddDistinct : (stateAt (j + 1)).previous ≠ (stateAt j).current := by
      have h := hDistinct (2 * j + 3) (by omega)
      rw [show 2 * j + 3 - 1 = 2 * j + 2 by omega,
        show 2 * j + 3 = 2 * (j + 1) + 1 by omega, hgEven j, hgOdd (j + 1)] at h
      exact h
    have hTangentUpper :
        |tangentCoefficient EuclideanPlane.orientation (stateAt j).current
          (stateAt (j + 1)).previous| ≤ 1 :=
      abs_tangentCoefficient_le_one EuclideanPlane.orientation (stateAt j).current
        (stateAt (j + 1)).previous (stateAt (j + 1)).previous_ne hOddDistinct
    have hRadiusRatioNonneg :
        0 ≤ ‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖ :=
      div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hLowerProduct :
        Dmin *
            ((1 / 2 : ℝ) *
              |parallelCoefficient (stateAt j).previous (stateAt j).current /
                tangentCoefficient EuclideanPlane.orientation (stateAt j).previous
                  (stateAt j).current|) *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖) ≤
          |tangentCoefficient EuclideanPlane.orientation (stateAt j).current
              (stateAt (j + 1)).previous| * |(stepAt j).evenPerturbation| *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖) := by
      apply mul_le_mul_of_nonneg_right _ hRadiusRatioNonneg
      exact (mul_le_mul_of_nonneg_left hEvenBounds.1 hDminPos.le).trans
        (mul_le_mul_of_nonneg_right hTangentLowerState (abs_nonneg _))
    have hUpperProduct :
        |tangentCoefficient EuclideanPlane.orientation (stateAt j).current
              (stateAt (j + 1)).previous| * |(stepAt j).evenPerturbation| *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖) ≤
          (3 / 2 : ℝ) *
            |parallelCoefficient (stateAt j).previous (stateAt j).current /
              tangentCoefficient EuclideanPlane.orientation (stateAt j).previous
                (stateAt j).current| *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖) := by
      apply mul_le_mul_of_nonneg_right _ hRadiusRatioNonneg
      exact (mul_le_mul_of_nonneg_right hTangentUpper (abs_nonneg _)).trans
        (by simpa only [one_mul] using hEvenBounds.2)
    constructor
    · calc
        (Dmin / 4) * ‖(stateAt (j + 1)).previous‖ * cancellationRatio j =
            (Dmin * ((1 / 2 : ℝ) *
              |parallelCoefficient (stateAt j).previous (stateAt j).current /
                tangentCoefficient EuclideanPlane.orientation (stateAt j).previous
                  (stateAt j).current|) *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖)) / 2 := by
          dsimp only [cancellationRatio]
          ring
        _ ≤ (|tangentCoefficient EuclideanPlane.orientation (stateAt j).current
              (stateAt (j + 1)).previous| * |(stepAt j).evenPerturbation| *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖)) / 2 :=
          div_le_div_of_nonneg_right hLowerProduct (by norm_num)
        _ = |parallelCoefficient (stateAt j).current
              (stateAt (j + 1)).previous| / 2 := by
          rw [hCoefficientFormula]
          ring
        _ ≤ ‖(stateAt (j + 1)).current‖ := hRetainedBounds.1
    · calc
        ‖(stateAt (j + 1)).current‖ ≤
            (3 / 2 : ℝ) *
              |parallelCoefficient (stateAt j).current (stateAt (j + 1)).previous| :=
          hRetainedBounds.2
        _ = (3 / 2 : ℝ) *
            (|tangentCoefficient EuclideanPlane.orientation (stateAt j).current
                (stateAt (j + 1)).previous| * |(stepAt j).evenPerturbation| *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖)) := by
          rw [hCoefficientFormula]
          ring
        _ ≤ (3 / 2 : ℝ) *
            ((3 / 2 : ℝ) *
              |parallelCoefficient (stateAt j).previous (stateAt j).current /
                tangentCoefficient EuclideanPlane.orientation (stateAt j).previous
                  (stateAt j).current| *
              (‖(stateAt (j + 1)).previous‖ / ‖(stateAt j).current‖)) :=
          mul_le_mul_of_nonneg_left hUpperProduct (by norm_num)
        _ = (9 / 4 : ℝ) * ‖(stateAt (j + 1)).previous‖ * cancellationRatio j := by
          dsimp only [cancellationRatio]
          ring
  have hShiftedLogRatio :
      Filter.Tendsto
        (fun j ↦ (-Real.log ‖(stateAt (j + 1)).current‖) /
          (-Real.log ‖(stateAt (j + 1)).previous‖)) Filter.atTop (nhds 1) := by
    apply tendsto_logRatio_one_of_multiplicativeBounds
        (fun j ↦ ‖(stateAt (j + 1)).previous‖)
        (fun j ↦ ‖(stateAt (j + 1)).current‖) cancellationRatio
        (Dmin / 4) (9 / 4 : ℝ)
    · exact fun j ↦ norm_pos_iff.mpr (stateAt (j + 1)).previous_ne
    · exact fun j ↦ norm_pos_iff.mpr (stateAt (j + 1)).current_ne
    · exact hCancellationRatioPos
    · exact fun j ↦ (stateAt (j + 1)).previous_norm_le.trans_lt seed.a_lt_one
    · exact div_pos hDminPos (by norm_num)
    · norm_num
    · exact hLogMultiplicativeBounds
    · intro j
      have h := (stepAt j).logControl
      rw [← hStateSucc] at h
      exact h
  have hOddLogRatio :
      Filter.Tendsto
        (fun j ↦ (-Real.log ‖g (2 * j + 2)‖) / (-Real.log ‖g (2 * j + 1)‖))
        Filter.atTop (nhds 1) := by
    have hAllStates :
        Filter.Tendsto
          (fun j ↦ (-Real.log ‖(stateAt j).current‖) /
            (-Real.log ‖(stateAt j).previous‖)) Filter.atTop (nhds 1) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mp hShiftedLogRatio
    simpa only [hgEven, hgOdd] using hAllStates
  -- The remaining fields are assembled from the cancellation and logarithmic estimates.
  refine ⟨g, δ, seed.a, seed.b, IsAlternatingScale.ofConditions hgNonzero seed.a_pos
    seed.b_pos ?_ ?_ hδZero ?_ ?_ hRecurrence ?_ ?_ ?_ ?_ ?_ ?_ hRatioQuarter ?_⟩
  · exact congrArg WithLp.ofLp hgZero
  · exact congrArg WithLp.ofLp (hgOne.trans (hStateZero ▸ seed.previous_eq))
  · rw [hδOne, hStateZero]
    exact abs_pos.mpr seed.state.previousPerturbation_ne
  · rw [hδOne, hStateZero]
    exact seed.first_perturbation_lt
  · exact hRadiusStrictAnti
  · exact hRadiusTendsto
  · exact hRatioTendsto
  · exact hRatioSummable
  · exact hFlat
  · exact hOddLogRatio
  · exact hPerturbationRatio

end PlanarGradient
