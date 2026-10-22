/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_28

section Chapter01Exercise19

-- Domain sample for this exercise:
-- * source-facing layer in this file: the explicit `ℝ² → ℝ` counterexample
-- * chapter core/canonical owners: `gateauxDifferentiableWithinAt_of_hasFDerivAt`,
--   `exists_gateauxDifferentiableAt_not_hasFDerivAt`
-- * chapter Gateaux bridge/view owner reused below: `IsGateauxDerivativeWithinAt`

local notation "Point2" => EuclideanSpace ℝ (Fin 2)

/- Chapter01 Exercise 1.9 (1): the general Fréchet-to-Gateaux implication is already owned in
`Definition_1_2_28` at the intrinsic normed-space level. -/
#check gateauxDifferentiableWithinAt_of_hasFDerivAt

/- Chapter01 Exercise 1.9 (3), general form: the converse fails in general, already owned in
`Definition_1_2_28` as an existential counterexample theorem. -/
#check exists_gateauxDifferentiableAt_not_hasFDerivAt

/-- An explicit `EuclideanSpace ℝ (Fin 2) → ℝ` map whose directional derivatives at `0`
are all zero, while the map is not continuous at `0`. -/
noncomputable def gateauxNotFrechetCounterexample :
    Point2 → ℝ :=
  fun x ↦
    if x = 0 then 0 else (x 0) ^ 3 * x 1 / ((x 0) ^ 6 + (x 1) ^ 2)

/-- A Gateaux-derivative formulation for Chapter01 Exercise 1.9: the explicit
counterexample has Gateaux derivative at `0` given by the zero continuous linear map. -/
theorem isGateauxDerivativeWithinAt_univ_gateauxNotFrechetCounterexample_zero :
    IsGateauxDerivativeWithinAt ℝ Set.univ gateauxNotFrechetCounterexample 0 0 := by
  -- Repackage the imported scalar line derivatives into the chapter's Gateaux owner.
  intro d
  simpa [IsGateauxDerivativeWithinAt, HasLineDerivWithinAt,
    gateauxNotFrechetCounterexample,
    gateauxNotFrechetCounterexampleScalar] using
    gateauxCounterexampleScalar_hasDerivAt_zeroAlongLine d

/-- The counterexample is therefore Gateaux differentiable at `0` on `Set.univ`. -/
theorem gateauxDifferentiableWithinAt_univ_gateauxNotFrechetCounterexample :
    SunYuanGateauxDifferentiableWithinAt ℝ Set.univ gateauxNotFrechetCounterexample 0 := by
  exact ⟨isOpen_univ, by simp, 0,
    isGateauxDerivativeWithinAt_univ_gateauxNotFrechetCounterexample_zero⟩

/-- Helper for Chapter01 Exercise 1.9: along the imported cubic path, the local counterexample
is constantly `1 / 2` away from the origin. -/
lemma gateauxNotFrechetCounterexample_path_eq_half
    {u : ℝ} (hu : u ≠ 0) :
    gateauxNotFrechetCounterexample (gateauxCounterexampleCubicPath u) = (1 / 2 : ℝ) := by
  -- Normalize the local owner to the chapter-level scalar counterexample.
  simpa [gateauxNotFrechetCounterexample, gateauxNotFrechetCounterexampleScalar] using
    gateauxCounterexampleScalar_path_eq_half hu

/-- Helper for Chapter01 Exercise 1.9: the explicit counterexample is not continuous at `0`. -/
lemma not_continuousAt_gateauxNotFrechetCounterexample :
    ¬ ContinuousAt gateauxNotFrechetCounterexample 0 := by
  intro hcont
  -- Compose the assumed continuity with the cubic path that stays at height `1 / 2`.
  have hpathAt : ContinuousAt gateauxCounterexampleCubicPath 0 := by
    -- The cubic path is a sum of continuous coordinate injections.
    unfold gateauxCounterexampleCubicPath
    exact (continuousAt_id.smul_const _).add
      ((hasDerivAt_pow 3 (0 : ℝ)).continuousAt.smul_const _)
  have hpathZeroVec : gateauxCounterexampleCubicPath 0 = (0 : Point2) := by
    simp [gateauxCounterexampleCubicPath]
  have hpathCont :
      ContinuousAt
        (fun u : ℝ ↦ gateauxNotFrechetCounterexample (gateauxCounterexampleCubicPath u))
        0 := by
    -- Transport continuity of the counterexample along the cubic path through the origin.
    have houter :
        ContinuousAt gateauxNotFrechetCounterexample (gateauxCounterexampleCubicPath 0) := by
      simpa [hpathZeroVec] using hcont
    exact ContinuousAt.comp houter hpathAt
  have hpathZero :
      gateauxNotFrechetCounterexample (gateauxCounterexampleCubicPath 0) = 0 := by
    simp [gateauxCounterexampleCubicPath, gateauxNotFrechetCounterexample]
  have hquarter : (0 : ℝ) < 1 / 4 := by
    norm_num
  let pathValue : ℝ :=
    (fun u : ℝ ↦ gateauxNotFrechetCounterexample (gateauxCounterexampleCubicPath u)) 0
  have hpathValue : pathValue = 0 := by
    simpa [pathValue] using hpathZero
  have hballNhds :
      Metric.ball pathValue (1 / 4) ∈ nhds pathValue := by
    -- Rewrite the path value at `0` to the origin before applying the metric neighborhood fact.
    simpa [hpathValue] using (Metric.ball_mem_nhds (0 : ℝ) hquarter)
  rcases Metric.mem_nhds_iff.mp (hpathCont hballNhds) with ⟨δ, hδpos, hδ⟩
  have hhalf_mem : (δ / 2 : ℝ) ∈ Metric.ball (0 : ℝ) δ := by
    simp [Metric.mem_ball, abs_of_nonneg, hδpos.le, half_lt_self hδpos]
  have himage_mem := hδ hhalf_mem
  have hhalf_ne : (δ / 2 : ℝ) ≠ 0 := by
    positivity
  have hvalue :
      gateauxNotFrechetCounterexample (gateauxCounterexampleCubicPath (δ / 2)) =
        (1 / 2 : ℝ) :=
    gateauxNotFrechetCounterexample_path_eq_half hhalf_ne
  have : (1 / 2 : ℝ) ∈ Metric.ball (0 : ℝ) (1 / 4) := by
    simpa [Metric.mem_ball, hpathValue, hvalue] using himage_mem
  have hnotmem : (1 / 2 : ℝ) ∉ Metric.ball (0 : ℝ) (1 / 4) := by
    norm_num [Metric.mem_ball, abs_of_nonneg]
  exact hnotmem this

/-- Chapter01 Exercise 1.9 (3): the converse of `(1)` fails because
`gateauxNotFrechetCounterexample` is Gateaux differentiable but not Fréchet
differentiable at `0`. -/
theorem not_differentiableAt_gateauxNotFrechetCounterexample :
    ¬ DifferentiableAt ℝ gateauxNotFrechetCounterexample 0 := by
  -- Route correction: refute Fréchet differentiability through the induced continuity claim.
  intro hdiff
  exact not_continuousAt_gateauxNotFrechetCounterexample hdiff.continuousAt

end Chapter01Exercise19
