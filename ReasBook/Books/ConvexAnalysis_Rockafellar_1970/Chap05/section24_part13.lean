/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part12

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

-- Proof sketch: restrict the finite convex function to the nonempty open interval `(a, b)` and
-- apply the one-dimensional monotone-primitive theorem to the right-derivative profile and then
-- to the left-derivative profile. The resulting normalized integral primitives differ from `f`
-- only by additive constants, so evaluating at `x` and `y` yields both interval-integral
-- formulas for `f y - f x`.
/-- Corollary 5.24.1: if `f` is a finite convex function on the nonempty open interval `(a, b)`,
then for any `x, y ∈ (a, b)`,
`f y - f x = ∫ t in x..y, derivWithin f (Set.Ioi t) t` and
`f y - f x = ∫ t in x..y, derivWithin f (Set.Iio t) t`. -/
theorem convexOn_Ioo_sub_eq_intervalIntegral_rightDerivWithin_and_leftDerivWithin
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ioo a b) f)
    {x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    f y - f x = ∫ t in x..y, derivWithin f (Set.Ioi t) t ∧
      f y - f x = ∫ t in x..y, derivWithin f (Set.Iio t) t := by
  have hsubset : Set.uIcc x y ⊆ Set.Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le (lt_min hx.1 hy.1) hz.1,
      lt_of_le_of_lt hz.2 (max_lt hx.2 hy.2)⟩
  have hcontIoo : ContinuousOn f (Set.Ioo a b) := hf.continuousOn isOpen_Ioo
  have hcont : ContinuousOn f (Set.uIcc x y) := hcontIoo.mono hsubset
  have hderiv :
      ∀ t ∈ Set.Ioo (min x y) (max x y),
        HasDerivWithinAt f (derivWithin f (Set.Ioi t) t) (Set.Ioi t) t := by
    intro t ht
    have ht' : t ∈ interior (Set.Ioo a b) := by
      have : t ∈ Set.Ioo a b := ⟨lt_of_lt_of_le (lt_min hx.1 hy.1) (le_of_lt ht.1),
        lt_of_le_of_lt (le_of_lt ht.2) (max_lt hx.2 hy.2)⟩
      simpa using this
    exact hf.hasDerivWithinAt_rightDeriv_of_mem_interior ht'
  have hmonoIoo : MonotoneOn (fun t => derivWithin f (Set.Ioi t) t) (Set.Ioo a b) := by
    simpa using hf.monotoneOn_rightDeriv
  have hmono : MonotoneOn (fun t => derivWithin f (Set.Ioi t) t) (Set.uIcc x y) :=
    hmonoIoo.mono hsubset
  have hint : IntervalIntegrable (fun t => derivWithin f (Set.Ioi t) t) MeasureTheory.volume x y := by
    exact hmono.intervalIntegrable
  have hRight : f y - f x = ∫ t in x..y, derivWithin f (Set.Ioi t) t := by
    simpa using (intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint).symm
  let negL : ℝ →ₗ[ℝ] ℝ := (-1 : ℝ) • LinearMap.id
  have hConvNeg' : ConvexOn ℝ (negL ⁻¹' Set.Ioo a b) (f ∘ negL) := hf.comp_linearMap negL
  have hConvNeg : ConvexOn ℝ (Set.Ioo (-b) (-a)) (fun t : ℝ => f (-t)) := by
    convert hConvNeg' using 1
    · ext t
      simp [negL, LinearMap.id_apply]
      constructor <;> intro h <;> constructor <;> linarith
    · ext t
      simp [negL, LinearMap.id_apply]
  have hxNeg : -y ∈ Set.Ioo (-b) (-a) := by
    constructor <;> linarith [hy.1, hy.2]
  have hyNeg : -x ∈ Set.Ioo (-b) (-a) := by
    constructor <;> linarith [hx.1, hx.2]
  have hsubsetNeg : Set.uIcc (-y) (-x) ⊆ Set.Ioo (-b) (-a) := by
    intro z hz
    exact ⟨lt_of_lt_of_le (lt_min hxNeg.1 hyNeg.1) hz.1,
      lt_of_le_of_lt hz.2 (max_lt hxNeg.2 hyNeg.2)⟩
  have hcontNegIoo : ContinuousOn (fun t : ℝ => f (-t)) (Set.Ioo (-b) (-a)) :=
    hConvNeg.continuousOn isOpen_Ioo
  have hcontNeg : ContinuousOn (fun t : ℝ => f (-t)) (Set.uIcc (-y) (-x)) :=
    hcontNegIoo.mono hsubsetNeg
  have hderivNeg :
      ∀ t ∈ Set.Ioo (min (-y) (-x)) (max (-y) (-x)),
        HasDerivWithinAt (fun s : ℝ => f (-s))
          (derivWithin (fun s : ℝ => f (-s)) (Set.Ioi t) t) (Set.Ioi t) t := by
    intro t ht
    have ht' : t ∈ interior (Set.Ioo (-b) (-a)) := by
      have : t ∈ Set.Ioo (-b) (-a) :=
        ⟨lt_of_lt_of_le (lt_min hxNeg.1 hyNeg.1) (le_of_lt ht.1),
          lt_of_le_of_lt (le_of_lt ht.2) (max_lt hxNeg.2 hyNeg.2)⟩
      simpa using this
    exact hConvNeg.hasDerivWithinAt_rightDeriv_of_mem_interior ht'
  have hmonoNegIoo :
      MonotoneOn (fun t => derivWithin (fun s : ℝ => f (-s)) (Set.Ioi t) t)
        (Set.Ioo (-b) (-a)) := by
    simpa using hConvNeg.monotoneOn_rightDeriv
  have hmonoNeg :
      MonotoneOn (fun t => derivWithin (fun s : ℝ => f (-s)) (Set.Ioi t) t)
        (Set.uIcc (-y) (-x)) :=
    hmonoNegIoo.mono hsubsetNeg
  have hintNeg :
      IntervalIntegrable (fun t => derivWithin (fun s : ℝ => f (-s)) (Set.Ioi t) t)
        MeasureTheory.volume (-y) (-x) := by
    exact hmonoNeg.intervalIntegrable
  have hNegIntegral :
      f x - f y =
        ∫ t in (-y)..(-x), derivWithin (fun s : ℝ => f (-s)) (Set.Ioi t) t := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDeriv_right hcontNeg hderivNeg hintNeg).symm
  have hLeftAux : f x - f y = ∫ t in x..y, -derivWithin f (Set.Iio t) t := by
    calc
      f x - f y = ∫ t in (-y)..(-x), derivWithin (fun s : ℝ => f (-s)) (Set.Ioi t) t := by
        simpa using hNegIntegral
      _ = ∫ t in x..y, derivWithin (fun s : ℝ => f (-s)) (Set.Ioi (-t)) (-t) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := fun t : ℝ => derivWithin (fun s : ℝ => f (-s)) (Set.Ioi t) t)
            (a := x) (b := y)).symm
      _ = ∫ t in x..y, -derivWithin f (Set.Iio t) t := by
        refine intervalIntegral.integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro t ht
        simpa using (derivWithin_comp_neg (f := f) (s := Set.Ioi (-t)) (x := -t))
  have hLeft : f y - f x = ∫ t in x..y, derivWithin f (Set.Iio t) t := by
    calc
      f y - f x = - (f x - f y) := by ring
      _ = - ∫ t in x..y, -derivWithin f (Set.Iio t) t := by rw [hLeftAux]
      _ = ∫ t in x..y, derivWithin f (Set.Iio t) t := by
        rw [intervalIntegral.integral_neg]
        simp
  exact ⟨hRight, hLeft⟩

-- Proof sketch: apply Theorem 23.1 to the convex function `y ↦ f'(x; y)`, whose convexity and
-- positive homogeneity come from the same theorem applied to `f` at the base point `x`. The
-- first clause is then exactly the right-hand limit description of the directional derivative of
-- `f'(x; ·)` at `y`, and the inequality follows from sublinearity of `y ↦ f'(x; y)`.
/-- Helper for Proposition 5.24.2: convexity plus positive homogeneity carries real epigraph
upper bounds through vector addition. -/
lemma helperForProposition_5_24_2_midpoint_subadditivity_of_convex_posHom
    {n : ℕ} {D : (Fin n → ℝ) → EReal}
    (hpos : PositivelyHomogeneous D) (hconv : ConvexFunction D)
    {u v : Fin n → ℝ} {μ ν : ℝ}
    (hu : D u ≤ (μ : EReal)) (hv : D v ≤ (ν : EReal)) :
    D (u + v) ≤ ((μ + ν : ℝ) : EReal) := by
  have hconvEp : Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) D) := by
    simpa [ConvexFunction] using hconv
  have htwo_pos : 0 < (2 : ℝ) := by
    norm_num
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by
    norm_num
  have hhalf_sum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by
    norm_num
  -- First double both vectors so their midpoint is exactly `u + v`.
  have hu' : D ((2 : ℝ) • u) ≤ (((2 * μ : ℝ) : ℝ) : EReal) := by
    calc
      D ((2 : ℝ) • u) = ((2 : ℝ) : EReal) * D u := by
        simpa using hpos u 2 htwo_pos
      _ ≤ ((2 : ℝ) : EReal) * (μ : EReal) := by
        gcongr
      _ = (((2 * μ : ℝ) : ℝ) : EReal) := by
        norm_num
  have hv' : D ((2 : ℝ) • v) ≤ (((2 * ν : ℝ) : ℝ) : EReal) := by
    calc
      D ((2 : ℝ) • v) = ((2 : ℝ) : EReal) * D v := by
        simpa using hpos v 2 htwo_pos
      _ ≤ ((2 : ℝ) : EReal) * (ν : EReal) := by
        gcongr
      _ = (((2 * ν : ℝ) : ℝ) : EReal) := by
        norm_num
  have hmemu :
      (((2 : ℝ) • u), 2 * μ) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) D := by
    exact
      epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := (2 : ℝ) • u)
        (μ := 2 * μ) (by simp) hu'
  have hmemv :
      (((2 : ℝ) • v), 2 * ν) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) D := by
    exact
      epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := (2 : ℝ) • v)
        (μ := 2 * ν) (by simp) hv'
  have hmid_mem :
      (1 / 2 : ℝ) • (((2 : ℝ) • u), 2 * μ) + (1 / 2 : ℝ) • (((2 : ℝ) • v), 2 * ν) ∈
        epigraph (Set.univ : Set (Fin n → ℝ)) D := by
    exact hconvEp hmemu hmemv hhalf_nonneg hhalf_nonneg hhalf_sum
  have hmid_ineq :
      D ((1 / 2 : ℝ) • ((2 : ℝ) • u) + (1 / 2 : ℝ) • ((2 : ℝ) • v)) ≤
        ((((1 / 2 : ℝ) * (2 * μ) + (1 / 2 : ℝ) * (2 * ν) : ℝ)) : EReal) := by
    simpa [epigraph] using hmid_mem.2
  have hvec :
      (1 / 2 : ℝ) • ((2 : ℝ) • u) + (1 / 2 : ℝ) • ((2 : ℝ) • v) = u + v := by
    ext i
    ring_nf
    simp
  have hscalar :
      (1 / 2 : ℝ) * (2 * μ) + (1 / 2 : ℝ) * (2 * ν) = μ + ν := by
    ring
  -- Rewrite the midpoint estimate back to the desired sum.
  simpa [hvec, hscalar] using hmid_ineq

/-- Helper for Proposition 5.24.2: an `EReal` lying below every real number must be `⊥`. -/
lemma helperForProposition_5_24_2_eq_bot_of_le_all_reals (q : EReal)
    (hq : ∀ r : ℝ, q ≤ (r : EReal)) :
    q = (⊥ : EReal) := by
  by_cases hqbot : q = (⊥ : EReal)
  · exact hqbot
  by_cases hqtop : q = (⊤ : EReal)
  · have htop_le : (⊤ : EReal) ≤ ((0 : ℝ) : EReal) := by
      simpa [hqtop] using hq 0
    exact (not_top_le_coe 0 htop_le).elim
  have hqReal : (((q.toReal : ℝ)) : EReal) = q := EReal.coe_toReal hqtop hqbot
  have hqShift : q ≤ (((q.toReal - 1 : ℝ)) : EReal) := hq (q.toReal - 1)
  have hreal_le : q.toReal ≤ q.toReal - 1 := by
    rw [← hqReal] at hqShift
    exact_mod_cast hqShift
  linarith

/-- Helper for Proposition 5.24.2: the positive-step quotient at `t = 1` is controlled by the
original directional derivative. -/
lemma helperForProposition_5_24_2_differenceQuotientAt_one_le
    {n : ℕ} {D : (Fin n → ℝ) → EReal}
    (hpos : PositivelyHomogeneous D) (hconv : ConvexFunction D)
    {y z : Fin n → ℝ}
    (hy : D y ≠ (⊤ : EReal) ∧ D y ≠ (⊥ : EReal)) :
    directionalDifferenceQuotientAt D y z 1 ≤ D z := by
  by_cases hzTop : D z = (⊤ : EReal)
  · -- If `D z = ⊤`, the desired upper bound is automatic.
    simpa [hzTop]
  by_cases hzBot : D z = (⊥ : EReal)
  · -- When `D z = ⊥`, convexity plus positive homogeneity force `D (y + z) = ⊥`.
    have hyReal : D y = (((D y).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal hy.1 hy.2).symm
    have hsumBot : D (y + z) = (⊥ : EReal) := by
      apply helperForProposition_5_24_2_eq_bot_of_le_all_reals
      intro r
      have hadd :
          D (y + z) ≤ ((((D y).toReal + (r - (D y).toReal) : ℝ)) : EReal) := by
        have hyUpper : D y ≤ (((D y).toReal : ℝ) : EReal) := by
          rw [hyReal]
          rfl
        have hzUpper : D z ≤ (((r - (D y).toReal : ℝ)) : EReal) := by
          simpa [hzBot]
        exact
          helperForProposition_5_24_2_midpoint_subadditivity_of_convex_posHom
            hpos hconv hyUpper hzUpper
      simpa using hadd
    have hquotBot : directionalDifferenceQuotientAt D y z 1 = (⊥ : EReal) := by
      rw [directionalDifferenceQuotientAt, one_smul, hsumBot]
      simp [hy.1, hy.2]
    simpa [hzBot, hquotBot]
  -- In the finite branch, sublinearity at `y + z` converts directly into the quotient bound.
  have hyReal : D y = (((D y).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hy.1 hy.2).symm
  have hzReal : D z = (((D z).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hzTop hzBot).symm
  have haddReal :
      D (y + z) ≤ ((((D y).toReal + (D z).toReal : ℝ)) : EReal) := by
    have hyUpper : D y ≤ (((D y).toReal : ℝ) : EReal) := by
      rw [hyReal]
      rfl
    have hzUpper : D z ≤ (((D z).toReal : ℝ) : EReal) := by
      rw [hzReal]
      rfl
    exact
      helperForProposition_5_24_2_midpoint_subadditivity_of_convex_posHom
        hpos hconv hyUpper hzUpper
  have haddCoe :
      D (y + z) ≤ ((((D z).toReal : ℝ) : EReal) + (((D y).toReal : ℝ) : EReal)) := by
    have hrealReal : (D y).toReal + (D z).toReal = (D z).toReal + (D y).toReal := by
      ring
    have hreal :
        (((D y).toReal + (D z).toReal : ℝ) : EReal) =
          (((D z).toReal : ℝ) : EReal) + (((D y).toReal : ℝ) : EReal) := by
      rw [show (((D y).toReal + (D z).toReal : ℝ) : EReal) =
          (((D z).toReal + (D y).toReal : ℝ) : EReal) by
            exact congrArg (fun r : ℝ => (r : EReal)) hrealReal]
      rw [EReal.coe_add]
    exact hreal ▸ haddReal
  have hadd :
      D (y + z) ≤ D z + D y := by
    rw [hzReal, hyReal]
    exact haddCoe
  have hquot_le :
      D (y + z) - D y ≤ D z := by
    have hy_not_bot_or : D y ≠ (⊥ : EReal) ∨ D z ≠ (⊤ : EReal) := Or.inl hy.2
    have hy_not_top_or : D y ≠ (⊤ : EReal) ∨ D z ≠ (⊥ : EReal) := Or.inl hy.1
    exact
      (EReal.sub_le_iff_le_add hy_not_bot_or hy_not_top_or).2
        (by simpa [add_comm, add_left_comm, add_assoc] using hadd)
  simpa [directionalDifferenceQuotientAt, one_smul] using hquot_le

/-- Helper for Proposition 5.24.2: the infimum formula from Theorem 23.1 is bounded above by the
`t = 1` positive-step quotient. -/
lemma helperForProposition_5_24_2_iterated_upperDerivative_le_of_quotientAt_one
    {n : ℕ} {D : (Fin n → ℝ) → EReal} {y z : Fin n → ℝ}
    (hsInfEq :
      upperDirectionalDerivativeAt D y z =
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt D y z t)) :
    upperDirectionalDerivativeAt D y z ≤ directionalDifferenceQuotientAt D y z 1 := by
  have hQbdd :
      BddBelow ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt D y z t) := by
    refine ⟨⊥, ?_⟩
    intro q hq
    simp at hq ⊢
  have hone_pos : 0 < (1 : ℝ) := by
    norm_num
  have hone_mem :
      directionalDifferenceQuotientAt D y z 1 ∈
        (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt D y z t := by
    exact ⟨1, hone_pos, rfl⟩
  -- The textbook compares the infimum representation with the concrete quotient at `t = 1`.
  rw [hsInfEq]
  exact csInf_le hQbdd hone_mem

/-- Proposition 5.24.2: if `f` is convex, `f` is finite at `x`, and `f'(x; y)` is finite, then
the directional derivative of the convex function `u ↦ f'(x; u)` at `y` in direction `z` is the
right-hand limit
`lim_{λ ↓ 0} (f'(x; y + λ z) - f'(x; y)) / λ`, and it is bounded above by `f'(x; z)` for every
`z`. -/
theorem upperDirectionalDerivativeAt_iterated_tendsto_and_le {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) {x y : Fin n → ℝ}
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hy : upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) ∧
      upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal)) :
    (∀ z : Fin n → ℝ,
      Filter.Tendsto
        (directionalDifferenceQuotientAt (upperDirectionalDerivativeAt f x) y z)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt (upperDirectionalDerivativeAt f x) y z))) ∧
      ∀ z : Fin n → ℝ,
        upperDirectionalDerivativeAt (upperDirectionalDerivativeAt f x) y z ≤
          upperDirectionalDerivativeAt f x z := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨_hdirF, hposD, hconvD, _hzeroD, _hsymmD⟩
  rcases convex_directionalDerivative_monotone_exists_and_sublinear D hconvD y hy with
    ⟨hiter, _hposIter, _hconvIter, _hzeroIter, _hsymmIter⟩
  refine ⟨?_, ?_⟩
  · intro z
    -- The first assertion is exactly Theorem 23.1 applied to `D = f'(x; ·)` at the point `y`.
    simpa [D] using (hiter z).2.1
  · intro z
    have hupper_le_q1 :
        upperDirectionalDerivativeAt D y z ≤ directionalDifferenceQuotientAt D y z 1 := by
      -- Evaluate the infimum formula at the concrete witness `t = 1`.
      exact
        helperForProposition_5_24_2_iterated_upperDerivative_le_of_quotientAt_one
          ((hiter z).2.2)
    have hq1_le :
        directionalDifferenceQuotientAt D y z 1 ≤ D z := by
      -- Sublinearity of `D` gives the textbook bound on the one-step quotient.
      exact
        helperForProposition_5_24_2_differenceQuotientAt_one_le hposD hconvD
          (y := y) (z := z) hy
    exact le_trans hupper_le_q1 hq1_le

/-- Helper for Corollary 5.24.2: proper convexity packages the interior of the effective domain
as an open convex set on which `f` is finite. -/
lemma helperForCorollary_5_24_2_constantSequenceSetup
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    ConvexFunction f ∧
      IsOpen C ∧
      Convex ℝ C ∧
      (∀ z ∈ C, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal)) := by
  dsimp
  -- First read proper convexity on the whole space as ordinary convexity.
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdomConv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf
  refine ⟨hf, isOpen_interior, hdomConv.interior, ?_⟩
  intro z hz
  -- Interior-domain points are exactly the finite points needed by Theorem 5.24.8.
  have hzDom : z ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := interior_subset hz
  have hz_ne_top : f z ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hzDom
  have hz_ne_bot : f z ≠ (⊥ : EReal) := hproper.2.2 z (by simp)
  exact ⟨hz_ne_top, hz_ne_bot⟩

/-- Helper for Corollary 5.24.2: specialize Theorem 5.24.8 to the constant sequence `fᵢ = f`
and a convergent sequence of pairs `(xᵢ, yᵢ)`. -/
lemma helperForCorollary_5_24_2_pairSequence_limsup_upperDirectionalDerivative
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    {pSeq : ℕ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hp :
      p ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ×ˢ
        (Set.univ : Set (Fin n → ℝ)))
    (hpSeq :
      ∀ i,
        pSeq i ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ×ˢ
          (Set.univ : Set (Fin n → ℝ)))
    (hp_tendsto : Filter.Tendsto pSeq Filter.atTop (nhds p)) :
    Filter.limsup (fun i => upperDirectionalDerivativeAt f (pSeq i).1 (pSeq i).2) Filter.atTop ≤
      upperDirectionalDerivativeAt f p.1 p.2 := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  rcases helperForCorollary_5_24_2_constantSequenceSetup (f := f) hproper with
    ⟨hf, hCopen, hCconv, hf_finite⟩
  have hpoint :
      ∀ z ∈ C, Filter.Tendsto (fun _ : ℕ => f z) Filter.atTop (nhds (f z)) := by
    intro z hz
    -- The constant function sequence converges pointwise trivially.
    simpa using Filter.tendsto_const_nhds
  have hp_tendsto_fst : Filter.Tendsto (fun i => (pSeq i).1) Filter.atTop (nhds p.1) := by
    simpa using (continuous_fst.tendsto p).comp hp_tendsto
  have hp_tendsto_snd : Filter.Tendsto (fun i => (pSeq i).2) Filter.atTop (nhds p.2) := by
    simpa using (continuous_snd.tendsto p).comp hp_tendsto
  have hmain :=
    convexOn_pointwiseLimit_limsup_upperDirectionalDerivative_le_and_eventual_subdifferential_subset
      (C := C) hCopen hCconv hf hf_finite (fun _ => f) (fun _ => hf)
      (fun _ z hz => hf_finite z hz) hp.1 (fun i => (pSeq i).1) (fun i => (hpSeq i).1)
      hp_tendsto_fst hpoint
  -- Now read the `y`-coordinate of the pair sequence into the directional-derivative clause.
  exact hmain.1 p.2 (fun i => (pSeq i).2) hp_tendsto_snd

/-- Helper for Corollary 5.24.2: the pairwise limsup inequality from the constant-sequence
specialization yields upper semicontinuity on `int (dom f) × ℝ^n`. -/
lemma helperForCorollary_5_24_2_upperSemicontinuousOn_upperDirectionalDerivative
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    UpperSemicontinuousOn
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => upperDirectionalDerivativeAt f p.1 p.2)
      (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ×ˢ
        (Set.univ : Set (Fin n → ℝ))) := by
  intro p hp a ha
  let s : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ×ˢ
      (Set.univ : Set (Fin n → ℝ))
  -- Argue by contradiction: otherwise there is a sequence in `𝓝[s] p` whose values stay above `a`.
  by_contra hUpper
  have hfreq_not_lt :
      ∃ᶠ q : (Fin n → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        ¬ upperDirectionalDerivativeAt f q.1 q.2 < a :=
    (Filter.not_eventually.1 hUpper)
  have hfreq :
      ∃ᶠ q : (Fin n → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        a ≤ upperDirectionalDerivativeAt f q.1 q.2 := by
    exact hfreq_not_lt.mono (fun q hq => le_of_not_gt hq)
  have hfreq_mem :
      ∃ᶠ q : (Fin n → ℝ) × (Fin n → ℝ) in nhdsWithin p s,
        a ≤ upperDirectionalDerivativeAt f q.1 q.2 ∧
          q ∈ s := by
    exact hfreq.and_eventually eventually_mem_nhdsWithin
  rcases Filter.exists_seq_forall_of_frequently hfreq_mem with ⟨pSeq, hpSeq_tendsto, hpSeq_spec⟩
  have hpSeq_ge :
      ∀ i, a ≤ upperDirectionalDerivativeAt f (pSeq i).1 (pSeq i).2 := by
    intro i
    exact (hpSeq_spec i).1
  have hpSeq_mem :
      ∀ i,
        pSeq i ∈ s := by
    intro i
    exact (hpSeq_spec i).2
  have hpSeq_tendsto_nhds : Filter.Tendsto pSeq Filter.atTop (nhds p) :=
    hpSeq_tendsto.mono_right nhdsWithin_le_nhds
  have hlimsup :
      Filter.limsup (fun i => upperDirectionalDerivativeAt f (pSeq i).1 (pSeq i).2)
          Filter.atTop ≤
        upperDirectionalDerivativeAt f p.1 p.2 :=
    helperForCorollary_5_24_2_pairSequence_limsup_upperDirectionalDerivative
      (f := f) hproper hp (by
        intro i
        simpa [s] using hpSeq_mem i) hpSeq_tendsto_nhds
  have ha_le_limsup :
      a ≤ Filter.limsup (fun i => upperDirectionalDerivativeAt f (pSeq i).1 (pSeq i).2)
        Filter.atTop :=
    Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall hpSeq_ge)
  exact (not_le_of_lt ha) (ha_le_limsup.trans hlimsup)

end Section24
end Chap05
