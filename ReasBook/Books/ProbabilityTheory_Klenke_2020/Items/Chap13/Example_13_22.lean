/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace StieltjesFunction

/-- Helper for Example 13.22: translating a real Stieltjes function preserves right continuity on
every right ray. -/
private theorem translate_rightContinuous (F : StieltjesFunction ℝ) (a x : ℝ) :
    ContinuousWithinAt (fun y : ℝ ↦ F (y + a)) (Set.Ici x) x := by
  have h_add : ContinuousWithinAt (fun y : ℝ ↦ y + a) (Set.Ici x) x :=
    (continuous_add_const a).continuousWithinAt
  have h_mapsTo : Set.MapsTo (fun y : ℝ ↦ y + a) (Set.Ici x) (Set.Ici (x + a)) :=
    fun y hy ↦ by simpa using add_le_add_right hy a
  have h_comp :
      ContinuousWithinAt ((fun y : ℝ ↦ F y) ∘ fun y : ℝ ↦ y + a) (Set.Ici x) x :=
    ContinuousWithinAt.comp (F.right_continuous (x + a)) h_add h_mapsTo
  simpa [Function.comp] using h_comp

/-- Translation of a real Stieltjes function by `a`, i.e. `x ↦ F (x + a)`. -/
def translate (F : StieltjesFunction ℝ) (a : ℝ) : StieltjesFunction ℝ :=
  { toFun := fun x ↦ F (x + a)
    mono' := F.mono.comp (monotone_id.add_const a)
    right_continuous' := translate_rightContinuous F a }

@[simp] theorem translate_apply (F : StieltjesFunction ℝ) (a x : ℝ) :
    F.translate a x = F (x + a) := rfl

/-- Translating a defective distribution function preserves defectiveness. -/
instance instIsDefectiveDistributionFunction_translate (F : StieltjesFunction ℝ)
    [IsDefectiveDistributionFunction F] (a : ℝ) :
    IsDefectiveDistributionFunction (F.translate a) := by
  refine
    { nonneg := fun x ↦ ?_
      le_one := fun x ↦ ?_
      tendsto_atBot_zero := ?_ }
  · -- Proof comment: translation only changes the evaluation point.
    simpa [StieltjesFunction.translate_apply] using
      (IsDefectiveDistributionFunction.nonneg (F := F) (x + a))
  · -- Proof comment: the translated function inherits the same `[0,1]` range bound.
    simpa [StieltjesFunction.translate_apply] using
      (IsDefectiveDistributionFunction.le_one (F := F) (x + a))
  · -- Proof comment: adding a constant preserves the `-∞` tail, so compose the original limit.
    simpa [StieltjesFunction.translate_apply] using
      (IsDefectiveDistributionFunction.tendsto_atBot_zero (F := F)).comp
        (tendsto_atBot_add_const_right atBot a tendsto_id)

/-- Translating a distribution function preserves the distribution-function property. -/
instance instIsDistributionFunction_translate (F : StieltjesFunction ℝ)
    [IsDistributionFunction F] (a : ℝ) :
    IsDistributionFunction (F.translate a) := by
  refine
    { toIsDefectiveDistributionFunction := inferInstance
      tendsto_atTop_one := ?_ }
  -- Proof comment: the right tail is unchanged up to the same real translation.
  simpa [StieltjesFunction.translate_apply] using
    (IsDistributionFunction.tendsto_atTop_one (F := F)).comp
      (tendsto_atTop_add_const_right atTop a tendsto_id)

end StieltjesFunction

section

/-- The zero Stieltjes function is a defective distribution function. -/
instance : IsDefectiveDistributionFunction (0 : StieltjesFunction ℝ) where
  nonneg _ := by simp
  le_one _ := by simp
  tendsto_atBot_zero := tendsto_const_nhds

/-- Helper for Example 13.22: below every real threshold there is a continuity point of a
defective distribution function. -/
private lemma exists_continuityPoint_lt (G : StieltjesFunction ℝ)
    [IsDefectiveDistributionFunction G] (x : ℝ) :
    ∃ z < x, ContinuousAt G z := by
  let s : Set ℝ := {y | ¬ ContinuousAt G y}
  have hs_countable : s.Countable := G.mono.countable_not_continuousAt
  have hs_dense : Dense sᶜ := hs_countable.dense_compl ℝ
  -- Proof comment: pick a continuity point from the dense complement inside the open ray `(-∞, x)`.
  obtain ⟨z, hz_mem, hz_lt⟩ := hs_dense.exists_mem_open (U := Set.Iio x) isOpen_Iio
    ⟨x - 1, sub_lt_self x zero_lt_one⟩
  refine ⟨z, hz_lt, ?_⟩
  simpa [s] using hz_mem

/-- Helper for Example 13.22: the constant Stieltjes function `1` cannot satisfy the defective
left-tail limit `F(x) → 0` as `x → -∞`. -/
private theorem constOneNotIsDefectiveDistributionFunction :
    ¬ IsDefectiveDistributionFunction (StieltjesFunction.const ℝ 1) := by
  intro h
  have h_const :
      Tendsto (StieltjesFunction.const ℝ 1) atBot (𝓝 (1 : ℝ)) := tendsto_const_nhds
  -- Proof comment: the same constant function cannot converge to both `1` and `0` at `-∞`.
  have h_eq : (1 : ℝ) = 0 := tendsto_nhds_unique h_const h.tendsto_atBot_zero
  norm_num at h_eq

/-- Helper for Example 13.22: weak convergence of the right shifts would force an impossible
continuity-point value for the limit candidate. -/
private theorem rightShiftedLimitAtSmallContinuityPointContradiction
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDefectiveDistributionFunction G]
    (hcont : ∀ ⦃x : ℝ⦄, ContinuousAt G x →
      Tendsto (fun n : ℕ ↦ F.translate n x) atTop (𝓝 (G x))) :
    False := by
  have hsmall :
      ∀ᶠ y in atBot, G y < (1 / 2 : ℝ) :=
    (IsDefectiveDistributionFunction.tendsto_atBot_zero (F := G)).eventually_lt_const
      (by norm_num)
  obtain ⟨x, hx⟩ := hsmall.exists
  obtain ⟨z, hz_lt, hz_cont⟩ := exists_continuityPoint_lt G x
  have hz_small : G z < (1 / 2 : ℝ) := lt_of_le_of_lt (G.mono hz_lt.le) hx
  have hz_limit_G : Tendsto (fun n : ℕ ↦ F.translate n z) atTop (𝓝 (G z)) := hcont hz_cont
  have hshift : Tendsto (fun n : ℕ ↦ z + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop z tendsto_natCast_atTop_atTop
  have hz_limit_one_comp :
      Tendsto ((fun y : ℝ ↦ F y) ∘ fun n : ℕ ↦ z + (n : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    (IsDistributionFunction.tendsto_atTop_one (F := F)).comp hshift
  have hz_limit_one : Tendsto (fun n : ℕ ↦ F.translate n z) atTop (𝓝 (1 : ℝ)) := by
    -- Proof comment: the right shifts at `z` are just values of `F` along a sequence going to `+∞`.
    simpa [Function.comp_apply, StieltjesFunction.translate_apply] using hz_limit_one_comp
  -- Proof comment: uniqueness of limits identifies the weak limit value with the explicit
  -- pointwise right-shift limit `1`.
  have hz_eq : G z = 1 := tendsto_nhds_unique hz_limit_G hz_limit_one
  have h_not : ¬ ((1 : ℝ) < 1 / 2) := by norm_num
  exact h_not (hz_eq ▸ hz_small)

variable (F : StieltjesFunction ℝ)

-- Proof sketch: since `F y → 1` as `y → +∞`, compose this with
-- `n ↦ x + n`, which also tends to `+∞`.
/-- For Example 13.22, at each fixed `x`, the right-translated values `F(x + n)` converge to
`1`. -/
theorem tendsto_right_shifted_distribution_function_at_point [IsDistributionFunction F] (x : ℝ) :
    Tendsto (fun n : ℕ ↦ F.translate n x) atTop (𝓝 1) := by
  have hshift : Tendsto (fun n : ℕ ↦ x + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
  have hlimit_comp :
      Tendsto ((fun y : ℝ ↦ F y) ∘ fun n : ℕ ↦ x + (n : ℝ)) atTop (𝓝 1) :=
    (IsDistributionFunction.tendsto_atTop_one (F := F)).comp hshift
  -- Proof comment: rewrite the right shift as evaluation of `F` along a sequence escaping to `+∞`.
  simpa [Function.comp_apply, StieltjesFunction.translate_apply] using hlimit_comp

-- Proof sketch: weak convergence would force the candidate limit to agree with the pointwise
-- limit `1` at every continuity point. Since a defective distribution function must tend to `0`
-- at `-∞`, the constant pointwise limit `1` cannot arise from any admissible weak limit in the
-- sense of Definition 13.21.
/-- For Example 13.22, the right-shifted distribution functions do not converge weakly, even to a
defective distribution function, because their pointwise limit is the inadmissible constant
function `1`. -/
theorem right_shifted_distribution_functions_not_weakly_converges_to
    [IsDistributionFunction F] {G : StieltjesFunction ℝ} :
    ¬ distribution_function_weakly_converges_to (fun n ↦ F.translate n) G := by
  intro hweak
  rcases hweak with ⟨hG, _hFs, hcont, _hmass⟩
  letI : IsDefectiveDistributionFunction G := hG
  -- Proof comment: a weak limit would have to match the explicit right-shift limit `1` at a
  -- continuity point where the defective left tail is still below `1/2`.
  exact rightShiftedLimitAtSmallContinuityPointContradiction F G hcont

-- Proof sketch: the constant function `1` fails the defining condition `F(x) → 0` as
-- `x → -∞`, so it cannot be a distribution function.
/-- For Example 13.22, the constant function `1` is not a distribution function on `ℝ`. -/
theorem constant_one_not_isDistributionFunction :
    ¬ IsDistributionFunction (StieltjesFunction.const ℝ 1) := by
  intro h
  -- Proof comment: every distribution function is defective, so the same left-tail obstruction
  -- applies.
  exact constOneNotIsDefectiveDistributionFunction h.toIsDefectiveDistributionFunction

-- Proof sketch: the same left-tail obstruction already rules out defectiveness, since a
-- defective distribution function must tend to `0` at `-∞`.
/-- The constant function `1` is not even a defective distribution function on `ℝ`. -/
theorem constant_one_not_isDefectiveDistributionFunction :
    ¬ IsDefectiveDistributionFunction (StieltjesFunction.const ℝ 1) := by
  -- Proof comment: this is exactly the auxiliary left-tail contradiction.
  exact constOneNotIsDefectiveDistributionFunction

-- Proof sketch: since `F y → 0` as `y → -∞`, compose this with
-- `n ↦ x - n`, which tends to `-∞`.
/-- For Example 13.22, at each fixed `x`, the left-translated values `F(x - n)` converge to
`0`. -/
theorem tendsto_left_shifted_distribution_function_at_point [IsDistributionFunction F] (x : ℝ) :
    Tendsto (fun n : ℕ ↦ F.translate (-(n : ℝ)) x) atTop (𝓝 0) := by
  have hneg : Tendsto (fun n : ℕ ↦ -((n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun n : ℕ ↦ x - (n : ℝ)) atTop atBot :=
    by
      have hshift' : Tendsto (fun n : ℕ ↦ -((n : ℝ)) + x) atTop atBot :=
        tendsto_atBot_add_const_right _ x hneg
      simpa [sub_eq_add_neg, add_comm] using hshift'
  -- Proof comment: rewrite the left shift as evaluation of `F` along a sequence escaping to `-∞`.
  simpa [StieltjesFunction.translate_apply, sub_eq_add_neg] using
    (IsDefectiveDistributionFunction.tendsto_atBot_zero (F := F)).comp hshift

/- Example 13.22 (4): the zero Stieltjes function has right-tail limit `0`; this is the direct
constant-function convergence fact witnessed by `tendsto_const_nhds`. -/

-- Proof sketch: for fixed `n`, the map `x ↦ x - n` tends to `+∞` as `x → +∞`; composing with
-- `F x → 1` gives the right-tail limit `1` for the shifted function.
/- Example 13.22 (5): every left-translated function `x ↦ F(x - n)` still has right-tail limit
`1`; this is the `tendsto_atTop_one` field of the translated `IsDistributionFunction` instance. -/

-- Proof sketch: the left shifts converge pointwise to the zero function, but weak convergence in
-- the sense of Definition 13.21 would force convergence of the endpoint values, equivalently of
-- the total masses. Here each shifted distribution function still has endpoint value `1`, while
-- the zero limit has endpoint value `0`.
/-- Helper for Example 13.22: every left-translated distribution function still has endpoint mass
`1`. -/
private lemma leftShiftedEndpointMass_eq_one
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] (n : ℕ) :
    (((F.translate (-(n : ℝ))).measure Set.univ).toReal : ℝ) = 1 := by
  have hFn : IsDistributionFunction (F.translate (-(n : ℝ))) := inferInstance
  -- Proof comment: the translated function is still a distribution function, so its total mass
  -- is the endpoint value `1`.
  rw [StieltjesFunction.measure_univ (F.translate (-(n : ℝ)))
    hFn.tendsto_atBot_zero hFn.tendsto_atTop_one]
  simp

/-- Helper for Example 13.22: the zero Stieltjes function has endpoint mass `0`. -/
private lemma zeroEndpointMass_eq_zero :
    ((((0 : StieltjesFunction ℝ).measure Set.univ).toReal : ℝ) = 0) := by
  -- Proof comment: both tail limits of the zero Stieltjes function are `0`, so its total mass is
  -- the zero endpoint gap.
  rw [StieltjesFunction.measure_univ (0 : StieltjesFunction ℝ) tendsto_const_nhds
    tendsto_const_nhds]
  simp

/-- Helper for Example 13.22: the endpoint masses of the left shifts have limsup `1`. -/
private lemma leftShiftedEndpointMass_limsup_eq_one
    (F : StieltjesFunction ℝ) [IsDistributionFunction F] :
    limsup (fun n : ℕ ↦ (((F.translate (-(n : ℝ))).measure Set.univ).toReal : ℝ)) atTop = 1 := by
  have hmass_fun :
      (fun n : ℕ ↦ (((F.translate (-(n : ℝ))).measure Set.univ).toReal : ℝ)) =
        fun _ : ℕ ↦ (1 : ℝ) := by
    -- Proof comment: each translated distribution function still has total mass `1`.
    funext n
    exact leftShiftedEndpointMass_eq_one F n
  -- Proof comment: after identifying the sequence with the constant sequence `1`, the limsup is
  -- the constant value itself.
  rw [hmass_fun, limsup_const]

/-- Example 13.22: although the left-shifted distribution functions converge pointwise to `0`,
they do not converge weakly to the zero defective distribution function because the endpoint
condition fails. -/
theorem left_shifted_distribution_functions_not_weakly_converges_to_zero
    [IsDistributionFunction F] :
    ¬ distribution_function_weakly_converges_to
      (fun n ↦ F.translate (-(n : ℝ))) 0 := by
  intro hweak
  rcases hweak with ⟨_hzero, _hFs, _hcont, hmass⟩
  -- Route correction: work directly with Definition 13.21's endpoint-mass inequality instead of
  -- transporting through a separate endpoint-`Tendsto` theorem.
  -- Proof comment: weak convergence to `0` would require the limit mass `0` to dominate the
  -- limsup of the shifted endpoint masses, but that limsup is still `1`.
  rw [zeroEndpointMass_eq_zero, leftShiftedEndpointMass_limsup_eq_one F] at hmass
  norm_num at hmass

end
