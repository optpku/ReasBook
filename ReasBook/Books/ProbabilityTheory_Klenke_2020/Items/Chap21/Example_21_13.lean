/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The Brownian bridge is indexed by times in the unit interval `[0,1]`. -/
abbrev BrownianBridgeTime := Set.Icc (0 : NNReal) 1

/-- The covariance kernel of the Brownian bridge on `[0,1]`. -/
def brownianBridgeCovariance (s t : BrownianBridgeTime) : ℝ :=
  (((s : NNReal) ⊓ (t : NNReal)) : ℝ) - (s : ℝ) * (t : ℝ)

/-- The Brownian bridge of Example 21.13 associated to a Brownian motion `B` on `[0,1]` is the
process `X_t = B_t - t B_1`, indexed by `t ∈ [0,1]`. -/
def brownianBridge (B : NNReal → Ω → ℝ) : BrownianBridgeTime → Ω → ℝ :=
  fun t ω ↦ B t ω - (t : ℝ) * B 1 ω

/-- Evaluating the Brownian bridge gives the defining formula `B_t - t B_1`. -/
@[simp] theorem brownianBridge_apply (B : NNReal → Ω → ℝ) (t : BrownianBridgeTime) (ω : Ω) :
    brownianBridge B t ω = B t ω - (t : ℝ) * B 1 ω :=
  rfl

variable [MeasurableSpace Ω]
variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/-- Helper for Example 21.13: Brownian increments over ordered times have the centered Gaussian
law with variance equal to the time lag. -/
lemma brownianIncrement_hasLaw_ofBrownianMotion
    (hB : IsBrownianMotion μ B) {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 (t - s)) μ := by
  -- Proof comment: stationary increments reduce the increment on `[s,t]` to the increment on
  -- `[0, t - s]`, whose law is prescribed by the Brownian-motion marginal axiom.
  by_cases hEq : s = t
  · subst hEq
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    have hConst : HasLaw (fun _ : Ω ↦ (0 : ℝ)) (gaussianReal 0 0) μ := by
      constructor
      · exact measurable_const.aemeasurable
      · rw [Measure.map_const]
        simp [gaussianReal_zero_var]
    simpa using hConst
  · let u : NNReal := t - s
    have hu_pos : 0 < u := by
      exact tsub_pos_of_lt (lt_of_le_of_ne hst hEq)
    have hLawU : HasLaw (B u) (gaussianReal 0 u) μ := hB.gaussian_marginal hu_pos
    have hLawZero : HasLaw (fun ω ↦ B (u + 0) ω - B 0 ω) (gaussianReal 0 u) μ := by
      have hLawBase : HasLaw (fun ω ↦ B u ω - B 0 ω) (gaussianReal 0 u) μ := by
        refine hLawU.congr ?_
        simp [hB.zero]
      simpa using hLawBase
    have hStationary := hB.stationaryIncrements 0 u s
    have hu_add : u + s = t := by
      simp [u, tsub_add_cancel_of_le hst]
    simpa [u, hu_add, add_comm, add_left_comm, add_assoc] using hStationary.symm.hasLaw hLawZero

/-- Helper for Example 21.13: every Brownian marginal has mean `0`. -/
lemma brownianMotion_mean_zero
    (hB : IsBrownianMotion μ B) (t : NNReal) :
    ∫ ω, B t ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: at time `0` the path is identically zero, and at positive times the Gaussian
  -- marginal has mean `0`.
  by_cases ht : t = 0
  · subst ht
    simp [hB.zero]
  · calc
      ∫ ω, B t ω ∂μ = ∫ x : ℝ, x ∂gaussianReal 0 t := by
          exact (hB.gaussian_marginal (pos_iff_ne_zero.mpr ht)).integral_eq
      _ = 0 := by
          simp

/-- Helper for Example 21.13: every Brownian marginal has variance equal to its time parameter. -/
lemma brownianEval_variance_eq_ofBrownianMotion
    (hB : IsBrownianMotion μ B) (t : NNReal) :
    Var[B t; μ] = t := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: the time-zero marginal is constant, while positive-time marginals are exactly
  -- the centered Gaussian laws prescribed by the Brownian-motion axiom.
  by_cases ht : t = 0
  · subst ht
    simp [hB.zero]
  · have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht
    have hLaw : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht_pos
    simpa using hLaw.variance_eq

/-- Helper for Example 21.13: every fixed Brownian marginal belongs to `L²`. -/
lemma brownianEval_memLp_two_ofBrownianMotion
    (hB : IsBrownianMotion μ B) (t : NNReal) :
    MemLp (B t) 2 μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: at time `0` the path is constant, while positive-time marginals are Gaussian
  -- with nonzero variance and therefore lie in `L²`.
  by_cases ht : t = 0
  · subst ht
    simp [hB.zero]
  · have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht
    have hLaw : HasLaw (B t) (gaussianReal 0 t) μ := hB.gaussian_marginal ht_pos
    have hVar : Var[B t; μ] = t := by
      simpa using hLaw.variance_eq
    have hVar_ne : Var[B t; μ] ≠ 0 := by
      rw [hVar]
      exact_mod_cast ht
    exact memLp_two_of_variance_ne_zero hLaw.aemeasurable.aestronglyMeasurable hVar_ne

/-- Helper for Example 21.13: the covariance kernel of Brownian motion is `s ⊓ t`. -/
lemma brownianMotion_covariance_eq
    (hB : IsBrownianMotion μ B) (s t : NNReal) :
    cov[B s, B t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: order the two times, decompose `B_t` into the past value `B_s` plus the
  -- future increment, and then use independent increments to kill the mixed covariance term.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  have hs_mem : MemLp (B s) 2 μ := brownianEval_memLp_two_ofBrownianMotion hB s
  have hIncLaw :
      HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 (t - s)) μ :=
    brownianIncrement_hasLaw_ofBrownianMotion hB hst
  have hInc_mem : MemLp (fun ω ↦ B t ω - B s ω) 2 μ := hIncLaw.hasGaussianLaw.memLp_two
  have hIndep :
      (B s) ⟂ᵢ[μ] (fun ω ↦ B t ω - B s ω) :=
    hB.indepIncrements.indepFun_eval_sub (show (0 : NNReal) ≤ s by simp) hst
      (Filter.Eventually.of_forall fun ω ↦ by simp [hB.zero])
  have hSplit :
      B t = fun ω ↦ B s ω + (B t ω - B s ω) := by
    funext ω
    ring
  rw [hSplit]
  change cov[B s, B s + (fun ω ↦ B t ω - B s ω); μ] = ((s ⊓ t : NNReal) : ℝ)
  rw [covariance_add_right hs_mem hs_mem hInc_mem,
    hIndep.covariance_eq_zero hs_mem hInc_mem, covariance_self hs_mem.aemeasurable,
    brownianEval_variance_eq_ofBrownianMotion hB s]
  simp [inf_eq_left.mpr hst]

/-- Helper for Example 21.13: evaluating Brownian motion along a monotone finite family of times
has a joint Gaussian law. -/
lemma brownianMotion_hasGaussianLaw_of_monotone
    (hB : IsBrownianMotion μ B) {n : ℕ} (t : Fin n → NNReal) (ht : Monotone t) :
    HasGaussianLaw (fun ω i ↦ B (t i) ω) μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let tAux : Fin (n + 1) → NNReal := Fin.cases 0 t
  have htAux : Monotone tAux := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    cases n with
    | zero =>
        exact Fin.elim0 i
    | succ n =>
        rcases i with ⟨i, hi⟩
        cases i with
        | zero =>
            simp [tAux]
        | succ i =>
            have hi' : i.succ < n.succ := hi
            have hle :
                (⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi'⟩ : Fin (n + 1)) ≤ ⟨i.succ, hi'⟩ := by
              exact Nat.le_succ i
            simpa [tAux] using
              ht hle
  let Y : Fin n → Ω → ℝ := fun i ω ↦ B (tAux i.succ) ω - B (tAux i.castSucc) ω
  have hY_gauss : ∀ i : Fin n, HasGaussianLaw (Y i) μ := by
    intro i
    exact (brownianIncrement_hasLaw_ofBrownianMotion hB (htAux i.castSucc_le_succ)).hasGaussianLaw
  have hY_indep : iIndepFun Y μ := by
    simpa [Y] using hB.indepIncrements n tAux htAux
  have hY_joint : HasGaussianLaw (fun ω i ↦ Y i ω) μ :=
    hY_indep.hasGaussianLaw hY_gauss
  let cumulativeSumFun : (Fin n → ℝ) → Fin n → ℝ := fun x i ↦
        Finset.sum (Finset.range (i.1 + 1)) fun j ↦
          if hj : j < n then x ⟨j, hj⟩ else 0
  let cumulativeSumsLinear : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := cumulativeSumFun
      map_add' := by
        intro x y
        ext i
        calc
          cumulativeSumFun (x + y) i
              = Finset.sum (Finset.range (i.1 + 1)) fun j ↦
                  (if hj : j < n then x ⟨j, hj⟩ else 0) +
                    (if hj : j < n then y ⟨j, hj⟩ else 0) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      split_ifs <;> simp [Pi.add_apply]
          _ = (cumulativeSumFun x + cumulativeSumFun y) i := by
                simp [cumulativeSumFun, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        ext i
        simp only [cumulativeSumFun, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        split_ifs <;> simp }
  let cumulativeSums : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ⟨cumulativeSumsLinear, cumulativeSumsLinear.continuous_of_finiteDimensional⟩
  have hCumulative :
      ∀ ω i, cumulativeSums (fun j ↦ Y j ω) i = B (t i) ω := by
    intro ω i
    rcases i with ⟨i, hi⟩
    induction i with
    | zero =>
        have h0 : 0 < n := hi
        simp [cumulativeSums, cumulativeSumsLinear, cumulativeSumFun, Y, tAux, h0, hB.zero]
    | succ i ih =>
        have hi' : i < n := Nat.lt_of_succ_lt hi
        have hstep :
            cumulativeSums (fun j ↦ Y j ω) ⟨i.succ, hi⟩ =
              cumulativeSums (fun j ↦ Y j ω) ⟨i, hi'⟩ + Y ⟨i.succ, hi⟩ ω := by
          simp [cumulativeSums, cumulativeSumsLinear, cumulativeSumFun, Finset.sum_range_succ, hi']
        calc
          cumulativeSums (fun j ↦ Y j ω) ⟨i.succ, hi⟩
              = cumulativeSums (fun j ↦ Y j ω) ⟨i, hi'⟩ + Y ⟨i.succ, hi⟩ ω := hstep
          _ = B (t ⟨i, hi'⟩) ω + (B (t ⟨i.succ, hi⟩) ω - B (t ⟨i, hi'⟩) ω) := by
                rw [ih hi']
                simp [Y, tAux]
          _ = B (t ⟨i.succ, hi⟩) ω := by
                ring
  have hRecover :
      (fun ω ↦ cumulativeSums (fun j ↦ Y j ω)) =ᵐ[μ] fun ω i ↦ B (t i) ω := by
    exact Filter.Eventually.of_forall fun ω ↦ by
      ext i
      exact hCumulative ω i
  exact (hY_joint.map cumulativeSums).congr hRecover

/-- Helper for Example 21.13: Brownian motion is a Gaussian process. -/
theorem brownianMotion_isGaussianProcess
    (hB : IsBrownianMotion μ B) :
    IsGaussianProcess B μ := by
  -- Proof comment: sort a finite family of times, express the corresponding Brownian values as
  -- cumulative sums of independent Gaussian increments, and transport that joint Gaussian law
  -- back to the original finite index set.
  classical
  refine ⟨fun I ↦ ?_⟩
  let e : Fin I.card ≃o I := I.orderIsoOfFin rfl
  let restrictAlongOrderLinear : (Fin I.card → ℝ) →ₗ[ℝ] I → ℝ :=
    { toFun := fun x i ↦ x (e.symm i)
      map_add' := by
        intro x y
        ext i
        rfl
      map_smul' := by
        intro m x
        ext i
        rfl }
  let restrictAlongOrder : (Fin I.card → ℝ) →L[ℝ] I → ℝ :=
    ⟨restrictAlongOrderLinear, restrictAlongOrderLinear.continuous_of_finiteDimensional⟩
  have hFin :
      HasGaussianLaw (fun ω (i : Fin I.card) ↦ B (e i) ω) μ :=
    brownianMotion_hasGaussianLaw_of_monotone hB (fun i ↦ (e i : NNReal)) e.monotone
  have hRestrict :
      (fun ω ↦ I.restrict (B · ω)) =
        fun ω ↦
          restrictAlongOrder (fun i : Fin I.card ↦ B (e i) ω) := by
    ext ω i
    simp [restrictAlongOrder, restrictAlongOrderLinear]
  rw [hRestrict]
  exact hFin.map restrictAlongOrder

/-- Helper for Example 21.13: restricting a continuous path to `[0,1]` and subtracting the
deterministic correction `t ↦ t * c` preserves continuity. -/
lemma continuous_brownianBridgePath_of_continuous
    {f : NNReal → ℝ} (hf : Continuous f) (c : ℝ) :
    Continuous (fun t : BrownianBridgeTime ↦ f t - (t : ℝ) * c) := by
  -- Proof comment: continuity on the subtype comes from restricting `f`, and the affine
  -- correction `t ↦ (t : ℝ) * c` is continuous as a product of continuous coordinate functions.
  have hf_restrict : Continuous fun t : BrownianBridgeTime ↦ f t :=
    hf.comp continuous_subtype_val
  have hlinear : Continuous fun t : BrownianBridgeTime ↦ (t : ℝ) * c :=
    (NNReal.continuous_coe.comp continuous_subtype_val).mul continuous_const
  exact hf_restrict.sub hlinear

-- Proof sketch: Brownian motion is a Gaussian process, and for each `t ∈ [0,1]` the variable
-- `B_t - t B_1` is a linear combination of the Gaussian vector `(B_t, B_1)`. Finite-dimensional
-- laws of the bridge are therefore Gaussian by stability of Gaussian laws under linear maps.
/-- Example 21.13: the Brownian bridge associated to a Brownian motion is a Gaussian process on
`[0,1]`. -/
theorem brownianBridge_isGaussianProcess
    (hB : IsBrownianMotion μ B) :
    IsGaussianProcess (brownianBridge B) μ := by
  -- Route correction: each bridge coordinate is a linear image of the two Brownian coordinates
  -- `(B_t, B_1)`, so we push Gaussianity through the finite set `{t, 1}`.
  let hGaussian : IsGaussianProcess B μ := brownianMotion_isGaussianProcess hB
  refine hGaussian.of_isGaussianProcess ?_
  intro t
  let I : Finset NNReal := {(t : NNReal), 1}
  have ht_mem : (t : NNReal) ∈ I := by
    simp [I]
  have h1_mem : (1 : NNReal) ∈ I := by
    simp [I]
  refine ⟨I, ?_, ?_⟩
  · refine
      { toFun := fun x ↦ x ⟨(t : NNReal), ht_mem⟩ - (t : ℝ) * x ⟨1, h1_mem⟩
        map_add' := ?_
        map_smul' := ?_
        cont := ?_ }
    · -- Proof comment: the bridge coordinate is additive because both evaluation maps are linear.
      intro x y
      change
        x ⟨(t : NNReal), ht_mem⟩ + y ⟨(t : NNReal), ht_mem⟩ -
            (t : ℝ) * (x ⟨1, h1_mem⟩ + y ⟨1, h1_mem⟩) =
          (x ⟨(t : NNReal), ht_mem⟩ - (t : ℝ) * x ⟨1, h1_mem⟩) +
            (y ⟨(t : NNReal), ht_mem⟩ - (t : ℝ) * y ⟨1, h1_mem⟩)
      ring
    · -- Proof comment: scalar multiplication distributes through both evaluations.
      intro c x
      change
        c * x ⟨(t : NNReal), ht_mem⟩ - (t : ℝ) * (c * x ⟨1, h1_mem⟩) =
          c * (x ⟨(t : NNReal), ht_mem⟩ - (t : ℝ) * x ⟨1, h1_mem⟩)
      ring
    · -- Proof comment: evaluation is continuous on the finite coordinate space, and so is the
      -- affine combination defining the bridge coordinate.
      fun_prop
  · -- Proof comment: evaluating the linear functional on the restricted Brownian path gives
    -- exactly `B t - t * B 1`.
    intro ω
    simp [brownianBridge, I]

-- Proof sketch: almost every Brownian sample path is continuous on `NNReal`, and
-- `t ↦ (t : ℝ) * B 1 ω` is continuous on `[0,1]`; subtracting these two continuous functions gives
-- a continuous bridge path.
/-- The Brownian bridge associated to a Brownian motion has almost surely continuous paths on
`[0,1]`. -/
theorem brownianBridge_hasAlmostSurelyContinuousPaths
    (hB : IsBrownianMotion μ B) :
    HasAlmostSurelyContinuousPaths μ (brownianBridge B) := by
  -- Proof comment: almost every Brownian sample path is continuous on `NNReal`, and the bridge
  -- path is obtained by restricting that path to `[0,1]` and subtracting a deterministic linear
  -- correction.
  filter_upwards [hB.continuous_paths] with ω hω
  simpa [processPath, brownianBridge] using
    continuous_brownianBridgePath_of_continuous (f := fun t ↦ B t ω) hω (B 1 ω)

-- Proof sketch: Brownian motion marginals are centered Gaussians, so `B_t` and `B_1` both have
-- mean `0`. Linearity of expectation then gives `E[B_t - t B_1] = 0`.
/-- Every time marginal of the Brownian bridge associated to a Brownian motion is centered. -/
theorem brownianBridge_mean_zero
    (hB : IsBrownianMotion μ B) (t : BrownianBridgeTime) :
    ∫ ω, brownianBridge B t ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: rewrite the bridge marginal as `B_t - t B_1`, integrate termwise, and
  -- substitute the already-known zero expectations of Brownian marginals.
  have hbridge :
      brownianBridge B t = fun ω ↦ B t ω - (t : ℝ) * B 1 ω := by
    funext ω
    simp [brownianBridge]
  rw [hbridge, integral_sub]
  · rw [integral_const_mul, brownianMotion_mean_zero hB t,
      brownianMotion_mean_zero hB 1]
    ring
  · exact (brownianEval_memLp_two_ofBrownianMotion hB t).integrable (by norm_num)
  · exact ((brownianEval_memLp_two_ofBrownianMotion hB 1).const_mul (t : ℝ)).integrable
      (by norm_num)

-- Proof sketch: expand the covariance of
-- `(B_s - s B_1, B_t - t B_1)`, use bilinearity of covariance, and substitute the Brownian-motion
-- covariance identities `cov[B_s, B_t] = s ∧ t`, `cov[B_s, B_1] = s`, `cov[B_1, B_t] = t`, and
-- `cov[B_1, B_1] = 1`. Since `s, t ∈ [0,1]`, this simplifies to `min(s,t) - st`.
/-- The covariance kernel of the Brownian bridge is `Γ(s,t) = min(s,t) - st`. -/
theorem brownianBridge_covariance_eq
    (hB : IsBrownianMotion μ B) (s t : BrownianBridgeTime) :
    cov[brownianBridge B s, brownianBridge B t; μ] = brownianBridgeCovariance s t := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: expand the bridge coordinates, use bilinearity of covariance, and then
  -- substitute the Brownian covariance kernel `u ↦ u ⊓ v`.
  have hs_mem : MemLp (B s) 2 μ := brownianEval_memLp_two_ofBrownianMotion hB s
  have ht_mem : MemLp (B t) 2 μ := brownianEval_memLp_two_ofBrownianMotion hB t
  have h1_mem : MemLp (B 1) 2 μ := brownianEval_memLp_two_ofBrownianMotion hB 1
  have hs_bridge :
      brownianBridge B s = fun ω ↦ B s ω - (s : ℝ) * B 1 ω := by
    funext ω
    simp [brownianBridge]
  have ht_bridge :
      brownianBridge B t = fun ω ↦ B t ω - (t : ℝ) * B 1 ω := by
    funext ω
    simp [brownianBridge]
  have hs1 : ((s : NNReal) ⊓ 1 : NNReal) = s := min_eq_left s.2.2
  have h1t : ((1 : NNReal) ⊓ (t : NNReal)) = t := min_eq_right t.2.2
  calc
    cov[brownianBridge B s, brownianBridge B t; μ]
        = cov[fun ω ↦ B s ω - (s : ℝ) * B 1 ω, fun ω ↦ B t ω - (t : ℝ) * B 1 ω; μ] := by
            rw [hs_bridge, ht_bridge]
    _ = cov[B s - fun ω ↦ (s : ℝ) * B 1 ω, B t - fun ω ↦ (t : ℝ) * B 1 ω; μ] := by
          rfl
    _ = brownianBridgeCovariance s t := by
          rw [covariance_sub_left hs_mem (h1_mem.const_mul (s : ℝ))
              (ht_mem.sub (h1_mem.const_mul (t : ℝ)))]
          rw [covariance_sub_right hs_mem ht_mem (h1_mem.const_mul (t : ℝ))]
          rw [covariance_sub_right (h1_mem.const_mul (s : ℝ)) ht_mem
            (h1_mem.const_mul (t : ℝ))]
          rw [covariance_const_mul_right, covariance_const_mul_left, covariance_const_mul_left,
            covariance_const_mul_right]
          rw [brownianMotion_covariance_eq hB s t, brownianMotion_covariance_eq hB s 1,
            brownianMotion_covariance_eq hB 1 t, brownianMotion_covariance_eq hB 1 1]
          rw [brownianBridgeCovariance]
          simp [hs1, h1t]
          ring

/-- A Brownian bridge on `[0,1]` is a centered Gaussian process with covariance kernel
`Γ(s,t) = min(s,t) - st` and almost surely continuous sample paths. -/
class IsBrownianBridge (μ : Measure Ω) (Y : BrownianBridgeTime → Ω → ℝ) : Prop
    extends IsGaussianProcess Y μ where
  /-- Every marginal of a Brownian bridge has mean `0`. -/
  mean_zero : ∀ t : BrownianBridgeTime, ∫ ω, Y t ω ∂μ = 0
  /-- The covariance kernel of a Brownian bridge is `Γ(s,t) = min(s,t) - st`. -/
  covariance_eq :
    ∀ s t : BrownianBridgeTime, cov[Y s, Y t; μ] = brownianBridgeCovariance s t
  /-- Brownian bridges have almost surely continuous sample paths on `[0,1]`. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ Y

/-- The canonical bridge associated to a Brownian motion is a Brownian bridge. -/
instance {μ : Measure Ω} {B : NNReal → Ω → ℝ} [IsBrownianMotion μ B] :
    IsBrownianBridge μ (brownianBridge B) :=
  ⟨brownianBridge_isGaussianProcess ‹IsBrownianMotion μ B›,
    brownianBridge_mean_zero ‹IsBrownianMotion μ B›,
    brownianBridge_covariance_eq ‹IsBrownianMotion μ B›,
    brownianBridge_hasAlmostSurelyContinuousPaths ‹IsBrownianMotion μ B›⟩

end ProbabilityTheory
