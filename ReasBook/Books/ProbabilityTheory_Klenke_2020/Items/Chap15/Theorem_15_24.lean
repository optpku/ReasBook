/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Example_15_15
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

noncomputable section

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Theorem 15.24: the canonical embedding of `ℝ` into `ℝ¹` along the unique
coordinate axis is continuous. -/
lemma continuous_single_zero :
    Continuous (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) := by
  -- Proof comment: `EuclideanSpace.single` is the standard continuous `lp.single` map in
  -- dimension one.
  have hsingle : Continuous fun t : ℝ ↦ (Pi.single (0 : Fin 1) t : Fin 1 → ℝ) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    simpa using continuous_id
  simpa [EuclideanSpace.single] using
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 1 ↦ ℝ)).comp hsingle

/-- Helper for Theorem 15.24: transporting a real probability law along the unique coordinate-axis
embedding into `ℝ¹` preserves the characteristic function after reading that coordinate. -/
lemma charFun_map_single_zero (μ : ProbabilityMeasure ℝ) (x : E1) :
    charFun
      (Measure.map (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) (μ : Measure ℝ)) x =
      charFun (μ : Measure ℝ) (x (0 : Fin 1)) := by
  -- Proof comment: rewrite the pushforward characteristic function by `integral_map`, then reduce
  -- the one-dimensional inner product to multiplication by the unique coordinate.
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply_real,
    MeasureTheory.integral_map
      (continuous_single_zero.measurable.aemeasurable :
        AEMeasurable (fun t : ℝ ↦ (EuclideanSpace.single (0 : Fin 1) t : E1)) (μ : Measure ℝ))
      (by fun_prop)]
  congr with t
  congr 1
  have hinner : inner ℝ (EuclideanSpace.single (0 : Fin 1) t) x = x 0 * t := by
    simpa [mul_comm] using
      (EuclideanSpace.inner_single_left (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner)

/-- Helper for Theorem 15.24: the unique coordinate projection on `ℝ¹` is almost everywhere
measurable for every probability law. -/
lemma coordZeroAEMeasurable (μ : ProbabilityMeasure E1) :
    AEMeasurable (fun x : E1 ↦ x (0 : Fin 1)) μ := by
  -- Proof comment: coordinate evaluation is continuous on Euclidean space, hence measurable.
  have hcont : Continuous (fun x : E1 ↦ x (0 : Fin 1)) := by
    fun_prop
  exact hcont.aemeasurable

/-- Helper for Theorem 15.24: pushing a law on `ℝ¹` forward along the unique coordinate preserves
characteristic functions after re-inserting that coordinate axis. -/
lemma charFun_map_coordZero (μ : ProbabilityMeasure E1) (t : ℝ) :
    charFun (ProbabilityMeasure.map μ (coordZeroAEMeasurable μ) : Measure ℝ) t =
      charFun (μ : Measure E1) (EuclideanSpace.single (0 : Fin 1) t) := by
  -- Proof comment: rewrite the pushforward characteristic function by `integral_map`, then
  -- identify the inner product with the unique coordinate.
  change charFun (Measure.map (fun x : E1 ↦ x (0 : Fin 1)) (μ : Measure E1)) t =
    charFun (μ : Measure E1) (EuclideanSpace.single (0 : Fin 1) t)
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply,
    MeasureTheory.integral_map (coordZeroAEMeasurable μ) (by fun_prop)]
  congr with x
  congr 1
  have hinner : inner ℝ x (EuclideanSpace.single (0 : Fin 1) t) = t * x 0 := by
    simpa using (EuclideanSpace.inner_single_right (i := (0 : Fin 1)) t x)
  simp [hinner]

/-- Helper for Theorem 15.24: a pointwise limit of characteristic functions on `ℝ¹` that is
continuous at `0` is again the characteristic function of a probability measure. -/
lemma existsProbabilityMeasureOfTendstoCharFunAtOrigin
    (Ps : ℕ → ProbabilityMeasure E1) {f : E1 → ℂ} (hf : ContinuousAt f 0)
    (hφ : ∀ t : E1, Tendsto (fun n ↦ charFun (Ps n) t) atTop (𝓝 (f t))) :
    ∃ Q : ProbabilityMeasure E1, ∀ t : E1, charFun (Q : Measure E1) t = f t := by
  have hTightRange :
      IsTightMeasureSet (Set.range fun n ↦ ((Ps n : ProbabilityMeasure E1) : Measure E1)) := by
    -- Proof comment: Lévy's tightness theorem applies directly because the pointwise limit is
    -- continuous at the origin.
    refine MeasureTheory.isTightMeasureSet_of_tendsto_charFun hf ?_
    intro t
    simpa using hφ t
  have hTight :
      IsTightMeasureSet (((↑) : ProbabilityMeasure E1 → Measure E1) '' Set.range Ps) := by
    -- Proof comment: rewrite the range in the form expected by Prokhorov compactness.
    convert hTightRange using 1
    ext μ
    constructor
    · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Ps n, ⟨n, rfl⟩, rfl⟩
  have hCompact : IsCompact (closure (Set.range Ps)) :=
    isCompact_closure_of_isTightMeasureSet (S := Set.range Ps) hTight
  obtain ⟨Q, _hQmem, σ, hσmono, hσtendsto⟩ :=
    hCompact.tendsto_subseq (fun n ↦ subset_closure ⟨n, rfl⟩)
  refine ⟨Q, ?_⟩
  intro t
  -- Proof comment: identify the subsequential weak limit by uniqueness of the pointwise limit of
  -- the corresponding characteristic functions.
  have hQt :
      Tendsto (fun n ↦ charFun (Ps (σ n)) t) atTop (𝓝 (charFun (Q : Measure E1) t)) :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hσtendsto) t
  have hft : Tendsto (fun n ↦ charFun (Ps (σ n)) t) atTop (𝓝 (f t)) :=
    (hφ t).comp hσmono.tendsto_atTop
  exact tendsto_nhds_unique hQt hft

/-- Helper for Theorem 15.24: the `n`th polygonal approximation uses the regular grid
`k / (n + 1)` on `[0, n + 1]`. -/
noncomputable def polyaGrid (n k : ℕ) : ℝ :=
  k / (n + 1 : ℝ)

/-- Helper for Theorem 15.24: the terminal node index `(n + 1)^2` corresponds to the grid point
`n + 1`. -/
def polyaLastIndex (n : ℕ) : ℕ :=
  (n + 1) ^ 2

/-- Helper for Theorem 15.24: the normalized nodal values of the zero-tail polygonal core. -/
noncomputable def polyaCoreHeight (f : ℝ → ℝ) (n k : ℕ) : ℝ :=
  (f (polyaGrid n k) - f (n + 1)) / (1 - f (n + 1))

/-- Helper for Theorem 15.24: the zero-tail even polygonal core used in Pólya's approximation. -/
noncomputable def polyaCore (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  polygonalTentCombination (polyaLastIndex n) (polyaGrid n) (polyaCoreHeight f n)

/-- Helper for Theorem 15.24: the constant-tail polygonal approximant obtained by re-inserting the
tail level `f (n + 1)`. -/
noncomputable def polyaApprox (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun t ↦ f (n + 1) + (1 - f (n + 1)) * polyaCore f n t

/-- Helper for Theorem 15.24: the probability measure attached to the normalized zero-tail
polygonal core. -/
noncomputable def polyaCoreMeasure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  polygonalCharacteristicMeasure (polyaLastIndex n) (polyaGrid n) (polyaCoreHeight f n)

/-- Helper for Theorem 15.24: the full approximating measure, obtained as the convex combination
of the core law with a Dirac mass at `0`. -/
noncomputable def polyaApproxMeasure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (f (n + 1)) • Measure.dirac 0 +
    ENNReal.ofReal (1 - f (n + 1)) • polyaCoreMeasure f n

/-- Helper for Theorem 15.24: the regular Pólya grid starts at `0`. -/
lemma polyaGrid_zero (n : ℕ) :
    polyaGrid n 0 = 0 := by
  -- Proof comment: the zeroth grid point has zero numerator.
  simp [polyaGrid]

/-- Helper for Theorem 15.24: the terminal Pólya grid point is `n + 1`. -/
lemma polyaGrid_lastIndex (n : ℕ) :
    polyaGrid n (polyaLastIndex n) = n + 1 := by
  -- Proof comment: `(n + 1)^2 / (n + 1)` collapses to the endpoint `n + 1`.
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hne : (n + 1 : ℝ) ≠ 0 := ne_of_gt hpos
  rw [polyaGrid, polyaLastIndex]
  field_simp [hne]
  ring
  norm_num

/-- Helper for Theorem 15.24: consecutive Pólya grid points are strictly increasing. -/
lemma polyaGrid_strictMono (n : ℕ) (k : ℕ) :
    polyaGrid n k < polyaGrid n (k + 1) := by
  -- Proof comment: the regular grid has positive mesh `1 / (n + 1)`.
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [polyaGrid, polyaGrid]
  exact (div_lt_div_iff_of_pos_right hpos).2 (by exact_mod_cast Nat.lt_succ_self k)

/-- Helper for Theorem 15.24: every positive-index Pólya grid point is positive. -/
lemma polyaGrid_pos (n : ℕ) {k : ℕ} (hk : 0 < k) :
    0 < polyaGrid n k := by
  -- Proof comment: the mesh denominator is positive and the numerator is a positive natural.
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [polyaGrid]
  exact div_pos (by exact_mod_cast hk) hpos

/-- Helper for Theorem 15.24: consecutive Pólya grid points are separated by the mesh
`(n + 1)⁻¹`. -/
lemma polyaGrid_step (n k : ℕ) :
    polyaGrid n (k + 1) - polyaGrid n k = 1 / (n + 1 : ℝ) := by
  have hdenom : (n + 1 : ℝ) ≠ 0 := by positivity
  -- Proof comment: the regular grid has constant increment because only the numerator changes by
  -- `1`.
  rw [polyaGrid, polyaGrid]
  field_simp [hdenom]
  norm_num

/-- Helper for Theorem 15.24: in the nontrivial branch the normalization denominator
`1 - f (n + 1)` is strictly positive. -/
lemma one_sub_polyaTail_pos
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n : ℕ) :
    0 < 1 - f (n + 1) := by
  -- Proof comment: the strict-tail branch says every positive radius has value strictly below `1`.
  have hlt_tail : f (n + 1) < 1 := hlt (n + 1) (by positivity)
  linarith

/-- Helper for Theorem 15.24: the normalized core starts at height `1`. -/
lemma polyaCoreHeight_zero
    {f : ℝ → ℝ} (hf_zero : f 0 = 1)
    (hlt : ∀ r > 0, f r < 1) (n : ℕ) :
    polyaCoreHeight f n 0 = 1 := by
  -- Proof comment: after inserting `f 0 = 1`, the numerator and denominator coincide.
  have hdenom : (1 : ℝ) - f (n + 1) ≠ 0 := ne_of_gt (one_sub_polyaTail_pos hlt n)
  rw [polyaCoreHeight, polyaGrid_zero, hf_zero]
  field_simp [hdenom]

/-- Helper for Theorem 15.24: the normalized core has terminal value `0` at the last grid point. -/
lemma polyaCoreHeight_last
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n : ℕ) :
    polyaCoreHeight f n (polyaLastIndex n) = 0 := by
  -- Proof comment: the terminal grid point is exactly `n + 1`, so the normalized numerator
  -- vanishes.
  have hdenom : (1 : ℝ) - f (n + 1) ≠ 0 := ne_of_gt (one_sub_polyaTail_pos hlt n)
  rw [polyaCoreHeight, polyaGrid_lastIndex]
  field_simp [hdenom]
  ring

/-- Helper for Theorem 15.24: every Pólya grid point up to the terminal index lies in
`[0, n + 1]`. -/
lemma polyaGrid_le_last (n : ℕ) {k : ℕ} (hk : k ≤ polyaLastIndex n) :
    polyaGrid n k ≤ n + 1 := by
  -- Proof comment: `k ≤ (n + 1)^2` becomes `k / (n + 1) ≤ n + 1` after dividing by the positive
  -- mesh denominator.
  have hpos : (0 : ℝ) < n + 1 := by positivity
  rw [polyaGrid]
  refine (div_le_iff₀ hpos).2 ?_
  have hk' : ((k : ℕ) : ℝ) ≤ ((polyaLastIndex n : ℕ) : ℝ) := by
    exact_mod_cast hk
  simpa [polyaLastIndex, pow_two] using hk'

/-- Helper for Theorem 15.24: the normalized core is the canonical even polygonal interpolant for
its nodal data. -/
lemma polyaCore_isEvenPolygonalInterpolant
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n : ℕ) :
    IsEvenPolygonalInterpolant
      (polyaLastIndex n) (polyaGrid n) (polyaCoreHeight f n) (polyaCore f n) := by
  -- Proof comment: the owner theorem for `polygonalTentCombination` applies once the regular-grid
  -- endpoint identities are in place.
  simpa [polyaCore] using
    polygonalTentCombination_isEvenPolygonalInterpolant
      (polyaLastIndex n) (polyaGrid n) (polyaCoreHeight f n)
      (polyaGrid_zero n)
      (by
        intro k hk
        exact polyaGrid_strictMono n k)
      (polyaCoreHeight_last hlt n)

/-- Helper for Theorem 15.24: the normalized nodal values are nonnegative up to the terminal
point. -/
lemma polyaCoreHeight_nonneg
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0))
    (n : ℕ) {k : ℕ} (hk : k ≤ polyaLastIndex n) :
    0 ≤ polyaCoreHeight f n k := by
  -- Proof comment: antitonicity on the nonnegative ray bounds the terminal value `f (n + 1)`
  -- below every earlier sampled value.
  have hk_nonneg : 0 ≤ polyaGrid n k := by
    rw [polyaGrid]
    positivity
  have hk_le : polyaGrid n k ≤ n + 1 := polyaGrid_le_last n hk
  have htail_le :
      f (n + 1) ≤ f (polyaGrid n k) := hanti hk_nonneg (show 0 ≤ (n + 1 : ℝ) by positivity) hk_le
  have hden_pos : 0 < 1 - f (n + 1) := one_sub_polyaTail_pos hlt n
  exact div_nonneg (sub_nonneg.mpr htail_le) hden_pos.le

/-- Helper for Theorem 15.24: normalizing by the positive tail factor rescales the sampled secant
slopes by the same positive constant. -/
lemma polyaCoreSlope_eq_scaled
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n k : ℕ) :
    polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) k =
      polygonalSegmentSlope (polyaGrid n) (fun j ↦ f (polyaGrid n j)) k / (1 - f (n + 1)) := by
  -- Proof comment: both nodal differences are divided by the same positive normalization factor.
  have hdenom : (1 : ℝ) - f (n + 1) ≠ 0 := ne_of_gt (one_sub_polyaTail_pos hlt n)
  have hgrid :
      polyaGrid n (k + 1) - polyaGrid n k ≠ 0 := by
    have hlt_grid : polyaGrid n k < polyaGrid n (k + 1) := polyaGrid_strictMono n k
    linarith
  unfold polygonalSegmentSlope polyaCoreHeight
  field_simp [hdenom, hgrid]
  ring

/-- Helper for Theorem 15.24: the polygonal weights of the normalized core are nonnegative. -/
lemma polyaCoreWeight_nonneg
    {f : ℝ → ℝ} (hf_convex : ConvexOn ℝ (Ici 0) f) (hlt : ∀ r > 0, f r < 1)
    (hanti : AntitoneOn f (Ici 0)) (n : ℕ) {k : ℕ} (hk : k < polyaLastIndex n) :
    0 ≤ polygonalWeight (polyaGrid n) (polyaCoreHeight f n) (polyaLastIndex n) k := by
  -- Proof comment: on interior intervals the sampled secant slopes increase by convexity; on the
  -- final interval the last normalized slope is nonpositive because the terminal node height is
  -- `0`.
  have hnode_pos : 0 < polyaGrid n (k + 1) := polyaGrid_pos n (Nat.succ_pos _)
  by_cases hk_next : k + 1 < polyaLastIndex n
  · have hslope_raw :=
      hf_convex.slope_mono_adjacent
        (show 0 ≤ polyaGrid n k from by
          rw [polyaGrid]
          positivity)
        (show 0 ≤ polyaGrid n (k + 2) from by
          rw [polyaGrid]
          positivity)
        (polyaGrid_strictMono n k)
        (polyaGrid_strictMono n (k + 1))
    have hslope :
        polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) k ≤
          polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) (k + 1) := by
      rw [polyaCoreSlope_eq_scaled hlt n k,
        polyaCoreSlope_eq_scaled hlt n (k + 1)]
      exact div_le_div_of_nonneg_right hslope_raw (one_sub_polyaTail_pos hlt n).le
    have hcoeff_nonneg :
        0 ≤
          polyaGrid n (k + 1) *
            (polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) (k + 1) -
              polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) k) := by
      exact mul_nonneg hnode_pos.le (sub_nonneg.mpr hslope)
    simpa [polygonalWeight, hk_next] using hcoeff_nonneg
  · have hk_last : k + 1 = polyaLastIndex n := by
      omega
    have hheight_nonneg :
        0 ≤ polyaCoreHeight f n k :=
      polyaCoreHeight_nonneg hlt hanti n (by omega)
    have hslope_nonpos :
        polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) k ≤ 0 := by
      have hgrid_lt : polyaGrid n k < polyaGrid n (polyaLastIndex n) := by
        simpa [hk_last] using polyaGrid_strictMono n k
      have hgrid_ne :
          polyaGrid n (polyaLastIndex n) - polyaGrid n k ≠ 0 := by
        linarith
      rw [polygonalSegmentSlope, hk_last, polyaCoreHeight_last hlt n]
      have hnum_nonpos : 0 - polyaCoreHeight f n k ≤ 0 := by
        simpa using neg_nonpos.mpr hheight_nonneg
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (sub_nonneg.mpr hgrid_lt.le)
    have hcoeff_nonneg :
        0 ≤
          polyaGrid n (k + 1) *
            (0 - polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) k) := by
      exact mul_nonneg hnode_pos.le (sub_nonneg.mpr hslope_nonpos)
    simpa [polygonalWeight, hk_next] using hcoeff_nonneg

/-- Helper for Theorem 15.24: each one-dimensional tent kernel `x ↦ max (1 - x / r) 0` is convex
on the nonnegative ray. -/
lemma polyaTentKernel_convexOn {r : ℝ} (hr : 0 < r) :
    ConvexOn ℝ (Ici 0) (fun x : ℝ ↦ max (1 - x / r) 0) := by
  -- Proof comment: the positive-side tent kernel is the maximum of an affine function and the
  -- constant zero function.
  have haff : ConvexOn ℝ (Ici 0) (fun x : ℝ ↦ 1 - x / r) := by
    refine ⟨convex_Ici (0 : ℝ), ?_⟩
    intro x hx y hy a b ha hb hab
    have hEq :
        (fun z : ℝ ↦ 1 - z / r) (a • x + b • y) =
          a • (fun z : ℝ ↦ 1 - z / r) x + b • (fun z : ℝ ↦ 1 - z / r) y := by
      dsimp
      field_simp [hr.ne']
      nlinarith [hab]
    exact le_of_eq hEq
  have hzero : ConvexOn ℝ (Ici 0) (fun _ : ℝ ↦ (0 : ℝ)) :=
    convexOn_const 0 (convex_Ici (0 : ℝ))
  change ConvexOn ℝ (Ici 0) (fun x : ℝ ↦ (fun y : ℝ ↦ 1 - y / r) x ⊔ (fun _ : ℝ ↦ (0 : ℝ)) x)
  simpa using haff.sup hzero

/-- Helper for Theorem 15.24: on the nonnegative ray the normalized core is exactly the finite sum
of weighted tent kernels without absolute values. -/
lemma polyaCore_eqOn_nonnegRaySum
    {f : ℝ → ℝ} (n : ℕ) :
    EqOn (polyaCore f n)
      (fun x : ℝ ↦
        Finset.sum (Finset.range (polyaLastIndex n)) fun k ↦
          polygonalWeight (polyaGrid n) (polyaCoreHeight f n) (polyaLastIndex n) k *
            max (1 - x / polyaGrid n (k + 1)) 0)
      (Ici 0) := by
  intro x hx
  -- Proof comment: on `Ici 0`, the absolute value inside `polygonalTentCombination` disappears.
  have habs : |x| = x := abs_of_nonneg (show 0 ≤ x from hx)
  simp [polyaCore, polygonalTentCombination, habs]

/-- Helper for Theorem 15.24: each weighted tent summand in the normalized core is convex on
`Ici 0`. -/
lemma polyaCoreSummand_convexOn
    {f : ℝ → ℝ} (hf_convex : ConvexOn ℝ (Ici 0) f) (hlt : ∀ r > 0, f r < 1)
    (hanti : AntitoneOn f (Ici 0)) (n : ℕ) {k : ℕ} (hk : k < polyaLastIndex n) :
    ConvexOn ℝ (Ici 0)
      (fun x : ℝ ↦
        polygonalWeight (polyaGrid n) (polyaCoreHeight f n) (polyaLastIndex n) k *
          max (1 - x / polyaGrid n (k + 1)) 0) := by
  have hweight_nonneg :
      0 ≤ polygonalWeight (polyaGrid n) (polyaCoreHeight f n) (polyaLastIndex n) k :=
    polyaCoreWeight_nonneg hf_convex hlt hanti n hk
  have hgrid_pos : 0 < polyaGrid n (k + 1) :=
    polyaGrid_pos n (Nat.succ_pos _)
  -- Proof comment: nonnegative scalar multiples of convex functions are convex.
  change ConvexOn ℝ (Ici 0) (fun x : ℝ ↦
    polygonalWeight (polyaGrid n) (polyaCoreHeight f n) (polyaLastIndex n) k •
      max (1 - x / polyaGrid n (k + 1)) 0)
  simpa [smul_eq_mul] using ConvexOn.smul hweight_nonneg (polyaTentKernel_convexOn hgrid_pos)

/-- Helper for Theorem 15.24: the normalized zero-tail polygonal core is convex on `Ici 0`. -/
lemma polyaCore_convexOn
    {f : ℝ → ℝ} (hf_convex : ConvexOn ℝ (Ici 0) f) (hlt : ∀ r > 0, f r < 1)
    (hanti : AntitoneOn f (Ici 0)) (n : ℕ) :
    ConvexOn ℝ (Ici 0) (polyaCore f n) := by
  let summand : ℕ → ℝ → ℝ := fun k x ↦
    polygonalWeight (polyaGrid n) (polyaCoreHeight f n) (polyaLastIndex n) k *
      max (1 - x / polyaGrid n (k + 1)) 0
  have hsum :
      ∀ m ≤ polyaLastIndex n,
        ConvexOn ℝ (Ici 0) (fun x : ℝ ↦ Finset.sum (Finset.range m) fun k ↦ summand k x) := by
    intro m hm
    induction m with
    | zero =>
        -- Proof comment: the empty-range sum is the zero function.
        simpa [summand] using convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))
    | succ m ihm =>
        have hm' : m ≤ polyaLastIndex n := Nat.le_of_succ_le hm
        have hprev :
            ConvexOn ℝ (Ici 0) (fun x : ℝ ↦ Finset.sum (Finset.range m) fun k ↦ summand k x) :=
          ihm hm'
        have hlast :
            ConvexOn ℝ (Ici 0) (summand m) :=
          polyaCoreSummand_convexOn hf_convex hlt hanti n
            (lt_of_lt_of_le (Nat.lt_succ_self m) hm)
        -- Proof comment: add the final convex tent summand to the inductive convex partial sum.
        simpa [summand, Finset.sum_range_succ] using hprev.add hlast
  -- Proof comment: replace the core by its nonnegative-ray tent-sum normal form and use the finite
  -- convex-sum closure established above.
  have hcoreEq :
      EqOn (polyaCore f n)
        (fun x : ℝ ↦ Finset.sum (Finset.range (polyaLastIndex n)) fun k ↦ summand k x)
        (Ici 0) := by
    intro x hx
    simpa [summand] using (polyaCore_eqOn_nonnegRaySum (f := f) n hx)
  have hsumTop :
      ConvexOn ℝ (Ici 0)
        (fun x : ℝ ↦ Finset.sum (Finset.range (polyaLastIndex n)) fun k ↦ summand k x) :=
    hsum (polyaLastIndex n) le_rfl
  exact ConvexOn.congr hsumTop hcoreEq.symm

/-- Helper for Theorem 15.24: the normalized zero-tail polygonal core determines a probability
measure through Example 15.15. -/
lemma isProbabilityMeasure_polyaCoreMeasure
    {f : ℝ → ℝ} (hf_zero : f 0 = 1)
    (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) (n : ℕ) :
    IsProbabilityMeasure (polyaCoreMeasure f n) := by
  -- Proof comment: the normalized core satisfies the owner theorem's polygonal interpolation and
  -- convexity hypotheses.
  have hinterp := polyaCore_isEvenPolygonalInterpolant hlt n
  have hconv := polyaCore_convexOn hf_convex hlt hanti n
  simpa [polyaCoreMeasure] using
    (convexPolygonalInterpolant_isCharacteristicFunction
      (polyaLastIndex n) (polyaGrid n) (polyaCoreHeight f n) (polyaCore f n)
      (polyaGrid_zero n)
      (by
        intro k hk
        exact polyaGrid_strictMono n k)
      (polyaCoreHeight_zero hf_zero hlt n)
      (polyaCoreHeight_last hlt n)
      hinterp hconv).1

/-- Helper for Theorem 15.24: the normalized zero-tail polygonal core is the characteristic
function of its explicit polygonal measure. -/
lemma charFun_polyaCoreMeasure_eq
    {f : ℝ → ℝ} (hf_zero : f 0 = 1)
    (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) (n : ℕ) :
    ∀ t : ℝ, charFun (polyaCoreMeasure f n) t = (polyaCore f n t : ℂ) := by
  -- Proof comment: after the normalized-core setup is verified, Example 15.15 gives the exact
  -- characteristic-function identity.
  have hinterp := polyaCore_isEvenPolygonalInterpolant hlt n
  have hconv := polyaCore_convexOn hf_convex hlt hanti n
  simpa [polyaCoreMeasure] using
    (convexPolygonalInterpolant_isCharacteristicFunction
      (polyaLastIndex n) (polyaGrid n) (polyaCoreHeight f n) (polyaCore f n)
      (polyaGrid_zero n)
      (by
        intro k hk
        exact polyaGrid_strictMono n k)
      (polyaCoreHeight_zero hf_zero hlt n)
      (polyaCoreHeight_last hlt n)
      hinterp hconv).2

/-- Helper for Theorem 15.24: the full polygonal approximant agrees with `f` at every grid node. -/
lemma polyaApprox_apply_nodes
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n : ℕ) {k : ℕ} (hk : k ≤ polyaLastIndex n) :
    polyaApprox f n (polyaGrid n k) = f (polyaGrid n k) := by
  have hcore_node :
      polyaCore f n (polyaGrid n k) = polyaCoreHeight f n k :=
    (polyaCore_isEvenPolygonalInterpolant hlt n).1 k hk
  have hdenom : (1 : ℝ) - f (n + 1) ≠ 0 :=
    ne_of_gt (one_sub_polyaTail_pos hlt n)
  -- Proof comment: the affine rescaling defining `polyaApprox` inverts the normalization of the
  -- core heights exactly at the interpolation nodes.
  rw [polyaApprox, hcore_node, polyaCoreHeight]
  field_simp [hdenom]
  ring

/-- Helper for Theorem 15.24: the full polygonal approximants are even. -/
lemma polyaApprox_even
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n : ℕ) :
    Function.Even (polyaApprox f n) := by
  intro x
  have hcore_even : polyaCore f n (-x) = polyaCore f n x :=
    (polyaCore_isEvenPolygonalInterpolant hlt n).2.2.2 x
  -- Proof comment: adding back the constant tail level preserves evenness.
  simp [polyaApprox, hcore_even]

/-- Helper for Theorem 15.24: on each grid interval the full polygonal approximant is affine with
the secant slope of the sampled values of `f`. -/
lemma polyaApprox_affine
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n : ℕ) {k : ℕ} (hk : k < polyaLastIndex n) {x : ℝ}
    (hx : x ∈ Icc (polyaGrid n k) (polyaGrid n (k + 1))) :
    polyaApprox f n x =
      f (polyaGrid n k) +
        polygonalSegmentSlope (polyaGrid n) (fun j ↦ f (polyaGrid n j)) k *
          (x - polyaGrid n k) := by
  have hcore_affine :
      polyaCore f n x =
        polyaCoreHeight f n k +
          polygonalSegmentSlope (polyaGrid n) (polyaCoreHeight f n) k *
            (x - polyaGrid n k) :=
    (polyaCore_isEvenPolygonalInterpolant hlt n).2.1 k hk hx
  have hdenom : (1 : ℝ) - f (n + 1) ≠ 0 :=
    ne_of_gt (one_sub_polyaTail_pos hlt n)
  -- Proof comment: the constant-tail correction turns the normalized affine core back into the
  -- affine interpolation between the original sampled values of `f`.
  rw [polyaApprox, hcore_affine, polyaCoreHeight, polyaCoreSlope_eq_scaled hlt n k]
  field_simp [hdenom]
  ring

/-- Helper for Theorem 15.24: on each grid interval the full polygonal approximant is the convex
combination of the adjacent sampled values of `f`. -/
lemma polyaApprox_eq_weightedNodeValues
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) (n : ℕ) {k : ℕ} (hk : k < polyaLastIndex n) {x : ℝ}
    (hx : x ∈ Icc (polyaGrid n k) (polyaGrid n (k + 1))) :
    let θ : ℝ := (x - polyaGrid n k) / (polyaGrid n (k + 1) - polyaGrid n k)
    polyaApprox f n x =
      (1 - θ) * f (polyaGrid n k) + θ * f (polyaGrid n (k + 1)) := by
  let θ : ℝ := (x - polyaGrid n k) / (polyaGrid n (k + 1) - polyaGrid n k)
  have hgrid_ne : polyaGrid n (k + 1) - polyaGrid n k ≠ 0 := by
    linarith [polyaGrid_strictMono n k]
  -- Proof comment: rewrite the affine interval formula in barycentric coordinates.
  dsimp [θ]
  rw [polyaApprox_affine hlt n hk hx, polygonalSegmentSlope]
  field_simp [hgrid_ne]
  ring

/-- Helper for Theorem 15.24: the Dirac-plus-core approximating measure is a probability measure. -/
lemma isProbabilityMeasure_polyaApproxMeasure
    {f : ℝ → ℝ} (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) (n : ℕ) :
    IsProbabilityMeasure (polyaApproxMeasure f n) := by
  have hcore_prob : IsProbabilityMeasure (polyaCoreMeasure f n) :=
    isProbabilityMeasure_polyaCoreMeasure hf_zero hf_convex hlt hanti n
  have hcore_univ : polyaCoreMeasure f n univ = 1 :=
    MeasureTheory.isProbabilityMeasure_iff.mp hcore_prob
  have htail_nonneg : 0 ≤ f (n + 1) := (hf_unit (n + 1)).1
  have hone_sub_nonneg : 0 ≤ 1 - f (n + 1) := by
    linarith [(hf_unit (n + 1)).2]
  -- Proof comment: the two scalar weights are nonnegative and sum to `1`, while the core measure
  -- already has total mass `1`.
  rw [MeasureTheory.isProbabilityMeasure_iff]
  calc
    polyaApproxMeasure f n univ =
        ENNReal.ofReal (f (n + 1)) * Measure.dirac 0 univ +
          ENNReal.ofReal (1 - f (n + 1)) * polyaCoreMeasure f n univ := by
            simp [polyaApproxMeasure, Measure.add_apply]
    _ = ENNReal.ofReal (f (n + 1)) + ENNReal.ofReal (1 - f (n + 1)) := by
          simp [hcore_univ]
    _ = ENNReal.ofReal (f (n + 1) + (1 - f (n + 1))) := by
          rw [ENNReal.ofReal_add htail_nonneg hone_sub_nonneg]
    _ = 1 := by simp

/-- Helper for Theorem 15.24: the full approximating measure has characteristic function
`polyaApprox f n`. -/
lemma charFun_polyaApproxMeasure_eq
    {f : ℝ → ℝ} (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) (n : ℕ) :
    ∀ t : ℝ, charFun (polyaApproxMeasure f n) t = (polyaApprox f n t : ℂ) := by
  letI : IsProbabilityMeasure (polyaApproxMeasure f n) :=
    isProbabilityMeasure_polyaApproxMeasure hf_zero hf_unit hf_convex hlt hanti n
  letI : IsProbabilityMeasure (polyaCoreMeasure f n) :=
    isProbabilityMeasure_polyaCoreMeasure hf_zero hf_convex hlt hanti n
  intro t
  have htail_nonneg : 0 ≤ f (n + 1) := (hf_unit (n + 1)).1
  have hone_sub_nonneg : 0 ≤ 1 - f (n + 1) := by
    linarith [(hf_unit (n + 1)).2]
  have hcore_univ : polyaCoreMeasure f n univ = 1 :=
    MeasureTheory.isProbabilityMeasure_iff.mp
      (isProbabilityMeasure_polyaCoreMeasure hf_zero hf_convex hlt hanti n)
  have hfinite_dirac :
      IsFiniteMeasure (ENNReal.ofReal (f (n + 1)) • Measure.dirac (0 : ℝ)) := by
    refine ⟨?_⟩
    simp [Measure.smul_apply]
  have hfinite_core :
      IsFiniteMeasure (ENNReal.ofReal (1 - f (n + 1)) • polyaCoreMeasure f n) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, hcore_univ]
    simp
  have hInt_dirac :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
        (ENNReal.ofReal (f (n + 1)) • Measure.dirac (0 : ℝ)) := by
    simpa [mul_assoc] using
      (@integrableComplexExpKernel
        (ENNReal.ofReal (f (n + 1)) • Measure.dirac (0 : ℝ)) hfinite_dirac t)
  have hInt_core :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
        (ENNReal.ofReal (1 - f (n + 1)) • polyaCoreMeasure f n) := by
    simpa [mul_assoc] using
      (@integrableComplexExpKernel
        (ENNReal.ofReal (1 - f (n + 1)) • polyaCoreMeasure f n) hfinite_core t)
  -- Proof comment: the full approximant is exactly the Dirac-plus-core convex combination, so
  -- its characteristic function is the same convex combination of the two characteristic
  -- functions.
  rw [MeasureTheory.charFun_apply_real, polyaApproxMeasure,
    integral_add_measure hInt_dirac hInt_core, integral_smul_measure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal htail_nonneg, ENNReal.toReal_ofReal hone_sub_nonneg]
  rw [← MeasureTheory.charFun_apply_real, ← MeasureTheory.charFun_apply_real]
  calc
    (((f (n + 1) : ℝ) : ℂ) * charFun (Measure.dirac 0) t) +
        (((1 - f (n + 1) : ℝ) : ℂ) * charFun (polyaCoreMeasure f n) t) =
      (((f (n + 1) : ℝ) : ℂ) * 1) +
        (((1 - f (n + 1) : ℝ) : ℂ) * (polyaCore f n t : ℂ)) := by
          rw [MeasureTheory.charFun_dirac,
            charFun_polyaCoreMeasure_eq hf_zero hf_convex hlt hanti n]
          simp
    _ = (polyaApprox f n t : ℂ) := by
          simp [polyaApprox, mul_comm]

/-- Helper for Theorem 15.24: if the grid mesh is smaller than a continuity radius around a
nonnegative point `x`, then the `n`th polygonal approximant is `ε`-close to `f x`. -/
lemma polyaApprox_dist_lt_of_mesh
    {f : ℝ → ℝ} (hlt : ∀ r > 0, f r < 1) {x ε δ : ℝ} (hx : 0 ≤ x)
    (hδ : ∀ ⦃y : ℝ⦄, dist y x < δ → dist (f y) (f x) < ε)
    (n : ℕ) (hx_lt_last : x < n + 1) (hmesh : 1 / (n + 1 : ℝ) < δ) :
    dist (polyaApprox f n x) (f x) < ε := by
  have hlast_pos : 0 < polyaLastIndex n := by
    dsimp [polyaLastIndex]
    positivity
  have hx_before_last : x < polyaGrid n (polyaLastIndex n) := by
    simpa [polyaGrid_lastIndex n] using hx_lt_last
  obtain ⟨k, hk, hxk⟩ :=
    exists_polygonalInterval
      (polyaLastIndex n) (polyaGrid n) (polyaGrid_zero n)
      (by
        intro j hj
        exact polyaGrid_strictMono n j)
      hlast_pos hx hx_before_last
  have hleft_dist : dist (polyaGrid n k) x < δ := by
    have hleft_le : x - polyaGrid n k ≤ 1 / (n + 1 : ℝ) := by
      calc
        x - polyaGrid n k ≤ polyaGrid n (k + 1) - polyaGrid n k := by
          linarith [hxk.1, hxk.2]
        _ = 1 / (n + 1 : ℝ) := polyaGrid_step n k
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxk.1)]
    linarith
  have hright_dist : dist (polyaGrid n (k + 1)) x < δ := by
    have hright_le : polyaGrid n (k + 1) - x ≤ 1 / (n + 1 : ℝ) := by
      calc
        polyaGrid n (k + 1) - x ≤ polyaGrid n (k + 1) - polyaGrid n k := by
          linarith [hxk.1, hxk.2]
        _ = 1 / (n + 1 : ℝ) := polyaGrid_step n k
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxk.2)]
    linarith
  have hleft_val : |f (polyaGrid n k) - f x| < ε := by
    simpa [Real.dist_eq] using hδ hleft_dist
  have hright_val : |f (polyaGrid n (k + 1)) - f x| < ε := by
    simpa [Real.dist_eq] using hδ hright_dist
  let θ : ℝ := (x - polyaGrid n k) / (polyaGrid n (k + 1) - polyaGrid n k)
  have hθ_nonneg : 0 ≤ θ := by
    have hdiff_pos : 0 < polyaGrid n (k + 1) - polyaGrid n k := by
      linarith [polyaGrid_strictMono n k]
    dsimp [θ]
    exact div_nonneg (sub_nonneg.mpr hxk.1) hdiff_pos.le
  have hθ_le_one : θ ≤ 1 := by
    have hdiff_pos : 0 < polyaGrid n (k + 1) - polyaGrid n k := by
      linarith [polyaGrid_strictMono n k]
    dsimp [θ]
    rw [div_le_one hdiff_pos]
    linarith [hxk.1, hxk.2]
  have hone_sub_nonneg : 0 ≤ 1 - θ := by
    linarith
  have hcomb :
      polyaApprox f n x =
        (1 - θ) * f (polyaGrid n k) + θ * f (polyaGrid n (k + 1)) := by
    simpa [θ] using polyaApprox_eq_weightedNodeValues hlt n hk hxk
  have hnorm : |polyaApprox f n x - f x| < ε := by
    rw [hcomb]
    have hrewrite :
        (1 - θ) * f (polyaGrid n k) + θ * f (polyaGrid n (k + 1)) - f x =
          (1 - θ) * (f (polyaGrid n k) - f x) +
            θ * (f (polyaGrid n (k + 1)) - f x) := by
      ring
    rw [hrewrite]
    calc
      |(1 - θ) * (f (polyaGrid n k) - f x) +
          θ * (f (polyaGrid n (k + 1)) - f x)| ≤
        |(1 - θ) * (f (polyaGrid n k) - f x)| +
          |θ * (f (polyaGrid n (k + 1)) - f x)| := abs_add_le _ _
      _ = (1 - θ) * |f (polyaGrid n k) - f x| +
            θ * |f (polyaGrid n (k + 1)) - f x| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hone_sub_nonneg, abs_of_nonneg hθ_nonneg]
      _ < (1 - θ) * ε + θ * ε := by
            by_cases hθ_zero : θ = 0
            · rw [hθ_zero]
              simpa using hleft_val
            · have hθ_pos : 0 < θ := by
                exact lt_of_le_of_ne hθ_nonneg (by simpa [eq_comm] using hθ_zero)
              have hleft_le : (1 - θ) * |f (polyaGrid n k) - f x| ≤ (1 - θ) * ε := by
                exact mul_le_mul_of_nonneg_left hleft_val.le hone_sub_nonneg
              have hright_lt :
                  θ * |f (polyaGrid n (k + 1)) - f x| < θ * ε := by
                exact mul_lt_mul_of_pos_left hright_val hθ_pos
              exact add_lt_add_of_le_of_lt hleft_le hright_lt
      _ = ε := by ring
  simpa [Real.dist_eq] using hnorm

/-- Helper for Theorem 15.24: at every nonnegative frequency, the polygonal approximants are
eventually uniformly close to `f`. -/
lemma polyaApprox_eventually_close_nonneg
    {f : ℝ → ℝ} (hf_cont : Continuous f)
    (hlt : ∀ r > 0, f r < 1) {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, dist (polyaApprox f n x) (f x) < ε := by
  have hcontx : ContinuousAt f x := hf_cont.continuousAt
  rcases (Metric.continuousAt_iff.mp hcontx) ε hε with ⟨δ, hδpos, hδ⟩
  obtain ⟨Nδ, hNδ⟩ := exists_nat_one_div_lt hδpos
  let N := max Nδ (Nat.ceil x)
  refine ⟨N, ?_⟩
  intro n hn
  have hnδ : Nδ ≤ n := le_trans (le_max_left _ _) hn
  have hnceil : Nat.ceil x ≤ n := le_trans (le_max_right _ _) hn
  have hx_lt_last : x < n + 1 := by
    have hx_le : x ≤ Nat.ceil x := Nat.le_ceil x
    have hceil_le : (Nat.ceil x : ℝ) ≤ n := by
      exact_mod_cast hnceil
    linarith
  have hmesh : 1 / (n + 1 : ℝ) < δ := by
    have hstep_le : (Nδ + 1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.succ_le_succ hnδ
    have hmesh_le : 1 / (n + 1 : ℝ) ≤ 1 / (Nδ + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity : 0 < (Nδ + 1 : ℝ)) hstep_le
    exact lt_of_le_of_lt hmesh_le hNδ
  -- Proof comment: once the mesh and tail are small enough, the local interval estimate applies.
  exact polyaApprox_dist_lt_of_mesh hlt hx (by
    intro y hy
    exact hδ hy) n hx_lt_last hmesh

/-- Helper for Theorem 15.24: at every nonnegative frequency, the polygonal approximants converge
pointwise back to `f`. -/
lemma tendsto_polyaApprox_nonneg
    {f : ℝ → ℝ} (hf_cont : Continuous f)
    (hlt : ∀ r > 0, f r < 1) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n ↦ polyaApprox f n x) atTop (𝓝 (f x)) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  exact polyaApprox_eventually_close_nonneg hf_cont hlt hx hε

/-- Helper for Theorem 15.24: for each fixed real frequency, the polygonal approximants converge
pointwise back to `f`. -/
lemma tendsto_polyaApprox
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_even : Function.Even f)
    (hlt : ∀ r > 0, f r < 1) (t : ℝ) :
    Tendsto (fun n ↦ polyaApprox f n t) atTop (𝓝 (f t)) := by
  let x : ℝ := |t|
  have htarget : f x = f t := by
    by_cases ht : 0 ≤ t
    · simp [x, abs_of_nonneg ht]
    · have ht' : t < 0 := lt_of_not_ge ht
      simpa [x, abs_of_neg ht'] using (hf_even t)
  have hrewrite :
      (fun n ↦ polyaApprox f n t) = fun n ↦ polyaApprox f n x := by
    funext n
    by_cases ht : 0 ≤ t
    · simp [x, abs_of_nonneg ht]
    · have ht' : t < 0 := lt_of_not_ge ht
      simpa [x, abs_of_neg ht'] using (polyaApprox_even hlt n t).symm
  rw [hrewrite]
  simpa [htarget] using
    tendsto_polyaApprox_nonneg hf_cont hlt (x := x) (by simp [x])

/-- Helper for Theorem 15.24: in the strict-tail branch, the `n`th Pólya approximant defines a
probability measure on `ℝ`. -/
noncomputable def polyaApproxProbabilityMeasure
    {f : ℝ → ℝ} (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨polyaApproxMeasure f n,
    isProbabilityMeasure_polyaApproxMeasure hf_zero hf_unit hf_convex hlt hanti n⟩

/-- Helper for Theorem 15.24: transport the strict-tail Pólya approximant law from `ℝ` to `ℝ¹`
along the unique coordinate axis. -/
noncomputable def polyaApproxEuclideanLaw
    {f : ℝ → ℝ} (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) (n : ℕ) :
    ProbabilityMeasure E1 :=
  ProbabilityMeasure.map
    (polyaApproxProbabilityMeasure hf_zero hf_unit hf_convex hlt hanti n)
    (continuous_single_zero.measurable.aemeasurable)

/-- Helper for Theorem 15.24: after transport to `ℝ¹`, the characteristic functions of the
strict-tail Pólya approximant laws converge pointwise to `x ↦ (f (x 0) : ℂ)`. -/
lemma tendsto_charFun_polyaApproxEuclideanLaw
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_even : Function.Even f) (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) :
    ∀ x : E1,
      Tendsto
        (fun n ↦ charFun (polyaApproxEuclideanLaw hf_zero hf_unit hf_convex hlt hanti n :
          Measure E1) x)
        atTop (𝓝 (((f (x 0) : ℝ) : ℂ))) := by
  intro x
  have hrewrite :
      (fun n ↦ charFun (polyaApproxEuclideanLaw hf_zero hf_unit hf_convex hlt hanti n :
          Measure E1) x) =
        fun n : ℕ ↦ (polyaApprox f n (x 0) : ℂ) := by
    funext n
    calc
      charFun (polyaApproxEuclideanLaw hf_zero hf_unit hf_convex hlt hanti n : Measure E1) x =
          charFun
            (polyaApproxProbabilityMeasure hf_zero hf_unit hf_convex hlt hanti n : Measure ℝ)
            (x 0) := by
              simpa [polyaApproxEuclideanLaw] using
                charFun_map_single_zero
                  (μ := polyaApproxProbabilityMeasure hf_zero hf_unit hf_convex hlt hanti n) x
      _ = (polyaApprox f n (x 0) : ℂ) := by
            simpa [polyaApproxProbabilityMeasure] using
              charFun_polyaApproxMeasure_eq hf_zero hf_unit hf_convex hlt hanti n (x 0)
  have hlimit_real :
      Tendsto (fun n ↦ polyaApprox f n (x 0)) atTop (𝓝 (f (x 0))) :=
    tendsto_polyaApprox hf_cont hf_even hlt (x 0)
  rw [hrewrite]
  exact (Complex.continuous_ofReal.tendsto (f (x 0))).comp hlimit_real

/-- Helper for Theorem 15.24: the transported strict-tail limit `x ↦ (f (x 0) : ℂ)` is
continuous at the origin of `ℝ¹`. -/
lemma continuousAt_polyaLimitEuclidean
    {f : ℝ → ℝ} (hf_cont : Continuous f) :
    ContinuousAt (fun x : E1 ↦ ((f (x 0) : ℝ) : ℂ)) 0 := by
  have hcoordCont : Continuous (fun x : E1 ↦ x (0 : Fin 1)) := by
    fun_prop
  simpa using
    (Complex.continuous_ofReal.comp (hf_cont.comp hcoordCont)).continuousAt

/-- Helper for Theorem 15.24: in the strict-tail branch, the transported Pólya approximant laws
converge to a probability law on `ℝ¹` with characteristic function `x ↦ (f (x 0) : ℂ)`. -/
lemma existsEuclideanLaw_charFun_eq_polyaLimit
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_even : Function.Even f) (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hlt : ∀ r > 0, f r < 1) (hanti : AntitoneOn f (Ici 0)) :
    ∃ Q : ProbabilityMeasure E1,
      ∀ x : E1, charFun (Q : Measure E1) x = (((f (x 0) : ℝ) : ℂ)) := by
  exact
    existsProbabilityMeasureOfTendstoCharFunAtOrigin
      (fun n ↦ polyaApproxEuclideanLaw hf_zero hf_unit hf_convex hlt hanti n)
      (continuousAt_polyaLimitEuclidean hf_cont)
      (tendsto_charFun_polyaApproxEuclideanLaw
        hf_cont hf_even hf_zero hf_unit hf_convex hlt hanti)

-- Proof sketch: approximate `f` on `[0, ∞)` by even convex polygonal interpolants as in
-- `convexPolygonalInterpolant_isCharacteristicFunction`, then apply the one-dimensional
-- continuity-at-zero Lévy reconstruction lemma `existsProbabilityMeasureOfTendstoCharFunAtOrigin`
-- to the pointwise limit of the corresponding characteristic functions.
/-- Helper for Theorem 15.24: a convex function on `Ici 0` that is bounded above by `1` and
normalized by `f 0 = 1` is antitone on the nonnegative ray. -/
lemma convexOn_unitInterval_antitoneOn_nonnegRay
    {f : ℝ → ℝ} (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f) :
    AntitoneOn f (Ici 0) := by
  intro x hx y hy hxy
  by_contra hlt
  have hfxy : f x < f y := lt_of_not_ge hlt
  have hxy_lt : x < y := lt_of_le_of_ne hxy (by
    intro hxy_eq
    subst hxy_eq
    exact lt_irrefl _ hfxy)
  let s : ℝ := (f y - f x) / (y - x)
  have hs_pos : 0 < s := by
    -- Proof comment: a strict increase from `x` to `y` forces a positive secant slope.
    dsimp [s]
    exact div_pos (sub_pos.mpr hfxy) (sub_pos.mpr hxy_lt)
  let z : ℝ := x + (2 - f x) / s
  have hz_mem : z ∈ Ici 0 := by
    -- Proof comment: the correction term is nonnegative because `f x ≤ 1` and `s > 0`.
    have hcorr_nonneg : 0 ≤ (2 - f x) / s := by
      have hx_le_one : f x ≤ 1 := (hf_unit x).2
      have : 0 ≤ 2 - f x := by linarith
      exact div_nonneg this hs_pos.le
    simpa [z] using add_nonneg hx hcorr_nonneg
  have hyz : y ≤ z := by
    have hmul : (y - x) * s = f y - f x := by
      dsimp [s]
      field_simp [sub_ne_zero.mpr hxy_lt.ne.symm]
    have hbound : (y - x) * s < 2 - f x := by
      have hy_le_one : f y ≤ 1 := (hf_unit y).2
      rw [hmul]
      linarith
    have hdiv : y - x < (2 - f x) / s := by
      rw [lt_div_iff₀ hs_pos]
      simpa [mul_comm] using hbound
    dsimp [z]
    linarith
  have hy_ne_x : y ≠ x := ne_of_gt hxy_lt
  have hxz : x < z := by
    have hx_le_one : f x ≤ 1 := (hf_unit x).2
    have hcorr_pos : 0 < (2 - f x) / s := by
      have : 0 < 2 - f x := by linarith
      exact div_pos this hs_pos
    dsimp [z]
    linarith
  have hz_ne_x : z ≠ x := ne_of_gt hxz
  have hsec := hf_convex.secant_mono hx hy hz_mem hy_ne_x hz_ne_x hyz
  have hsec' : s ≤ (f z - f x) / (z - x) := by
    simpa [s] using hsec
  have hmul : s * (z - x) ≤ f z - f x := by
    -- Proof comment: multiplying the monotone secant inequality by the positive denominator moves
    -- the lower bound to the graph value at `z`.
    have hz_sub_nonneg : 0 ≤ z - x := sub_nonneg.mpr hxz.le
    have hmul' : s * (z - x) ≤ ((f z - f x) / (z - x)) * (z - x) :=
      mul_le_mul_of_nonneg_right hsec' hz_sub_nonneg
    have hcancel : ((f z - f x) / (z - x)) * (z - x) = f z - f x := by
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hz_ne_x)]
    exact hmul'.trans_eq hcancel
  have hsz : s * (z - x) = 2 - f x := by
    have hz_sub : z - x = (2 - f x) / s := by
      dsimp [z]
      ring
    rw [hz_sub, mul_div_cancel₀ _ (ne_of_gt hs_pos)]
  have htwo_le : 2 ≤ f z := by
    linarith
  have hz_le_one : f z ≤ 1 := (hf_unit z).2
  linarith

/-- Helper for Theorem 15.24: if the convex nonnegative-ray function from Pólya's criterion hits
the value `1` at one positive point, then it is identically `1`. -/
lemma convexOn_unitInterval_eq_one_of_pos_eq_one
    {f : ℝ → ℝ} (hf_even : Function.Even f) (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f)
    (hanti : AntitoneOn f (Ici 0)) {r : ℝ} (hr_pos : 0 < r) (hr_one : f r = 1) :
    ∀ x : ℝ, f x = 1 := by
  have h_nonneg : ∀ {x : ℝ}, 0 ≤ x → f x = 1 := by
    intro x hx
    by_cases hxr : x ≤ r
    · -- Proof comment: on `[0,r]`, antitonicity pins the graph between `f r = 1` and the upper
      -- bound `1`.
      have hx_ge : f r ≤ f x := hanti hx hr_pos.le hxr
      have hx_le : f x ≤ 1 := (hf_unit x).2
      linarith [hr_one]
    · have hrx : r ≤ x := le_of_not_ge hxr
      have hx_pos : 0 < x := lt_of_lt_of_le hr_pos hrx
      have hsec :=
        hf_convex.secant_mono (by simp) hr_pos.le hx hr_pos.ne' hx_pos.ne' hrx
      have hx_ge_one : 1 ≤ f x := by
        -- Proof comment: the secant from `0` to `r` has slope `0`, so every later secant must be
        -- nonnegative.
        rw [hf_zero, hr_one] at hsec
        have hsec' : 0 ≤ (f x - 1) / x := by
          simpa using hsec
        rcases (div_nonneg_iff.mp hsec') with hnum | hnum
        · exact by linarith
        · linarith
      have hx_le : f x ≤ 1 := (hf_unit x).2
      linarith
  intro x
  by_cases hx : 0 ≤ x
  · exact h_nonneg hx
  · have hneg : 0 ≤ -x := by linarith
    simpa [hf_even x] using h_nonneg hneg

/-- Theorem 15.24: Polya's criterion on `ℝ`: a continuous even function `f : ℝ → ℝ` with values
in `[0,1]`, normalized by `f 0 = 1`, and convex on `[0, ∞)` is the characteristic function of a
probability measure on `ℝ`. -/
theorem exists_probabilityMeasure_charFun_eq_of_continuous_even_convexOn_unitInterval
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_even : Function.Even f) (hf_zero : f 0 = 1)
    (hf_unit : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hf_convex : ConvexOn ℝ (Ici 0) f) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ t : ℝ, charFun μ t = (f t : ℂ) := by
  -- Proof comment: the verified helper lemmas above reduce the source proof to constructing
  -- zero-tail even convex polygonal approximants and showing their characteristic functions
  -- converge pointwise to `f`.
  have hanti : AntitoneOn f (Ici 0) :=
    convexOn_unitInterval_antitoneOn_nonnegRay hf_unit hf_convex
  by_cases hposOne : ∃ r > 0, f r = 1
  · rcases hposOne with ⟨r, hr_pos, hr_one⟩
    have hconst : ∀ x : ℝ, f x = 1 :=
      convexOn_unitInterval_eq_one_of_pos_eq_one
        hf_even hf_zero hf_unit hf_convex hanti hr_pos hr_one
    refine ⟨diracProba 0, ?_⟩
    intro t
    -- Proof comment: once convexity forces `f ≡ 1`, the Dirac mass at `0` has exactly the right
    -- characteristic function.
    simp [MeasureTheory.diracProba, hconst t, MeasureTheory.charFun_dirac]
  · have hlt : ∀ r > 0, f r < 1 := by
      intro r hr_pos
      have hr_le : f r ≤ 1 := (hf_unit r).2
      have hr_ne : f r ≠ 1 := by
        intro hr_eq
        exact hposOne ⟨r, hr_pos, hr_eq⟩
      exact lt_of_le_of_ne hr_le hr_ne
    rcases existsEuclideanLaw_charFun_eq_polyaLimit
        hf_cont hf_even hf_zero hf_unit hf_convex hlt hanti with
      ⟨Q, hQchar⟩
    refine ⟨ProbabilityMeasure.map Q (coordZeroAEMeasurable Q), ?_⟩
    intro t
    -- Proof comment: pushing the limiting law back along the unique coordinate recovers the
    -- original real-valued characteristic function.
    rw [charFun_map_coordZero]
    simpa using hQchar (EuclideanSpace.single (0 : Fin 1) t)
