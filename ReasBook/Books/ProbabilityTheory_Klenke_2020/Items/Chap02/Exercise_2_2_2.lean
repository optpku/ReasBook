/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {U V : Ω → ℝ}

-- Lebesgue measure restricted to the unit interval `[0,1]`.
local notation "unitIntervalVolume" => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Helper for Exercise 2.2.2: the restricted Lebesgue measure on `[0,1]` has total mass `1`. -/
private theorem unitIntervalVolume_univ :
    unitIntervalVolume Set.univ = 1 := by
  -- Proof comment: on the whole space, the restricted measure only sees the interval `[0,1]`,
  -- whose Lebesgue volume is its length.
  rw [Measure.restrict_apply_univ]
  norm_num [Real.volume_Icc]

/-- Helper for Exercise 2.2.2: `unitIntervalVolume` is a probability measure. -/
private instance : IsProbabilityMeasure unitIntervalVolume :=
  ⟨unitIntervalVolume_univ⟩

/-- Helper for Exercise 2.2.2: the centered angular variable used to place the Box-Muller formula
in the canonical polar chart. -/
noncomputable
abbrev centeredAngle (v : ℝ) : ℝ :=
  2 * Real.pi * v - Real.pi

/-- Helper for Exercise 2.2.2: the radial transform appearing in the Box-Muller parameterization.
-/
noncomputable abbrev rayleighMap (u : ℝ) : ℝ :=
  Real.sqrt (-2 * Real.log u)

/-- Helper for Exercise 2.2.2: inverse of the combined polar-input map on the polar target. -/
private noncomputable def polarInputInverse (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (-(p.1 ^ 2 / 2)), (p.2 + Real.pi) / (2 * Real.pi))

/-- The Box-Muller map sends a pair of real parameters `(u, v)` to the corresponding pair of
Gaussian coordinates. -/
noncomputable
def boxMullerPair (u v : ℝ) : ℝ × ℝ :=
  (Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * v),
    Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * v))

/-- Helper for Exercise 2.2.2: the Box-Muller pair is the negative of the canonical polar chart
evaluated at the radius `sqrt (-2 log u)` and the centered angle `2πv - π`. -/
private theorem boxMullerPair_eq_neg_polarCoordShift (u v : ℝ) :
    boxMullerPair u v = -polarCoord.symm (rayleighMap u, centeredAngle v) := by
  -- Proof comment: the centered-angle shift replaces `θ` by `θ - π`, so both trigonometric
  -- coordinates pick up one global minus sign.
  ext
  · rw [boxMullerPair, polarCoord, centeredAngle, rayleighMap]
    simp [sub_eq_add_neg]
    rw [show 2 * Real.pi * v + -Real.pi = 2 * Real.pi * v - Real.pi by ring, Real.cos_sub_pi]
    ring
  · rw [boxMullerPair, polarCoord, centeredAngle, rayleighMap]
    simp [sub_eq_add_neg]
    rw [show 2 * Real.pi * v + -Real.pi = 2 * Real.pi * v - Real.pi by ring, Real.sin_sub_pi]
    ring

/-- Helper for Exercise 2.2.2: independence plus the two marginal uniform laws identifies the law
of `(U,V)` with the product measure on the unit square. -/
private theorem unitIntervalPair_hasLaw
    (hU : HasLaw U unitIntervalVolume P)
    (hV : HasLaw V unitIntervalVolume P)
    (hUV : U ⟂ᵢ[P] V) :
    HasLaw (fun ω ↦ (U ω, V ω)) (Measure.prod unitIntervalVolume unitIntervalVolume) P := by
  letI : IsProbabilityMeasure P := hU.isProbabilityMeasure
  refine ⟨hU.aemeasurable.prodMk hV.aemeasurable, ?_⟩
  -- Proof comment: the finite-measure independence criterion rewrites the pair law directly as the
  -- product of the two marginal pushforwards.
  rw [(indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).mp hUV,
    hU.map_eq, hV.map_eq]

/-- Helper for Exercise 2.2.2: replacing the closed unit square by its interior does not change
the product-restricted Lebesgue measure. -/
private theorem unitIntervalProd_eq_restrict_unitSquareInterior :
    Measure.prod unitIntervalVolume unitIntervalVolume =
      (volume : Measure (ℝ × ℝ)).restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
  -- Proof comment: product-restricted Lebesgue measure is restriction to the square, and the
  -- boundary has zero Lebesgue mass, so we may work on the open square where the inverse map is
  -- smooth.
  calc
    Measure.prod unitIntervalVolume unitIntervalVolume
        = ((volume : Measure ℝ).prod volume).restrict
            (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
          rw [Measure.prod_restrict]
    _ = (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
          rw [Measure.volume_eq_prod]
    _ = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
          rw [Measure.restrict_congr_set]
          rw [Measure.volume_eq_prod]
          exact (Measure.set_prod_ae_eq
            (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
            Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm

/-- Helper for Exercise 2.2.2: points in the polar target are sent by `polarInputInverse` into
the open unit square. -/
private theorem polarInputInverse_mem_unitSquareInterior {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    polarInputInverse p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
  -- Proof comment: positive radius gives an exponential parameter in `(0,1)`, and the affine
  -- angle normalization sends `(-π, π)` exactly to `(0,1)`.
  rcases hp with ⟨hr, hθ⟩
  refine ⟨?_, ?_⟩
  · constructor
    · simpa [polarInputInverse] using Real.exp_pos (-(p.1 ^ 2 / 2))
    · have hsq : 0 < p.1 ^ 2 := sq_pos_of_pos hr
      have hsq' : 0 < p.1 ^ 2 / 2 := by nlinarith
      have hneg : -(p.1 ^ 2 / 2) < 0 := by linarith
      simpa [polarInputInverse] using (Real.exp_lt_one_iff.mpr hneg)
  · have htwoPi : 0 < 2 * Real.pi := by positivity
    constructor
    · have hpos : 0 < p.2 + Real.pi := by nlinarith [hθ.1]
      simpa [polarInputInverse] using div_pos hpos htwoPi
    · have hlt : p.2 + Real.pi < 2 * Real.pi := by nlinarith [hθ.2]
      have hdiv : (p.2 + Real.pi) / (2 * Real.pi) < 1 := by
        have := div_lt_div_of_pos_right hlt htwoPi
        simpa using this
      simpa [polarInputInverse] using hdiv

/-- Helper for Exercise 2.2.2: the polar-input map recovers the original polar coordinates after
applying `polarInputInverse` on the target. -/
private theorem rayleighCenteredAngle_polarInputInverse {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    (rayleighMap (polarInputInverse p).1, centeredAngle (polarInputInverse p).2) = p := by
  -- Proof comment: the inverse map is chosen precisely so that the exponential/logarithm
  -- cancellation reconstructs the radius and the affine normalization reconstructs the angle.
  rcases hp with ⟨hr, hθ⟩
  ext
  · have hsqrt : 0 ≤ p.1 ^ 2 := sq_nonneg p.1
    rw [polarInputInverse, rayleighMap, Real.log_exp]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]
  · have htwoPi : (2 * Real.pi) ≠ 0 := by positivity
    rw [polarInputInverse, centeredAngle]
    field_simp [htwoPi]
    ring

/-- Helper for Exercise 2.2.2: the polar-input map sends the open unit square into the polar
target. -/
private theorem rayleighCenteredAngle_mem_target {q : ℝ × ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) :
    (rayleighMap q.1, centeredAngle q.2) ∈ polarCoord.target := by
  -- Proof comment: on `(0,1)`, the Box-Muller radius is strictly positive, and the affine angle
  -- normalization sends `(0,1)` onto `(-π, π)`.
  rcases hq with ⟨hu, hv⟩
  constructor
  · have hlog : Real.log q.1 < 0 := Real.log_neg hu.1 hu.2
    have hrad : 0 < -2 * Real.log q.1 := by nlinarith
    simpa [rayleighMap] using Real.sqrt_pos.mpr hrad
  · have htwoPi : 0 < 2 * Real.pi := by positivity
    constructor <;> nlinarith [hv.1, hv.2, htwoPi]

/-- Helper for Exercise 2.2.2: on the open unit square, `polarInputInverse` is the inverse of the
polar-input map. -/
private theorem polarInputInverse_rayleighCenteredAngle {q : ℝ × ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) :
    polarInputInverse (rayleighMap q.1, centeredAngle q.2) = q := by
  -- Proof comment: this is the converse exponential/logarithm cancellation on `(0,1)` together
  -- with the inverse affine angle normalization.
  rcases hq with ⟨hu, hv⟩
  ext
  · have hnonneg : 0 ≤ -2 * Real.log q.1 := by
      have hlog : Real.log q.1 < 0 := Real.log_neg hu.1 hu.2
      nlinarith
    rw [polarInputInverse, rayleighMap]
    rw [Real.sq_sqrt hnonneg]
    ring_nf
    rw [Real.exp_log hu.1]
  · have htwoPi : (2 * Real.pi) ≠ 0 := by positivity
    rw [polarInputInverse, centeredAngle]
    apply (div_eq_iff htwoPi).2
    ring

/-- Helper for Exercise 2.2.2: `polarInputInverse` maps the polar target exactly onto the open
unit square. -/
private theorem polarInputInverse_image_target :
    polarInputInverse '' polarCoord.target =
      Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
  -- Proof comment: one inclusion is the target-to-square estimate, and the reverse inclusion uses
  -- the explicit inverse `(rayleighMap, centeredAngle)` on the open square.
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact polarInputInverse_mem_unitSquareInterior hp
  · intro hq
    refine ⟨(rayleighMap q.1, centeredAngle q.2), rayleighCenteredAngle_mem_target hq, ?_⟩
    simpa using polarInputInverse_rayleighCenteredAngle hq

/-- Helper for Exercise 2.2.2: the product of two centered standard Gaussians is invariant under
global negation. -/
private theorem gaussianProd_map_neg :
    Measure.map (fun z : ℝ × ℝ ↦ -z) ((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  -- Proof comment: map each Gaussian factor by `x ↦ -x`, use the one-dimensional symmetry of the
  -- centered Gaussian, and then reassemble the product.
  calc
    Measure.map (fun z : ℝ × ℝ ↦ -z) ((gaussianReal 0 1).prod (gaussianReal 0 1))
        = (Measure.map (fun x : ℝ ↦ -x) (gaussianReal 0 1)).prod
            (Measure.map (fun y : ℝ ↦ -y) (gaussianReal 0 1)) := by
              simpa using (Measure.map_prod_map
                (μa := gaussianReal 0 1) (μc := gaussianReal 0 1)
                (f := fun x : ℝ ↦ -x) (g := fun y : ℝ ↦ -y)
                (by fun_prop) (by fun_prop)).symm
    _ = ((gaussianReal (-0) 1).prod (gaussianReal (-0) 1)) := by
          simpa using congrArg₂ Measure.prod
            (gaussianReal_map_neg (μ := 0) (v := 1))
            (gaussianReal_map_neg (μ := 0) (v := 1))
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by simp

/-- Helper for Exercise 2.2.2: the affine angle normalization sends `(0,1)` exactly to
`(-π, π)`. -/
private theorem centeredAngle_image_unitIntervalInterior :
    centeredAngle '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (-Real.pi) Real.pi := by
  -- Proof comment: solve the affine change of variables explicitly in both directions.
  ext θ
  constructor
  · rintro ⟨v, hv, rfl⟩
    have htwoPi : 0 < 2 * Real.pi := by positivity
    constructor <;> nlinarith [hv.1, hv.2, htwoPi]
  · intro hθ
    refine ⟨(θ + Real.pi) / (2 * Real.pi), ?_, ?_⟩
    · have htwoPi : 0 < 2 * Real.pi := by positivity
      constructor
      · have hpos : 0 < θ + Real.pi := by nlinarith [hθ.1]
        simpa using div_pos hpos htwoPi
      · have hlt : θ + Real.pi < 2 * Real.pi := by nlinarith [hθ.2]
        have hdiv : (θ + Real.pi) / (2 * Real.pi) < 1 := by
          have := div_lt_div_of_pos_right hlt htwoPi
          simpa using this
        simpa using hdiv
    · have htwoPi : (2 * Real.pi) ≠ 0 := by positivity
      rw [centeredAngle]
      field_simp [htwoPi]
      ring

/-- Helper for Exercise 2.2.2: the affine angle map scales Lebesgue measure by `(2π)⁻¹`. -/
private theorem centeredAngle_map_volume :
    Measure.map centeredAngle (volume : Measure ℝ) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹) • (volume : Measure ℝ) := by
  -- Proof comment: decompose `centeredAngle` into a dilation followed by a translation; only the
  -- dilation changes Lebesgue measure.
  have htwoPi : (2 * Real.pi) ≠ 0 := by positivity
  calc
    Measure.map centeredAngle (volume : Measure ℝ)
        = Measure.map (fun x : ℝ ↦ x + (-Real.pi))
            (Measure.map (fun x : ℝ ↦ (2 * Real.pi) * x) (volume : Measure ℝ)) := by
              rw [show centeredAngle =
                (fun x : ℝ ↦ x + (-Real.pi)) ∘ fun x : ℝ ↦ (2 * Real.pi) * x by
                  funext x
                  dsimp [centeredAngle]
                  ring]
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map (fun x : ℝ ↦ x + (-Real.pi))
          (ENNReal.ofReal |(2 * Real.pi)⁻¹| • (volume : Measure ℝ)) := by
            rw [Real.map_volume_mul_left htwoPi]
    _ = ENNReal.ofReal |(2 * Real.pi)⁻¹| •
          Measure.map (fun x : ℝ ↦ x + (-Real.pi)) (volume : Measure ℝ) := by
            rw [Measure.map_smul]
    _ = ENNReal.ofReal |(2 * Real.pi)⁻¹| • (volume : Measure ℝ) := by
          rw [map_add_right_eq_self]
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) • (volume : Measure ℝ) := by
          congr 1
          rw [abs_of_pos]
          positivity

/-- Helper for Exercise 2.2.2: the angular coordinate has constant density `(2π)⁻¹` on
`(-π, π)`. -/
private theorem centeredAngle_map_unitIntervalInterior :
    Measure.map centeredAngle ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) =
      ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)).withDensity
        (fun _ ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹)) := by
  -- Proof comment: restrict the global affine scaling law to the image interval.
  have hpreimage :
      centeredAngle ⁻¹' (Set.Ioo (-Real.pi) Real.pi) = Set.Ioo (0 : ℝ) 1 := by
    rw [← centeredAngle_image_unitIntervalInterior]
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have htwoPi : 0 < 2 * Real.pi := by positivity
      have : y = x := by
        dsimp [centeredAngle] at hxy
        nlinarith [hxy, htwoPi]
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  calc
    Measure.map centeredAngle ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))
        = (Measure.map centeredAngle (volume : Measure ℝ)).restrict
            (Set.Ioo (-Real.pi) Real.pi) := by
              rw [Measure.restrict_map (μ := (volume : Measure ℝ)) (f := centeredAngle)
                (by fun_prop) measurableSet_Ioo, hpreimage]
    _ = (ENNReal.ofReal ((2 * Real.pi)⁻¹) • (volume : Measure ℝ)).restrict
          (Set.Ioo (-Real.pi) Real.pi) := by
            rw [centeredAngle_map_volume]
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) •
          ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)) := by
            rw [Measure.restrict_smul]
    _ = ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)).withDensity
          (fun _ ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹)) := by
            rw [← MeasureTheory.withDensity_const]

/-- Helper for Exercise 2.2.2: the inverse radial parametrization is sent back to the radius by
`rayleighMap`. -/
private theorem rayleighMap_expNegHalfSq {r : ℝ} (hr : 0 < r) :
    rayleighMap (Real.exp (-(r ^ 2 / 2))) = r := by
  -- Proof comment: on positive radii, the exponential and logarithm cancel and the square root
  -- recovers `r`.
  rw [rayleighMap, Real.log_exp]
  ring_nf
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]

/-- Helper for Exercise 2.2.2: the inverse radial parametrization maps `(0, ∞)` exactly onto
`(0,1)`. -/
private theorem expNegHalfSq_image_Ioi :
    (fun r : ℝ ↦ Real.exp (-(r ^ 2 / 2))) '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
  -- Proof comment: positivity is immediate from the exponential, and surjectivity uses the
  -- explicit inverse `rayleighMap`.
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · simpa using Real.exp_pos (-(r ^ 2 / 2))
    · have hneg : -(r ^ 2 / 2) < 0 := by
        have hr0 : 0 < r := hr
        have : 0 < r ^ 2 / 2 := by nlinarith [sq_pos_of_pos hr0]
        linarith
      simpa using (Real.exp_lt_one_iff.mpr hneg)
  · intro hu
    refine ⟨rayleighMap u, ?_, ?_⟩
    · have hlog : Real.log u < 0 := Real.log_neg hu.1 hu.2
      have hrad : 0 < -2 * Real.log u := by nlinarith
      simpa [rayleighMap] using Real.sqrt_pos.mpr hrad
    · have hnonneg : 0 ≤ -2 * Real.log u := by
        have hlog : Real.log u < 0 := Real.log_neg hu.1 hu.2
        nlinarith
      change Real.exp (-((Real.sqrt (-2 * Real.log u)) ^ 2 / 2)) = u
      rw [Real.sq_sqrt hnonneg]
      ring_nf
      rw [Real.exp_log hu.1]

/-- Helper for Exercise 2.2.2: the inverse radial map already packages the one-dimensional
change-of-variables formula in the exact Rayleigh normal form needed later. -/
private theorem rayleighInverse_lintegral_changeOfVariables (f : ℝ → ENNReal) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * Real.exp (-(r ^ 2 / 2))) * f r =
      ∫⁻ u in Set.Ioo (0 : ℝ) 1, f (rayleighMap u) := by
  let g : ℝ → ℝ := fun r ↦ Real.exp (-(r ^ 2 / 2))
  have hg_derivAt :
      ∀ x, HasDerivAt g (-(x * Real.exp (-(x ^ 2 / 2)))) x := by
    intro x
    -- Proof comment: differentiate the exponential parameterization once; the sign is chosen so
    -- the Jacobian contribution is the positive Rayleigh density.
    have h_inner : HasDerivAt (fun r : ℝ ↦ -(r ^ 2 / 2)) (-x) x := by
      have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2 / 2) x x := by
        simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          ((hasDerivAt_id x).pow 2).div_const (2 : ℝ)
      simpa using hsq.neg
    simpa [g, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp (-(x ^ 2 / 2))).comp x h_inner
  have hg_deriv :
      ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt g (-(x * Real.exp (-(x ^ 2 / 2)))) (Set.Ioi (0 : ℝ)) x := by
    intro x hx
    exact (hg_derivAt x).hasDerivWithinAt
  have hg_antitone : AntitoneOn g (Set.Ioi (0 : ℝ)) := by
    -- Proof comment: the derivative is nonpositive on `(0,∞)`, so the inverse-radius map is
    -- antitone on that interval.
    refine antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ)) (f := g) ?_ ?_ ?_
    · intro x hx
      exact (hg_derivAt x).continuousAt.continuousWithinAt
    · intro x hx
      exact (hg_derivAt x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa [interior_Ioi] using hx
      have hnonneg : 0 ≤ x * Real.exp (-(x ^ 2 / 2)) := le_of_lt <| mul_pos hx' (Real.exp_pos _)
      rw [(hg_derivAt x).deriv]
      exact neg_nonpos.mpr hnonneg
  have hchange :
      ∫⁻ u in g '' Set.Ioi (0 : ℝ), f (rayleighMap u) =
        ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (-(-(r * Real.exp (-(r ^ 2 / 2))))) * f (rayleighMap (g r)) := by
    -- Proof comment: this is the specialized Jacobian formula for the inverse-radius map.
    simpa [g] using
      (lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
        (s := Set.Ioi (0 : ℝ)) (f := g)
        (f' := fun r ↦ -(r * Real.exp (-(r ^ 2 / 2))))
        measurableSet_Ioi hg_deriv hg_antitone (fun u ↦ f (rayleighMap u)))
  rw [expNegHalfSq_image_Ioi] at hchange
  symm
  calc
    ∫⁻ u in Set.Ioo (0 : ℝ) 1, f (rayleighMap u) =
        ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (-(-(r * Real.exp (-(r ^ 2 / 2))))) * f (rayleighMap (g r)) := hchange
    _ = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * Real.exp (-(r ^ 2 / 2))) * f r := by
          refine setLIntegral_congr_fun measurableSet_Ioi ?_
          intro r hr
          simp [g, rayleighMap_expNegHalfSq hr]

/-- Helper for Exercise 2.2.2: the radial coordinate has Rayleigh density on `(0, ∞)`. -/
private theorem rayleighMap_map_unitIntervalInterior :
    Measure.map rayleighMap ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) =
      ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r ↦ ENNReal.ofReal (r * Real.exp (-(r ^ 2 / 2)))) := by
  -- Proof comment: apply the one-dimensional change-of-variables formula to the inverse map
  -- `r ↦ exp (-(r^2 / 2))`, whose derivative contributes the Rayleigh density.
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  -- Proof comment: rewrite the mapped measure by `lintegral_map'`, rewrite the target by the
  -- `withDensity` integral formula, and finish with the specialized radius helper.
  rw [lintegral_map' hf.aemeasurable (by fun_prop)]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) hf.aemeasurable]
  exact (rayleighInverse_lintegral_changeOfVariables f).symm

/-- Helper for Exercise 2.2.2: the independent radius-angle map sends the open unit square to the
polar target density. -/
private theorem rayleighCenteredAngle_map_unitSquareInterior :
    Measure.map (fun p : ℝ × ℝ ↦ (rayleighMap p.1, centeredAngle p.2))
      (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))) =
      ((volume : Measure (ℝ × ℝ)).restrict polarCoord.target).withDensity
        (fun p ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2)))) := by
  -- Proof comment: product-measure functoriality packages the one-dimensional radius and angle
  -- laws into the polar density on `(0,∞) × (-π,π)`.
  let μ01 : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)
  let μr : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  let μθ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)
  calc
    Measure.map (fun p : ℝ × ℝ ↦ (rayleighMap p.1, centeredAngle p.2)) (μ01.prod μ01)
        = (Measure.map rayleighMap μ01).prod (Measure.map centeredAngle μ01) := by
            -- Proof comment: split the deterministic map into its independent coordinate maps.
            simpa [μ01] using
              (Measure.map_prod_map
                (μa := μ01) (μc := μ01)
                (f := rayleighMap) (g := centeredAngle)
                (by fun_prop) (by fun_prop)).symm
    _ = (μr.withDensity (fun r ↦ ENNReal.ofReal (r * Real.exp (-(r ^ 2 / 2))))).prod
          (μθ.withDensity (fun _ ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹))) := by
            rw [rayleighMap_map_unitIntervalInterior, centeredAngle_map_unitIntervalInterior]
    _ = (μr.prod μθ).withDensity
          (fun p ↦ ENNReal.ofReal (p.1 * Real.exp (-(p.1 ^ 2 / 2))) *
            ENNReal.ofReal ((2 * Real.pi)⁻¹)) := by
            rw [prod_withDensity (by fun_prop) (by fun_prop)]
    _ = (((volume : Measure ℝ).prod volume).restrict
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)).withDensity
          (fun p ↦ ENNReal.ofReal (p.1 * Real.exp (-(p.1 ^ 2 / 2))) *
            ENNReal.ofReal ((2 * Real.pi)⁻¹)) := by
            rw [Measure.prod_restrict]
    _ = ((volume : Measure (ℝ × ℝ)).restrict polarCoord.target).withDensity
          (fun p ↦ ENNReal.ofReal (p.1 * Real.exp (-(p.1 ^ 2 / 2))) *
            ENNReal.ofReal ((2 * Real.pi)⁻¹)) := by
            rw [Measure.volume_eq_prod]
            rfl
    _ = ((volume : Measure (ℝ × ℝ)).restrict polarCoord.target).withDensity
          (fun p ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2)))) := by
            apply withDensity_congr_ae
            filter_upwards
              [ae_restrict_mem (μ := (volume : Measure (ℝ × ℝ)))
                (s := polarCoord.target) polarCoord.open_target.measurableSet]
              with p hp
            rcases hp with ⟨hp1, hp2⟩
            have hnonneg : 0 ≤ p.1 * Real.exp (-(p.1 ^ 2 / 2)) := by
              exact mul_nonneg (le_of_lt hp1) (Real.exp_nonneg _)
            rw [← ENNReal.ofReal_mul hnonneg]
            congr 1
            ring

/-- Helper for Exercise 2.2.2: the product of two standard Gaussian laws has the usual Cartesian
density. -/
private noncomputable def cartesianGaussianDensity (z : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2))

/-- Helper for Exercise 2.2.2: the Gaussian product measure is Lebesgue measure with the standard
two-dimensional Gaussian density. -/
private theorem gaussianProd_eq_cartesianWithDensity :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (volume : Measure (ℝ × ℝ)).withDensity cartesianGaussianDensity := by
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1))
        = (((volume : Measure ℝ).withDensity (gaussianPDF 0 1)).prod
            ((volume : Measure ℝ).withDensity (gaussianPDF 0 1))) := by
            simp [gaussianReal, one_ne_zero]
    _ = (((volume : Measure ℝ).prod volume).withDensity
          (fun z : ℝ × ℝ ↦ gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2)) := by
            rw [prod_withDensity (by fun_prop) (by fun_prop)]
    _ = (volume : Measure (ℝ × ℝ)).withDensity
          (fun z : ℝ × ℝ ↦ gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) := by
            rw [Measure.volume_eq_prod]
    _ = (volume : Measure (ℝ × ℝ)).withDensity cartesianGaussianDensity := by
          refine withDensity_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
          -- Proof comment: collapse the coordinatewise Gaussian factors into the single quadratic
          -- form `x^2 + y^2`.
          have hz1_nonneg : 0 ≤ gaussianPDFReal 0 1 z.1 := gaussianPDFReal_nonneg _ _ _
          rw [cartesianGaussianDensity]
          simp only [gaussianPDF_def]
          rw [← ENNReal.ofReal_mul hz1_nonneg]
          congr 1
          have hreal :
              gaussianPDFReal 0 1 z.1 * gaussianPDFReal 0 1 z.2 =
                Real.pi⁻¹ * (1 / 2 : ℝ) * Real.exp ((-z.2 ^ 2 + -z.1 ^ 2) / 2) := by
            rw [gaussianPDFReal_def]
            norm_num
            have hsqrt_pi :
                (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹ = Real.pi⁻¹ := by
              have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := by positivity
              field_simp [hsqrt_pi_ne]
              nlinarith [Real.sq_sqrt (show 0 ≤ Real.pi by positivity)]
            have hsqrt_two :
                (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
              have hsqrt_two_ne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
              field_simp [hsqrt_two_ne]
              nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
            calc
              (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * Real.exp (-(z.1 ^ 2) / 2) *
                  ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ * Real.exp (-(z.2 ^ 2) / 2))
                  = (((Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹) *
                      ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹)) *
                      (Real.exp (-(z.1 ^ 2) / 2) * Real.exp (-(z.2 ^ 2) / 2)) := by ring
              _ = (Real.pi⁻¹ * (1 / 2 : ℝ)) *
                    (Real.exp (-(z.1 ^ 2) / 2) * Real.exp (-(z.2 ^ 2) / 2)) := by
                      rw [hsqrt_pi, hsqrt_two]
              _ = Real.pi⁻¹ * (1 / 2 : ℝ) *
                    Real.exp (-(z.1 ^ 2) / 2 + -(z.2 ^ 2) / 2) := by
                      rw [← Real.exp_add]
              _ = Real.pi⁻¹ * (1 / 2 : ℝ) * Real.exp ((-z.2 ^ 2 + -z.1 ^ 2) / 2) := by
                      congr 2
                      ring
          simpa [one_div] using hreal

/-- Helper for Exercise 2.2.2: after pulling the Cartesian Gaussian density back through
`polarCoord.symm`, the Jacobian factor becomes the Rayleigh density on the polar target. -/
private theorem polarGaussianDensity_comp_symm {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2))) =
      ENNReal.ofReal p.1 * cartesianGaussianDensity (polarCoord.symm p) := by
  rcases hp with ⟨hr, _hθ⟩
  -- Proof comment: in polar coordinates, the quadratic form `x^2 + y^2` collapses to `r^2`.
  rw [cartesianGaussianDensity, ← ENNReal.ofReal_mul (le_of_lt hr)]
  congr 1
  have hnormSq : (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
    change (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2
    ring_nf
    nlinarith [Real.cos_sq_add_sin_sq p.2]
  rw [hnormSq]
  ring

/-- Helper for Exercise 2.2.2: pushing the polar target density through `polarCoord.symm`
recovers the Cartesian product of two standard Gaussian laws. -/
private theorem polarTargetDensity_map_symm_eq_gaussianProd :
    Measure.map polarCoord.symm
      (((volume : Measure (ℝ × ℝ)).restrict polarCoord.target).withDensity
        (fun p ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2))))) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hcart_meas : Measurable cartesianGaussianDensity := by
    -- Proof comment: the Cartesian Gaussian density is an explicit measurable function of the two
    -- coordinates.
    change Measurable
      (fun z : ℝ × ℝ ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)))
    fun_prop
  rw [gaussianProd_eq_cartesianWithDensity]
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hcomp :
      Measurable fun p : ℝ × ℝ ↦ f (polarCoord.symm p) := hf.comp (by fun_prop)
  -- Proof comment: compare both measures on nonnegative test functions, and use the polar
  -- change-of-variables theorem with the Cartesian Gaussian density folded into the test
  -- function.
  rw [lintegral_map' hf.aemeasurable (by fun_prop)]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) hcomp.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul₀ hcart_meas.aemeasurable hf.aemeasurable]
  have hrewrite :
      ∫⁻ p in polarCoord.target,
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2))) *
          f (polarCoord.symm p) =
        ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 *
            (cartesianGaussianDensity (polarCoord.symm p) * f (polarCoord.symm p)) := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp ↦ ?_
    rw [polarGaussianDensity_comp_symm hp]
    ring
  calc
    ∫⁻ p,
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2))) *
          f (polarCoord.symm p) ∂((volume : Measure (ℝ × ℝ)).restrict polarCoord.target)
        = ∫⁻ p in polarCoord.target,
            ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2))) *
              f (polarCoord.symm p) := rfl
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 *
            (cartesianGaussianDensity (polarCoord.symm p) * f (polarCoord.symm p)) := hrewrite
    _ = ∫⁻ z, cartesianGaussianDensity z * f z := by
          simpa [smul_eq_mul] using
            (lintegral_comp_polarCoord_symm
              (fun z : ℝ × ℝ ↦ cartesianGaussianDensity z * f z))

/-- Helper for Exercise 2.2.2: the deterministic Box-Muller map sends the unit-square product
measure to the product of two standard Gaussian laws. -/
private theorem boxMullerPair_hasLaw_unitSquare :
    HasLaw (fun p : ℝ × ℝ ↦ boxMullerPair p.1 p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1))
      (Measure.prod unitIntervalVolume unitIntervalVolume) := by
  let pairMap : ℝ × ℝ → ℝ × ℝ := fun p ↦ (rayleighMap p.1, centeredAngle p.2)
  have hbox :
      (fun p : ℝ × ℝ ↦ boxMullerPair p.1 p.2) =
        ((fun z : ℝ × ℝ ↦ -z) ∘ polarCoord.symm) ∘ pairMap := by
    -- Proof comment: the Box-Muller formula is exactly the polar chart followed by one global
    -- sign change coming from the centered-angle shift by `π`.
    funext p
    simpa [pairMap, Function.comp] using boxMullerPair_eq_neg_polarCoordShift p.1 p.2
  refine ⟨?_, ?_⟩
  · -- Proof comment: measurability is immediate from the factorization through the polar chart.
    rw [hbox]
    fun_prop
  have hsource :
      Measure.prod unitIntervalVolume unitIntervalVolume =
        (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))) := by
    -- Proof comment: boundary-nullity lets us replace the closed unit square by its interior,
    -- where the explicit inverse polar map is smooth.
    calc
      Measure.prod unitIntervalVolume unitIntervalVolume
          = (volume : Measure (ℝ × ℝ)).restrict
              (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) :=
            unitIntervalProd_eq_restrict_unitSquareInterior
      _ = (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))) := by
            rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  -- Proof comment: after rewriting to the open square, the map factors through the polar target
  -- density and then through `polarCoord.symm`; the last step is Gaussian symmetry under `z ↦ -z`.
  calc
    Measure.map (fun p : ℝ × ℝ ↦ boxMullerPair p.1 p.2)
        (Measure.prod unitIntervalVolume unitIntervalVolume)
        = Measure.map ((fun z : ℝ × ℝ ↦ -z) ∘ polarCoord.symm)
            (Measure.map pairMap (Measure.prod unitIntervalVolume unitIntervalVolume)) := by
              rw [hbox, ← Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map (fun z : ℝ × ℝ ↦ -z)
          (Measure.map polarCoord.symm
            (Measure.map pairMap (Measure.prod unitIntervalVolume unitIntervalVolume))) := by
            rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map (fun z : ℝ × ℝ ↦ -z)
          (Measure.map polarCoord.symm
            (Measure.map pairMap
              (((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)).prod
                ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))))) := by
            rw [hsource]
    _ = Measure.map (fun z : ℝ × ℝ ↦ -z)
          (Measure.map polarCoord.symm
            (((volume : Measure (ℝ × ℝ)).restrict polarCoord.target).withDensity
              (fun p ↦ ENNReal.ofReal ((2 * Real.pi)⁻¹ * p.1 * Real.exp (-(p.1 ^ 2 / 2)))))) := by
            rw [rayleighCenteredAngle_map_unitSquareInterior]
    _ = Measure.map (fun z : ℝ × ℝ ↦ -z) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            rw [polarTargetDensity_map_symm_eq_gaussianProd]
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)) := gaussianProd_map_neg

-- Proof sketch: compute the law of the radius `R = sqrt (-2 log U)` from the uniform law of `U`,
-- combine it with the uniform angular variable `2πV`, and apply the transformation formula in
-- polar coordinates to identify the pushforward measure with the product of two standard Gaussian
-- laws.
/-- Exercise 2.2.2: If `U` and `V` are independent and both uniformly distributed on `[0,1]`,
then the Box-Muller transform has joint law equal to the product of two standard Gaussian laws. -/
theorem boxMullerPair_hasLaw
    (hU : HasLaw U unitIntervalVolume P)
    (hV : HasLaw V unitIntervalVolume P)
    (hUV : U ⟂ᵢ[P] V)
    :
    HasLaw (fun ω ↦ boxMullerPair (U ω) (V ω))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) P := by
  have hPair : HasLaw (fun ω ↦ (U ω, V ω)) (Measure.prod unitIntervalVolume unitIntervalVolume) P :=
    unitIntervalPair_hasLaw hU hV hUV
  -- Proof comment: once the independent pair `(U,V)` is identified with the unit-square product
  -- law, the target theorem is just the deterministic Box-Muller pushforward composed with `hPair`.
  simpa [Function.comp] using (HasLaw.comp boxMullerPair_hasLaw_unitSquare hPair)

-- Proof sketch: rewrite independence in terms of the pushforward law of the pair
-- `(boxMullerPair (U ω) (V ω)).1, (boxMullerPair (U ω) (V ω)).2`, then use
-- `boxMullerPair_hasLaw` to identify this law with the product of the two marginal Gaussian laws.
/-- The two coordinates produced by the Box-Muller transform are independent. -/
theorem boxMuller_fst_indepFun_snd
    (hU : HasLaw U unitIntervalVolume P)
    (hV : HasLaw V unitIntervalVolume P)
    (hUV : U ⟂ᵢ[P] V)
    :
    (fun ω ↦ (boxMullerPair (U ω) (V ω)).1) ⟂ᵢ[P]
      (fun ω ↦ (boxMullerPair (U ω) (V ω)).2) := by
  let F : Ω → ℝ × ℝ := fun ω ↦ boxMullerPair (U ω) (V ω)
  letI : IsProbabilityMeasure P := hU.isProbabilityMeasure
  have hJoint : HasLaw F ((gaussianReal 0 1).prod (gaussianReal 0 1)) P :=
    boxMullerPair_hasLaw hU hV hUV
  have hFstLaw :
      HasLaw Prod.fst (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (measurePreserving_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
  have hSndLaw :
      HasLaw Prod.snd (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (measurePreserving_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
  have hFst : HasLaw (Prod.fst ∘ F) (gaussianReal 0 1) P := HasLaw.comp hFstLaw hJoint
  have hSnd : HasLaw (Prod.snd ∘ F) (gaussianReal 0 1) P := HasLaw.comp hSndLaw hJoint
  have hEta : (fun ω ↦ ((Prod.fst ∘ F) ω, (Prod.snd ∘ F) ω)) = F := by
    -- Proof comment: the independence criterion is stated for the explicit pair map, which is
    -- definitionally the same random vector `F`.
    funext ω
    exact Prod.eta (F ω)
  -- Proof comment: the joint law already identifies the pair map with the product of the Gaussian
  -- marginals, so the standard independence criterion applies directly.
  refine (indepFun_iff_map_prod_eq_prod_map_map hFst.aemeasurable hSnd.aemeasurable).2 ?_
  rw [hEta, hJoint.map_eq, hFst.map_eq, hSnd.map_eq]

-- Proof sketch: compose the joint-law statement `boxMullerPair_hasLaw` with the first-coordinate
-- projection and use that the first marginal of the product measure
-- `(gaussianReal 0 1).prod (gaussianReal 0 1)` is `gaussianReal 0 1`.
/-- The first Box-Muller coordinate has the standard Gaussian law. -/
theorem boxMuller_fst_hasLaw
    (hU : HasLaw U unitIntervalVolume P)
    (hV : HasLaw V unitIntervalVolume P)
    (hUV : U ⟂ᵢ[P] V)
    :
    HasLaw (fun ω ↦ (boxMullerPair (U ω) (V ω)).1) (gaussianReal 0 1) P := by
  let F : Ω → ℝ × ℝ := fun ω ↦ boxMullerPair (U ω) (V ω)
  have hJoint : HasLaw F ((gaussianReal 0 1).prod (gaussianReal 0 1)) P :=
    boxMullerPair_hasLaw hU hV hUV
  have hFstLaw :
      HasLaw Prod.fst (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (measurePreserving_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
  -- Proof comment: compose the joint Gaussian product law with the first projection, which is
  -- measure-preserving for a product of probability measures.
  simpa [F, Function.comp] using (HasLaw.comp hFstLaw hJoint)

-- Proof sketch: compose the joint-law statement `boxMullerPair_hasLaw` with the second-coordinate
-- projection and use that the second marginal of the product measure
-- `(gaussianReal 0 1).prod (gaussianReal 0 1)` is `gaussianReal 0 1`.
/-- The second Box-Muller coordinate has the standard Gaussian law. -/
theorem boxMuller_snd_hasLaw
    (hU : HasLaw U unitIntervalVolume P)
    (hV : HasLaw V unitIntervalVolume P)
    (hUV : U ⟂ᵢ[P] V)
    :
    HasLaw (fun ω ↦ (boxMullerPair (U ω) (V ω)).2) (gaussianReal 0 1) P := by
  let F : Ω → ℝ × ℝ := fun ω ↦ boxMullerPair (U ω) (V ω)
  have hJoint : HasLaw F ((gaussianReal 0 1).prod (gaussianReal 0 1)) P :=
    boxMullerPair_hasLaw hU hV hUV
  have hSndLaw :
      HasLaw Prod.snd (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (measurePreserving_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
  -- Proof comment: the second projection of a Gaussian product is again the standard Gaussian.
  simpa [F, Function.comp] using (HasLaw.comp hSndLaw hJoint)
