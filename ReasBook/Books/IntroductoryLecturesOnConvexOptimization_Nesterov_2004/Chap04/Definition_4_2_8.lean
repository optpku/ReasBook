/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.8 lies in uniformly convex differentiable analysis on real Hilbert spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* mathlib `StrongConvexOn`
* Chapter 2 `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Definition_2_2`
* Chapter 3 `Definition_3_2_2`, which recalls strong convexity by the canonical owner and keeps
  the source first-order presentation as companion API

Best owner abstraction:
* source-facing: the degree-`p` uniform-convexity inequality with remainder
  `(1 / p) * σp * ‖y - x‖^p`
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: the first-order lower-support inequality phrased with `gradientWithin d Q`

Primitive data:
* a feasible set `Q`
* a function `d`
* a degree `p`
* a positive parameter `σp`
* at a fixed feasible base point, an explicit within-set gradient witness
  `HasGradientWithinAt d g Q x`

Derived API:
* the source definition: existence of a positive modulus `σp` witnessing the chapter's
  first-order lower-support inequality with remainder `(1 / p) * σp * ‖y - x‖^p`
* the canonical fixed-modulus owner predicate `UniformConvexOn` as a one-way companion
* the `gradientWithin` corollary obtained from `DifferentiableWithinAt ℝ d Q x`

This file therefore keeps the source first-order power lower-support condition as the main
surface for Definition 4.2.8, and records mathlib's fixed-modulus owner `UniformConvexOn` only
as a canonical companion that implies the source inequality. -/

/-- The degree-`p` modulus `r ↦ (1 / p) * σp * r^p` used in Definition 4.2.8. -/
abbrev uniformConvexPowerModulus (σp p : ℝ) : ℝ → ℝ :=
  fun r ↦ (1 / p) * σp * Real.rpow r p

section

variable {Q : Set E} {p : ℝ} {d : E → ℝ}

/- Definition 4.2.8 is source-facing: `Q` is closed and convex, `d` is differentiable on `Q`,
`p ≥ 2`, and some positive parameter `σp` makes the first-order lower-support inequality with
remainder `(1 / p) * σp * ‖y - x‖^p` hold on `Q`. The canonical owner `UniformConvexOn` is kept
only as a one-way companion that implies this source condition. -/

-- Semantic recall checked with `lean_leansearch`: the relevant mathlib owners are
-- `UniformConvexOn`, `UniformConvexOn.convexOn`, and `gradientWithin`.

namespace UniformConvexOn

/-- A degree-`p` uniformly convex function lies above every feasible tangent plane arising from an
explicit within-set gradient witness, with the power remainder term from Definition 4.2.8. -/
theorem lower_tangent_power_of_hasGradientWithinAt
    {σp : ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (x : E) (hx : x ∈ Q) (g : E) (hgrad : HasGradientWithinAt d g Q x) (y : E) (hy : y ∈ Q) :
    d y ≥ d x + inner ℝ g (y - x) + uniformConvexPowerModulus σp p ‖y - x‖ := by
  let seg : ℝ → E := AffineMap.lineMap x y
  let fseg : ℝ → ℝ := d ∘ seg
  let c : ℝ := uniformConvexPowerModulus σp p ‖y - x‖
  have hmaps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := huniform.1.mapsTo_lineMap hx hy
  -- Compose the feasible gradient witness with the chord `seg`.
  have hderiv :
      HasDerivWithinAt fseg (inner ℝ g (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [fseg, seg] using
      hgrad.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap hmaps (AffineMap.lineMap_apply_zero x y).symm
  have hslope_bound :
      ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 → t ≠ 0 →
        slope fseg 0 t ≤ d y - d x - (1 - t) * c := by
    intro t ht ht0
    have ht_nonneg : 0 ≤ t := ht.1
    have ht_le_one : t ≤ 1 := ht.2
    have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht0)
    have huniform_t :=
      huniform.2 hx hy (sub_nonneg.mpr ht_le_one) ht_nonneg (by ring)
    have hline : seg t = (1 - t) • x + t • y := by
      have hx' : x - t • x = (1 - t) • x := by
        simpa [sub_eq_add_neg] using (sub_smul (1 : ℝ) t x).symm
      calc
        seg t = t • (y - x) + x := by simp [seg, AffineMap.lineMap_apply]
        _ = t • y + (x - t • x) := by
              simp [sub_eq_add_neg, add_left_comm, add_comm]
        _ = t • y + (1 - t) • x := by rw [hx']
        _ = (1 - t) • x + t • y := by ac_rfl
    have hdivide :
        (fseg t - fseg 0) / (t - 0) ≤ d y - d x - (1 - t) * c := by
      dsimp [fseg]
      rw [hline]
      rw [show seg 0 = x by simp [seg], sub_zero]
      have huniform_t' :
          d ((1 - t) • x + t • y) ≤
            (1 - t) • d x + t • d y - (1 - t) * t * c := by
        simpa [smul_eq_mul, c, norm_sub_rev] using huniform_t
      have hnum :
          d ((1 - t) • x + t • y) - d x ≤
            t * (d y - d x - (1 - t) * c) := by
        calc
          d ((1 - t) • x + t • y) - d x
              ≤ ((1 - t) * d x + t * d y - (1 - t) * t * c) - d x := by
                  exact sub_le_sub_right huniform_t' (d x)
          _ = t * (d y - d x - (1 - t) * c) := by ring
      refine (div_le_iff₀ ht_pos).2 ?_
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hnum
    simpa [slope, ht0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdivide
  have hslope_tendsto :
      Filter.Tendsto (slope fseg 0)
        (nhdsWithin 0 (Set.Icc (0 : ℝ) 1 \ {0})) (nhds (inner ℝ g (y - x))) :=
    hasDerivWithinAt_iff_tendsto_slope.mp hderiv
  have hright_tendsto :
      Filter.Tendsto (fun t : ℝ ↦ d y - d x - (1 - t) * c)
        (nhdsWithin 0 (Set.Icc (0 : ℝ) 1 \ {0})) (nhds (d y - d x - c)) := by
    have hcont : Continuous fun t : ℝ ↦ d y - d x - (1 - t) * c := by
      continuity
    have hcont0 : ContinuousAt (fun t : ℝ ↦ d y - d x - (1 - t) * c) 0 := hcont.continuousAt
    simpa using tendsto_nhdsWithin_of_tendsto_nhds hcont0.tendsto
  let u : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hu_mem : ∀ n : ℕ, u n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    dsimp [u]
    constructor
    · positivity
    · have hn : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa [one_div] using inv_le_one_of_one_le₀ hn
  have hu_ne : ∀ n : ℕ, u n ≠ 0 := by
    intro n
    dsimp [u]
    positivity
  have hu_tendsto :
      Filter.Tendsto u Filter.atTop (nhdsWithin 0 (Set.Icc (0 : ℝ) 1 \ {0})) := by
    refine tendsto_nhdsWithin_iff.mpr ?_
    refine ⟨?_, ?_⟩
    · simpa [u, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds (0 : ℝ)))
    · exact Filter.Eventually.of_forall fun n ↦ ⟨hu_mem n, hu_ne n⟩
  have hlimit :
      inner ℝ g (y - x) ≤ d y - d x - c := by
    have hslope_seq :
        Filter.Tendsto (fun n : ℕ ↦ slope fseg 0 (u n)) Filter.atTop
          (nhds (inner ℝ g (y - x))) := hslope_tendsto.comp hu_tendsto
    have hright_seq :
        Filter.Tendsto (fun n : ℕ ↦ d y - d x - (1 - u n) * c) Filter.atTop
          (nhds (d y - d x - c)) := hright_tendsto.comp hu_tendsto
    exact le_of_tendsto_of_tendsto' hslope_seq hright_seq fun n ↦ hslope_bound (hu_mem n) (hu_ne n)
  have hc : c = uniformConvexPowerModulus σp p ‖y - x‖ := rfl
  linarith

/-- A degree-`p` uniformly convex function lies above the tangent plane determined by its
within-set gradient at a feasible base point, with the power remainder term from Definition
4.2.8. -/
theorem lower_tangent_power
    {σp : ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (x : E) (hx : x ∈ Q) (hdiff : DifferentiableWithinAt ℝ d Q x) (y : E) (hy : y ∈ Q) :
    d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
      uniformConvexPowerModulus σp p ‖y - x‖ := by
  simpa using
    huniform.lower_tangent_power_of_hasGradientWithinAt
      x hx (gradientWithin d Q x) hdiff.hasGradientWithinAt y hy

end UniformConvexOn

/-- Definition 4.2.8: `d` is uniformly convex on `Q` of degree `p` if `p ≥ 2` and there exists
a positive parameter `σp` such that, for all `x, y ∈ Q`,
`d y ≥ d x + ⟪∇ d(x), y - x⟫ + (1 / p) * σp * ‖y - x‖^p`. -/
class ExistsPosUniformConvexOn (Q : Set E) (p : ℝ) (d : E → ℝ) : Prop where
  hp : 2 ≤ p
  isClosed : IsClosed Q
  convex : Convex ℝ Q
  differentiableOn : DifferentiableOn ℝ d Q
  lower_tangent_power :
    ∃ σp > 0,
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
          uniformConvexPowerModulus σp p ‖y - x‖

/-- A `ExistsPosUniformConvexOn Q p d` hypothesis canonically supplies the positive lower-support
power witness from Definition 4.2.8. -/
instance [hd : ExistsPosUniformConvexOn Q p d] :
    Fact
      (∃ σp > 0,
        ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
          d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
            uniformConvexPowerModulus σp p ‖y - x‖) where
  out := hd.lower_tangent_power

/-- Any fixed-modulus canonical owner witness implies the corresponding first-order lower-support
power inequality from Definition 4.2.8. -/
theorem uniformConvexOn_imp_lower_tangent_power
    {σp : ℝ}
    (hd : DifferentiableOn ℝ d Q) :
    UniformConvexOn Q (uniformConvexPowerModulus σp p) d →
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
          uniformConvexPowerModulus σp p ‖y - x‖ := by
  intro huniform x y hx hy
  exact huniform.lower_tangent_power x hx (hd x hx) y hy

/-- The source-facing existential surface is definitionally the lower-tangent-power condition. -/
theorem exists_pos_uniformConvexOn_iff_forall_lower_tangent_power :
    ExistsPosUniformConvexOn Q p d ↔
      2 ≤ p ∧
        IsClosed Q ∧
        Convex ℝ Q ∧
        DifferentiableOn ℝ d Q ∧
        ∃ σp > 0,
          ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
            d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
              uniformConvexPowerModulus σp p ‖y - x‖ := by
  constructor
  · intro h
    exact ⟨h.hp, h.isClosed, h.convex, h.differentiableOn, h.lower_tangent_power⟩
  · rintro ⟨hp, hQ_closed, hQ_convex, hd, σp, hσp, hlower⟩
    exact ⟨hp, hQ_closed, hQ_convex, hd, ⟨σp, hσp, hlower⟩⟩

/-- A positive canonical `UniformConvexOn` witness yields the source-facing Definition 4.2.8
condition. -/
theorem existsPosUniformConvexOn_of_existsPosUniformConvexOnOwner
    (hQ_closed : IsClosed Q)
    (hd : DifferentiableOn ℝ d Q) :
    (2 ≤ p ∧ ∃ σp > 0, UniformConvexOn Q (uniformConvexPowerModulus σp p) d) →
      ExistsPosUniformConvexOn Q p d := by
  rintro ⟨hp, σp, hσp, huniform⟩
  refine ⟨hp, hQ_closed, huniform.1, hd, ?_⟩
  exact ⟨σp, hσp, uniformConvexOn_imp_lower_tangent_power hd huniform⟩

end
