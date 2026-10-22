/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_39
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Asymptotics
open scoped Gradient Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Primary domain: constrained finite max-type convex minimization on complete real
inner-product spaces.

Sampled owner-style declarations:
* `maxTypeObjective` in `Definition_2_39`, the owner max objective of a nonempty finite family;
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine max model at a base point;
* `ConvexOn.sup` in mathlib, the canonical owner theorem for pointwise maxima of convex
  functions;
* `hasGradientAt_iff_sub_affineApproximation_isLittleO` in `Definition_1_4_6`, the Chapter 1
  owner bridge from differentiability to a first-order affine remainder estimate.

Best owner abstraction:
* the canonical pair `maxTypeObjective fs` and `maxTypeAffineApproximation fs xStar`.

Primitive data:
* the feasible set `Q`;
* the nonempty component family `fs`;
* componentwise convexity on `Q`;
* differentiability of each component at the base point `xStar`.

Derived API:
* convexity of `Q`, recovered from any componentwise hypothesis `ConvexOn ℝ Q (fs i)` because the
  family has an index;
* the constrained minimizing predicate `IsMinOn (maxTypeObjective fs) Q xStar`;
* the affine lower-model condition
  `maxTypeAffineApproximation fs xStar x ≥ maxTypeObjective fs xStar`.

Source/core/bridge triage:
* source-facing: Theorem 2.39 as the optimality criterion for the max-type objective;
* core/canonical: `maxTypeObjective fs`, `maxTypeAffineApproximation fs xStar`, and `IsMinOn`;
* bridge/view: the pointwise affine-max inequality on `Q`.

No local public alias of the owner max objective or affine model is kept in this file. -/

/-- Helper for Theorem 2.39: if the affine model of one component at `xStar` is strictly below the
level `m` in the direction `x - xStar`, then that component stays strictly below `m` along the
segment issuing from `xStar` for all sufficiently small positive times. -/
private theorem eventually_lt_max_of_affineApproximation_lt
    {f : E → ℝ} {xStar x : E} {m : ℝ}
    (hf : DifferentiableAt ℝ f xStar)
    (hxStar_le : f xStar ≤ m)
    (haff : f xStar + inner ℝ (∇ f xStar) (x - xStar) < m) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), f (xStar + t • (x - xStar)) < m := by
  let d : E := x - xStar
  let δ : ℝ := m - (f xStar + inner ℝ (∇ f xStar) d)
  have hδ : 0 < δ := by
    simpa [d, δ] using sub_pos.mpr haff
  let c : ℝ := δ / (2 * (‖d‖ + 1))
  have hc : 0 < c := by
    have hden : 0 < 2 * (‖d‖ + 1) := by
      positivity
    positivity
  let path : ℝ → E := fun t ↦ xStar + t • d
  have hpath : Tendsto path (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds xStar) := by
    have hcont : Continuous path := by
      dsimp [path]
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hpath0 : Tendsto path (nhds (0 : ℝ)) (nhds (path 0)) := hcont.continuousAt.tendsto
    simpa [path] using
      (hpath0.mono_left nhdsWithin_le_nhds :
        Tendsto path (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (path 0)))
  have hrem :
      ((fun y : E ↦ f y - f xStar - inner ℝ (∇ f xStar) (y - xStar)) ∘ path)
        =o[nhdsWithin (0 : ℝ) (Set.Ioi 0)] ((fun y : E ↦ y - xStar) ∘ path) := by
    exact
      (hasGradientAt_iff_isLittleO.mp hf.hasGradientAt).comp_tendsto hpath
  have hsmall :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖f (path t) - (f xStar + inner ℝ (∇ f xStar) (path t - xStar))‖ ≤
          c * ‖path t - xStar‖ := by
    simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrem.bound hc
  have hIoc : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioc (0 : ℝ) 1 :=
    Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hsmall, hIoc] with t ht_small ht
  have ht_nonneg : 0 ≤ t := le_of_lt ht.1
  have ht_le : t ≤ 1 := ht.2
  have hsub : path t - xStar = t • d := by
    simp [path]
  have hnorm : ‖path t - xStar‖ = t * ‖d‖ := by
    rw [hsub, norm_smul, Real.norm_of_nonneg ht_nonneg]
  have hinner :
      inner ℝ (∇ f xStar) (path t - xStar) = t * inner ℝ (∇ f xStar) d := by
    rw [hsub, inner_smul_right]
  have herr :
      f (path t) - (f xStar + inner ℝ (∇ f xStar) (path t - xStar)) ≤ (δ / 2) * t := by
    have hle :
        f (path t) - (f xStar + inner ℝ (∇ f xStar) (path t - xStar)) ≤
          c * ‖path t - xStar‖ :=
      le_trans (le_abs_self _) ht_small
    rw [hnorm] at hle
    have hratio : ‖d‖ / (‖d‖ + 1) ≤ (1 : ℝ) := by
      have hden : 0 < ‖d‖ + 1 := by positivity
      rw [div_le_iff₀ hden]
      nlinarith [norm_nonneg d]
    have hc_mul' : c * ‖d‖ ≤ δ / 2 := by
      have hne : (‖d‖ + 1 : ℝ) ≠ 0 := by positivity
      calc
        c * ‖d‖ = (δ / 2) * (‖d‖ / (‖d‖ + 1)) := by
          dsimp [c]
          field_simp [hne]
        _ ≤ (δ / 2) * 1 := by
          gcongr
        _ = δ / 2 := by ring
    have hc_mul :
        c * (t * ‖d‖) ≤ (δ / 2) * t := by
      calc
        c * (t * ‖d‖) = t * (c * ‖d‖) := by ring
        _ ≤ t * (δ / 2) := by
              gcongr
        _ = (δ / 2) * t := by ring
    exact hle.trans hc_mul
  have hmain :
      f xStar + inner ℝ (∇ f xStar) (path t - xStar) ≤ m - δ * t := by
    calc
      f xStar + inner ℝ (∇ f xStar) (path t - xStar)
          = (1 - t) * f xStar + t * (f xStar + inner ℝ (∇ f xStar) d) := by
              rw [hinner]
              ring
      _ ≤ (1 - t) * m + t * (f xStar + inner ℝ (∇ f xStar) d) := by
            gcongr
            linarith
      _ = (1 - t) * m + t * (m - δ) := by
            congr 1
            dsimp [δ]
            ring
      _ = m - δ * t := by
            ring
  have hsplit :
      f (path t) =
        (f xStar + inner ℝ (∇ f xStar) (path t - xStar)) +
          (f (path t) - (f xStar + inner ℝ (∇ f xStar) (path t - xStar))) := by
    ring
  have hsum_le : f (path t) ≤ m - (δ / 2) * t := by
    rw [hsplit]
    linarith
  have hstrict : m - (δ / 2) * t < m := by
    nlinarith [hδ, ht.1]
  exact lt_of_le_of_lt hsum_le hstrict

/-- Theorem 2.39: for a nonempty family of components `f₁, …, fₘ` convex on the same feasible set
`Q ⊆ E` and differentiable at the feasible base point `xStar`, the point `xStar` minimizes the
pointwise maximum objective exactly when every first-order affine max model based at `xStar` is
bounded below by `f(xStar)` on `Q`. The textbook `ℝⁿ`/`Fin m` formulation is the specialization
`E = EuclideanSpace ℝ (Fin n)` and `ι = Fin m`. -/
-- Proof sketch: use convexity of each component to show the max objective dominates the affine max
-- model everywhere. For the forward implication, combine this domination with global minimality of
-- `xStar`. For the converse, if the affine max model drops below `f(xStar)` in some feasible
-- direction, restrict each component to the line segment from `xStar` to that point and use the
-- first-order decrease to contradict minimality.
theorem isMinOn_maxTypeObjective_iff_affineApproximation_ge
    (Q : Set E) (fs : ι → E → ℝ) (xStar : E)
    (hconv : ∀ i : ι, ConvexOn ℝ Q (fs i))
    (hxStar : xStar ∈ Q)
    (hdiff : ∀ i : ι, DifferentiableAt ℝ (fs i) xStar) :
    IsMinOn (maxTypeObjective fs) Q xStar ↔
      ∀ x ∈ Q,
        maxTypeAffineApproximation fs xStar x ≥ maxTypeObjective fs xStar := by
  classical
  have hQ_convex : Convex ℝ Q := by
    let i0 : ι := Classical.choice ‹Nonempty ι›
    exact (hconv i0).1
  rw [isMinOn_iff]
  constructor
  · intro hmin x hx
    -- Contrapositive source step: if one affine max model drops below `f(xStar)`, every component
    -- drops below `f(xStar)` along the corresponding segment for small positive times.
    by_contra hmodel
    have hmodel_lt : maxTypeAffineApproximation fs xStar x < maxTypeObjective fs xStar :=
      lt_of_not_ge hmodel
    have hlt_comp :
        ∀ i : ι, fs i xStar + inner ℝ (∇ (fs i) xStar) (x - xStar) < maxTypeObjective fs xStar := by
      intro i
      exact lt_of_le_of_lt
        (by
          rw [maxTypeAffineApproximation_apply]
          exact
            Finset.le_sup'
              (fun j : ι ↦ fs j xStar + inner ℝ (∇ (fs j) xStar) (x - xStar))
              (Finset.mem_univ i))
        hmodel_lt
    have hxStar_le :
        ∀ i : ι, fs i xStar ≤ maxTypeObjective fs xStar := by
      intro i
      rw [maxTypeObjective_apply]
      exact Finset.le_sup' (fun j : ι ↦ fs j xStar) (Finset.mem_univ i)
    have hall_lt :
        ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ i : ι, fs i (xStar + t • (x - xStar)) < maxTypeObjective fs xStar :=
      Filter.eventually_all.2 fun i ↦
        eventually_lt_max_of_affineApproximation_lt
          (hdiff i) (hxStar_le i) (hlt_comp i)
    have hIoc : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioc (0 : ℝ) 1 :=
      Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)
    obtain ⟨t, hallt, ht⟩ := (hall_lt.and hIoc).exists
    have ht_nonneg : 0 ≤ t := le_of_lt ht.1
    -- Convexity keeps the chosen segment point inside the feasible set.
    have hxt : xStar + t • (x - xStar) ∈ Q := by
      have hsum : (1 - t) + t = (1 : ℝ) := by ring
      have hcomb :
          (1 - t) • xStar + t • x ∈ Q :=
        hQ_convex hxStar hx (sub_nonneg.mpr ht.2) ht_nonneg hsum
      have hpath_eq : xStar + t • (x - xStar) = (1 - t) • xStar + t • x := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_smul, one_smul, neg_smul]
      rw [hpath_eq]
      exact hcomb
    have hmax_lt :
        maxTypeObjective fs (xStar + t • (x - xStar)) < maxTypeObjective fs xStar := by
      rw [maxTypeObjective_apply, Finset.sup'_lt_iff]
      intro i hi
      exact hallt i
    exact (not_lt_of_ge (hmin _ hxt)) hmax_lt
  · intro hmodel x hx
    -- Each component tangent model is dominated by the true component value, hence by the finite
    -- maximum objective at `x`.
    have hcomp :
        ∀ i : ι,
          firstOrderTaylorModelAt (fs i) xStar x ≤ maxTypeObjective fs x := by
      intro i
      have hfdWithin :
          HasFDerivWithinAt (fs i) (fderiv ℝ (fs i) xStar) Q xStar :=
        (hdiff i).hasFDerivAt.hasFDerivWithinAt
      have hgradWithin :
          HasGradientWithinAt (fs i) (∇ (fs i) xStar) Q xStar := by
        simpa using hfdWithin.hasGradientWithinAt
      have hlower :
          fs i x ≥ fs i xStar + inner ℝ (∇ (fs i) xStar) (x - xStar) :=
        (hconv i).lower_tangent_plane_of_hasGradientWithinAt
          xStar hxStar (∇ (fs i) xStar) hgradWithin x hx
      have hmax :
          fs i x ≤ maxTypeObjective fs x := by
        rw [maxTypeObjective_apply]
        exact Finset.le_sup' (fun j : ι ↦ fs j x) (Finset.mem_univ i)
      simpa [firstOrderTaylorModelAt_apply] using le_trans hlower hmax
    have hle :
        maxTypeAffineApproximation fs xStar x ≤ maxTypeObjective fs x := by
      simpa [maxTypeAffineApproximation] using
        (maxTypeObjective_le_iff
          (fun i ↦ firstOrderTaylorModelAt (fs i) xStar) x (maxTypeObjective fs x)).2 hcomp
    exact le_trans (hmodel x hx) hle
