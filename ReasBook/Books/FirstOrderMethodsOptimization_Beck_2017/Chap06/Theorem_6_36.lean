/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Filter.Extr
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_13
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_15

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u}

private abbrev epigraph_penalty (g : E → ℝ) : E × ℝ → EReal :=
  fun p ↦ ((g p.1 - p.2 : ℝ) : EReal)

/- Theorem 6.36 is `bridge/view`: the source-facing object is the projection mapping onto the
epigraph `epi(g)`. The canonical owners already exist upstream as Chapter 6's `prox[...]` and
`P[...]`, together with Chapter 2's `realEpigraph` and Theorem 6.30's owner residual
`level_set_projection_residual`. The only genuinely new source-facing datum in this file is
therefore the epigraph-specialized surface for that existing residual owner, obtained by viewing
`realEpigraph g` as the zero sublevel set of `(y, t) ↦ g y - t`. -/

/-- The real epigraph of `g` is the zero sublevel set of the product-space penalty
`(y, t) ↦ g y - t`. -/
theorem realEpigraph_eq_zero_sublevel (g : E → ℝ) :
    realEpigraph (fun y : E ↦ (g y : EReal)) =
      epigraph_penalty g ⁻¹' Set.Iic (0 : EReal) := by
  ext p
  simpa [realEpigraph, epigraph_penalty] using
    show g p.1 ≤ p.2 ↔ (((g p.1 - p.2 : ℝ) : EReal) ≤ 0) from by
      constructor
      · intro hp
        exact_mod_cast sub_nonpos.mpr hp
      · intro hp
        have hp' : g p.1 - p.2 ≤ 0 := by
          exact_mod_cast hp
        linarith

section

variable [NormedAddCommGroup E]

/-- The residual function controlling projection onto the epigraph of `g` at `(x, s)`. When the
scaled proximal minimizer set of `g` at `x` is a singleton, this is exactly the textbook function
`ψ(λ) = g (prox_{λ g} (x)) - λ - s`. -/
abbrev epigraph_projection_residual (g : E → ℝ) (x : E) (s : ℝ) : ℝ → EReal :=
  fun lam ↦
    sInf
      ((fun y : E ↦ ((g y - lam - s : ℝ) : EReal)) ''
        prox[fun y : E ↦ (lam : EReal) * (g y : EReal)] x)

/-- Helper for Theorem 6.36: a real-valued objective, viewed in `EReal`, is proper. -/
lemma real_toEReal_proper (g : E → ℝ) :
    IsProperExtendedRealFunction (fun y : E ↦ (g y : EReal)) := by
  refine ⟨?_, ?_⟩
  · intro y
    simp
  · refine ⟨0, ?_⟩
    simp [effective_domain]

/-- Helper for Theorem 6.36: once the scaled proximal set is a singleton `{u}`, the public
epigraph residual collapses to the textbook scalar value `g u - λ - s`. -/
lemma epigraph_projection_residual_eq_of_scaled_prox_eq_singleton
    (g : E → ℝ) (x : E) (s lam : ℝ) (u : E)
    (hprox : prox[fun y : E ↦ (lam : EReal) * (g y : EReal)] x = {u}) :
    epigraph_projection_residual g x s lam = ((g u - lam - s : ℝ) : EReal) := by
  -- The public residual is defined as the infimum over the scaled proximal image, so a singleton
  -- proximal set gives the textbook value immediately.
  rw [epigraph_projection_residual, hprox, Set.image_singleton, sInf_singleton]

-- Proof sketch: unfold `realEpigraph`; if `g x ≤ s`, then `(x, s)` is feasible, and its
-- distance to itself is zero. Every projected point has distance at least zero, so `(x, s)` is
-- the unique projection point.
/-- A point already lying in the real epigraph of `g` projects to itself. -/
theorem projection_mapping_realEpigraph_eq_singleton_of_mem
    (g : E → ℝ) (x : E) (s : ℝ) (hgxs : g x ≤ s) :
    P[realEpigraph (fun y : E ↦ (g y : EReal))] (x, s) = {(x, s)} := by
  have hx_mem : (x, s) ∈ realEpigraph (fun y : E ↦ (g y : EReal)) := by
    -- Feasibility is exactly the defining epigraph inequality at `(x, s)`.
    simpa [realEpigraph] using hgxs
  have hx_proj : (x, s) ∈ P[realEpigraph (fun y : E ↦ (g y : EReal))] (x, s) := by
    -- A feasible point has zero distance to itself, so it is a projection point.
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hx_mem, ?_⟩
    intro z hz
    simp only [sub_self, norm_zero]
    exact norm_nonneg (z - (x, s))
  ext y
  constructor
  · intro hy
    have hy_min : IsMinOn (fun z ↦ ‖z - (x, s)‖) (realEpigraph (fun y : E ↦ (g y : EReal))) y :=
      (mem_projection_mapping_iff.mp hy).2
    have hy_le : ‖y - (x, s)‖ ≤ ‖(x, s) - (x, s)‖ := by
      exact (isMinOn_iff.mp hy_min) (x, s) hx_mem
    have hy_norm : ‖y - (x, s)‖ = 0 := by
      have hy_nonneg : ‖(x, s) - (x, s)‖ ≤ ‖y - (x, s)‖ := by
        simp only [sub_self, norm_zero]
        exact norm_nonneg (y - (x, s))
      simp only [sub_self, norm_zero] at hy_nonneg hy_le
      exact le_antisymm hy_le hy_nonneg
    have hy_eq : y = (x, s) := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hy_norm)
    simp [hy_eq]
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hx_proj

section

variable {ι : Type u} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "EP" => EuclideanSpace ℝ (Option ι)

/-- The Euclidean product point `(x, s)` in `EuclideanSpace ℝ (Option ι)`, with horizontal
coordinates `x` and vertical coordinate `s`. -/
abbrev euclideanProductPoint (x : E) (s : ℝ) : EP :=
  WithLp.toLp (p := (2 : ENNReal)) fun o ↦
    match o with
    | none => s
    | some i => x.ofLp i

private abbrev euclideanProductBase (p : EP) : E :=
  WithLp.toLp (p := (2 : ENNReal)) fun i ↦ p.ofLp (some i)

private abbrev euclideanProductHeight (p : EP) : ℝ :=
  p.ofLp none

/-- Helper for Theorem 6.36: the Euclidean epigraph penalty on `EP` is the finite-valued function
`p ↦ g (base p) - height p`. -/
private abbrev euclidean_epigraph_penalty (g : E → ℝ) : EP → EReal :=
  fun p ↦ ((g (euclideanProductBase p) - euclideanProductHeight p : ℝ) : EReal)

/-- Helper for Theorem 6.36: the repaired Euclidean residual uses the Euclidean ambient point
`euclideanProductPoint x s`, not the legacy max-norm product owner. -/
private abbrev euclidean_epigraph_projection_residual
    (g : E → ℝ) (x : E) (s : ℝ) : ℝ → EReal :=
  level_set_projection_residual (euclidean_epigraph_penalty g) 0 (euclideanProductPoint x s)

/-- Helper for Theorem 6.36: the base coordinate of `euclideanProductPoint x s` is `x`. -/
@[simp] lemma euclideanProductBase_point (x : E) (s : ℝ) :
    euclideanProductBase (euclideanProductPoint x s) = x := by
  -- Read the Euclidean product point coordinatewise.
  ext i
  simp

/-- Helper for Theorem 6.36: the height coordinate of `euclideanProductPoint x s` is `s`. -/
@[simp] lemma euclideanProductHeight_point (x : E) (s : ℝ) :
    euclideanProductHeight (euclideanProductPoint x s) = s := by
  -- The `none` coordinate stores the scalar height.
  simp

/-- Helper for Theorem 6.36: the Euclidean product base map is additive. -/
@[simp] lemma euclideanProductBase_add (p q : EP) :
    euclideanProductBase (p + q) = euclideanProductBase p + euclideanProductBase q := by
  -- Addition is coordinatewise in the Euclidean model.
  ext i
  simp [euclideanProductBase]

/-- Helper for Theorem 6.36: the Euclidean product base map is homogeneous. -/
@[simp] lemma euclideanProductBase_smul (a : ℝ) (p : EP) :
    euclideanProductBase (a • p) = a • euclideanProductBase p := by
  -- Scalar multiplication is coordinatewise in the Euclidean model.
  ext i
  simp [euclideanProductBase]

/-- Helper for Theorem 6.36: the Euclidean height map is additive. -/
@[simp] lemma euclideanProductHeight_add (p q : EP) :
    euclideanProductHeight (p + q) = euclideanProductHeight p + euclideanProductHeight q := by
  -- The `none` coordinate behaves linearly under addition.
  simp [euclideanProductHeight]

/-- Helper for Theorem 6.36: the Euclidean height map is homogeneous. -/
@[simp] lemma euclideanProductHeight_smul (a : ℝ) (p : EP) :
    euclideanProductHeight (a • p) = a * euclideanProductHeight p := by
  -- The `none` coordinate behaves linearly under scalar multiplication.
  simp [euclideanProductHeight, smul_eq_mul]

/-- The real epigraph of a coordinate Euclidean function, represented inside the Euclidean product
space `EuclideanSpace ℝ (Option ι)` rather than the default max-norm product `E × ℝ`. -/
def euclideanRealEpigraph (g : E → ℝ) : Set EP :=
  {p | g (euclideanProductBase p) ≤ euclideanProductHeight p}

/-- A Euclidean product point `(x, s)` belongs to `euclideanRealEpigraph g` exactly when
`g x ≤ s`. -/
@[simp] theorem mem_euclideanRealEpigraph_point_iff (g : E → ℝ) (x : E) (s : ℝ) :
    euclideanProductPoint x s ∈ euclideanRealEpigraph g ↔ g x ≤ s := by
  simp [euclideanRealEpigraph]

/-- Helper for Theorem 6.36: the Euclidean epigraph is the zero sublevel set of the repaired
Euclidean penalty. -/
theorem euclideanRealEpigraph_eq_zero_sublevel (g : E → ℝ) :
    euclideanRealEpigraph g =
      euclidean_epigraph_penalty g ⁻¹' Set.Iic (0 : EReal) := by
  -- This is the Euclidean analogue of the earlier product-space zero-sublevel identity.
  ext p
  simpa [euclideanRealEpigraph, euclidean_epigraph_penalty] using
    show g (euclideanProductBase p) ≤ euclideanProductHeight p ↔
        (((g (euclideanProductBase p) - euclideanProductHeight p : ℝ) : EReal) ≤ 0) from by
      constructor
      · intro hp
        exact_mod_cast sub_nonpos.mpr hp
      · intro hp
        have hp' : g (euclideanProductBase p) - euclideanProductHeight p ≤ 0 := by
          exact_mod_cast hp
        linarith

/-- Helper for Theorem 6.36: a feasible Euclidean product point projects to itself. -/
theorem projection_mapping_euclideanRealEpigraph_eq_singleton_of_mem
    (g : E → ℝ) (x : E) (s : ℝ) (hgxs : g x ≤ s) :
    P[euclideanRealEpigraph g] (euclideanProductPoint x s) = {euclideanProductPoint x s} := by
  have hx_mem : euclideanProductPoint x s ∈ euclideanRealEpigraph g := by
    -- Feasibility is exactly the defining Euclidean epigraph inequality.
    simpa [euclideanRealEpigraph] using hgxs
  have hx_proj : euclideanProductPoint x s ∈ P[euclideanRealEpigraph g] (euclideanProductPoint x s) := by
    -- A feasible point has zero Euclidean distance to itself.
    rw [mem_projection_mapping_iff, isMinOn_iff]
    refine ⟨hx_mem, ?_⟩
    intro z hz
    simp only [sub_self, norm_zero]
    exact norm_nonneg (z - euclideanProductPoint x s)
  ext y
  constructor
  · intro hy
    have hy_min :
        IsMinOn (fun z ↦ ‖z - euclideanProductPoint x s‖) (euclideanRealEpigraph g) y :=
      (mem_projection_mapping_iff.mp hy).2
    have hy_le : ‖y - euclideanProductPoint x s‖ ≤
        ‖euclideanProductPoint x s - euclideanProductPoint x s‖ := by
      exact (isMinOn_iff.mp hy_min) _ hx_mem
    have hy_norm : ‖y - euclideanProductPoint x s‖ = 0 := by
      have hy_nonneg :
          ‖euclideanProductPoint x s - euclideanProductPoint x s‖ ≤
            ‖y - euclideanProductPoint x s‖ := by
        simp only [sub_self, norm_zero]
        exact norm_nonneg (y - euclideanProductPoint x s)
      simp only [sub_self, norm_zero] at hy_nonneg hy_le
      exact le_antisymm hy_le hy_nonneg
    have hy_eq : y = euclideanProductPoint x s := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hy_norm)
    simp [hy_eq]
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hx_proj

/-- Helper for Theorem 6.36: the Euclidean epigraph penalty is proper, lower semicontinuous, and
convex when `g` is convex. -/
lemma euclidean_epigraph_penalty_proper_closed_convex
    (g : E → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) :
    IsProperExtendedRealFunction (euclidean_epigraph_penalty g) ∧
      LowerSemicontinuous (euclidean_epigraph_penalty g) ∧
      is_convex_function (euclidean_epigraph_penalty g) := by
  have hproper : IsProperExtendedRealFunction (euclidean_epigraph_penalty g) := by
    -- The penalty is finite everywhere because it is the `EReal` lift of a real-valued function.
    refine ⟨?_, ?_⟩
    · intro p
      exact EReal.coe_ne_bot _
    · refine ⟨euclideanProductPoint 0 0, ?_⟩
      simp [effective_domain, euclidean_epigraph_penalty]
  have hcont_g : Continuous g := by
    -- A convex real-valued function on finite-dimensional Euclidean space is continuous.
    simpa [continuousOn_univ] using hg_convex.continuousOn
  have hcont_base : Continuous (fun p : EP ↦ euclideanProductBase p) := by
    -- The base projection is coordinatewise continuous.
    change Continuous
      (fun p : EP ↦ WithLp.toLp (p := (2 : ENNReal)) fun i ↦ p.ofLp (some i))
    fun_prop
  have hcont_height : Continuous (fun p : EP ↦ euclideanProductHeight p) := by
    -- The height projection is the `none` coordinate map.
    change Continuous (fun p : EP ↦ p.ofLp none)
    fun_prop
  have hclosed : LowerSemicontinuous (euclidean_epigraph_penalty g) := by
    -- Continuity of the real-valued penalty upgrades directly to lower semicontinuity.
    have hcont_penalty :
        Continuous (fun p : EP ↦ g (euclideanProductBase p) - euclideanProductHeight p) :=
      (hcont_g.comp hcont_base).sub hcont_height
    simpa [euclidean_epigraph_penalty] using
      (continuous_coe_real_ereal.comp hcont_penalty).lowerSemicontinuous
  have hdom :
      effective_domain (euclidean_epigraph_penalty g) = Set.univ := by
    -- The Euclidean penalty never takes the value `⊤`.
    ext p
    constructor
    · intro hp
      simp
    · intro hp
      simpa [effective_domain, euclidean_epigraph_penalty, EReal.coe_sub] using
        (EReal.coe_lt_top (g (euclideanProductBase p) - euclideanProductHeight p))
  have hconv_real :
      ConvexOn ℝ Set.univ
        (fun p : EP ↦ g (euclideanProductBase p) - euclideanProductHeight p) := by
    refine ⟨convex_univ, ?_⟩
    intro p hp q hq a b ha hb hab
    -- Convexity comes from convexity of `g` on the base coordinate and linearity of height.
    have hg :
        g (a • euclideanProductBase p + b • euclideanProductBase q) ≤
          a * g (euclideanProductBase p) + b * g (euclideanProductBase q) := by
      simpa [smul_eq_mul] using
        hg_convex.2
          (x := euclideanProductBase p) (by simp)
          (y := euclideanProductBase q) (by simp)
          ha hb hab
    calc
      g (euclideanProductBase (a • p + b • q)) - euclideanProductHeight (a • p + b • q)
          = g (a • euclideanProductBase p + b • euclideanProductBase q) -
              (a * euclideanProductHeight p + b * euclideanProductHeight q) := by
                simp [smul_eq_mul]
      _ ≤ (a * g (euclideanProductBase p) + b * g (euclideanProductBase q)) -
            (a * euclideanProductHeight p + b * euclideanProductHeight q) := by
              exact sub_le_sub hg le_rfl
      _ = a * (g (euclideanProductBase p) - euclideanProductHeight p) +
            b * (g (euclideanProductBase q) - euclideanProductHeight q) := by
              ring
  have hconv : is_convex_function (euclidean_epigraph_penalty g) := by
    have hne_bot :
        ∀ p ∈ effective_domain (euclidean_epigraph_penalty g),
          euclidean_epigraph_penalty g p ≠ ⊥ := by
      intro p hp
      simpa [euclidean_epigraph_penalty, EReal.coe_sub] using
        (EReal.coe_ne_bot (g (euclideanProductBase p) - euclideanProductHeight p))
    refine (is_convex_function_iff_convexOn_toReal hne_bot).2 ?_
    simpa [hdom, euclidean_epigraph_penalty] using hconv_real
  exact ⟨hproper, hclosed, hconv⟩

/-- Helper for Theorem 6.36: the repaired Euclidean residual is nonincreasing on nonnegative
reals. -/
lemma euclidean_epigraph_projection_residual_antitoneOn_nonneg
    (g : E → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (x : E) (s : ℝ) :
    AntitoneOn (euclidean_epigraph_projection_residual g x s) (Set.Ici 0) := by
  rcases euclidean_epigraph_penalty_proper_closed_convex g hg_convex with
    ⟨hproper, hclosed, hconvex⟩
  -- The Euclidean residual is exactly Chapter 6's level-set residual for the repaired penalty.
  simpa [euclidean_epigraph_projection_residual] using
    level_set_projection_residual_antitoneOn_nonneg
      (f := euclidean_epigraph_penalty g) (α := 0) hproper hclosed hconvex
      (euclideanProductPoint x s)

/-- Helper for Theorem 6.36: the Euclidean base projection is a continuous linear map. -/
private noncomputable abbrev euclideanProductBaseLinear : EP →L[ℝ] E :=
  { toLinearMap :=
      { toFun := euclideanProductBase
        map_add' := euclideanProductBase_add
        map_smul' := euclideanProductBase_smul }
    cont := by
      -- The coordinate projection is continuous in the Euclidean model.
      change Continuous
        (fun p : EP ↦ WithLp.toLp (p := (2 : ENNReal)) fun i ↦ p.ofLp (some i))
      fun_prop }

/-- Helper for Theorem 6.36: the Euclidean base projection viewed as a continuous affine map. -/
private noncomputable abbrev euclideanProductBaseAffine : EP →ᴬ[ℝ] E :=
  euclideanProductBaseLinear.toContinuousAffineMap

/-- Helper for Theorem 6.36: the adjoint of the Euclidean base projection. -/
private noncomputable abbrev euclideanProductBaseAdjoint : E →L[ℝ] EP :=
  ContinuousLinearMap.adjoint euclideanProductBaseLinear

/-- Helper for Theorem 6.36: the bundled base projection evaluates to the coordinate projection. -/
@[simp] lemma euclideanProductBaseLinear_apply (p : EP) :
    euclideanProductBaseLinear p = euclideanProductBase p := rfl

/-- Helper for Theorem 6.36: the base projection annihilates the vertical basis vector. -/
@[simp] lemma euclideanProductBase_basisFun_none :
    euclideanProductBase (EuclideanSpace.basisFun (Option ι) ℝ none) = 0 := by
  -- The `none` basis vector has no horizontal coordinates.
  classical
  ext i
  change (EuclideanSpace.basisFun (Option ι) ℝ none) (some i) = 0
  simp [EuclideanSpace.basisFun_apply]

/-- Helper for Theorem 6.36: the base projection sends a horizontal basis vector to the matching
horizontal basis vector. -/
@[simp] lemma euclideanProductBase_basisFun_some (i : ι) :
    euclideanProductBase (EuclideanSpace.basisFun (Option ι) ℝ (some i)) =
      EuclideanSpace.basisFun ι ℝ i := by
  -- The `some i` basis vector records exactly the `i`-th horizontal coordinate.
  classical
  ext j
  change (EuclideanSpace.basisFun (Option ι) ℝ (some i)) (some j) =
    (EuclideanSpace.basisFun ι ℝ i) j
  simp [EuclideanSpace.basisFun_apply]

/-- Helper for Theorem 6.36: the adjoint of the Euclidean base projection inserts a horizontal
vector with zero height. -/
@[simp] lemma euclideanProductBaseLinear_adjoint_apply (y : E) :
    euclideanProductBaseAdjoint y = euclideanProductPoint y 0 := by
  -- Read the adjoint on the Euclidean basis of the product space.
  classical
  ext o
  cases o with
  | none =>
      calc
        (euclideanProductBaseAdjoint y) none
            = inner ℝ (euclideanProductBaseAdjoint y)
                (EuclideanSpace.basisFun (Option ι) ℝ none) := by
                  symm
                  simpa using EuclideanSpace.inner_basisFun_real
                    (x := euclideanProductBaseAdjoint y) (i := none)
        _ = inner ℝ y
              (euclideanProductBaseLinear (EuclideanSpace.basisFun (Option ι) ℝ none)) := by
                simpa [euclideanProductBaseAdjoint] using
                  (ContinuousLinearMap.adjoint_inner_left euclideanProductBaseLinear
                    (EuclideanSpace.basisFun (Option ι) ℝ none) y)
        _ = inner ℝ y (0 : E) := by
              have hnone :
                  euclideanProductBaseLinear (EuclideanSpace.basisFun (Option ι) ℝ none) =
                    (0 : E) := by
                ext i
                simp [euclideanProductBaseLinear_apply, euclideanProductBase,
                  EuclideanSpace.basisFun_apply]
              rw [hnone]
        _ = 0 := by simp
        _ = euclideanProductPoint y 0 none := by simp [euclideanProductPoint]
  | some i =>
      calc
        (euclideanProductBaseAdjoint y) (some i)
            = inner ℝ (euclideanProductBaseAdjoint y)
                (EuclideanSpace.basisFun (Option ι) ℝ (some i)) := by
                  symm
                  simpa using EuclideanSpace.inner_basisFun_real
                    (x := euclideanProductBaseAdjoint y) (i := some i)
        _ = inner ℝ y
              (euclideanProductBaseLinear (EuclideanSpace.basisFun (Option ι) ℝ (some i))) := by
                simpa [euclideanProductBaseAdjoint] using
                  (ContinuousLinearMap.adjoint_inner_left euclideanProductBaseLinear
                    (EuclideanSpace.basisFun (Option ι) ℝ (some i)) y)
        _ = inner ℝ y (EuclideanSpace.basisFun ι ℝ i) := by
              have hsome :
                  euclideanProductBaseLinear (EuclideanSpace.basisFun (Option ι) ℝ (some i)) =
                    EuclideanSpace.basisFun ι ℝ i := by
                ext j
                simp [euclideanProductBaseLinear_apply, euclideanProductBase,
                  EuclideanSpace.basisFun_apply]
              rw [hsome]
        _ = y i := by
              simpa using EuclideanSpace.inner_basisFun_real (x := y) (i := i)
        _ = euclideanProductPoint y 0 (some i) := by simp [euclideanProductPoint]

/-- Helper for Theorem 6.36: the Euclidean base affine map satisfies the isotropy hypothesis from
Theorem 6.15 with parameter `α = 1`. -/
@[simp] lemma euclideanProductBaseAffine_isotropic :
    euclideanProductBaseAffine.contLinear ∘L euclideanProductBaseAdjoint =
      (1 : ℝ) • (1 : E →L[ℝ] E) := by
  -- The base map followed by its adjoint is the identity on horizontal coordinates.
  ext y i
  simp [euclideanProductBaseAffine, euclideanProductBaseLinear_adjoint_apply]

/-- Helper for Theorem 6.36: shifting by the negative vertical perturbation raises the height by
`λ`. -/
lemma euclideanProductPoint_sub_neg_smul_vertical_basis
    (x : E) (s : ℝ) (lam : PosReal) :
    euclideanProductPoint x s -
        (-(lam : ℝ) • EuclideanSpace.basisFun (Option ι) ℝ none) =
      euclideanProductPoint x (s + (lam : ℝ)) := by
  -- Only the vertical coordinate changes under this perturbation.
  classical
  ext o
  cases o with
  | none =>
      simp [euclideanProductPoint, EuclideanSpace.basisFun_apply]
  | some i =>
      simp [euclideanProductPoint, EuclideanSpace.basisFun_apply]

/-- Helper for Theorem 6.36: the affine correction from Theorem 6.15 is exactly the map
`z ↦ (z, t)` in Euclidean product coordinates. -/
lemma euclideanProductBase_affine_transport (x z : E) (t : ℝ) :
    euclideanProductPoint x t +
        euclideanProductBaseAdjoint (z - x) =
      euclideanProductPoint z t := by
  -- The adjoint inserts the horizontal displacement while leaving the height unchanged.
  rw [euclideanProductBaseLinear_adjoint_apply]
  ext o
  cases o with
  | none =>
      simp [euclideanProductPoint]
  | some i =>
      simp [euclideanProductPoint]

/-- Helper for Theorem 6.36: positively scaling a real-valued objective preserves properness. -/
lemma scaled_real_function_proper (g : E → ℝ) (lam : PosReal) :
    IsProperExtendedRealFunction (fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)) := by
  -- A positive finite scalar cannot create `⊥` or remove finite values.
  have hlam_nonneg : (0 : EReal) ≤ (lam : ℝ) := by
    exact_mod_cast le_of_lt (show 0 < (lam : ℝ) from lam.2)
  refine ⟨?_, ?_⟩
  · intro y
    exact
      (EReal.mul_ne_bot _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (EReal.coe_ne_bot _),
          Or.inl (EReal.coe_ne_top _), Or.inl hlam_nonneg⟩
  · refine ⟨0, ?_⟩
    exact lt_top_iff_ne_top.mpr <|
      (EReal.mul_ne_top _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hlam_nonneg,
          Or.inl (EReal.coe_ne_top _), Or.inr (EReal.coe_ne_top _)⟩

/-- Helper for Theorem 6.36: the scaled Euclidean epigraph penalty splits into the horizontal
scaled objective and the vertical linear perturbation used in Theorem 6.13. -/
lemma euclidean_epigraph_penalty_scaled_split
    (g : E → ℝ) (lam : PosReal) :
    ((lam : EReal) • euclidean_epigraph_penalty g) =
      (fun p : EP ↦ ((lam : ℝ) : EReal) * (g (euclideanProductBase p) : EReal)) +
        fun p : EP ↦
          ((-inner ℝ ((lam : ℝ) • EuclideanSpace.basisFun (Option ι) ℝ none) p : ℝ) : EReal) := by
  -- Expanding the vertical basis inner product produces the `- λ t` term.
  funext p
  let vertical : EP := EuclideanSpace.basisFun (Option ι) ℝ none
  have hbase : inner ℝ vertical p = euclideanProductHeight p := by
    change inner ℝ (EuclideanSpace.basisFun (Option ι) ℝ none) p = p none
    exact EuclideanSpace.basisFun_inner (x := p) (i := none)
  have hinner :
      inner ℝ ((lam : ℝ) • vertical) p = (lam : ℝ) * euclideanProductHeight p := by
    calc
      inner ℝ ((lam : ℝ) • vertical) p = (starRingEnd ℝ (lam : ℝ)) * inner ℝ vertical p := by
        rw [inner_smul_left]
      _ = (lam : ℝ) * inner ℝ vertical p := by simp
      _ = (lam : ℝ) * euclideanProductHeight p := by rw [hbase]
  have hvertical :
      -inner ℝ ((lam : ℝ) • vertical) p =
        -(lam : ℝ) * euclideanProductHeight p := by
    simpa [neg_mul] using congrArg Neg.neg hinner
  calc
    ((lam : EReal) • euclidean_epigraph_penalty g) p
        = ((((lam : ℝ) *
              (g (euclideanProductBase p) - euclideanProductHeight p) : ℝ)) : EReal) := by
            simp [euclidean_epigraph_penalty, Pi.smul_apply, smul_eq_mul, EReal.coe_mul]
    _ = ((((lam : ℝ) * g (euclideanProductBase p) -
            inner ℝ ((lam : ℝ) • vertical) p : ℝ)) : EReal) := by
          rw [hinner]
          ring
    _ = ((fun p : EP ↦ ((lam : ℝ) : EReal) * (g (euclideanProductBase p) : EReal)) +
          fun p : EP ↦
            ((-inner ℝ ((lam : ℝ) • vertical) p : ℝ) : EReal))
          p := by
            simp [sub_eq_add_neg, EReal.coe_mul]

/-- Helper for Theorem 6.36: the active branch reduces to a proximal-transport identity for the
repaired Euclidean penalty. -/
lemma prox_scaled_euclidean_epigraph_penalty_eq_lifted_scaled_prox
    (g : E → ℝ) (x : E) (s : ℝ) (lam : PosReal) :
    prox[((lam : EReal) • euclidean_epigraph_penalty g)] (euclideanProductPoint x s) =
      (fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) ''
        prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x := by
  let vertical : EP := EuclideanSpace.basisFun (Option ι) ℝ none
  let gscaled : E → EReal := fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)
  have hshift :
      euclideanProductPoint x s + (lam : ℝ) • vertical =
        euclideanProductPoint x (s + (lam : ℝ)) := by
    -- The positive vertical shift is the same base-point correction written additively.
    simpa [sub_eq_add_neg, vertical] using
      euclideanProductPoint_sub_neg_smul_vertical_basis x s lam
  have hperturb :
      prox[(fun p : EP ↦ ((lam : ℝ) : EReal) * (g (euclideanProductBase p) : EReal)) +
          fun p : EP ↦ (((0 / 2 : ℝ) * ‖p‖ ^ (2 : ℕ) + -inner ℝ ((lam : ℝ) • vertical) p : ℝ) : EReal)]
          (euclideanProductPoint x s) =
        prox[gscaled ∘ euclideanProductBaseAffine]
          (euclideanProductPoint x (s + (lam : ℝ))) := by
    have hquad :
        prox[gscaled ∘ euclideanProductBaseAffine +
            fun p : EP ↦ ((((0 / 2 : ℝ) * ‖p‖ ^ (2 : ℕ) +
              -inner ℝ ((lam : ℝ) • vertical) p : ℝ)) : EReal)]
            (euclideanProductPoint x s) =
          prox[gscaled ∘ euclideanProductBaseAffine]
            (euclideanProductPoint x s + (lam : ℝ) • vertical) := by
      -- Theorem 6.13 removes the linear perturbation before we rewrite the shifted base point.
      simpa [gscaled, vertical, euclideanProductBaseAffine, zero_mul, zero_add] using
        proximal_mapping_quadratic_perturbation
          (g := gscaled ∘ euclideanProductBaseAffine) (c := 0) (hc := by norm_num)
          (a := -(lam : ℝ) • vertical) (x := euclideanProductPoint x s)
    rw [hshift] at hquad
    exact hquad
  have htransport :
      prox[gscaled ∘ euclideanProductBaseAffine]
          (euclideanProductPoint x (s + (lam : ℝ))) =
        (fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) '' prox[gscaled] x := by
    have hmap :
        (fun z : E ↦
          euclideanProductPoint x (s + (lam : ℝ)) +
            (((1 : ℝ)⁻¹ • euclideanProductBaseAdjoint))
              (z - euclideanProductBaseAffine (euclideanProductPoint x (s + (lam : ℝ))))) =
          (fun z : E ↦ euclideanProductPoint z (s + (lam : ℝ))) := by
      -- Theorem 6.15's affine correction is exactly horizontal insertion at fixed height.
      funext z
      simpa [euclideanProductBaseAffine, euclideanProductBase_point, euclideanProductBaseAdjoint] using
        euclideanProductBase_affine_transport x z (s + (lam : ℝ))
    calc
      prox[gscaled ∘ euclideanProductBaseAffine]
          (euclideanProductPoint x (s + (lam : ℝ)))
          =
            (fun z : E ↦
              euclideanProductPoint x (s + (lam : ℝ)) +
                (((1 : ℝ)⁻¹ • euclideanProductBaseAdjoint))
                  (z - euclideanProductBaseAffine (euclideanProductPoint x (s + (lam : ℝ))))) ''
              prox[(1 : EReal) • gscaled]
                (euclideanProductBaseAffine (euclideanProductPoint x (s + (lam : ℝ)))) := by
              -- Theorem 6.15 transports the pullback proximal problem through the base map.
              simpa [gscaled, euclideanProductBaseAffine] using
                proximal_mapping_precompose_continuousAffineMap
                  (g := gscaled) (hg_proper := scaled_real_function_proper g lam)
                  (φ := euclideanProductBaseAffine) (α := 1) (hα := zero_lt_one)
                  (hφ := euclideanProductBaseAffine_isotropic)
                  (x := euclideanProductPoint x (s + (lam : ℝ)))
      _ = (fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) '' prox[gscaled] x := by
            rw [hmap]
            simp [euclideanProductBaseAffine]
  -- Route correction: chain Theorem 6.13 and Theorem 6.15 through the explicit Euclidean
  -- transport lemmas proved above.
  calc
    prox[((lam : EReal) • euclidean_epigraph_penalty g)] (euclideanProductPoint x s)
        = prox[gscaled ∘ euclideanProductBaseAffine]
            (euclideanProductPoint x (s + (lam : ℝ))) := by
              rw [euclidean_epigraph_penalty_scaled_split]
              simpa [zero_mul, zero_add] using hperturb
    _ = (fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) '' prox[gscaled] x := htransport
    _ = (fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) ''
          prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x := by
            rfl

/-- Helper for Theorem 6.36: on positive parameters, the private Euclidean residual coincides
with the public scalar residual. -/
lemma euclidean_epigraph_projection_residual_eq_public_residual_of_pos
    (g : E → ℝ) (x : E) (s : ℝ) (lam : PosReal) :
    euclidean_epigraph_projection_residual g x s (lam : ℝ) =
      epigraph_projection_residual g x s (lam : ℝ) := by
  have himage :
      euclidean_epigraph_penalty g ''
          ((fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) ''
            prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x) =
        (fun y : E ↦ ((g y - (lam : ℝ) - s : ℝ) : EReal)) ''
          prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x := by
    -- Evaluating the Euclidean penalty on a lifted proximal point produces the textbook scalar
    -- residual integrand `g y - λ - s`.
    ext z
    constructor
    · rintro ⟨p, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      have hreal : g y - (s + (lam : ℝ)) = g y - (lam : ℝ) - s := by ring
      simpa [euclidean_epigraph_penalty, hreal]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨euclideanProductPoint y (s + (lam : ℝ)), ?_, ?_⟩
      · exact ⟨y, hy, rfl⟩
      · have hreal : g y - (s + (lam : ℝ)) = g y - (lam : ℝ) - s := by ring
        simpa [euclidean_epigraph_penalty, hreal]
  -- The positive-parameter transport lemma converts the Euclidean residual owner to the public
  -- scalar owner.
  calc
    euclidean_epigraph_projection_residual g x s (lam : ℝ)
        = sInf
            (euclidean_epigraph_penalty g ''
              prox[((lam : EReal) • euclidean_epigraph_penalty g)]
                (euclideanProductPoint x s)) := by
                  simp [euclidean_epigraph_projection_residual, level_set_projection_residual]
    _ = sInf
          (euclidean_epigraph_penalty g ''
            ((fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) ''
              prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x)) := by
                rw [prox_scaled_euclidean_epigraph_penalty_eq_lifted_scaled_prox]
    _ = sInf
          ((fun y : E ↦ ((g y - (lam : ℝ) - s : ℝ) : EReal)) ''
            prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x) := by
              rw [himage]
    _ = epigraph_projection_residual g x s (lam : ℝ) := by
          rfl

-- Proof sketch: rewrite the epigraph as a zero sublevel set in the Euclidean product model. If
-- `s < g x` and `λ > 0` is a root of the residual equation, compare the constrained quadratic
-- minimizers with the scaled proximal minimizers of `g`, then identify the projected point set
-- with the vertical lift of those minimizers by `s + λ`.
/-- The active-constraint branch of Theorem 6.36 in the Euclidean product model. If `(x, s)` lies
strictly below the epigraph of `g` and `λ > 0` is a root of the epigraph residual equation, then
the projection onto the epigraph is obtained by lifting the proximal set of `λ g` by the vertical
shift `s + λ`. -/
theorem projection_mapping_realEpigraph_eq_lifted_scaled_prox_of_root
    (g : E → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (x : E) (s : ℝ) (hgxs : s < g x)
    (lam : PosReal) (hψ : epigraph_projection_residual g x s (lam : ℝ) = 0) :
    P[euclideanRealEpigraph g] (euclideanProductPoint x s) =
      (fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) ''
        prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x := by
  rcases euclidean_epigraph_penalty_proper_closed_convex g hg_convex with
    ⟨hproper, hclosed, hconvex⟩
  have hψ' : euclidean_epigraph_projection_residual g x s (lam : ℝ) = 0 := by
    -- The root condition is stated for the public scalar residual, so first move it to the
    -- private Euclidean residual used by Theorem 6.30.
    simpa [euclidean_epigraph_projection_residual_eq_public_residual_of_pos g x s lam] using hψ
  -- Route correction: specialize Theorem 6.30 to the repaired Euclidean penalty, then convert the
  -- resulting scaled prox set using the Euclidean transport bridge.
  calc
    P[euclideanRealEpigraph g] (euclideanProductPoint x s)
        = P[(euclidean_epigraph_penalty g) ⁻¹' Set.Iic (0 : EReal)] (euclideanProductPoint x s) := by
            rw [euclideanRealEpigraph_eq_zero_sublevel]
    _ = prox[((lam : EReal) • euclidean_epigraph_penalty g)] (euclideanProductPoint x s) := by
          exact
            projection_mapping_sublevel_eq_scaled_prox_of_level_set_projection_residual_eq_zero
              (f := euclidean_epigraph_penalty g) (α := 0) hproper hclosed hconvex
              (x := euclideanProductPoint x s) lam hψ'
    _ = (fun y : E ↦ euclideanProductPoint y (s + (lam : ℝ))) ''
          prox[fun y : E ↦ ((lam : ℝ) : EReal) * (g y : EReal)] x :=
          prox_scaled_euclidean_epigraph_penalty_eq_lifted_scaled_prox g x s lam

-- Proof sketch: if `g x ≤ s`, the Euclidean product point already lies in the epigraph and hence
-- projects to itself. Otherwise `s < g x`, so the hypothesis supplies the active multiplier data
-- and `projection_mapping_realEpigraph_eq_lifted_scaled_prox_of_root` gives the second branch.
/-- Theorem 6.36 in the Euclidean product model: the projection onto the real epigraph of a convex
function is the singleton `{(x, s)}` at feasible points, while on the infeasible branch it is
obtained from the proximal set of `λ g` using any positive root `λ` of the epigraph residual
equation. -/
theorem projection_mapping_realEpigraph_eq_piecewise_lifted_scaled_prox
    (g : E → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (x : E) (s : ℝ) (lam : ℝ)
    (hactive : s < g x → 0 < lam ∧ epigraph_projection_residual g x s lam = 0) :
    P[euclideanRealEpigraph g] (euclideanProductPoint x s) =
      if hgxs : g x ≤ s then
        {euclideanProductPoint x s}
      else
        (fun y : E ↦ euclideanProductPoint y (s + lam)) ''
          prox[fun y : E ↦ (lam : EReal) * (g y : EReal)] x := by
  by_cases hgxs : g x ≤ s
  · -- On the feasible branch the Euclidean product point already belongs to the epigraph.
    simp [hgxs, projection_mapping_euclideanRealEpigraph_eq_singleton_of_mem, euclideanProductPoint]
  · have hsx : s < g x := lt_of_not_ge hgxs
    rcases hactive hsx with ⟨hlam, hψ⟩
    let lamPos : PosReal := ⟨lam, hlam⟩
    have hbranch :
        P[euclideanRealEpigraph g] (euclideanProductPoint x s) =
          (fun y : E ↦ euclideanProductPoint y (s + (lamPos : ℝ))) ''
            prox[fun y : E ↦ ((lamPos : ℝ) : EReal) * (g y : EReal)] x :=
      projection_mapping_realEpigraph_eq_lifted_scaled_prox_of_root g hg_convex x s hsx lamPos hψ
    -- The infeasible branch is exactly the active-constraint formula with `lamPos = lam`.
    simpa [hgxs, lamPos] using hbranch

end

section

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Theorem 6.36: a convex real-valued function becomes a proper closed convex
extended-real objective after coercion to `EReal`. -/
lemma real_toEReal_proper_closed_convex
    (g : E → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) :
    IsProperExtendedRealFunction (fun y : E ↦ (g y : EReal)) ∧
      LowerSemicontinuous (fun y : E ↦ (g y : EReal)) ∧
      is_convex_function (fun y : E ↦ (g y : EReal)) := by
  have hproper : IsProperExtendedRealFunction (fun y : E ↦ (g y : EReal)) :=
    real_toEReal_proper g
  have hcont : Continuous g := by
    -- Finite-dimensional convex functions are continuous on all of `E`.
    simpa [continuousOn_univ] using hg_convex.continuousOn
  have hclosed : LowerSemicontinuous (fun y : E ↦ (g y : EReal)) := by
    -- Lower semicontinuity comes from continuity of the real-valued lift.
    exact (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  have hconvex : is_convex_function (fun y : E ↦ (g y : EReal)) := by
    have hne_bot :
        ∀ y ∈ effective_domain (fun y : E ↦ (g y : EReal)),
          (fun y : E ↦ (g y : EReal)) y ≠ ⊥ := by
      intro y hy
      simp
    -- Convexity reduces to the real-valued convexity statement on the full domain.
    refine (is_convex_function_iff_convexOn_toReal hne_bot).2 ?_
    simpa [effective_domain] using hg_convex
  exact ⟨hproper, hclosed, hconvex⟩

-- Proof sketch: compare the optimality inequalities for proximal points of `λ₁ g` and `λ₂ g`
-- with `0 ≤ λ₁ ≤ λ₂`, as in the level-set residual monotonicity argument. This gives
-- monotonicity of the infimum of the values `g y - λ - s` over the corresponding scaled proximal
-- minimizer sets, hence of `epigraph_projection_residual g x s`.
/-- The epigraph residual attached to a convex function is nonincreasing on the nonnegative
reals. -/
theorem epigraph_projection_residual_antitoneOn_nonneg
    (g : E → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (x : E) (s : ℝ) :
    AntitoneOn (epigraph_projection_residual g x s) (Set.Ici 0) := by
  let f : E → EReal := fun y : E ↦ (g y : EReal)
  rcases real_toEReal_proper_closed_convex g hg_convex with ⟨hf_proper, hf_closed, hf_convex⟩
  intro lam1 hlam1 lam2 hlam2 hle
  rcases lt_or_eq_of_le hle with hlt | rfl
  · by_cases hzero1 : lam1 = 0
    · have hlam2_pos : 0 < lam2 := lt_of_le_of_lt hlam1 hlt
      let lam2Pos : PosReal := ⟨lam2, hlam2_pos⟩
      rcases prox_eq_singleton_of_proper_closed_convex (((lam2Pos : EReal) • f))
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos).1
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos).2.1
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos).2.2
          x with
        ⟨u2, hprox2scaled⟩
      have hprox2 :
          prox[fun y : E ↦ (lam2 : EReal) * (g y : EReal)] x = {u2} := by
        simpa [f, Pi.smul_apply, smul_eq_mul, lam2Pos] using hprox2scaled
      have hu2 : u2 ∈ prox[fun y : E ↦ (lam2 : EReal) * (g y : EReal)] x := by
        simpa [hprox2]
      have hu2_min :
          ∀ v, proximal_objective (fun y : E ↦ (lam2 : EReal) * (g y : EReal)) x u2 ≤
            proximal_objective (fun y : E ↦ (lam2 : EReal) * (g y : EReal)) x v := by
        -- A proximal point minimizes the scaled proximal objective globally.
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu2
        exact hu2
      have hu2_real :
          lam2 * g u2 + (1 / 2 : ℝ) * ‖u2 - x‖ ^ (2 : ℕ) ≤ lam2 * g x := by
        -- Compare the positive-parameter proximal objective at `u2` with its value at `x`.
        exact EReal.coe_le_coe_iff.mp <| by
          simpa [proximal_objective_apply, hzero1, Pi.smul_apply, smul_eq_mul,
            EReal.coe_mul, EReal.coe_add] using hu2_min x
      have hu2_le : g u2 ≤ g x := by
        nlinarith [hu2_real]
      have hres2 :
          epigraph_projection_residual g x s lam2 = ((g u2 - lam2 - s : ℝ) : EReal) :=
        epigraph_projection_residual_eq_of_scaled_prox_eq_singleton g x s lam2 u2 hprox2
      have hres0 :
          epigraph_projection_residual g x s lam1 = ((g x - lam1 - s : ℝ) : EReal) := by
        subst hzero1
        simpa using
          epigraph_projection_residual_eq_of_scaled_prox_eq_singleton g x s 0 x
            (by
              -- At `λ = 0`, the proximal set is the singleton `{x}`.
              simpa [Pi.smul_apply, smul_eq_mul] using prox_zero_eq_singleton x)
      -- The positive branch decreases the function value, and subtracting `λ₂` only decreases it
      -- further relative to the zero branch.
      rw [hres2, hres0]
      exact_mod_cast (show g u2 - lam2 - s ≤ g x - lam1 - s by
        nlinarith [hu2_le, hlam2_pos])
    · have hlam1_pos : 0 < lam1 := lt_of_le_of_ne hlam1 (Ne.symm hzero1)
      let lam1Pos : PosReal := ⟨lam1, hlam1_pos⟩
      let lam2Pos : PosReal := ⟨lam2, lt_of_lt_of_le hlam1_pos hle⟩
      rcases prox_eq_singleton_of_proper_closed_convex (((lam1Pos : EReal) • f))
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam1Pos).1
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam1Pos).2.1
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam1Pos).2.2
          x with
        ⟨u1, hprox1scaled⟩
      rcases prox_eq_singleton_of_proper_closed_convex (((lam2Pos : EReal) • f))
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos).1
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos).2.1
          (scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos).2.2
          x with
        ⟨u2, hprox2scaled⟩
      have hprox1 :
          prox[fun y : E ↦ (lam1 : EReal) * (g y : EReal)] x = {u1} := by
        simpa [f, Pi.smul_apply, smul_eq_mul, lam1Pos] using hprox1scaled
      have hprox2 :
          prox[fun y : E ↦ (lam2 : EReal) * (g y : EReal)] x = {u2} := by
        simpa [f, Pi.smul_apply, smul_eq_mul, lam2Pos] using hprox2scaled
      have hu1 : u1 ∈ prox[((lam1Pos : EReal) • f)] x := by
        simpa [hprox1scaled]
      have hu2 : u2 ∈ prox[((lam2Pos : EReal) • f)] x := by
        simpa [hprox2scaled]
      have hgu : g u2 ≤ g u1 := by
        -- Theorem 6.30's monotonicity lemma compares function values along positive parameters.
        have hvalue :=
          scaled_prox_function_value_antitone_of_le f hf_proper x lam1Pos lam2Pos hlt hu1 hu2
        simpa [f] using hvalue
      have hres1 :
          epigraph_projection_residual g x s lam1 = ((g u1 - lam1 - s : ℝ) : EReal) :=
        epigraph_projection_residual_eq_of_scaled_prox_eq_singleton g x s lam1 u1 hprox1
      have hres2 :
          epigraph_projection_residual g x s lam2 = ((g u2 - lam2 - s : ℝ) : EReal) :=
        epigraph_projection_residual_eq_of_scaled_prox_eq_singleton g x s lam2 u2 hprox2
      -- Positive parameters compare through the antitonicity of scaled proximal function values
      -- and the extra `- λ` term from the residual.
      rw [hres2, hres1]
      exact_mod_cast (show g u2 - lam2 - s ≤ g u1 - lam1 - s by
        nlinarith [hgu, hlt])
  · exact le_rfl

end

end
