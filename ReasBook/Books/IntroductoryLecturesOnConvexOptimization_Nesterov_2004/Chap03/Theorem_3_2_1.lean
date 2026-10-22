/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Theorem 3.2.1 lies in the chapter's nonsmooth first-order black-box complexity domain.

Mandatory domain-style sampling before refinement:
* `IsSubgradientAt` in `Definition_3_1_5`, the chapter owner for valid first-order replies;
* mathlib `ConvexOn`, `IsMinOn`, and `LipschitzOnWith`, the canonical owner predicates for the
  problem-class data;
* mathlib `AffineSubspace.mk'` and `AffineSubspace.mem_mk'`, the canonical owner for an affine
  translate of a linear span;
* `coordinateSubspace k n` with notation `ℝ^{k,n}` in `Chap02/Definition_2_12`, the chapter owner
  for prefix coordinate subspaces in `ℝⁿ`;
* `FirstOrderConvexMinimizationProblem` in `Definition_3_40`, the downstream chapter owner that
  reuses the oracle surface introduced here.

Best owner abstraction:
* source-facing: the class `𝒫(x₀, R, M)`, the oracle owner `FirstOrderOracle`, the
  prefix-support-growth predicate, and the span-based iterate predicate;
* core/canonical: `IsSubgradientAt`, `ConvexOn`, `IsMinOn`, `LipschitzOnWith`, and the affine
  subspace `AffineSubspace.mk' x₀ (...)`, together with the coordinate-subspace owner
  `coordinateSubspace`;
* bridge/view: the pair-valued oracle reply `FirstOrderOracle.answer` and the projection lemmas
  from the source-facing owners.

Primitive data:
* the objective `f`;
* the chosen minimizer `xStar`;
* the oracle reply map `subgradient`;
* the oracle-side prefix-support-growth condition;
* the iterate sequence `xSeq`.

Derived API:
* the component accessors for `𝒫(x₀, R, M)`;
* the pair-valued oracle answer and its coordinate lemmas;
* the zero-step consequence of the affine linear-span owner.

The owner layer is intentionally split by the actual mathematics it uses:
* `IsInLipschitzConvexProblemClass` only needs the normed-space layer for convexity, minimizers,
  closed balls, and Lipschitz continuity;
* `FirstOrderOracle` lives on the chapter's real inner-product-space subgradient owner from
  `Definition_3_1_5`;
* `HasCoordinateSupportGrowth` lives on the chapter coordinate-subspace owner `ℝ^{i,n}`;
* `SatisfiesLinearSpanCondition` only needs affine/span structure.

The hard lower-bound theorem itself remains the textbook `ℝⁿ` specialization on
`EuclideanSpace ℝ (Fin n)`. -/

section LipschitzConvexProblemClass

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A function together with a chosen minimizer lies in the Lipschitz convex class
`𝒫(x₀, R, M)` when the objective is convex on the whole space, the chosen point globally
minimizes it, the starting point `x₀` lies in the closed ball `B₂(x*, R)`, and the objective is
`M`-Lipschitz on that ball. -/
def IsInLipschitzConvexProblemClass
    (x0 : V) (R M : NNReal) (f : V → ℝ) (xStar : V) : Prop :=
  ConvexOn ℝ Set.univ f ∧
    IsMinOn f Set.univ xStar ∧
    x0 ∈ Metric.closedBall xStar R ∧
    LipschitzOnWith M f (Metric.closedBall xStar R)

scoped[LipschitzConvexProblemClass] notation "𝒫(" x0 ", " R ", " M ")" =>
  IsInLipschitzConvexProblemClass x0 R M

open scoped LipschitzConvexProblemClass

namespace IsInLipschitzConvexProblemClass

variable {x0 xStar : V} {R M : NNReal} {f : V → ℝ}

/-- Membership in `𝒫(x₀, R, M)` records whole-space convexity of the objective. -/
theorem convexOn_univ
    (hf : 𝒫(x0, R, M) f xStar) :
    ConvexOn ℝ Set.univ f :=
  hf.1

/-- Membership in `𝒫(x₀, R, M)` records that the chosen point globally minimizes the objective. -/
theorem isMinOn
    (hf : 𝒫(x0, R, M) f xStar) :
    IsMinOn f Set.univ xStar :=
  hf.2.1

/-- Membership in `𝒫(x₀, R, M)` records that `x₀` lies in the controlling closed ball. -/
theorem start_mem_closedBall
    (hf : 𝒫(x0, R, M) f xStar) :
    x0 ∈ Metric.closedBall xStar R :=
  hf.2.2.1

/-- Membership in `𝒫(x₀, R, M)` records the Lipschitz bound on the controlling closed ball. -/
theorem lipschitzOn_closedBall
    (hf : 𝒫(x0, R, M) f xStar) :
    LipschitzOnWith M f (Metric.closedBall xStar R) :=
  hf.2.2.2

end IsInLipschitzConvexProblemClass

end LipschitzConvexProblemClass

section FirstOrderOracle

open scoped WithTopConvexAnalysis

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A first-order black-box oracle for a problem returns a subgradient at each query point. -/
structure FirstOrderOracle (f : V → ℝ) where
  /-- The subgradient returned by the oracle at the query point. -/
  subgradient : V → V
  /-- The returned vector is a genuine subgradient of the objective. -/
  subgradient_spec :
    ∀ x : V, IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (subgradient x)

namespace FirstOrderOracle

variable {f : V → ℝ}

/-- The reply of a first-order black-box oracle at `x` is the pair `(f(x), g(x))` consisting of
the objective value and the returned subgradient. -/
def answer (oracle : FirstOrderOracle f) (x : V) : ℝ × V :=
  (f x, oracle.subgradient x)

/-- The first component of the oracle reply is the objective value at the query point. -/
@[simp] theorem answer_fst (oracle : FirstOrderOracle f) (x : V) :
    (oracle.answer x).1 = f x :=
  rfl

/-- The second component of the oracle reply is the returned subgradient. -/
@[simp] theorem answer_snd (oracle : FirstOrderOracle f) (x : V) :
    (oracle.answer x).2 = oracle.subgradient x :=
  rfl

end FirstOrderOracle

end FirstOrderOracle

section LinearSpanCondition

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A sequence `x₀, x₁, …, x_k` satisfies the linear-span condition for a subgradient map `g`
when it starts at `x₀` and every iterate `x_t` with `t ≤ k` lies in
`x₀ + Lin{g(x₀), …, g(x_{t-1})}`. -/
def SatisfiesLinearSpanCondition
    (x0 : V) (g : V → V) (xSeq : ℕ → V) (k : ℕ) : Prop :=
  ∀ t ≤ k,
    xSeq t ∈
      AffineSubspace.mk' x0
        (Submodule.span ℝ (Set.range fun i : Fin t ↦ g (xSeq i)))

/-- A sequence satisfying the linear-span condition starts from the prescribed point `x₀`. -/
theorem SatisfiesLinearSpanCondition.zero_eq
    {x0 : V} {g : V → V} {xSeq : ℕ → V} {k : ℕ}
    (hx : SatisfiesLinearSpanCondition x0 g xSeq k) :
    xSeq 0 = x0 := by
  have hx0 :
      xSeq 0 ∈
        AffineSubspace.mk' x0
          (Submodule.span ℝ (Set.range fun i : Fin 0 ↦ g (xSeq i))) :=
    hx 0 (Nat.zero_le k)
  rw [AffineSubspace.mem_mk'] at hx0
  simpa [sub_eq_zero] using hx0

end LinearSpanCondition

section EuclideanLowerBound

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

open scoped LipschitzConvexProblemClass CoordinateSubspace

/-- A subgradient map satisfies the resisting-oracle prefix-support rule up to step `k` when each
query point lying in the affine translate `x₀ + ℝ^{i,n}` with `i < k` receives a subgradient in
the next prefix coordinate subspace `ℝ^{i+1,n}`. -/
def HasCoordinateSupportGrowth
    (x0 : E) (g : E → E) (k : ℕ) : Prop :=
  ∀ i < k, ∀ ⦃x : E⦄, x ∈ AffineSubspace.mk' x0 ℝ^{i,n} → g x ∈ ℝ^{i + 1,n}

/-- Helper for Theorem 3.2.1: every coordinate of a vector in `ℝⁿ` is bounded by the ambient
Euclidean norm. -/
theorem abs_coordinate_le_norm (v : E) (j : Fin n) :
    |v j| ≤ ‖v‖ := by
  have hinner : inner ℝ v e[j] = v j := by
    simpa using EuclideanSpace.inner_single_right j (1 : ℝ) v
  -- Re-express the chosen coordinate as an inner product against the standard basis vector.
  calc
    |v j| = |inner ℝ v e[j]| := by rw [hinner]
    _ ≤ ‖v‖ * ‖e[j]‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by simp [EuclideanSpace.single]

/-- Helper for Theorem 3.2.1: the span-condition iterates stay in the affine translate of the
corresponding prefix coordinate subspace whenever the oracle replies satisfy support growth. -/
theorem iterates_mem_affine_coordinateSubspace_under_support_growth
    {x0 : E} {g : E → E} {xSeq : ℕ → E} {k : ℕ}
    (hgrow : HasCoordinateSupportGrowth x0 g k)
    (hxSeq : SatisfiesLinearSpanCondition x0 g xSeq k)
    (i : ℕ) (hi : i ≤ k) :
    xSeq i ∈ AffineSubspace.mk' x0 ℝ^{i,n} := by
  refine Nat.strong_induction_on i ?_ hi
  intro i ih hik
  cases i with
  | zero =>
      -- At time `0`, the span condition already forces `x₀ = x0`.
      rw [SatisfiesLinearSpanCondition.zero_eq hxSeq]
      rw [AffineSubspace.mem_mk']
      simp
  | succ i =>
      have hstep :
          xSeq (i + 1) - x0 ∈
            Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t)) := by
        -- The span condition expresses `x_{i+1}` as `x0` plus a span combination.
        have hxSeq_step :
            xSeq (i + 1) ∈
              AffineSubspace.mk' x0
                (Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t))) :=
          hxSeq (i + 1) hik
        rwa [AffineSubspace.mem_mk'] at hxSeq_step
      have hspan :
          Submodule.span ℝ (Set.range fun t : Fin (i + 1) ↦ g (xSeq t)) ≤ ℝ^{i + 1,n} :=
        prefix_span_le_coordinateSubspace (fun t ↦ g (xSeq t)) fun j ↦
          hgrow j (lt_of_lt_of_le j.is_lt hik)
            (ih j j.is_lt (Nat.le_of_lt (lt_of_lt_of_le j.is_lt hik)))
      -- Push the span membership through the prefix-span inclusion.
      rw [AffineSubspace.mem_mk']
      exact hspan hstep

/-- Helper for Theorem 3.2.1: points in the affine translate `x0 + ℝ^{k,n}` agree with `x0` on
every coordinate of index at least `k`. -/
theorem coordinate_eq_start_of_mem_affine_coordinateSubspace
    {x0 x : E} {k : ℕ} {j : Fin n}
    (hx : x ∈ AffineSubspace.mk' x0 ℝ^{k,n})
    (hj : k ≤ j.1) :
    x j = x0 j := by
  -- Membership in the affine translate means the tail coordinates of `x - x0` vanish.
  rw [AffineSubspace.mem_mk'] at hx
  exact sub_eq_zero.mp ((mem_coordinateSubspace_iff.mp hx) j hj)

/-- Helper for Theorem 3.2.1: shifting the minimizer by radius `R` in a fresh coordinate forces
every point in `x0 + ℝ^{k,n}` to stay at distance at least `R` from that minimizer. -/
theorem shifted_coordinate_distance_lower_bound
    (x0 : E) (R : NNReal) {k : ℕ} {x : E} {j : Fin n}
    (hx : x ∈ AffineSubspace.mk' x0 ℝ^{k,n})
    (hj : k ≤ j.1) :
    (R : ℝ) ≤ dist x (x0 + (R : ℝ) • e[j]) := by
  have hxj : x j = x0 j :=
    coordinate_eq_start_of_mem_affine_coordinateSubspace hx hj
  -- The fresh coordinate of `x - xStar` is exactly `-R`, so the whole norm is at least `R`.
  have hcoord :=
    abs_coordinate_le_norm (x - (x0 + (R : ℝ) • e[j])) j
  simpa [dist_eq_norm, hxj, EuclideanSpace.single] using hcoord

/-- Helper for Theorem 3.2.1: the shifted-point distance witness belongs to
`𝒫(x₀, R, M)`. -/
theorem scaled_shifted_distance_witness_mem_problemClass
    (x0 : E) (R M : NNReal) {k : ℕ} {j : Fin n} :
    𝒫(x0, R, M)
      (fun x ↦ ((M : ℝ) / (2 * (2 + Real.sqrt (k + 1 : ℝ)))) * dist x (x0 + (R : ℝ) • e[j]))
      (x0 + (R : ℝ) • e[j]) := by
  let scale : ℝ := (M : ℝ) / (2 * (2 + Real.sqrt (k + 1 : ℝ)))
  let xStar : E := x0 + (R : ℝ) • e[j]
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hscale_le_M : scale ≤ M := by
    dsimp [scale]
    have hden_pos : 0 < 2 * (2 + Real.sqrt (k + 1 : ℝ)) := by
      positivity
    rw [div_le_iff₀ hden_pos]
    nlinarith [show 0 ≤ (M : ℝ) by exact M.2, Real.sqrt_nonneg (k + 1 : ℝ)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The witness is a nonnegative scalar multiple of the convex distance function.
    simpa [scale, xStar, smul_eq_mul] using
      (convexOn_univ_dist xStar).smul hscale_nonneg
  · -- The shifted point is a global minimizer because the distance is minimized there.
    intro y _hy
    change scale * dist xStar xStar ≤ scale * dist y xStar
    simpa [hscale_nonneg] using mul_nonneg hscale_nonneg (dist_nonneg : 0 ≤ dist y xStar)
  · -- The chosen minimizer sits exactly at distance `R` from the starting point.
    rw [Metric.mem_closedBall]
    change dist x0 xStar ≤ R
    rw [dist_eq_norm]
    have hsub : x0 - xStar = -((R : ℝ) • e[j]) := by
      dsimp [xStar]
      abel
    rw [hsub, norm_neg, norm_smul]
    simp [EuclideanSpace.single]
  · -- The witness is globally `scale`-Lipschitz, and `scale ≤ M`.
    refine LipschitzOnWith.of_le_add_mul M ?_
    intro x _hx y _hy
    change scale * dist x xStar ≤ scale * dist y xStar + M * dist x y
    calc
      scale * dist x xStar ≤ scale * (dist x y + dist y xStar) := by
        gcongr
        exact dist_triangle x y xStar
      _ = scale * dist y xStar + scale * dist x y := by ring
      _ ≤ scale * dist y xStar + M * dist x y := by
        gcongr

/-- Theorem 3.2.1: for every `k` with `0 ≤ k ≤ n - 1`, there exist an objective `f` and a chosen
minimizer `x*` in the class `𝒫(x₀, R, M)` such that every first-order oracle whose replies satisfy
the resisting-oracle prefix-support rule, together with every iterate sequence satisfying the span
condition for that oracle, has objective gap at least `MR / (2 (2 + √(k + 1)))` at step `k`. -/
-- Proof sketch: choose the Nemirovski hard instance with `k + 1` active coordinates and tune its
-- parameters so that the chosen minimizer is exactly at distance `R` from `x₀` and the objective
-- is `M`-Lipschitz on the relevant ball. The oracle-side prefix-support hypothesis and the span
-- condition then trap the first `k` iterates in the coordinate-prefix subspace where the hard
-- instance still has objective value at least the displayed lower bound above the optimum.
theorem exists_problem_with_nonsmooth_firstOrder_lower_bound
    (n : ℕ) (x0 : EuclideanSpace ℝ (Fin n)) (R M : NNReal) {k : ℕ} (hk : k + 1 ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ∃ xStar : EuclideanSpace ℝ (Fin n),
      𝒫(x0, R, M) f xStar ∧
        ∀ oracle : FirstOrderOracle f,
          HasCoordinateSupportGrowth x0 oracle.subgradient k →
          ∀ xSeq : ℕ → EuclideanSpace ℝ (Fin n),
            SatisfiesLinearSpanCondition x0 oracle.subgradient xSeq k →
              f (xSeq k) - f xStar ≥
                ((M : ℝ) * (R : ℝ)) / (2 * (2 + Real.sqrt (k + 1 : ℝ))) := by
  let j : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  let scale : ℝ := (M : ℝ) / (2 * (2 + Real.sqrt (k + 1 : ℝ)))
  let xStar : EuclideanSpace ℝ (Fin n) :=
    x0 + (R : ℝ) • (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n))
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ scale * dist x xStar
  refine ⟨f, xStar, ?_, ?_⟩
  · -- Package the shifted-distance witness into the chapter's problem class.
    simpa [f, xStar, j] using
      (scaled_shifted_distance_witness_mem_problemClass (n := n) x0 R M (k := k) (j := j))
  · intro oracle hgrow xSeq hxSeq
    have hxk :
        xSeq k ∈ AffineSubspace.mk' x0 ℝ^{k,n} :=
      iterates_mem_affine_coordinateSubspace_under_support_growth
        (n := n) hgrow hxSeq k le_rfl
    have hdist : (R : ℝ) ≤ dist (xSeq k) xStar := by
      -- The `k`-th iterate still agrees with `x0` on the fresh coordinate `j = k`.
      simpa [xStar, j] using
        (shifted_coordinate_distance_lower_bound (n := n) x0 R hxk
          (show k ≤ j.1 by simp [j]))
    have hscale_nonneg : 0 ≤ scale := by
      dsimp [scale]
      positivity
    have hgap : scale * (R : ℝ) ≤ scale * dist (xSeq k) xStar :=
      mul_le_mul_of_nonneg_left hdist hscale_nonneg
    -- Convert the distance lower bound into the objective-gap estimate.
    calc
      f (xSeq k) - f xStar = scale * dist (xSeq k) xStar := by
        simp [f, xStar, scale]
      _ ≥ scale * (R : ℝ) := hgap
      _ = ((M : ℝ) * (R : ℝ)) / (2 * (2 + Real.sqrt (k + 1 : ℝ))) := by
        dsimp [scale]
        ring

end EuclideanLowerBound

end
