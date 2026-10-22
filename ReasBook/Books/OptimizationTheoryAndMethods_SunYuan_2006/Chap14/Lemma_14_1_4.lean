/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_3
noncomputable section

open scoped BigOperators Pointwise ClarkeDifferential ClarkeDirectionalDerivative

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "DualSpace" => StrongDual ℝ E
local notation "WeakDualSpace" => WeakDual ℝ E

/-
Domain sampling:
- primary domain: Clarke generalized gradients and their set-valued continuity calculus
- sampled chapter owners: `clarkeDifferential`, `mem_clarkeDifferential_iff`,
  `LocallyLipschitzAt`
- sampled mathlib owner in the same set-valued continuity domain: `UpperHemicontinuousOn`
- source-facing layer here: Lemma 14.1.4 consequences for neighborhoods, finite sums, and
  the chain-rule inclusion
- core/canonical owner reused here: `clarkeDifferential`
- primitive data: a function together with the local Lipschitz hypotheses demanded by each item
- derived API here: the neighborhood formula, upper-hemicontinuity statement, finite-sum
  inclusion, and chain-rule inclusion built on the canonical Clarke owner
-/

/- Chapter14 Lemma 14.1.4 (1): recall the canonical Clarke-differential membership criterion. -/
#check mem_clarkeDifferential_iff

/-- Helper for Chapter14 Lemma 14.1.4: the sum of two locally Lipschitz scalar maps is locally
Lipschitz at the same point. -/
theorem LocallyLipschitzAt.add {f g : E → ℝ} {x : E}
    (hf : LocallyLipschitzAt f x) (hg : LocallyLipschitzAt g x) :
    LocallyLipschitzAt (fun y ↦ f y + g y) x := by
  rcases locallyLipschitzAt_iff.mp hf with ⟨εf, hεf, Kf, hKf⟩
  rcases locallyLipschitzAt_iff.mp hg with ⟨εg, hεg, Kg, hKg⟩
  let ε := min εf εg
  have hε : 0 < ε := lt_min hεf hεg
  refine locallyLipschitzAt_of_closedBall (K := Kf + Kg) ⟨ε, hε, ?_⟩
  have hf' : LipschitzOnWith Kf f (Metric.closedBall x ε) :=
    hKf.mono <| Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hg' : LipschitzOnWith Kg g (Metric.closedBall x ε) :=
    hKg.mono <| Metric.closedBall_subset_closedBall (min_le_right _ _)
  -- Intersect the two closed-ball witnesses and add the resulting Lipschitz bounds.
  simpa [ε] using hf'.add hg'

/-- Helper for Chapter14 Lemma 14.1.4: a locally Lipschitz map is continuous at the same base
point. -/
theorem LocallyLipschitzAt.continuousAt
    {X : Type*} {Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {F : X → Y} {x : X} (hF : LocallyLipschitzAt F x) :
    ContinuousAt F x := by
  rcases locallyLipschitzAt_iff.mp hF with ⟨ε₀, hε₀, K, hK⟩
  refine Metric.continuousAt_iff'.2 ?_
  intro ε hε
  let δ := min ε₀ (ε / ((K : ℝ) + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    refine lt_min hε₀ ?_
    positivity
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hy_closed : y ∈ Metric.closedBall x ε₀ := by
    rw [Metric.mem_closedBall]
    exact le_trans (le_of_lt hy) (min_le_left _ _)
  have hx_closed : x ∈ Metric.closedBall x ε₀ :=
    Metric.mem_closedBall_self hε₀.le
  have hdist :
      dist (F y) (F x) ≤ (K : ℝ) * dist y x :=
    hK.dist_le_mul y hy_closed x hx_closed
  have hy_lt : dist y x < ε / ((K : ℝ) + 1) := by
    exact lt_of_lt_of_le hy (min_le_right _ _)
  have hmul_lt :
      (K : ℝ) * dist y x < ε := by
    have hδ_eq : ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) = ε := by
      have hden_ne : ((K : ℝ) + 1) ≠ 0 := by positivity
      field_simp [hden_ne]
    have hmul_le :
        (K : ℝ) * dist y x ≤ (K : ℝ) * (ε / ((K : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hy_lt) K.2
    calc
      (K : ℝ) * dist y x ≤ (K : ℝ) * (ε / ((K : ℝ) + 1)) := hmul_le
      _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) := by
        exact mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ = ε := hδ_eq
  -- The closed-ball Lipschitz witness controls the image distance on the punctured neighborhood.
  exact lt_of_le_of_lt hdist hmul_lt

/-- Helper for Chapter14 Lemma 14.1.4: an evaluation halfspace in `WeakDual ℝ E` is stable under
weak-* closed convex hull. -/
lemma eval_halfspace_closedConvexHull_subset
    (d : E) (c : ℝ) {s : Set WeakDualSpace}
    (hs : s ⊆ {η : WeakDualSpace | η d ≤ c}) :
    closedConvexHull ℝ s ⊆ {η : WeakDualSpace | η d ≤ c} := by
  -- The target halfspace is weak-* closed because evaluation at `d` is continuous.
  have hclosed : IsClosed {η : WeakDualSpace | η d ≤ c} :=
    isClosed_le (WeakDual.eval_continuous d) continuous_const
  -- The same halfspace is convex because evaluation at `d` is linear.
  have hconv : Convex ℝ {η : WeakDualSpace | η d ≤ c} := by
    simpa using
      convex_halfSpace_le
        (show IsLinearMap ℝ (fun η : WeakDualSpace ↦ η d) by
          refine ⟨?_, ?_⟩
          · intro x y
            rfl
          · intro a x
            rfl)
        c
  exact closedConvexHull_min hs hconv hclosed

/-- Helper for Chapter14 Lemma 14.1.4: a weak-* closed convex subset of `WeakDual ℝ E` is exactly
the intersection of the evaluation halfspaces that contain it. -/
lemma mem_closed_convex_iff_eval_halfspaces
    {S : Set WeakDualSpace} {ξ : WeakDualSpace}
    (h_conv : Convex ℝ S) (h_closed : IsClosed S) :
    ξ ∈ S ↔ ∀ d : E, ∃ η ∈ S, ξ d ≤ η d := by
  constructor
  · intro hξ d
    -- Inside `S`, the evaluation inequality is realized by `ξ` itself.
    exact ⟨ξ, hξ, le_rfl⟩
  · intro h_eval
    letI : LocallyConvexSpace ℝ WeakDualSpace :=
      WeakBilin.locallyConvexSpace (B := topDualPairing ℝ E)
    -- Route correction: the previous proof attempt lacked the weak-* support bridge.
    -- We now rewrite closed convex membership through Hahn-Banach halfspaces, then specialize
    -- every dual functional on `WeakDual ℝ E` to evaluation at some `d : E`.
    rw [← iInter_halfSpaces_eq h_conv h_closed]
    rw [Set.mem_iInter]
    intro l
    obtain ⟨d, rfl⟩ :=
      LinearMap.dualEmbedding_surjective (topDualPairing ℝ E) l
    obtain ⟨η, hηS, hle⟩ := h_eval d
    refine ⟨η, hηS, ?_⟩
    change ξ d ≤ η d
    exact hle

/-- Helper for Chapter14 Lemma 14.1.4: the support value of the finite Minkowski sum of nearby
Clarke differentials is attained by summing support maximizers of the summands. -/
lemma exists_mem_toWeakDual_image_finsetSum_clarkeDifferential_eval_eq
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x d : E)
    (h_local : ∀ i ∈ s, LocallyLipschitzAt (f i) x) :
    ∃ η ∈ s.sum (fun i ↦ StrongDual.toWeakDual '' (∂ᶜ (f i)) x),
      η d = s.sum (fun i ↦ clarkeDirectionalDerivReal (f i) x d) := by
  classical
  have hmax :
      ∀ i : s,
        ∃ ξ : DualSpace, ξ ∈ (∂ᶜ (f i.1)) x ∧ ξ d = clarkeDirectionalDerivReal (f i.1) x d := by
    intro i
    have hgreat :=
      clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
        (f i.1) x d (h_local i.1 i.2)
    rcases hgreat.1 with ⟨ξ, hξ, hξeval⟩
    exact ⟨ξ, hξ, hξeval⟩
  choose ξ hξmem hξeval using hmax
  let ζ : ι → DualSpace := fun i ↦ if hi : i ∈ s then ξ ⟨i, hi⟩ else 0
  have hζmem : ∀ i ∈ s, ζ i ∈ (∂ᶜ (f i)) x := by
    intro i hi
    simpa [ζ, hi] using hξmem ⟨i, hi⟩
  have hζeval : ∀ i ∈ s, ζ i d = clarkeDirectionalDerivReal (f i) x d := by
    intro i hi
    simpa [ζ, hi] using hξeval ⟨i, hi⟩
  refine ⟨∑ i ∈ s, StrongDual.toWeakDual (ζ i), ?_, ?_⟩
  · -- Build the weak-dual witness termwise inside the finite Minkowski sum.
    exact Set.finsetSum_mem_finsetSum s
      (fun i ↦ StrongDual.toWeakDual '' (∂ᶜ (f i)) x)
      (fun i ↦ StrongDual.toWeakDual (ζ i))
      (fun i hi ↦ ⟨ζ i, hζmem i hi, rfl⟩)
  · -- Evaluation commutes with the finite sum and records the maximizing support values.
    let ev : WeakDualSpace →ₗ[ℝ] ℝ :=
      { toFun := fun η ↦ η d
        map_add' := by intro η₁ η₂; rfl
        map_smul' := by intro a η; rfl }
    calc
      (∑ i ∈ s, StrongDual.toWeakDual (ζ i)) d = ∑ i ∈ s, (StrongDual.toWeakDual (ζ i)) d := by
        change ev (∑ i ∈ s, StrongDual.toWeakDual (ζ i)) =
          ∑ i ∈ s, ev (StrongDual.toWeakDual (ζ i))
        rw [map_sum]
      _ = ∑ i ∈ s, clarkeDirectionalDerivReal (f i) x d := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using hζeval i hi

/-- Helper for Chapter14 Lemma 14.1.4: upper semicontinuity of the Clarke directional derivative
at `(x, d)` gives a closed-ball neighborhood on which the fixed-direction support values stay
below `clarkeDirectionalDerivReal f x d + ε`. -/
lemma clarkeDirectionalDeriv_nearby_le_of_upperSemicontinuousAt
    (f : E → ℝ) (x d : E) (h_local : LocallyLipschitzAt f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Metric.closedBall x δ,
      fᵒ(y; d) ≤ (((clarkeDirectionalDerivReal f x d + ε : ℝ)) : EReal) := by
  let F : E → EReal := fun y ↦ fᵒ(y; d)
  have husc_pair : UpperSemicontinuousAt (fun p : E × E ↦ fᵒ(p.1; p.2)) (x, d) :=
    clarkeDirectionalDerivative_upperSemicontinuousAt (f := f) (x := x) h_local d
  have hcont : ContinuousAt (fun y : E ↦ (y, d)) x :=
    (continuous_id.prodMk continuous_const).continuousAt
  have husc : UpperSemicontinuousAt F x := by
    -- Route correction: specialize the known `(y, e)` upper-semicontinuity theorem to the
    -- source-faithful fixed direction `e = d` before extracting a closed-ball radius.
    convert husc_pair.comp (g := fun y : E ↦ (y, d)) hcont using 1
    ext y
    simp [F]
  have hstrict_real :
      clarkeDirectionalDerivReal f x d < clarkeDirectionalDerivReal f x d + ε := by
    linarith
  have hstrict :
      F x < (((clarkeDirectionalDerivReal f x d + ε : ℝ)) : EReal) := by
    -- Replace the base value by the finite real-valued Clarke derivative before lifting the
    -- strict inequality from `ℝ` to `EReal`.
    change fᵒ(x; d) < (((clarkeDirectionalDerivReal f x d + ε : ℝ)) : EReal)
    rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local]
    exact_mod_cast hstrict_real
  rw [upperSemicontinuousAt_iff] at husc
  have h_event :
      ∀ᶠ y in nhds x, F y < (((clarkeDirectionalDerivReal f x d + ε : ℝ)) : EReal) :=
    husc _ hstrict
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 h_event
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  -- The closed ball produced by the neighborhood basis is exactly the uniform region we need.
  exact le_of_lt (hball hy)

/-- Chapter14 Lemma 14.1.4 (2): if `f` is Lipschitz near `x`, then the weak-* image of
`(∂ᶜ f) x` in `WeakDual ℝ E` is the intersection over all radii `δ > 0` of the weak-*
closed convex hulls of the unions of the nearby weak-* images of the Clarke differentials
`(∂ᶜ f) y` for `y ∈ Metric.closedBall x δ`. -/
theorem toWeakDual_image_clarkeDifferential_eq_iInter_closedConvexHull_iUnion
    (f : E → ℝ) (x : E) (h_local : LocallyLipschitzAt f x) :
    StrongDual.toWeakDual '' (∂ᶜ f) x =
      ⋂ (δ : ℝ) (_ : 0 < δ),
        closedConvexHull ℝ
          (⋃ y ∈ Metric.closedBall x δ, StrongDual.toWeakDual '' (∂ᶜ f) y) := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · intro ξ hξ
    rw [Set.mem_iInter]
    intro δ
    rw [Set.mem_iInter]
    intro hδ
    -- The nearby union already contains the base fiber at `y = x`.
    exact (subset_closedConvexHull (𝕜 := ℝ)) <|
      Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨Metric.mem_closedBall_self hδ.le, hξ⟩⟩
  · intro ξ hξ
    have h_conv :
        Convex ℝ (StrongDual.toWeakDual '' (∂ᶜ f) x) := by
      -- The target set is the linear image of the convex Clarke differential.
      simpa using
        (convex_clarkeDifferential_of_locallyLipschitzAt f x h_local).linear_image
          (StrongDual.toWeakDual.toLinearMap : DualSpace →ₗ[ℝ] WeakDualSpace)
    have h_closed :
        IsClosed (StrongDual.toWeakDual '' (∂ᶜ f) x) := by
      -- Weak-* compactness from Lemma 14.1.3 gives closedness in the Hausdorff weak dual.
      exact
        (isCompact_toWeakDual_image_clarkeDifferential_of_locallyLipschitzAt f x h_local).isClosed
    rw [mem_closed_convex_iff_eval_halfspaces h_conv h_closed]
    intro d
    obtain ⟨ξmax, hξmax_mem, hξmax_eval⟩ :=
      (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
        f x d h_local).1
    refine ⟨StrongDual.toWeakDual ξmax, ⟨ξmax, hξmax_mem, rfl⟩, ?_⟩
    have hξ_le : ξ d ≤ clarkeDirectionalDerivReal f x d := by
      by_contra hlt
      have hε : 0 < (ξ d - clarkeDirectionalDerivReal f x d) / 2 := by
        linarith
      obtain ⟨δ, hδ, hnear⟩ :=
        clarkeDirectionalDeriv_nearby_le_of_upperSemicontinuousAt f x d h_local hε
      have hmemδ :
          ξ ∈ closedConvexHull ℝ
            (⋃ y ∈ Metric.closedBall x δ, StrongDual.toWeakDual '' (∂ᶜ f) y) := by
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hξ δ) hδ
      have hhalfspace :
          closedConvexHull ℝ
              (⋃ y ∈ Metric.closedBall x δ, StrongDual.toWeakDual '' (∂ᶜ f) y) ⊆
            {η : WeakDualSpace |
              η d ≤ clarkeDirectionalDerivReal f x d + (ξ d - clarkeDirectionalDerivReal f x d) / 2} := by
        refine eval_halfspace_closedConvexHull_subset d _ ?_
        intro η hη
        rcases Set.mem_iUnion.1 hη with ⟨y, hη⟩
        rcases Set.mem_iUnion.1 hη with ⟨hy, hη⟩
        rcases hη with ⟨ζ, hζ, rfl⟩
        have hζ_mem :
            (((ζ d : ℝ)) : EReal) ≤ fᵒ(y; d) := by
          exact (mem_clarkeDifferential_iff (f := f) (x := y) ζ).1 hζ d
        have hζ_near :
            fᵒ(y; d) ≤
              (((clarkeDirectionalDerivReal f x d +
                    (ξ d - clarkeDirectionalDerivReal f x d) / 2 : ℝ)) : EReal) :=
          hnear y hy
        show (StrongDual.toWeakDual ζ) d ≤
            clarkeDirectionalDerivReal f x d +
              (ξ d - clarkeDirectionalDerivReal f x d) / 2
        exact_mod_cast (hζ_mem.trans hζ_near)
      have hbound : ξ d ≤
          clarkeDirectionalDerivReal f x d + (ξ d - clarkeDirectionalDerivReal f x d) / 2 :=
        hhalfspace hmemδ
      have hgt : clarkeDirectionalDerivReal f x d < ξ d := lt_of_not_ge hlt
      linarith
    -- The maximizing subgradient at `x` closes the support inequality.
    calc
      ξ d ≤ clarkeDirectionalDerivReal f x d := hξ_le
      _ = ξmax d := by
        simpa using hξmax_eval.symm
      _ = (StrongDual.toWeakDual ξmax) d := by
        rfl

/-- Helper for Chapter14 Lemma 14.1.4: in finite dimension, the weak-* image of the Clarke
differential is upper hemicontinuous on the local-Lipschitz locus. -/
lemma toWeakDual_image_clarkeDifferential_upperHemicontinuousOn_of_finiteDimensional
    [FiniteDimensional ℝ E] (f : E → ℝ) :
    UpperHemicontinuousOn
      (fun x : E ↦ StrongDual.toWeakDual '' (∂ᶜ f) x)
      {x : E | LocallyLipschitzAt f x} := by
  classical
  let F : E → Set WeakDualSpace := fun y ↦ StrongDual.toWeakDual '' (∂ᶜ f) y
  refine UpperHemicontinuousOn.of_frequently ?_
  intro x hx t ht hfreq
  rcases locallyLipschitzAt_iff.mp hx with ⟨ε, hε, K, hK⟩
  have hε2 : 0 < ε / 2 := by positivity
  let B : Set WeakDualSpace :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : DualSpace) (K : ℝ)
  have hseqCompactB : IsSeqCompact B := by
    simpa [B] using
      (WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := E) (x' := (0 : DualSpace)) (r := (K : ℝ)))
  have hbounded_near :
      ∀ᶠ y in nhdsWithin x {y : E | LocallyLipschitzAt f y}, F y ⊆ B := by
    have hball_nhds :
        Metric.closedBall x (ε / 2) ∈ nhdsWithin x {y : E | LocallyLipschitzAt f y} :=
      mem_nhdsWithin_of_mem_nhds <| Metric.closedBall_mem_nhds x hε2
    filter_upwards [hball_nhds] with y hy η hη
    rcases hη with ⟨ξ, hξ, rfl⟩
    have hy' : y ∈ Metric.closedBall x (ε / 2) := hy
    have hsubset : Metric.closedBall y (ε / 2) ⊆ Metric.closedBall x ε := by
      intro z hz
      rw [Metric.mem_closedBall] at hy' hz ⊢
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ ε / 2 + ε / 2 := by gcongr
        _ = ε := by ring
    have hξ_norm : ‖ξ‖ ≤ (K : ℝ) :=
      norm_le_of_mem_clarkeDifferential_of_closedBallLipschitz
        f y K ⟨ε / 2, hε2, hK.mono hsubset⟩ hξ
    change ξ ∈ Metric.closedBall (0 : DualSpace) (K : ℝ)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hξ_norm
  obtain ⟨xseq, hxseq, hxmem⟩ := Filter.exists_seq_forall_of_frequently hfreq
  choose ξseq hξmem using hxmem
  have hξeventB : ∀ᶠ n in Filter.atTop, ξseq n ∈ B := by
    filter_upwards [hxseq.eventually hbounded_near] with n hn
    exact hn (hξmem n).1
  obtain ⟨ξ₀, -, φ, hφ, hξφ⟩ := hseqCompactB.subseq_of_frequently_in (x := ξseq) <| by
    exact hξeventB.frequently
  have hξ₀_mem_t : ξ₀ ∈ t := by
    exact ht.mem_of_tendsto hξφ <| Filter.Eventually.of_forall fun n ↦ (hξmem (φ n)).2
  have hξ₀_mem_Fx : ξ₀ ∈ F x := by
    dsimp [F]
    rw [toWeakDual_image_clarkeDifferential_eq_iInter_closedConvexHull_iUnion f x hx, Set.mem_iInter]
    intro δ
    rw [Set.mem_iInter]
    intro hδ
    have hball_event :
        ∀ᶠ n in Filter.atTop, xseq (φ n) ∈ Metric.closedBall x δ := by
      exact (hxseq.comp hφ.tendsto_atTop).eventually <|
        mem_nhdsWithin_of_mem_nhds <| Metric.closedBall_mem_nhds x hδ
    have hHull_event :
        ∀ᶠ n in Filter.atTop,
          ξseq (φ n) ∈
            closedConvexHull ℝ (⋃ y ∈ Metric.closedBall x δ, F y) := by
      filter_upwards [hball_event] with n hn
      exact subset_closedConvexHull (𝕜 := ℝ) <|
        Set.mem_iUnion.2 ⟨xseq (φ n), Set.mem_iUnion.2 ⟨hn, (hξmem (φ n)).1⟩⟩
    exact isClosed_closedConvexHull.mem_of_tendsto hξφ hHull_event
  exact ⟨ξ₀, hξ₀_mem_Fx, hξ₀_mem_t⟩

/-- Helper for Chapter14 Lemma 14.1.4: in finite dimension, the norm-dual and weak-* dual
topologies agree along the canonical dual identification. -/
lemma isInducing_toWeakDual_of_finiteDimensional [FiniteDimensional ℝ E] :
    Topology.IsInducing (StrongDual.toWeakDual : DualSpace → WeakDualSpace) := by
  let e : DualSpace ≃ₗ[ℝ] WeakDualSpace := StrongDual.toWeakDual
  simpa using
    (e.toContinuousLinearEquiv.toHomeomorph.isInducing :
      Topology.IsInducing (e : DualSpace → WeakDualSpace))

/-- Chapter14 Lemma 14.1.4 (3): if `E` is finite-dimensional, then the Clarke differential
`∂ f` is upper hemicontinuous on the locus where `f` is locally Lipschitz. -/
theorem clarkeDifferential_upperHemicontinuousOn_of_finiteDimensional
    [FiniteDimensional ℝ E] (f : E → ℝ) :
    UpperHemicontinuousOn (∂ᶜ f) {x : E | LocallyLipschitzAt f x} := by
  -- Route correction: prove upper hemicontinuity first for the weak-* image correspondence,
  -- then pull it back along the finite-dimensional dual identification.
  have hweak :
      UpperHemicontinuousOn
        (fun x : E ↦ StrongDual.toWeakDual '' (∂ᶜ f) x)
        {x : E | LocallyLipschitzAt f x} :=
    toWeakDual_image_clarkeDifferential_upperHemicontinuousOn_of_finiteDimensional f
  have hrange :
      Set.range (StrongDual.toWeakDual : DualSpace → WeakDualSpace) = Set.univ := by
    ext ξ
    constructor
    · intro _
      simp
    · intro _
      rcases StrongDual.toWeakDual.surjective ξ with ⟨η, rfl⟩
      exact ⟨η, rfl⟩
  simpa [Set.preimage_image_eq, StrongDual.toWeakDual.injective] using
    hweak.isInducing_comp
      (i := (StrongDual.toWeakDual : DualSpace → WeakDualSpace))
      isInducing_toWeakDual_of_finiteDimensional
      (by simpa [hrange] using (isClosed_univ : IsClosed (Set.univ : Set WeakDualSpace)))

/-- Chapter14 Lemma 14.1.4 (4): a finite sum of functions indexed by a finite set `s` that are
Lipschitz near `x` is again Lipschitz near `x`. -/
theorem locallyLipschitzAt_finsetSum
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (h_local : ∀ i ∈ s, LocallyLipschitzAt (f i) x) :
    LocallyLipschitzAt (fun y ↦ s.sum fun i ↦ f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine locallyLipschitzAt_of_closedBall (K := 0) ⟨1, zero_lt_one, ?_⟩
      -- The empty sum is the constant zero function, hence it is globally Lipschitz.
      simpa using (LipschitzWith.const (b := (0 : ℝ))).lipschitzOnWith
  | @insert i s hi hs =>
      have hi_local : LocallyLipschitzAt (f i) x := h_local i (by simp)
      have hs_local : ∀ j ∈ s, LocallyLipschitzAt (f j) x := by
        intro j hj
        exact h_local j (by simp [hj])
      -- Split off the head term and close the remaining finite sum by the induction hypothesis.
      simpa [Finset.sum_insert hi] using hi_local.add (hs hs_local)

/-- Helper for Chapter14 Lemma 14.1.4: the real-valued Clarke directional derivative of a sum of
two locally Lipschitz scalar maps is bounded by the sum of the two support values. -/
lemma clarkeDirectionalDerivReal_add_le
    (u v : E → ℝ) (x d : E)
    (hu : LocallyLipschitzAt u x) (hv : LocallyLipschitzAt v x) :
    clarkeDirectionalDerivReal (fun y ↦ u y + v y) x d ≤
      clarkeDirectionalDerivReal u x d + clarkeDirectionalDerivReal v x d := by
  let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
  let quv : E × ℝ → EReal :=
    fun p ↦ ((((u (p.1 + p.2 • d) + v (p.1 + p.2 • d)) - (u p.1 + v p.1)) / p.2 : ℝ) : EReal)
  let qu : E × ℝ → EReal :=
    fun p ↦ (((u (p.1 + p.2 • d) - u p.1) / p.2 : ℝ) : EReal)
  let qv : E × ℝ → EReal :=
    fun p ↦ (((v (p.1 + p.2 • d) - v p.1) / p.2 : ℝ) : EReal)
  have hquv_eq : quv =ᶠ[l] fun p ↦ qu p + qv p := by
    -- Split the common difference quotient pointwise before taking the limsup.
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp_ne : p.2 ≠ 0 := ne_of_gt hp
    have hreal :
        (((u (p.1 + p.2 • d) + v (p.1 + p.2 • d)) - (u p.1 + v p.1)) / p.2 : ℝ) =
          ((u (p.1 + p.2 • d) - u p.1) / p.2 : ℝ) +
            ((v (p.1 + p.2 • d) - v p.1) / p.2 : ℝ) := by
      field_simp [hp_ne]
      ring
    dsimp [quv, qu, qv]
    exact_mod_cast hreal
  have hquv_limsup :
      Filter.limsup quv l = (fun y ↦ u y + v y)ᵒ(x; d) := by
    -- Rewrite the composite quotient back to the canonical Clarke limsup formula.
    rw [clarkeDirectionalDeriv_eq_limsup]
    simpa [l, quv, wholeSpaceClarkePairDomain_eq_positiveTimes]
  have hqu_limsup : Filter.limsup qu l = uᵒ(x; d) := by
    rw [clarkeDirectionalDeriv_eq_limsup]
    simpa [l, qu, wholeSpaceClarkePairDomain_eq_positiveTimes]
  have hqv_limsup : Filter.limsup qv l = vᵒ(x; d) := by
    rw [clarkeDirectionalDeriv_eq_limsup]
    simpa [l, qv, wholeSpaceClarkePairDomain_eq_positiveTimes]
  obtain ⟨Ku, hqu_upper, hqu_lower⟩ := by
    simpa [l, qu] using eventually_bounded_clarkeQuotient_of_locallyLipschitzAt u x d hu
  obtain ⟨Kv, hqv_upper, hqv_lower⟩ := by
    simpa [l, qv] using eventually_bounded_clarkeQuotient_of_locallyLipschitzAt v x d hv
  have hl_ne : l.NeBot := by
    rw [show l =
        nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d) by
          simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]]
    exact wholeSpaceClarkePairFilter_neBot x d
  letI := hl_ne
  have hqu_bdd : l.IsBoundedUnder (· ≤ ·) qu := ⟨(((Ku : ℝ) * ‖d‖ : ℝ) : EReal), hqu_upper⟩
  have hqu_limsup_ge :
      (((-((Ku : ℝ) * ‖d‖) : ℝ) : EReal) ≤ Filter.limsup qu l) := by
    refine Filter.le_limsup_of_le (f := l) (u := qu)
      (a := (((-((Ku : ℝ) * ‖d‖) : ℝ) : EReal))) (hf := hqu_bdd) ?_
    intro b hb
    rcases hl_ne.nonempty_of_mem (Filter.inter_mem hqu_lower hb) with ⟨p, hp⟩
    exact le_trans hp.1 hp.2
  have hqu_ne_bot : Filter.limsup qu l ≠ ⊥ := by
    exact (lt_of_lt_of_le (EReal.bot_lt_coe (-((Ku : ℝ) * ‖d‖))) hqu_limsup_ge).ne'
  have hqv_bdd : l.IsBoundedUnder (· ≤ ·) qv := ⟨(((Kv : ℝ) * ‖d‖ : ℝ) : EReal), hqv_upper⟩
  have hqv_limsup_ge :
      (((-((Kv : ℝ) * ‖d‖) : ℝ) : EReal) ≤ Filter.limsup qv l) := by
    refine Filter.le_limsup_of_le (f := l) (u := qv)
      (a := (((-((Kv : ℝ) * ‖d‖) : ℝ) : EReal))) (hf := hqv_bdd) ?_
    intro b hb
    rcases hl_ne.nonempty_of_mem (Filter.inter_mem hqv_lower hb) with ⟨p, hp⟩
    exact le_trans hp.1 hp.2
  have hqv_ne_bot : Filter.limsup qv l ≠ ⊥ := by
    exact (lt_of_lt_of_le (EReal.bot_lt_coe (-((Kv : ℝ) * ‖d‖))) hqv_limsup_ge).ne'
  have hsum :
      (fun y ↦ u y + v y)ᵒ(x; d) ≤ uᵒ(x; d) + vᵒ(x; d) := by
    calc
      (fun y ↦ u y + v y)ᵒ(x; d) = Filter.limsup quv l := hquv_limsup.symm
      _ = Filter.limsup (fun p ↦ qu p + qv p) l := by
        exact Filter.limsup_congr hquv_eq
      _ ≤ Filter.limsup qu l + Filter.limsup qv l := by
        exact EReal.limsup_add_le (Or.inl hqu_ne_bot) (Or.inr hqv_ne_bot)
      _ = uᵒ(x; d) + vᵒ(x; d) := by rw [hqu_limsup, hqv_limsup]
  have huv : LocallyLipschitzAt (fun y ↦ u y + v y) x := hu.add hv
  have hsum_real :
      (((clarkeDirectionalDerivReal (fun y ↦ u y + v y) x d : ℝ)) : EReal) ≤
        (((clarkeDirectionalDerivReal u x d + clarkeDirectionalDerivReal v x d : ℝ)) : EReal) := by
    calc
      (((clarkeDirectionalDerivReal (fun y ↦ u y + v y) x d : ℝ)) : EReal)
          = (fun y ↦ u y + v y)ᵒ(x; d) := by
            rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun y ↦ u y + v y) x d huv]
      _ ≤ uᵒ(x; d) + vᵒ(x; d) := hsum
      _ = (((clarkeDirectionalDerivReal u x d : ℝ)) : EReal) +
            (((clarkeDirectionalDerivReal v x d : ℝ)) : EReal) := by
            rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt u x d hu,
              ← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt v x d hv]
      _ = (((clarkeDirectionalDerivReal u x d + clarkeDirectionalDerivReal v x d : ℝ)) : EReal) := by
            norm_num
  exact_mod_cast hsum_real

/-- Helper for Chapter14 Lemma 14.1.4: the real-valued Clarke directional derivative of a finite
sum is bounded by the finite sum of the support values of the summands. -/
lemma clarkeDirectionalDerivReal_finsetSum_le
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x d : E)
    (h_local : ∀ i ∈ s, LocallyLipschitzAt (f i) x) :
    clarkeDirectionalDerivReal (fun y ↦ s.sum fun i ↦ f i y) x d ≤
      s.sum (fun i ↦ clarkeDirectionalDerivReal (f i) x d) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero_local : LocallyLipschitzAt (fun _ : E ↦ (0 : ℝ)) x := by
        refine locallyLipschitzAt_of_closedBall (K := 0) ⟨1, zero_lt_one, ?_⟩
        simpa using (LipschitzWith.const (b := (0 : ℝ))).lipschitzOnWith
      have hzero :
          clarkeDirectionalDerivReal (fun _ : E ↦ (0 : ℝ)) x d = 0 := by
        have hzeroE :
            (((clarkeDirectionalDerivReal (fun _ : E ↦ (0 : ℝ)) x d : ℝ)) : EReal) = 0 := by
          rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun _ : E ↦ (0 : ℝ)) x d
            hzero_local]
          rw [clarkeDirectionalDeriv_eq_limsup]
          let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
          have hl_ne : l.NeBot := by
            rw [show l =
                nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d) by
                  simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]]
            exact wholeSpaceClarkePairFilter_neBot x d
          letI := hl_ne
          simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]
        exact_mod_cast hzeroE
      -- The empty sum is the constant zero function, so its support value vanishes.
      simpa [hzero]
  | @insert i s hi hs =>
      have hi_local : LocallyLipschitzAt (f i) x := h_local i (by simp)
      have hs_local : ∀ j ∈ s, LocallyLipschitzAt (f j) x := by
        intro j hj
        exact h_local j (by simp [hj])
      have htail_local : LocallyLipschitzAt (fun y ↦ s.sum fun j ↦ f j y) x :=
        locallyLipschitzAt_finsetSum s f x hs_local
      have hhead :
          clarkeDirectionalDerivReal
              (fun y ↦ f i y + s.sum (fun j ↦ f j y)) x d ≤
            clarkeDirectionalDerivReal (f i) x d +
              clarkeDirectionalDerivReal (fun y ↦ s.sum fun j ↦ f j y) x d :=
        clarkeDirectionalDerivReal_add_le (f i) (fun y ↦ s.sum fun j ↦ f j y) x d
          hi_local htail_local
      -- Split off the head term and use the induction hypothesis on the tail sum.
      calc
        clarkeDirectionalDerivReal (fun y ↦ (insert i s).sum fun j ↦ f j y) x d
            = clarkeDirectionalDerivReal
                (fun y ↦ f i y + s.sum (fun j ↦ f j y)) x d := by
                  simp [Finset.sum_insert hi]
        _ ≤ clarkeDirectionalDerivReal (f i) x d +
              clarkeDirectionalDerivReal (fun y ↦ s.sum fun j ↦ f j y) x d := hhead
        _ ≤ clarkeDirectionalDerivReal (f i) x d +
              s.sum (fun j ↦ clarkeDirectionalDerivReal (f j) x d) := by
              exact add_le_add le_rfl (hs hs_local)
        _ = (insert i s).sum (fun j ↦ clarkeDirectionalDerivReal (f j) x d) := by
              simp [Finset.sum_insert hi]

/-- Chapter14 Lemma 14.1.4 (5): if each `f i` in a finite family indexed by `s` is Lipschitz
near `x`, then the Clarke differential of the finite sum is contained in the pointwise sum of the
Clarke differentials of the summands. -/
theorem clarkeDifferential_finsetSum_subset
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (h_local : ∀ i ∈ s, LocallyLipschitzAt (f i) x) :
    (∂ᶜ (fun y ↦ s.sum fun i ↦ f i y)) x ⊆
      s.sum (fun i ↦ (∂ᶜ (f i)) x) := by
  classical
  intro ξ hξ
  let S : Set WeakDualSpace := s.sum (fun i ↦ StrongDual.toWeakDual '' (∂ᶜ (f i)) x)
  have hsum_local : LocallyLipschitzAt (fun y ↦ s.sum fun i ↦ f i y) x :=
    locallyLipschitzAt_finsetSum s f x h_local
  have h_conv_sum :
      ∀ t : Finset ι, t ⊆ s →
        Convex ℝ (t.sum (fun i ↦ StrongDual.toWeakDual '' (∂ᶜ (f i)) x)) := by
    intro t hts
    induction t using Finset.induction_on with
    | empty =>
        simpa using (convex_zero : Convex ℝ (0 : Set WeakDualSpace))
    | @insert i t hi ht =>
        have his : i ∈ s := hts (by simp)
        have htts : t ⊆ s := by
          intro j hj
          exact hts (by simp [hj])
        have hi_conv :
            Convex ℝ (StrongDual.toWeakDual '' (∂ᶜ (f i)) x) := by
          simpa using
            (convex_clarkeDifferential_of_locallyLipschitzAt (f i) x (h_local i his)).linear_image
              (StrongDual.toWeakDual.toLinearMap : DualSpace →ₗ[ℝ] WeakDualSpace)
        simpa [Finset.sum_insert hi] using hi_conv.add (ht htts)
  have h_compact_sum :
      ∀ t : Finset ι, t ⊆ s →
        IsCompact (t.sum (fun i ↦ StrongDual.toWeakDual '' (∂ᶜ (f i)) x)) := by
    intro t hts
    induction t using Finset.induction_on with
    | empty =>
        simpa using isCompact_singleton (0 : WeakDualSpace)
    | @insert i t hi ht =>
        have his : i ∈ s := hts (by simp)
        have htts : t ⊆ s := by
          intro j hj
          exact hts (by simp [hj])
        have hi_compact :
            IsCompact (StrongDual.toWeakDual '' (∂ᶜ (f i)) x) :=
          isCompact_toWeakDual_image_clarkeDifferential_of_locallyLipschitzAt
            (f i) x (h_local i his)
        simpa [Finset.sum_insert hi] using (hi_compact.prod (ht htts)).image continuous_add
  have h_conv : Convex ℝ S := by
    simpa [S] using h_conv_sum s (by intro i hi; exact hi)
  have h_compact : IsCompact S := by
    simpa [S] using h_compact_sum s (by intro i hi; exact hi)
  have h_closed : IsClosed S := h_compact.isClosed
  have hξ_image : StrongDual.toWeakDual ξ ∈ S := by
    rw [mem_closed_convex_iff_eval_halfspaces h_conv h_closed]
    intro d
    obtain ⟨η, hηS, hηeval⟩ :=
      exists_mem_toWeakDual_image_finsetSum_clarkeDifferential_eval_eq s f x d h_local
    refine ⟨η, hηS, ?_⟩
    have hξ_support :
        ξ d ≤ clarkeDirectionalDerivReal (fun y ↦ s.sum fun i ↦ f i y) x d := by
      -- The main generalized gradient inequality becomes a real support bound after using
      -- local Lipschitzness of the finite sum.
      have hξE :
          (((ξ d : ℝ)) : EReal) ≤
            (((clarkeDirectionalDerivReal (fun y ↦ s.sum fun i ↦ f i y) x d : ℝ)) : EReal) := by
        simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
          (fun y ↦ s.sum fun i ↦ f i y) x d hsum_local] using
          (mem_clarkeDifferential_iff (fun y ↦ s.sum fun i ↦ f i y) x ξ).1 hξ d
      exact_mod_cast hξE
    calc
      (StrongDual.toWeakDual ξ) d = ξ d := by rfl
      _ ≤ clarkeDirectionalDerivReal (fun y ↦ s.sum fun i ↦ f i y) x d := hξ_support
      _ ≤ s.sum (fun i ↦ clarkeDirectionalDerivReal (f i) x d) := by
          exact clarkeDirectionalDerivReal_finsetSum_le s f x d h_local
      _ = η d := hηeval.symm
  rcases (Set.mem_finsetSum (t := s)
      (f := fun i ↦ StrongDual.toWeakDual '' (∂ᶜ (f i)) x)
      (a := StrongDual.toWeakDual ξ)).1 hξ_image with ⟨η, hηmem, hηsum⟩
  have hpreimage :
      ∀ i ∈ s, ∃ ζ : DualSpace, ζ ∈ (∂ᶜ (f i)) x ∧ StrongDual.toWeakDual ζ = η i := by
    intro i hi
    rcases hηmem hi with ⟨zeta0, hzeta0, hzeta0eq⟩
    exact ⟨zeta0, hzeta0, hzeta0eq⟩
  let zeta : ι → DualSpace :=
    fun i ↦ if hi : i ∈ s then (hpreimage i hi).choose else 0
  have hζmem : ∀ i ∈ s, zeta i ∈ (∂ᶜ (f i)) x := by
    intro i hi
    dsimp [zeta]
    simp [hi, (hpreimage i hi).choose_spec.1]
  have hζeq : ∀ i ∈ s, StrongDual.toWeakDual (zeta i) = η i := by
    intro i hi
    dsimp [zeta]
    simp [hi, (hpreimage i hi).choose_spec.2]
  have hζsum :
      StrongDual.toWeakDual (∑ i ∈ s, zeta i) = StrongDual.toWeakDual ξ := by
    -- Sum the chosen strong-dual witnesses and compare after applying the weak-dual embedding.
    calc
      StrongDual.toWeakDual (∑ i ∈ s, zeta i)
          = ∑ i ∈ s, StrongDual.toWeakDual (zeta i) := by
              change
                (StrongDual.toWeakDual.toLinearMap : DualSpace →ₗ[ℝ] WeakDualSpace)
                    (∑ i ∈ s, zeta i) =
                  ∑ i ∈ s,
                    (StrongDual.toWeakDual.toLinearMap : DualSpace →ₗ[ℝ] WeakDualSpace) (zeta i)
              rw [map_sum]
      _ = ∑ i ∈ s, η i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hζeq i hi
      _ = StrongDual.toWeakDual ξ := hηsum
  have hsum_eq : ∑ i ∈ s, zeta i = ξ := (StrongDual.toWeakDual_inj _ _).1 hζsum
  -- Pull the weak-dual decomposition back through the injective embedding.
  refine hsum_eq ▸ Set.finsetSum_mem_finsetSum s
    (fun i ↦ (∂ᶜ (f i)) x) zeta ?_
  intro i hi
  exact hζmem i hi

section ChainRule

variable {n : ℕ}

local notation "Codomain" => EuclideanSpace ℝ (Fin n)
local notation "CodomainDual" => StrongDual ℝ Codomain

/-- Helper for Chapter14 Lemma 14.1.4: the chain-rule generator set consists of the weak-* images
of sums `∑ i, α_i • ξ_i` with `α ∈ ∂ᶜ g(h x)` and `ξ_i ∈ ∂ᶜ h_i(x)`. -/
def chainRuleGeneratorSet (g : Codomain → ℝ) (h : E → Codomain) (x : E) : Set WeakDualSpace :=
  ((fun p : CodomainDual × (Fin n → DualSpace) ↦
      (StrongDual.toWeakDual
        (∑ i : Fin n, (p.1 (EuclideanSpace.single i (1 : ℝ))) • p.2 i) :
          WeakDualSpace)) ''
    {p : CodomainDual × (Fin n → DualSpace) |
      p.1 ∈ (∂ᶜ g) (h x) ∧
        ∀ i : Fin n, p.2 i ∈ (∂ᶜ (fun y ↦ h y i)) x})

/-- Helper for Chapter14 Lemma 14.1.4: a codomain dual element evaluates on Euclidean space by
summing its coefficients on the standard basis. -/
lemma codomainDual_apply_eq_sum_single_coeff
    (α : CodomainDual) (v : Codomain) :
    α v = ∑ i : Fin n, (α (EuclideanSpace.single i (1 : ℝ))) * v i := by
  -- Expand `v` in the standard Euclidean basis before evaluating the linear functional `α`.
  calc
    α v = α (∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ)) := by
      rw [show (∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ)) = v by
        simpa [EuclideanSpace.basisFun_apply] using
          (OrthonormalBasis.sum_repr (b := EuclideanSpace.basisFun (Fin n) ℝ) v)]
    _ = ∑ i : Fin n, α (v i • EuclideanSpace.single i (1 : ℝ)) := by
      rw [map_sum]
    _ = ∑ i : Fin n, (α (EuclideanSpace.single i (1 : ℝ))) * v i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [map_smul]
      ring

/-- Helper for Chapter14 Lemma 14.1.4: the componentwise Clarke support values of `h` at `(x, d)`
assembled as a Euclidean vector. -/
def componentClarkeVector (h : E → Codomain) (x d : E) : Codomain :=
  ∑ i : Fin n, clarkeDirectionalDerivReal (fun y ↦ h y i) x d • EuclideanSpace.single i (1 : ℝ)

/-- Helper for Chapter14 Lemma 14.1.4: the `i`-th coordinate of the component Clarke vector is the
Clarke directional derivative of the `i`-th component. -/
@[simp] lemma componentClarkeVector_apply
    (h : E → Codomain) (x d : E) (i : Fin n) :
    componentClarkeVector h x d i =
      clarkeDirectionalDerivReal (fun y ↦ h y i) x d := by
  -- Read the standard-basis expansion coordinatewise.
  let c : Fin n → ℝ := fun j ↦ clarkeDirectionalDerivReal (fun y ↦ h y j) x d
  have hsum : ∑ j : Fin n, c j • Pi.single j (1 : ℝ) = c := by
    simpa using (Module.Basis.sum_repr (b := Pi.basisFun ℝ (Fin n)) c)
  have hi' := congrArg (fun u : Fin n → ℝ ↦ u i) hsum
  simpa [c, componentClarkeVector, PiLp.ofLp_single] using hi'

/-- Helper for Chapter14 Lemma 14.1.4: coordinatewise Lipschitz control on a set gives a single
Euclidean-valued Lipschitz bound with constant `∑ i, K i`. -/
lemma lipschitzOnWith_euclidean_of_components
    {s : Set E} (h : E → Codomain) (K : Fin n → NNReal)
    (hK : ∀ i : Fin n, LipschitzOnWith (K i) (fun y ↦ h y i) s) :
    LipschitzOnWith (∑ i, K i) h s := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro y hy z hz
  have hcoord : ∀ i : Fin n, dist (h y i) (h z i) ≤ (K i : ℝ) * dist y z := by
    intro i
    exact (hK i).dist_le_mul y hy z hz
  have hsq :
      ∑ i : Fin n, dist (h y i) (h z i) ^ 2 ≤
        (((∑ i : Fin n, (K i : ℝ)) * dist y z) ^ 2) := by
    have hsq_coord :
        ∑ i : Fin n, dist (h y i) (h z i) ^ 2 ≤
          ∑ i : Fin n, (((K i : ℝ) * dist y z) ^ 2) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hleft_nonneg : 0 ≤ dist (h y i) (h z i) := dist_nonneg
      have hright_nonneg : 0 ≤ (K i : ℝ) * dist y z := by positivity
      nlinarith [hcoord i, hleft_nonneg, hright_nonneg]
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (K i : ℝ) * dist y z := by
      intro i _
      positivity
    have hsq_sum :
        ∑ i : Fin n, (((K i : ℝ) * dist y z) ^ 2) ≤
          (∑ i : Fin n, (K i : ℝ) * dist y z) ^ 2 := by
      simpa using
        (Finset.sum_sq_le_sq_sum_of_nonneg
          (s := Finset.univ) (f := fun i : Fin n ↦ (K i : ℝ) * dist y z) hnonneg)
    calc
      ∑ i : Fin n, dist (h y i) (h z i) ^ 2
          ≤ ∑ i : Fin n, (((K i : ℝ) * dist y z) ^ 2) := hsq_coord
      _ ≤ (∑ i : Fin n, (K i : ℝ) * dist y z) ^ 2 := hsq_sum
      _ = (((∑ i : Fin n, (K i : ℝ)) * dist y z) ^ 2) := by
        rw [Finset.sum_mul]
  rw [EuclideanSpace.dist_eq]
  have hnonneg_rhs : 0 ≤ ((↑(∑ i : Fin n, K i) : ℝ) * dist y z) := by
    positivity
  have hsq' :
      ∑ i : Fin n, dist (h y i) (h z i) ^ 2 ≤
        (↑(∑ i : Fin n, K i) * dist y z) ^ 2 := by
    simpa [NNReal.coe_sum] using hsq
  -- Compare the Euclidean distance to the square of the summed coordinatewise bound.
  exact Real.sqrt_le_iff.mpr ⟨hnonneg_rhs, hsq'⟩

/-- Helper for Chapter14 Lemma 14.1.4: finitely many locally Lipschitz coordinate maps assemble
to a locally Lipschitz map into Euclidean space. -/
lemma locallyLipschitzAt_euclidean_of_components
    (h : E → Codomain) (x : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x) :
    LocallyLipschitzAt h x := by
  classical
  by_cases hne : Nonempty (Fin n)
  · letI := hne
    have hdata :
        ∀ i : Fin n,
          ∃ ε : ℝ, 0 < ε ∧ ∃ K : NNReal,
            LipschitzOnWith K (fun y ↦ h y i) (Metric.closedBall x ε) := by
      intro i
      exact locallyLipschitzAt_iff.mp (h_local_h i)
    choose ε hε K hK using hdata
    let ε0 : ℝ := Finset.univ.inf' Finset.univ_nonempty ε
    have hε0 : 0 < ε0 := (Finset.lt_inf'_iff _).2 fun i _ ↦ hε i
    refine locallyLipschitzAt_of_closedBall (K := ∑ i, K i) ⟨ε0, hε0, ?_⟩
    have hK' :
        ∀ i : Fin n,
          LipschitzOnWith (K i) (fun y ↦ h y i) (Metric.closedBall x ε0) := by
      intro i
      exact (hK i).mono <|
        Metric.closedBall_subset_closedBall (Finset.inf'_le _ <| Finset.mem_univ i)
    -- Use the coordinatewise estimate on the common closed ball.
    simpa [ε0] using lipschitzOnWith_euclidean_of_components h K hK'
  · letI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
    have hconst : ∀ y : E, h y = h x := by
      intro y
      exact Subsingleton.elim _ _
    refine locallyLipschitzAt_of_closedBall (K := 0) ⟨1, zero_lt_one, ?_⟩
    -- In the zero-dimensional case the Euclidean-valued map is constant.
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro y hy z hz
    simp [hconst y, hconst z]

/-- Chapter14 Lemma 14.1.4 (6): if every component of `h : E → ℝ^n` is Lipschitz near `x` and
`g : ℝ^n → ℝ` is Lipschitz near `h x`, then the composite `g ∘ h` is Lipschitz near `x`. -/
theorem locallyLipschitzAt_comp_of_components
    (g : Codomain → ℝ) (h : E → Codomain) (x : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x)
    (h_local_g : LocallyLipschitzAt g (h x)) :
    LocallyLipschitzAt (fun y ↦ g (h y)) x := by
  rcases locallyLipschitzAt_iff.mp (locallyLipschitzAt_euclidean_of_components h x h_local_h) with
    ⟨εh, hεh, Kh, hKh⟩
  rcases locallyLipschitzAt_iff.mp h_local_g with ⟨εg, hεg, Kg, hKg⟩
  obtain ⟨gExt, hgExt, hgEq⟩ := hKg.extend_real
  let δ : ℝ := min εh (εg / ((Kh : ℝ) + 1))
  have hδ : 0 < δ := by
    refine lt_min hεh ?_
    positivity
  refine locallyLipschitzAt_of_closedBall (K := Kg * Kh) ⟨δ, hδ, ?_⟩
  have hKhδ : LipschitzOnWith Kh h (Metric.closedBall x δ) :=
    hKh.mono <| Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hMaps :
      Set.MapsTo h (Metric.closedBall x δ) (Metric.closedBall (h x) εg) := by
    intro y hy
    have hy_dist : dist y x ≤ δ := Metric.mem_closedBall.mp hy
    have hx_mem : x ∈ Metric.closedBall x δ := Metric.mem_closedBall_self hδ.le
    have hdist_h : dist (h y) (h x) ≤ (Kh : ℝ) * dist y x := (hKhδ.dist_le_mul y hy x hx_mem)
    have hKhδ_le : (Kh : ℝ) * dist y x ≤ εg := by
      calc
        (Kh : ℝ) * dist y x ≤ (Kh : ℝ) * δ := by
          gcongr
        _ ≤ (Kh : ℝ) * (εg / ((Kh : ℝ) + 1)) := by
          gcongr
          exact min_le_right _ _
        _ ≤ εg := by
          have hden : 0 < (Kh : ℝ) + 1 := by positivity
          have hdiv_le_one : (Kh : ℝ) / ((Kh : ℝ) + 1) ≤ 1 :=
            (div_le_one hden).2 <| by nlinarith
          calc
            (Kh : ℝ) * (εg / ((Kh : ℝ) + 1))
                = εg * ((Kh : ℝ) / ((Kh : ℝ) + 1)) := by ring
            _ ≤ εg * 1 := by
              gcongr
            _ = εg := by ring
    exact Metric.mem_closedBall.mpr (hdist_h.trans hKhδ_le)
  have hCompExt : LipschitzOnWith (Kg * Kh) (gExt ∘ h) (Metric.closedBall x δ) :=
    hgExt.comp_lipschitzOnWith hKhδ
  -- Replace the extension by `g` on the image of the small ball.
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro y hy z hz
  have hyEq : gExt (h y) = g (h y) := (hgEq (hMaps hy)).symm
  have hzEq : gExt (h z) = g (h z) := (hgEq (hMaps hz)).symm
  simpa [Function.comp, hyEq, hzEq] using hCompExt.dist_le_mul y hy z hz

/-- Helper for Chapter14 Lemma 14.1.4: every direction `d` admits a generator whose evaluation at
`d` realizes the outer Clarke support value on the vector of componentwise support values. -/
lemma exists_mem_chainRule_generator_eval_eq
    (g : Codomain → ℝ) (h : E → Codomain) (x d : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x)
    (h_local_g : LocallyLipschitzAt g (h x)) :
    ∃ η ∈ chainRuleGeneratorSet g h x,
      η d = clarkeDirectionalDerivReal g (h x)
        (componentClarkeVector h x d) := by
  classical
  let v : Codomain := componentClarkeVector h x d
  obtain ⟨α, hαmem, hαeval⟩ :=
    (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
      g (h x) v h_local_g).1
  have hcoord :
      ∀ i : Fin n,
        ∃ ξ : DualSpace,
          ξ ∈ (∂ᶜ (fun y ↦ h y i)) x ∧
            ξ d = clarkeDirectionalDerivReal (fun y ↦ h y i) x d := by
    intro i
    exact
      (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
        (fun y ↦ h y i) x d (h_local_h i)).1
  choose ξ hξmem hξeval using hcoord
  refine ⟨StrongDual.toWeakDual (∑ i : Fin n, (α (EuclideanSpace.single i (1 : ℝ))) • ξ i), ?_, ?_⟩
  · -- Package the maximizing outer subgradient and the maximizing coordinate subgradients into
    -- one point of the displayed generator image.
    refine ⟨(α, ξ), ?_, rfl⟩
    exact ⟨hαmem, hξmem⟩
  · -- Evaluate the packaged witness in direction `d` and rewrite it as the outer support value.
    calc
      (StrongDual.toWeakDual (∑ i : Fin n, (α (EuclideanSpace.single i (1 : ℝ))) • ξ i)) d
          = (∑ i : Fin n, (α (EuclideanSpace.single i (1 : ℝ))) • ξ i) d := by
              rfl
      _ = ∑ i : Fin n,
            ((α (EuclideanSpace.single i (1 : ℝ))) • ξ i) d := by
            let ev : DualSpace →ₗ[ℝ] ℝ :=
              { toFun := fun ζ ↦ ζ d
                map_add' := by intro ζ₁ ζ₂; rfl
                map_smul' := by intro a ζ; rfl }
            change ev (∑ i : Fin n, (α (EuclideanSpace.single i (1 : ℝ))) • ξ i) =
              ∑ i : Fin n, ev ((α (EuclideanSpace.single i (1 : ℝ))) • ξ i)
            rw [map_sum]
      _ = ∑ i : Fin n,
            (α (EuclideanSpace.single i (1 : ℝ))) *
              clarkeDirectionalDerivReal (fun y ↦ h y i) x d := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hξeval i]
      _ = α v := by
            symm
            simpa [v] using codomainDual_apply_eq_sum_single_coeff (n := n) α v
      _ = clarkeDirectionalDerivReal g (h x) v := hαeval

/-- Helper for Chapter14 Lemma 14.1.4: the exact componentwise quotient vector of `h` along the
nearby pair `p = (y, t)` in direction `d`. -/
def exactComponentQuotientVector (h : E → Codomain) (d : E) (p : E × ℝ) : Codomain :=
  ∑ i : Fin n,
    (((h (p.1 + p.2 • d) i - h p.1 i) / p.2) : ℝ) • EuclideanSpace.single i (1 : ℝ)

/-- Helper for Chapter14 Lemma 14.1.4: the `i`-th coordinate of the exact quotient vector is the
corresponding scalar difference quotient. -/
@[simp] lemma exactComponentQuotientVector_apply
    (h : E → Codomain) (d : E) (p : E × ℝ) (i : Fin n) :
    exactComponentQuotientVector h d p i =
      (h (p.1 + p.2 • d) i - h p.1 i) / p.2 := by
  let c : Fin n → ℝ := fun j ↦ (h (p.1 + p.2 • d) j - h p.1 j) / p.2
  have hsum : ∑ j : Fin n, c j • Pi.single j (1 : ℝ) = c := by
    simpa using (Module.Basis.sum_repr (b := Pi.basisFun ℝ (Fin n)) c)
  have hi' := congrArg (fun u : Fin n → ℝ ↦ u i) hsum
  simpa [c, exactComponentQuotientVector, PiLp.ofLp_single] using hi'

/-- Helper for Chapter14 Lemma 14.1.4: negating `h` negates each exact component quotient. -/
@[simp] lemma exactComponentQuotientVector_neg_apply
    (h : E → Codomain) (d : E) (p : E × ℝ) (i : Fin n) :
    exactComponentQuotientVector (fun y ↦ -h y) d p i =
      -exactComponentQuotientVector h d p i := by
  simp [exactComponentQuotientVector_apply]
  ring

/-- Helper for Chapter14 Lemma 14.1.4: along any nearby positive-time sequence converging to
`(x, 0)`, a strict upper real cutoff for one component Clarke derivative forces the matching exact
component quotients below the same cutoff eventually. -/
lemma component_exactQuotient_eventually_le_of_lt_bound
    (h : E → Codomain) (x d : E) (i : Fin n)
    (h_local_i : LocallyLipschitzAt (fun y ↦ h y i) x)
    {y : ℕ → E} {t : ℕ → ℝ} {b : ℝ}
    (hy : Filter.Tendsto y Filter.atTop (nhds x))
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (ht_pos : ∀ k : ℕ, 0 < t k)
    (hb : clarkeDirectionalDerivReal (fun z ↦ h z i) x d < b) :
    ∀ᶠ k in Filter.atTop,
      exactComponentQuotientVector h d (y k, t k) i ≤ b := by
  have hbE : (fun z ↦ h z i)ᵒ(x; d) < ((b : ℝ) : EReal) := by
    -- Rewrite the scalar Clarke derivative cutoff into the canonical `EReal` form expected by
    -- the closed-ball quotient lemma.
    rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun z ↦ h z i) x d h_local_i]
    exact_mod_cast hb
  obtain ⟨ρ, hρ, hρbound⟩ :=
    clarkeQuotient_eventually_le_of_lt_bound (f := fun z ↦ h z i) (x := x) (d := d) hbE
  have hpair :
      Filter.Tendsto (fun k : ℕ ↦ ((y k : E), (t k : ℝ))) Filter.atTop
        (nhds ((x : E), (0 : ℝ))) := by
    -- The pair sequence converges to the source Clarke base point `(x, 0)`.
    simpa using Filter.Tendsto.prodMk_nhds hy ht
  have hball :
      ∀ᶠ k in Filter.atTop,
        (y k, t k) ∈ Metric.closedBall ((x : E), (0 : ℝ)) ρ :=
    hpair.eventually <| Metric.closedBall_mem_nhds ((x : E), (0 : ℝ)) hρ
  filter_upwards [hball] with k hk
  have hkE := hρbound hk (ht_pos k)
  -- The closed-ball cutoff lemma already returns the desired scalar bound.
  simpa using hkE

/-- Helper for Chapter14 Lemma 14.1.4: any cluster point of exact componentwise quotient vectors
inherits the signed component support bounds required by the chain-rule generator lemma. -/
lemma cluster_exactComponentQuotientVector_has_signed_component_bounds
    (h : E → Codomain) (x d : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x)
    {y : ℕ → E} {t : ℕ → ℝ} {a : Codomain}
    (hy : Filter.Tendsto y Filter.atTop (nhds x))
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (ht_pos : ∀ k : ℕ, 0 < t k)
    (ha : Filter.Tendsto (fun k ↦ exactComponentQuotientVector h d (y k, t k))
      Filter.atTop (nhds a)) :
    (∀ i : Fin n, a i ≤ clarkeDirectionalDerivReal (fun z ↦ h z i) x d) ∧
      (∀ i : Fin n, -a i ≤ clarkeDirectionalDerivReal (fun z ↦ -h z i) x d) := by
  constructor
  · intro i
    by_contra hai
    obtain ⟨b, hb_left, hb_right⟩ := exists_between (lt_of_not_ge hai)
    have hcoord_tendsto_raw :
        Filter.Tendsto
          (((fun x : Codomain ↦ x.ofLp i) : Codomain → ℝ) ∘
            fun k ↦ exactComponentQuotientVector h d (y k, t k))
          Filter.atTop (nhds (a.ofLp i)) := by
      -- Project the Euclidean-valued cluster-point convergence onto coordinate `i`.
      exact (((EuclideanSpace.proj i : Codomain →L[ℝ] ℝ).continuous.tendsto a).comp ha)
    have hcoord_gt :
        ∀ᶠ k in Filter.atTop, b < (exactComponentQuotientVector h d (y k, t k)).ofLp i :=
      hcoord_tendsto_raw.eventually <| Ioi_mem_nhds hb_right
    have hcoord_le :
        ∀ᶠ k in Filter.atTop, (exactComponentQuotientVector h d (y k, t k)).ofLp i ≤ b := by
      simpa using
        (component_exactQuotient_eventually_le_of_lt_bound
          h x d i (h_local_h i) hy ht ht_pos hb_left)
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hcoord_gt
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hcoord_le
    have hbad :=
      And.intro (hN₁ (max N₁ N₂) <| le_max_left _ _) (hN₂ (max N₁ N₂) <| le_max_right _ _)
    linarith
  · intro i
    by_contra hai
    obtain ⟨b, hb_left, hb_right⟩ := exists_between (lt_of_not_ge hai)
    have hcoord_base :
        Filter.Tendsto
          (((fun x : Codomain ↦ x.ofLp i) : Codomain → ℝ) ∘
            fun k ↦ exactComponentQuotientVector h d (y k, t k))
          Filter.atTop (nhds (a.ofLp i)) := by
      -- Project the Euclidean-valued cluster-point convergence onto coordinate `i`.
      exact (((EuclideanSpace.proj i : Codomain →L[ℝ] ℝ).continuous.tendsto a).comp ha)
    have hcoord_tendsto :
        Filter.Tendsto
          (fun k ↦ -((exactComponentQuotientVector h d (y k, t k)).ofLp i))
          Filter.atTop (nhds (-a.ofLp i)) := by
      -- Negate the projected coordinate limit so the lower bound becomes another upper cutoff.
      simpa using hcoord_base.neg
    have hcoord_gt :
        ∀ᶠ k in Filter.atTop, b < -((exactComponentQuotientVector h d (y k, t k)).ofLp i) :=
      hcoord_tendsto.eventually <| Ioi_mem_nhds hb_right
    have hcoord_le_raw :
        ∀ᶠ k in Filter.atTop,
          exactComponentQuotientVector (fun y ↦ -h y) d (y k, t k) i ≤ b :=
      component_exactQuotient_eventually_le_of_lt_bound
        (fun y ↦ -h y) x d i
        (by simpa using (h_local_h i).neg)
        hy ht ht_pos hb_left
    have hcoord_le :
        ∀ᶠ k in Filter.atTop, -((exactComponentQuotientVector h d (y k, t k)).ofLp i) ≤ b := by
      -- Rewrite the negated-component quotient back to the original `h` sequence.
      filter_upwards [hcoord_le_raw] with k hk
      have hnegquot :
          (-(h (y k + t k • d) i) + h (y k) i) / t k =
            -(((h (y k + t k • d) i - h (y k) i) / t k : ℝ)) := by
        ring
      simpa [exactComponentQuotientVector_apply, hnegquot] using hk
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hcoord_gt
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hcoord_le
    have hbad :=
      And.intro (hN₁ (max N₁ N₂) <| le_max_left _ _) (hN₂ (max N₁ N₂) <| le_max_right _ _)
    linarith

/-- Helper for Chapter14 Lemma 14.1.4: exact componentwise quotient vectors coming from one
small positive-time product ball stay in a fixed closed ball of the Euclidean codomain. -/
lemma exactComponentQuotientVector_bounded_of_nearby_pairs
    (h : E → Codomain) (x d : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x) :
    ∃ ρ > 0, ∃ R > 0, ∀ {p : E × ℝ},
      p ∈ Metric.closedBall ((x : E), (0 : ℝ)) ρ →
      0 < p.2 →
      exactComponentQuotientVector h d p ∈ Metric.closedBall (0 : Codomain) R := by
  rcases locallyLipschitzAt_iff.mp (locallyLipschitzAt_euclidean_of_components h x h_local_h) with
    ⟨ε, hε, K, hK⟩
  obtain ⟨ρ, hρ, hgeom⟩ :=
    clarkeWitness_points_mem_closedBall_of_nearby_pair (x := x) (d := d) hε
  refine ⟨ρ, hρ, (K : ℝ) * ‖d‖ + 1, by positivity, ?_⟩
  intro p hp hp_pos
  rcases hgeom (x' := x) (d' := d) (Metric.mem_closedBall_self hρ.le) hp hp_pos with
    ⟨hp_mem, hpd_mem, _⟩
  have hp_ne : p.2 ≠ 0 := ne_of_gt hp_pos
  have hrepr :
      exactComponentQuotientVector h d p =
        (1 / p.2 : ℝ) • (h (p.1 + p.2 • d) - h p.1) := by
    -- Rewrite the exact quotient vector as one scalar multiple of the codomain difference.
    ext i
    simp [exactComponentQuotientVector_apply, hp_ne]
    field_simp [hp_ne]
  have hmove : dist (p.1 + p.2 • d) p.1 = p.2 * ‖d‖ := by
    -- The displacement from `p.1` to the endpoint in direction `d` has the expected size.
    calc
      dist (p.1 + p.2 • d) p.1 = ‖(p.1 + p.2 • d) - p.1‖ := by rw [dist_eq_norm]
      _ = ‖p.2 • d‖ := by simp
      _ = p.2 * ‖d‖ := by rw [norm_smul, Real.norm_of_nonneg hp_pos.le]
  have hnorm :
      ‖exactComponentQuotientVector h d p‖ ≤ (K : ℝ) * ‖d‖ := by
    -- Divide the Lipschitz estimate for `h` by the positive time step `p.2`.
    calc
      ‖exactComponentQuotientVector h d p‖
          = ‖(1 / p.2 : ℝ) • (h (p.1 + p.2 • d) - h p.1)‖ := by
              rw [hrepr]
      _ = |1 / p.2| * ‖h (p.1 + p.2 • d) - h p.1‖ := norm_smul _ _
      _ = (1 / p.2 : ℝ) * ‖h (p.1 + p.2 • d) - h p.1‖ := by
            have h_inv_nonneg : 0 ≤ (1 / p.2 : ℝ) := by positivity
            rw [abs_of_nonneg h_inv_nonneg]
      _ = (1 / p.2 : ℝ) * dist (h (p.1 + p.2 • d)) (h p.1) := by
            rw [dist_eq_norm]
      _ ≤ (1 / p.2 : ℝ) * ((K : ℝ) * dist (p.1 + p.2 • d) p.1) := by
            exact mul_le_mul_of_nonneg_left
              (hK.dist_le_mul (p.1 + p.2 • d) hpd_mem p.1 hp_mem) (by positivity)
      _ = (1 / p.2 : ℝ) * ((K : ℝ) * (p.2 * ‖d‖)) := by rw [hmove]
      _ = (K : ℝ) * ‖d‖ := by
            field_simp [hp_ne]
  have hnorm_closed :
      ‖exactComponentQuotientVector h d p‖ ≤ (K : ℝ) * ‖d‖ + 1 := by
    linarith
  -- The norm bound is exactly the closed-ball membership needed for compactness later.
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_closed

/-- Helper for Chapter14 Lemma 14.1.4: the composite quotient can be rewritten exactly as the
outer quotient for `g` in the direction of the exact componentwise quotient vector. -/
lemma composite_quotient_eq_outer_exactComponentQuotient
    (g : Codomain → ℝ) (h : E → Codomain) (d : E) (p : E × ℝ)
    (hp : 0 < p.2) :
    ((g (h (p.1 + p.2 • d)) - g (h p.1)) / p.2 : ℝ) =
      ((g (h p.1 + p.2 • exactComponentQuotientVector h d p) - g (h p.1)) / p.2 : ℝ) := by
  have hp_ne : p.2 ≠ 0 := ne_of_gt hp
  have hvector :
      h p.1 + p.2 • exactComponentQuotientVector h d p = h (p.1 + p.2 • d) := by
    -- Compare the two codomain vectors coordinatewise and clear the scalar denominator.
    ext i
    simp [exactComponentQuotientVector_apply, hp_ne]
    field_simp [hp_ne]
    ring
  -- Once the codomain vectors agree, the two real difference quotients are identical.
  rw [hvector]

/-- Helper for Chapter14 Lemma 14.1.4: a strict real cutoff above the frozen outer Clarke support
at `(x0, a)` eventually bounds the actual nearby outer quotients of `g` along any nearby
base-direction sequence. -/
lemma outer_quotient_eventually_le_of_lt_bound
    (g : Codomain → ℝ) (x0 a : Codomain)
    {u q : ℕ → Codomain} {t : ℕ → ℝ} {b : ℝ}
    (h_local : LocallyLipschitzAt g x0)
    (hu : Filter.Tendsto u Filter.atTop (nhds x0))
    (hq : Filter.Tendsto q Filter.atTop (nhds a))
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (ht_pos : ∀ k : ℕ, 0 < t k)
    (hb : clarkeDirectionalDerivReal g x0 a < b) :
    ∀ᶠ k in Filter.atTop,
      ((g (u k + t k • q k) - g (u k)) / t k : ℝ) ≤ b := by
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  have hbE : gᵒ(x0; a) < ((b : ℝ) : EReal) := by
    rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt g x0 a h_local]
    exact_mod_cast hb
  obtain ⟨c, hc_left, hc_right⟩ := EReal.lt_iff_exists_real_btwn.mp hbE
  obtain ⟨ρq, hρq, hρq_bound⟩ :=
    clarkeQuotient_eventually_le_of_lt_bound (f := g) (x := x0) (d := a) hc_left
  obtain ⟨ρg, hρg, hgeom⟩ :=
    clarkeWitness_points_mem_closedBall_of_nearby_pair (x := x0) (d := a) hε
  have hcb : c < b := by
    exact_mod_cast hc_right
  let ρe : ℝ := (b - c) / ((K : ℝ) + 1)
  have hρe_pos : 0 < ρe := by
    dsimp [ρe]
    exact div_pos (sub_pos.mpr hcb) (by positivity)
  let ρ : ℝ := min ρg (min (ρq / 2) ρe)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρg (lt_min (by linarith) hρe_pos)
  have hρ_le_g : ρ ≤ ρg := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_half : ρ ≤ ρq / 2 := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_e : ρ ≤ ρe := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hpair :
      Filter.Tendsto (fun k : ℕ ↦ ((u k : Codomain), (q k : Codomain)))
        Filter.atTop (nhds (x0, a)) := by
    simpa using Filter.Tendsto.prodMk_nhds hu hq
  have hpair_ball :
      ∀ᶠ k in Filter.atTop, (u k, q k) ∈ Metric.closedBall (x0, a) ρ :=
    hpair.eventually <| Metric.closedBall_mem_nhds (x0, a) hρ_pos
  have ht_ball :
      ∀ᶠ k in Filter.atTop, t k ∈ Metric.closedBall (0 : ℝ) ρ :=
    ht.eventually <| Metric.closedBall_mem_nhds 0 hρ_pos
  filter_upwards [hpair_ball, ht_ball] with k hk_pair hk_t
  have hx_pair : dist (u k) x0 ≤ ρ ∧ dist (q k) a ≤ ρ := by
    simpa [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] using hk_pair
  have ht_dist : dist (t k) 0 ≤ ρ := by
    simpa [Metric.mem_closedBall] using hk_t
  have hx'd'_g : (u k, q k) ∈ Metric.closedBall (x0, a) ρg := by
    have hk_pair' : dist (u k, q k) (x0, a) ≤ ρ := by
      simpa [Metric.mem_closedBall] using hk_pair
    simpa [Metric.mem_closedBall] using le_trans hk_pair' hρ_le_g
  have hp_ball_g : (u k, t k) ∈ Metric.closedBall ((u k : Codomain), (0 : ℝ)) ρg := by
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
    constructor
    · simpa using hρg.le
    · exact le_trans ht_dist hρ_le_g
  obtain ⟨hu_mem, hua_mem, huq_mem⟩ := hgeom hx'd'_g hp_ball_g (ht_pos k)
  have hp_fixed : (u k, t k) ∈ Metric.closedBall ((x0 : Codomain), (0 : ℝ)) ρq := by
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
    constructor
    · calc
        dist (u k) x0 ≤ ρ := hx_pair.1
        _ ≤ ρq / 2 := hρ_le_half
        _ ≤ ρq := by linarith
    · calc
        dist (t k) 0 ≤ ρ := ht_dist
        _ ≤ ρq / 2 := hρ_le_half
        _ ≤ ρq := by linarith
  have hcompare :=
    clarkeQuotient_le_add_norm_sub_of_closedBallLipschitz
      (f := g) (x := x0) (y := u k) (d := a) (d' := q k) (t := t k) (eps := ε)
      (ht_pos k) K hK hu_mem hua_mem huq_mem
  have hfixed_le :
      (((g (u k + t k • a) - g (u k)) / t k : ℝ) : EReal) ≤ c :=
    hρq_bound hp_fixed (ht_pos k)
  have hρe_eq : ((K : ℝ) + 1) * ρe = b - c := by
    have hden_ne : ((K : ℝ) + 1) ≠ 0 := by positivity
    dsimp [ρe]
    field_simp [hden_ne]
  have herror :
      (K : ℝ) * ‖q k - a‖ < b - c := by
    calc
      (K : ℝ) * ‖q k - a‖ = (K : ℝ) * dist (q k) a := by
        rw [dist_eq_norm]
      _ ≤ (K : ℝ) * ρ := by
        exact mul_le_mul_of_nonneg_left hx_pair.2 K.2
      _ ≤ (K : ℝ) * ρe := by
        exact mul_le_mul_of_nonneg_left hρ_le_e K.2
      _ < ((K : ℝ) + 1) * ρe := by
        exact mul_lt_mul_of_pos_right (by linarith) hρe_pos
      _ = b - c := hρe_eq
  have hmidE :
      (((g (u k + t k • q k) - g (u k)) / t k : ℝ) : EReal) ≤
        (((c + (K : ℝ) * ‖q k - a‖ : ℝ)) : EReal) := by
    calc
      (((g (u k + t k • q k) - g (u k)) / t k : ℝ) : EReal)
          ≤ (((g (u k + t k • a) - g (u k)) / t k : ℝ) : EReal) +
              ((((K : ℝ) * ‖q k - a‖ : ℝ)) : EReal) := by
            simpa using hcompare
      _ ≤ (c : EReal) + ((((K : ℝ) * ‖q k - a‖ : ℝ)) : EReal) := by
            exact add_le_add hfixed_le le_rfl
      _ = (((c + (K : ℝ) * ‖q k - a‖ : ℝ)) : EReal) := by
            simp
  have hmid :
      ((g (u k + t k • q k) - g (u k)) / t k : ℝ) ≤
        c + (K : ℝ) * ‖q k - a‖ := by
    exact_mod_cast hmidE
  have hsum_lt : c + (K : ℝ) * ‖q k - a‖ < b := by
    linarith
  -- Compare the nearby quotient to the frozen `a`-quotient, then absorb the perturbation margin.
  exact le_of_lt (lt_of_le_of_lt hmid hsum_lt)

/-- Helper for Chapter14 Lemma 14.1.4: the limsup of nearby outer quotients is bounded by the
frozen outer Clarke support once the base points, directions, and times converge to
`(x0, a, 0)`. -/
lemma limsup_outer_quotient_le_clarkeDirectionalDerivReal
    (g : Codomain → ℝ) (x0 a : Codomain)
    {u q : ℕ → Codomain} {t : ℕ → ℝ}
    (h_local : LocallyLipschitzAt g x0)
    (hu : Filter.Tendsto u Filter.atTop (nhds x0))
    (hq : Filter.Tendsto q Filter.atTop (nhds a))
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (ht_pos : ∀ k : ℕ, 0 < t k) :
    Filter.limsup
        (fun k ↦ ((((g (u k + t k • q k) - g (u k)) / t k : ℝ)) : EReal))
        Filter.atTop ≤ (((clarkeDirectionalDerivReal g x0 a : ℝ)) : EReal) := by
  let s : ℕ → EReal :=
    fun k ↦ ((((g (u k + t k • q k) - g (u k)) / t k : ℝ)) : EReal)
  have hs_cobdd :
      Filter.atTop.IsCoboundedUnder (· ≤ ·) s :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop (x := (⊥ : EReal)) fun _ ↦ by
      simp [s]
  by_contra hlt
  have hlt' :
      (((clarkeDirectionalDerivReal g x0 a : ℝ)) : EReal) < Filter.limsup s Filter.atTop :=
    lt_of_not_ge hlt
  obtain ⟨b, hb_left, hb_right⟩ := EReal.lt_iff_exists_real_btwn.mp hlt'
  have hb_real : clarkeDirectionalDerivReal g x0 a < b := by
    exact_mod_cast hb_left
  have h_event : ∀ᶠ k in Filter.atTop, s k ≤ (b : EReal) := by
    filter_upwards
        [outer_quotient_eventually_le_of_lt_bound
          g x0 a h_local hu hq ht ht_pos hb_real] with k hk
    change ((((g (u k + t k • q k) - g (u k)) / t k : ℝ)) : EReal) ≤ ((b : ℝ) : EReal)
    exact_mod_cast hk
  have hlimsup_le :
      Filter.limsup s Filter.atTop ≤ (b : EReal) :=
    Filter.limsup_le_of_le (hf := hs_cobdd) h_event
  exact (not_le_of_gt hb_right) hlimsup_le

/-- Helper for Chapter14 Lemma 14.1.4: a Clarke subgradient of `-f` at `x` negates to a Clarke
subgradient of `f` at `x`. -/
lemma neg_mem_clarkeDifferential_of_mem_neg
    (f : E → ℝ) (x : E) (h_local : LocallyLipschitzAt f x) {ξ : DualSpace}
    (hξ : ξ ∈ (∂ᶜ (fun y ↦ -f y)) x) :
    -ξ ∈ (∂ᶜ f) x := by
  rw [mem_clarkeDifferential_iff] at hξ ⊢
  intro d
  have hξ_eval : (((ξ (-d) : ℝ)) : EReal) ≤ (fun y ↦ -f y)ᵒ(x; -d) := hξ (-d)
  have hdir :
      (fun y ↦ -f y)ᵒ(x; -d) = fᵒ(x; d) := by
    -- Reapply the sign-change identity to the original `f` with direction `-d`.
    change (-f)ᵒ(x; -d) = fᵒ(x; d)
    simpa [neg_neg] using
      (clarkeDirectionalDerivative_neg_direction
        (f := f) (x := x) (h_lipschitz := h_local) (-d)).symm
  simpa [hdir] using hξ_eval

/-- Helper for Chapter14 Lemma 14.1.4: signed component bounds on a codomain vector `a` let us
choose a chain-rule generator whose evaluation at `d` dominates `gᵒ(h x; a)`. -/
lemma exists_mem_chainRule_generator_eval_ge_of_signed_component_bounds
    (g : Codomain → ℝ) (h : E → Codomain) (x : E) (a : Codomain) (d : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x)
    (h_local_g : LocallyLipschitzAt g (h x))
    (ha_pos : ∀ i : Fin n, a i ≤ clarkeDirectionalDerivReal (fun y ↦ h y i) x d)
    (ha_neg : ∀ i : Fin n, -a i ≤ clarkeDirectionalDerivReal (fun y ↦ -h y i) x d) :
    ∃ η ∈ chainRuleGeneratorSet g h x,
      clarkeDirectionalDerivReal g (h x) a ≤ η d := by
  classical
  obtain ⟨α, hαmem, hαeval⟩ :=
    (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
      g (h x) a h_local_g).1
  let coeff : Fin n → ℝ := fun i ↦ α (EuclideanSpace.single i (1 : ℝ))
  have hcomponent :
      ∀ i : Fin n,
        ∃ ξ : DualSpace,
          ξ ∈ (∂ᶜ (fun y ↦ h y i)) x ∧ coeff i * a i ≤ coeff i * ξ d := by
    intro i
    by_cases hcoeff_nonneg : 0 ≤ coeff i
    · obtain ⟨ξ, hξmem, hξeval⟩ :=
        (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
          (fun y ↦ h y i) x d (h_local_h i)).1
      refine ⟨ξ, hξmem, ?_⟩
      have hbound : a i ≤ ξ d := by
        simpa [hξeval] using ha_pos i
      -- Nonnegative outer coefficients preserve the componentwise upper bound.
      exact mul_le_mul_of_nonneg_left hbound hcoeff_nonneg
    · have hcoeff_nonpos : coeff i ≤ 0 := le_of_lt (lt_of_not_ge hcoeff_nonneg)
      obtain ⟨ζ, hζmem, hζeval⟩ :=
        (clarkeDirectionalDeriv_isGreatest_image_clarkeDifferential_of_locallyLipschitzAt
          (fun y ↦ -h y i) x d (h_local_h i).neg).1
      refine ⟨-ζ, neg_mem_clarkeDifferential_of_mem_neg
        (f := fun y ↦ h y i) (x := x) (h_local := h_local_h i) hζmem, ?_⟩
      have hbound : -a i ≤ ζ d := by
        simpa [hζeval] using ha_neg i
      have hbound' : -ζ d ≤ a i := by
        linarith
      -- Negative outer coefficients require maximizing `-h_i` and then negating back.
      simpa [coeff] using mul_le_mul_of_nonpos_left hbound' hcoeff_nonpos
  choose ξ hξmem hξbound using hcomponent
  refine ⟨StrongDual.toWeakDual (∑ i : Fin n, coeff i • ξ i), ?_, ?_⟩
  · -- Package the maximizing outer subgradient together with the signed component witnesses.
    refine ⟨(α, ξ), ?_, rfl⟩
    exact ⟨hαmem, hξmem⟩
  · -- Sum the coordinatewise inequalities to dominate the outer support value at `a`.
    calc
      clarkeDirectionalDerivReal g (h x) a = α a := hαeval.symm
      _ = ∑ i : Fin n, coeff i * a i := by
            simpa [coeff] using codomainDual_apply_eq_sum_single_coeff (n := n) α a
      _ ≤ ∑ i : Fin n, coeff i * ξ i d := by
            exact Finset.sum_le_sum fun i _ ↦ hξbound i
      _ = (∑ i : Fin n, coeff i • ξ i) d := by
            let ev : DualSpace →ₗ[ℝ] ℝ :=
              { toFun := fun ζ ↦ ζ d
                map_add' := by intro ζ₁ ζ₂; rfl
                map_smul' := by intro c ζ; rfl }
            symm
            change ev (∑ i : Fin n, coeff i • ξ i) = ∑ i : Fin n, ev (coeff i • ξ i)
            rw [map_sum]
      _ = (StrongDual.toWeakDual (∑ i : Fin n, coeff i • ξ i)) d := by
            rfl

/-- Helper for Chapter14 Lemma 14.1.4: every composite direction `d` admits a chain-rule
generator whose evaluation dominates the Clarke directional derivative of `g ∘ h`. -/
lemma exists_mem_chainRule_generator_eval_ge_comp
    (g : Codomain → ℝ) (h : E → Codomain) (x d : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x)
    (h_local_g : LocallyLipschitzAt g (h x)) :
    ∃ η ∈ chainRuleGeneratorSet g h x,
      clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d ≤ η d := by
  -- Route correction: the false fixed-vector target has been replaced by the source-faithful
  -- goal of finding one generator that dominates the composite support in direction `d`.
  have h_local_comp :
      LocallyLipschitzAt (fun y ↦ g (h y)) x :=
    locallyLipschitzAt_comp_of_components g h x h_local_h h_local_g
  let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
  let qcomp : E × ℝ → EReal :=
    fun p ↦ ((((g (h (p.1 + p.2 • d)) - g (h p.1)) / p.2 : ℝ)) : EReal)
  have hqlimsup :
      Filter.limsup qcomp l =
        (((clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d : ℝ)) : EReal) := by
    calc
      Filter.limsup qcomp l = (fun y ↦ g (h y))ᵒ(x; d) := by
        rw [clarkeDirectionalDeriv_eq_limsup]
        simp [l, qcomp, wholeSpaceClarkePairDomain_eq_positiveTimes]
      _ = (((clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d : ℝ)) : EReal) := by
        symm
        exact coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
          (fun y ↦ g (h y)) x d h_local_comp
  letI : l.NeBot := by
    simpa [l, wholeSpaceClarkePairDomain_eq_positiveTimes] using wholeSpaceClarkePairFilter_neBot x d
  rcases locallyLipschitzAt_iff.mp h_local_comp with ⟨εc, hεc, Kc, hKc⟩
  have hqcomp_upper :
      ∀ᶠ p in l, qcomp p ≤ (((Kc : ℝ) * ‖d‖ : ℝ) : EReal) := by
    filter_upwards
        [show ∀ᶠ p in l,
            |((fun y ↦ g (h y)) (p.1 + p.2 • d) - (fun y ↦ g (h y)) p.1) / p.2|
              ≤ (Kc : ℝ) * ‖d‖ from
          by
            simpa [l, wholeSpaceClarkePairDomain_eq_positiveTimes] using
              eventuallyAbsClarkeQuotient_le_of_closedBallLipschitz
                (f := fun y ↦ g (h y)) (x := x) (d := d) Kc hεc hKc] with p hp
    change ((((g (h (p.1 + p.2 • d)) - g (h p.1)) / p.2 : ℝ)) : EReal) ≤
      (((Kc : ℝ) * ‖d‖ : ℝ) : EReal)
    exact_mod_cast (abs_le.mp hp).2
  have hqcomp_bdd : l.IsBoundedUnder (· ≤ ·) qcomp :=
    ⟨(((Kc : ℝ) * ‖d‖ : ℝ) : EReal), hqcomp_upper⟩
  have hqcomp_cobdd : l.IsCoboundedUnder (· ≤ ·) qcomp :=
    Filter.isCoboundedUnder_le_of_le l (x := (⊥ : EReal)) fun _ ↦ by
      simp [qcomp]
  obtain ⟨pseq, hpseq_q, hpseq⟩ :=
    exists_seq_tendsto_limsup (f := l) (u := qcomp) (hc := hqcomp_cobdd) (hb := hqcomp_bdd)
  have hpseq_q_tendsto :
      Filter.Tendsto (qcomp ∘ pseq) Filter.atTop
        (nhds (((clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d : ℝ)) : EReal)) := by
    simpa [hqlimsup] using hpseq_q
  have hpseq_base :
      Filter.Tendsto pseq Filter.atTop (nhds ((x : E), (0 : ℝ))) :=
    hpseq.mono_right nhdsWithin_le_nhds
  have hpseq_pos :
      ∀ᶠ k in Filter.atTop, 0 < (pseq k).2 := by
    have hpos_mem : {p : E × ℝ | 0 < p.2} ∈ l := by
      change {p : E × ℝ | 0 < p.2} ∈
        nhds ((x : E), (0 : ℝ)) ⊓ Filter.principal {p : E × ℝ | 0 < p.2}
      rw [Filter.mem_inf_iff]
      refine ⟨Set.univ, Filter.univ_mem, {p : E × ℝ | 0 < p.2}, by simp, ?_⟩
      ext p
      simp
    simpa using hpseq.eventually hpos_mem
  have hbounded :
      ∃ ρ > 0, ∃ R > 0, ∀ {p : E × ℝ},
        p ∈ Metric.closedBall ((x : E), (0 : ℝ)) ρ →
        0 < p.2 →
        exactComponentQuotientVector h d p ∈ Metric.closedBall (0 : Codomain) R :=
    exactComponentQuotientVector_bounded_of_nearby_pairs h x d h_local_h
  rcases hbounded with ⟨ρ, hρ, R, hR, hboundExact⟩
  have hpseq_ball :
      ∀ᶠ k in Filter.atTop, pseq k ∈ Metric.closedBall ((x : E), (0 : ℝ)) ρ :=
    hpseq_base.eventually <| Metric.closedBall_mem_nhds ((x : E), (0 : ℝ)) hρ
  obtain ⟨Npos, hNpos⟩ := Filter.eventually_atTop.1 hpseq_pos
  obtain ⟨Nball, hNball⟩ := Filter.eventually_atTop.1 hpseq_ball
  let N : ℕ := max Npos Nball
  let shift : ℕ → ℕ := fun k ↦ k + N
  have hshift_mono : StrictMono shift := by
    intro m n hmn
    dsimp [shift]
    exact Nat.add_lt_add_right hmn N
  let y : ℕ → E := fun k ↦ (pseq (shift k)).1
  let t : ℕ → ℝ := fun k ↦ (pseq (shift k)).2
  let qExact : ℕ → Codomain := fun k ↦ exactComponentQuotientVector h d (y k, t k)
  have ht_pos : ∀ k : ℕ, 0 < t k := by
    intro k
    dsimp [t, shift]
    exact hNpos (k + N) (le_trans (le_max_left _ _) (Nat.le_add_left N k))
  have hpair_shift :
      Filter.Tendsto (fun k ↦ pseq (shift k)) Filter.atTop
        (nhds ((x : E), (0 : ℝ))) :=
    hpseq_base.comp hshift_mono.tendsto_atTop
  have hy : Filter.Tendsto y Filter.atTop (nhds x) := by
    exact continuous_fst.continuousAt.tendsto.comp hpair_shift
  have ht : Filter.Tendsto t Filter.atTop (nhds 0) := by
    exact continuous_snd.continuousAt.tendsto.comp hpair_shift
  have hqcomp_shift :
      Filter.Tendsto (fun k ↦ qcomp (pseq (shift k))) Filter.atTop
        (nhds (((clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d : ℝ)) : EReal)) :=
    hpseq_q_tendsto.comp hshift_mono.tendsto_atTop
  have hqExact_mem : ∀ k : ℕ, qExact k ∈ Metric.closedBall (0 : Codomain) R := by
    intro k
    have hk_ball : pseq (shift k) ∈ Metric.closedBall ((x : E), (0 : ℝ)) ρ := by
      dsimp [shift]
      exact hNball (k + N) (le_trans (le_max_right _ _) (Nat.le_add_left N k))
    exact hboundExact hk_ball (ht_pos k)
  obtain ⟨a, ha_mem, φ, hφ, hqφ_tendsto⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : Codomain) R) hqExact_mem
  have hyφ : Filter.Tendsto (fun k ↦ y (φ k)) Filter.atTop (nhds x) :=
    hy.comp hφ.tendsto_atTop
  have htφ : Filter.Tendsto (fun k ↦ t (φ k)) Filter.atTop (nhds 0) :=
    ht.comp hφ.tendsto_atTop
  have htφ_pos : ∀ k : ℕ, 0 < t (φ k) := fun k ↦ ht_pos (φ k)
  have hqφ :
      Filter.Tendsto
        (fun k ↦ exactComponentQuotientVector h d (y (φ k), t (φ k)))
        Filter.atTop (nhds a) := by
    change Filter.Tendsto ((fun k ↦ exactComponentQuotientVector h d (y k, t k)) ∘ φ)
      Filter.atTop (nhds a)
    simpa [Function.comp] using hqφ_tendsto
  obtain ⟨ha_pos, ha_neg⟩ :=
    cluster_exactComponentQuotientVector_has_signed_component_bounds
      h x d h_local_h hyφ htφ htφ_pos hqφ
  have hhφ :
      Filter.Tendsto (fun k ↦ h (y (φ k))) Filter.atTop (nhds (h x)) := by
    exact
      (LocallyLipschitzAt.continuousAt
        (locallyLipschitzAt_euclidean_of_components h x h_local_h)).tendsto.comp hyφ
  have hqcomp_subseq :
      Filter.Tendsto (fun k ↦ qcomp (pseq (shift (φ k)))) Filter.atTop
        (nhds (((clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d : ℝ)) : EReal)) :=
    hqcomp_shift.comp hφ.tendsto_atTop
  have houter_support :
      clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d ≤
        clarkeDirectionalDerivReal g (h x) a := by
    by_contra hlt
    obtain ⟨b, hb_left, hb_right⟩ :=
      exists_between (lt_of_not_ge hlt)
    have houter_event :
        ∀ᶠ k in Filter.atTop,
          ((g (h (y (φ k)) + t (φ k) • exactComponentQuotientVector h d (y (φ k), t (φ k))) -
                g (h (y (φ k)))) / t (φ k) : ℝ) ≤ b :=
      outer_quotient_eventually_le_of_lt_bound
        g (h x) a h_local_g hhφ hqφ htφ htφ_pos hb_left
    have hcomp_event :
        ∀ᶠ k in Filter.atTop, qcomp (pseq (shift (φ k))) ≤ ((b : ℝ) : EReal) := by
      filter_upwards [houter_event] with k hk
      have hk_eq :
          qcomp (pseq (shift (φ k))) =
            ((((g (h (y (φ k)) + t (φ k) •
                    exactComponentQuotientVector h d (y (φ k), t (φ k))) -
                    g (h (y (φ k)))) / t (φ k) : ℝ)) : EReal) := by
        dsimp [qcomp, y, t, shift]
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
          (composite_quotient_eq_outer_exactComponentQuotient
            g h d (y (φ k), t (φ k)) (htφ_pos k))
      rw [hk_eq]
      exact_mod_cast hk
    have hbE :
        (((b : ℝ)) : EReal) <
          (((clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d : ℝ)) : EReal) := by
      exact_mod_cast hb_right
    have hgt_event :
        ∀ᶠ k in Filter.atTop, ((b : ℝ) : EReal) < qcomp (pseq (shift (φ k))) :=
      hqcomp_subseq.eventually <| Ioi_mem_nhds hbE
    obtain ⟨Nle, hNle⟩ := Filter.eventually_atTop.1 hcomp_event
    obtain ⟨Ngt, hNgt⟩ := Filter.eventually_atTop.1 hgt_event
    exact (not_le_of_gt (hNgt (max Nle Ngt) (le_max_right _ _)))
      (hNle (max Nle Ngt) (le_max_left _ _))
  obtain ⟨η, hηmem, hηbound⟩ :=
    exists_mem_chainRule_generator_eval_ge_of_signed_component_bounds
      g h x a d h_local_h h_local_g ha_pos ha_neg
  refine ⟨η, hηmem, ?_⟩
  -- The subsequence outer-support bound and the signed component inequalities now match the
  -- chain-rule generator witness returned above.
  calc
    clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d
        ≤ clarkeDirectionalDerivReal g (h x) a := houter_support
    _ ≤ η d := hηbound

/-- Helper for Chapter14 Lemma 14.1.4: every composite Clarke subgradient lies in the weak-* closed
convex hull generated by the chain-rule witnesses. -/
lemma toWeakDual_mem_chainRule_closedConvexHull_of_mem_clarkeDifferential
    (g : Codomain → ℝ) (h : E → Codomain) (x : E) {ξ : DualSpace}
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x)
    (h_local_g : LocallyLipschitzAt g (h x))
    (hξ : ξ ∈ (∂ᶜ (fun y ↦ g (h y))) x) :
    StrongDual.toWeakDual ξ ∈ closedConvexHull ℝ (chainRuleGeneratorSet g h x) := by
  have h_local_comp :
      LocallyLipschitzAt (fun y ↦ g (h y)) x :=
    locallyLipschitzAt_comp_of_components g h x h_local_h h_local_g
  rw [mem_closed_convex_iff_eval_halfspaces convex_closedConvexHull isClosed_closedConvexHull]
  intro d
  have hξ_support :
      ξ d ≤ clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d := by
    have hξE :
        (((ξ d : ℝ)) : EReal) ≤
          (((clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d : ℝ)) : EReal) := by
      simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
        (fun y ↦ g (h y)) x d h_local_comp] using
        (mem_clarkeDifferential_iff (fun y ↦ g (h y)) x ξ).1 hξ d
    exact_mod_cast hξE
  obtain ⟨η, hηmem, hηdom⟩ :=
    exists_mem_chainRule_generator_eval_ge_comp g h x d h_local_h h_local_g
  refine ⟨η, subset_closedConvexHull (𝕜 := ℝ) hηmem, ?_⟩
  -- Compare the composite support value with the dominating generator returned above.
  calc
    (StrongDual.toWeakDual ξ) d = ξ d := by
      rfl
    _ ≤ clarkeDirectionalDerivReal (fun y ↦ g (h y)) x d := hξ_support
    _ ≤ η d := hηdom

/-- Chapter14 Lemma 14.1.4 (7): if `f = g ∘ h`, every component `h_i` is Lipschitz near `x`,
and `g` is Lipschitz near `h x`, then the image of `∂ f(x)` in `WeakDual ℝ E` is contained in the
weak-* closed convex hull of the finite sums `∑ i, α_i • ξ_i` with `ξ_i ∈ ∂ h_i(x)` and
`α ∈ ∂ g(h x)`, where the coefficient `α_i` is the value of the codomain dual element `α` on the
`i`-th standard basis vector. -/
theorem clarkeDifferential_comp_subset_weakClosedConvexHull
    (g : Codomain → ℝ) (h : E → Codomain) (x : E)
    (h_local_h : ∀ i : Fin n, LocallyLipschitzAt (fun y ↦ h y i) x)
    (h_local_g : LocallyLipschitzAt g (h x)) :
    StrongDual.toWeakDual ''
        (∂ᶜ (fun y ↦ g (h y))) x ⊆
      (closedConvexHull ℝ)
        ((fun p : CodomainDual × (Fin n → DualSpace) ↦
            (StrongDual.toWeakDual
              (∑ i : Fin n, (p.1 (EuclideanSpace.single i (1 : ℝ))) • p.2 i) :
                WeakDualSpace)) ''
          {p : CodomainDual × (Fin n → DualSpace) |
            p.1 ∈ (∂ᶜ g) (h x) ∧
              ∀ i : Fin n, p.2 i ∈ (∂ᶜ (fun y ↦ h y i)) x}) := by
  -- Route correction: keep the exact displayed generator set and close the theorem through the
  -- weak-* halfspace criterion already used earlier in the file.
  change StrongDual.toWeakDual '' (∂ᶜ (fun y ↦ g (h y))) x ⊆
    closedConvexHull ℝ (chainRuleGeneratorSet g h x)
  intro η hη
  rcases hη with ⟨ξ, hξ, rfl⟩
  -- Reduce the set inclusion to the closed-convex membership lemma for one subgradient `ξ`.
  exact toWeakDual_mem_chainRule_closedConvexHull_of_mem_clarkeDifferential
    g h x h_local_h h_local_g hξ

end ChainRule

#print axioms clarkeDirectionalDeriv
#print axioms clarkeDifferential

end
