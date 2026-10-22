/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part1

open scoped Topology
open scoped Pointwise
open scoped ConvexAnalysis

section Chap05
section Section25

/-- Helper for Theorem 25.1: normalizing the displacement from `x` to a punctured point produces
a direction in the closed unit ball and a radial decomposition of that point. -/
lemma helperForTheorem_25_1_normalizedDirection_mem_closedUnitBall {n : Nat}
    {x z : Fin n → Real} (hzx : z ≠ x) :
    0 < ‖z - x‖ ∧
      ((1 / ‖z - x‖) • (z - x)) ∈ Metric.closedBall (0 : Fin n → Real) 1 ∧
      z = x + ‖z - x‖ • ((1 / ‖z - x‖) • (z - x)) := by
  have hnormPos : 0 < ‖z - x‖ := by
    -- A punctured point has nonzero displacement, hence positive norm.
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  have hunitNorm :
      ‖((1 / ‖z - x‖) • (z - x))‖ = 1 := by
    -- The normalized displacement has norm exactly one.
    calc
      ‖((1 / ‖z - x‖) • (z - x))‖ = |1 / ‖z - x‖| * ‖z - x‖ := norm_smul _ _
      _ = (1 / ‖z - x‖) * ‖z - x‖ := by
          rw [abs_of_nonneg (by positivity)]
      _ = 1 := by
          field_simp [hnormPos.ne']
  have huBall :
      ((1 / ‖z - x‖) • (z - x)) ∈ Metric.closedBall (0 : Fin n → Real) 1 := by
    -- Repackage the norm computation as closed-ball membership.
    rw [Metric.mem_closedBall]
    simpa [dist_eq_norm] using (show ‖((1 / ‖z - x‖) • (z - x))‖ ≤ 1 from le_of_eq hunitNorm)
  have hsmul :
      ‖z - x‖ • ((1 / ‖z - x‖) • (z - x)) = z - x := by
    have hmul : ‖z - x‖ * (1 / ‖z - x‖) = 1 := by
      field_simp [hnormPos.ne']
    -- Scaling the normalized direction by the original norm recovers the displacement.
    calc
      ‖z - x‖ • ((1 / ‖z - x‖) • (z - x)) =
          (‖z - x‖ * (1 / ‖z - x‖)) • (z - x) := by
            rw [smul_smul]
      _ = (1 : Real) • (z - x) := by rw [hmul]
      _ = z - x := by simp
  refine ⟨hnormPos, huBall, ?_⟩
  -- Add the recovered displacement back to the base point.
  calc
    z = x + (z - x) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = x + ‖z - x‖ • ((1 / ‖z - x‖) • (z - x)) := by rw [hsmul]

/-- Helper for Theorem 25.1: after rewriting a punctured nearby point in normalized radial form,
its error quotient lies between `0` and the dyadic remainder at any larger fixed scale. -/
lemma helperForTheorem_25_1_errorQuotient_le_remainderAt_fixedScale {n : Nat}
    {f : (Fin n → Real) → EReal} {x g : Fin n → Real} {ρ : Real}
    (hf : ConvexFunction f)
    (hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hsub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) g))
    (hρpos : 0 < ρ) (N : Nat) {z : Fin n → Real} (hzx : z ≠ x)
    (hzFinite : f z ≠ ⊤ ∧ f z ≠ ⊥)
    (hstepFinite :
      f (x + helperForTheorem_25_1_dyadicScale ρ N • ((1 / ‖z - x‖) • (z - x))) ≠ ⊤ ∧
        f (x + helperForTheorem_25_1_dyadicScale ρ N • ((1 / ‖z - x‖) • (z - x))) ≠ ⊥)
    (hzle : ‖z - x‖ ≤ helperForTheorem_25_1_dyadicScale ρ N) :
    ((1 / ‖z - x‖) • (z - x)) ∈ Metric.closedBall (0 : Fin n → Real) 1 ∧
      0 ≤ erealGradientErrorQuotient f x g z ∧
      erealGradientErrorQuotient f x g z ≤
        helperForTheorem_25_1_dyadicRemainder f x g ρ N
          ((1 / ‖z - x‖) • (z - x)) := by
  let t : Real := ‖z - x‖
  let u : Fin n → Real := (1 / t) • (z - x)
  let τ : Real := helperForTheorem_25_1_dyadicScale ρ N
  have hnormData :=
    helperForTheorem_25_1_normalizedDirection_mem_closedUnitBall (x := x) (z := z) hzx
  rcases hnormData with ⟨htPosRaw, huBallRaw, hzreprRaw⟩
  have htPos : 0 < t := by simpa [t] using htPosRaw
  have huBall : u ∈ Metric.closedBall (0 : Fin n → Real) 1 := by
    simpa [u, t] using huBallRaw
  have hzrepr : z = x + t • u := by
    simpa [u, t] using hzreprRaw
  have hτPos : 0 < τ := by
    simpa [τ] using helperForTheorem_25_1_dyadicScale_pos hρpos N
  have hstepFinite' : f (x + τ • u) ≠ ⊤ ∧ f (x + τ • u) ≠ ⊥ := by
    simpa [τ, u, t] using hstepFinite
  let Qz : Real := ((f z).toReal - (f x).toReal) / t
  let Qτ : Real := ((f (x + τ • u)).toReal - (f x).toReal) / τ
  have hQz_eq_quot :
      directionalDifferenceQuotientAt f x u t = ((Qz : Real) : EReal) := by
    have hzrepr' : x + t • u = z := by simpa using hzrepr.symm
    -- At the actual point `z`, the directional quotient is finite and matches the real quotient.
    simp [Qz, directionalDifferenceQuotientAt, hzrepr', EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal hzFinite.1 hzFinite.2, EReal.coe_toReal hxFinite.1 hxFinite.2]
  have hQτ_eq_quot :
      directionalDifferenceQuotientAt f x u τ = ((Qτ : Real) : EReal) := by
    -- The same finite-value rewrite applies at the dyadic comparison point.
    simp [Qτ, directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal hstepFinite'.1 hstepFinite'.2, EReal.coe_toReal hxFinite.1 hxFinite.2]
  have hmono :
      MonotoneOn (directionalDifferenceQuotientAt f x u) (Set.Ioi (0 : Real)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite).1 u |>.1
  have hlowerE :
      (((g ⬝ᵥ u : Real) : Real) : EReal) ≤ directionalDifferenceQuotientAt f x u t :=
    helperForTheorem_23_2_differenceQuotient_lowerBound_of_subgradient
      f x hxFinite (dotProductEquiv Real (Fin n) g) hsub u htPos
  have hlowerReal : g ⬝ᵥ u ≤ Qz := by
    exact_mod_cast
      (show (((g ⬝ᵥ u : Real) : Real) : EReal) ≤ ((Qz : Real) : EReal) by
        simpa [hQz_eq_quot] using hlowerE)
  have hupperE :
      directionalDifferenceQuotientAt f x u t ≤ directionalDifferenceQuotientAt f x u τ :=
    hmono htPos hτPos (by simpa [t, τ] using hzle)
  have hupperReal : Qz ≤ Qτ := by
    exact_mod_cast
      (show ((Qz : Real) : EReal) ≤ ((Qτ : Real) : EReal) by
        simpa [hQz_eq_quot, hQτ_eq_quot] using hupperE)
  have herrorEq :
      erealGradientErrorQuotient f x g z = Qz - g ⬝ᵥ u := by
    have htNe : t ≠ 0 := ne_of_gt htPos
    have htoRealSub :
        (f z - f x).toReal = (f z).toReal - (f x).toReal := by
      simpa using EReal.toReal_sub hzFinite.1 hzFinite.2 hxFinite.1 hxFinite.2
    have hsubrepr : z - x = t • u := by
      calc
        z - x = (x + t • u) - x := by rw [hzrepr]
        _ = t • u := by simp
    have hdot : g ⬝ᵥ (z - x) = t * (g ⬝ᵥ u) := by
      rw [hsubrepr]
      simpa [smul_eq_mul] using (dotProduct_smul t g u)
    -- Rewrite the normalized error in terms of the real secant quotient minus `g ⬝ u`.
    rw [erealGradientErrorQuotient, htoRealSub, hdot]
    change (((f z).toReal - (f x).toReal) - t * (g ⬝ᵥ u)) / ‖z - x‖ = Qz - g ⬝ᵥ u
    rw [show ‖z - x‖ = t by rfl]
    dsimp [Qz]
    field_simp [htNe]
  have hremainderEq :
      helperForTheorem_25_1_dyadicRemainder f x g ρ N u = Qτ - g ⬝ᵥ u := by
    have hτNe : τ ≠ 0 := ne_of_gt hτPos
    -- Expanding the dyadic remainder gives the same affine correction at the fixed dyadic scale.
    calc
      helperForTheorem_25_1_dyadicRemainder f x g ρ N u =
          ((((f (x + τ • u)).toReal - (f x).toReal) - τ * (g ⬝ᵥ u)) / τ) := by
            simp [helperForTheorem_25_1_dyadicRemainder, τ]
      _ = (((f (x + τ • u)).toReal - (f x).toReal) / τ) - ((τ * (g ⬝ᵥ u)) / τ) := by
            rw [sub_div]
      _ = (((f (x + τ • u)).toReal - (f x).toReal) / τ) - g ⬝ᵥ u := by
            have hcancel : τ * (g ⬝ᵥ u) / τ = g ⬝ᵥ u := by
              field_simp [hτNe]
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using congrArg
              (fun s : Real => (((f (x + τ • u)).toReal - (f x).toReal) / τ) - s) hcancel
      _ = Qτ - g ⬝ᵥ u := by rfl
  refine ⟨by simpa [u, t] using huBall, ?_, ?_⟩
  · -- The subgradient lower bound makes the error quotient nonnegative.
    rw [herrorEq]
    linarith
  · -- Monotonicity of convex secants transfers the dyadic remainder bound back to `z`.
    rw [herrorEq, hremainderEq]
    linarith

/-- Helper for Theorem 25.1: a uniform dyadic remainder bound makes the punctured error quotient
eventually `ε`-small in the metric neighborhood filter. -/
lemma helperForTheorem_25_1_uniformBound_implies_errorQuotient_eventually_small {n : Nat}
    {f : (Fin n → Real) → EReal} {x g : Fin n → Real} {ρ ρ' eps : Real}
    (hf : ConvexFunction f)
    (hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hsub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) g))
    (hρpos : 0 < ρ) (hρ'pos : 0 < ρ')
    (hρ'finite :
      ∀ z : Fin n → Real, z ∈ Metric.closedBall x ρ' → f z ≠ ⊤ ∧ f z ≠ ⊥)
    (hRuniform :
      TendstoUniformlyOn (helperForTheorem_25_1_dyadicRemainder f x g ρ) (fun _ => 0)
        Filter.atTop (Metric.closedBall (0 : Fin n → Real) 1))
    (heps : 0 < eps) :
    ∀ᶠ z in
      nhdsWithin x ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        dist (erealGradientErrorQuotient f x g z) 0 < eps := by
  let S : Set (Fin n → Real) :=
    {z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have huniform :
      ∀ᶠ N in Filter.atTop,
        ∀ u ∈ Metric.closedBall (0 : Fin n → Real) 1,
          dist (0 : Real) (helperForTheorem_25_1_dyadicRemainder f x g ρ N u) < eps :=
    (Metric.tendstoUniformlyOn_iff.mp hRuniform) eps heps
  have hτsmall :
      ∀ᶠ N in Filter.atTop, helperForTheorem_25_1_dyadicScale ρ N < ρ' := by
    have hdistSmall :
        ∀ᶠ N in Filter.atTop, dist (helperForTheorem_25_1_dyadicScale ρ N) 0 < ρ' :=
      (Metric.tendsto_nhds.1 (helperForTheorem_25_1_dyadicScale_tendsto_zero (ρ := ρ))) ρ'
        hρ'pos
    filter_upwards [hdistSmall] with N hN
    have hτnonneg : 0 ≤ helperForTheorem_25_1_dyadicScale ρ N := by
      exact le_of_lt (helperForTheorem_25_1_dyadicScale_pos hρpos N)
    simpa [Real.dist_eq, abs_of_nonneg hτnonneg] using hN
  rcases Filter.eventually_atTop.1 (Filter.Eventually.and huniform hτsmall) with
    ⟨N, hNtail⟩
  have hNboth := hNtail N le_rfl
  rcases hNboth with ⟨hNuniform, hNτ⟩
  let τ : Real := helperForTheorem_25_1_dyadicScale ρ N
  let r : Real := min ρ' τ
  have hrPos : 0 < r := by
    -- Choose a punctured ball small enough for both finiteness and the dyadic comparison scale.
    dsimp [r, τ]
    exact lt_min hρ'pos (helperForTheorem_25_1_dyadicScale_pos hρpos N)
  have hbase :
      Metric.ball x r ∩ S ∈ nhdsWithin x S := by
    exact Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hrPos))
      self_mem_nhdsWithin
  refine Filter.mem_of_superset hbase ?_
  intro z hz
  rcases hz with ⟨hzBall, hzS⟩
  rcases hzS with ⟨hzx, _hzDom⟩
  have hzNormLt : ‖z - x‖ < r := by
    simpa [S, r, dist_eq_norm] using (Metric.mem_ball.mp hzBall)
  have hzClosed : z ∈ Metric.closedBall x ρ' := by
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le hzNormLt (min_le_left _ _))
  have hzFinite : f z ≠ ⊤ ∧ f z ≠ ⊥ := hρ'finite z hzClosed
  let u : Fin n → Real := (1 / ‖z - x‖) • (z - x)
  have hnormData :=
    helperForTheorem_25_1_normalizedDirection_mem_closedUnitBall (x := x) (z := z) hzx
  have huBall : u ∈ Metric.closedBall (0 : Fin n → Real) 1 := by
    simpa [u] using hnormData.2.1
  have hstepClosed : x + τ • u ∈ Metric.closedBall x ρ' := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have huNorm : ‖u‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using huBall
    have hτnonneg : 0 ≤ τ := by
      dsimp [τ]
      exact le_of_lt (helperForTheorem_25_1_dyadicScale_pos hρpos N)
    -- The normalized direction stays in the unit ball, so the dyadic step stays within radius `ρ'`.
    calc
      ‖(x + τ • u) - x‖ = ‖τ • u‖ := by simp [sub_eq_add_neg, add_assoc]
      _ = |τ| * ‖u‖ := norm_smul _ _
      _ = τ * ‖u‖ := by rw [abs_of_nonneg hτnonneg]
      _ ≤ τ * 1 := by gcongr
      _ = τ := by ring
      _ ≤ ρ' := le_of_lt hNτ
  have hstepFinite : f (x + τ • u) ≠ ⊤ ∧ f (x + τ • u) ≠ ⊥ := hρ'finite _ hstepClosed
  have hzLe : ‖z - x‖ ≤ τ := by
    exact le_of_lt (lt_of_lt_of_le hzNormLt (min_le_right _ _))
  have hsqueeze :=
    helperForTheorem_25_1_errorQuotient_le_remainderAt_fixedScale
      (f := f) (x := x) (g := g) (ρ := ρ) hf hxFinite hsub hρpos N hzx hzFinite
      (by simpa [τ, u] using hstepFinite) (by simpa [τ] using hzLe)
  rcases hsqueeze with ⟨huBall', herrorNonneg, herrorLe⟩
  have hRdist :
      dist (0 : Real) (helperForTheorem_25_1_dyadicRemainder f x g ρ N u) < eps :=
    hNuniform u huBall'
  have hRnonneg : 0 ≤ helperForTheorem_25_1_dyadicRemainder f x g ρ N u :=
    le_trans herrorNonneg herrorLe
  have hRlt : helperForTheorem_25_1_dyadicRemainder f x g ρ N u < eps := by
    simpa [Real.dist_eq, abs_of_nonneg hRnonneg] using hRdist
  have herrorLt : erealGradientErrorQuotient f x g z < eps :=
    lt_of_le_of_lt herrorLe hRlt
  -- The squeeze converts the uniform dyadic bound into the metric estimate for the error quotient.
  simpa [Real.dist_eq, abs_of_nonneg herrorNonneg] using herrorLt

/-- Helper for Theorem 25.1: if the upper directional derivative is already linear on the interior
of the effective domain of a proper convex function, then the first-order error quotient vanishes
and `f` is differentiable at `x`. -/
lemma helperForTheorem_25_1_linearDirectionalDerivative_implies_ERealDifferentiableAt {n : Nat}
    {f : (Fin n → Real) → EReal} {x g : Fin n → Real}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hdir :
      ∀ y : Fin n → Real,
        upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal)) :
    ERealDifferentiableAt f x := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := interior_subset hxInt
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    refine ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hxDom,
      ?_⟩
    exact hproper.2.2 x (by simp)
  have hsub :
      IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) :=
    helperForTheorem_25_1_subgradient_of_linearDirectionalDerivative
      (hproper := hproper) (hxInt := hxInt) (hdir := hdir)
  rcases helperForTheorem_25_1_exists_closedBall_subset_interior_effectiveDomain
      (f := f) (x := x) hxInt with
    ⟨ρ, hρpos, hρsubInt⟩
  rcases helperForTheorem_25_1_exists_closedBall_finiteValues
      (f := f) (x := x) hproper hxInt with
    ⟨ρ', hρ'pos, hρ'finite⟩
  -- The differentiability witness uses the given candidate gradient `g`.
  refine ⟨g, ?_, ?_⟩
  · -- The local finiteness is already available; the remaining analytic step is the Chapter 10
    -- Route correction: the earlier Chapter 10 convex-family route was too indirect. The current
    -- plan fixes the dyadic remainder family on the compact unit ball and reduces the unresolved
    -- work to Dini's theorem plus the fixed-scale secant squeeze.
    let R : Nat → (Fin n → Real) → Real :=
      helperForTheorem_25_1_dyadicRemainder f x g ρ
    have hRuniform :
        TendstoUniformlyOn R (fun _ => 0) Filter.atTop
          (Metric.closedBall (0 : Fin n → Real) 1) :=
      helperForTheorem_25_1_remainderSequence_tendstoUniformlyOn_closedUnitBall
        (f := f) (x := x) (g := g) (ρ := ρ) hproper hxInt hρpos hρsubInt hdir hsub
    have hlimit :
        Filter.Tendsto (erealGradientErrorQuotient f x g)
          (nhdsWithin x
            ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f))
          (nhds 0) := by
      -- The metric formulation reduces to a single eventual `ε`-estimate on the punctured filter.
      rw [Metric.tendsto_nhds]
      intro eps heps
      exact helperForTheorem_25_1_uniformBound_implies_errorQuotient_eventually_small
        (f := f) (x := x) (g := g) (ρ := ρ) (ρ' := ρ') hf hxFinite hsub hρpos hρ'pos
        hρ'finite hRuniform heps
    exact ⟨hxFinite.1, hxFinite.2, hlimit⟩
  · -- The same closed ball provides eventual punctured finite-valued control.
    have hnear :
        {z : Fin n → Real |
            z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧ f z ≠ ⊥} ∈ nhds x := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds x hρ'pos) ?_
      intro z hz
      have hzClosed : z ∈ Metric.closedBall x ρ' := by
        exact Metric.mem_closedBall.mpr (le_of_lt hz)
      have hzFinite : f z ≠ ⊤ ∧ f z ≠ ⊥ := hρ'finite z hzClosed
      have hzDom : z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
        simpa [effectiveDomain_eq] using (lt_top_iff_ne_top.mpr hzFinite.1)
      exact ⟨hzDom, hzFinite.2⟩
    exact mem_nhdsWithin_of_mem_nhds hnear

-- Proof sketch: use Theorem 23.2 to convert subgradients into linear minorants of the upper
-- directional derivative, show differentiability identifies that directional derivative with the
-- linear functional given by the chosen gradient witness, and then apply `erealGradient_unique`.
-- For the converse, a unique vector subgradient determines all directional difference quotients,
-- forcing the first-order error term to vanish and hence giving differentiability at `x`.
/-- Theorem 25.1: let `f` be convex and finite at `x`. Then differentiability at `x` makes the
chosen gradient witness `∇ f(x)` the unique Euclidean subgradient of `f` at `x`, so in particular
`f z ≥ f x + ⟨∇ f(x), z - x⟩` for every `z`. Conversely, if `f` has a unique Euclidean
subgradient at `x`, then `f` is differentiable at `x`. -/
theorem convexFunction_differentiableAt_iff_gradient_is_unique_subgradient {n : Nat}
    (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) (x : Fin n → Real)
    (hx : f x ≠ ⊤ ∧ f x ≠ ⊥) :
    (∀ hdiff : ERealDifferentiableAt f x,
      IsSubgradientAt f x (dotProductEquiv Real (Fin n) (erealGradientAt hdiff)) ∧
      (∀ z : Fin n → Real,
        f z ≥ f x + ((((erealGradientAt hdiff) ⬝ᵥ (z - x)) : Real) : EReal)) ∧
      ∀ g : Fin n → Real,
        IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) → g = erealGradientAt hdiff) ∧
    ((∃! g : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) g)) →
      ERealDifferentiableAt f x) := by
  constructor
  · intro hdiff
    -- The differentiability witness determines both the directional derivative and the subgradient.
    rcases
        helperForTheorem_25_1_gradient_gives_subgradient_and_directionalDerivative
          (hf := hf) (hdiff := hdiff) with
      ⟨hdirEq, hsubGrad⟩
    refine ⟨hsubGrad, ?_, ?_⟩
    · -- The explicit affine lower bound is just the subgradient inequality specialized at `z`.
      intro z
      simpa [dotProduct_comm] using hsubGrad z
    · intro g hg
      have hiffg :=
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          f hf x hx (dotProductEquiv Real (Fin n) g)).1
      have hminorG :
          ∀ y : Fin n → Real,
            ((((dotProductEquiv Real (Fin n) g) y : Real) : Real) : EReal) ≤
              upperDirectionalDerivativeAt f x y :=
        hiffg.mp hg
      -- Compare both candidate subgradients against the already identified linear derivative.
      have hdotEq :
          ∀ y : Fin n → Real, g ⬝ᵥ y = erealGradientAt hdiff ⬝ᵥ y := by
        intro y
        have hyLe :
            (((g ⬝ᵥ y : Real) : EReal)) ≤
              ((((erealGradientAt hdiff) ⬝ᵥ y : Real) : EReal)) := by
          calc
            (((g ⬝ᵥ y : Real) : EReal)) =
                ((((dotProductEquiv Real (Fin n) g) y : Real) : Real) : EReal) := by
                  simp
            _ ≤ upperDirectionalDerivativeAt f x y := hminorG y
            _ = ((((erealGradientAt hdiff) ⬝ᵥ y : Real) : Real) : EReal) := hdirEq y
        have hnegLe :
            ((((erealGradientAt hdiff) ⬝ᵥ y : Real) : EReal)) ≤
              (((g ⬝ᵥ y : Real) : EReal)) := by
          have hnegLe' :
              (((g ⬝ᵥ (-y) : Real) : EReal)) ≤
                ((((erealGradientAt hdiff) ⬝ᵥ (-y) : Real) : EReal)) := by
            calc
              (((g ⬝ᵥ (-y) : Real) : EReal)) =
                  ((((dotProductEquiv Real (Fin n) g) (-y) : Real) : Real) : EReal) := by
                    simp
              _ ≤ upperDirectionalDerivativeAt f x (-y) := hminorG (-y)
              _ = ((((erealGradientAt hdiff) ⬝ᵥ (-y) : Real) : Real) : EReal) := hdirEq (-y)
          have hnegReal :
              -(g ⬝ᵥ y) ≤ -(erealGradientAt hdiff ⬝ᵥ y) := by
            simpa [dotProduct_comm] using hnegLe'
          have hposReal :
              erealGradientAt hdiff ⬝ᵥ y ≤ g ⬝ᵥ y := by
            linarith
          exact (EReal.coe_le_coe_iff).2 hposReal
        have hyEq :
            (((g ⬝ᵥ y : Real) : EReal)) =
              ((((erealGradientAt hdiff) ⬝ᵥ y : Real) : EReal)) := le_antisymm hyLe hnegLe
        exact (EReal.coe_eq_coe_iff).1 hyEq
      exact helperForTheorem_25_1_eq_of_dotProduct_eq hdotEq
  · intro huniq
    -- Route correction: the easy converse reductions are handled now; only the analytic upgrade
    -- from linear directional derivative to the full differentiability filter remains isolated in
    -- the dedicated helper.
    rcases
        helperForTheorem_25_1_uniqueSubgradient_implies_linearDirectionalDerivative
          (hf := hf) (x := x) hx huniq with
      ⟨g, hproper, hxInt, hdir⟩
    exact
      helperForTheorem_25_1_linearDirectionalDerivative_implies_ERealDifferentiableAt
        (hproper := hproper) (hxInt := hxInt) (hdir := hdir)

/-- Variant of Theorem 25.1: for a convex function finite at `x`, differentiability at `x` is
equivalent to the subtype of Euclidean subgradients `g` with `dotProductEquiv ℝ (Fin n) g ∈ ∂ f x`
being a `Unique` type. -/
theorem convexFunction_differentiableAt_iff_unique_subgradient_subtype {n : Nat}
    (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) (x : Fin n → Real)
    (hx : f x ≠ ⊤ ∧ f x ≠ ⊥) :
    ERealDifferentiableAt f x ↔
      Nonempty (Unique {g : Fin n → Real // dotProductEquiv ℝ (Fin n) g ∈ ∂ f x}) := by
  constructor
  · intro hdiff
    rcases
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient f hf x hx).1 hdiff with
      ⟨hsub, _hlower, huniq⟩
    refine ⟨?_⟩
    refine
      { default := ⟨erealGradientAt hdiff, by simpa using hsub⟩
        uniq := ?_ }
    intro y
    apply Subtype.ext
    exact huniq y.1 y.2
  · rintro ⟨hUnique⟩
    have hExistsUnique :
        ∃! g : Fin n → Real, dotProductEquiv ℝ (Fin n) g ∈ ∂ f x := by
      refine ⟨hUnique.default.1, hUnique.default.2, ?_⟩
      intro g hg
      exact congrArg Subtype.val (hUnique.uniq ⟨g, hg⟩)
    exact
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient f hf x hx).2
        (by simpa using hExistsUnique)

-- Proof sketch: apply Theorem 25.1 to obtain the unique subgradient determined by the gradient
-- witness. Its existence makes `f` proper by Theorem 23.3, while the singleton subdifferential is
-- bounded, so Theorem 23.4 yields `x ∈ interior (dom f)`.
/-- Corollary 25.1.1: if `f` is convex and differentiable at `x`, then `f` is proper on `ℝ^n` and
`x` lies in the interior of the effective domain `dom f`. -/
theorem convexFunction_proper_and_mem_interior_of_differentiableAt {n : Nat}
    (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) (x : Fin n → Real)
    (hdiff : ERealDifferentiableAt f x) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f ∧
      x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  have hx : f x ≠ ⊤ ∧ f x ≠ ⊥ := ERealDifferentiableAt.finiteAt hdiff
  have hcore :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient f hf x hx).1 hdiff
  have huniq : ∃! g : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) := by
    -- The gradient supplied by differentiability is the unique Euclidean subgradient at `x`.
    refine ⟨erealGradientAt hdiff, hcore.1, ?_⟩
    intro g hg
    exact hcore.2.2 g hg
  -- The Section 25 helper packages the properness and interior conclusions from uniqueness.
  rcases
      helperForTheorem_25_1_uniqueSubgradient_implies_linearDirectionalDerivative
        (hf := hf) (x := x) hx huniq with
    ⟨g, hproper, hxInt, _hdir⟩
  exact ⟨hproper, hxInt⟩

-- Proof sketch: choose the gradient witness supplied by differentiability, evaluate the
-- first-order expansion along the ray `t ↦ x + t • y`, and use `y ≠ 0` so the normalized error
-- term turns into the directional difference quotient converging to the pairing with the gradient.
/-- Helper for Theorem 25.1.1: a positive step in a nonzero direction cannot stay at the base
point. -/
lemma helperForTheorem_25_1_1_nonzero_ray_ne {n : Nat} {x y : Fin n → Real}
    (hy : y ≠ 0) {t : Real} (ht : 0 < t) :
    x + t • y ≠ x := by
  intro hEq
  have hsmul : t • y = 0 := by
    -- Cancel the common `x` term to isolate the scaled direction vector.
    exact add_left_cancel (by simpa using hEq : x + t • y = x + 0)
  -- A positive scalar cannot annihilate a nonzero vector over `ℝ`.
  rcases smul_eq_zero.mp hsmul with ht0 | hy0
  · exact (ne_of_gt ht) ht0
  · exact hy hy0

/-- Helper for Theorem 25.1.1: the positive ray `t ↦ x + t • y` tends to `x` through the
punctured neighborhood when `y ≠ 0`. -/
lemma helperForTheorem_25_1_1_tendsto_ray_to_puncturedNeighborhood
    {n : Nat} {x y : Fin n → Real} (hy : y ≠ 0) :
    Filter.Tendsto (fun t : Real => x + t • y)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhdsWithin x {z | z ≠ x}) := by
  have hcont : ContinuousAt (fun t : Real => x + t • y) (0 : Real) := by
    fun_prop
  have hwithin : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0), x + t • y ∈ ({z | z ≠ x} : Set _) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact helperForTheorem_25_1_1_nonzero_ray_ne (x := x) (y := y) hy ht
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hwithin
  simpa [zero_smul] using (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-- Helper for Theorem 25.1.1: an eventual positive-ray effective-domain hypothesis upgrades to
eventual membership in the punctured effective-domain set used by `HasERealGradientAt`. -/
lemma helperForTheorem_25_1_1_eventually_mem_puncturedEffectiveDomain_of_eventually_mem_effectiveDomain_ray
    {n : Nat} {f : (Fin n → Real) → EReal} {x y : Fin n → Real}
    (hy : y ≠ 0)
    (hray : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
      x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
      x + t • y ∈
        ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  have hpos : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0), 0 < t := by
    -- The source filter only sees positive parameters.
    simpa using
      (self_mem_nhdsWithin : Set.Ioi (0 : Real) ∈ nhdsWithin (0 : Real) (Set.Ioi 0))
  -- Combine positivity with the assumed eventual effective-domain membership along the ray.
  filter_upwards [hpos, hray] with t ht hmem
  exact ⟨helperForTheorem_25_1_1_nonzero_ray_ne (x := x) (y := y) hy ht, hmem⟩

/-- Helper for Theorem 25.1.1: under the eventual positive-ray effective-domain hypothesis, the
ray parameterization tends to the punctured effective-domain neighborhood of `x`. -/
lemma helperForTheorem_25_1_1_tendsto_ray_to_puncturedEffectiveDomain
    {n : Nat} {f : (Fin n → Real) → EReal} {x y : Fin n → Real}
    (hy : y ≠ 0)
    (hray : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
      x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    Filter.Tendsto (fun t : Real => x + t • y)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhdsWithin x
        ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  have hcont : ContinuousAt (fun t : Real => x + t • y) (0 : Real) := by
    -- The ray map is continuous as an affine function of the scalar parameter.
    fun_prop
  have hwithin :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        x + t • y ∈
          ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    helperForTheorem_25_1_1_eventually_mem_puncturedEffectiveDomain_of_eventually_mem_effectiveDomain_ray
      (x := x) (y := y) hy hray
  -- The continuous ray map tends to `x`, and `hwithin` upgrades this to a within-limit.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ hwithin
  simpa [zero_smul] using (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-- Theorem 25.1.1: if `f` is differentiable at `x`, then for every nonzero direction `y`, the
right directional difference quotient converges to `⟨∇ f(x), y⟩`. -/
theorem ERealDifferentiableAt.tendsto_directionalDifferenceQuotient {n : Nat}
    {f : (Fin n → Real) → EReal} {x y : Fin n → Real}
    (hf : ERealDifferentiableAt f x) (hy : y ≠ 0) :
    Filter.Tendsto (directionalDifferenceQuotientAt f x y)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds ((((erealGradientAt hf) ⬝ᵥ y : Real) : EReal))) := by
  let g : Fin n → Real := erealGradientAt hf
  have hg : HasERealGradientAt f x g := by
    simpa [g] using ERealDifferentiableAt.hasERealGradientAt (hf := hf)
  have hx : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
    exact ERealDifferentiableAt.finiteAt (hf := hf)
  have hfinite :
      ∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧ f z ≠ ⊥ :=
    ERealDifferentiableAt.eventually_finiteValuedWithin_punctured (hf := hf)
  have hfiniteRay :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧
          f (x + t • y) ≠ ⊥ := by
    exact
      (helperForTheorem_25_1_1_tendsto_ray_to_puncturedNeighborhood (x := x) (y := y) hy).eventually
        hfinite
  have hray :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        x + t • y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    exact hfiniteRay.mono fun _ ht => ht.1
  have hrayInto :
      Filter.Tendsto (fun t : Real => x + t • y)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhdsWithin x
          ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :=
    helperForTheorem_25_1_1_tendsto_ray_to_puncturedEffectiveDomain
      (x := x) (y := y) hy hray
  have herrorRay :
      Filter.Tendsto (fun t : Real => erealGradientErrorQuotient f x g (x + t • y))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds 0) :=
    hg.2.2.comp hrayInto
  have hrealEq :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        ((f (x + t • y)).toReal - (f x).toReal) / t =
          ‖y‖ * erealGradientErrorQuotient f x g (x + t • y) + g ⬝ᵥ y := by
    filter_upwards [self_mem_nhdsWithin, hfiniteRay] with t ht htFinite
    have htne : t ≠ 0 := ne_of_gt ht
    have hyNorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have htop : f (x + t • y) ≠ ⊤ :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) htFinite.1
    have hsub :
        x + t • y - x = t • y := by
      simp [sub_eq_add_neg, add_assoc]
    have hdot :
        g ⬝ᵥ (t • y) = t * (g ⬝ᵥ y) := by
      simpa [smul_eq_mul] using (dotProduct_smul t g y)
    have hnorm :
        ‖t • y‖ = t * ‖y‖ := by
      simpa [Real.norm_of_nonneg (le_of_lt ht)] using norm_smul t y
    have htoRealSub :
        (f (x + t • y) - f x).toReal = (f (x + t • y)).toReal - (f x).toReal := by
      simpa using EReal.toReal_sub htop htFinite.2 hx.1 hx.2
    rw [erealGradientErrorQuotient, hsub, hdot, hnorm, htoRealSub]
    field_simp [htne, hyNorm]
    ring
  have hrealTendsto :
      Filter.Tendsto (fun t : Real => ((f (x + t • y)).toReal - (f x).toReal) / t)
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (g ⬝ᵥ y)) := by
    have hAffine :
        Filter.Tendsto
          (fun t : Real => ‖y‖ * erealGradientErrorQuotient f x g (x + t • y) + g ⬝ᵥ y)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds (g ⬝ᵥ y)) := by
      have hcont : Continuous (fun r : Real => ‖y‖ * r + g ⬝ᵥ y) := by
        fun_prop
      simpa using hcont.continuousAt.tendsto.comp herrorRay
    refine Filter.Tendsto.congr' ?_ hAffine
    filter_upwards [hrealEq] with t htEq
    exact htEq.symm
  have hcoereal :
      Filter.Tendsto
        (fun t : Real => ((((f (x + t • y)).toReal - (f x).toReal) / t : Real) : EReal))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds (((g ⬝ᵥ y : Real) : EReal))) := by
    exact (EReal.tendsto_coe).2 hrealTendsto
  have hcoereal' :
      Filter.Tendsto
        (fun t : Real => ((((f (x + t • y)).toReal - (f x).toReal) / t : Real) : EReal))
        (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhds ((((erealGradientAt hf) ⬝ᵥ y : Real) : EReal))) := by
    simpa [g] using hcoereal
  have hquotEq :
      ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0),
        directionalDifferenceQuotientAt f x y t =
          ((((f (x + t • y)).toReal - (f x).toReal) / t : Real) : EReal) := by
    filter_upwards [self_mem_nhdsWithin, hfiniteRay] with t ht htFinite
    have htop : f (x + t • y) ≠ ⊤ :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) htFinite.1
    simp [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal htop htFinite.2, EReal.coe_toReal hx.1 hx.2]
  exact Filter.Tendsto.congr' (by
    filter_upwards [hquotEq] with t htEq
    exact htEq.symm) hcoereal'

/-- A function has `j`th coordinate partial derivative `L` at `x` when the difference quotient
along the `j`th standard basis vector `Pi.single j 1` tends to `L` as the scalar parameter tends
to `0` from both sides. -/
def HasCoordinatePartialDerivativeAt {n : Nat} (f : (Fin n → Real) → EReal)
    (x : Fin n → Real) (j : Fin n) (L : EReal) : Prop :=
  Filter.Tendsto (directionalDifferenceQuotientAt f x (Pi.single j (1 : Real)))
    (𝓝[>] (0 : Real))
    (𝓝 L) ∧
  Filter.Tendsto (directionalDifferenceQuotientAt f x (Pi.single j (1 : Real)))
    (𝓝[<] (0 : Real))
    (𝓝 L)

/-- Helper for Theorem 25.1.2: the `j`th standard basis vector in `ℝⁿ` is nonzero. -/
lemma helperForTheorem_25_1_2_basisVector_ne_zero {n : Nat} (j : Fin n) :
    (Pi.single j (1 : Real) : Fin n → Real) ≠ 0 := by
  intro hzero
  have hvalue := congrArg (fun v : Fin n → Real => v j) hzero
  simp at hvalue

-- Proof sketch: apply Theorem 25.1.1 to the directions `e_j` and `-e_j`, then use the
-- bilateral-directional-derivative symmetry from Section 23 to identify the left-hand quotient
-- along `e_j` with the right-hand quotient along `-e_j`; both one-sided limits equal the pairing
-- of the chosen gradient witness with the `j`th standard basis vector.
/-- Theorem 25.1.2: if `f` is differentiable at `x`, then for each coordinate index `j`, the
partial derivative with respect to `ξ_j`, viewed as the bilateral directional derivative along
the standard basis vector `e_j = Pi.single j 1`, exists and equals `⟨∇ f(x), e_j⟩`. -/
theorem ERealDifferentiableAt.hasCoordinatePartialDerivativeAt {n : Nat}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hf : ERealDifferentiableAt f x) (j : Fin n) :
    HasCoordinatePartialDerivativeAt f x j
      (((((erealGradientAt hf) ⬝ᵥ Pi.single j (1 : Real)) : Real) : EReal)) := by
  let e : Fin n → Real := Pi.single j (1 : Real)
  have he : e ≠ 0 := helperForTheorem_25_1_2_basisVector_ne_zero j
  have hright :
      Filter.Tendsto (directionalDifferenceQuotientAt f x e)
        (𝓝[>] (0 : Real))
        (𝓝 ((((erealGradientAt hf) ⬝ᵥ e : Real) : EReal))) :=
    ERealDifferentiableAt.tendsto_directionalDifferenceQuotient (hf := hf) (y := e) he
  have hnegRight :
      Filter.Tendsto (directionalDifferenceQuotientAt f x (-e))
        (𝓝[>] (0 : Real))
        (𝓝 ((((erealGradientAt hf) ⬝ᵥ (-e) : Real) : EReal))) :=
    ERealDifferentiableAt.tendsto_directionalDifferenceQuotient
      (hf := hf) (y := -e) (by simpa using neg_ne_zero.mpr he)
  have hdotNeg :
      (erealGradientAt hf) ⬝ᵥ (-e) = -((erealGradientAt hf) ⬝ᵥ e) := by
    simpa [smul_eq_mul] using (dotProduct_smul (-1 : Real) (erealGradientAt hf) e)
  have hleft :
      Filter.Tendsto (directionalDifferenceQuotientAt f x e)
        (𝓝[<] (0 : Real))
        (𝓝 ((((erealGradientAt hf) ⬝ᵥ e : Real) : EReal))) := by
    have hleft_from_right :
        ∀ L : EReal,
          Filter.Tendsto (directionalDifferenceQuotientAt f x (-e)) (𝓝[>] (0 : Real)) (𝓝 L) →
            Filter.Tendsto (directionalDifferenceQuotientAt f x e) (𝓝[<] (0 : Real)) (𝓝 (-L)) :=
      (bilateralDirectionalDerivative_iff_exists_neg_direction (f := f) (x := x) (y := e)
        (ERealDifferentiableAt.finiteAt (hf := hf))).1
    have hnegRight' :
        Filter.Tendsto (directionalDifferenceQuotientAt f x (-e))
          (𝓝[>] (0 : Real))
          (𝓝 (-((((erealGradientAt hf) ⬝ᵥ e : Real) : EReal)))) := by
      simpa [hdotNeg] using hnegRight
    simpa using hleft_from_right (-((((erealGradientAt hf) ⬝ᵥ e : Real) : EReal))) hnegRight'
  simpa [e] using And.intro hright hleft

end Section25
end Chap05
