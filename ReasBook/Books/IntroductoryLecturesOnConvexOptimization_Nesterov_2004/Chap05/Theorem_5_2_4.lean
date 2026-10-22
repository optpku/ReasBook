/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement SelfConcordantAuxiliaryFunction
  IntermediateNewtonQuadraticConvergenceRegion

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The scaled suboptimality `Δ_f(x) = M_f^2 (f(x) - f^*)` used in the path-following bounds. -/
def selfConcordantScaledSuboptimality
    (f : E → ℝ) (Mf : NNReal) (x : E) (fStar : ℝ) : ℝ :=
  (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar)

-- Proof sketch: unfold `selfConcordantScaledSuboptimality`.
/-- Expanding `selfConcordantScaledSuboptimality f M_f x f*` gives `M_f^2 (f(x) - f*)`. -/
theorem selfConcordantScaledSuboptimality_def
    (f : E → ℝ) (Mf : NNReal) (x : E) (fStar : ℝ) :
    selfConcordantScaledSuboptimality f Mf x fStar =
      (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) := by
  -- This wrapper theorem is purely definitional.
  rfl

/-- The diameter of the initial sublevel set `{x ∈ dom | f x ≤ f(y₀)}` measured in the local norm
at the base point `y₀`. -/
def pathFollowingLevelSetDiameter
    {dom : Set E} (f : E → ℝ) (y0 : dom) : ℝ :=
  sSup
    ((fun p : E × E ↦ hessianLocalNorm f (y0 : E) (p.1 - p.2)) ''
      {p : E × E |
        p.1 ∈ dom ∧ p.2 ∈ dom ∧ f p.1 ≤ f (y0 : E) ∧ f p.2 ≤ f (y0 : E)})

-- Proof sketch: unfold `pathFollowingLevelSetDiameter`.
/-- Expanding `pathFollowingLevelSetDiameter f y₀` gives the supremum of the local-norm distances
between pairs of points in the initial sublevel set. -/
theorem pathFollowingLevelSetDiameter_def
    {dom : Set E} (f : E → ℝ) (y0 : dom) :
    pathFollowingLevelSetDiameter f y0 =
      sSup
        ((fun p : E × E ↦ hessianLocalNorm f (y0 : E) (p.1 - p.2)) ''
          {p : E × E |
            p.1 ∈ dom ∧ p.2 ∈ dom ∧ f p.1 ≤ f (y0 : E) ∧ f p.2 ≤ f (y0 : E)}) := by
  -- This wrapper theorem is purely definitional.
  rfl

/-- A chosen inverse value of the self-concordant auxiliary function `ω(t) = t - log(1 + t)`. -/
noncomputable def selfConcordantOmegaInverse (s : ℝ) : Set.Ioi (-1 : ℝ) :=
  Function.invFun ω s

-- Proof sketch: unfold `selfConcordantOmegaInverse`.
/-- Expanding `selfConcordantOmegaInverse s` gives the chosen inverse value of
`selfConcordantOmega` at `s`. -/
theorem selfConcordantOmegaInverse_def (s : ℝ) :
    selfConcordantOmegaInverse s = Function.invFun ω s := by
  -- This wrapper theorem is purely definitional.
  rfl

/-- The path-following threshold argument
`((1 - β(τ)) (1 - 2 β(τ))) / 2` always lies in `(-1, ∞)`. -/
theorem pathFollowingQuadraticRegionTimeThreshold_mem_Ioi (τ : ℝ) :
    -1 <
      ((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2 := by
  have hsquare : 0 ≤ (4 * pathFollowingCenteringBeta τ - 3) ^ (2 : ℕ) := sq_nonneg _
  nlinarith

/-- The threshold on `t_k` ensuring that the `k`-th path-following iterate has entered the
quadratic-convergence region of the intermediate Newton method. -/
def pathFollowingQuadraticRegionTimeThreshold
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) : ℝ :=
  ω
      (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
        pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)) /
    ((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
      selfConcordantOmegaInverse
        (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar)))

-- Proof sketch: unfold `pathFollowingQuadraticRegionTimeThreshold`.
/-- Expanding `pathFollowingQuadraticRegionTimeThreshold` gives the scalar threshold on `t_k`
obtained by rearranging the entry condition from the proof of `(5.2.22)`. -/
theorem pathFollowingQuadraticRegionTimeThreshold_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) :
    pathFollowingQuadraticRegionTimeThreshold f Mf y0 xStar τ =
      ω
          (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
            pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)) /
        ((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
          selfConcordantOmegaInverse
            (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) := by
  -- This wrapper theorem is purely definitional.
  rfl

/-- The explicit lower bound on the iteration index in `(5.2.22)` forcing the path-following
iterates into the quadratic-convergence region. -/
def pathFollowingQuadraticRegionEntryBound
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) : ℝ :=
  Real.sqrt
    (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar) /
        (pathFollowingGammaRadius τ * pathFollowingKappa τ) *
      Real.log
        (((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
            selfConcordantOmegaInverse
              (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) /
          ω
            (⟨((1 - pathFollowingCenteringBeta τ) * (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
              pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ))))

-- Proof sketch: unfold `pathFollowingQuadraticRegionEntryBound`.
/-- Expanding `pathFollowingQuadraticRegionEntryBound` recovers the square-root bound from
display `(5.2.22)`, written with `pathFollowingGammaRadius τ` and `pathFollowingKappa τ`. -/
theorem pathFollowingQuadraticRegionEntryBound_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) (y0 : dom) (xStar : E) (τ : ℝ) :
    pathFollowingQuadraticRegionEntryBound f Mf y0 xStar τ =
      Real.sqrt
        (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar) /
            (pathFollowingGammaRadius τ * pathFollowingKappa τ) *
          Real.log
            (((Mf : ℝ) * pathFollowingLevelSetDiameter f y0 *
                selfConcordantOmegaInverse
                  (selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))) /
              ω
                (⟨((1 - pathFollowingCenteringBeta τ) *
                    (1 - 2 * pathFollowingCenteringBeta τ)) / 2,
                  pathFollowingQuadraticRegionTimeThreshold_mem_Ioi τ⟩ : Set.Ioi (-1 : ℝ)))) := by
  -- This wrapper theorem is purely definitional.
  rfl

/-- Helper for Theorem 5 2 4: once the path-following iterates enter
`𝒟[f | dom, M_f]`, the one-step stability hypothesis propagates that membership to every later
iterate. -/
lemma intermediateNewtonQuadraticConvergenceRegion_stable_from_le
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (hstable :
      ∀ k : ℕ,
        process.y k ∈ 𝒟[f | dom, Mf] →
          process.y (k + 1) ∈ 𝒟[f | dom, Mf])
    {m n : ℕ} (hmn : m ≤ n)
    (hm : process.y m ∈ 𝒟[f | dom, Mf]) :
    process.y n ∈ 𝒟[f | dom, Mf] := by
  -- Rewrite the later index as `m + d` so that repeated use of `hstable` matches the source
  -- forward-invariance argument.
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, rfl⟩
  induction d with
  | zero =>
      simpa using hm
  | succ d ih =>
      -- One more application of the one-step stability hypothesis advances the induction.
      have hstep : process.y ((m + d) + 1) ∈ 𝒟[f | dom, Mf] := hstable (m + d) ih
      simpa [Nat.add_assoc] using hstep

/-- Helper for Theorem 5 2 4: if the initial point `y₀` is not yet in the intermediate Newton
quadratic-convergence region, then its scaled gap above the minimizer value is strictly positive.
-/
lemma scaled_suboptimality_pos_of_not_mem_intermediateNewtonQuadraticConvergenceRegion
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (xStar : E) (hmin : IsMinOn f dom xStar)
    (hy0_not : (y0 : E) ∉ 𝒟[f | dom, Mf]) :
    0 < selfConcordantScaledSuboptimality f (Mf : NNReal) (y0 : E) (f xStar) := by
  have hmin_y0 : f xStar ≤ f (y0 : E) := (isMinOn_iff.mp hmin) _ y0.2
  have hgap_nonneg : 0 ≤ f (y0 : E) - f xStar := sub_nonneg.mpr hmin_y0
  have hscaled_nonneg :
      0 ≤ selfConcordantScaledSuboptimality f (Mf : NNReal) (y0 : E) (f xStar) := by
    -- The scaled gap is a nonnegative scalar multiple of the nonnegative objective gap.
    rw [selfConcordantScaledSuboptimality_def]
    positivity
  by_contra hscaled_not_pos
  have hscaled_eq_zero :
      selfConcordantScaledSuboptimality f (Mf : NNReal) (y0 : E) (f xStar) = 0 := by
    exact le_antisymm (le_of_not_gt hscaled_not_pos) hscaled_nonneg
  have hgap_eq_zero : f (y0 : E) - f xStar = 0 := by
    rw [selfConcordantScaledSuboptimality_def] at hscaled_eq_zero
    exact (mul_eq_zero.mp hscaled_eq_zero).resolve_left (by positivity)
  have hy0_min : IsMinOn f dom (y0 : E) := by
    -- Vanishing gap identifies `y₀` itself as a minimizer on `dom`.
    refine isMinOn_iff.mpr ?_
    intro z hz
    have hmin_z : f xStar ≤ f z := (isMinOn_iff.mp hmin) z hz
    have hy0_eq : f (y0 : E) = f xStar := by
      linarith
    linarith
  have hgrad0 : ∇ f (y0 : E) = 0 :=
    gradient_eq_zero_at_selfconcordant_minimizer
      (dom := dom) (Mf := (Mf : NNReal)) (f := f)
      (inferInstance : IsOpen dom) y0 hy0_min
  have hy0_mem : (y0 : E) ∈ 𝒟[f | dom, Mf] := by
    -- A minimizer is stationary, so its Newton decrement is zero and therefore lies below the
    -- region threshold `1 / (2 M_f)`.
    rw [mem_intermediateNewtonQuadraticConvergenceRegion_iff (dom := dom) (f := f)
      (Mf := Mf) y0.2]
    have hlambda_eq_zero : λ[f; (y0 : E) | y0.2] = 0 := by
      rw [NewtonDecrement.ofPosDefMem_def]
      simp [hgrad0]
    simpa [hlambda_eq_zero] using
      (show (0 : ℝ) < 1 / (2 * (((Mf : NNReal) : ℝ))) by positivity)
  exact hy0_not hy0_mem

/-- Helper for Theorem 5 2 4: once the initial scaled gap is strictly positive, the local-norm
diameter of the initial sublevel set is also strictly positive because the pair `(y₀, x*)`
already contributes a positive distance. -/
lemma pathFollowingLevelSetDiameter_pos_of_scaled_suboptimality_pos
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (xStar : E) (hmin : IsMinOn f dom xStar)
    (hscaled :
      0 < selfConcordantScaledSuboptimality f (Mf : NNReal) (y0 : E) (f xStar)) :
    0 < pathFollowingLevelSetDiameter f y0 := by
  have hgap_pos : 0 < f (y0 : E) - f xStar := by
    -- The positive scaled gap forces the raw objective gap to be positive because `M_f > 0`.
    rw [selfConcordantScaledSuboptimality_def] at hscaled
    positivity
  have hxStar_mem : xStar ∈ dom := hmin.1
  have hy0_ne : (y0 : E) ≠ xStar := by
    intro hy0_eq
    have hzero :
        selfConcordantScaledSuboptimality f (Mf : NNReal) (y0 : E) (f xStar) = 0 := by
      rw [selfConcordantScaledSuboptimality_def, hy0_eq]
      ring
    exact (show False by simpa [hzero] using hscaled).elim
  have hnorm_pos : 0 < hessianLocalNorm f (y0 : E) ((y0 : E) - xStar) := by
    -- Positive definiteness turns the nonzero direction `y₀ - x*` into a positive local norm.
    rw [hessianLocalNorm_def]
    apply Real.sqrt_pos.mpr
    exact HasPositiveDefiniteHessianOn.posdef y0.2 (sub_ne_zero.mpr hy0_ne)
  have hvalue_le :
      hessianLocalNorm f (y0 : E) ((y0 : E) - xStar) ≤ pathFollowingLevelSetDiameter f y0 := by
    -- The witness pair `(y₀, x*)` belongs to the defining sublevel set, so its local distance
    -- is bounded by the supremum.
    rw [pathFollowingLevelSetDiameter_def]
    apply le_sSup
    refine ⟨((y0 : E), xStar), ?_, rfl⟩
    refine ⟨y0.2, hxStar_mem, le_rfl, ?_⟩
    exact (isMinOn_iff.mp hmin) _ y0.2
  exact lt_of_lt_of_le hnorm_pos hvalue_le

-- Proof sketch: if no iterate up to `N` has yet entered the quadratic-convergence region, the
-- hypothesis `hdecay` gives the exponential estimate for `t_N`. The lower bound `hN` makes this
-- estimate at most `pathFollowingQuadraticRegionTimeThreshold f Mf y₀ x* τ`, so `hentry`
-- forces `y_N` into the region, a contradiction. Therefore some earlier iterate enters the
-- region, and the forward-invariance hypothesis `hstable` propagates that membership to `y_N`.
/-- Theorem 5.2.4: for a path-following process generated by `(5.2.16)`, every index above the
bound `(5.2.22)` yields an iterate in the quadratic-convergence region of the intermediate Newton
method. The textbook statement writes `𝒬_f`; here the conclusion is formalized by the region
`𝒟[f | dom, M_f]` proved in the accompanying argument. -/
theorem selfConcordantPathFollowing_mem_intermediateNewtonQuadraticConvergenceRegion_of_large_index
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (htau : τ ≤ 0.23) (y0 : dom) (xStar : E)
    (hmin : IsMinOn f dom xStar)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (hstable :
      ∀ k : ℕ,
        process.y k ∈ 𝒟[f | dom, Mf] →
          process.y (k + 1) ∈ 𝒟[f | dom, Mf])
    (hdecay :
      ∀ m : ℕ,
        (∀ k : ℕ, k ≤ m →
          process.y k ∉ 𝒟[f | dom, Mf]) →
        (process.t m : ℝ) ≤
          Real.exp
            (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (m : ℝ) ^ (2 : ℕ) /
                selfConcordantScaledSuboptimality f Mf (y0 : E) (f xStar))))
    (hentry :
      ∀ m : ℕ,
        (process.t m : ℝ) ≤ pathFollowingQuadraticRegionTimeThreshold f (Mf : NNReal) y0 xStar τ →
          process.y m ∈ 𝒟[f | dom, Mf])
    {N : ℕ}
    (hN : pathFollowingQuadraticRegionEntryBound f (Mf : NNReal) y0 xStar τ ≤ (N : ℝ)) :
    process.y N ∈ 𝒟[f | dom, Mf] := by
  classical
  -- Split on whether the process has already entered the quadratic-convergence region by time `N`.
  by_cases hentered : ∃ k : ℕ, k ≤ N ∧ process.y k ∈ 𝒟[f | dom, Mf]
  · rcases hentered with ⟨k, hkN, hk_mem⟩
    -- Forward invariance propagates the first available witness all the way to index `N`.
    exact
      intermediateNewtonQuadraticConvergenceRegion_stable_from_le
        y0 process hstable hkN hk_mem
  · have hno_entry :
        ∀ k : ℕ, k ≤ N → process.y k ∉ 𝒟[f | dom, Mf] := by
      intro k hk
      exact fun hk_mem ↦ hentered ⟨k, hk, hk_mem⟩
    have hdecayN := hdecay N hno_entry
    have hy0_not : (y0 : E) ∉ 𝒟[f | dom, Mf] := by
      -- The no-entry hypothesis specializes at `k = 0` and `process.y 0 = y₀`.
      simpa [process.y_zero] using hno_entry 0 (Nat.zero_le N)
    have hscaled_pos :
        0 < selfConcordantScaledSuboptimality f (Mf : NNReal) (y0 : E) (f xStar) :=
      scaled_suboptimality_pos_of_not_mem_intermediateNewtonQuadraticConvergenceRegion
        y0 xStar hmin hy0_not
    have hdiam_pos : 0 < pathFollowingLevelSetDiameter f y0 :=
      pathFollowingLevelSetDiameter_pos_of_scaled_suboptimality_pos
        y0 xStar hmin hscaled_pos
    -- Route correction: the remaining work is the source-faithful scalar bridge turning the
    -- explicit index lower bound `hN` into the threshold inequality required by `hentry`.
    -- The geometric part is now established: `hno_entry 0` gives the strict initial gap and the
    -- pair `(y₀, x*)` gives a positive level-set diameter.
    -- TODO: derive
    -- `(process.t N : ℝ) ≤ pathFollowingQuadraticRegionTimeThreshold f (Mf : NNReal) y0 xStar τ`
    -- from `hdecayN`, `hN`, `hscaled_pos`, and `hdiam_pos` by comparing the unfolded formulas for
    -- `pathFollowingQuadraticRegionEntryBound` and `pathFollowingQuadraticRegionTimeThreshold`.
    -- The remaining blocker is the scalar side: the current theorem hypotheses do not yet give
    -- the sign information needed for `pathFollowingGammaRadius τ * pathFollowingKappa τ` and the
    -- local `selfConcordantOmegaInverse` still uses the non-branch-restricted `Function.invFun ω`.
    sorry

end
