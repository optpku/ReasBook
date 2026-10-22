/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient MinGradientNormAlongIterates

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ}

variable {L ω fStar : ℝ}

/- Primary domain:
* sufficient-decrease consequences for real-Hilbert-space gradient-method trajectories

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `IsGStar` in `Definition_1_6_5.lean`, whose lower-boundedness component is the canonical owner
  `BddBelow (Set.range f)`
* the sufficient-decrease bridge theorems in `Proposition_1_6_7.lean`
* `minGradientNormAlongIterates` in `Chap02/Definition_2_23.lean`

Source/core/bridge triage:
* source-facing: Theorem 1.6.8's telescoping inequality, vanishing-gradient conclusion, and
  `g_N^*` estimate under the chapter's sufficient-decrease hypothesis
* core/canonical owner: the recursive trajectory `gradientMethod stepSize f x0` and the
  finite-window minimum `minGradientNormAlongIterates`
* bridge/view: Proposition 1.6.7's constant-step, exact-line-search, and Armijo corollaries that
  produce the sufficient-decrease hypothesis used here; the source prose names the owner finite
  minimum `minGradientNormAlongIterates f (gradientMethod stepSize f x0) 0 N (Nat.zero_le N)` by
  the textbook symbol `g_N^*`

Primitive data:
* the objective `f`, step schedule `stepSize`, and initial point `x0`
* the real sufficient-decrease scale `L`
* the sufficient-decrease hypothesis `hdesc`
* the exact optimal value parameter `fStar` together with the canonical owner hypothesis
  `IsGLB (Set.range f) fStar` for the source-facing quantitative bounds
* an arbitrary lower-bound witness `fLower ∈ lowerBounds (Set.range f)` for the companion
  lower-bound-only estimates
* the lower-boundedness owner `BddBelow (Set.range f)` when only existence of a bound is needed

Derived API:
* the telescoping estimate
* convergence of the gradients to `0`
* the source-facing `g_N^*` square-root bound for the owner window minimum
  `g[f; gradientMethod stepSize f x0; 0, N | Nat.zero_le N]`
* lower-bound-only companion estimates obtained by replacing the exact `fStar` owner hypothesis by
  an arbitrary witness `fLower ∈ lowerBounds (Set.range f)`

This file stays at the sufficient-decrease layer. The smoothness and step-rule assumptions that
produce `hdesc` are already owned upstream by `Proposition_1_6_7`; after choosing such a bridge,
this file only uses the resulting real coefficient `L` appearing in `(ω / L)`. The ambient space
is refined to the same real-Hilbert-space owner level as `gradientMethod` and
`minGradientNormAlongIterates`, since no theorem here uses coordinates or finite-dimensional
Euclidean structure. The textbook scalar `f^*` is exposed through the exact-infimum owner
`IsGLB (Set.range f) fStar`; the weaker arbitrary-lower-bound form is kept only as companion API
through `lowerBounds (Set.range f)`. -/

section SufficientDecrease

variable (stepSize : ℕ → ℝ) (x0 : E)

local notation "traj" => gradientMethod stepSize f x0
variable
  (hdesc :
    ∀ k : ℕ,
      (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)))

-- Proof sketch: sum the assumed descent inequalities over `k = 0, …, N` and telescope the left
-- side to obtain the first inequality; the second follows from the lower-bound hypothesis
-- applied to the iterate `traj (N + 1)`.
/-- Companion form of Theorem 1.6.8: any chosen lower bound
`fLower ∈ lowerBounds (Set.range f)` yields the same telescoping estimate with `fLower` in place
of the exact optimal value `f^*`. -/
theorem squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
    {fLower : ℝ}
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hfLower : fLower ∈ lowerBounds (Set.range f))
    (N : ℕ) :
    ((ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ)) ≤
        f x0 - f (traj (N + 1)) ∧
      f x0 - f (traj (N + 1)) ≤ f x0 - fLower := by
  constructor
  · -- Summing the sufficient-decrease bounds produces the telescoping estimate.
    have hsum :
        ∑ k ∈ Finset.range (N + 1), (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          ∑ k ∈ Finset.range (N + 1), (f (traj k) - f (traj (k + 1))) := by
      exact Finset.sum_le_sum fun k hk ↦ hdesc k
    have htel :
        ∑ k ∈ Finset.range (N + 1), (f (traj k) - f (traj (k + 1))) =
          f (traj 0) - f (traj (N + 1)) := by
      simpa using (Finset.sum_range_sub' (fun k ↦ f (traj k)) (N + 1))
    calc
      (ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) =
          ∑ k ∈ Finset.range (N + 1), (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range (N + 1), (f (traj k) - f (traj (k + 1))) := hsum
      _ = f (traj 0) - f (traj (N + 1)) := htel
      _ = f x0 - f (traj (N + 1)) := by simp
  · -- The terminal iterate still lies above any lower bound of `f`.
    have hterminal : fLower ≤ f (traj (N + 1)) := hfLower ⟨traj (N + 1), rfl⟩
    simpa using sub_le_sub_left hterminal (f x0)

/-- Helper for Theorem 1.6.8: the exact-infimum telescoping estimate follows by applying the
lower-bound companion theorem to the canonical lower-bound witness supplied by
`hfStar : IsGLB (Set.range f) fStar`. -/
theorem squared_gradient_norm_sum_le_and_value_gap_le_of_isGLB
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hfStar : IsGLB (Set.range f) fStar)
    (N : ℕ) :
    ((ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ)) ≤
        f x0 - f (traj (N + 1)) ∧
      f x0 - f (traj (N + 1)) ≤ f x0 - fStar := by
  -- Specialize the lower-bound telescope to the exact infimum witness `hfStar.1`.
  simpa using
    squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
      (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
      hfStar.1 N

/-- Theorem 1.6.8: for the gradient-method trajectory `gradientMethod stepSize f x0`, any
uniform descent bound of the form `(ω / L) ‖∇ f(xₖ)‖² ≤ f(xₖ) - f(xₖ₊₁)` yields the telescoping
estimate `(ω / L) ∑_{k=0}^N ‖∇ f(xₖ)‖² ≤ f(x₀) - f(x_{N+1}) ≤ f(x₀) - f^*`, where `fStar` is
the exact infimum value of `f`. -/
theorem squared_gradient_norm_sum_le_and_value_gap_le
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hfStar : IsGLB (Set.range f) fStar)
    (N : ℕ) :
    ((ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ)) ≤
        f x0 - f (traj (N + 1)) ∧
      f x0 - f (traj (N + 1)) ≤ f x0 - fStar := by
  simpa using
    squared_gradient_norm_sum_le_and_value_gap_le_of_isGLB
      (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc hfStar N

end SufficientDecrease

section PositiveSufficientDecrease

variable (stepSize : ℕ → ℝ) (x0 : E)

local notation "traj" => gradientMethod stepSize f x0
variable (hL : 0 < L) (hω : 0 < ω)
variable
  (hdesc :
    ∀ k : ℕ,
      (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f (traj k) - f (traj (k + 1)))

local notation "g⋆[" N "]" => minGradientNormAlongIterates f traj 0 N (Nat.zero_le N)

-- Proof sketch: use `BddBelow (Set.range f)` to choose some lower bound value, apply the previous
-- theorem to obtain a uniform bound on the partial sums of `∑ ‖∇ f(xₖ)‖²`, and conclude that
-- this nonnegative series is summable. Hence `‖∇ f(xₖ)‖ → 0`, so the gradient vectors themselves
-- converge to `0`.
/-- Under the positive sufficient-decrease hypothesis of Theorem 1.6.8 and the canonical
lower-boundedness assumption `BddBelow (Set.range f)`, the gradients along
`gradientMethod stepSize f x0` converge to zero. -/
theorem tendsto_gradient_zero
    (hL : 0 < L) (hω : 0 < ω)
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hbelow : BddBelow (Set.range f)) :
    Filter.Tendsto (fun k : ℕ ↦ ∇ f (traj k)) Filter.atTop (nhds 0) := by
  rcases hbelow with ⟨fLower, hfLower⟩
  let a : ℕ → ℝ := fun k ↦ (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ)
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    dsimp [a]
    positivity
  have hsum_range_le : ∀ n : ℕ, ∑ i ∈ Finset.range n, a i ≤ f x0 - fLower := by
    intro n
    cases n with
    | zero =>
        simpa [a] using sub_nonneg.mpr (hfLower ⟨x0, by simp⟩)
    | succ N =>
        -- The telescoping theorem gives a uniform bound on every partial sum.
        have hpartial :
            (ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
              f x0 - fLower :=
          (squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
            (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
            hfLower N).1.trans
            (squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
              (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
              hfLower N).2
        simpa [a, Finset.mul_sum] using hpartial
  have hsummable_a : Summable a := summable_of_sum_range_le ha_nonneg hsum_range_le
  have hsummable_sq : Summable (fun k : ℕ ↦ ‖∇ f (traj k)‖ ^ (2 : ℕ)) := by
    -- Remove the positive constant factor from the summable sequence.
    exact
      (summable_mul_left_iff (show ω / L ≠ 0 by exact div_ne_zero (ne_of_gt hω) (ne_of_gt hL))).1
        hsummable_a
  have hsq_zero :
      Filter.Tendsto (fun k : ℕ ↦ ‖∇ f (traj k)‖ ^ (2 : ℕ)) Filter.atTop (nhds 0) :=
    hsummable_sq.tendsto_atTop_zero
  have hnorm_zero :
      Filter.Tendsto (fun k : ℕ ↦ ‖∇ f (traj k)‖) Filter.atTop (nhds 0) := by
    -- Taking square roots converts convergence of squared norms into convergence of norms.
    have hsqrt_zero :
        Filter.Tendsto (fun k : ℕ ↦ Real.sqrt (‖∇ f (traj k)‖ ^ (2 : ℕ)))
          Filter.atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq_zero
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt_zero
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_zero

/-- Helper for Theorem 1.6.8: the finite-window minimum of gradient norms is nonnegative because
it is attained by some iterate in the window. -/
lemma minGradientNormAlongIterates_nonneg
    (N : ℕ) :
    0 ≤ g⋆[N] := by
  -- The owner minimum equals a norm at some iterate, so nonnegativity is immediate.
  rcases minGradientNormAlongIterates.exists_eq f traj (Nat.zero_le N) with
    ⟨i, -, -, hEq⟩
  rw [hEq]
  exact norm_nonneg _

/-- Helper for Theorem 1.6.8: the square of the window minimum `g⋆[N]` is bounded by the average
of the squared gradient norms over the same window. -/
lemma minGradientNormAlongIterates_sq_mul_le_sum_sq
    (N : ℕ) :
    ((N + 1 : ℝ) * g⋆[N] ^ (2 : ℕ)) ≤
      ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
  have hmin_nonneg : 0 ≤ g⋆[N] :=
    minGradientNormAlongIterates_nonneg (stepSize := stepSize) (x0 := x0) (f := f) N
  have hpointwise :
      ∀ k ∈ Finset.range (N + 1), g⋆[N] ^ (2 : ℕ) ≤ ‖∇ f (traj k)‖ ^ (2 : ℕ) := by
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hle :
        g⋆[N] ≤ ‖∇ f (traj k)‖ :=
      minGradientNormAlongIterates.le f traj (Nat.zero_le N) (Nat.zero_le k) hkN
    exact (sq_le_sq₀ hmin_nonneg (norm_nonneg _)).2 hle
  -- Sum the pointwise squared bounds over the whole window.
  have hsum :
      ∑ k ∈ Finset.range (N + 1), g⋆[N] ^ (2 : ℕ) ≤
        ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) :=
    Finset.sum_le_sum hpointwise
  simpa using hsum

-- Proof sketch: the minimum of `N + 1` nonnegative numbers has square at most the average of
-- their squares, and the latter is bounded by Theorem 1.6.8 after rearranging the coefficient
-- `(ω / L)`.
/-- Companion form of the Chapter 1 estimate for the owner window minimum
`g⋆[N]`, representing the textbook quantity `g_N^*`: any chosen lower bound
`fLower ∈ lowerBounds (Set.range f)` gives the same square-root bound with `fLower` in place of
the exact optimum value `f^*`. -/
theorem minGradientNormAlongIterates_le_sqrt_of_lower_bound
    {fLower : ℝ}
    (hL : 0 < L) (hω : 0 < ω)
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (hfLower : fLower ∈ lowerBounds (Set.range f))
    (N : ℕ) :
    g⋆[N] ≤
      Real.sqrt ((L * (f x0 - fLower)) / (ω * (N + 1 : ℝ))) := by
  have hgap_nonneg : 0 ≤ f x0 - fLower := by
    exact sub_nonneg.mpr (hfLower ⟨x0, by simp⟩)
  have hpair :=
    squared_gradient_norm_sum_le_and_value_gap_le_of_lower_bound
      (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hdesc
      hfLower N
  have hsum_sq_le :
      ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        (L / ω) * (f x0 - fLower) := by
    have hscaled : (ω / L) * ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
        f x0 - fLower :=
      hpair.1.trans hpair.2
    have hdiv :
        ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          (f x0 - fLower) / (ω / L) := by
      exact (le_div_iff₀ (div_pos hω hL)).2 (by simpa [mul_comm] using hscaled)
    have hrewrite : (f x0 - fLower) / (ω / L) = (L / ω) * (f x0 - fLower) := by
      field_simp [ne_of_gt hL, ne_of_gt hω]
    rwa [hrewrite] at hdiv
  have hsq :
      g⋆[N] ^ (2 : ℕ) ≤ ((L * (f x0 - fLower)) / ω) / (N + 1 : ℝ) := by
    apply (le_div_iff₀ (by positivity : 0 < (N + 1 : ℝ))).2
    calc
      g⋆[N] ^ (2 : ℕ) * (N + 1 : ℝ) = (N + 1 : ℝ) * g⋆[N] ^ (2 : ℕ) := by ring
      _ ≤ ∑ k ∈ Finset.range (N + 1), ‖∇ f (traj k)‖ ^ (2 : ℕ) :=
        minGradientNormAlongIterates_sq_mul_le_sum_sq
          (stepSize := stepSize) (x0 := x0) (f := f) N
      _ ≤ (L / ω) * (f x0 - fLower) := hsum_sq_le
      _ = (L * (f x0 - fLower)) / ω := by
        field_simp [ne_of_gt hω]
  have hsq' :
      g⋆[N] ^ (2 : ℕ) ≤ (L * (f x0 - fLower)) / (ω * (N + 1 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hmin_nonneg : 0 ≤ g⋆[N] :=
    minGradientNormAlongIterates_nonneg (stepSize := stepSize) (x0 := x0) (f := f) N
  have hrhs_nonneg : 0 ≤ (L * (f x0 - fLower)) / (ω * (N + 1 : ℝ)) := by
    positivity
  -- Apply the square-root monotonicity step to the squared estimate.
  exact (Real.le_sqrt hmin_nonneg hrhs_nonneg).2 hsq'

/- The owner window minimum `g⋆[N]`, representing the textbook quantity `g_N^*`, is bounded by
the standard `O((N + 1)^{-1/2})` rate obtained from the telescoping descent estimate, with the
exact optimum value exposed by
`IsGLB (Set.range f) fStar`. -/
theorem minGradientNormAlongIterates_le_sqrt
    (hfStar : IsGLB (Set.range f) fStar)
    (hL : 0 < L) (hω : 0 < ω)
    (hdesc :
      ∀ k : ℕ,
        (ω / L) * ‖∇ f (traj k)‖ ^ (2 : ℕ) ≤
          f (traj k) - f (traj (k + 1)))
    (N : ℕ) :
    g⋆[N] ≤
      Real.sqrt ((L * (f x0 - fStar)) / (ω * (N + 1 : ℝ))) := by
  -- The exact-infimum rate bound is the lower-bound companion theorem with the GLB witness.
  simpa using
    minGradientNormAlongIterates_le_sqrt_of_lower_bound
      (stepSize := stepSize) (x0 := x0) (f := f) (L := L) (ω := ω) hL hω hdesc hfStar.1 N

end PositiveSufficientDecrease

end
