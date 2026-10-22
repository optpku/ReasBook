/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 7.8 lies in the scalar concavity / maximizer layer of the centrally symmetric
rounding argument.

Sampled owner-style declarations:
- mathlib `StrictConcaveOn`, the canonical owner for strict concavity on an interval;
- mathlib `IsMaxOn`, the canonical owner for interval maximizers;
- `rankOneUpdatePotential` in `Lemma_7_4`, the matrix-level specialization whose scalar part is the
  same logarithmic objective with `σ = (1 / n) ‖g‖_{G,*}² - 1`;
- `oneSidedRoundingPotential` in `Lemma_7_5`, a nearby chapter scalar maximizer statement with the
  same `IsMaxOn` owner discipline.

Best owner abstraction:
- source-facing: the scalar objective `V(α)` and its distinguished critical point `α*`;
- core/canonical: mathlib's `StrictConcaveOn` and `IsMaxOn`;
- bridge/view: later matrix-level specializations obtained by substituting a concrete `σ`.

Primitive data:
- the dimension parameter `n`;
- the scalar parameter `σ`;
- the interval variable `α`.

Derived API:
- strict concavity on `Set.Ico 0 1`;
- membership of the explicit critical point in that interval;
- the first-order characterization, maximizer characterization, and closed-form value at `α*`.

The scalar coefficient `n (1 + σ) - 1` is not kept as a separate public owner: it is derived data
inside the objective and critical-point formulas. -/

/-- The scalar objective `V(α)` on `[0, 1)` used in the centrally symmetric rounding estimate. -/
def centralSymmetryRoundingObjective (n : ℕ) (σ : ℝ) (α : ℝ) : ℝ :=
  Real.log (1 + α * ((n : ℝ) * (1 + σ) - 1)) +
    ((n : ℝ) - 1) * Real.log (1 - α)

/-- The explicit critical point `α* = σ / (n (1 + σ) - 1)` of the scalar objective. -/
def centralSymmetryRoundingAlphaStar (n : ℕ) (σ : ℝ) : ℝ :=
  σ / ((n : ℝ) * (1 + σ) - 1)

/-- Helper for Proposition 7.8: on `[0, 1)`, both logarithmic arguments in the scalar objective are
strictly positive. -/
lemma centralSymmetryRoundingObjective_log_arguments_pos
    {n : ℕ} {σ α : ℝ} (hn : 1 ≤ n) (hσ : -1 ≤ σ) (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    0 < 1 - α ∧ 0 < 1 + α * ((n : ℝ) * (1 + σ) - 1) := by
  rcases hα with ⟨hα0, hα1⟩
  have hα_nonneg : 0 ≤ α := hα0
  have hσ' : 0 ≤ 1 + σ := by linarith
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : 0 ≤ α * ((n : ℝ) * (1 + σ)) := by
    exact mul_nonneg hα_nonneg (mul_nonneg (by linarith) hσ')
  constructor
  · linarith
  · nlinarith

/-- Helper for Proposition 7.8: the scalar objective has the expected first derivative on the open
interval `(0, 1)`. -/
lemma centralSymmetryRoundingObjective_hasDerivAt
    {n : ℕ} {σ α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hlog : 0 < 1 + α * (((n : ℝ) * (1 + σ)) - 1)) :
    HasDerivAt (centralSymmetryRoundingObjective n σ)
      ((((n : ℝ) * (1 + σ) - 1) / (1 + α * (((n : ℝ) * (1 + σ) - 1))) -
          (((n : ℝ) - 1) / (1 - α)))) α := by
  let c : ℝ := (n : ℝ) * (1 + σ) - 1
  have hpos : 0 < 1 - α := by
    linarith [hα.2]
  have hlog₁ : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x * c)) (c / (1 + α * c)) α := by
    have hinner : HasDerivAt (fun x : ℝ ↦ 1 + x * c) c α := by
      simpa [c, mul_comm, mul_left_comm, mul_assoc] using
        ((hasDerivAt_id α).mul_const c).const_add 1
    exact hinner.log hlog.ne'
  have hlog₂ : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) ((-1) / (1 - α)) α := by
    have hinner : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) α := by
      simpa using (hasDerivAt_id α).const_sub 1
    exact hinner.log hpos.ne'
  have hscaled :
      HasDerivAt (fun x : ℝ ↦ ((n : ℝ) - 1) * Real.log (1 - x))
        (((n : ℝ) - 1) * (((-1) / (1 - α)))) α := by
    exact hlog₂.const_mul ((n : ℝ) - 1)
  have hsum :
      HasDerivAt
        (fun x : ℝ ↦
          Real.log (1 + x * c) + ((n : ℝ) - 1) * Real.log (1 - x))
        (c / (1 + α * c) + ((n : ℝ) - 1) * (((-1) / (1 - α)))) α := by
    simpa [Pi.add_apply] using hlog₁.add hscaled
  have hobjective :
      (fun x : ℝ ↦ Real.log (1 + x * c) + ((n : ℝ) - 1) * Real.log (1 - x)) =
        centralSymmetryRoundingObjective n σ := by
    -- Rewrite the objective to the source-facing logarithmic form before closing the derivative.
    funext x
    simp [centralSymmetryRoundingObjective, c, add_comm]
  rw [← hobjective]
  simpa [c, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Helper for Proposition 7.8: the derivative formula is available as a reusable rewrite lemma. -/
lemma centralSymmetryRoundingObjective_deriv_formula
    {n : ℕ} {σ α : ℝ} (hn : 1 ≤ n) (hσ : -1 ≤ σ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (centralSymmetryRoundingObjective n σ) α =
      (((n : ℝ) * (1 + σ) - 1) / (1 + α * (((n : ℝ) * (1 + σ) - 1))) -
        (((n : ℝ) - 1) / (1 - α))) := by
  -- Rewrite the derivative through the explicit `HasDerivAt` computation above.
  have hlog := (centralSymmetryRoundingObjective_log_arguments_pos hn hσ ⟨le_of_lt hα.1, hα.2⟩).2
  simpa using (centralSymmetryRoundingObjective_hasDerivAt
    (n := n) (σ := σ) (α := α) ⟨le_of_lt hα.1, hα.2⟩ hlog).deriv

/-- Helper for Proposition 7.8: at the explicit critical point, the first logarithmic argument
simplifies to `1 + σ`. -/
lemma centralSymmetryRoundingAlphaStar_log_argument
    {n : ℕ} {σ : ℝ} (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) :
    1 + centralSymmetryRoundingAlphaStar n σ * (((n : ℝ) * (1 + σ)) - 1) = 1 + σ := by
  dsimp [centralSymmetryRoundingAlphaStar]
  field_simp [hcoeff]

/-- Helper for Proposition 7.8: multiplying the closed form for `α*` by the scalar coefficient
recovers `σ`. -/
lemma centralSymmetryRoundingAlphaStar_mul_coeff
    {n : ℕ} {σ : ℝ} (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) :
    centralSymmetryRoundingAlphaStar n σ * (((n : ℝ) * (1 + σ) - 1)) = σ := by
  -- Cancel the nonzero coefficient in the closed form `α* = σ / (n (1 + σ) - 1)`.
  dsimp [centralSymmetryRoundingAlphaStar]
  field_simp [hcoeff]

-- Proof sketch: use `2 ≤ n` and `0 ≤ σ` to show
-- `0 ≤ σ / (n (1 + σ) - 1) < 1`, equivalently that the explicit critical point lies in
-- `Set.Ico 0 1`.
/-- The explicit critical point `α*` lies in the interval `[0, 1)`. -/
theorem centralSymmetryRoundingAlphaStar_mem_Ico
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) :
    centralSymmetryRoundingAlphaStar n σ ∈ Set.Ico (0 : ℝ) 1 := by
  let c : ℝ := (n : ℝ) * (1 + σ) - 1
  have hcoeff_pos : 0 < c := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hσ' : 1 ≤ 1 + σ := by linarith
    nlinarith
  have hlt_gap : σ < c := by
    have hn1 : 0 < (n : ℝ) - 1 := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hσ' : 0 < 1 + σ := by linarith
    have : 0 < ((n : ℝ) - 1) * (1 + σ) := by positivity
    nlinarith [show c - σ = ((n : ℝ) - 1) * (1 + σ) by
      dsimp [c]
      ring]
  constructor
  · -- The numerator and denominator are both nonnegative.
    rw [centralSymmetryRoundingAlphaStar]
    exact div_nonneg hσ hcoeff_pos.le
  · -- The gap estimate `σ < n (1 + σ) - 1` gives the strict upper bound.
    rw [centralSymmetryRoundingAlphaStar]
    exact (div_lt_iff₀ hcoeff_pos).2 (by simpa using hlt_gap)

/-- Helper for Proposition 7.8: subtracting two derivative values factors through `y - x` with a
manifestly nonnegative bracket. -/
lemma centralSymmetryRoundingObjective_deriv_sub_deriv_factorization
    {n : ℕ} {σ x y : ℝ} (hn : 1 ≤ n) (hσ : -1 ≤ σ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (centralSymmetryRoundingObjective n σ) x -
        deriv (centralSymmetryRoundingObjective n σ) y =
      (y - x) *
        (((((n : ℝ) * (1 + σ) - 1) ^ 2) /
              ((1 + x * (((n : ℝ) * (1 + σ) - 1))) *
                (1 + y * (((n : ℝ) * (1 + σ) - 1)))) +
            (((n : ℝ) - 1) / ((1 - x) * (1 - y))))) := by
  let c : ℝ := (n : ℝ) * (1 + σ) - 1
  have hxlog :
      0 < 1 + x * c := by
    simpa [c] using
      (centralSymmetryRoundingObjective_log_arguments_pos hn hσ ⟨le_of_lt hx.1, hx.2⟩).2
  have hylog :
      0 < 1 + y * c := by
    simpa [c] using
      (centralSymmetryRoundingObjective_log_arguments_pos hn hσ ⟨le_of_lt hy.1, hy.2⟩).2
  have hxone : 1 - x ≠ 0 := by linarith [hx.2]
  have hyone : 1 - y ≠ 0 := by linarith [hy.2]
  let u : ℝ := 1 + x * c
  let v : ℝ := 1 + y * c
  let m : ℝ := (n : ℝ) - 1
  have hfirst :
      c / u - c / v =
        (y - x) * (c ^ 2 / (u * v)) := by
    field_simp [u, v, hxlog.ne', hylog.ne']
    ring
  have hsecond :
      -m / (1 - x) + m / (1 - y) =
        (y - x) * (m / ((1 - x) * (1 - y))) := by
    field_simp [m, hxone, hyone]
    ring
  -- Split the derivative difference into the two rational difference terms and factor `y - x`.
  have hfactor :
      (c / u - m / (1 - x)) - (c / v - m / (1 - y)) =
        (y - x) * (c ^ 2 / (u * v) + m / ((1 - x) * (1 - y))) := by
    calc
      (c / u - m / (1 - x)) - (c / v - m / (1 - y)) =
        (c / u - c / v) + (-m / (1 - x) + m / (1 - y)) := by
          ring
      _ =
        (y - x) * (c ^ 2 / (u * v)) + (y - x) * (m / ((1 - x) * (1 - y))) := by
          rw [hfirst, hsecond]
      _ =
        (y - x) * (c ^ 2 / (u * v) + m / ((1 - x) * (1 - y))) := by
          ring
  rw [centralSymmetryRoundingObjective_deriv_formula hn hσ hx,
    centralSymmetryRoundingObjective_deriv_formula hn hσ hy]
  simpa [u, v, m, c] using hfactor

/-- Helper for Proposition 7.8: the derivative of the scalar objective is strictly antitone on
`(0, 1)` once at least one logarithmic summand is genuinely nonconstant. -/
lemma centralSymmetryRoundingObjective_deriv_strictAntiOn
    {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : -1 ≤ σ)
    (hstrict : ((n : ℝ) * (1 + σ) - 1 ≠ 0) ∨ 1 < n) :
    StrictAntiOn (deriv (centralSymmetryRoundingObjective n σ)) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxlog :=
    (centralSymmetryRoundingObjective_log_arguments_pos hn hσ ⟨le_of_lt hx.1, hx.2⟩).2
  have hylog :=
    (centralSymmetryRoundingObjective_log_arguments_pos hn hσ ⟨le_of_lt hy.1, hy.2⟩).2
  have hxone : 0 < 1 - x := by linarith [hx.2]
  have hyone : 0 < 1 - y := by linarith [hy.2]
  have hn_nonneg : 0 ≤ (n : ℝ) - 1 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfirst_nonneg :
      0 ≤
        (((n : ℝ) * (1 + σ) - 1) ^ 2) /
          ((1 + x * (((n : ℝ) * (1 + σ) - 1))) * (1 + y * (((n : ℝ) * (1 + σ) - 1)))) := by
    exact div_nonneg (sq_nonneg _) (mul_pos hxlog hylog).le
  have hsecond_nonneg :
      0 ≤ ((n : ℝ) - 1) / ((1 - x) * (1 - y)) := by
    exact div_nonneg hn_nonneg (mul_pos hxone hyone).le
  have hsum_pos :
      0 <
        ((((n : ℝ) * (1 + σ) - 1) ^ 2) /
              ((1 + x * (((n : ℝ) * (1 + σ) - 1))) *
                (1 + y * (((n : ℝ) * (1 + σ) - 1)))) +
            (((n : ℝ) - 1) / ((1 - x) * (1 - y)))) := by
    rcases hstrict with hcoeff | hn_strict
    · have hfirst_pos :
        0 <
          (((n : ℝ) * (1 + σ) - 1) ^ 2) /
            ((1 + x * (((n : ℝ) * (1 + σ) - 1))) *
              (1 + y * (((n : ℝ) * (1 + σ) - 1)))) := by
        exact div_pos (sq_pos_iff.mpr hcoeff) (mul_pos hxlog hylog)
      linarith
    · have hn1_pos : 0 < (n : ℝ) - 1 := by
        have hn' : (1 : ℝ) < n := by exact_mod_cast hn_strict
        linarith
      have hsecond_pos : 0 < ((n : ℝ) - 1) / ((1 - x) * (1 - y)) := by
        exact div_pos hn1_pos (mul_pos hxone hyone)
      linarith
  have hdiff_pos :
      0 <
        deriv (centralSymmetryRoundingObjective n σ) x -
          deriv (centralSymmetryRoundingObjective n σ) y := by
    rw [centralSymmetryRoundingObjective_deriv_sub_deriv_factorization hn hσ hx hy]
    exact mul_pos (sub_pos.mpr hxy) hsum_pos
  exact sub_pos.mp hdiff_pos

/-- Helper for Proposition 7.8: the derivative vanishes at the explicit critical point. -/
lemma centralSymmetryRoundingObjective_deriv_eq_zero_at_alphaStar
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) :
    deriv (centralSymmetryRoundingObjective n σ) (centralSymmetryRoundingAlphaStar n σ) = 0 := by
  let c : ℝ := (n : ℝ) * (1 + σ) - 1
  have hcoeff_pos : 0 < c := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hσ' : 1 ≤ 1 + σ := by linarith
    nlinarith
  have hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0 := by
    simpa [c] using hcoeff_pos.ne'
  have hαstar :
      centralSymmetryRoundingAlphaStar n σ ∈ Set.Ico (0 : ℝ) 1 :=
    centralSymmetryRoundingAlphaStar_mem_Ico hn hσ
  have hlog : 0 < 1 + centralSymmetryRoundingAlphaStar n σ * c := by
    -- The first logarithmic argument at `α*` is exactly `1 + σ`.
    rw [centralSymmetryRoundingAlphaStar_log_argument (n := n) (σ := σ) hcoeff]
    linarith
  have hone_sub :
      1 - centralSymmetryRoundingAlphaStar n σ = ((n : ℝ) - 1) * (1 + σ) / c := by
    -- Rewrite the second denominator in the same closed form used in the proposition.
    dsimp [centralSymmetryRoundingAlphaStar, c]
    field_simp [hcoeff_pos.ne']
    ring_nf
  have hformula :
      deriv (centralSymmetryRoundingObjective n σ) (centralSymmetryRoundingAlphaStar n σ) =
        c / (1 + σ) - ((n : ℝ) - 1) / (((n : ℝ) - 1) * (1 + σ) / c) := by
    -- The derivative computation at `α*` reduces to a single rational identity.
    simpa [c, hone_sub, centralSymmetryRoundingAlphaStar_log_argument (n := n) (σ := σ) hcoeff]
      using
        (centralSymmetryRoundingObjective_hasDerivAt
          (n := n) (σ := σ) (α := centralSymmetryRoundingAlphaStar n σ) hαstar hlog).deriv
  have hn1_pos : 0 < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hσ1_pos : 0 < 1 + σ := by
    linarith
  rw [hformula]
  field_simp [hcoeff_pos.ne', hn1_pos.ne', hσ1_pos.ne']
  ring

/-- Helper for Proposition 7.8: the explicit critical point is a maximizer on `[0, 1)`. -/
lemma centralSymmetryRoundingObjective_isMaxOn_alphaStar
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) :
    IsMaxOn (centralSymmetryRoundingObjective n σ) (Set.Ico (0 : ℝ) 1)
      (centralSymmetryRoundingAlphaStar n σ) := by
  have hn₁ : 1 ≤ n := le_trans (by norm_num) hn
  have hσ₁ : -1 ≤ σ := by linarith
  have hn_strict : 1 < n := by linarith
  have hαstar :
      centralSymmetryRoundingAlphaStar n σ ∈ Set.Ico (0 : ℝ) 1 :=
    centralSymmetryRoundingAlphaStar_mem_Ico hn hσ
  have hcoeff :
      ((n : ℝ) * (1 + σ) - 1) ≠ 0 := by
    have hcoeff_pos : 0 < (n : ℝ) * (1 + σ) - 1 := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hσ' : 1 ≤ 1 + σ := by linarith
      nlinarith
    exact hcoeff_pos.ne'
  have hlog :
      0 < 1 + centralSymmetryRoundingAlphaStar n σ * (((n : ℝ) * (1 + σ) - 1)) := by
    -- The logarithmic domain condition at `α*` is exactly the already simplified first argument.
    rw [centralSymmetryRoundingAlphaStar_log_argument (n := n) (σ := σ) hcoeff]
    linarith
  have hderivAtRaw :
      HasDerivAt (centralSymmetryRoundingObjective n σ)
        ((((n : ℝ) * (1 + σ) - 1) /
              (1 + centralSymmetryRoundingAlphaStar n σ * (((n : ℝ) * (1 + σ) - 1))) -
            (((n : ℝ) - 1) / (1 - centralSymmetryRoundingAlphaStar n σ))))
        (centralSymmetryRoundingAlphaStar n σ) :=
    centralSymmetryRoundingObjective_hasDerivAt
      (n := n) (σ := σ) (α := centralSymmetryRoundingAlphaStar n σ) hαstar hlog
  have hexpr_zero :
      (((n : ℝ) * (1 + σ) - 1) /
              (1 + centralSymmetryRoundingAlphaStar n σ * (((n : ℝ) * (1 + σ) - 1))) -
            (((n : ℝ) - 1) / (1 - centralSymmetryRoundingAlphaStar n σ))) = 0 := by
    -- Match the explicit derivative value with the previously proved vanishing statement.
    rw [← hderivAtRaw.deriv, centralSymmetryRoundingObjective_deriv_eq_zero_at_alphaStar hn hσ]
  have hderivAtStar :
      HasDerivAt (centralSymmetryRoundingObjective n σ) 0
        (centralSymmetryRoundingAlphaStar n σ) := by
    simpa [hexpr_zero] using hderivAtRaw
  have hcont :
      ContinuousOn (centralSymmetryRoundingObjective n σ) (Set.Ico (0 : ℝ) 1) := by
    intro α hα
    have hlogα :=
      (centralSymmetryRoundingObjective_log_arguments_pos hn₁ hσ₁ hα).2
    exact
      (centralSymmetryRoundingObjective_hasDerivAt
        (n := n) (σ := σ) (α := α) hα hlogα).continuousAt.continuousWithinAt
  have hstrictConcave :
      StrictConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (centralSymmetryRoundingObjective n σ) := by
    -- Route correction: use the first-derivative antitonicity route instead of a second-derivative
    -- detour, then invoke the canonical strict-concavity theorem for derivatives.
    have hanti :
        StrictAntiOn (deriv (centralSymmetryRoundingObjective n σ))
          (interior (Set.Ico (0 : ℝ) 1)) := by
      simpa using
        (centralSymmetryRoundingObjective_deriv_strictAntiOn
          (n := n) (σ := σ) hn₁ hσ₁ (Or.inr hn_strict))
    exact hanti.strictConcaveOn_of_deriv (convex_Ico (0 : ℝ) 1) hcont
  have hconcave : ConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (centralSymmetryRoundingObjective n σ) :=
    hstrictConcave.concaveOn
  intro β hβ
  rcases lt_trichotomy β (centralSymmetryRoundingAlphaStar n σ) with hlt | heq | hgt
  · -- On the left, the secant slope into `α*` is nonnegative because the derivative at `α*` is `0`.
    have hslope :
        0 ≤
          slope (centralSymmetryRoundingObjective n σ) β
            (centralSymmetryRoundingAlphaStar n σ) := by
      simpa using hconcave.le_slope_of_hasDerivAt hβ hαstar hlt hderivAtStar
    have hden : 0 < centralSymmetryRoundingAlphaStar n σ - β := sub_pos.mpr hlt
    have hnum :
        0 ≤
          centralSymmetryRoundingObjective n σ (centralSymmetryRoundingAlphaStar n σ) -
            centralSymmetryRoundingObjective n σ β := by
      rw [slope_def_field] at hslope
      rcases (div_nonneg_iff.mp hslope) with hcase | hcase
      · exact hcase.1
      · linarith [hden, hcase.2]
    exact sub_nonneg.mp hnum
  · -- Equality is the trivial middle case of the trichotomy.
    simp [heq]
  · -- On the right, the secant slope out of `α*` is nonpositive because the derivative
    -- at `α*` is `0`.
    have hslope :
        slope (centralSymmetryRoundingObjective n σ)
            (centralSymmetryRoundingAlphaStar n σ) β ≤
          0 := by
      simpa using hconcave.slope_le_of_hasDerivAt hαstar hβ hgt hderivAtStar
    have hden : 0 < β - centralSymmetryRoundingAlphaStar n σ := sub_pos.mpr hgt
    have hnum :
        centralSymmetryRoundingObjective n σ β -
            centralSymmetryRoundingObjective n σ (centralSymmetryRoundingAlphaStar n σ) ≤
          0 := by
      rw [slope_def_field] at hslope
      rcases (div_nonpos_iff.mp hslope) with hcase | hcase
      · linarith [hden, hcase.2]
      · exact hcase.1
    exact sub_nonpos.mp hnum

-- Proof sketch: write `V` as the sum of two logarithmic terms composed with affine maps taking
-- `[0, 1)` into `(0, ∞)`. The hypothesis `-1 ≤ σ` keeps the first logarithmic argument positive on
-- `Set.Ico 0 1`, `1 ≤ n` keeps the second logarithmic coefficient nonnegative, and the extra
-- nonconstancy hypothesis rules out the degenerate constant case. Strict concavity then follows
-- from strict concavity of `Real.log` on `Set.Ioi 0` together with stability under affine
-- reparametrization and addition.
/-- The objective `V` is strictly concave on `[0, 1)` once both logarithmic terms are well defined
and at least one of them is genuinely nonconstant. -/
theorem centralSymmetryRoundingObjective_strictConcaveOn
    {n : ℕ} {σ : ℝ} (hn : 1 ≤ n) (hσ : -1 ≤ σ)
    (hstrict : ((n : ℝ) * (1 + σ) - 1 ≠ 0) ∨ 1 < n) :
    StrictConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (centralSymmetryRoundingObjective n σ) := by
  have hcont :
      ContinuousOn (centralSymmetryRoundingObjective n σ) (Set.Ico (0 : ℝ) 1) := by
    intro α hα
    have hlogα :=
      (centralSymmetryRoundingObjective_log_arguments_pos hn hσ hα).2
    exact
      (centralSymmetryRoundingObjective_hasDerivAt
        (n := n) (σ := σ) (α := α) hα hlogα).continuousAt.continuousWithinAt
  -- Route correction: the source-faithful route is to prove strict antitonicity of `V'` and feed
  -- it directly into mathlib's derivative-based strict concavity theorem.
  have hanti :
      StrictAntiOn (deriv (centralSymmetryRoundingObjective n σ))
        (interior (Set.Ico (0 : ℝ) 1)) := by
    simpa using
      (centralSymmetryRoundingObjective_deriv_strictAntiOn
        (n := n) (σ := σ) hn hσ hstrict)
  exact hanti.strictConcaveOn_of_deriv (convex_Ico (0 : ℝ) 1) hcont

-- Proof sketch: compute `V'(α)` on the genuine logarithmic domain, namely points of `[0, 1)` for
-- which the first logarithmic argument `1 + α (n (1 + σ) - 1)` is positive. On that domain, the
-- critical-point equation reduces to a linear equation in `α`, whose unique solution is
-- `α = σ / (n (1 + σ) - 1)`. The coefficient hypothesis keeps the displayed closed form defined.
/-- On the genuine logarithmic domain inside `[0, 1)`, the first-order condition for `V` is
equivalent to `α = α*`. -/
theorem centralSymmetryRoundingObjective_firstOrderCondition_iff
    {n : ℕ} {σ : ℝ} (hn : 1 ≤ n)
    (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hlog : 0 < 1 + α * ((n : ℝ) * (1 + σ) - 1)) :
    ((n : ℝ) - 1) / (1 - α) =
        (((n : ℝ) * (1 + σ) - 1) / (1 + α * ((n : ℝ) * (1 + σ) - 1))) ↔
      α = centralSymmetryRoundingAlphaStar n σ := by
  have hcross :
      ((n : ℝ) - 1) / (1 - α) =
          (((n : ℝ) * (1 + σ) - 1) / (1 + α * ((n : ℝ) * (1 + σ) - 1))) ↔
        α * (((n : ℝ) * (1 + σ) - 1)) = σ := by
    have hone : 1 - α ≠ 0 := by linarith [hα.2]
    constructor
    · intro hEq
      -- Cross-multiplying the first-order condition reduces it to the linear identity `α * c = σ`.
      field_simp [hone, hlog.ne'] at hEq
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    · intro hmul
      -- Reinsert the linear identity into the normalized rational equation.
      field_simp [hone, hlog.ne']
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
  constructor
  · intro hEq
    -- Divide the linear identity by the nonzero coefficient to recover the closed form for `α*`.
    rw [centralSymmetryRoundingAlphaStar]
    exact (eq_div_iff hcoeff).2 (by simpa [mul_comm] using hcross.mp hEq)
  · intro hEq
    subst hEq
    -- The closed form for `α*` satisfies the cross-multiplied first-order equation by construction.
    exact hcross.mpr (by
      simpa [mul_comm] using
        (centralSymmetryRoundingAlphaStar_mul_coeff (n := n) (σ := σ) hcoeff))

-- Proof sketch: strict concavity gives uniqueness of a feasible maximizer on the convex set
-- `[0, 1)`. The first-order characterization identifies the only critical point with
-- `σ / (n (1 + σ) - 1)`, and the separate membership theorem shows that this point is feasible.
/-- Proposition 7.8: among feasible points `α ∈ [0, 1)`, the scalar objective `V` is maximized
exactly at `α* = σ / (n (1 + σ) - 1)`. -/
theorem centralSymmetryRoundingObjective_isMaxOn_iff
    {n : ℕ} {σ : ℝ} (hn : 2 ≤ n) (hσ : 0 ≤ σ) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    IsMaxOn (centralSymmetryRoundingObjective n σ) (Set.Ico (0 : ℝ) 1) α ↔
      α = centralSymmetryRoundingAlphaStar n σ := by
  have hstrict :
      StrictConcaveOn ℝ (Set.Ico (0 : ℝ) 1) (centralSymmetryRoundingObjective n σ) := by
    have hn₁ : 1 ≤ n := le_trans (by norm_num) hn
    have hσ₁ : -1 ≤ σ := by linarith
    have hn_strict : 1 < n := by linarith
    exact centralSymmetryRoundingObjective_strictConcaveOn
      (n := n) (σ := σ) hn₁ hσ₁ (Or.inr hn_strict)
  constructor
  · intro hmax
    -- Strict concavity leaves room for at most one feasible maximizer, so compare with `α*`.
    exact
      hstrict.eq_of_isMaxOn hmax
        (centralSymmetryRoundingObjective_isMaxOn_alphaStar (n := n) (σ := σ) hn hσ)
        hα (centralSymmetryRoundingAlphaStar_mem_Ico (n := n) (σ := σ) hn hσ)
  · intro hEq
    -- The reverse implication is the explicit maximizer theorem.
    subst hEq
    exact centralSymmetryRoundingObjective_isMaxOn_alphaStar (n := n) (σ := σ) hn hσ

-- Proof sketch: substitute `α* = σ / (n (1 + σ) - 1)` into the two logarithmic factors,
-- simplify `1 + α* (n (1 + σ) - 1) = 1 + σ` and
-- `1 - α* = ((n - 1) (1 + σ)) / (n (1 + σ) - 1)`, then evaluate `V(α*)`. Only the
-- nondegeneracy of `n (1 + σ) - 1` is needed for the substitution.
/-- The scalar objective evaluated at `α*` has the closed form stated in the proposition. -/
theorem centralSymmetryRoundingObjective_alphaStar_value
    {n : ℕ} {σ : ℝ} (hcoeff : ((n : ℝ) * (1 + σ) - 1) ≠ 0) :
    centralSymmetryRoundingObjective n σ (centralSymmetryRoundingAlphaStar n σ) =
      Real.log (1 + σ) +
        ((n : ℝ) - 1) *
          Real.log
            (((n : ℝ) - 1) * (1 + σ) / ((n : ℝ) * (1 + σ) - 1)) := by
  let c : ℝ := (n : ℝ) * (1 + σ) - 1
  -- Substitute the explicit critical point and rewrite the two logarithmic arguments separately.
  have harg₁ : 1 + centralSymmetryRoundingAlphaStar n σ * c = 1 + σ := by
    dsimp [centralSymmetryRoundingAlphaStar, c]
    field_simp [hcoeff]
  have harg₂ :
      1 - centralSymmetryRoundingAlphaStar n σ = ((n : ℝ) - 1) * (1 + σ) / c := by
    dsimp [centralSymmetryRoundingAlphaStar, c]
    field_simp [hcoeff]
    ring_nf
  rw [centralSymmetryRoundingObjective, harg₁, harg₂]
