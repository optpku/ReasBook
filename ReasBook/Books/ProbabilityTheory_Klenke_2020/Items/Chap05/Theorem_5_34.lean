/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Example_3_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u}

/-- Additivity identifies each interval count with the corresponding increment of the associated
counting process `t ↦ N_(0,t]`. -/
theorem poissonIntervalCount_increment_eq_sub
    {NI : NNReal → NNReal → Ω → ℕ}
    (hadditive : ∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω)
    {s t : NNReal} (hst : s ≤ t) :
    NI s t = fun ω ↦ NI 0 t ω - NI 0 s ω := by
  ext ω
  rw [hadditive 0 s t bot_le hst]
  simp

variable [MeasurableSpace Ω]

/-- The source-facing interval-count side of this item: a family `NI s t` of random variables
indexed by half-open intervals `(s,t]` satisfies the textbook axioms `(P1)`--`(P5)`. The chapter's
core owner abstraction remains `IsPoissonProcess`; this predicate is the bridge layer used to
relate the textbook interval-count formulation to that owner object. The random-variable content is
recorded explicitly, so the associated counting process `t ↦ NI 0 t` is genuinely stochastic. The
zero-time axiom `(P1)` is kept as a derived theorem, since for `ℕ`-valued interval counts it
already follows from additivity `(P2)` by taking `r = s = t`, and the monotonicity of the
associated counting process `t ↦ NI 0 t` is derived from the same additivity. -/
def HasPoissonIntervalCountProperties
    (α : NNReal) (P : Measure Ω) (NI : NNReal → NNReal → Ω → ℕ) : Prop :=
  (∀ s t, s ≤ t → Measurable (NI s t)) ∧
    (∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω) ∧
      HasIndepIncrements (fun t ω ↦ NI 0 t ω) P ∧
      (∀ s t, s ≤ t → IdentDistrib (NI s t) (NI 0 (t - s)) P P) ∧
      (Tendsto
          (fun h : NNReal ↦ (P {ω | NI 0 h ω = 1}).toReal / (h : ℝ))
          (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (α : ℝ)) ∧
        Tendsto
          (fun h : NNReal ↦ (P {ω | 2 ≤ NI 0 h ω}).toReal / (h : ℝ))
          (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)))

/-- The interval-count family in this item consists of random variables. -/
theorem HasPoissonIntervalCountProperties.measurable
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    ∀ s t, s ≤ t → Measurable (NI s t) := by
  rcases hNI with ⟨hmeasurable, -, -, -, -⟩
  exact hmeasurable

/-- The associated counting process `t ↦ N_(0,t]` is stochastic. -/
theorem HasPoissonIntervalCountProperties.stochastic
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    IsStochasticProcess (fun t ω ↦ NI 0 t ω) := by
  intro t
  exact hNI.measurable 0 t bot_le

/-- For `ℕ`-valued interval counts, the textbook zero-time axiom `(P1)` follows from additivity
`(P2)` by taking `r = s = t`. -/
theorem HasPoissonIntervalCountProperties.zero
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    ∀ s, NI s s = 0 := by
  intro s
  have hadditive : ∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω := by
    rcases hNI with ⟨-, h, -, -, -⟩
    exact h
  ext ω
  have hω := congrFun (hadditive s s s le_rfl le_rfl) ω
  have hω' : NI s s ω + 0 = NI s s ω + NI s s ω := by simpa using hω
  simpa using (Nat.add_left_cancel hω').symm

/-- `(P2)` on the interval-count side of this item. -/
theorem HasPoissonIntervalCountProperties.additive
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    ∀ r s t, r ≤ s → s ≤ t → NI r t = fun ω ↦ NI r s ω + NI s t ω := by
  rcases hNI with ⟨-, hadditive, -, -, -⟩
  exact hadditive

/-- Additivity of interval counts makes the associated counting process `t ↦ N_(0,t]`
nondecreasing. -/
theorem HasPoissonIntervalCountProperties.mono
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    Monotone (fun t ω ↦ NI 0 t ω) := by
  intro s t hst ω
  have hω := congrFun (hNI.additive 0 s t bot_le hst) ω
  exact Nat.le.intro hω.symm

/-- `(P3)` on the interval-count side of this item, expressed in the owner API
`HasIndepIncrements`. -/
theorem HasPoissonIntervalCountProperties.indepIncrements
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    HasIndepIncrements (fun t ω ↦ NI 0 t ω) P := by
  rcases hNI with ⟨-, -, hindep, -, -⟩
  exact hindep

/-- The interval-count axioms already force the ambient measure to be a probability measure,
because independent increments over a constant time sequence yield an independent family. -/
theorem HasPoissonIntervalCountProperties.isProbabilityMeasure
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    IsProbabilityMeasure P := by
  let hconst : Monotone (fun _ : ℕ ↦ (0 : NNReal)) := fun _ _ _ ↦ le_rfl
  exact (hNI.indepIncrements.nat hconst).isProbabilityMeasure

/-- `(P4)` on the interval-count side of this item. -/
theorem HasPoissonIntervalCountProperties.stationary
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    ∀ s t, s ≤ t → IdentDistrib (NI s t) (NI 0 (t - s)) P P := by
  rcases hNI with ⟨-, -, -, hstationary, -⟩
  exact hstationary

/-- `(P5)` on the interval-count side of this item. -/
theorem HasPoissonIntervalCountProperties.smallTime
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    Tendsto
        (fun h : NNReal ↦ (P {ω | NI 0 h ω = 1}).toReal / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (α : ℝ)) ∧
      Tendsto
        (fun h : NNReal ↦ (P {ω | 2 ≤ NI 0 h ω}).toReal / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)) := by
  rcases hNI with ⟨-, -, -, -, hsmall⟩
  exact hsmall

/-- Helper for Theorem 5.34: the singleton mass of `poissonMeasure r` is the explicit Poisson PMF
value. -/
private theorem poissonMeasure_apply_singleton_eq
    (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite `poissonMeasure` as the measure attached to the Poisson PMF.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Theorem 5.34: the Poisson law with rate `r` assigns mass `e^{-r}` to `0`. -/
private theorem poissonMeasure_apply_zero_toReal
    (r : NNReal) :
    ((poissonMeasure r) ({0} : Set ℕ)).toReal = Real.exp (-(r : ℝ)) := by
  -- Proof comment: specialize the singleton formula at `0` and simplify the PMF term.
  rw [poissonMeasure_apply_singleton_eq, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  simp [poissonPMFReal]

/-- Helper for Theorem 5.34: the Poisson law with rate `r` assigns mass `e^{-r} r` to `1`. -/
private theorem poissonMeasure_apply_one_toReal
    (r : NNReal) :
    ((poissonMeasure r) ({1} : Set ℕ)).toReal = Real.exp (-(r : ℝ)) * (r : ℝ) := by
  -- Proof comment: specialize the singleton formula at `1` and collapse the factorial term.
  rw [poissonMeasure_apply_singleton_eq, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  simp [poissonPMFReal]

/-- Helper for Theorem 5.34: the Poisson tail above `1` has the explicit remainder form from the
exponential series. -/
private theorem poissonMeasure_apply_ge_two_toReal
    (r : NNReal) :
    ((poissonMeasure r) {n : ℕ | 2 ≤ n}).toReal =
      Real.exp (-(r : ℝ)) * (Real.exp (r : ℝ) - 1 - (r : ℝ)) := by
  let A : Set ℕ := {n : ℕ | 2 ≤ n}
  have hA_meas : MeasurableSet A := by
    simp [A]
  have hA_compl : Aᶜ = ({0} : Set ℕ) ∪ ({1} : Set ℕ) := by
    ext n
    simp [A]
    omega
  have hRealCompl :
      (poissonMeasure r).real A +
          (poissonMeasure r).real ((({0} : Set ℕ) ∪ ({1} : Set ℕ))) = 1 := by
    -- Proof comment: the tail set and its complement partition the whole space.
    simpa [hA_compl] using
      (show (poissonMeasure r).real A + (poissonMeasure r).real Aᶜ =
          (poissonMeasure r).real Set.univ from
        MeasureTheory.measureReal_add_measureReal_compl hA_meas)
  have hRealUnion :
      (poissonMeasure r).real ((({0} : Set ℕ) ∪ ({1} : Set ℕ))) =
        (poissonMeasure r).real ({0} : Set ℕ) +
          (poissonMeasure r).real ({1} : Set ℕ) := by
    -- Proof comment: the two singleton atoms are disjoint, so their masses add.
    simpa using
      (show (poissonMeasure r).real ((({0} : Set ℕ) ∪ ({1} : Set ℕ))) =
          (poissonMeasure r).real ({0} : Set ℕ) +
            (poissonMeasure r).real ({1} : Set ℕ) from
        MeasureTheory.measureReal_union (by simp) (measurableSet_singleton (1 : ℕ)))
  have hTail :
      (poissonMeasure r).real A =
        1 - (poissonMeasure r).real ({0} : Set ℕ) - (poissonMeasure r).real ({1} : Set ℕ) := by
    linarith
  have hTailToReal :
      ((poissonMeasure r) A).toReal =
        1 - ((poissonMeasure r) ({0} : Set ℕ)).toReal -
          ((poissonMeasure r) ({1} : Set ℕ)).toReal := by
    simpa [MeasureTheory.Measure.real_def] using hTail
  -- Proof comment: rewrite the complement mass as the second-order exponential remainder.
  have hExp :
      (1 : ℝ) = Real.exp (-(r : ℝ)) * Real.exp (r : ℝ) := by
    rw [← Real.exp_add]
    ring_nf
    rw [Real.exp_zero]
  calc
    ((poissonMeasure r) {n : ℕ | 2 ≤ n}).toReal
        = 1 - Real.exp (-(r : ℝ)) - Real.exp (-(r : ℝ)) * (r : ℝ) := by
            simpa [A, poissonMeasure_apply_zero_toReal, poissonMeasure_apply_one_toReal] using
              hTailToReal
    _ = 1 - Real.exp (-(r : ℝ)) - Real.exp (-(r : ℝ)) * (r : ℝ) := by rfl
    _ = Real.exp (-(r : ℝ)) * Real.exp (r : ℝ) -
            Real.exp (-(r : ℝ)) - Real.exp (-(r : ℝ)) * (r : ℝ) := by
            rw [hExp]
    _ = Real.exp (-(r : ℝ)) * (Real.exp (r : ℝ) - 1 - (r : ℝ)) := by
          ring

/-- Helper for Theorem 5.34: the Poisson law has the textbook first- and second-order small-time
asymptotics. -/
private theorem poissonMeasure_smallTime
    (α : NNReal) :
    Tendsto
        (fun h : NNReal ↦ ((poissonMeasure (α * h)) ({1} : Set ℕ)).toReal / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (α : ℝ)) ∧
      Tendsto
        (fun h : NNReal ↦
          ((poissonMeasure (α * h)) {n : ℕ | 2 ≤ n}).toReal / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)) := by
  -- The source small-time condition is right-sided: `h ↓ 0` with `h > 0`.
  constructor
  · have hEventually :
        Filter.EventuallyEq
          (nhdsWithin (0 : NNReal) (Set.Ioi 0))
          (fun h : NNReal ↦ ((poissonMeasure (α * h)) ({1} : Set ℕ)).toReal / (h : ℝ))
          (fun h : NNReal ↦ (α : ℝ) * Real.exp (-(((α * h : NNReal) : ℝ)))) := by
      -- Proof comment: on the punctured neighborhood, the singleton mass quotient simplifies
      -- to the explicit first-order Poisson term.
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hh)
      rw [poissonMeasure_apply_one_toReal]
      field_simp [hh0]
      rw [NNReal.coe_mul, mul_comm]
    have hLimit :
        Tendsto (fun h : NNReal ↦ (α : ℝ) * Real.exp (-(((α * h : NNReal) : ℝ))))
          (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (α : ℝ)) := by
      -- Proof comment: the simplified quotient extends continuously to `α` at `h = 0`.
      have hcont :
          Continuous fun h : NNReal ↦ (α : ℝ) * Real.exp (-(((α * h : NNReal) : ℝ))) := by
        fun_prop
      have hcont0 :
          ContinuousAt
            (fun h : NNReal ↦ (α : ℝ) * Real.exp (-(((α * h : NNReal) : ℝ))))
            (0 : NNReal) :=
        hcont.continuousAt
      simpa using hcont0.continuousWithinAt.tendsto
    exact hLimit.congr' hEventually.symm
  · have hSmall :
        ∀ᶠ h in nhdsWithin (0 : NNReal) (Set.Ioi 0), (((α * h : NNReal) : ℝ)) < 1 := by
      -- Proof comment: sufficiently close to `0`, the Poisson parameter lies in `[0,1)`.
      have hTendsto :
          Tendsto (fun h : NNReal ↦ (((α * h : NNReal) : ℝ)))
            (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)) := by
        have hcont : Continuous fun h : NNReal ↦ (((α * h : NNReal) : ℝ)) := by
          fun_prop
        have hcont0 : ContinuousAt (fun h : NNReal ↦ (((α * h : NNReal) : ℝ))) (0 : NNReal) :=
          hcont.continuousAt
        simpa using hcont0.continuousWithinAt.tendsto
      exact hTendsto (Iio_mem_nhds zero_lt_one)
    have hBound :
        ∀ᶠ h in nhdsWithin (0 : NNReal) (Set.Ioi 0),
          0 ≤ ((poissonMeasure (α * h)) {n : ℕ | 2 ≤ n}).toReal / (h : ℝ) ∧
            ((poissonMeasure (α * h)) {n : ℕ | 2 ≤ n}).toReal / (h : ℝ) ≤
              (α : ℝ) ^ 2 * (h : ℝ) := by
      -- Proof comment: the second-order remainder is controlled by the quadratic exponential
      -- error term `exp x - 1 - x = O(x^2)`.
      filter_upwards [self_mem_nhdsWithin, hSmall] with h hh hx
      have hh0 : 0 < (h : ℝ) := by exact_mod_cast hh
      let x : ℝ := (((α * h : NNReal) : ℝ))
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        positivity
      have hExpNeg_le : Real.exp (-x) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      have hRemainder_nonneg : 0 ≤ Real.exp x - 1 - x := by
        linarith [Real.add_one_le_exp x]
      have hRemainder_le : Real.exp x - 1 - x ≤ x ^ 2 := by
        have hNorm := Real.norm_exp_sub_one_sub_id_le (x := x) (by
          rw [Real.norm_of_nonneg hx_nonneg]
          linarith)
        simpa [abs_of_nonneg hRemainder_nonneg, Real.norm_of_nonneg hx_nonneg] using hNorm
      rw [poissonMeasure_apply_ge_two_toReal]
      constructor
      · positivity
      · calc
          Real.exp (-x) * (Real.exp x - 1 - x) / (h : ℝ)
              ≤ x ^ 2 / (h : ℝ) := by
                have hMul :
                    Real.exp (-x) * (Real.exp x - 1 - x) ≤ x ^ 2 := by
                  have hMulOne :
                      Real.exp (-x) * (Real.exp x - 1 - x) ≤ 1 * (Real.exp x - 1 - x) :=
                    mul_le_mul_of_nonneg_right hExpNeg_le hRemainder_nonneg
                  exact hMulOne.trans (by simpa using hRemainder_le)
                exact div_le_div_of_nonneg_right hMul hh0.le
          _ = (α : ℝ) ^ 2 * (h : ℝ) := by
                dsimp [x]
                have hh0' : (h : ℝ) ≠ 0 := ne_of_gt hh0
                field_simp [hh0']
    have hUpper :
        Tendsto (fun h : NNReal ↦ (α : ℝ) ^ 2 * (h : ℝ))
          (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)) := by
      -- Proof comment: the linear upper bound vanishes with `h`.
      have hcont : Continuous fun h : NNReal ↦ (α : ℝ) ^ 2 * (h : ℝ) := by
        fun_prop
      have hcont0 :
          ContinuousAt (fun h : NNReal ↦ (α : ℝ) ^ 2 * (h : ℝ)) (0 : NNReal) :=
        hcont.continuousAt
      simpa using hcont0.continuousWithinAt.tendsto
    exact squeeze_zero'
      (hBound.mono fun _ hh ↦ hh.1)
      (hBound.mono fun _ hh ↦ hh.2)
      hUpper

/-- Helper for Theorem 5.34: the origin-started count at time `t` viewed as a law on `ℕ`. -/
private noncomputable abbrev zeroStartedCountLaw
    (P : Measure Ω) (NI : NNReal → NNReal → Ω → ℕ) (t : NNReal) : Measure ℕ :=
  P.map (NI 0 t)

/-- Helper for Theorem 5.34: the singleton mass at `n` of the origin-started count law at time
`t`. -/
private noncomputable abbrev zeroStartedCountMass
    (P : Measure Ω) (NI : NNReal → NNReal → Ω → ℕ) (t : NNReal) (n : ℕ) : ℝ :=
  ((zeroStartedCountLaw P NI t) ({n} : Set ℕ)).toReal

/-- Helper for Theorem 5.34: the tail mass above `1` of the origin-started count law at time
`t`. -/
private noncomputable abbrev zeroStartedCountTailMass
    (P : Measure Ω) (NI : NNReal → NNReal → Ω → ℕ) (t : NNReal) : ℝ :=
  ((zeroStartedCountLaw P NI t) {n : ℕ | 2 ≤ n}).toReal

/-- Helper for Theorem 5.34: the origin-started count law at time `t`, packaged as a `PMF`. -/
private noncomputable abbrev zeroStartedCountPMF
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) (t : NNReal) : PMF ℕ :=
  letI : IsProbabilityMeasure P := hNI.isProbabilityMeasure
  letI : IsProbabilityMeasure (zeroStartedCountLaw P NI t) :=
    Measure.isProbabilityMeasure_map (hNI.measurable 0 t bot_le).aemeasurable
  (zeroStartedCountLaw P NI t).toPMF

/-- Helper for Theorem 5.34: every probability measure on `ℕ` splits into the masses at `0`, `1`,
and the tail above `1`. -/
private theorem natMeasure_apply_zero_toReal_eq_one_sub_apply_one_sub_tail
    (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (μ ({0} : Set ℕ)).toReal =
      1 - (μ ({1} : Set ℕ)).toReal - (μ {n : ℕ | 2 ≤ n}).toReal := by
  let A : Set ℕ := {n : ℕ | 2 ≤ n}
  have hA_meas : MeasurableSet A := by
    simp [A]
  have hA_compl : Aᶜ = ({0} : Set ℕ) ∪ ({1} : Set ℕ) := by
    ext n
    simp [A]
    omega
  have hRealCompl :
      μ.real A + μ.real ((({0} : Set ℕ) ∪ ({1} : Set ℕ))) = 1 := by
    -- Proof comment: the tail set and its complement partition all of `ℕ`.
    simpa [hA_compl] using
      (show μ.real A + μ.real Aᶜ = μ.real Set.univ from
        MeasureTheory.measureReal_add_measureReal_compl hA_meas)
  have hRealUnion :
      μ.real ((({0} : Set ℕ) ∪ ({1} : Set ℕ))) =
        μ.real ({0} : Set ℕ) + μ.real ({1} : Set ℕ) := by
    -- Proof comment: the singleton masses at `0` and `1` are disjoint and therefore add.
    simpa using
      (show μ.real ((({0} : Set ℕ) ∪ ({1} : Set ℕ))) =
          μ.real ({0} : Set ℕ) + μ.real ({1} : Set ℕ) from
        MeasureTheory.measureReal_union (by simp) (measurableSet_singleton (1 : ℕ)))
  have hZero :
      μ.real ({0} : Set ℕ) = 1 - μ.real ({1} : Set ℕ) - μ.real A := by
    linarith
  -- Proof comment: convert the real-valued measure identity back to `toReal`.
  simpa [MeasureTheory.Measure.real_def, A] using hZero

/-- Helper for Theorem 5.34: `(P5)` becomes the exact zero/one/tail small-time asymptotics for the
origin-started laws `P.map (NI 0 h)`. -/
private theorem zeroStartedCountMass_smallTime
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    Tendsto
        (fun h : NNReal ↦ zeroStartedCountMass P NI h 1 / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (α : ℝ)) ∧
      Tendsto
        (fun h : NNReal ↦ zeroStartedCountTailMass P NI h / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)) ∧
      Tendsto
        (fun h : NNReal ↦ (zeroStartedCountMass P NI h 0 - 1) / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (-(α : ℝ))) := by
  letI := hNI.isProbabilityMeasure
  rcases hNI.smallTime with ⟨hOneRaw, hTailRaw⟩
  have hOneEq :
      (fun h : NNReal ↦ zeroStartedCountMass P NI h 1 / (h : ℝ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun h : NNReal ↦ (P {ω | NI 0 h ω = 1}).toReal / (h : ℝ)) := by
    filter_upwards with h
    rw [zeroStartedCountMass, zeroStartedCountLaw,
      Measure.map_apply (hNI.measurable 0 h bot_le) (measurableSet_singleton 1)]
    rfl
  have hTailEq :
      (fun h : NNReal ↦ zeroStartedCountTailMass P NI h / (h : ℝ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun h : NNReal ↦ (P {ω | 2 ≤ NI 0 h ω}).toReal / (h : ℝ)) := by
    filter_upwards with h
    rw [zeroStartedCountTailMass, zeroStartedCountLaw,
      Measure.map_apply (hNI.measurable 0 h bot_le)
        (by simp)]
    simp
  have hZeroEq :
      (fun h : NNReal ↦ (zeroStartedCountMass P NI h 0 - 1) / (h : ℝ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun h : NNReal ↦
          -(zeroStartedCountMass P NI h 1 / (h : ℝ)) -
            zeroStartedCountTailMass P NI h / (h : ℝ)) := by
    filter_upwards with h
    letI : IsProbabilityMeasure (zeroStartedCountLaw P NI h) :=
      Measure.isProbabilityMeasure_map (hNI.measurable 0 h bot_le).aemeasurable
    have hMass :
        zeroStartedCountMass P NI h 0 =
          1 - zeroStartedCountMass P NI h 1 - zeroStartedCountTailMass P NI h := by
      simpa [zeroStartedCountMass, zeroStartedCountTailMass, zeroStartedCountLaw] using
        natMeasure_apply_zero_toReal_eq_one_sub_apply_one_sub_tail
          (μ := zeroStartedCountLaw P NI h)
    -- Proof comment: the zero mass is exactly the complement of the one-jump and multi-jump
    -- masses, so its quotient is the negative sum of the other two quotients.
    rw [hMass]
    ring
  have hOne :
      Tendsto
        (fun h : NNReal ↦ zeroStartedCountMass P NI h 1 / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (α : ℝ)) :=
    hOneRaw.congr' hOneEq.symm
  have hTail :
      Tendsto
        (fun h : NNReal ↦ zeroStartedCountTailMass P NI h / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)) :=
    hTailRaw.congr' hTailEq.symm
  have hZero :
      Tendsto
        (fun h : NNReal ↦
          -(zeroStartedCountMass P NI h 1 / (h : ℝ)) -
            zeroStartedCountTailMass P NI h / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (-(α : ℝ))) := by
    -- Proof comment: the zero-mass quotient is the negative sum of the first-jump and tail
    -- quotients, and both components already have limits from `(P5)`.
    simpa using hOne.neg.sub hTail
  exact ⟨hOne, hTail, hZero.congr' hZeroEq.symm⟩

/-- Helper for Theorem 5.34: the equal mesh `t / (n + 1)` tends to `0` through the punctured
right neighborhood when `t > 0`. -/
private theorem zeroStartedCountMesh_tendsto_zeroWithin
    (t : NNReal) (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ t / (n + 1)) atTop (nhdsWithin (0 : NNReal) (Set.Ioi 0)) := by
  have hToZero :
      Tendsto (fun n : ℕ ↦ t / (n + 1)) atTop (nhds (0 : NNReal)) := by
    -- Proof comment: factor the mesh as `t * (n + 1)⁻¹` and use the standard reciprocal limit.
    have hMul :
        Tendsto (fun n : ℕ ↦ t * (1 / ((n : NNReal) + 1))) atTop (nhds (t * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hMul
  have hEventuallyPos : ∀ᶠ n : ℕ in atTop, t / (n + 1) ∈ Set.Ioi (0 : NNReal) := by
    -- Proof comment: every mesh size is positive because both `t` and `n + 1` are positive.
    exact Filter.Eventually.of_forall fun n ↦ by
      exact div_pos ht (show (0 : NNReal) < n + 1 by exact_mod_cast Nat.succ_pos n)
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (fun n : ℕ ↦ t / (n + 1)) hToZero hEventuallyPos

/-- Helper for Theorem 5.34: the pushforward law of a measurable `ℕ`-valued random variable,
packaged as a `PMF`. -/
private noncomputable abbrev mappedNatLaw
    (P : Measure Ω) (hP : IsProbabilityMeasure P) (X : Ω → ℕ) (hX : Measurable X) : PMF ℕ :=
  letI : IsProbabilityMeasure P := hP
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  (P.map X).toPMF

/-- Helper for Theorem 5.34: the real-valued pgf of the pushforward law of an `ℕ`-valued random
variable is the expectation of the power map `ω ↦ z ^ X ω`. -/
private theorem probabilityGeneratingFunctionReal_map_toPMF_eq_integral
    {P : Measure Ω} [IsProbabilityMeasure P] (X : Ω → ℕ) (hX : Measurable X)
    (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal (mappedNatLaw P ‹_› X hX) z =
      ∫ ω, (z : ℝ) ^ X ω ∂P := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hPowMeas : Measurable (fun n : ℕ ↦ (z : ℝ) ^ n) := by
    fun_prop
  have hPowIntegrableMap : Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) (P.map X) := by
    -- Proof comment: on `[0, 1]`, every power of `z` is bounded by `1`, so the power map is
    -- integrable against the pushed-forward probability law.
    refine Integrable.of_bound hPowMeas.aestronglyMeasurable 1 ?_
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg z.2.1 n)]
    simpa using (pow_le_one₀ z.2.1 z.2.2 : (z : ℝ) ^ n ≤ 1)
  have hPowIntegrableLaw :
      Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) ((P.map X).toPMF.toMeasure) := by
    simpa [Measure.toPMF_toMeasure] using hPowIntegrableMap
  calc
    probabilityGeneratingFunctionReal (mappedNatLaw P ‹_› X hX) z
      = ∑' n : ℕ, (((P.map X).toPMF) n).toReal * (z : ℝ) ^ n := by
          simp [mappedNatLaw, probabilityGeneratingFunctionReal_apply]
    _ = ∫ n, (z : ℝ) ^ n ∂((P.map X).toPMF.toMeasure) := by
          -- Proof comment: the pgf series is exactly the integral of `n ↦ z ^ n` against the
          -- law `PMF`.
          symm
          rw [PMF.integral_eq_tsum _ _ hPowIntegrableLaw]
          simp [smul_eq_mul]
    _ = ∫ n, (z : ℝ) ^ n ∂(P.map X) := by
          simp [Measure.toPMF_toMeasure]
    _ = ∫ ω, (z : ℝ) ^ X ω ∂P := by
          rw [integral_map hX.aemeasurable hPowMeas.aestronglyMeasurable]

/-- Helper for Theorem 5.34: the real pgf of the Poisson law is the exponential formula from
Example 3.4, rewritten through `toPMF`. -/
private theorem poissonMeasure_probabilityGeneratingFunctionReal_eq
    (lam : NNReal) (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal ((poissonMeasure lam).toPMF) z =
      Real.exp ((lam : ℝ) * ((z : ℝ) - 1)) := by
  letI : IsProbabilityMeasure (poissonMeasure lam) := inferInstance
  -- Proof comment: compare the `toPMF` coefficients with the singleton-mass generating series
  -- from Example 3.4.
  calc
    probabilityGeneratingFunctionReal ((poissonMeasure lam).toPMF) z
        = probabilityGeneratingSeries (poissonMeasure lam) z := by
            rw [probabilityGeneratingFunctionReal_apply, probabilityGeneratingSeries]
            refine tsum_congr fun n ↦ ?_
            rw [Measure.toPMF_apply]
    _ = Real.exp ((lam : ℝ) * ((z : ℝ) - 1)) := example_3_4_poisson_pgf lam z

/-- Helper for Theorem 5.34: the zero-started interval-count laws form a pgf semigroup on
`[0,1]`. -/
private theorem zeroStartedCountLawPgf_add
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI)
    (z : Set.Icc (0 : ℝ) 1) (s t : NNReal) :
    probabilityGeneratingFunctionReal
        (mappedNatLaw P hNI.isProbabilityMeasure
          (NI 0 (s + t)) (hNI.measurable 0 (s + t) bot_le)) z =
      probabilityGeneratingFunctionReal
        (mappedNatLaw P hNI.isProbabilityMeasure (NI 0 s) (hNI.measurable 0 s bot_le)) z *
        probabilityGeneratingFunctionReal
          (mappedNatLaw P hNI.isProbabilityMeasure (NI 0 t) (hNI.measurable 0 t bot_le)) z := by
  letI := hNI.isProbabilityMeasure
  have hst : s ≤ s + t := by
    exact le_add_of_nonneg_right t.2
  let τ : Fin 3 → NNReal
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => s
    | _ => s + t
  have hτmono : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [τ] at hij ⊢
  have hIncrIndep :
      iIndepFun
        (fun (i : Fin 2) ω ↦
          (fun u ω' ↦ NI 0 u ω') (τ i.succ) ω -
            (fun u ω' ↦ NI 0 u ω') (τ i.castSucc) ω) P :=
    hNI.indepIncrements 2 τ hτmono
  have hindep :
      (NI 0 s) ⟂ᵢ[P] (NI s (s + t)) := by
    -- Proof comment: specialize `(P3)` to the time grid `0 ≤ s ≤ s + t` and then rewrite the
    -- two adjacent increments using the zero-time and additivity identities from `(P1)` and
    -- `(P2)`.
    refine (hIncrIndep.indepFun (show (0 : Fin 2) ≠ 1 by decide)).congr ?_ ?_
    · exact Filter.Eventually.of_forall fun ω ↦ by
        simp [τ, congrFun (hNI.zero 0) ω]
    · exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [τ] using (congrFun (poissonIntervalCount_increment_eq_sub hNI.additive hst) ω).symm
  have hPowNatMeas : Measurable (fun n : ℕ ↦ (z : ℝ) ^ n) := by
    fun_prop
  have hPowIndep :
      (fun ω ↦ (z : ℝ) ^ NI 0 s ω) ⟂ᵢ[P] (fun ω ↦ (z : ℝ) ^ NI s (s + t) ω) :=
    hindep.comp hPowNatMeas hPowNatMeas
  have hPowLeft :
      AEStronglyMeasurable (fun ω ↦ (z : ℝ) ^ NI 0 s ω) P := by
    exact ((hNI.measurable 0 s bot_le).const_pow (z : ℝ)).aestronglyMeasurable
  have hPowRight :
      AEStronglyMeasurable (fun ω ↦ (z : ℝ) ^ NI s (s + t) ω) P := by
    exact ((hNI.measurable s (s + t) hst).const_pow (z : ℝ)).aestronglyMeasurable
  have hStationaryPow :
      ∫ ω, (z : ℝ) ^ NI s (s + t) ω ∂P = ∫ ω, (z : ℝ) ^ NI 0 t ω ∂P := by
    -- Proof comment: `(P4)` identifies the interval count over `(s, s + t]` with the origin
    -- started count over `(0, t]`, so the power expectations agree.
    simpa [Function.comp, add_tsub_cancel_left] using
      ((hNI.stationary s (s + t) hst).comp hPowNatMeas).integral_eq
  calc
    probabilityGeneratingFunctionReal
        (mappedNatLaw P hNI.isProbabilityMeasure
          (NI 0 (s + t)) (hNI.measurable 0 (s + t) bot_le)) z
      = ∫ ω, (z : ℝ) ^ NI 0 (s + t) ω ∂P := by
          simpa using
            probabilityGeneratingFunctionReal_map_toPMF_eq_integral
              (P := P) (X := NI 0 (s + t)) (hX := hNI.measurable 0 (s + t) bot_le) z
    _ = ∫ ω, ((z : ℝ) ^ NI 0 s ω) * ((z : ℝ) ^ NI s (s + t) ω) ∂P := by
          -- Proof comment: use `(P2)` to split the count on `(0, s + t]` into the adjacent
          -- intervals `(0, s]` and `(s, s + t]`.
          congr with ω
          rw [congrFun (hNI.additive 0 s (s + t) bot_le hst) ω, pow_add]
    _ = (∫ ω, (z : ℝ) ^ NI 0 s ω ∂P) * (∫ ω, (z : ℝ) ^ NI s (s + t) ω ∂P) := by
          exact hPowIndep.integral_mul_eq_mul_integral hPowLeft hPowRight
    _ = (∫ ω, (z : ℝ) ^ NI 0 s ω ∂P) * (∫ ω, (z : ℝ) ^ NI 0 t ω ∂P) := by
          rw [hStationaryPow]
    _ = probabilityGeneratingFunctionReal
          (mappedNatLaw P hNI.isProbabilityMeasure (NI 0 s) (hNI.measurable 0 s bot_le)) z *
        probabilityGeneratingFunctionReal
          (mappedNatLaw P hNI.isProbabilityMeasure (NI 0 t) (hNI.measurable 0 t bot_le)) z := by
          rw [← (show
            probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure (NI 0 s) (hNI.measurable 0 s bot_le)) z =
                ∫ ω, (z : ℝ) ^ NI 0 s ω ∂P by
                  simpa using
                    probabilityGeneratingFunctionReal_map_toPMF_eq_integral
                      (P := P) (X := NI 0 s) (hX := hNI.measurable 0 s bot_le) z),
            ← (show
            probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure (NI 0 t) (hNI.measurable 0 t bot_le)) z =
                ∫ ω, (z : ℝ) ^ NI 0 t ω ∂P by
                  simpa using
            probabilityGeneratingFunctionReal_map_toPMF_eq_integral
                      (P := P) (X := NI 0 t) (hX := hNI.measurable 0 t bot_le) z)]

/-- Helper for Theorem 5.34: iterating the pgf semigroup over equal mesh intervals turns time
`n • u` into the `n`th power of the one-step pgf. -/
private theorem zeroStartedCountLawPgf_nsmul
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI)
    (z : Set.Icc (0 : ℝ) 1) (u : NNReal) :
    ∀ n : ℕ,
      probabilityGeneratingFunctionReal
          (mappedNatLaw P hNI.isProbabilityMeasure
            (NI 0 (n • u)) (hNI.measurable 0 (n • u) bot_le)) z =
        probabilityGeneratingFunctionReal
          (mappedNatLaw P hNI.isProbabilityMeasure
            (NI 0 u) (hNI.measurable 0 u bot_le)) z ^ n
  | 0 => by
      letI := hNI.isProbabilityMeasure
      -- Proof comment: at time `0`, the count is almost surely `0`, so the pgf is `1`.
      have hzeroEval :
          probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure
                (NI 0 (0 • u)) (hNI.measurable 0 (0 • u) bot_le)) z = 1 := by
        rw [zero_nsmul, probabilityGeneratingFunctionReal_map_toPMF_eq_integral
          (P := P) (X := NI 0 0) (hX := hNI.measurable 0 0 bot_le) z]
        -- Proof comment: `(P1)` identifies the origin-started zero-time count with `0`.
        simp [hNI.zero 0]
      simpa using hzeroEval
  | n + 1 => by
      letI := hNI.isProbabilityMeasure
      -- Proof comment: split `(n + 1) • u` as `n • u + u` and apply the binary semigroup step.
      calc
        probabilityGeneratingFunctionReal
            (mappedNatLaw P hNI.isProbabilityMeasure
              (NI 0 ((n + 1) • u)) (hNI.measurable 0 ((n + 1) • u) bot_le)) z
          = probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure
                (NI 0 (n • u + u)) (hNI.measurable 0 (n • u + u) bot_le)) z := by
                  rw [succ_nsmul]
        _ = probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure
                (NI 0 (n • u)) (hNI.measurable 0 (n • u) bot_le)) z *
            probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure
                (NI 0 u) (hNI.measurable 0 u bot_le)) z := by
                  simpa [succ_nsmul] using zeroStartedCountLawPgf_add hNI z (n • u) u
        _ =
            probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure
                (NI 0 u) (hNI.measurable 0 u bot_le)) z ^ n *
              probabilityGeneratingFunctionReal
                (mappedNatLaw P hNI.isProbabilityMeasure
                  (NI 0 u) (hNI.measurable 0 u bot_le)) z := by
                    rw [zeroStartedCountLawPgf_nsmul hNI z u n]
        _ =
            probabilityGeneratingFunctionReal
              (mappedNatLaw P hNI.isProbabilityMeasure
                (NI 0 u) (hNI.measurable 0 u bot_le)) z ^ (n + 1) := by
                  rw [pow_succ, mul_comm]

/-- Helper for Theorem 5.34: after removing the singleton contribution, the pgf error is bounded
by the multi-jump tail mass. -/
private theorem zeroStartedCountLawPgf_error_le_tail
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI)
    (z : Set.Icc (0 : ℝ) 1) (h : NNReal) :
    ‖probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1 -
        ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1‖ ≤
      zeroStartedCountTailMass P NI h := by
  let μ : Measure ℕ := zeroStartedCountLaw P NI h
  letI : IsProbabilityMeasure P := hNI.isProbabilityMeasure
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (hNI.measurable 0 h bot_le).aemeasurable
  let oneSet : Set ℕ := ({1} : Set ℕ)
  let tailSet : Set ℕ := {n : ℕ | 2 ≤ n}
  let indicatorOne : ℕ → ℝ := oneSet.indicator (fun _ ↦ (1 : ℝ))
  let indicatorTail : ℕ → ℝ := tailSet.indicator (fun _ ↦ (1 : ℝ))
  let remainder : ℕ → ℝ := fun n ↦ (z : ℝ) ^ n - 1 - ((z : ℝ) - 1) * indicatorOne n
  have hPgf :
      probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z =
        ∫ n, (z : ℝ) ^ n ∂μ := by
    -- Proof comment: the pgf of the origin-started law is the expectation of the power map.
    simpa [zeroStartedCountPMF, μ, zeroStartedCountLaw, mappedNatLaw] using
      probabilityGeneratingFunctionReal_map_toPMF_eq_integral
        (P := μ) (X := id) (hX := measurable_id) z
  have hPowIntegrable : Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) μ := by
    -- Proof comment: on `[0,1]`, the power map is uniformly bounded by `1`.
    refine Integrable.of_bound (measurable_id.const_pow (z : ℝ)).aestronglyMeasurable 1 ?_
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg z.2.1 n)]
    exact pow_le_one₀ z.2.1 z.2.2
  have hConstIntegrable : Integrable (fun _ : ℕ ↦ (1 : ℝ)) μ := integrable_const 1
  have hIndicatorOneIntegrable : Integrable indicatorOne μ :=
    hConstIntegrable.indicator (measurableSet_singleton 1)
  have hIndicatorTailIntegrable : Integrable indicatorTail μ := by
    refine hConstIntegrable.indicator ?_
    simp [tailSet]
  have hIndicatorOne :
      ∫ n, indicatorOne n ∂μ = zeroStartedCountMass P NI h 1 := by
    -- Proof comment: the integral of the singleton indicator is exactly the singleton mass.
    simpa [indicatorOne, oneSet, μ, zeroStartedCountMass, zeroStartedCountLaw,
      MeasureTheory.Measure.real_def] using
      (MeasureTheory.integral_indicator_one (μ := μ) (s := oneSet)
        (measurableSet_singleton 1))
  have hIndicatorTail :
      ∫ n, indicatorTail n ∂μ = zeroStartedCountTailMass P NI h := by
    -- Proof comment: the same identity evaluates the tail indicator integral as the tail mass.
    simpa [indicatorTail, tailSet, μ, zeroStartedCountTailMass, zeroStartedCountLaw,
      MeasureTheory.Measure.real_def] using
      (MeasureTheory.integral_indicator_one (μ := μ) (s := tailSet)
        (by simp [tailSet]))
  have hIntegralOne : ∫ n, (1 : ℝ) ∂μ = 1 := by
    -- Proof comment: `μ` is a probability measure, so the integral of `1` is `1`.
    simpa [MeasureTheory.Measure.real_def] using
      (MeasureTheory.integral_indicator_one (μ := μ) (s := Set.univ) measurableSet_univ)
  have hRemainderEq :
      ∫ n, remainder n ∂μ =
        probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1 -
          ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1 := by
    have hScaledIndicatorIntegrable :
        Integrable (fun n : ℕ ↦ ((z : ℝ) - 1) * indicatorOne n) μ :=
      hIndicatorOneIntegrable.const_mul ((z : ℝ) - 1)
    -- Proof comment: separate the pgf into the constant term, the singleton term, and the tail.
    calc
      ∫ n, remainder n ∂μ
          = ∫ n, ((z : ℝ) ^ n - 1) ∂μ -
              ∫ n, ((z : ℝ) - 1) * indicatorOne n ∂μ := by
                simpa [remainder] using
                  (integral_sub
                    (f := fun n : ℕ ↦ (z : ℝ) ^ n - 1)
                    (g := fun n : ℕ ↦ ((z : ℝ) - 1) * indicatorOne n)
                    (hPowIntegrable.sub hConstIntegrable)
                    hScaledIndicatorIntegrable)
      _ = (∫ n, (z : ℝ) ^ n ∂μ - ∫ n, (1 : ℝ) ∂μ) -
            ((z : ℝ) - 1) * ∫ n, indicatorOne n ∂μ := by
              rw [integral_sub hPowIntegrable hConstIntegrable,
                MeasureTheory.integral_const_mul]
      _ = probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1 -
            ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1 := by
              rw [hPgf, hIntegralOne, hIndicatorOne]
  have hPointwise :
      ∀ n : ℕ, ‖remainder n‖ ≤ indicatorTail n := by
    intro n
    by_cases h0 : n = 0
    · subst h0
      simp [remainder, indicatorOne, indicatorTail, oneSet, tailSet]
    by_cases h1 : n = 1
    · subst h1
      simp [remainder, indicatorOne, indicatorTail, oneSet, tailSet]
    have h2 : 2 ≤ n := by omega
    have hPowNonneg : 0 ≤ (z : ℝ) ^ n := pow_nonneg z.2.1 n
    have hPowLeOne : (z : ℝ) ^ n ≤ 1 := pow_le_one₀ z.2.1 z.2.2
    have hNormLe : ‖(z : ℝ) ^ n - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos]
      · linarith
      · linarith
    simpa [remainder, indicatorOne, indicatorTail, oneSet, tailSet, h0, h1, h2] using hNormLe
  have hBound :
      ‖∫ n, remainder n ∂μ‖ ≤ ∫ n, indicatorTail n ∂μ := by
    -- Proof comment: the remainder vanishes on `0` and `1`, and on the tail it is bounded by `1`.
    refine MeasureTheory.norm_integral_le_of_norm_le hIndicatorTailIntegrable ?_
    exact Filter.Eventually.of_forall hPointwise
  calc
    ‖probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1 -
        ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1‖
        = ‖∫ n, remainder n ∂μ‖ := by rw [hRemainderEq]
    _ ≤ ∫ n, indicatorTail n ∂μ := hBound
    _ = zeroStartedCountTailMass P NI h := hIndicatorTail

/-- Helper for Theorem 5.34: the pgf of the origin-started law has the expected linear small-time
asymptotic on `[0,1]`. -/
private theorem zeroStartedCountLawPgf_smallTime
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI)
    (z : Set.Icc (0 : ℝ) 1) :
    Tendsto
      (fun h : NNReal ↦
        (probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1) / (h : ℝ))
      (nhdsWithin (0 : NNReal) (Set.Ioi 0))
      (𝓝 ((α : ℝ) * ((z : ℝ) - 1))) := by
  letI := hNI.isProbabilityMeasure
  rcases zeroStartedCountMass_smallTime hNI with ⟨hOne, hTail, -⟩
  have hRemainder :
      Tendsto
        (fun h : NNReal ↦
          ((probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1) -
              ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1) / (h : ℝ))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0)) (𝓝 (0 : ℝ)) := by
    have hBound :
        ∀ᶠ h : NNReal in nhdsWithin (0 : NNReal) (Set.Ioi 0),
          ‖(((probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1) -
                ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1) / (h : ℝ))‖ ≤
            zeroStartedCountTailMass P NI h / (h : ℝ) := by
      -- Proof comment: divide the tail bound by `h`; on the punctured neighborhood, `h > 0`.
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : 0 < (h : ℝ) := by exact_mod_cast hh
      have hTailNonneg : 0 ≤ zeroStartedCountTailMass P NI h := ENNReal.toReal_nonneg
      calc
        ‖(((probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1) -
              ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1) / (h : ℝ))‖
            = ‖(probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1) -
                ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1‖ / (h : ℝ) := by
                  rw [norm_div, Real.norm_of_nonneg hh0.le]
        _ ≤ zeroStartedCountTailMass P NI h / (h : ℝ) := by
              exact div_le_div_of_nonneg_right
                (zeroStartedCountLawPgf_error_le_tail hNI z h) hh0.le
    exact squeeze_zero_norm' hBound hTail
  have hLead :
      Tendsto
        (fun h : NNReal ↦ ((z : ℝ) - 1) * (zeroStartedCountMass P NI h 1 / (h : ℝ)))
        (nhdsWithin (0 : NNReal) (Set.Ioi 0))
        (𝓝 (((z : ℝ) - 1) * (α : ℝ))) :=
    tendsto_const_nhds.mul hOne
  have hDecomp :
      (fun h : NNReal ↦
        (probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1) / (h : ℝ)) =
      (fun h : NNReal ↦
        (((probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI h) z - 1) -
              ((z : ℝ) - 1) * zeroStartedCountMass P NI h 1) / (h : ℝ)) +
          ((z : ℝ) - 1) * (zeroStartedCountMass P NI h 1 / (h : ℝ))) := by
    funext h
    ring
  -- Proof comment: the pgf quotient is the singleton contribution plus a remainder controlled by
  -- the multi-jump tail, so the limit is `α (z - 1)`.
  rw [hDecomp]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hRemainder.add hLead

/-- Helper for Theorem 5.34: the Poisson masses satisfy the standard first-moment shift identity.
-/
private theorem poissonPMFReal_succ_mul
    (r : NNReal) (n : ℕ) :
    poissonPMFReal r (n + 1) * (n + 1 : ℝ) = (r : ℝ) * poissonPMFReal r n := by
  -- Proof comment: rewrite the factorial and power at `n + 1`, then cancel the common factor
  -- `(n!)⁻¹`.
  rw [poissonPMFReal, poissonPMFReal, pow_succ, Nat.factorial_succ]
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hfac]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

/-- Helper for Theorem 5.34: the Poisson law with rate `r` has expectation `r`. -/
private theorem integral_natCast_poissonMeasure_eq
    (r : NNReal) :
    ∫ n, (n : ℝ) ∂poissonMeasure r = (r : ℝ) := by
  let c : ℕ → ENNReal := fun n ↦ poissonMeasure r ({n} : Set ℕ)
  have hc : ∀ n, c n ≠ ⊤ := by
    intro n
    rw [show c n = ENNReal.ofReal (poissonPMFReal r n) by
      simp [c, poissonMeasure_apply_singleton_eq]]
    simp
  have hs' : Summable (fun n : ℕ ↦ poissonPMFReal r n * (n : ℝ)) := by
    have hshift :
        Summable (fun n : ℕ ↦ poissonPMFReal r (n + 1) * ((n + 1 : ℕ) : ℝ)) := by
      have hbase : Summable (fun n : ℕ ↦ (r : ℝ) * poissonPMFReal r n) :=
        (poissonPMFRealSum r).summable.mul_left (r : ℝ)
      refine hbase.congr ?_
      intro n
      rw [← poissonPMFReal_succ_mul]
      simp
    exact (summable_nat_add_iff 1).mp <| by
      simpa [Nat.succ_eq_add_one] using hshift
  have hs : Summable (fun n : ℕ ↦ (c n).toReal * ‖(n : ℝ)‖) := by
    refine hs'.congr ?_
    intro n
    rw [show c n = ENNReal.ofReal (poissonPMFReal r n) by
      simp [c, poissonMeasure_apply_singleton_eq]]
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have hmeasure : Measure.sum (fun n : ℕ ↦ c n • Measure.dirac n) = poissonMeasure r := by
    simpa [c] using (Measure.sum_smul_dirac (μ := poissonMeasure r)).symm
  have hsumc :
      ∑' n : ℕ, (c n).toReal * (n : ℝ) = ∑' n : ℕ, poissonPMFReal r n * (n : ℝ) := by
    -- Proof comment: normalize each singleton coefficient back to the explicit Poisson mass.
    refine tsum_congr fun n ↦ ?_
    rw [show c n = ENNReal.ofReal (poissonPMFReal r n) by
      simp [c, poissonMeasure_apply_singleton_eq]]
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  calc
    ∫ n, (n : ℝ) ∂poissonMeasure r
        = ∫ n, (n : ℝ) ∂Measure.sum (fun n : ℕ ↦ c n • Measure.dirac n) := by
            rw [hmeasure.symm]
    _ = ∑' n : ℕ, (c n).toReal * (n : ℝ) := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_sum_dirac_eq_tsum (f := fun n : ℕ ↦ (n : ℝ)) hc hs)
    _ = ∑' n : ℕ, poissonPMFReal r n * (n : ℝ) := hsumc
    _ = (r : ℝ) := by
          -- Proof comment: shift the series by one index and use the explicit Poisson recursion.
          rw [← hs'.sum_add_tsum_nat_add 1]
          have htail :
              ∑' i : ℕ, poissonPMFReal r (i + 1) * ((i + 1 : ℕ) : ℝ) = (r : ℝ) := by
            calc
              ∑' i : ℕ, poissonPMFReal r (i + 1) * ((i + 1 : ℕ) : ℝ)
                  = ∑' i : ℕ, (r : ℝ) * poissonPMFReal r i := by
                      refine tsum_congr fun i ↦ ?_
                      simpa using poissonPMFReal_succ_mul r i
              _ = (r : ℝ) * ∑' i : ℕ, poissonPMFReal r i := by
                    rw [tsum_mul_left]
              _ = (r : ℝ) * 1 := by
                    rw [(poissonPMFRealSum r).tsum_eq]
              _ = (r : ℝ) := by ring
          simpa using htail

/-- Companion lemma: a Poisson process induces an interval-count family on
half-open intervals `(s,t]` satisfying `(P1)`--`(P5)`, with genuine interval counts because the
owner object is now a nondecreasing counting process. -/
theorem IsPoissonProcess.hasPoissonIntervalCountProperties
    {P : Measure Ω} {N : NNReal → Ω → ℕ} {α : NNReal}
    (hN : IsPoissonProcess α P N) :
    HasPoissonIntervalCountProperties α P (fun s t ω ↦ N t ω - N s ω) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    -- Proof comment: interval counts are measurable because they are differences of stochastic
    -- process coordinates.
    simpa using (hN.stochastic t).sub (hN.stochastic s)
  · intro r s t hrs hst
    -- Proof comment: monotonicity makes truncated subtraction equal the genuine increment split.
    ext ω
    have hrsω : N r ω ≤ N s ω := hN.mono hrs ω
    have hstω : N s ω ≤ N t ω := hN.mono hst ω
    change N t ω - N r ω = (N s ω - N r ω) + (N t ω - N s ω)
    omega
  · -- Proof comment: the associated origin-started counting process is exactly `N`
    -- because `N 0 = 0`.
    simpa [hN.zero] using hN.indepIncrements
  · intro s t hst
    -- Proof comment: both interval counts and origin-started counts have the same Poisson law.
    have hLeft :
        HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (α * (t - s))) P :=
      hN.poisson_increment hst
    have hRight :
        HasLaw (fun ω ↦ N (t - s) ω - N 0 ω) (poissonMeasure (α * (t - s))) P := by
      simpa [hN.zero] using hN.poisson_law (t - s)
    exact hLeft.identDistrib hRight
  · -- Route correction: the current file already uses the punctured right-neighborhood filter,
    -- so `(P5)` closes by transporting the explicit Poisson masses along `hN.poisson_law`.
    letI := hN.isProbabilityMeasure
    rcases poissonMeasure_smallTime α with ⟨hOne, hTail⟩
    refine ⟨?_, ?_⟩
    · have hEventually :
          Filter.EventuallyEq
            (nhdsWithin (0 : NNReal) (Set.Ioi 0))
            (fun h : NNReal ↦ (P {ω | N h ω - N 0 ω = 1}).toReal / (h : ℝ))
            (fun h : NNReal ↦ ((poissonMeasure (α * h)) ({1} : Set ℕ)).toReal / (h : ℝ)) := by
        -- Proof comment: rewrite the event mass by the law of `N h`.
        filter_upwards [self_mem_nhdsWithin] with h hh
        have hLaw : HasLaw (N h) (poissonMeasure (α * h)) P := hN.poisson_law h
        have hMass :
            P {ω | N h ω = 1} = (poissonMeasure (α * h)) ({1} : Set ℕ) := by
          rw [← hLaw.map_eq]
          simpa using (Measure.map_apply (hN.stochastic h) (measurableSet_singleton 1)).symm
        simp [hN.zero, hMass]
      exact hOne.congr' hEventually.symm
    · have hEventually :
          Filter.EventuallyEq
            (nhdsWithin (0 : NNReal) (Set.Ioi 0))
            (fun h : NNReal ↦ (P {ω | 2 ≤ N h ω - N 0 ω}).toReal / (h : ℝ))
            (fun h : NNReal ↦
              ((poissonMeasure (α * h)) {n : ℕ | 2 ≤ n}).toReal / (h : ℝ)) := by
        -- Proof comment: the same law transport identifies the tail event with the canonical
        -- Poisson tail above `1`.
        filter_upwards [self_mem_nhdsWithin] with h hh
        have hLaw : HasLaw (N h) (poissonMeasure (α * h)) P := hN.poisson_law h
        have hMass :
            P {ω | 2 ≤ N h ω} = (poissonMeasure (α * h)) {n : ℕ | 2 ≤ n} := by
          rw [← hLaw.map_eq]
          simpa using
            (Measure.map_apply (hN.stochastic h)
              (by simp)).symm
        simp [hN.zero, hMass]
      exact hTail.congr' hEventually.symm

/-- Helper for Theorem 5.34: refining time `t` into equal mesh intervals expresses the pgf at
time `t` as the corresponding power of the mesh-step pgf. -/
private theorem zeroStartedCountLawPgf_eq_meshPower
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI)
    (t : NNReal) (z : Set.Icc (0 : ℝ) 1) (m : ℕ) :
    probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t) z =
      probabilityGeneratingFunctionReal
          (zeroStartedCountPMF hNI (t / (m + 1))) z ^ (m + 1) := by
  have hmeshEq : ((m + 1 : ℕ) • (t / (m + 1 : NNReal))) = t := by
    rw [nsmul_eq_mul]
    have hm0 : (m + 1 : NNReal) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    field_simp [hm0]
    simp [Nat.cast_add, left_distrib, mul_comm]
  calc
    probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t) z
        = probabilityGeneratingFunctionReal
            (zeroStartedCountPMF hNI (((m + 1 : ℕ) • (t / (m + 1 : NNReal))))) z := by
              simp [hmeshEq]
    _ = probabilityGeneratingFunctionReal
          (zeroStartedCountPMF hNI (t / (m + 1))) z ^ (m + 1) := by
            simpa [zeroStartedCountPMF] using
              zeroStartedCountLawPgf_nsmul hNI z (t / (m + 1)) (m + 1)

/-- Helper for Theorem 5.34: for fixed `z ∈ [0,1]` and `t > 0`, the pgf of the time-`t`
origin-started count law equals the Poisson exponential `exp ((α t) (z - 1))`. -/
private theorem zeroStartedCountLawPgf_eq_exp_of_pos
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI)
    {t : NNReal} (htpos : 0 < t) (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t) z =
      Real.exp ((((α * t : NNReal) : ℝ) * ((z : ℝ) - 1))) := by
  let g : ℕ → ℝ
    | 0 => 0
    | m + 1 =>
        probabilityGeneratingFunctionReal
          (zeroStartedCountPMF hNI (t / (m + 1))) z - 1
  have hmesh :
      Tendsto (fun m : ℕ ↦ t / (m + 1)) atTop (nhdsWithin (0 : NNReal) (Set.Ioi 0)) :=
    zeroStartedCountMesh_tendsto_zeroWithin t htpos
  have hComp :
      Tendsto
        (fun m : ℕ ↦
          (probabilityGeneratingFunctionReal
                (zeroStartedCountPMF hNI (t / (m + 1))) z - 1) /
            (((t / (m + 1) : NNReal) : ℝ)))
        atTop (𝓝 ((α : ℝ) * ((z : ℝ) - 1))) :=
    (zeroStartedCountLawPgf_smallTime hNI z).comp hmesh
  have hScaledShift :
      Tendsto
        (fun m : ℕ ↦ ((m + 1 : ℝ) * g (m + 1)))
        atTop (𝓝 ((((α * t : NNReal) : ℝ) * ((z : ℝ) - 1)))) := by
    have hMul :
        Tendsto
          (fun m : ℕ ↦
            (t : ℝ) *
              ((probabilityGeneratingFunctionReal
                    (zeroStartedCountPMF hNI (t / (m + 1))) z - 1) /
                (((t / (m + 1) : NNReal) : ℝ))))
          atTop (𝓝 ((t : ℝ) * ((α : ℝ) * ((z : ℝ) - 1)))) :=
      tendsto_const_nhds.mul hComp
    have hEq :
        (fun m : ℕ ↦ ((m + 1 : ℝ) * g (m + 1))) =
          (fun m : ℕ ↦
            (t : ℝ) *
              ((probabilityGeneratingFunctionReal
                    (zeroStartedCountPMF hNI (t / (m + 1))) z - 1) /
                (((t / (m + 1) : NNReal) : ℝ)))) := by
      funext m
      dsimp [g]
      have ht0 : (t : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_gt htpos
      have hmesh0 : (((t / (m + 1) : NNReal) : ℝ)) ≠ 0 := by
        exact_mod_cast (div_pos htpos (show (0 : NNReal) < m + 1 by
          exact_mod_cast Nat.succ_pos m)).ne'
      have hratio : (t : ℝ) / (((t / (m + 1) : NNReal) : ℝ)) = (m + 1 : ℝ) := by
        rw [NNReal.coe_div]
        field_simp [ht0]
        norm_num
      calc
        ((m + 1 : ℝ) *
            (probabilityGeneratingFunctionReal
                (zeroStartedCountPMF hNI (t / (m + 1))) z - 1))
            = ((t : ℝ) / (((t / (m + 1) : NNReal) : ℝ))) *
                (probabilityGeneratingFunctionReal
                    (zeroStartedCountPMF hNI (t / (m + 1))) z - 1) := by
                  rw [hratio]
        _ = (t : ℝ) *
              ((probabilityGeneratingFunctionReal
                    (zeroStartedCountPMF hNI (t / (m + 1))) z - 1) /
                (((t / (m + 1) : NNReal) : ℝ))) := by
              field_simp [hmesh0]
    simpa [NNReal.coe_mul, mul_assoc, mul_left_comm, mul_comm] using
      hMul.congr' (Filter.EventuallyEq.of_eq hEq.symm)
  have hScaled :
      Tendsto
        (fun m : ℕ ↦ (m : ℝ) * g m)
        atTop (𝓝 ((((α * t : NNReal) : ℝ) * ((z : ℝ) - 1)))) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa using hScaledShift
  have hExp :
      Tendsto
        (fun m : ℕ ↦ (1 + g m) ^ m)
        atTop (𝓝 (Real.exp ((((α * t : NNReal) : ℝ) * ((z : ℝ) - 1))))) :=
    Real.tendsto_one_add_pow_exp_of_tendsto hScaled
  have hExpShift :
      Tendsto
        (fun m : ℕ ↦
          (probabilityGeneratingFunctionReal
              (zeroStartedCountPMF hNI (t / (m + 1))) z) ^ (m + 1))
        atTop (𝓝 (Real.exp ((((α * t : NNReal) : ℝ) * ((z : ℝ) - 1))))) := by
    have hEq :
        (fun m : ℕ ↦ (1 + g (m + 1)) ^ (m + 1)) =
          (fun m : ℕ ↦
            (probabilityGeneratingFunctionReal
                (zeroStartedCountPMF hNI (t / (m + 1))) z) ^ (m + 1)) := by
      funext m
      simp [g]
    exact (hExp.comp (Filter.tendsto_add_atTop_nat 1)).congr'
      (Filter.EventuallyEq.of_eq hEq)
  have hConstEq :
      Tendsto
        (fun _ : ℕ ↦ probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t) z)
        atTop (𝓝 (Real.exp ((((α * t : NNReal) : ℝ) * ((z : ℝ) - 1))))) := by
    have hEq :
        (fun _ : ℕ ↦ probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t) z) =
          (fun m : ℕ ↦
            (probabilityGeneratingFunctionReal
                (zeroStartedCountPMF hNI (t / (m + 1))) z) ^ (m + 1)) := by
      funext m
      exact zeroStartedCountLawPgf_eq_meshPower hNI t z m
    exact hExpShift.congr' (Filter.EventuallyEq.of_eq hEq.symm)
  exact tendsto_nhds_unique tendsto_const_nhds hConstEq

/-- Helper for Theorem 5.34: every origin-started count `NI 0 t` has the Poisson law with
parameter `α t`. -/
private theorem zeroStartedCount_hasLawPoisson
    {α : NNReal} {P : Measure Ω} {NI : NNReal → NNReal → Ω → ℕ}
    (hNI : HasPoissonIntervalCountProperties α P NI) (t : NNReal) :
    HasLaw (NI 0 t) (poissonMeasure (α * t)) P := by
  letI := hNI.isProbabilityMeasure
  by_cases ht : t = 0
  · -- Proof comment: the time-zero count is identically `0`, so its law is `Poi(0)`.
    simpa [ht, hNI.zero 0] using (hasLawZeroPoissonMeasureZero (μ := P) (Ω := Ω))
  · have htpos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht)
    have hpgf :
        probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t) =
          probabilityGeneratingFunctionReal ((poissonMeasure (α * t)).toPMF) := by
      refine probabilityGeneratingFunctionReal_eq_of_agree_on_samplingPoints
        (p := zeroStartedCountPMF hNI t)
        (q := ((poissonMeasure (α * t)).toPMF))
        (r := (1 / 2 : ℝ))
        (by norm_num) (by norm_num) ?_
      intro n
      let z : Set.Icc (0 : ℝ) 1 :=
        ⟨(1 / 2 : ℝ) * (((n : ℝ) + 1) / ((n : ℝ) + 2)), by
          constructor
          · positivity
          · have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
            have hnum : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
            have hfrac : (((n : ℝ) + 1) / ((n : ℝ) + 2)) ≤ 1 := by
              field_simp [hden.ne']
              linarith
            nlinarith⟩
      calc
        probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t)
            ((1 / 2 : ℝ) * (((n : ℝ) + 1) / ((n : ℝ) + 2)))
            = probabilityGeneratingFunctionReal (zeroStartedCountPMF hNI t) z := by rfl
        _ = Real.exp ((((α * t : NNReal) : ℝ) * ((z : ℝ) - 1))) := by
              exact zeroStartedCountLawPgf_eq_exp_of_pos hNI htpos z
        _ = probabilityGeneratingFunctionReal ((poissonMeasure (α * t)).toPMF) z := by
              symm
              exact poissonMeasure_probabilityGeneratingFunctionReal_eq (α * t) z
        _ = probabilityGeneratingFunctionReal ((poissonMeasure (α * t)).toPMF)
              ((1 / 2 : ℝ) * (((n : ℝ) + 1) / ((n : ℝ) + 2))) := by
                rfl
    have hPMF :
        zeroStartedCountPMF hNI t = (poissonMeasure (α * t)).toPMF :=
      probabilityGeneratingFunctionReal_injective hpgf
    refine ⟨(hNI.measurable 0 t bot_le).aemeasurable, ?_⟩
    -- Proof comment: equality of pgfs identifies the time-`t` law with the Poisson law.
    simpa [zeroStartedCountPMF, zeroStartedCountLaw, Measure.toPMF_toMeasure] using
      congrArg PMF.toMeasure hPMF

/-- Theorem 5.34: if an interval-count family on half-open intervals `(s,t]` satisfies the
textbook axioms `(P1)`--`(P5)`, then the induced process `t ↦ N_(0,t]` is a Poisson process with
intensity `α`; the companion theorem `poissonIntervalCount_mean_unit_interval_count_eq` identifies
this `α` with the mean unit-interval count `E[N_(0,1]]`. Conversely,
`IsPoissonProcess.hasPoissonIntervalCountProperties` gives the reverse implication from a Poisson
process to its interval-count family. -/
theorem isPoissonProcess_of_hasPoissonIntervalCountProperties
    {P : Measure Ω} (NI : NNReal → NNReal → Ω → ℕ) {α : NNReal}
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    IsPoissonProcess α P (fun t ω ↦ NI 0 t ω) := by
  refine isPoissonProcess_of_textbook hNI.stochastic (hNI.zero 0) hNI.mono hNI.indepIncrements ?_
  intro s t hst
  have hIntervalLaw : HasLaw (NI s t) (poissonMeasure (α * (t - s))) P := by
    have hMarginal : HasLaw (NI 0 (t - s)) (poissonMeasure (α * (t - s))) P :=
      zeroStartedCount_hasLawPoisson hNI (t - s)
    refine ⟨(hNI.measurable s t hst.le).aemeasurable, ?_⟩
    exact (hNI.stationary s t hst.le).map_eq.trans hMarginal.map_eq
  -- Proof comment: stationarity transfers the Poisson law to `(s, t]`, and additivity rewrites
  -- that interval count as the increment of the origin-started counting process.
  simpa [poissonIntervalCount_increment_eq_sub hNI.additive hst.le] using hIntervalLaw

-- Proof sketch: once the forward implication produces the Poisson marginal law at time `1`,
-- transport the expectation of `NI 0 1` to `poissonMeasure α` and evaluate the latter by the
-- explicit first-moment computation above.
/-- For an interval-count family satisfying `(P1)`--`(P5)`, the intensity parameter appearing in
`(P5)` agrees with the mean unit-interval count `E[N_(0,1]]`. -/
theorem poissonIntervalCount_mean_unit_interval_count_eq
    {α : NNReal} {P : Measure Ω}
    (NI : NNReal → NNReal → Ω → ℕ)
    (hNI : HasPoissonIntervalCountProperties α P NI) :
    P[fun ω ↦ (NI 0 1 ω : ℝ)] = (α : ℝ) := by
  letI := hNI.isProbabilityMeasure
  have hProcess :
      IsPoissonProcess α P (fun t ω ↦ NI 0 t ω) :=
    isPoissonProcess_of_hasPoissonIntervalCountProperties (NI := NI) hNI
  have hLaw : HasLaw (NI 0 1) (poissonMeasure (α * 1)) P := by
    simpa using hProcess.poisson_law 1
  -- Proof comment: rewrite the unit-time expectation as the expectation under the Poisson law.
  calc
    P[fun ω ↦ (NI 0 1 ω : ℝ)] = ∫ n, (n : ℝ) ∂poissonMeasure (α * 1) := by
      simpa [Function.comp_apply] using
        hLaw.integral_comp
          (f := fun n : ℕ ↦ (n : ℝ))
          (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).aestronglyMeasurable
    _ = ((α * 1 : NNReal) : ℝ) := integral_natCast_poissonMeasure_eq (α * 1)
    _ = (α : ℝ) := by simp

/-- Convenience bridge: a Poisson process is equivalent to its origin-started interval-increment
family satisfying `(P1)`--`(P5)`, together with the explicit start-at-zero field needed to recover
the process from those interval counts. -/
theorem isPoissonProcess_iff_hasPoissonIntervalCountProperties
    {P : Measure Ω} {N : NNReal → Ω → ℕ} {α : NNReal} :
    IsPoissonProcess α P N ↔
      N 0 = 0 ∧
        HasPoissonIntervalCountProperties α P (fun s t ω ↦ N t ω - N s ω) := by
  refine ⟨?_, ?_⟩
  · intro hN
    -- Proof comment: the reverse direction is the companion interval-count construction above.
    exact ⟨hN.zero, hN.hasPoissonIntervalCountProperties⟩
  · intro hN
    rcases hN with ⟨hzero, hcount⟩
    -- Proof comment: apply the forward companion theorem to the interval-increment family and
    -- then collapse the origin-started reconstruction using `N 0 = 0`.
    have hProcess :
        IsPoissonProcess α P (fun t ω ↦ N t ω - N 0 ω) :=
      isPoissonProcess_of_hasPoissonIntervalCountProperties
        (NI := fun s t ω ↦ N t ω - N s ω) hcount
    simpa [hzero] using hProcess
