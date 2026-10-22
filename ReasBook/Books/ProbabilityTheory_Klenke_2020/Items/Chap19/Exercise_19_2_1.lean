/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib.MeasureTheory.Function.L2Space

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- Helper for Exercise 19.2.1: every entry of a stochastic matrix is finite because it is bounded
by the corresponding row sum `1`. -/
private theorem stochasticEntry_neTop
    {p : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p) (x y : E) :
    p x y ≠ ∞ := by
  have hle : p x y ≤ 1 := by
    calc
      p x y ≤ ∑' z : E, p x z := ENNReal.le_tsum y
      _ = 1 := hp x
  exact (lt_of_le_of_lt hle (by simp)).ne

/-- Helper for Exercise 19.2.1: evaluating `discreteMatrixKernel p` on a singleton recovers the
corresponding matrix entry. -/
private theorem discreteMatrixKernel_apply_singleton_eq_entry
    {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (p : E → E → ℝ≥0∞) (x y : E) :
    discreteMatrixKernel p y ({x} : Set E) = p y x := by
  -- Proof comment: expand the row measure into weighted Dirac masses and keep only the `{x}`
  -- summand in the resulting countable series.
  rw [discreteMatrixKernel_apply]
  simp +contextual [tsum_eq_single x]

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

attribute [local instance] Classical.propDecidable

namespace Kernel

/-- A continuous linear endomorphism of `L²(π)` realizes kernel averaging along `κ` if every
square-integrable representative `φ` is sent to the `L²(π)` class of `x ↦ ∫ y, φ y ∂κ x`.
Because the condition is required for every representative of an `L²` class, it encodes the
descent of kernel averaging to a genuine operator on `L²(π)` rather than depending on a chosen
coercion `L²(π) → E → ℝ`. -/
def IsL2TransitionOperator (κ : Kernel E E) (π : Measure E)
    (T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)) : Prop :=
  ∀ ⦃φ : E → ℝ⦄ (hφ : MemLp φ 2 π), T (hφ.toLp φ) =ᵐ[π] fun x ↦ ∫ y, φ y ∂κ x

/-- Helper for Exercise 19.2.1: the `L²(π)` Markov operator induced by `κ` is self-adjoint if it
admits a self-adjoint continuous linear realization of kernel averaging. This keeps the main
statement source-facing instead of parameterizing it by a chosen endomorphism of `L²(π)`. -/
def HasSelfAdjointL2TransitionOperator (κ : Kernel E E) (π : Measure E) : Prop :=
  ∃ T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ), IsL2TransitionOperator κ π T ∧ IsSelfAdjoint T

/-- Any two `L²(π)` realizations of kernel averaging along the same kernel agree. -/
theorem isL2TransitionOperator_ext
    {κ : Kernel E E} {π : Measure E}
    {T₁ T₂ : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT₁ : IsL2TransitionOperator κ π T₁)
    (hT₂ : IsL2TransitionOperator κ π T₂) :
    T₁ = T₂ :=
  by
    -- Proof comment: it suffices to compare the two operators on an arbitrary `L²(π)` class and
    -- use the defining kernel-average representative for that class.
    ext f
    have hself : (Lp.memLp f).toLp (f : E → ℝ) = f := by
      rw [Lp.ext_iff]
      exact MemLp.coeFn_toLp (Lp.memLp f)
    have h₁ :
        T₁ f =ᵐ[π] fun x ↦ ∫ y, f y ∂κ x := by
      simpa [hself] using hT₁ (Lp.memLp f)
    have h₂ :
        T₂ f =ᵐ[π] fun x ↦ ∫ y, f y ∂κ x := by
      simpa [hself] using hT₂ (Lp.memLp f)
    exact h₁.trans h₂.symm

/-- A chosen `L²(π)` realization is self-adjoint exactly when the induced `L²(π)` Markov operator
is self-adjoint. -/
theorem hasSelfAdjointL2TransitionOperator_iff
    {κ : Kernel E E} {π : Measure E}
    {T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT : IsL2TransitionOperator κ π T) :
    HasSelfAdjointL2TransitionOperator κ π ↔ IsSelfAdjoint T :=
  by
    constructor
    · rintro ⟨T', hT', hself'⟩
      -- Proof comment: uniqueness of the `L²(π)` realization identifies every witness with `T`.
      have hEq : T' = T := isL2TransitionOperator_ext hT' hT
      simpa [hEq] using hself'
    · intro hself
      exact ⟨T, hT, hself⟩

end Kernel

/-- Helper for Exercise 19.2.1: on a countable discrete state space, the `π`-flow sent from `A`
to `B` by `discreteMatrixKernel p` expands to the corresponding double countable sum of the
singleton-weighted matrix entries. -/
private theorem discreteMatrixKernel_flow [Countable E]
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, discreteMatrixKernel p x B ∂π =
      (∑' x : E,
        if x ∈ A then ∑' y : E, if y ∈ B then p x y * π ({x} : Set E) else 0 else 0) := by
  classical
  -- Proof comment: rewrite the restricted integral as an indicator integral and expand it over
  -- the countable discrete state space.
  rw [← lintegral_indicator hA, MeasureTheory.lintegral_countable']
  refine tsum_congr fun x ↦ ?_
  by_cases hx : x ∈ A
  · rw [if_pos hx, Set.indicator_of_mem hx]
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ hB]
    have hmul :
        ∑' y : E, (if y ∈ B then p x y else 0) * π ({x} : Set E) =
          (∑' y : E, if y ∈ B then p x y else 0) * π ({x} : Set E) :=
      ENNReal.tsum_mul_right
    have hdirac :
        (fun y : E ↦ (p x y • Measure.dirac y) B) = fun y : E ↦ if y ∈ B then p x y else 0 := by
      funext y
      by_cases hy : y ∈ B <;> simp [Measure.smul_apply, hy]
    rw [hdirac]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.symm
  · rw [if_neg hx, Set.indicator_of_notMem hx, zero_mul]

/-- Helper for Exercise 19.2.1: singleton detailed balance upgrades to setwise reversibility for
`discreteMatrixKernel p`. -/
private theorem isReversible_discreteMatrixKernel_of_singletonBalance [Countable E]
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hbal : ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E)) :
    Kernel.IsReversible (discreteMatrixKernel p) π := by
  classical
  intro A B hA hB
  let flowTerm : E → E → ℝ≥0∞ := fun x y ↦
    if x ∈ A ∧ y ∈ B then p x y * π ({x} : Set E) else 0
  have hflow_left :
      (∑' x : E, if x ∈ A then ∑' y : E, if y ∈ B then p x y * π ({x} : Set E) else 0 else 0) =
        ∑' x : E, ∑' y : E, flowTerm x y := by
    -- Proof comment: fold the two membership tests into a single indicator on `A × B`.
    refine tsum_congr fun x ↦ ?_
    by_cases hx : x ∈ A <;> simp [flowTerm, hx]
  have hflow_right :
      (∑' y : E, if y ∈ B then ∑' x : E, if x ∈ A then p y x * π ({y} : Set E) else 0 else 0) =
        ∑' y : E, ∑' x : E, flowTerm x y := by
    -- Proof comment: detailed balance identifies the reversed edge weight with the forward one.
    refine tsum_congr fun y ↦ ?_
    by_cases hy : y ∈ B
    · rw [if_pos hy]
      refine tsum_congr fun x ↦ ?_
      by_cases hx : x ∈ A <;> simp [flowTerm, hx, hy, hbal y x]
    · simp [flowTerm, hy]
  calc
    ∫⁻ x in A, discreteMatrixKernel p x B ∂π
      = ∑' x : E, if x ∈ A then ∑' y : E, if y ∈ B then p x y * π ({x} : Set E) else 0 else 0 :=
          discreteMatrixKernel_flow A B hA hB
    _ = ∑' x : E, ∑' y : E, flowTerm x y := hflow_left
    _ = ∑' y : E, ∑' x : E, flowTerm x y := ENNReal.tsum_comm
    _ = ∑' y : E, if y ∈ B then ∑' x : E, if x ∈ A then p y x * π ({y} : Set E) else 0 else 0 :=
          hflow_right.symm
    _ = ∫⁻ x in B, discreteMatrixKernel p x A ∂π :=
          (discreteMatrixKernel_flow B A hB hA).symm

/-- Helper for Exercise 19.2.1: pairing singleton indicators through an `L²(π)` transition
operator for `discreteMatrixKernel p` reads off the weighted singleton transition mass. -/
private theorem innerSingletonTransition_eq_weightedKernelMass
    {p : E → E → ℝ≥0∞} {π : Measure E}
    [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    {T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT : Kernel.IsL2TransitionOperator (discreteMatrixKernel p) π T)
    (x y : E) :
    inner ℝ
        (MeasureTheory.indicatorConstLp 2 (measurableSet_singleton x) ((hπ_finite x).ne) (1 : ℝ))
        (T (MeasureTheory.indicatorConstLp 2 (measurableSet_singleton y) ((hπ_finite y).ne)
          (1 : ℝ))) =
      (p x y * π ({x} : Set E)).toReal := by
  let e : E → E →₂[π] ℝ := fun z ↦
    MeasureTheory.indicatorConstLp 2 (measurableSet_singleton z) ((hπ_finite z).ne) (1 : ℝ)
  let g : E → ℝ := fun z ↦
    ∫ t, ({y} : Set E).indicator (fun _ ↦ (1 : ℝ)) t ∂ discreteMatrixKernel p z
  have hTy : T (e y) =ᵐ[π] g := by
    -- Proof comment: apply the `L²(π)` transition-operator axiom to the singleton indicator at
    -- `y` and keep the resulting row-average formula under one name.
    simpa [e, g, MeasureTheory.indicatorConstLp] using
      hT
        (MeasureTheory.memLp_indicator_const (2 : ℝ≥0∞)
          (measurableSet_singleton y) (1 : ℝ) (Or.inr ((hπ_finite y).ne)))
  have hsingleton :
      ({x} : Set E).EqOn g (fun _ ↦ g x) := by
    -- Proof comment: restricting to the singleton `{x}` turns the row-average into a constant.
    intro z hz
    simp at hz
    simpa [g, hz]
  have hvalue : g x = (p x y).toReal := by
    -- Proof comment: integrating the singleton indicator against the row kernel at `x` is just
    -- the singleton mass `p x y`, viewed in `ℝ`.
    have hsingletonMass : discreteMatrixKernel p x ({y} : Set E) = p x y := by
      simpa using discreteMatrixKernel_apply_singleton_eq_entry p y x
    change
      (∫ t, ({y} : Set E).indicator (fun _ ↦ (1 : ℝ)) t ∂ discreteMatrixKernel p x) =
        (p x y).toReal
    have hInt :
        (∫ t, ({y} : Set E).indicator (fun _ ↦ (1 : ℝ)) t ∂ discreteMatrixKernel p x) =
          (discreteMatrixKernel p x).real ({y} : Set E) := by
      simpa using
        (MeasureTheory.integral_indicator_one (measurableSet_singleton y))
    rw [hInt]
    simpa [Measure.real_def] using congrArg ENNReal.toReal hsingletonMass
  have hpxy_ne : p x y ≠ ∞ := stochasticEntry_neTop hp x y
  -- Proof comment: first rewrite the inner product as a singleton set integral, then collapse the
  -- set integral to the value of the row-average at `x`.
  calc
    inner ℝ (e x) (T (e y)) = ∫ z in ({x} : Set E), T (e y) z ∂π := by
      simpa [e] using
        (MeasureTheory.L2.inner_indicatorConstLp_one
          (measurableSet_singleton x) ((hπ_finite x).ne) (T (e y)))
    _ = ∫ z in ({x} : Set E), g z ∂π := by
      rw [integral_congr_ae (ae_restrict_of_ae hTy)]
    _ = ∫ z in ({x} : Set E), g x ∂π := by
      rw [integral_congr_ae <|
        ae_restrict_of_forall_mem (measurableSet_singleton x) hsingleton]
    _ = π.real ({x} : Set E) * g x := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
    _ = π.real ({x} : Set E) * (p x y).toReal := by rw [hvalue]
    _ = (p x y * π ({x} : Set E)).toReal := by
      simpa [Measure.real_def, ENNReal.toReal_mul, hpxy_ne, (hπ_finite x).ne, mul_comm,
        mul_left_comm, mul_assoc]

/-- Helper for Exercise 19.2.1: reversibility of `discreteMatrixKernel p` already implies the
singleton detailed-balance identities needed for the `L²(π)` symmetry calculation. -/
private theorem singletonBalance_of_isReversible_discreteMatrixKernel
    {p : E → E → ℝ≥0∞} {π : Measure E}
    [Countable E]
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π) :
    ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) := by
  intro x y
  -- Proof comment: test reversibility on the measurable singletons `{x}` and `{y}` and collapse
  -- the resulting flow integrals with the discrete expansion lemma.
  calc
    p x y * π ({x} : Set E)
      = ∫⁻ z in ({x} : Set E), discreteMatrixKernel p z ({y} : Set E) ∂π := by
          symm
          simpa [discreteMatrixKernel_apply_singleton_eq_entry] using
            (discreteMatrixKernel_flow ({x} : Set E) ({y} : Set E)
              (measurableSet_singleton x) (measurableSet_singleton y))
    _ = ∫⁻ z in ({y} : Set E), discreteMatrixKernel p z ({x} : Set E) ∂π := by
          simpa using
            (hrev (measurableSet_singleton x) (measurableSet_singleton y) :
              ∫⁻ z in ({x} : Set E), discreteMatrixKernel p z ({y} : Set E) ∂π =
                ∫⁻ z in ({y} : Set E), discreteMatrixKernel p z ({x} : Set E) ∂π)
    _ = p y x * π ({y} : Set E) := by
          simpa [discreteMatrixKernel_apply_singleton_eq_entry] using
            (discreteMatrixKernel_flow ({y} : Set E) ({x} : Set E)
              (measurableSet_singleton y) (measurableSet_singleton x))

/-- Helper for Exercise 19.2.1: a self-adjoint `L²(π)` realization of the discrete averaging
operator forces the singleton detailed-balance identities
`p x y * π {x} = p y x * π {y}`. -/
theorem singletonDetailedBalance_of_selfAdjointL2TransitionOperator
    {p : E → E → ℝ≥0∞} {π : Measure E}
    [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    {T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT : Kernel.IsL2TransitionOperator (discreteMatrixKernel p) π T)
    (hself : IsSelfAdjoint T) :
    ∀ x y : E, p x y * π {x} = p y x * π {y} := by
  let e : E → E →₂[π] ℝ := fun z ↦
    MeasureTheory.indicatorConstLp 2 (measurableSet_singleton z) ((hπ_finite z).ne) (1 : ℝ)
  intro x y
  have hinner :
      inner ℝ (e x) (T (e y)) = inner ℝ (e y) (T (e x)) := by
    -- Proof comment: self-adjointness lets us move `T` across the `L²(π)` inner product, and in
    -- the real case the remaining inner product is symmetric.
    calc
      inner ℝ (e x) (T (e y)) = inner ℝ (T (e x)) (e y) := by
        simpa [hself.adjoint_eq] using T.adjoint_inner_right (e x) (e y)
      _ = inner ℝ (e y) (T (e x)) := real_inner_comm _ _
  have hmass :
      (p x y * π ({x} : Set E)).toReal = (p y x * π ({y} : Set E)).toReal := by
    -- Proof comment: the singleton bridge lemma rewrites both inner products to the desired
    -- weighted singleton masses.
    calc
      (p x y * π ({x} : Set E)).toReal = inner ℝ (e x) (T (e y)) := by
        symm
        simpa [e] using
          innerSingletonTransition_eq_weightedKernelMass hp hπ_finite hT x y
      _ = inner ℝ (e y) (T (e x)) := hinner
      _ = (p y x * π ({y} : Set E)).toReal := by
        simpa [e] using
          innerSingletonTransition_eq_weightedKernelMass hp hπ_finite hT y x
  have hxy_ne : p x y * π ({x} : Set E) ≠ ∞ := by
    exact ENNReal.mul_ne_top (stochasticEntry_neTop hp x y) (hπ_finite x).ne
  have hyx_ne : p y x * π ({y} : Set E) ≠ ∞ := by
    exact ENNReal.mul_ne_top (stochasticEntry_neTop hp y x) (hπ_finite y).ne
  exact (ENNReal.toReal_eq_toReal_iff' hxy_ne hyx_ne).mp hmass

/-- Helper for Exercise 19.2.1: a stochastic row defines a `PMF` whose measure is exactly the
corresponding row of `discreteMatrixKernel p`. -/
private theorem rowPmfToMeasure_eq_discreteMatrixKernel
    {p : E → E → ℝ≥0∞} [Countable E]
    (hp : IsStochasticMatrix p) (x : E) :
    let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
    discreteMatrixKernel p x = q.toMeasure := by
  let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
  ext s hs
  -- Proof comment: rewrite both measures on `s` into the same singleton-indicator normal form.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ hs]
  change ∑' y : E, (p x y • Measure.dirac y) s = q.toMeasure s
  calc
    ∑' y : E, (p x y • Measure.dirac y) s
      = ∑' y : E, s.indicator (fun z : E ↦ p x z) y := by
          refine tsum_congr fun y ↦ ?_
          by_cases hy : y ∈ s
          · simp [Measure.smul_apply, hy]
          · simp [Measure.smul_apply, hy]
    _ = q.toMeasure s := by
        simpa [q] using (q.toMeasure_apply hs).symm

/-- Helper for Exercise 19.2.1: absolute summability of the row action gives integrability against
`discreteMatrixKernel p x`. -/
private theorem integrable_discreteMatrixKernel_of_summableNorm
    {p : E → E → ℝ≥0∞} [Countable E]
    (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    Integrable f (discreteMatrixKernel p x) := by
  refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
  -- Proof comment: compute the norm integral on the Dirac decomposition of the row measure.
  rw [hasFiniteIntegral_iff_norm, discreteMatrixKernel_apply, lintegral_sum_measure]
  have hterm :
      (fun y : E ↦ ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂p x y • Measure.dirac y) =
        fun y : E ↦ ENNReal.ofReal ((p x y).toReal * ‖f y‖) := by
    funext y
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have hentry :
        p x y = ENNReal.ofReal (p x y).toReal :=
      (ENNReal.ofReal_toReal (stochasticEntry_neTop hp x y)).symm
    calc
      p x y * ENNReal.ofReal ‖f y‖
          = ENNReal.ofReal (p x y).toReal * ENNReal.ofReal ‖f y‖ := by
              simpa using congrArg (fun t : ℝ≥0∞ ↦ t * ENNReal.ofReal ‖f y‖) hentry
      _ = ENNReal.ofReal ((p x y).toReal * ‖f y‖) := by
            simpa using
              (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
  rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ by positivity) hpf]
  simp

/-- Helper for Exercise 19.2.1: a discrete-kernel row integral equals the corresponding weighted
series whenever the row action is absolutely summable. -/
private theorem integral_discreteMatrixKernel_eq_tsum_of_summableNorm
    {p : E → E → ℝ≥0∞} [Countable E]
    (hp : IsStochasticMatrix p) (f : E → ℝ) (x : E)
    (hpf : Summable (fun y : E ↦ (p x y).toReal * ‖f y‖)) :
    ∫ y, f y ∂discreteMatrixKernel p x = ∑' y : E, (p x y).toReal * f y := by
  let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
  have hrow : discreteMatrixKernel p x = q.toMeasure := by
    simpa [q] using rowPmfToMeasure_eq_discreteMatrixKernel hp x
  have hint : Integrable f q.toMeasure := by
    simpa [hrow] using integrable_discreteMatrixKernel_of_summableNorm hp f x hpf
  -- Proof comment: switch to the `PMF` row and invoke the standard `PMF` integral formula.
  calc
    ∫ y, f y ∂discreteMatrixKernel p x = ∫ y, f y ∂q.toMeasure := by rw [hrow]
    _ = ∑' y : E, (q y).toReal • f y := PMF.integral_eq_tsum q f hint
    _ = ∑' y : E, (p x y).toReal * f y := by
          simp_rw [smul_eq_mul]
          rfl

/-- Helper for Exercise 19.2.1: an `L²(π)` function on a countable discrete space has summable
singleton-mass weighted squares. -/
private theorem summable_singletonMass_mul_sq_of_memLp
    {π : Measure E} [Countable E]
    (hπ_finite : ∀ x : E, π {x} < ∞)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    Summable (fun y : E ↦ π.real {y} * (φ y) ^ 2) := by
  have hsq : Integrable (fun y : E ↦ (φ y) ^ 2) π := hφ.integrable_sq
  have hsq' :
      Integrable (fun y : E ↦ (φ y) ^ 2)
        (Measure.sum fun y : E ↦ π {y} • Measure.dirac y) := by
    simpa [Measure.sum_smul_dirac] using hsq
  have hsum :
      Summable (fun y : E ↦ (π {y}).toReal * ‖(φ y) ^ 2‖) :=
    (show
      Integrable (fun y : E ↦ (φ y) ^ 2)
          (Measure.sum fun y : E ↦ π {y} • Measure.dirac y) ↔
        Summable (fun y : E ↦ (π {y}).toReal * ‖(φ y) ^ 2‖) from
      MeasureTheory.integrable_sum_dirac_iff (fun y ↦ (hπ_finite y).ne)).1 hsq'
  simpa [Measure.real_def, Real.norm_eq_abs, abs_sq] using hsum

/-- Helper for Exercise 19.2.1: on a positive-mass singleton, reversibility turns a global
`L²(π)` bound into square-summability of the corresponding row action. -/
private theorem rowSquareSummable_of_memLp_of_singleton_pos
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hbal : ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E))
    {x : E} (hπx : π ({x} : Set E) ≠ 0)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    Summable (fun y : E ↦ (p x y).toReal * (φ y) ^ 2) := by
  have hglobal := summable_singletonMass_mul_sq_of_memLp hπ_finite hφ
  have hπx_real_ne :
      π.real ({x} : Set E) ≠ 0 := by
    exact (MeasureTheory.measureReal_ne_zero_iff ((hπ_finite x).ne)).2 hπx
  have hπx_real_pos : 0 < π.real ({x} : Set E) :=
    lt_of_le_of_ne MeasureTheory.measureReal_nonneg (by simpa using hπx_real_ne.symm)
  have hcompare :
      ∀ y : E,
        (p x y).toReal * (φ y) ^ 2
          ≤ (π.real ({x} : Set E))⁻¹ * (π.real ({y} : Set E) * (φ y) ^ 2) := by
    intro y
    have hxy_ne : p x y ≠ ∞ := stochasticEntry_neTop hp x y
    have hyx_ne : p y x ≠ ∞ := stochasticEntry_neTop hp y x
    have hbal_real :
        (p x y).toReal * π.real ({x} : Set E) =
          (p y x).toReal * π.real ({y} : Set E) := by
      simpa [Measure.real_def, ENNReal.toReal_mul, hxy_ne, hyx_ne, (hπ_finite x).ne,
        (hπ_finite y).ne, mul_comm, mul_left_comm, mul_assoc] using congrArg ENNReal.toReal
          (hbal x y)
    have hyx_le_one_ennreal : p y x ≤ 1 := by
      calc
        p y x ≤ ∑' z : E, p y z := ENNReal.le_tsum x
        _ = 1 := hp y
    have hyx_le_one : (p y x).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hyx_le_one_ennreal
    have hmass_bound :
        (p x y).toReal * π.real ({x} : Set E) ≤ π.real ({y} : Set E) := by
      calc
        (p x y).toReal * π.real ({x} : Set E)
          = (p y x).toReal * π.real ({y} : Set E) := hbal_real
        _ ≤ 1 * π.real ({y} : Set E) := by
            gcongr
        _ = π.real ({y} : Set E) := by simp
    have hweight_bound :
        (p x y).toReal ≤ π.real ({y} : Set E) / π.real ({x} : Set E) := by
      exact (le_div_iff₀ hπx_real_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmass_bound)
    have hsq_nonneg : 0 ≤ (φ y) ^ 2 := sq_nonneg _
    calc
      (p x y).toReal * (φ y) ^ 2
        ≤ (π.real ({y} : Set E) / π.real ({x} : Set E)) * (φ y) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hweight_bound hsq_nonneg
      _ = (π.real ({x} : Set E))⁻¹ * (π.real ({y} : Set E) * (φ y) ^ 2) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hscaled :
      Summable (fun y : E ↦
        (π.real ({x} : Set E))⁻¹ * (π.real ({y} : Set E) * (φ y) ^ 2)) :=
    hglobal.mul_left _
  exact Summable.of_nonneg_of_le (fun y ↦ by positivity) hcompare hscaled

/-- Helper for Exercise 19.2.1: on a positive-mass singleton, the reversible row action is both
absolutely summable and summable on any `L²(π)` representative. -/
private theorem rowSummable_of_memLp_of_singleton_pos
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hbal : ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E))
    {x : E} (hπx : π ({x} : Set E) ≠ 0)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    Summable (fun y : E ↦ (p x y).toReal * ‖φ y‖) ∧
      Summable (fun y : E ↦ (p x y).toReal * φ y) := by
  have hsq :
      Summable (fun y : E ↦ (p x y).toReal * (φ y) ^ 2) :=
    rowSquareSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx hφ
  have hrow_ne_top : ∑' y : E, p x y ≠ ∞ := by
    simpa [hp x]
  have hrow :
      Summable (fun y : E ↦ (p x y).toReal) :=
    ENNReal.summable_toReal hrow_ne_top
  have hmajorant :
      Summable (fun y : E ↦
        (1 / 2 : ℝ) * ((p x y).toReal * (φ y) ^ 2 + (p x y).toReal)) := by
    exact (hsq.add hrow).mul_left (1 / 2 : ℝ)
  have hterm_le :
      ∀ y : E,
        (p x y).toReal * ‖φ y‖
          ≤ (1 / 2 : ℝ) * ((p x y).toReal * (φ y) ^ 2 + (p x y).toReal) := by
    intro y
    have hbase : 2 * ‖φ y‖ ≤ ‖φ y‖ ^ 2 + 1 := by
      simpa using two_mul_le_add_sq ‖φ y‖ (1 : ℝ)
    have hscaled :
        ((p x y).toReal / 2) * (2 * ‖φ y‖)
          ≤ ((p x y).toReal / 2) * (‖φ y‖ ^ 2 + 1) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    simpa [pow_two, sq_abs, mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib,
      div_eq_mul_inv] using hscaled
  have habs :
      Summable (fun y : E ↦ (p x y).toReal * ‖φ y‖) :=
    Summable.of_nonneg_of_le (fun y ↦ by positivity) hterm_le hmajorant
  have hsigned_norm :
      Summable (fun y : E ↦ ‖(p x y).toReal * φ y‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, abs_mul, mul_comm, mul_left_comm,
      mul_assoc] using habs
  exact ⟨habs, hsigned_norm.of_norm⟩

/-- Helper for Exercise 19.2.1: on a countable discrete space, `π`-almost every point has
positive singleton mass. This is the discrete bridge that lets later proofs reduce `π`-a.e.
claims to pointwise identities on positive-mass states. -/
private theorem ae_nonzero_singletonMass
    {π : Measure E} [Countable E] :
    ∀ᵐ x ∂π, π ({x} : Set E) ≠ 0 := by
  let s : Set E := {x : E | π ({x} : Set E) = 0}
  have hzero :
      π s = 0 := by
    -- Proof comment: expand the measure of `s` as the countable sum of singleton masses; every
    -- term vanishes because membership in `s` is exactly the zero-mass condition.
    calc
      π s = ∫⁻ x, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂π := by
            simpa using
              (MeasureTheory.lintegral_indicator_one MeasurableSet.of_discrete).symm
      _ = ∑' x : E, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * π ({x} : Set E) := by
            simpa [mul_comm] using
              (MeasureTheory.lintegral_countable' (s.indicator fun _ ↦ (1 : ℝ≥0∞)))
      _ = ∑' x : E, 0 := by
            refine tsum_congr fun x ↦ ?_
            by_cases hx : π ({x} : Set E) = 0 <;> simp [s, hx]
      _ = 0 := by simp
  have hs_ae : ∀ᵐ x ∂π, x ∉ s := by
    rw [ae_iff]
    simpa [s] using hzero
  exact hs_ae.mono fun x hx ↦ by simpa [s] using hx

/-- Helper for Exercise 19.2.1: if two functions agree `π`-a.e., then they agree at every state
whose singleton mass under `π` is positive. -/
private theorem eq_of_aeEq_of_singletonMass_ne_zero
    {π : Measure E} {φ ψ : E → ℝ}
    (hEq : φ =ᵐ[π] ψ) {x : E} (hπx : π ({x} : Set E) ≠ 0) :
    φ x = ψ x := by
  by_contra hne
  have hnull : π {z : E | φ z ≠ ψ z} = 0 := by
    -- Proof comment: rewrite `π`-a.e. equality as nullity of the disagreement set.
    simpa [Filter.EventuallyEq, ae_iff] using hEq
  have hxnull : π ({x} : Set E) = 0 := by
    refine measure_mono_null ?_ hnull
    intro z hz
    simp at hz
    simpa [hz, hne]
  exact hπx hxnull

/-- Helper for Exercise 19.2.1: reversibility forces every positive-mass row of `p` to ignore
zero-mass columns of `π`. This is the transport step needed to descend kernel averaging to
`L²(π)` classes. -/
private theorem discreteMatrixKernel_entry_eq_zero_of_singletonMass_eq_zero
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hbal : ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E))
    {x y : E} (hπx : π ({x} : Set E) ≠ 0) (hπy : π ({y} : Set E) = 0) :
    p x y = 0 := by
  have hxy : p x y * π ({x} : Set E) = 0 := by
    -- Proof comment: detailed balance moves the column mass to the zero singleton at `y`.
    simpa [hπy] using hbal x y
  rcases mul_eq_zero.mp hxy with hpxy | hxzero
  · exact hpxy
  · exact (hπx hxzero).elim

/-- Helper for Exercise 19.2.1: under reversibility, kernel averaging along
`discreteMatrixKernel p` depends only on the `L²(π)` class of the representative. -/
private theorem discreteMatrixKernelAveraging_congr_ae_of_reversible
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    {φ ψ : E → ℝ} (hφ : MemLp φ 2 π) (hψ : MemLp ψ 2 π) (hEq : φ =ᵐ[π] ψ) :
    (fun x ↦ ∫ y, φ y ∂discreteMatrixKernel p x) =ᵐ[π]
      fun x ↦ ∫ y, ψ y ∂discreteMatrixKernel p x := by
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  have hpoint :
      ∀ x : E, π ({x} : Set E) ≠ 0 →
        (∫ y, φ y ∂discreteMatrixKernel p x) = ∫ y, ψ y ∂discreteMatrixKernel p x := by
    intro x hπx
    rcases rowSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx hφ with
      ⟨hφabs, _⟩
    rcases rowSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx hψ with
      ⟨hψabs, _⟩
    -- Proof comment: expand both row integrals as absolutely convergent series and compare each
    -- term using either zero column mass or pointwise equality on positive-mass singletons.
    rw [integral_discreteMatrixKernel_eq_tsum_of_summableNorm hp φ x hφabs,
      integral_discreteMatrixKernel_eq_tsum_of_summableNorm hp ψ x hψabs]
    refine tsum_congr fun y ↦ ?_
    by_cases hπy : π ({y} : Set E) = 0
    · have hpxy : p x y = 0 :=
        discreteMatrixKernel_entry_eq_zero_of_singletonMass_eq_zero hbal hπx hπy
      simp [hpxy]
    · have hyEq : φ y = ψ y := eq_of_aeEq_of_singletonMass_ne_zero hEq hπy
      simp [hyEq]
  -- Proof comment: the only possible failures of pointwise equality occur on zero-mass
  -- singletons, and those states are `π`-negligible.
  have hAeNonzero : ∀ᵐ x ∂π, π ({x} : Set E) ≠ 0 := ae_nonzero_singletonMass
  filter_upwards [hAeNonzero] with x hπx
  exact hpoint x hπx

/-- Helper for Exercise 19.2.1: on every positive-mass row, the square of the kernel average is
bounded by the rowwise average of the square. This is the rowwise Jensen step for the forward
`L²(π)` operator construction. -/
private theorem sq_discreteMatrixKernelAveraging_le_rowSquareIntegral
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hbal : ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E))
    {x : E} (hπx : π ({x} : Set E) ≠ 0)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    (∫ y, φ y ∂discreteMatrixKernel p x) ^ 2 ≤
      ∫ y, (φ y) ^ 2 ∂discreteMatrixKernel p x := by
  have hsq :
      Summable (fun y : E ↦ (p x y).toReal * ‖(φ y) ^ 2‖) := by
    -- Proof comment: the existing rowwise square-summability lemma gives the integrability input
    -- for the row probability measure.
    simpa [Real.norm_eq_abs, abs_sq] using
      rowSquareSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx hφ
  have hrowMem : MemLp φ 2 (discreteMatrixKernel p x) := by
    -- Proof comment: on the discrete row measure, square-integrability is exactly integrability
    -- of the square.
    rw [MeasureTheory.memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable]
    simpa using
      integrable_discreteMatrixKernel_of_summableNorm hp (fun y ↦ (φ y) ^ 2) x hsq
  let q : PMF E := ⟨fun y : E ↦ p x y, ENNReal.summable.hasSum_iff.2 (hp x)⟩
  have hrow :
      discreteMatrixKernel p x = q.toMeasure := by
    simpa [q] using rowPmfToMeasure_eq_discreteMatrixKernel hp x
  have hrowMem' : MemLp φ 2 q.toMeasure := by simpa [hrow] using hrowMem
  have hvar_nonneg : 0 ≤ Var[φ; q.toMeasure] := variance_nonneg φ q.toMeasure
  -- Proof comment: rewrite the variance and move the nonnegative term to the other side.
  rw [variance_eq_sub hrowMem'] at hvar_nonneg
  have hsq_le :
      (∫ y, φ y ∂q.toMeasure) ^ 2 ≤ ∫ y, (φ y) ^ 2 ∂q.toMeasure := by
    exact sub_nonneg.mp hvar_nonneg
  simpa [hrow] using hsq_le

/-- Helper for Exercise 19.2.1: reversibility upgrades the rowwise Jensen estimate to a global
`π`-weighted square contraction for the raw kernel-averaging representative. -/
private theorem weightedEdgeSquareSeries_eq_sourceSquareSeries
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    let edge : E × E → ℝ := fun z ↦
      ((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (φ z.2) ^ 2
    Summable edge ∧
      ∑' z : E × E, edge z = ∑' y : E, π.real ({y} : Set E) * (φ y) ^ 2 := by
  let edge : E × E → ℝ := fun z ↦
    ((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (φ z.2) ^ 2
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  have hbalReal :
      ∀ x y : E,
        (p x y).toReal * π.real ({x} : Set E) = (p y x).toReal * π.real ({y} : Set E) :=
    by
      intro x y
      have hxy_ne : p x y ≠ ∞ := stochasticEntry_neTop hp x y
      have hyx_ne : p y x ≠ ∞ := stochasticEntry_neTop hp y x
      simpa [Measure.real_def, ENNReal.toReal_mul, hxy_ne, hyx_ne, (hπ_finite x).ne,
        (hπ_finite y).ne, mul_assoc, mul_left_comm, mul_comm] using
        congrArg ENNReal.toReal (hbal x y)
  have hsq : Summable (fun y : E ↦ π.real ({y} : Set E) * (φ y) ^ 2) :=
    summable_singletonMass_mul_sq_of_memLp hπ_finite hφ
  have hvertical :
      ∀ y : E, ∑' x : E, edge (x, y) = π.real ({y} : Set E) * (φ y) ^ 2 := by
    intro y
    have hrow_ne_top : ∑' x : E, p y x ≠ ∞ := by
      simpa [hp y]
    have hrow :
        Summable (fun x : E ↦ (p y x).toReal) :=
      ENNReal.summable_toReal hrow_ne_top
    have hrow_sum : ∑' x : E, (p y x).toReal = 1 := by
      simpa [hp y] using
        (ENNReal.tsum_toReal_eq (fun x : E ↦ stochasticEntry_neTop hp y x)).symm
    -- Proof comment: detailed balance rewrites each column fiber into a stochastic row of `p`.
    calc
      ∑' x : E, edge (x, y)
        = ∑' x : E, (p y x).toReal * (π.real ({y} : Set E) * (φ y) ^ 2) := by
            refine tsum_congr fun x ↦ ?_
            calc
              edge (x, y)
                = ((p x y).toReal * π.real ({x} : Set E)) * (φ y) ^ 2 := by
                    rfl
              _ = ((p y x).toReal * π.real ({y} : Set E)) * (φ y) ^ 2 := by
                    rw [hbalReal x y]
              _ = (p y x).toReal * (π.real ({y} : Set E) * (φ y) ^ 2) := by
                    ring
      _ = (∑' x : E, (p y x).toReal) * (π.real ({y} : Set E) * (φ y) ^ 2) := by
            simpa [mul_assoc] using hrow.tsum_mul_right (π.real ({y} : Set E) * (φ y) ^ 2)
      _ = π.real ({y} : Set E) * (φ y) ^ 2 := by
            rw [hrow_sum, one_mul]
  have hswapped :
      Summable (fun z : E × E ↦ edge z.swap) := by
    -- Proof comment: summability is easiest in the swapped order because each fixed column is a
    -- constant multiple of a stochastic row.
    refine (summable_prod_of_nonneg ?_).2 ?_
    · intro z
      positivity
    · constructor
      · intro y
        have hrow_ne_top : ∑' x : E, p y x ≠ ∞ := by
          simpa [hp y]
        have hrow :
            Summable (fun x : E ↦ (p y x).toReal) :=
          ENNReal.summable_toReal hrow_ne_top
        have hscaled :
            Summable (fun x : E ↦ (p y x).toReal * (π.real ({y} : Set E) * (φ y) ^ 2)) :=
          hrow.mul_right (π.real ({y} : Set E) * (φ y) ^ 2)
        refine hscaled.congr ?_
        intro x
        calc
          (p y x).toReal * (π.real ({y} : Set E) * (φ y) ^ 2)
            = ((p y x).toReal * π.real ({y} : Set E)) * (φ y) ^ 2 := by
                ring
          _ = ((p x y).toReal * π.real ({x} : Set E)) * (φ y) ^ 2 := by
                rw [← hbalReal x y]
          _ = edge (x, y) := by
                rfl
      · refine hsq.congr ?_
        intro y
        exact (hvertical y).symm
  have hedge : Summable edge := by
    simpa [edge] using hswapped.prod_symm
  constructor
  · exact hedge
  · -- Proof comment: the summable edge series can now be summed fiberwise and collapsed using
    -- the vertical normalization proved above.
    calc
      ∑' z : E × E, edge z = ∑' x : E, ∑' y : E, edge (x, y) := by
            simpa [edge] using hedge.tsum_prod
      _ = ∑' y : E, ∑' x : E, edge (x, y) := by
            simpa [edge] using
              (show Summable (Function.uncurry fun x y : E ↦ edge (x, y)) from hedge).tsum_comm.symm
      _ = ∑' y : E, π.real ({y} : Set E) * (φ y) ^ 2 := by
            refine tsum_congr fun y ↦ hvertical y

/-- Helper for Exercise 19.2.1: the reversible `π`-weighted row-square integrals collapse to the
source `L²(π)` square series. -/
private theorem weightedRowSquareIntegral_eq_sourceSquareSeries
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    let rowSq : E → ℝ := fun x ↦
      π.real ({x} : Set E) * ∫ y, (φ y) ^ 2 ∂discreteMatrixKernel p x
    Summable rowSq ∧
      ∑' x : E, rowSq x = ∑' y : E, π.real ({y} : Set E) * (φ y) ^ 2 := by
  let rowSq : E → ℝ := fun x ↦
    π.real ({x} : Set E) * ∫ y, (φ y) ^ 2 ∂discreteMatrixKernel p x
  let edge : E × E → ℝ := fun z ↦
    ((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (φ z.2) ^ 2
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  rcases weightedEdgeSquareSeries_eq_sourceSquareSeries hp hπ_finite hrev hφ with
    ⟨hedge, hedge_eq⟩
  have hrowEq :
      ∀ x : E, rowSq x = ∑' y : E, edge (x, y) := by
    intro x
    by_cases hπx : π ({x} : Set E) = 0
    · have hπx_real : π.real ({x} : Set E) = 0 := by
        simp [Measure.real_def, hπx]
      -- Proof comment: zero-mass rows vanish because the outer singleton weight is zero.
      simp [rowSq, edge, hπx_real]
    · have hrowSq :
        Summable (fun y : E ↦ (p x y).toReal * (φ y) ^ 2) :=
        rowSquareSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx hφ
      have hrowSqNorm :
          Summable (fun y : E ↦ (p x y).toReal * ‖(φ y) ^ 2‖) := by
        simpa [Real.norm_eq_abs, abs_sq] using hrowSq
      have hrowInt :
          ∫ y, (φ y) ^ 2 ∂discreteMatrixKernel p x =
            ∑' y : E, (p x y).toReal * (φ y) ^ 2 :=
        integral_discreteMatrixKernel_eq_tsum_of_summableNorm hp (fun y ↦ (φ y) ^ 2) x hrowSqNorm
      -- Proof comment: on positive-mass rows, the square integral is the absolutely convergent
      -- row series, so multiplying by `π {x}` matches the corresponding edge fiber.
      unfold rowSq
      rw [hrowInt]
      calc
        π.real ({x} : Set E) * ∑' y : E, (p x y).toReal * (φ y) ^ 2
          = ∑' y : E, π.real ({x} : Set E) * ((p x y).toReal * (φ y) ^ 2) := by
              simpa [mul_assoc] using (hrowSq.tsum_mul_left (π.real ({x} : Set E))).symm
        _ = ∑' y : E, edge (x, y) := by
              refine tsum_congr fun y ↦ ?_
              simp [edge, mul_assoc, mul_left_comm, mul_comm]
  have hrowFun : rowSq = fun x ↦ ∑' y : E, edge (x, y) := funext hrowEq
  constructor
  · -- Proof comment: summability of the row integrals is inherited from the summable edge
    -- series after summing fiberwise.
    have hrowSummable : Summable rowSq := by
      simpa [hrowFun] using hedge.prod
    simpa [rowSq] using hrowSummable
  · -- Proof comment: once each row is rewritten as its edge fiber, the total mass is exactly the
    -- previously normalized edge-square series.
    have hrowEqSum :
        ∑' x : E, rowSq x = ∑' y : E, π.real ({y} : Set E) * (φ y) ^ 2 := by
      calc
        ∑' x : E, rowSq x = ∑' x : E, ∑' y : E, edge (x, y) := by
              simp [hrowFun]
        _ = ∑' z : E × E, edge z := by
              simpa [edge] using hedge.tsum_prod.symm
        _ = ∑' y : E, π.real ({y} : Set E) * (φ y) ^ 2 := hedge_eq
    simpa [rowSq] using hrowEqSum

/-- Helper for Exercise 19.2.1: reversibility upgrades the rowwise Jensen estimate to a global
`π`-weighted square contraction for the raw kernel-averaging representative. -/
private theorem weightedSquare_discreteMatrixKernelAveraging_le_of_reversible
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    let avgFun : E → ℝ := fun x ↦ ∫ y, φ y ∂discreteMatrixKernel p x
    Summable (fun x ↦ π.real ({x} : Set E) * (avgFun x) ^ 2) ∧
      ∑' x : E, π.real ({x} : Set E) * (avgFun x) ^ 2 ≤
        ∑' y : E, π.real ({y} : Set E) * (φ y) ^ 2 := by
  let avgFun : E → ℝ := fun x ↦ ∫ y, φ y ∂discreteMatrixKernel p x
  let rowSq : E → ℝ := fun x ↦
    π.real ({x} : Set E) * ∫ y, (φ y) ^ 2 ∂discreteMatrixKernel p x
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  rcases weightedRowSquareIntegral_eq_sourceSquareSeries hp hπ_finite hrev hφ with
    ⟨hrowSqSummable, hrowSqEq⟩
  have hpointwise :
      ∀ x : E, π.real ({x} : Set E) * (avgFun x) ^ 2 ≤ rowSq x := by
    intro x
    by_cases hπx : π ({x} : Set E) = 0
    · have hπx_real : π.real ({x} : Set E) = 0 := by
        simp [Measure.real_def, hπx]
      -- Proof comment: zero-mass rows contribute nothing to the weighted square sum.
      simp [avgFun, rowSq, hπx_real]
    · -- Proof comment: on positive-mass rows, multiply the Jensen estimate by the nonnegative
      -- singleton mass `π.real {x}`.
      have hjensen :
          (∫ y, φ y ∂discreteMatrixKernel p x) ^ 2 ≤
            ∫ y, (φ y) ^ 2 ∂discreteMatrixKernel p x :=
        sq_discreteMatrixKernelAveraging_le_rowSquareIntegral hp hπ_finite hbal hπx hφ
      exact mul_le_mul_of_nonneg_left hjensen MeasureTheory.measureReal_nonneg
  have havgSummable :
      Summable (fun x ↦ π.real ({x} : Set E) * (avgFun x) ^ 2) :=
    Summable.of_nonneg_of_le (fun x ↦ by positivity) hpointwise hrowSqSummable
  have hdiff_nonneg :
      0 ≤ ∑' x : E, (rowSq x - π.real ({x} : Set E) * (avgFun x) ^ 2) := by
    have hdiffSummable :
        Summable (fun x : E ↦ rowSq x - π.real ({x} : Set E) * (avgFun x) ^ 2) :=
      hrowSqSummable.sub havgSummable
    have hterm_nonneg :
        ∀ x : E, 0 ≤ rowSq x - π.real ({x} : Set E) * (avgFun x) ^ 2 := by
      intro x
      exact sub_nonneg.mpr (hpointwise x)
    simpa [hrowSqSummable.tsum_sub havgSummable] using tsum_nonneg hterm_nonneg
  constructor
  · exact havgSummable
  · -- Proof comment: compare the weighted average-square series to the normalized row-square
    -- series, then collapse that series to the source `L²(π)` square mass.
    have havg_le_rowSq :
        ∑' x : E, π.real ({x} : Set E) * (avgFun x) ^ 2 ≤ ∑' x : E, rowSq x := by
      have hdiff_nonneg' := hdiff_nonneg
      rw [hrowSqSummable.tsum_sub havgSummable] at hdiff_nonneg'
      linarith
    calc
      ∑' x : E, π.real ({x} : Set E) * (avgFun x) ^ 2 ≤ ∑' x : E, rowSq x := havg_le_rowSq
      _ = ∑' y : E, π.real ({y} : Set E) * (φ y) ^ 2 := hrowSqEq

/-- Helper for Exercise 19.2.1: the square of the `L²(π)` norm of a real representative is the
integral of its pointwise square. This keeps the later norm estimate at the stable `L²`/integral
interface instead of reopening `eLpNorm` calculations. -/
private theorem toLpNormSqEqIntegralSq
    {π : Measure E} {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    ‖hφ.toLp φ‖ ^ 2 = ∫ x, (φ x) ^ 2 ∂π := by
  -- Proof comment: rewrite the `L²` norm through the inner product of the class with itself, then
  -- collapse the pointwise inner product on `ℝ` to an ordinary square.
  calc
    ‖hφ.toLp φ‖ ^ 2 = inner ℝ (hφ.toLp φ) (hφ.toLp φ) := by simp
    _ = ∫ x, φ x * φ x ∂π := by
          rw [MeasureTheory.L2.inner_def]
          apply integral_congr_ae
          filter_upwards [hφ.coeFn_toLp, hφ.coeFn_toLp] with x hx hy
          simpa [hx, hy, pow_two]
    _ = ∫ x, (φ x) ^ 2 ∂π := by
          simp [sq]

/-- Helper for Exercise 19.2.1: the reversible raw kernel average has an `L²(π)` representative,
and its `L²(π)` norm is controlled by the norm of the source representative. This is the exact
packaging theorem needed before constructing the forward Markov operator on `L²(π)`. -/
private theorem discreteMatrixKernelAveraging_memLp_norm_le_of_reversible
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    {φ : E → ℝ} (hφ : MemLp φ 2 π) :
    let avgFun : E → ℝ := fun x ↦ ∫ y, φ y ∂discreteMatrixKernel p x
    ∃ havg : MemLp avgFun 2 π, ‖havg.toLp avgFun‖ ≤ ‖hφ.toLp φ‖ := by
  classical
  let avgFun : E → ℝ := fun x ↦ ∫ y, φ y ∂discreteMatrixKernel p x
  rcases weightedSquare_discreteMatrixKernelAveraging_le_of_reversible hp hπ_finite hrev hφ with
    ⟨havgSummable, havgSqLe⟩
  have hsqIntegrable_sum :
      Integrable (fun x ↦ (avgFun x) ^ 2)
        (Measure.sum fun x : E ↦ π ({x} : Set E) • Measure.dirac x) := by
    -- Proof comment: on a countable discrete measure, summability of the singleton-weighted
    -- square series is exactly integrability of the square.
    rw [show
      Integrable (fun x : E ↦ (avgFun x) ^ 2)
          (Measure.sum fun x : E ↦ π ({x} : Set E) • Measure.dirac x) ↔
        Summable (fun x : E ↦ (π ({x} : Set E)).toReal * ‖(avgFun x) ^ 2‖) from
      MeasureTheory.integrable_sum_dirac_iff (fun x ↦ (hπ_finite x).ne)]
    simpa [Real.norm_eq_abs, abs_sq] using havgSummable
  have hsqIntegrable : Integrable (fun x ↦ (avgFun x) ^ 2) π := by
    simpa [MeasureTheory.Measure.sum_smul_dirac] using hsqIntegrable_sum
  have havg : MemLp avgFun 2 π := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable]
    simpa using hsqIntegrable
  have hφSqIntegrable : Integrable (fun x ↦ (φ x) ^ 2) π := hφ.integrable_sq
  have havgNormSq :
      ‖havg.toLp avgFun‖ ^ 2 =
        ∑' x : E, π.real ({x} : Set E) * (avgFun x) ^ 2 := by
    -- Proof comment: expand the square norm into the discrete singleton-mass weighted series.
    calc
      ‖havg.toLp avgFun‖ ^ 2 = ∫ x, (avgFun x) ^ 2 ∂π :=
        toLpNormSqEqIntegralSq havg
      _ = ∑' x : E, π.real ({x} : Set E) • (avgFun x) ^ 2 := by
            simpa using (MeasureTheory.integral_countable hsqIntegrable)
      _ = ∑' x : E, π.real ({x} : Set E) * (avgFun x) ^ 2 := by
            simp_rw [smul_eq_mul]
  have hφNormSq :
      ‖hφ.toLp φ‖ ^ 2 =
        ∑' x : E, π.real ({x} : Set E) * (φ x) ^ 2 := by
    -- Proof comment: the source `L²(π)` norm has the same discrete square expansion.
    calc
      ‖hφ.toLp φ‖ ^ 2 = ∫ x, (φ x) ^ 2 ∂π :=
        toLpNormSqEqIntegralSq hφ
      _ = ∑' x : E, π.real ({x} : Set E) • (φ x) ^ 2 := by
            simpa using (MeasureTheory.integral_countable hφSqIntegrable)
      _ = ∑' x : E, π.real ({x} : Set E) * (φ x) ^ 2 := by
            simp_rw [smul_eq_mul]
  refine ⟨havg, ?_⟩
  have hnorm_sq :
      ‖havg.toLp avgFun‖ ^ 2 ≤ ‖hφ.toLp φ‖ ^ 2 := by
    rw [havgNormSq, hφNormSq]
    exact havgSqLe
  -- Proof comment: both `L²` norms are nonnegative, so the square inequality descends to the
  -- desired norm inequality.
  nlinarith [hnorm_sq, norm_nonneg (havg.toLp avgFun), norm_nonneg (hφ.toLp φ)]

/-- Helper for Exercise 19.2.1: kernel averaging on canonical `L²(π)` representatives is additive
almost everywhere under reversibility. This is the linearity bridge needed to package the forward
Markov operator on `L²(π)`. -/
private theorem discreteMatrixKernelAveraging_add_ae_of_reversible
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    (f g : E →₂[π] ℝ) :
    (fun x ↦ ∫ y, ((f + g : E →₂[π] ℝ) : E → ℝ) y ∂discreteMatrixKernel p x) =ᵐ[π]
      fun x ↦
        (∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x) +
          (∫ y, (g : E → ℝ) y ∂discreteMatrixKernel p x) := by
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  have hcoe :
      (fun y ↦ ((f + g : E →₂[π] ℝ) : E → ℝ) y) =ᵐ[π]
        fun y ↦ (f : E → ℝ) y + (g : E → ℝ) y := by
    simpa using (Lp.coeFn_add f g)
  have havg :
      (fun x ↦ ∫ y, ((f + g : E →₂[π] ℝ) : E → ℝ) y ∂discreteMatrixKernel p x) =ᵐ[π]
        fun x ↦ ∫ y, ((f : E → ℝ) y + (g : E → ℝ) y) ∂discreteMatrixKernel p x := by
    exact discreteMatrixKernelAveraging_congr_ae_of_reversible hp hπ_finite hrev
      (Lp.memLp (f + g)) ((Lp.memLp f).add (Lp.memLp g)) hcoe
  -- Proof comment: once the two representatives are aligned, positive-mass rows are ordinary
  -- absolutely convergent series, so `integral_add` gives the rowwise formula.
  have hAeNonzero : ∀ᵐ x ∂π, π ({x} : Set E) ≠ 0 := ae_nonzero_singletonMass
  filter_upwards [hAeNonzero, havg] with x hπx havgx
  rcases rowSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx (Lp.memLp f) with
    ⟨hfabs, _⟩
  rcases rowSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx (Lp.memLp g) with
    ⟨hgabs, _⟩
  have hfint :
      Integrable (fun y ↦ (f : E → ℝ) y) (discreteMatrixKernel p x) :=
    integrable_discreteMatrixKernel_of_summableNorm hp (fun y ↦ (f : E → ℝ) y) x hfabs
  have hgint :
      Integrable (fun y ↦ (g : E → ℝ) y) (discreteMatrixKernel p x) :=
    integrable_discreteMatrixKernel_of_summableNorm hp (fun y ↦ (g : E → ℝ) y) x hgabs
  rw [havgx, integral_add hfint hgint]

/-- Helper for Exercise 19.2.1: kernel averaging on canonical `L²(π)` representatives is
homogeneous almost everywhere under reversibility. -/
private theorem discreteMatrixKernelAveraging_smul_ae_of_reversible
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    (c : ℝ) (f : E →₂[π] ℝ) :
    (fun x ↦ ∫ y, ((c • f : E →₂[π] ℝ) : E → ℝ) y ∂discreteMatrixKernel p x) =ᵐ[π]
      fun x ↦ c * (∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x) := by
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  have hcoe :
      (fun y ↦ ((c • f : E →₂[π] ℝ) : E → ℝ) y) =ᵐ[π]
        fun y ↦ c * (f : E → ℝ) y := by
    simpa [smul_eq_mul] using (Lp.coeFn_smul c f)
  have havg :
      (fun x ↦ ∫ y, ((c • f : E →₂[π] ℝ) : E → ℝ) y ∂discreteMatrixKernel p x) =ᵐ[π]
        fun x ↦ ∫ y, c * (f : E → ℝ) y ∂discreteMatrixKernel p x := by
    exact discreteMatrixKernelAveraging_congr_ae_of_reversible hp hπ_finite hrev
      (Lp.memLp (c • f)) ((Lp.memLp f).const_mul c) hcoe
  -- Proof comment: after descending to the concrete representative `c * f`, scalar linearity of
  -- the row integral gives the desired formula on every positive-mass row.
  have hAeNonzero : ∀ᵐ x ∂π, π ({x} : Set E) ≠ 0 := ae_nonzero_singletonMass
  filter_upwards [hAeNonzero, havg] with x hπx havgx
  rcases rowSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx (Lp.memLp f) with
    ⟨hfabs, _⟩
  have hfint :
      Integrable (fun y ↦ (f : E → ℝ) y) (discreteMatrixKernel p x) :=
    integrable_discreteMatrixKernel_of_summableNorm hp (fun y ↦ (f : E → ℝ) y) x hfabs
  rw [havgx, integral_const_mul]

/-- Helper for Exercise 19.2.1: taking `toReal` turns singleton detailed balance into an equality
of the real-valued edge weights used in the `L²(π)` symmetry argument. -/
private theorem singletonBalance_toReal
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hbal : ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E)) :
    ∀ x y : E,
      (p x y).toReal * π.real ({x} : Set E) = (p y x).toReal * π.real ({y} : Set E) := by
  intro x y
  have hxy_ne : p x y ≠ ∞ := stochasticEntry_neTop hp x y
  have hyx_ne : p y x ≠ ∞ := stochasticEntry_neTop hp y x
  simpa [Measure.real_def, ENNReal.toReal_mul, hxy_ne, hyx_ne, (hπ_finite x).ne,
    (hπ_finite y).ne, mul_assoc, mul_left_comm, mul_comm] using
    congrArg ENNReal.toReal (hbal x y)

/-- Helper for Exercise 19.2.1: the real-weighted edge series controlling the discrete reversible
`L²(π)` operator is absolutely summable. This is the only summability input needed for the final
`tsum_comm` symmetry step. -/
private theorem weightedEdgeSummable_of_reversible
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    (f g : E →₂[π] ℝ) :
    Summable (fun z : E × E ↦
      ‖((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (((f : E → ℝ) z.2) * g z.1)‖) := by
  let fEdgeSq : E × E → ℝ := fun z ↦
    ((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (((f : E → ℝ) z.2) ^ 2)
  have hfsqProd :
      Summable fEdgeSq := by
    simpa [fEdgeSq] using
      (weightedEdgeSquareSeries_eq_sourceSquareSeries hp hπ_finite hrev (Lp.memLp f)).1
  have hgsqSource :
      Summable (fun x : E ↦ π.real ({x} : Set E) * (g x) ^ 2) :=
    summable_singletonMass_mul_sq_of_memLp hπ_finite (Lp.memLp g)
  have hgsqProd :
      Summable (fun z : E × E ↦
        ((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (g z.1) ^ 2) := by
    -- Proof comment: the `g`-square part is already normalized in the forward row direction, so
    -- no balance rewrite is needed.
    refine (summable_prod_of_nonneg ?_).2 ?_
    · intro z
      positivity
    · constructor
      · intro x
        have hrow_ne_top : ∑' y : E, p x y ≠ ∞ := by
          simpa [hp x]
        have hrow :
            Summable (fun y : E ↦ (p x y).toReal) :=
          ENNReal.summable_toReal hrow_ne_top
        show Summable (fun y : E ↦
          ((p x y).toReal * π.real ({x} : Set E)) * (g x) ^ 2)
        refine (hrow.mul_right (π.real ({x} : Set E) * (g x) ^ 2)).congr ?_
        intro y
        ring
      · refine hgsqSource.congr ?_
        intro x
        have hrow_ne_top : ∑' y : E, p x y ≠ ∞ := by
          simpa [hp x]
        have hrow :
            Summable (fun y : E ↦ (p x y).toReal) :=
          ENNReal.summable_toReal hrow_ne_top
        have hrow_sum : ∑' y : E, (p x y).toReal = 1 := by
          simpa [hp x] using
            (ENNReal.tsum_toReal_eq (fun y : E ↦ stochasticEntry_neTop hp x y)).symm
        exact (calc
          ∑' y : E, ((p x y).toReal * π.real ({x} : Set E)) * (g x) ^ 2
            = ∑' y : E, (p x y).toReal * (π.real ({x} : Set E) * (g x) ^ 2) := by
                refine tsum_congr fun y ↦ ?_
                ring
          _ = (∑' y : E, (p x y).toReal) * (π.real ({x} : Set E) * (g x) ^ 2) := by
                simpa [mul_assoc] using hrow.tsum_mul_right (π.real ({x} : Set E) * (g x) ^ 2)
          _ = π.real ({x} : Set E) * (g x) ^ 2 := by
                rw [hrow_sum, one_mul]).symm
  have hmajorant :
      Summable (fun z : E × E ↦
        (1 / 2 : ℝ) *
          ((((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (((f : E → ℝ) z.2) ^ 2)) +
            (((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (g z.1) ^ 2))) := by
    exact (hfsqProd.add hgsqProd).mul_left (1 / 2 : ℝ)
  have hbound :
      ∀ z : E × E,
        ‖((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (((f : E → ℝ) z.2) * g z.1)‖ ≤
          (1 / 2 : ℝ) *
            ((((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (((f : E → ℝ) z.2) ^ 2)) +
              (((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (g z.1) ^ 2)) := by
    intro z
    let a : ℝ := ((f : E → ℝ) z.2)
    let b : ℝ := g z.1
    let w : ℝ := (p z.1 z.2).toReal * π.real ({z.1} : Set E)
    have hw_nonneg : 0 ≤ w := by
      dsimp [w]
      positivity
    have hbase : 2 * (|a| * |b|) ≤ a ^ 2 + b ^ 2 := by
      simpa [a, b, sq_abs, mul_assoc] using two_mul_le_add_sq |a| |b|
    have hscaled :
        (w / 2) * (2 * (|a| * |b|)) ≤ (w / 2) * (a ^ 2 + b ^ 2) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    -- Proof comment: `2ab ≤ a² + b²` gives a pointwise majorant by the sum of the two square
    -- edge series.
    calc
      ‖w * (a * b)‖ = (w / 2) * (2 * (|a| * |b|)) := by
        have hw_abs : |w| = w := abs_of_nonneg hw_nonneg
        calc
          ‖w * (a * b)‖ = |w * (a * b)| := by simp [Real.norm_eq_abs]
          _ = |w| * |a * b| := by rw [abs_mul]
          _ = w * (|a| * |b|) := by rw [hw_abs, abs_mul]
          _ = (w / 2) * (2 * (|a| * |b|)) := by ring
      _ ≤ (w / 2) * (a ^ 2 + b ^ 2) := hscaled
      _ = (1 / 2 : ℝ) * (w * a ^ 2 + w * b ^ 2) := by
            ring
      _ = (1 / 2 : ℝ) *
            ((((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (((f : E → ℝ) z.2) ^ 2)) +
              (((p z.1 z.2).toReal * π.real ({z.1} : Set E)) * (g z.1) ^ 2)) := by
            simp [a, b, w, mul_assoc, mul_left_comm, mul_comm]
  exact Summable.of_nonneg_of_le (fun z ↦ by positivity) hbound hmajorant

/-- Helper for Exercise 19.2.1: every `L²(π)` realization of the reversible discrete kernel
operator has the stable real-weighted double-sum formula for its inner product. -/
private theorem inner_discreteMatrixKernelAveraging_eq_weightedDoubleSum
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    {T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT : Kernel.IsL2TransitionOperator (discreteMatrixKernel p) π T)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π)
    (f g : E →₂[π] ℝ) :
    inner ℝ (T f) g =
      ∑' x : E, ∑' y : E,
        ((p x y).toReal * π.real ({x} : Set E)) * (((f : E → ℝ) y) * g x) := by
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  have hTf :
      T f =ᵐ[π] fun x ↦ ∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x := by
    simpa using hT (Lp.memLp f)
  have houterTerm :
      ∀ x : E,
        π.real ({x} : Set E) * (T f x * g x) =
          π.real ({x} : Set E) *
            ((∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x) * g x) := by
    intro x
    by_cases hπx : π ({x} : Set E) = 0
    · have hπx_real : π.real ({x} : Set E) = 0 := by
        simp [Measure.real_def, hπx]
      -- Proof comment: zero-mass states disappear from the outer singleton-weighted series.
      simp [hπx_real]
    · have hTx :
          T f x = ∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x :=
        eq_of_aeEq_of_singletonMass_ne_zero hTf hπx
      simp [hTx]
  have hrowTerm :
      ∀ x : E,
        π.real ({x} : Set E) *
            ((∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x) * g x) =
          ∑' y : E,
            ((p x y).toReal * π.real ({x} : Set E)) * (((f : E → ℝ) y) * g x) := by
    intro x
    by_cases hπx : π ({x} : Set E) = 0
    · have hπx_real : π.real ({x} : Set E) = 0 := by
        simp [Measure.real_def, hπx]
      simp [hπx_real]
    · rcases rowSummable_of_memLp_of_singleton_pos hp hπ_finite hbal hπx (Lp.memLp f) with
        ⟨hfabs, hfsum⟩
      -- Proof comment: on positive-mass rows, the kernel average is an absolutely convergent
      -- weighted series, so we can move both outer factors inside the `tsum`.
      rw [integral_discreteMatrixKernel_eq_tsum_of_summableNorm hp (fun y ↦ (f : E → ℝ) y) x
        hfabs]
      calc
        π.real ({x} : Set E) * ((∑' y : E, (p x y).toReal * (f : E → ℝ) y) * g x)
          = π.real ({x} : Set E) * ∑' y : E, ((p x y).toReal * (f : E → ℝ) y) * g x := by
              rw [hfsum.tsum_mul_right (g x)]
        _ = ∑' y : E, π.real ({x} : Set E) * (((p x y).toReal * (f : E → ℝ) y) * g x) := by
              simpa [mul_assoc] using
                ((hfsum.mul_right (g x)).tsum_mul_left (π.real ({x} : Set E))).symm
        _ = ∑' y : E,
              ((p x y).toReal * π.real ({x} : Set E)) * (((f : E → ℝ) y) * g x) := by
              refine tsum_congr fun y ↦ ?_
              simp [mul_assoc, mul_left_comm, mul_comm]
  -- Proof comment: expand the `L²` inner product into the discrete singleton-mass series, then
  -- rewrite each row by the corresponding absolutely convergent weighted sum.
  calc
    inner ℝ (T f) g = ∫ x, inner ℝ (T f x) (g x) ∂π := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∑' x : E, π.real ({x} : Set E) • inner ℝ (T f x) (g x) := by
          simpa using
            (MeasureTheory.integral_countable (μ := π)
              (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (T f) g))
    _ = ∑' x : E, π.real ({x} : Set E) * inner ℝ (T f x) (g x) := by
          refine tsum_congr fun x ↦ ?_
          simp [smul_eq_mul]
    _ = ∑' x : E, π.real ({x} : Set E) * (T f x * g x) := by
          refine tsum_congr fun x ↦ ?_
          have hinner : inner ℝ (T f x) (g x) = g x * T f x := by
            exact RCLike.inner_apply (T f x) (g x)
          rw [hinner]
          ring
    _ = ∑' x : E, π.real ({x} : Set E) *
          ((∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x) * g x) := by
            refine tsum_congr fun x ↦ houterTerm x
    _ = ∑' x : E, ∑' y : E,
          ((p x y).toReal * π.real ({x} : Set E)) * (((f : E → ℝ) y) * g x) := by
            refine tsum_congr fun x ↦ hrowTerm x

/-- Helper for Exercise 19.2.1: every `L²(π)` realization of the reversible discrete kernel
averaging operator is symmetric. -/
private theorem discreteMatrixKernelAveraging_isSymmetric_of_reversible
    {p : E → E → ℝ≥0∞} {π : Measure E} [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞)
    {T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT : Kernel.IsL2TransitionOperator (discreteMatrixKernel p) π T)
    (hrev : Kernel.IsReversible (discreteMatrixKernel p) π) :
    (T : (E →₂[π] ℝ) →ₗ[ℝ] (E →₂[π] ℝ)).IsSymmetric := by
  have hbal :
      ∀ x y : E, p x y * π ({x} : Set E) = p y x * π ({y} : Set E) :=
    singletonBalance_of_isReversible_discreteMatrixKernel hrev
  have hbalReal :
      ∀ x y : E,
        (p x y).toReal * π.real ({x} : Set E) = (p y x).toReal * π.real ({y} : Set E) :=
    singletonBalance_toReal hp hπ_finite hbal
  intro f g
  let series : E → E → ℝ := fun x y ↦
    ((p x y).toReal * π.real ({x} : Set E)) * (((f : E → ℝ) y) * g x)
  have hseries :
      Summable (Function.uncurry series) :=
    (weightedEdgeSummable_of_reversible hp hπ_finite hrev f g).of_norm
  -- Proof comment: the double-sum formula reduces symmetry to a single reversible edge swap.
  calc
    inner ℝ (T f) g = ∑' x : E, ∑' y : E, series x y := by
      simpa [series] using
        inner_discreteMatrixKernelAveraging_eq_weightedDoubleSum hp hπ_finite hT hrev f g
    _ = ∑' y : E, ∑' x : E, series x y := by
          simpa [series] using hseries.tsum_comm.symm
    _ = ∑' y : E, ∑' x : E,
          ((p y x).toReal * π.real ({y} : Set E)) * (((g : E → ℝ) x) * f y) := by
            refine tsum_congr fun y ↦ ?_
            refine tsum_congr fun x ↦ ?_
            calc
              series x y
                = ((p x y).toReal * π.real ({x} : Set E)) * (((f : E → ℝ) y) * g x) := by
                    rfl
              _ = ((p y x).toReal * π.real ({y} : Set E)) * (((g : E → ℝ) x) * f y) := by
                    rw [hbalReal x y]
                    ring
    _ = inner ℝ (T g) f := by
          symm
          simpa using
            inner_discreteMatrixKernelAveraging_eq_weightedDoubleSum hp hπ_finite hT hrev g f
    _ = inner ℝ f (T g) := by
          rw [real_inner_comm]

-- Proof sketch: for the forward implication, construct the `L²(π)` realization of kernel
-- averaging along `discreteMatrixKernel p` and use reversibility to rewrite the `L²` inner
-- product symmetrically, giving self-adjointness. For the reverse implication, use a self-adjoint
-- realization and test the symmetry identity on singleton indicators in the discrete `L²(π)`
-- space to recover the singleton reversibility identities.
-- Semantic recall note: the canonical owner remains `Kernel.IsReversible`; the local discrete
-- bridge to singleton detailed balance is `Definition_19_8`, and the countable upgrade route is
-- the same one used in Chap18 support for `discreteMatrixKernel`.
/-- Exercise 19.2.1: a discrete transition matrix `p` is reversible with respect to `π` if and
only if the induced Markov averaging operator on `L²(π)` is self-adjoint. On the discrete state
space, finite singleton masses of `π` are needed so that singleton indicator functions lie in
`L²(π)` and can be used to recover detailed balance from self-adjointness. -/
theorem discreteMatrix_isReversible_iff_markovOperator_isSelfAdjoint
    {p : E → E → ℝ≥0∞} {π : Measure E}
    [Countable E]
    (hp : IsStochasticMatrix p)
    (hπ_finite : ∀ x : E, π {x} < ∞) :
    IsReversible (discreteMatrixKernel p) π ↔
      Kernel.HasSelfAdjointL2TransitionOperator (discreteMatrixKernel p) π :=
  by
    let _ : IsMarkovKernel (discreteMatrixKernel p) :=
      discreteMatrixKernel_isMarkovKernel _ hp
    constructor
    · intro hrev
      -- Route correction: the old forward route stalled on the invariant-column identity `hcol`
      -- before any stable `L²(π)` operator existed. The new route keeps only the detailed-balance
      -- data and packages kernel averaging through the proved `MemLp`/norm estimate first.
      let avgFun : (E →₂[π] ℝ) → E → ℝ := fun f x ↦
        ∫ y, (f : E → ℝ) y ∂discreteMatrixKernel p x
      have havg :
          ∀ f : E →₂[π] ℝ,
            ∃ hmem : MemLp (avgFun f) 2 π, ‖hmem.toLp (avgFun f)‖ ≤ ‖f‖ := by
        intro f
        -- Proof comment: the new `MemLp` packaging theorem supplies exactly the bounded raw
        -- representative needed to descend kernel averaging to `L²(π)`.
        simpa [avgFun] using
          discreteMatrixKernelAveraging_memLp_norm_le_of_reversible
            hp hπ_finite hrev (Lp.memLp f)
      let TLinear : (E →₂[π] ℝ) →ₗ[ℝ] (E →₂[π] ℝ) :=
        { toFun := fun f ↦ (Classical.choose (havg f)).toLp (avgFun f)
          map_add' := by
            intro f g
            -- Proof comment: the raw averaging representative is additive almost everywhere, so
            -- `MemLp.toLp_congr` identifies the chosen `toLp` classes.
            calc
              (Classical.choose (havg (f + g))).toLp (avgFun (f + g))
                  = ((Classical.choose (havg f)).add (Classical.choose (havg g))).toLp
                      (avgFun f + avgFun g) := by
                        apply MemLp.toLp_congr
                        exact discreteMatrixKernelAveraging_add_ae_of_reversible
                          hp hπ_finite hrev f g
              _ = (Classical.choose (havg f)).toLp (avgFun f) +
                    (Classical.choose (havg g)).toLp (avgFun g) := by
                      exact MemLp.toLp_add (Classical.choose (havg f))
                        (Classical.choose (havg g))
          map_smul' := by
            intro c f
            -- Proof comment: the same `toLp_congr` argument turns the a.e. scalar-linearity of
            -- the raw averaging representative into scalar-linearity on `L²(π)`.
            calc
              (Classical.choose (havg (c • f))).toLp (avgFun (c • f))
                  = ((Classical.choose (havg f)).const_smul c).toLp (c • avgFun f) := by
                        apply MemLp.toLp_congr
                        exact discreteMatrixKernelAveraging_smul_ae_of_reversible
                          hp hπ_finite hrev c f
              _ = c • (Classical.choose (havg f)).toLp (avgFun f) := by
                    exact MemLp.toLp_const_smul c (Classical.choose (havg f)) }
      have hbound : ∀ f : E →₂[π] ℝ, ‖TLinear f‖ ≤ 1 * ‖f‖ := by
        intro f
        -- Proof comment: the already-proved `MemLp` packaging theorem is exactly the operator
        -- norm estimate needed to upgrade the linear map to a continuous one.
        simpa [one_mul, TLinear] using (Classical.choose_spec (havg f))
      let T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ) :=
        LinearMap.mkContinuous TLinear 1 hbound
      have hTransition :
          Kernel.IsL2TransitionOperator (discreteMatrixKernel p) π T := by
        intro φ hφ
        have hrepr :
            T (hφ.toLp φ) =ᵐ[π]
              fun x ↦ ∫ y, (((hφ.toLp φ : E →₂[π] ℝ) : E → ℝ) y) ∂discreteMatrixKernel p x := by
          -- Proof comment: by construction, `T` is the `toLp` class of the raw averaging
          -- representative associated with the canonical `L²(π)` coercion.
          simpa [T, TLinear, avgFun] using
            (MemLp.coeFn_toLp (Classical.choose (havg (hφ.toLp φ))))
        exact hrepr.trans <|
          discreteMatrixKernelAveraging_congr_ae_of_reversible hp hπ_finite hrev
            (Lp.memLp (hφ.toLp φ)) hφ (MemLp.coeFn_toLp hφ)
      have hSymm :
          (T : (E →₂[π] ℝ) →ₗ[ℝ] (E →₂[π] ℝ)).IsSymmetric :=
        discreteMatrixKernelAveraging_isSymmetric_of_reversible
          hp hπ_finite hTransition hrev
      exact ⟨T, hTransition, hSymm.isSelfAdjoint⟩
    · rintro ⟨T, hT, hself⟩
      -- Proof comment: self-adjointness on singleton indicators recovers detailed balance.
      have hbal :
          ∀ x y : E, p x y * π {x} = p y x * π {y} :=
        singletonDetailedBalance_of_selfAdjointL2TransitionOperator hp hπ_finite hT hself
      -- Then convert the singleton balance equation back to kernel reversibility.
      exact isReversible_discreteMatrixKernel_of_singletonBalance hbal

end ProbabilityTheory
