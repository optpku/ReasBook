/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Fourier.AddCircle
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Remark_20_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 20.5.1 (1): strongly mixing implies weak mixing. This is exactly the already
formalized theorem `isWeaklyMixing_of_isStronglyMixing`. -/
recall isWeaklyMixing_of_isStronglyMixing

-- Proof sketch: apply weak mixing to an invariant measurable set `A` with `B = A`. The Cesàro
-- averages then have constant value `|P A - (P A)^2|`, so the weak-mixing limit forces
-- `P A = 0` or `P A = 1`, which is the defining criterion for ergodicity.
/-- Helper for Exercise 20.5.1: weak mixing forces every invariant measurable event to have
probability `0` or `1`. -/
lemma weakMixingInvariantEvent_probEqZeroOrOne
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hweak : IsWeaklyMixing τ P) {A : Set Ω} (hA : MeasurableSet A) (hτA : τ ⁻¹' A = A) :
    P A = 0 ∨ P A = 1 := by
  let c : ℝ := |P.real A - P.real A * P.real A|
  have hlimit_zero := hweak A A hA hA
  have hlimit_const :
      Filter.Tendsto
        (fun n : ℕ ↦
          (1 / (n : ℝ)) *
            (Finset.sum (Finset.range n) fun i ↦
              |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|))
        Filter.atTop
        (nhds c) := by
    -- After the finite prefix `n = 0`, every average is the same constant.
    refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hsum :
        Finset.sum (Finset.range n) (fun i ↦
          |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|) =
          n * c := by
      calc
        Finset.sum (Finset.range n) (fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|) =
            Finset.sum (Finset.range n) (fun _ ↦ c) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hiterateA : ∀ j : ℕ, (τ^[j]) ⁻¹' A = A := by
            intro j
            induction j with
            | zero =>
                simp
            | succ j ih =>
                change τ ⁻¹' ((τ^[j]) ⁻¹' A) = A
                rw [ih, hτA]
          rw [hiterateA i]
          simp [c]
        _ = n * c := by
          simp [c]
    -- Rewrite the Cesàro average of a constant sequence.
    rw [hsum]
    field_simp [hn0]
  have hc : c = 0 := tendsto_nhds_unique hlimit_const hlimit_zero
  have hreal :
      P.real A = 0 ∨ P.real A = 1 := by
    -- Route correction: factor the normalized constant instead of trying to solve the original
    -- absolute-value equation directly.
    have hmul : P.real A * (1 - P.real A) = 0 := by
      have habs : P.real A - P.real A * P.real A = 0 := abs_eq_zero.mp hc
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr <| by linarith
  rcases hreal with hzero | hone
  · left
    exact (measureReal_eq_zero_iff (μ := P) (s := A)).mp hzero
  · right
    exact (ENNReal.toReal_eq_one_iff (P A)).mp (by simpa [Measure.real] using hone)

/-- Part of Exercise 20.5.1: every weakly mixing probability-preserving dynamical system is
ergodic. -/
theorem ergodic_of_isWeaklyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (hweak : IsWeaklyMixing τ P) :
    Ergodic τ P := by
  refine { toMeasurePreserving := hτ, toPreErgodic := ?_ }
  refine ⟨?_⟩
  intro A hA hτA
  -- Convert weak mixing on invariant events into the zero-one law required by `PreErgodic`.
  rcases weakMixingInvariantEvent_probEqZeroOrOne P hweak hA hτA with hA0 | hA1
  · exact Filter.eventuallyConst_set'.2 <| Or.inl <| ae_eq_empty.2 hA0
  · have hA_compl : P Aᶜ = 0 := by
      rw [measure_compl hA (measure_ne_top P A), IsProbabilityMeasure.measure_univ, hA1, tsub_self]
    exact Filter.eventuallyConst_set'.2 <| Or.inr <| ae_eq_univ.2 hA_compl

/-- Helper for Exercise 20.5.1: subtract the mean from a complex `L²` observable. -/
noncomputable def centeredL2
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Lp ℂ 2 P) : Lp ℂ 2 P :=
  f - Lp.const 2 P (∫ x, f x ∂P)

/-- Helper for Exercise 20.5.1: centering is additive on `L²`. -/
lemma centeredL2_add
    (P : Measure Ω) [IsProbabilityMeasure P] (f g : Lp ℂ 2 P) :
    centeredL2 P (f + g) = centeredL2 P f + centeredL2 P g := by
  -- Proof comment: both the `L²` observable and its mean are additive.
  have hf : Integrable f P := (Lp.memLp f).integrable (by norm_num)
  have hg : Integrable g P := (Lp.memLp g).integrable (by norm_num)
  have hInt :
      ∫ x, (f + g) x ∂P = ∫ x, f x ∂P + ∫ x, g x ∂P := by
    calc
      ∫ x, (f + g) x ∂P = ∫ x, (f x + g x) ∂P := by
        refine integral_congr_ae ?_
        exact Lp.coeFn_add f g
      _ = ∫ x, f x ∂P + ∫ x, g x ∂P := integral_add hf hg
  rw [centeredL2, centeredL2, centeredL2, hInt]
  rw [(Lp.const 2 P).map_add]
  abel

/-- Helper for Exercise 20.5.1: centering commutes with subtraction on `L²`. -/
lemma centeredL2_sub
    (P : Measure Ω) [IsProbabilityMeasure P] (f g : Lp ℂ 2 P) :
    centeredL2 P (f - g) = centeredL2 P f - centeredL2 P g := by
  -- Proof comment: centering is additive and commutes with negation of the mean.
  have hf : Integrable f P := (Lp.memLp f).integrable (by norm_num)
  have hg : Integrable g P := (Lp.memLp g).integrable (by norm_num)
  have hInt :
      ∫ x, (f - g) x ∂P = ∫ x, f x ∂P - ∫ x, g x ∂P := by
    calc
      ∫ x, (f - g) x ∂P = ∫ x, (f x - g x) ∂P := by
        refine integral_congr_ae ?_
        exact Lp.coeFn_sub f g
      _ = ∫ x, f x ∂P - ∫ x, g x ∂P := integral_sub hf hg
  rw [centeredL2, centeredL2, centeredL2, hInt]
  rw [(Lp.const 2 P).map_sub]
  abel

/-- Helper for Exercise 20.5.1: the mean of an `L²` observable on a probability space is bounded
by its `L²` norm. -/
lemma norm_integral_le_normL2
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Lp ℂ 2 P) :
    ‖∫ x, f x ∂P‖ ≤ ‖f‖ := by
  let oneLp : Lp ℂ 2 P := Lp.const 2 P 1
  have hInner :
      inner ℂ oneLp f = ∫ x, f x ∂P := by
    -- Proof comment: the constant-one vector paired with `f` is exactly the integral of `f`.
    simpa [oneLp, MeasureTheory.indicatorConstLp_univ] using
      (MeasureTheory.L2.inner_indicatorConstLp_one
        (μ := P) (𝕜 := ℂ) MeasurableSet.univ (measure_ne_top P Set.univ) f)
  have hone : ‖oneLp‖ ≤ 1 := by
    -- Proof comment: on a probability space, the constant-one function has `L²` norm at most `1`.
    have hone_eq :
        ‖oneLp‖ = 1 := by
      simpa [oneLp, Measure.real] using
        (Lp.norm_const' (p := (2 : ENNReal)) (μ := P) (c := (1 : ℂ))
          (by norm_num) (by norm_num))
    rw [hone_eq]
  have hbound : ‖∫ x, f x ∂P‖ ≤ ‖oneLp‖ * ‖f‖ := by
    have hinner_norm : ‖inner ℂ oneLp f‖ ≤ ‖oneLp‖ * ‖f‖ := norm_inner_le_norm _ _
    rw [hInner] at hinner_norm
    exact hinner_norm
  exact
    hbound.trans <| by
      simpa using mul_le_mul_of_nonneg_right hone (norm_nonneg _)

/-- Helper for Exercise 20.5.1: centering enlarges the `L²` norm by at most a factor `2`. -/
lemma norm_centeredL2_le_two
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Lp ℂ 2 P) :
    ‖centeredL2 P f‖ ≤ 2 * ‖f‖ := by
  have hconst :
      ‖Lp.const 2 P (∫ x, f x ∂P)‖ ≤ ‖∫ x, f x ∂P‖ := by
    -- Proof comment: the constant function inherits the same norm bound on a probability space.
    have hnorm :
        ‖Lp.const 2 P (∫ x, f x ∂P)‖ = ‖∫ x, f x ∂P‖ := by
      simpa [Measure.real] using
        (Lp.norm_const' (p := (2 : ENNReal)) (μ := P) (c := ∫ x, f x ∂P)
          (by norm_num) (by norm_num))
    rw [hnorm]
  calc
    ‖centeredL2 P f‖ ≤ ‖f‖ + ‖Lp.const 2 P (∫ x, f x ∂P)‖ := by
      simpa [centeredL2] using norm_sub_le f (Lp.const 2 P (∫ x, f x ∂P))
    _ ≤ ‖f‖ + ‖∫ x, f x ∂P‖ := by
      simpa [add_comm] using add_le_add_left hconst ‖f‖
    _ ≤ ‖f‖ + ‖f‖ := by
      simpa [add_comm] using add_le_add_left (norm_integral_le_normL2 P f) ‖f‖
    _ = 2 * ‖f‖ := by ring

/-- Helper for Exercise 20.5.1: centering commutes with scalar multiplication on `L²`. -/
lemma centeredL2_smul
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (f : Lp ℂ 2 P) :
    centeredL2 P (c • f) = c • centeredL2 P f := by
  have hInt :
      ∫ x, (c • f) x ∂P = c * ∫ x, f x ∂P := by
    -- Proof comment: pull the scalar through the Bochner integral.
    calc
      ∫ x, (c • f) x ∂P = ∫ x, c * f x ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with x hx
        simpa [Pi.smul_apply] using hx
      _ = c * ∫ x, f x ∂P := integral_smul c (f : Ω → ℂ)
  rw [centeredL2, centeredL2, hInt, smul_sub]
  -- Proof comment: the constant-function embedding is linear, so the centered constant term also
  -- factors through the scalar.
  congr 1

/-- Helper for Exercise 20.5.1: centering commutes with composition by a measure-preserving map. -/
lemma centeredL2_compMeasurePreserving
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (f : Lp ℂ 2 P) :
    Lp.compMeasurePreserving τ hτ (centeredL2 P f) =
      centeredL2 P (Lp.compMeasurePreserving τ hτ f) := by
  have hf : Integrable f P := (Lp.memLp f).integrable (by norm_num)
  have hInt :
      ∫ x, (Lp.compMeasurePreserving τ hτ f) x ∂P = ∫ x, f x ∂P := by
    -- Proof comment: a measure-preserving change of variables leaves the mean unchanged.
    have hmeas :
        AEStronglyMeasurable (fun x ↦ f x) (Measure.map τ P) := by
      simpa [hτ.map_eq] using (Lp.stronglyMeasurable f).aestronglyMeasurable
    calc
      ∫ x, (Lp.compMeasurePreserving τ hτ f) x ∂P = ∫ x, f (τ x) ∂P := by
        refine integral_congr_ae ?_
        exact Lp.coeFn_compMeasurePreserving f hτ
      _ = ∫ y, f y ∂Measure.map τ P := by
        symm
        exact integral_map hτ.aemeasurable hmeas
      _ = ∫ x, f x ∂P := by rw [hτ.map_eq]
  rw [centeredL2, centeredL2, map_sub, hInt]
  -- Proof comment: once the mean is rewritten through `hτ`, the constant term is unchanged.
  congr 1

/-- Helper for Exercise 20.5.1: an indicator constant is the corresponding scalar multiple of the
unit-valued indicator constant. -/
lemma indicatorConstLp_smul_one
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A) (c : ℂ) :
    indicatorConstLp 2 hA (measure_ne_top P A) c =
      c • indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ) := by
  apply Lp.ext
  -- Proof comment: compare the two indicator representatives pointwise on and off the set `A`.
  filter_upwards
      [indicatorConstLp_coeFn (μ := P) (p := (2 : ENNReal)) (s := A)
          (hs := hA) (hμs := measure_ne_top P A) (c := c),
        indicatorConstLp_coeFn (μ := P) (p := (2 : ENNReal)) (s := A)
          (hs := hA) (hμs := measure_ne_top P A) (c := (1 : ℂ)),
        Lp.coeFn_smul c (indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ))] with x hc hone hsmul
  by_cases hx : x ∈ A
  · simp [hc, hone, hsmul, Pi.smul_apply, hx]
  · simp [hc, hone, hsmul, Pi.smul_apply, hx]

/-- Helper for Exercise 20.5.1: the centered `L²` inner product of two indicator functions is the
centered correlation error of the corresponding measurable sets. -/
lemma centeredIndicatorInner_eq_correlationError
    (P : Measure Ω) [IsProbabilityMeasure P] {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℂ
      (centeredL2 P (indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ)))
      (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ))) =
        (P.real (A ∩ B) - P.real A * P.real B : ℂ) := by
  let eA : Lp ℂ 2 P := indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ)
  let eB : Lp ℂ 2 P := indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ)
  have hIntA : ∫ x, eA x ∂P = (P.real A : ℂ) := by
    -- Proof comment: integrating the unit indicator over the whole space gives the set measure.
    have hIntA' :
        ∫ x, indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ) x ∂P =
          ((P.real A : ℝ) • (1 : ℂ)) := by
      exact
        (integral_indicatorConstLp (μ := P) (p := (2 : ENNReal))
          hA (measure_ne_top P A) (1 : ℂ))
    simpa [eA] using hIntA'.trans (by simp [Algebra.smul_def])
  have hIntB : ∫ x, eB x ∂P = (P.real B : ℂ) := by
    -- Proof comment: the same computation applies to `B`.
    have hIntB' :
        ∫ x, indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ) x ∂P =
          ((P.real B : ℝ) • (1 : ℂ)) := by
      exact
        (integral_indicatorConstLp (μ := P) (p := (2 : ENNReal))
          hB (measure_ne_top P B) (1 : ℂ))
    simpa [eB] using hIntB'.trans (by simp [Algebra.smul_def])
  have hAB : inner ℂ eA eB = (P.real (A ∩ B) : ℂ) := by
    -- Proof comment: the `L²` inner product of two unit indicators is the measure of the
    -- intersection.
    simpa [eA, eB, Set.inter_comm] using
      (MeasureTheory.L2.inner_indicatorConstLp_one_indicatorConstLp_one
        (μ := P) (𝕜 := ℂ) hA hB (measure_ne_top P A) (measure_ne_top P B))
  have hAuniv :
      inner ℂ eA (Lp.const 2 P (P.real B : ℂ)) = (P.real A * P.real B : ℂ) := by
    -- Proof comment: pairing an indicator with a constant only records the measure of that
    -- indicator set.
    rw [← indicatorConstLp_univ (μ := P) (p := (2 : ENNReal)) (c := (P.real B : ℂ))]
    simpa [eA, Set.inter_comm, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
        (μ := P) (𝕜 := ℂ) hA MeasurableSet.univ
        (measure_ne_top P A) (measure_ne_top P Set.univ) (a := (1 : ℂ)) (b := (P.real B : ℂ)))
  have hunivB :
      inner ℂ (Lp.const 2 P (P.real A : ℂ)) eB = (P.real A * P.real B : ℂ) := by
    -- Proof comment: the left-constant/right-indicator pairing is symmetric because the scalar is
    -- real.
    rw [← indicatorConstLp_univ (μ := P) (p := (2 : ENNReal)) (c := (P.real A : ℂ))]
    simpa [eB, Set.inter_comm, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
        (μ := P) (𝕜 := ℂ) MeasurableSet.univ hB
        (measure_ne_top P Set.univ) (measure_ne_top P B) (a := (P.real A : ℂ)) (b := (1 : ℂ)))
  have hunivUniv :
      inner ℂ (Lp.const 2 P (P.real A : ℂ)) (Lp.const 2 P (P.real B : ℂ)) =
        (P.real A * P.real B : ℂ) := by
    -- Proof comment: the whole-space constant pair contributes exactly the product of the means.
    repeat rw [← indicatorConstLp_univ (μ := P) (p := (2 : ENNReal))]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp
        (μ := P) (𝕜 := ℂ) MeasurableSet.univ MeasurableSet.univ
        (measure_ne_top P Set.univ) (measure_ne_top P Set.univ)
        (a := (P.real A : ℂ)) (b := (P.real B : ℂ)))
  -- Proof comment: expand the two centered indicators and collapse each term to a set measure.
  rw [centeredL2, centeredL2, hIntA, hIntB, inner_sub_left, inner_sub_right, inner_sub_right]
  rw [hAB, hAuniv, hunivB, hunivUniv]
  ring

/-- Helper for Exercise 20.5.1: weak-mixing set correlations are exactly the centered
indicator-vector correlations in `L²`. -/
lemma centeredIndicatorCorrelation_eq_correlationError
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    ‖inner ℂ
      (centeredL2 P (indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ)))
      (Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n)
        (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ))))‖ =
      |P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B| := by
  let eA : Lp ℂ 2 P := indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ)
  let eB : Lp ℂ 2 P := indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ)
  have hpreimage_ne_top : P ((τ^[n]) ⁻¹' B) ≠ ⊤ := by
    simpa [(hτ.iterate n).measure_preimage hB.nullMeasurableSet] using (measure_ne_top P B)
  have hpre :
      Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n) eB =
        indicatorConstLp 2 ((hτ.iterate n).measurable hB)
          hpreimage_ne_top (1 : ℂ) := by
    -- Proof comment: pulling back an indicator along an iterate just takes the preimage of the
    -- underlying set.
    simpa [eB] using
      (MeasureTheory.Lp.indicatorConstLp_compMeasurePreserving
        (p := (2 : ENNReal)) (f := τ^[n]) (s := B) hB
        (measure_ne_top P B) (1 : ℂ) (hτ.iterate n))
  have hcenter :
      Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n) (centeredL2 P eB) =
        centeredL2 P
          (indicatorConstLp 2 ((hτ.iterate n).measurable hB)
            hpreimage_ne_top (1 : ℂ)) := by
    -- Proof comment: transport the centering through the iterate before applying the indicator
    -- inner-product formula.
    rw [centeredL2_compMeasurePreserving (P := P) (hτ := hτ.iterate n), hpre]
  have hmeasure :
      P.real ((τ^[n]) ⁻¹' B) = P.real B := by
    -- Proof comment: measure-preserving iterates keep the measure of the target set.
    simpa [Measure.real] using
      congrArg ENNReal.toReal ((hτ.iterate n).measure_preimage hB.nullMeasurableSet)
  rw [hcenter]
  rw [centeredIndicatorInner_eq_correlationError (P := P) (A := A)
    (B := (τ^[n]) ⁻¹' B) hA ((hτ.iterate n).measurable hB)]
  rw [hmeasure]
  simpa using
    (Complex.norm_real
      (P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B))

/-- Helper for Exercise 20.5.1: the Cesàro average of centered `L²` correlations along the iterates
of a measure-preserving map. -/
noncomputable def centeredCorrelationCesaro
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (f g : Lp ℂ 2 P) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    (Finset.sum (Finset.range n) fun i ↦
      ‖inner ℂ (centeredL2 P f)
        (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖)

/-- Helper for Exercise 20.5.1: centered Cesàro correlations are nonnegative term by term. -/
lemma centeredCorrelationCesaro_nonneg
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (f g : Lp ℂ 2 P) (n : ℕ) :
    0 ≤ centeredCorrelationCesaro P hτ f g n := by
  -- Proof comment: both the prefactor and each summand are nonnegative real numbers.
  unfold centeredCorrelationCesaro
  refine mul_nonneg ?_ ?_
  · positivity
  · exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Helper for Exercise 20.5.1: scalar multiples of indicator observables scale the centered
correlation term by the product of the scalar norms. -/
lemma centeredIndicatorConstCorrelation_eq_smul_correlationError
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c d : ℂ) (n : ℕ) :
    ‖inner ℂ
      (centeredL2 P (indicatorConstLp 2 hA (measure_ne_top P A) c))
      (Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n)
        (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) d)))‖ =
      ‖c‖ * ‖d‖ * |P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B| := by
  -- Proof comment: rewrite both indicators as scalar multiples of the unit indicators and factor
  -- the scalars through centering, the iterate, and the inner product.
  have hmap :
      Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n)
          (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) d)) =
        d •
          Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n)
            (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ))) := by
    -- Proof comment: move the scalar through the indicator normalization before touching the
    -- inner product.
    -- Route correction: use the linear-map interface for `compMeasurePreserving` so the scalar
    -- transport is handled once by `map_smul` instead of pointwise coercion rewrites.
    rw [indicatorConstLp_smul_one, centeredL2_smul]
    exact
      (MeasureTheory.Lp.compMeasurePreservingₗ (𝕜 := ℂ) (E := ℂ) (p := (2 : ENNReal))
        (μ := P) (μb := P) (τ^[n]) (hτ.iterate n)).map_smul d
        (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ)))
  calc
    ‖inner ℂ
        (centeredL2 P (indicatorConstLp 2 hA (measure_ne_top P A) c))
        (Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n)
          (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) d)))‖ =
        ‖starRingEnd ℂ c * (d * inner ℂ
          (centeredL2 P (indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ)))
          (Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n)
            (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ)))))‖ := by
      rw [indicatorConstLp_smul_one, centeredL2_smul, hmap]
      rw [inner_smul_left, inner_smul_right]
    _ = ‖c‖ * ‖d‖ *
        ‖inner ℂ
          (centeredL2 P (indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℂ)))
          (Lp.compMeasurePreserving (τ^[n]) (hτ.iterate n)
            (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℂ))))‖ := by
      simp [norm_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = ‖c‖ * ‖d‖ * |P.real (A ∩ (τ^[n]) ⁻¹' B) - P.real A * P.real B| := by
      rw [centeredIndicatorCorrelation_eq_correlationError (P := P) (hτ := hτ) hA hB n]

/-- Helper for Exercise 20.5.1: centered Cesàro correlations are subadditive in the left input. -/
lemma centeredCorrelationCesaro_add_left_le
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (f₁ f₂ g : Lp ℂ 2 P) (n : ℕ) :
    centeredCorrelationCesaro P hτ (f₁ + f₂) g n ≤
      centeredCorrelationCesaro P hτ f₁ g n +
        centeredCorrelationCesaro P hτ f₂ g n := by
  -- Proof comment: expand centering on the left, then bound each summand by the triangle
  -- inequality inside the norm.
  unfold centeredCorrelationCesaro
  have hfac : 0 ≤ (1 / (n : ℝ)) := by positivity
  have hsum :
      Finset.sum (Finset.range n) (fun i ↦
          ‖inner ℂ (centeredL2 P (f₁ + f₂))
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) ≤
        Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f₁)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) +
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f₂)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) := by
    calc
      Finset.sum (Finset.range n) (fun i ↦
          ‖inner ℂ (centeredL2 P (f₁ + f₂))
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) ≤
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f₁)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ +
              ‖inner ℂ (centeredL2 P f₂)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [centeredL2_add, inner_add_left]
        exact norm_add_le _ _
      _ =
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f₁)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) +
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f₂)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) := by
        rw [Finset.sum_add_distrib]
  calc
    (1 / (n : ℝ)) *
        Finset.sum (Finset.range n) (fun i ↦
          ‖inner ℂ (centeredL2 P (f₁ + f₂))
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) ≤
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) (fun i ↦
              ‖inner ℂ (centeredL2 P f₁)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) +
            Finset.sum (Finset.range n) (fun i ↦
              ‖inner ℂ (centeredL2 P f₂)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖)) := by
      exact mul_le_mul_of_nonneg_left hsum hfac
    _ =
        centeredCorrelationCesaro P hτ f₁ g n +
          centeredCorrelationCesaro P hτ f₂ g n := by
      rw [centeredCorrelationCesaro, centeredCorrelationCesaro, mul_add]

/-- Helper for Exercise 20.5.1: centered Cesàro correlations are subadditive in the right input. -/
lemma centeredCorrelationCesaro_add_right_le
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (f g₁ g₂ : Lp ℂ 2 P) (n : ℕ) :
    centeredCorrelationCesaro P hτ f (g₁ + g₂) n ≤
      centeredCorrelationCesaro P hτ f g₁ n +
        centeredCorrelationCesaro P hτ f g₂ n := by
  -- Proof comment: the iterate is linear on `Lp`, so the right-input estimate is the same
  -- triangle-inequality argument after commuting centering with addition.
  unfold centeredCorrelationCesaro
  have hfac : 0 ≤ (1 / (n : ℝ)) := by positivity
  have hsum :
      Finset.sum (Finset.range n) (fun i ↦
          ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P (g₁ + g₂)))‖) ≤
        Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₁))‖) +
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₂))‖) := by
    calc
      Finset.sum (Finset.range n) (fun i ↦
          ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P (g₁ + g₂)))‖) ≤
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₁))‖ +
              ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₂))‖) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [centeredL2_add, map_add, inner_add_right]
        exact norm_add_le _ _
      _ =
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₁))‖) +
          Finset.sum (Finset.range n) (fun i ↦
            ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₂))‖) := by
        rw [Finset.sum_add_distrib]
  calc
    (1 / (n : ℝ)) *
        Finset.sum (Finset.range n) (fun i ↦
          ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P (g₁ + g₂)))‖) ≤
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) (fun i ↦
              ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₁))‖) +
            Finset.sum (Finset.range n) (fun i ↦
              ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g₂))‖)) := by
      exact mul_le_mul_of_nonneg_left hsum hfac
    _ =
        centeredCorrelationCesaro P hτ f g₁ n +
          centeredCorrelationCesaro P hτ f g₂ n := by
      rw [centeredCorrelationCesaro, centeredCorrelationCesaro, mul_add]

/-- Helper for Exercise 20.5.1: the centered Cesàro averages vary Lipschitz-continuously in the
left `L²` input. -/
lemma centeredCorrelationCesaro_leftDiff_le
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (f f' g : Lp ℂ 2 P) (n : ℕ) :
    |centeredCorrelationCesaro P hτ f g n - centeredCorrelationCesaro P hτ f' g n| ≤
      4 * ‖g‖ * ‖f - f'‖ := by
  by_cases hn : n = 0
  · subst hn
    simp [centeredCorrelationCesaro]
    positivity
  · have hsub :
        centeredL2 P f - centeredL2 P f' = centeredL2 P (f - f') := by
      rw [← centeredL2_sub]
    have hconst_nonneg : 0 ≤ 4 * ‖g‖ * ‖f - f'‖ := by positivity
    have hsum :
        |(Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
          (Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f')
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖)| ≤
          (n : ℝ) * (4 * ‖g‖ * ‖f - f'‖) := by
      calc
        |(Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
          (Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f')
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖)| =
            |Finset.sum (Finset.range n) fun i ↦
              (‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f')
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖)| := by
          rw [Finset.sum_sub_distrib]
        _ ≤ Finset.sum (Finset.range n) fun i ↦
              |‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f')
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖| := by
          simpa [Real.norm_eq_abs] using
            (norm_sum_le (Finset.range n) fun i ↦
              (‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f')
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖))
        _ ≤ Finset.sum (Finset.range n) fun _ ↦ 4 * ‖g‖ * ‖f - f'‖ := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hterm :
              |‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f')
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖| ≤
                4 * ‖g‖ * ‖f - f'‖ := by
            calc
              |‖inner ℂ (centeredL2 P f)
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                  ‖inner ℂ (centeredL2 P f')
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖| ≤
                  ‖inner ℂ (centeredL2 P f)
                      (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g)) -
                    inner ℂ (centeredL2 P f')
                      (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ := by
                exact abs_norm_sub_norm_le _ _
              _ = ‖inner ℂ (centeredL2 P f - centeredL2 P f')
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ := by
                rw [inner_sub_left]
              _ = ‖inner ℂ (centeredL2 P (f - f'))
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ := by
                rw [hsub]
              _ ≤ ‖centeredL2 P (f - f')‖ *
                    ‖Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g)‖ := by
                exact norm_inner_le_norm _ _
              _ = ‖centeredL2 P (f - f')‖ * ‖centeredL2 P g‖ := by
                rw [Lp.norm_compMeasurePreserving _ (hτ.iterate i)]
              _ ≤ (2 * ‖f - f'‖) * (2 * ‖g‖) := by
                gcongr
                · exact norm_centeredL2_le_two P (f - f')
                · exact norm_centeredL2_le_two P g
              _ = 4 * ‖g‖ * ‖f - f'‖ := by ring
          exact hterm
        _ = (n : ℝ) * (4 * ‖g‖ * ‖f - f'‖) := by
          simp [mul_comm, mul_left_comm, mul_assoc]
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have hrew :
        centeredCorrelationCesaro P hτ f g n - centeredCorrelationCesaro P hτ f' g n =
          (1 / (n : ℝ)) *
            ((Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
              (Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f')
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖)) := by
      unfold centeredCorrelationCesaro
      ring
    calc
      |centeredCorrelationCesaro P hτ f g n - centeredCorrelationCesaro P hτ f' g n| =
          |(1 / (n : ℝ)) *
            ((Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
              (Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f')
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖))| := by
        rw [hrew]
      _ = (1 / (n : ℝ)) *
          |(Finset.sum (Finset.range n) fun i ↦
              ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
            (Finset.sum (Finset.range n) fun i ↦
              ‖inner ℂ (centeredL2 P f')
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖)| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 / (n : ℝ)) * ((n : ℝ) * (4 * ‖g‖ * ‖f - f'‖)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * ‖g‖ * ‖f - f'‖ := by
        field_simp [hn0]

/-- Helper for Exercise 20.5.1: the centered Cesàro averages vary Lipschitz-continuously in the
right `L²` input. -/
lemma centeredCorrelationCesaro_rightDiff_le
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (f g g' : Lp ℂ 2 P) (n : ℕ) :
    |centeredCorrelationCesaro P hτ f g n - centeredCorrelationCesaro P hτ f g' n| ≤
      4 * ‖f‖ * ‖g - g'‖ := by
  by_cases hn : n = 0
  · subst hn
    simp [centeredCorrelationCesaro]
    positivity
  · have hsub :
        centeredL2 P g - centeredL2 P g' = centeredL2 P (g - g') := by
      rw [← centeredL2_sub]
    have hconst_nonneg : 0 ≤ 4 * ‖f‖ * ‖g - g'‖ := by positivity
    have hsum :
        |(Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
          (Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖)| ≤
          (n : ℝ) * (4 * ‖f‖ * ‖g - g'‖) := by
      calc
        |(Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
          (Finset.sum (Finset.range n) fun i ↦
            ‖inner ℂ (centeredL2 P f)
              (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖)| =
            |Finset.sum (Finset.range n) fun i ↦
              (‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖)| := by
          rw [Finset.sum_sub_distrib]
        _ ≤ Finset.sum (Finset.range n) fun i ↦
              |‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖| := by
          simpa [Real.norm_eq_abs] using
            (norm_sum_le (Finset.range n) fun i ↦
              (‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖))
        _ ≤ Finset.sum (Finset.range n) fun _ ↦ 4 * ‖f‖ * ‖g - g'‖ := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hterm :
              |‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖| ≤
                4 * ‖f‖ * ‖g - g'‖ := by
            calc
              |‖inner ℂ (centeredL2 P f)
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖ -
                  ‖inner ℂ (centeredL2 P f)
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖| ≤
                  ‖inner ℂ (centeredL2 P f)
                      (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g)) -
                    inner ℂ (centeredL2 P f)
                      (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖ := by
                exact abs_norm_sub_norm_le _ _
              _ = ‖inner ℂ (centeredL2 P f)
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g) -
                      Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖ := by
                rw [inner_sub_right]
              _ = ‖inner ℂ (centeredL2 P f)
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P (g - g')))‖ := by
                rw [← map_sub, hsub]
              _ ≤ ‖centeredL2 P f‖ *
                    ‖Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P (g - g'))‖ := by
                exact norm_inner_le_norm _ _
              _ = ‖centeredL2 P f‖ * ‖centeredL2 P (g - g')‖ := by
                rw [Lp.norm_compMeasurePreserving _ (hτ.iterate i)]
              _ ≤ (2 * ‖f‖) * (2 * ‖g - g'‖) := by
                gcongr
                · exact norm_centeredL2_le_two P f
                · exact norm_centeredL2_le_two P (g - g')
              _ = 4 * ‖f‖ * ‖g - g'‖ := by ring
          exact hterm
        _ = (n : ℝ) * (4 * ‖f‖ * ‖g - g'‖) := by
          simp [mul_comm, mul_left_comm, mul_assoc]
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have hrew :
        centeredCorrelationCesaro P hτ f g n - centeredCorrelationCesaro P hτ f g' n =
          (1 / (n : ℝ)) *
            ((Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
              (Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖)) := by
      unfold centeredCorrelationCesaro
      ring
    calc
      |centeredCorrelationCesaro P hτ f g n - centeredCorrelationCesaro P hτ f g' n| =
          |(1 / (n : ℝ)) *
            ((Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
              (Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ (centeredL2 P f)
                  (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖))| := by
        rw [hrew]
      _ = (1 / (n : ℝ)) *
          |(Finset.sum (Finset.range n) fun i ↦
              ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g))‖) -
            (Finset.sum (Finset.range n) fun i ↦
              ‖inner ℂ (centeredL2 P f)
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 P g'))‖)| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (1 / (n : ℝ)) * ((n : ℝ) * (4 * ‖f‖ * ‖g - g'‖)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * ‖f‖ * ‖g - g'‖ := by
        field_simp [hn0]

/-- Helper for Exercise 20.5.1: weak mixing forces centered Cesàro decay for every pair of simple
`L²` observables. -/
lemma simpleFuncCenteredCorrelationCesaro_tendsto_zero_of_isWeaklyMixing
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (hweak : IsWeaklyMixing τ P) :
    ∀ s t : Lp.simpleFunc ℂ 2 P,
      Tendsto (fun n ↦ centeredCorrelationCesaro P hτ (s : Lp ℂ 2 P) (t : Lp ℂ 2 P) n)
        Filter.atTop (nhds 0) := by
  classical
  intro s
  refine Lp.simpleFunc.induction (α := Ω) (E := ℂ) (p := (2 : ENNReal)) (μ := P)
    (by norm_num) (by norm_num) ?_ ?_ s
  · intro c A hA hμA t
    refine Lp.simpleFunc.induction (α := Ω) (E := ℂ) (p := (2 : ENNReal)) (μ := P)
      (by norm_num) (by norm_num) ?_ ?_ t
    · intro d B hB hμB
      -- Proof comment: the indicator-indicator base case is exactly weak mixing after factoring
      -- out the scalar coefficients.
      have hscale :
          (fun n : ℕ ↦
            centeredCorrelationCesaro P hτ
              ((Lp.simpleFunc.indicatorConst (p := (2 : ENNReal)) hA hμA.ne c : Lp.simpleFunc ℂ 2 P) :
                Lp ℂ 2 P)
              ((Lp.simpleFunc.indicatorConst (p := (2 : ENNReal)) hB hμB.ne d : Lp.simpleFunc ℂ 2 P) :
                Lp ℂ 2 P)
              n) =
            fun n : ℕ ↦
              (‖c‖ * ‖d‖) *
                ((1 / (n : ℝ)) *
                  (Finset.sum (Finset.range n) fun i ↦
                    |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|)) := by
        funext n
        rw [centeredCorrelationCesaro]
        calc
          (1 / (n : ℝ)) *
              (Finset.sum (Finset.range n) fun i ↦
                ‖inner ℂ
                    (centeredL2 P (indicatorConstLp 2 hA (measure_ne_top P A) c))
                    (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i)
                      (centeredL2 P (indicatorConstLp 2 hB (measure_ne_top P B) d)))‖) =
              (1 / (n : ℝ)) *
                (Finset.sum (Finset.range n) fun i ↦
                  ‖c‖ * ‖d‖ *
                    |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|) := by
            refine congrArg (fun x : ℝ => (1 / (n : ℝ)) * x) ?_
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [centeredIndicatorConstCorrelation_eq_smul_correlationError
              (P := P) (hτ := hτ) hA hB c d i]
          _ = (‖c‖ * ‖d‖) *
                ((1 / (n : ℝ)) *
                  (Finset.sum (Finset.range n) fun i ↦
                    |P.real (A ∩ (τ^[i]) ⁻¹' B) - P.real A * P.real B|)) := by
            rw [← Finset.mul_sum]
            ring
      rw [hscale]
      simpa using (hweak A B hA hB).const_mul (‖c‖ * ‖d‖)
    · intro f g hf hg hdisj ihf ihg
      -- Proof comment: expand the right input as a sum and squeeze the average between two
      -- already-vanishing simple-function averages.
      refine squeeze_zero
        (fun n ↦ centeredCorrelationCesaro_nonneg P hτ
          ((Lp.simpleFunc.indicatorConst (p := (2 : ENNReal)) hA hμA.ne c : Lp.simpleFunc ℂ 2 P) :
            Lp ℂ 2 P)
          ((Lp.simpleFunc.toLp f hf + Lp.simpleFunc.toLp g hg : Lp ℂ 2 P)) n)
        ?_ (by simpa using (ihf.add ihg))
      intro n
      simpa using centeredCorrelationCesaro_add_right_le P hτ
        ((Lp.simpleFunc.indicatorConst (p := (2 : ENNReal)) hA hμA.ne c : Lp.simpleFunc ℂ 2 P) :
          Lp ℂ 2 P)
        (Lp.simpleFunc.toLp f hf) (Lp.simpleFunc.toLp g hg) n
  · intro f g hf hg hdisj ihf ihg t
    -- Proof comment: the same triangle-inequality squeeze handles sums in the left input.
    refine squeeze_zero
      (fun n ↦ centeredCorrelationCesaro_nonneg P hτ
        ((Lp.simpleFunc.toLp f hf + Lp.simpleFunc.toLp g hg : Lp ℂ 2 P))
        (t : Lp ℂ 2 P) n)
      ?_ (by simpa using ((ihf t).add (ihg t)))
    intro n
    simpa using centeredCorrelationCesaro_add_left_le P hτ
      (Lp.simpleFunc.toLp f hf) (Lp.simpleFunc.toLp g hg) (t : Lp ℂ 2 P) n

/-- Helper for Exercise 20.5.1: the first Fourier mode is an eigenfunction for iterates of the
rotation by `π` on `UnitAddCircle`. -/
lemma fourierOneIterate_add_pi (n : ℕ) (x : UnitAddCircle) :
    fourier 1 (((· + (Real.pi : UnitAddCircle)))^[n] x) =
      (fourier 1 (Real.pi : UnitAddCircle)) ^ n * fourier 1 x := by
  induction n with
  | zero =>
      -- The zeroth iterate contributes no rotation factor.
      simp
  | succ n ih =>
      -- One more iterate adds another copy of the rotation eigenvalue.
      rw [Function.iterate_succ_apply', fourier_one, AddCircle.toCircle_add]
      simp only [Circle.coe_mul]
      rw [← fourier_one, ← fourier_one, ih]
      simp [pow_succ, mul_left_comm, mul_comm]

/-- Helper for Exercise 20.5.1: the first Fourier mode has Haar mean `0` on `UnitAddCircle`. -/
lemma fourierOne_mean_zero :
    ∫ x : UnitAddCircle, fourier 1 x ∂AddCircle.haarAddCircle = 0 := by
  -- Read off the zeroth Fourier coefficient of the first Fourier mode.
  have hcoeff :=
    congrArg (fun g : ℤ → ℂ => g 0) (fourierCoeff_fourier (T := (1 : ℝ)) 1)
  simpa [fourierCoeff, fourier_zero] using hcoeff

/-- Helper for Exercise 20.5.1: the first Fourier mode keeps unit-magnitude self-correlation under
iterates of rotation by `π`. -/
lemma fourierOneSelfCorrelation_norm_eq_one (n : ℕ) :
    ‖∫ x : UnitAddCircle,
        starRingEnd ℂ (fourier 1 x) * fourier 1 (((· + (Real.pi : UnitAddCircle)))^[n] x)
          ∂AddCircle.haarAddCircle‖ = 1 := by
  have hpoint :
      (fun x : UnitAddCircle ↦
        starRingEnd ℂ (fourier 1 x) * fourier 1 (((· + (Real.pi : UnitAddCircle)))^[n] x)) =
      fun _ : UnitAddCircle ↦ (fourier 1 (Real.pi : UnitAddCircle)) ^ n := by
    funext x
    -- Collapse the shifted Fourier term using the eigenfunction identity, then cancel the phase.
    rw [fourierOneIterate_add_pi n x]
    calc
      starRingEnd ℂ (fourier 1 x) * ((fourier 1 (Real.pi : UnitAddCircle)) ^ n * fourier 1 x) =
          (fourier 1 (Real.pi : UnitAddCircle)) ^ n *
            (starRingEnd ℂ (fourier 1 x) * fourier 1 x) := by
        ring
      _ =
          (fourier 1 (Real.pi : UnitAddCircle)) ^ n * (fourier (-1) x * fourier 1 x) := by
        rw [fourier_neg]
      _ = (fourier 1 (Real.pi : UnitAddCircle)) ^ n * fourier 0 x := by
        congr 1
        simpa using (fourier_add (m := -1) (n := 1) (x := x)).symm
      _ = (fourier 1 (Real.pi : UnitAddCircle)) ^ n := by
        simp
  -- The correlation sequence is pointwise constant in `x`, so its integral keeps modulus `1`.
  rw [hpoint]
  have hnorm : ‖fourier 1 (Real.pi : UnitAddCircle)‖ = 1 := by
    simp
  have hreal : (AddCircle.haarAddCircle : Measure UnitAddCircle).real Set.univ = 1 := by
    simp [Measure.real]
  rw [integral_const, norm_smul, Real.norm_eq_abs]
  rw [hreal, abs_of_nonneg zero_le_one, one_mul]
  rw [norm_pow, hnorm, one_pow]

/-- Helper for Exercise 20.5.1: weak mixing would force the Cesàro averages of the first Fourier
self-correlations for the rotation by `π` to converge to `0`. -/
lemma fourierOneSelfCorrelationCesaro_tendsto_zero_of_isWeaklyMixing
    (hweak : IsWeaklyMixing ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle) :
    Tendsto
      (fun n : ℕ ↦
        (1 / (n : ℝ)) *
          (Finset.sum (Finset.range n) fun i ↦
            ‖∫ x : UnitAddCircle,
                starRingEnd ℂ (fourier 1 x) *
                  fourier 1 (((· + (Real.pi : UnitAddCircle)))^[i] x)
                ∂AddCircle.haarAddCircle‖))
      Filter.atTop
      (nhds 0) := by
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let τ : UnitAddCircle → UnitAddCircle := (· + (Real.pi : UnitAddCircle))
  let F : Lp ℂ 2 μ := fourierLp (T := (1 : ℝ)) 2 1
  let raw : ℕ → ℝ := fun n ↦
    (1 / (n : ℝ)) *
      (Finset.sum (Finset.range n) fun i ↦
        ‖∫ x : UnitAddCircle,
            starRingEnd ℂ (fourier 1 x) * fourier 1 ((τ^[i]) x)
            ∂μ‖)
  have hτ : MeasurePreserving τ μ μ := by
    simpa [τ, μ] using measurePreserving_add_right μ (Real.pi : UnitAddCircle)
  have hFae : (F : UnitAddCircle → ℂ) =ᵐ[μ] (fourier 1 : UnitAddCircle → ℂ) := by
    -- Proof comment: keep the coercions bundled at the function level so pullbacks along
    -- iterates can use the quasi-measure-preserving `ae_eq_comp` API directly.
    simpa [F, μ] using (coeFn_fourierLp (T := (1 : ℝ)) 2 1)
  have hFmeanZero : ∫ x : UnitAddCircle, F x ∂μ = 0 := by
    -- Proof comment: the `Lp` Fourier mode is almost everywhere the same as the continuous
    -- Fourier character, whose Haar mean already vanishes.
    calc
      ∫ x : UnitAddCircle, F x ∂μ = ∫ x : UnitAddCircle, fourier 1 x ∂μ := by
        exact integral_congr_ae hFae
      _ = 0 := by simpa [μ] using fourierOne_mean_zero
  have hcenterF : centeredL2 μ F = F := by
    -- Proof comment: the first Fourier mode is already mean zero, so centering does nothing.
    simp [centeredL2, hFmeanZero]
  have hnormF : ‖F‖ = 1 := by
    -- Proof comment: the Fourier modes form an orthonormal family in `L²`.
    simpa [F] using (orthonormal_fourier (T := (1 : ℝ))).1 (1 : ℤ)
  let φ : ℕ → Lp.simpleFunc ℂ 2 μ := fun n ↦
    Lp.simpleFunc.toLp
      (MeasureTheory.SimpleFunc.approxOn F (Lp.stronglyMeasurable F).measurable
        (Set.range F ∪ {0}) 0 (by simp) n)
      (MeasureTheory.SimpleFunc.memLp_approxOn_range
        (Lp.stronglyMeasurable F).measurable (Lp.memLp F) n)
  haveI : TopologicalSpace.SeparableSpace (Set.range F ∪ {0} : Set ℂ) :=
    (Lp.stronglyMeasurable F).separableSpace_range_union_singleton
  have hφ_tendsto :
      Tendsto (fun n ↦ ((φ n : Lp.simpleFunc ℂ 2 μ) : Lp ℂ 2 μ)) atTop (nhds F) := by
    -- Proof comment: approximate the Fourier mode in `L²` by the canonical simple-function
    -- approximants coming from `SimpleFunc.approxOn`.
    simpa [φ] using
      (MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp
        (p := (2 : ENNReal)) (μ := μ) (hp_ne_top := by norm_num)
        (Lp.stronglyMeasurable F).measurable (Lp.memLp F))
  have hraw_eq :
      raw = fun n ↦ centeredCorrelationCesaro μ hτ F F n := by
    -- Proof comment: once the first Fourier mode is identified with its `Lp` realization and
    -- centering is removed, the raw correlation average is exactly `centeredCorrelationCesaro`.
    funext n
    dsimp [raw, centeredCorrelationCesaro]
    refine congrArg (fun x : ℝ ↦ (1 / (n : ℝ)) * x) ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hCompFourier' :
        ((F : UnitAddCircle → ℂ) ∘ (τ^[i])) =ᵐ[μ]
          ((fourier 1 : UnitAddCircle → ℂ) ∘ (τ^[i])) := by
      exact (hτ.iterate i).quasiMeasurePreserving.ae_eq_comp hFae
    have hComp :
        ((Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) F : Lp ℂ 2 μ) :
            UnitAddCircle → ℂ) =ᵐ[μ]
          ((fourier 1 : UnitAddCircle → ℂ) ∘ (τ^[i])) := by
      exact (Lp.coeFn_compMeasurePreserving F (hτ.iterate i)).trans hCompFourier'
    have hcenterComp :
        Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 μ F) =
          Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) F := by
      -- Proof comment: the iterate sees the same `L²` vector because the Fourier mode is
      -- already centered.
      simpa [hcenterF]
    calc
      ‖∫ x : UnitAddCircle,
          starRingEnd ℂ (fourier 1 x) * fourier 1 ((τ^[i]) x) ∂μ‖ =
          ‖∫ x : UnitAddCircle,
              starRingEnd ℂ (F x) *
                (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) F) x ∂μ‖ := by
        refine congrArg norm ?_
        refine integral_congr_ae ?_
        filter_upwards [hFae, hComp] with x hxF hxComp
        have hxComp' :
            ((Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) F : Lp ℂ 2 μ) : UnitAddCircle → ℂ) x =
              fourier 1 ((τ^[i]) x) := by
          simpa [Function.comp] using hxComp
        rw [← hxF, ← hxComp']
      _ = ‖inner ℂ F (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) F)‖ := by
        congr 1
        simpa only [RCLike.inner_apply'] using
          (MeasureTheory.L2.inner_def (𝕜 := ℂ) F
            (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) F)).symm
      _ = ‖inner ℂ (centeredL2 μ F)
            (Lp.compMeasurePreserving (τ^[i]) (hτ.iterate i) (centeredL2 μ F))‖ := by
        simpa [hcenterF, hcenterComp]
  have hcorr :
      Tendsto (fun n ↦ centeredCorrelationCesaro μ hτ F F n) Filter.atTop (nhds 0) := by
    -- Proof comment: choose one simple approximation to the Fourier mode, transfer weak-mixing
    -- decay to that simple observable, and control the remaining error with the Lipschitz bounds.
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    let δ : ℝ := min 1 (ε / 24)
    have hδ_pos : 0 < δ := by
      positivity
    obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 hφ_tendsto) δ hδ_pos
    let s : Lp.simpleFunc ℂ 2 μ := φ k
    let sLp : Lp ℂ 2 μ := (s : Lp ℂ 2 μ)
    have hs_dist : dist sLp F < δ := by
      simpa [s, sLp] using hk k le_rfl
    have hs_close' : ‖sLp - F‖ < δ := by
      simpa [dist_eq_norm] using hs_dist
    have hs_close : ‖F - sLp‖ < δ := by
      rw [norm_sub_rev]
      exact hs_close'
    have hs_norm : ‖sLp‖ ≤ 2 := by
      -- Proof comment: the chosen simple approximant sits within distance `δ ≤ 1` of the unit
      -- Fourier mode, so its norm is uniformly bounded by `2`.
      calc
        ‖sLp‖ = ‖(sLp - F) + F‖ := by rw [sub_add_cancel]
        _ ≤ ‖sLp - F‖ + ‖F‖ := norm_add_le _ _
        _ ≤ δ + ‖F‖ := by
          exact add_le_add (le_of_lt hs_close') le_rfl
        _ ≤ δ + 1 := by
          gcongr
          simpa [hnormF]
        _ ≤ 2 := by
          have hδ_le : δ ≤ 1 := min_le_left _ _
          nlinarith
    have hs_tendsto :
        Tendsto
          (fun n ↦ centeredCorrelationCesaro μ hτ sLp sLp n)
          Filter.atTop
          (nhds 0) := by
      -- Proof comment: the simple-function decay theorem applies directly to the chosen
      -- approximant.
      change Tendsto
        (fun n ↦ centeredCorrelationCesaro μ hτ
          ((s : Lp.simpleFunc ℂ 2 μ) : Lp ℂ 2 μ)
          ((s : Lp.simpleFunc ℂ 2 μ) : Lp ℂ 2 μ) n)
        Filter.atTop (nhds 0)
      exact simpleFuncCenteredCorrelationCesaro_tendsto_zero_of_isWeaklyMixing μ hτ hweak s s
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hs_tendsto) (ε / 2) (by positivity)
    refine ⟨N, ?_⟩
    intro n hn
    have hs_small : centeredCorrelationCesaro μ hτ sLp sLp n < ε / 2 := by
      have hs_dist := hN n hn
      simpa [Real.dist_eq, abs_of_nonneg (centeredCorrelationCesaro_nonneg μ hτ _ _ n)] using hs_dist
    have hleft :
        |centeredCorrelationCesaro μ hτ F F n -
            centeredCorrelationCesaro μ hτ F sLp n| ≤
          4 * ‖F‖ * ‖F - sLp‖ := by
      exact centeredCorrelationCesaro_rightDiff_le μ hτ F F sLp n
    have hright :
        |centeredCorrelationCesaro μ hτ F sLp n -
            centeredCorrelationCesaro μ hτ sLp sLp n| ≤
          4 * ‖sLp‖ * ‖F - sLp‖ := by
      exact centeredCorrelationCesaro_leftDiff_le μ hτ F sLp sLp n
    have happrox_small :
        |centeredCorrelationCesaro μ hτ F F n -
            centeredCorrelationCesaro μ hτ sLp sLp n| <
          ε / 2 := by
      have hbound :
          4 * ‖F‖ * ‖F - sLp‖ + 4 * ‖sLp‖ * ‖F - sLp‖ ≤ 12 * ‖F - sLp‖ := by
        have hnorm_nonneg : 0 ≤ ‖F - sLp‖ := norm_nonneg _
        have hF_le : ‖F‖ ≤ 1 := by simpa [hnormF]
        nlinarith
      calc
        |centeredCorrelationCesaro μ hτ F F n -
            centeredCorrelationCesaro μ hτ sLp sLp n| =
            |(centeredCorrelationCesaro μ hτ F F n -
                centeredCorrelationCesaro μ hτ F sLp n) +
              (centeredCorrelationCesaro μ hτ F sLp n -
                centeredCorrelationCesaro μ hτ sLp sLp n)| := by
          ring
        _ ≤
            |centeredCorrelationCesaro μ hτ F F n -
                centeredCorrelationCesaro μ hτ F sLp n| +
              |centeredCorrelationCesaro μ hτ F sLp n -
                centeredCorrelationCesaro μ hτ sLp sLp n| := by
          simpa [Real.norm_eq_abs] using
            (norm_add_le
              (centeredCorrelationCesaro μ hτ F F n -
                centeredCorrelationCesaro μ hτ F sLp n)
              (centeredCorrelationCesaro μ hτ F sLp n -
                centeredCorrelationCesaro μ hτ sLp sLp n))
        _ ≤
            4 * ‖F‖ * ‖F - sLp‖ + 4 * ‖sLp‖ * ‖F - sLp‖ := by
          exact add_le_add hleft hright
        _ ≤ 12 * ‖F - sLp‖ := hbound
        _ < 12 * δ := by
          nlinarith
        _ ≤ ε / 2 := by
          have hδ_le : δ ≤ ε / 24 := min_le_right _ _
          nlinarith
    have hfinal :
        centeredCorrelationCesaro μ hτ F F n < ε := by
      have hnonneg : 0 ≤ centeredCorrelationCesaro μ hτ F F n :=
        centeredCorrelationCesaro_nonneg μ hτ F F n
      have hs_nonneg : 0 ≤ centeredCorrelationCesaro μ hτ sLp sLp n :=
        centeredCorrelationCesaro_nonneg μ hτ _ _ n
      calc
        centeredCorrelationCesaro μ hτ F F n =
            |centeredCorrelationCesaro μ hτ F F n| := by
          rw [abs_of_nonneg hnonneg]
        _ = |(centeredCorrelationCesaro μ hτ F F n -
              centeredCorrelationCesaro μ hτ sLp sLp n) +
            centeredCorrelationCesaro μ hτ sLp sLp n| := by
          congr
          ring
        _ ≤ |centeredCorrelationCesaro μ hτ F F n -
              centeredCorrelationCesaro μ hτ sLp sLp n| +
            |centeredCorrelationCesaro μ hτ sLp sLp n| := by
          simpa [Real.norm_eq_abs] using
            (norm_add_le
              (centeredCorrelationCesaro μ hτ F F n -
                centeredCorrelationCesaro μ hτ sLp sLp n)
              (centeredCorrelationCesaro μ hτ sLp sLp n))
        _ = |centeredCorrelationCesaro μ hτ F F n -
              centeredCorrelationCesaro μ hτ sLp sLp n| +
            centeredCorrelationCesaro μ hτ sLp sLp n := by
          rw [abs_of_nonneg hs_nonneg]
        _ < ε / 2 + ε / 2 := add_lt_add happrox_small hs_small
        _ = ε := by ring
    simpa [Real.dist_eq, abs_of_nonneg (centeredCorrelationCesaro_nonneg μ hτ F F n)] using hfinal
  have hraw_tendsto : Tendsto raw Filter.atTop (nhds 0) := by
    simpa [hraw_eq] using hcorr
  simpa [raw, μ, τ] using hraw_tendsto

-- Proof sketch: combine `mod_one_rotation_ergodic_iff_irrational` with `irrational_pi`,
-- then transport the result from `volume` to `AddCircle.haarAddCircle`. The measure-preserving
-- part is already contained in `Ergodic`. Nontrivial Fourier characters on the additive circle
-- give eigenfunctions for the rotation, so the system is not weakly mixing.
/-- Exercise 20.5.1 (3-5): rotation by `π` on `AddCircle 1` with Haar probability measure is an
ergodic but not weakly mixing dynamical system. -/
theorem rotation_by_pi_ergodic_not_weaklyMixing :
    Ergodic ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle ∧
      ¬ IsWeaklyMixing ((· + (Real.pi : UnitAddCircle))) AddCircle.haarAddCircle := by
  constructor
  · simpa [AddCircle.volume_eq_smul_haarAddCircle] using
      ((mod_one_rotation_ergodic_iff_irrational Real.pi).2 irrational_pi)
  · intro hweak
    have hzero := fourierOneSelfCorrelationCesaro_tendsto_zero_of_isWeaklyMixing hweak
    have hconst :
        Tendsto
          (fun n : ℕ ↦
            (1 / (n : ℝ)) *
              (Finset.sum (Finset.range n) fun i ↦
                ‖∫ x : UnitAddCircle,
                    starRingEnd ℂ (fourier 1 x) *
                      fourier 1 (((· + (Real.pi : UnitAddCircle)))^[i] x)
                    ∂AddCircle.haarAddCircle‖))
          Filter.atTop
          (nhds 1) := by
      -- Proof comment: after the initial term, every summand is exactly `1`.
      refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hn
      have hsum :
          Finset.sum (Finset.range n) (fun i ↦
            ‖∫ x : UnitAddCircle,
                starRingEnd ℂ (fourier 1 x) *
                  fourier 1 (((· + (Real.pi : UnitAddCircle)))^[i] x)
                ∂AddCircle.haarAddCircle‖) =
            Finset.sum (Finset.range n) (fun _ ↦ (1 : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using fourierOneSelfCorrelation_norm_eq_one i
      rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hn0]
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hconst hzero
    norm_num at this
