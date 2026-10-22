/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Corollary_8_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {τ : Ω → Ω} {X₀ : Ω → ℝ} {p : ℝ≥0∞}

section Lp

variable [Fact (1 ≤ p)]

local notation "ℐ" => MeasurableSpace.invariants τ

/- Theorem 20.16 is `source-facing`: it asserts `L^p(P)` convergence of Birkhoff averages. The
Chapter 7 owner abstraction for this notion is `TendstoInLp`, while raw `eLpNorm` convergence is
only the derived `bridge/view` supplied by `TendstoInLp.tendsto_eLpNorm`. The main public
statements therefore use `TendstoInLp`, and the seminorm formulations remain thin companions. -/

-- Proof sketch: combine the almost-sure convergence from Birkhoff's ergodic theorem with the
-- uniform integrability of the `p`th powers from Lemma 20.15, then apply the Vitali-type
-- `L¹` convergence criterion to the error sequence `|Aₙ - P[X₀ | MeasurableSpace.invariants τ]|^p`.
/-- Helper for Theorem 20.16: the orbit observable `X₀ ∘ τ^[n]` has the same law as `X₀` under
the probability measure `P`. -/
lemma orbitIterate_identDistrib
    (hτ : MeasurePreserving τ P P) (hX₀ : MemLp X₀ p P) :
    ∀ n, IdentDistrib (fun ω ↦ X₀ (τ^[n] ω)) X₀ P P := by
  intro n
  let μX : Measure ℝ := P.map X₀
  have hXlaw : HasLaw X₀ μX P := ⟨hX₀.aemeasurable, rfl⟩
  have hIterLaw : HasLaw (τ^[n]) P P := (MeasurePreserving.iterate hτ n).hasLaw
  -- Proof comment: both `X₀ ∘ τ^[n]` and `X₀` are pushforwards of the same law `μX`.
  simpa [μX, Function.comp] using HasLaw.identDistrib (hXlaw.comp hIterLaw) hXlaw

/-- Helper for Theorem 20.16: the Birkhoff averages form a uniformly `L^p`-integrable family. -/
lemma uniformIntegrable_birkhoffAverage
    (hp_top : p ≠ ∞) (hτ : MeasurePreserving τ P P) (hX₀ : MemLp X₀ p P) :
    UniformIntegrable (fun n ↦ birkhoffAverage ℝ τ X₀ n) p P := by
  let orbit : ℕ → Ω → ℝ := fun n ω ↦ X₀ (τ^[n] ω)
  have hOrbit0 : MemLp (orbit 0) p P := by
    simpa [orbit] using hX₀
  have hOrbitUI : UniformIntegrable orbit p P :=
    MemLp.uniformIntegrable_of_identDistrib
      (j := 0) Fact.out hp_top hOrbit0
      (orbitIterate_identDistrib (P := P) (τ := τ) (X₀ := X₀) hτ hX₀)
  -- Proof comment: `birkhoffAverage` is exactly the Cesàro average of the orbit sequence.
  convert (uniformIntegrable_average_real (μ := P) (p := p) Fact.out hOrbitUI) using 2 with n
  ext ω
  simp [orbit, birkhoffAverage, birkhoffSum, div_eq_inv_mul]

/-- Helper for Theorem 20.16: the almost-sure Birkhoff limit implies convergence in measure of the
averages to `P[X₀ | MeasurableSpace.invariants τ]`. -/
lemma tendstoInMeasure_birkhoffAverage_condExpInvariants
    (hp_top : p ≠ ∞) (hτ : MeasurePreserving τ P P) (hX₀ : MemLp X₀ p P) :
    TendstoInMeasure P (fun n ↦ birkhoffAverage ℝ τ X₀ n) atTop P[X₀ | ℐ] := by
  have hX₀_int : Integrable X₀ P :=
    memLp_one_iff_integrable.1 <| hX₀.mono_exponent Fact.out
  have hAvgUI := uniformIntegrable_birkhoffAverage (P := P) (τ := τ) (X₀ := X₀)
    (p := p) hp_top hτ hX₀
  -- Proof comment: finite-measure almost-sure convergence upgrades to convergence in measure.
  exact tendstoInMeasure_of_tendsto_ae
    (fun n ↦ hAvgUI.aestronglyMeasurable n)
    (birkhoffAverage_tendsto_ae_condExp_invariants (P := P) (τ := τ) (f := X₀) hτ hX₀_int)

/-- Theorem 20.16 (1): for a probability-preserving transformation `τ` and a real-valued
`L^p(P)` observable `X₀` with `1 ≤ p < ∞`, the Birkhoff averages of `X₀` along the orbit of `τ`
converge in `L^p(P)` to the conditional expectation of `X₀` onto the invariant σ-algebra
`MeasurableSpace.invariants τ`. -/
theorem birkhoffAverage_tendsto_condExp_invariants
    (hp_top : p ≠ ∞) (hτ : MeasurePreserving τ P P) (hX₀ : MemLp X₀ p P) :
    TendstoInLp p P (fun n ↦ birkhoffAverage ℝ τ X₀ n) P[X₀ | ℐ] := by
  have hAvgUI :=
    uniformIntegrable_birkhoffAverage (P := P) (τ := τ) (X₀ := X₀) (p := p) hp_top hτ hX₀
  have hCondMemLp : MemLp P[X₀ | ℐ] p P :=
    hX₀.condExp_of_one_le (MeasurableSpace.invariants_le τ)
  have hMeasure :
      TendstoInMeasure P (fun n ↦ birkhoffAverage ℝ τ X₀ n) atTop P[X₀ | ℐ] :=
    tendstoInMeasure_birkhoffAverage_condExpInvariants
      (P := P) (τ := τ) (X₀ := X₀) (p := p) hp_top hτ hX₀
  -- Proof comment: Vitali upgrades convergence in measure to `L^p` convergence on a probability
  -- space once the averages are uniformly `L^p`-integrable.
  refine (tendstoInLp_iff_tendsto_eLpNorm).2 ?_
  refine ⟨fun n ↦ hAvgUI.memLp n, hCondMemLp, ?_⟩
  exact tendsto_Lp_finite_of_tendstoInMeasure Fact.out hp_top
    (fun n ↦ (hAvgUI.aestronglyMeasurable n)) hCondMemLp hAvgUI.unifIntegrable hMeasure

/-- Bridge companion to Theorem 20.16 (1): the owner-level `L^p` convergence statement rewritten
as convergence of the corresponding `eLpNorm` errors. -/
theorem birkhoffAverage_tendsto_condExp_invariants_eLpNorm
    (hp_top : p ≠ ∞) (hτ : MeasurePreserving τ P P) (hX₀ : MemLp X₀ p P) :
    Tendsto
      (fun n ↦
        eLpNorm (birkhoffAverage ℝ τ X₀ n - P[X₀ | ℐ]) p P)
      atTop (𝓝 0) :=
  (birkhoffAverage_tendsto_condExp_invariants hp_top hτ hX₀).tendsto_eLpNorm

-- Proof sketch: apply the first part and use ergodicity to identify the conditional expectation
-- onto the invariant σ-algebra with the constant function equal to `P[X₀]`.
/-- Theorem 20.16 (2): if `τ` is ergodic, then the same Birkhoff averages converge in `L^p(P)`
to the constant expectation `P[X₀]`. -/
theorem birkhoffAverage_tendsto_expectation_of_ergodic
    (hp_top : p ≠ ∞) (hτ : Ergodic τ P) (hX₀ : MemLp X₀ p P) :
    TendstoInLp p P (fun n ↦ birkhoffAverage ℝ τ X₀ n) (fun _ ↦ P[X₀]) := by
  have hX₀_int : Integrable X₀ P :=
    memLp_one_iff_integrable.1 <| hX₀.mono_exponent Fact.out
  have hBase :=
    birkhoffAverage_tendsto_condExp_invariants
      (P := P) (τ := τ) (X₀ := X₀) (p := p) hp_top hτ.toMeasurePreserving hX₀
  have hCondEq :
      P[X₀ | ℐ] =ᵐ[P] fun _ ↦ P[X₀] :=
    condExpInvariantsAeEqExpectationOfErgodic (P := P) (τ := τ) (f := X₀) hτ hX₀_int
  rcases (tendstoInLp_iff_tendsto_eLpNorm).1 hBase with ⟨hAvgMemLp, hCondMemLp, hNorm⟩
  have hConstMemLp : MemLp (fun _ ↦ P[X₀]) p P := MemLp.ae_eq hCondEq hCondMemLp
  have hNorm' :
      Tendsto
        (fun n ↦ eLpNorm (birkhoffAverage ℝ τ X₀ n - fun _ ↦ P[X₀]) p P)
        atTop (𝓝 0) := by
    -- Proof comment: replace the conditional-expectation limit by the ergodic constant a.e.
    refine hNorm.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦
      eLpNorm_congr_ae (EventuallyEq.sub (EventuallyEq.rfl) hCondEq)
  -- Proof comment: package the rewritten `eLpNorm` convergence back into `TendstoInLp`.
  exact (tendstoInLp_iff_tendsto_eLpNorm).2 ⟨hAvgMemLp, hConstMemLp, hNorm'⟩

/-- Bridge companion to Theorem 20.16 (2): the owner-level `L^p` convergence statement rewritten
as convergence of the corresponding `eLpNorm` errors. -/
theorem birkhoffAverage_tendsto_expectation_of_ergodic_eLpNorm
    (hp_top : p ≠ ∞) (hτ : Ergodic τ P) (hX₀ : MemLp X₀ p P) :
    Tendsto
      (fun n ↦ eLpNorm (birkhoffAverage ℝ τ X₀ n - fun _ ↦ P[X₀]) p P)
      atTop (𝓝 0) :=
  (birkhoffAverage_tendsto_expectation_of_ergodic hp_top hτ hX₀).tendsto_eLpNorm

end Lp
