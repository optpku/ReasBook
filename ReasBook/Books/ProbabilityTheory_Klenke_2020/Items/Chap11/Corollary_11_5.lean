/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_7

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {μ : Measure Ω}
variable [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}

local notation "supermartingaleLimit" => fun ω ↦ -(ℱ.limitProcess (-X) μ ω)
local notation "nonnegativeSupermartingaleLimit" => fun ω ↦ max (supermartingaleLimit ω) 0

-- Corollary 11.5 is `source-facing`: it is the nonnegative-supermartingale dual of the previous
-- submartingale convergence result. Its `core/canonical` owner layer is still the chapter/mathlib
-- `limitProcess` API, and the only `bridge/view` needed here is passage to the submartingale
-- `-X`.
omit [IsFiniteMeasure μ] in
private theorem bddAbove_posPart_expectation_neg
    (hX_nonneg : 0 ≤ X) :
    BddAbove (Set.range fun n ↦ μ[fun ω ↦ ((-X n ω)⁺)]) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ∫ ω, ((-X n ω)⁺) ∂μ ≤ 0
  have hzero : (fun ω ↦ ((-X n ω)⁺)) =ᵐ[μ] (0 : Ω → ℝ) := .of_forall fun ω ↦ by
    show (X n ω)⁻ = 0
    exact negPart_eq_zero.2 (hX_nonneg n ω)
  rw [integral_congr_ae hzero]
  simp

private theorem nonnegative_supermartingale_limitProcess_bridge
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    StronglyMeasurable[⨆ n, ℱ n] supermartingaleLimit ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (supermartingaleLimit ω)) := by
  obtain ⟨_, hneg_tendsto⟩ :=
    submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      hX.neg (bddAbove_posPart_expectation_neg hX_nonneg)
  refine ⟨supermartingale_stronglyMeasurable_limitProcess, ?_⟩
  change ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (-(ℱ.limitProcess (-X) μ ω)))
  filter_upwards [hneg_tendsto] with ω hω
  simpa using hω.neg

private theorem nonnegative_supermartingale_limitProcess_nonneg_bridge
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    0 ≤ᵐ[μ] supermartingaleLimit := by
  exact (nonnegative_supermartingale_limitProcess_bridge hX hX_nonneg).2.mono fun ω hω ↦
    isClosed_Ici.mem_of_tendsto hω (Eventually.of_forall fun n ↦ hX_nonneg n ω)

private theorem ae_eq_nonnegative_supermartingale_limit
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    supermartingaleLimit =ᵐ[μ] nonnegativeSupermartingaleLimit := by
  filter_upwards [nonnegative_supermartingale_limitProcess_nonneg_bridge hX hX_nonneg] with ω hω
  change supermartingaleLimit ω = max (supermartingaleLimit ω) 0
  symm
  exact max_eq_left hω

private theorem nonnegative_supermartingale_limitProcess_expectation_le_bridge
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    μ[supermartingaleLimit] ≤ μ[X 0] := by
  have hlimit_int :
      Integrable supermartingaleLimit μ :=
    (submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      hX.neg (bddAbove_posPart_expectation_neg hX_nonneg)).1.neg
  have hlimit_nonneg : 0 ≤ᵐ[μ] supermartingaleLimit :=
    nonnegative_supermartingale_limitProcess_nonneg_bridge hX hX_nonneg
  have hlimit_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (supermartingaleLimit ω)) :=
    (nonnegative_supermartingale_limitProcess_bridge hX hX_nonneg).2
  have hfatou :
      ∫⁻ ω, ENNReal.ofReal (supermartingaleLimit ω) ∂μ ≤
        liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ) atTop := by
    have hliminf_eq :
        (fun ω ↦ liminf (fun n ↦ ENNReal.ofReal (X n ω)) atTop) =ᵐ[μ]
          fun ω ↦ ENNReal.ofReal (supermartingaleLimit ω) := by
      filter_upwards [hlimit_tendsto] with ω hω
      have hω' :
          Tendsto (fun n ↦ ENNReal.ofReal (X n ω)) atTop
            (𝓝 (ENNReal.ofReal (supermartingaleLimit ω))) :=
        (ENNReal.continuous_ofReal.tendsto (supermartingaleLimit ω)).comp hω
      simpa using hω'.liminf_eq
    calc
      ∫⁻ ω, ENNReal.ofReal (supermartingaleLimit ω) ∂μ =
          ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal (X n ω)) atTop ∂μ := by
            exact lintegral_congr_ae hliminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ) atTop := by
        refine lintegral_liminf_le ?_
        intro n
        have hXn_meas : Measurable (X n) := ((hX.stronglyMeasurable n).mono (ℱ.le n)).measurable
        exact hXn_meas.ennreal_ofReal
  have hμX0_nonneg : 0 ≤ μ[X 0] :=
    integral_nonneg_of_ae (.of_forall fun ω ↦ hX_nonneg 0 ω)
  have hfatou' :
      ENNReal.ofReal (μ[supermartingaleLimit]) ≤
        liminf (fun n ↦ ENNReal.ofReal (μ[X n])) atTop := by
    calc
      ENNReal.ofReal (μ[supermartingaleLimit]) =
          ∫⁻ ω, ENNReal.ofReal (supermartingaleLimit ω) ∂μ := by
            simpa using ofReal_integral_eq_lintegral_ofReal hlimit_int hlimit_nonneg
      _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ) atTop := hfatou
      _ = liminf (fun n ↦ ENNReal.ofReal (μ[X n])) atTop := by
        congr 1
        funext n
        symm
        exact ofReal_integral_eq_lintegral_ofReal (hX.integrable n)
          (.of_forall fun ω ↦ hX_nonneg n ω)
  have hliminf_bound :
      liminf (fun n ↦ ENNReal.ofReal (μ[X n])) atTop ≤ ENNReal.ofReal (μ[X 0]) := by
    simpa using
      (Filter.liminf_le_liminf
        (Filter.Eventually.of_forall fun n ↦
          (ENNReal.ofReal_le_ofReal_iff hμX0_nonneg).2
            ((supermartingale_expectation_antitone hX) (Nat.zero_le n))) :
        liminf (fun n ↦ ENNReal.ofReal (μ[X n])) atTop ≤
          liminf (fun _ : ℕ ↦ ENNReal.ofReal (μ[X 0])) atTop)
  exact (ENNReal.ofReal_le_ofReal_iff hμX0_nonneg).1 (hfatou'.trans hliminf_bound)

-- Proof sketch: replace the canonical `limitProcess` representative by its pointwise truncation
-- `ω ↦ max (-(ℱ.limitProcess (-X) μ ω)) 0`; this changes the random variable only on a null set,
-- so measurability, expectation, and almost-sure convergence are preserved while pointwise
-- nonnegativity becomes literal.
/-- Corollary 11.5: a nonnegative real-valued discrete supermartingale admits a
`⨆ n, ℱ n`-measurable pointwise nonnegative almost-sure limit whose expectation is bounded by the
initial expectation. -/
theorem nonnegative_supermartingale_convergence
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    ∃ X_inf : Ω → ℝ, StronglyMeasurable[⨆ n, ℱ n] X_inf ∧ (∀ ω, 0 ≤ X_inf ω) ∧
      μ[X_inf] ≤ μ[X 0] ∧ ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (X_inf ω)) := by
  refine ⟨nonnegativeSupermartingaleLimit, ?_, ?_, ?_, ?_⟩
  · have hmeas : Measurable[⨆ n, ℱ n] supermartingaleLimit :=
      (nonnegative_supermartingale_limitProcess_bridge hX hX_nonneg).1.measurable
    have hzero : Measurable[⨆ n, ℱ n] fun _ : Ω ↦ (0 : ℝ) := measurable_const
    exact (hmeas.max hzero).stronglyMeasurable
  · intro ω
    change 0 ≤ max (supermartingaleLimit ω) 0
    exact le_max_right _ _
  · calc
      μ[nonnegativeSupermartingaleLimit] = μ[supermartingaleLimit] := by
        symm
        exact integral_congr_ae (ae_eq_nonnegative_supermartingale_limit hX hX_nonneg)
      _ ≤ μ[X 0] :=
        nonnegative_supermartingale_limitProcess_expectation_le_bridge hX hX_nonneg
  · filter_upwards [nonnegative_supermartingale_limitProcess_bridge hX hX_nonneg |>.2,
      nonnegative_supermartingale_limitProcess_nonneg_bridge hX hX_nonneg] with ω hω hω_nonneg
    change Tendsto (fun n ↦ X n ω) atTop (𝓝 (max (supermartingaleLimit ω) 0))
    have hω_nonneg' : (0 : ℝ) ≤ supermartingaleLimit ω := hω_nonneg
    rw [max_eq_left hω_nonneg']
    exact hω

-- Proof sketch: the source-facing corollary above is obtained from the canonical bridge below by
-- modifying the chosen representative on a null set. The bridge itself stays owner-shaped: it
-- records measurability and almost-sure convergence for the canonical `limitProcess` of `-X`.
/-- The canonical `limitProcess` representative of the almost-sure limit of a nonnegative
real-valued supermartingale is `⨆ n, ℱ n`-measurable, and the supermartingale converges to it
almost surely. -/
theorem nonnegative_supermartingale_limitProcess
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    StronglyMeasurable[⨆ n, ℱ n] supermartingaleLimit ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (supermartingaleLimit ω)) :=
  nonnegative_supermartingale_limitProcess_bridge hX hX_nonneg

-- Proof sketch: on the almost-everywhere set where `X n ω` converges to the canonical limit,
-- the limit of nonnegative real numbers is nonnegative. Since `limitProcess` is only a chosen
-- `⨆ n, ℱ n`-measurable representative of the almost-sure limit class, this yields almost-sure,
-- not pointwise, nonnegativity.
/-- The limit process of a nonnegative supermartingale is almost surely nonnegative. -/
theorem nonnegative_supermartingale_limitProcess_nonneg
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    0 ≤ᵐ[μ] supermartingaleLimit := by
  exact nonnegative_supermartingale_limitProcess_nonneg_bridge hX hX_nonneg

-- Proof sketch: apply Fatou's lemma to the nonnegative process `X`, use the almost-sure
-- convergence to the canonical supermartingale limit, and combine this with the supermartingale
-- monotonicity of expectations to compare with `μ[X 0]`.
/-- The expectation of the almost-sure limit of a nonnegative supermartingale is bounded by the
initial expectation. -/
theorem nonnegative_supermartingale_limitProcess_expectation_le
    (hX : Supermartingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    μ[supermartingaleLimit] ≤ μ[X 0] :=
  nonnegative_supermartingale_limitProcess_expectation_le_bridge hX hX_nonneg
