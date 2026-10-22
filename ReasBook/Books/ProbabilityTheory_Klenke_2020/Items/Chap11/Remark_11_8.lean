/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- Helper for Remark 11.8: extend a discrete filtration by adjoining
`ℱ∞ = ⨆ n, ℱ n` at time `∞`. -/
def withInfinityFiltration (ℱ : Filtration ℕ mΩ) : Filtration ℕ∞ mΩ where
  seq := ENat.recTopCoe (⨆ k, ℱ k) ℱ
  mono' := by
    intro i j hij
    -- Proof comment: split on whether `j` is finite or `∞`, and then reduce the remaining
    -- finite-finite branch to monotonicity of the original filtration.
    cases j using ENat.recTopCoe with
    | top =>
        cases i using ENat.recTopCoe with
        | top =>
            rfl
        | coe i =>
            exact le_iSup (fun k ↦ ℱ k) i
    | coe j =>
        cases i using ENat.recTopCoe with
        | top =>
            have : False := by
              simp at hij
            exact this.elim
        | coe i =>
            exact ℱ.mono (by simpa using hij)
  le' := by
    intro i
    -- Proof comment: the finite slices already lie below `mΩ`, and so does their supremum.
    cases i using ENat.recTopCoe with
    | top =>
        exact iSup_le fun n ↦ ℱ.le n
    | coe n =>
        exact ℱ.le n

variable {ℱ : Filtration ℕ mΩ} {μ : Measure Ω}

-- `ENat.recTopCoe` together with `withInfinityFiltration` is the bridge/view layer for
-- Remark 11.8. The source-facing statements below specialize the terminal value to the canonical
-- one already produced by Theorem 11.7.
/-- Helper for Remark 11.8: if a discrete-time process is strongly adapted to `ℱ` and its
terminal value is
`⨆ n, ℱ n`-strongly measurable, then adjoining that terminal value yields a process strongly
adapted to the filtration extended by `∞`. -/
private theorem withInfinityProcess_stronglyAdapted
    {E : Type v} [TopologicalSpace E] {X : ℕ → Ω → E} {Xinf : Ω → E}
    (hadp : StronglyAdapted ℱ X) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf) :
    StronglyAdapted (withInfinityFiltration ℱ)
      (show ℕ∞ → Ω → E from ENat.recTopCoe Xinf X) := by
  intro i
  -- Proof comment: at finite times this is the original adaptedness hypothesis, while the
  -- `∞`-slice is exactly the supplied terminal measurability.
  cases i using ENat.recTopCoe with
  | top =>
      simpa [withInfinityFiltration] using hXinfm
  | coe n =>
      simpa [withInfinityFiltration] using hadp n

/-- Helper for Remark 11.8: an `ℕ`-indexed process becomes a martingale on `ℕ∞` once its terminal
value has the correct conditional expectations at all finite times. -/
private theorem withInfinityProcess_martingale_of_ae_eq_condExp
    [IsFiniteMeasure μ]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : ℕ → Ω → E} {Xinf : Ω → E}
    (hadp : StronglyAdapted ℱ X) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf)
    (hXinfint : Integrable Xinf μ)
    (hcond : ∀ n : ℕ, μ[Xinf | ℱ n] =ᵐ[μ] X n) :
    Martingale
      (show ℕ∞ → Ω → E from ENat.recTopCoe Xinf X)
      (withInfinityFiltration ℱ) μ := by
  refine ⟨withInfinityProcess_stronglyAdapted hadp hXinfm, ?_⟩
  intro i j hij
  -- Proof comment: split the index comparison into finite-finite, finite-`∞`, and `∞`-`∞`
  -- cases; the tower property handles the finite-finite branch.
  cases i using ENat.recTopCoe with
  | top =>
      cases j using ENat.recTopCoe with
      | top =>
          simpa [withInfinityFiltration] using
            (Filter.EventuallyEq.of_eq
              (condExp_of_stronglyMeasurable
                ((withInfinityFiltration ℱ).le ⊤)
                (by simpa [withInfinityFiltration] using hXinfm)
                hXinfint))
      | coe j =>
          have : False := by
            simp at hij
          exact this.elim
  | coe i =>
      cases j using ENat.recTopCoe with
      | top =>
          simpa [withInfinityFiltration] using hcond i
      | coe j =>
          have hij' : i ≤ j := by
            simpa using hij
          -- Proof comment: rewrite `X j` using the terminal conditional expectation and then
          -- collapse the nested conditional expectations by the filtration tower property.
          simpa [withInfinityFiltration] using
            ((condExp_congr_ae (hcond j).symm).trans
              ((ℱ.condExp_condExp Xinf hij').trans (hcond i)))

/-- Helper for Remark 11.8: an `ℕ`-indexed submartingale extends to `ℕ∞` once the terminal value
dominates each finite slice through conditional expectation. -/
private theorem withInfinityProcess_submartingale_of_ae_le_condExp
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Xinf : Ω → ℝ}
    (hX : Submartingale X ℱ μ) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf)
    (hXinfint : Integrable Xinf μ)
    (hcond : ∀ n : ℕ, X n ≤ᵐ[μ] μ[Xinf | ℱ n]) :
    Submartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe Xinf X)
      (withInfinityFiltration ℱ) μ := by
  -- Route correction: the finite-finite inequalities must come from the finite-time
  -- submartingale structure, not from the terminal-value comparison alone.
  refine ⟨withInfinityProcess_stronglyAdapted hX.stronglyAdapted hXinfm, ?_, ?_⟩
  · intro i j hij
    -- Proof comment: finite-finite comes from `hX`, finite-`∞` is the hypothesis, and
    -- `∞`-`∞` is the self-conditioning identity at `ℱ∞`.
    cases i using ENat.recTopCoe with
    | top =>
        cases j using ENat.recTopCoe with
        | top =>
            simpa [withInfinityFiltration] using
              (Filter.EventuallyEq.of_eq
                (condExp_of_stronglyMeasurable
                  ((withInfinityFiltration ℱ).le ⊤)
                  (by simpa [withInfinityFiltration] using hXinfm)
                  hXinfint)).symm.le
        | coe j =>
            have : False := by
              simp at hij
            exact this.elim
    | coe i =>
        cases j using ENat.recTopCoe with
        | top =>
            simpa [withInfinityFiltration] using hcond i
        | coe j =>
            have hij' : i ≤ j := by
              simpa using hij
            simpa [withInfinityFiltration] using hX.ae_le_condExp hij'
  · intro i
    -- Proof comment: the finite slices stay integrable from the original submartingale, and the
    -- terminal slice uses the supplied integrability hypothesis.
    cases i using ENat.recTopCoe with
    | top =>
        simpa using hXinfint
    | coe n =>
        simpa using hX.integrable n

/-- Helper for Remark 11.8: an `ℕ`-indexed supermartingale extends to `ℕ∞` once the terminal
value is conditionally bounded above by each finite slice. -/
private theorem withInfinityProcess_supermartingale_of_ae_ge_condExp
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {Xinf : Ω → ℝ}
    (hX : Supermartingale X ℱ μ) (hXinfm : StronglyMeasurable[⨆ n, ℱ n] Xinf)
    (hXinfint : Integrable Xinf μ)
    (hcond : ∀ n : ℕ, μ[Xinf | ℱ n] ≤ᵐ[μ] X n) :
    Supermartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe Xinf X)
      (withInfinityFiltration ℱ) μ := by
  -- Route correction: the finite-finite inequalities must come from the finite-time
  -- supermartingale structure, not just from the finite-to-terminal bounds.
  refine ⟨withInfinityProcess_stronglyAdapted hX.stronglyAdapted hXinfm, ?_, ?_⟩
  · intro i j hij
    -- Proof comment: finite-finite comes from `hX`, finite-`∞` is the hypothesis, and
    -- `∞`-`∞` again follows from self-conditioning at the terminal sigma-algebra.
    cases i using ENat.recTopCoe with
    | top =>
        cases j using ENat.recTopCoe with
        | top =>
            simpa [withInfinityFiltration] using
              (Filter.EventuallyEq.of_eq
                (condExp_of_stronglyMeasurable
                  ((withInfinityFiltration ℱ).le ⊤)
                  (by simpa [withInfinityFiltration] using hXinfm)
                  hXinfint)).le
        | coe j =>
            have : False := by
              simp at hij
            exact this.elim
    | coe i =>
        cases j using ENat.recTopCoe with
        | top =>
            simpa [withInfinityFiltration] using hcond i
        | coe j =>
            have hij' : i ≤ j := by
              simpa using hij
            simpa [withInfinityFiltration] using hX.condExp_ae_le hij'
  · intro i
    -- Proof comment: integrability is inherited from the finite-time supermartingale and from
    -- the supplied terminal-value integrability.
    cases i using ENat.recTopCoe with
    | top =>
        simpa using hXinfint
    | coe n =>
        simpa using hX.integrable n

section Real

variable {X : ℕ → Ω → ℝ}
variable [IsFiniteMeasure μ]

local notation "supermartingaleLimit" => fun ω ↦ -(ℱ.limitProcess (-X) μ ω)

/-- Remark 11.8 for martingales: adjoining the canonical terminal random variable
`ℱ.limitProcess X μ` from Theorem 11.7 turns `(X n)ₙ` into a martingale on `ℕ∞` for the
filtration extended by `ℱ∞ = ⨆ n, ℱ n`. -/
theorem withInfinityProcess_martingale
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Martingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe (ℱ.limitProcess X μ) X)
      (withInfinityFiltration ℱ) μ := by
  simpa using withInfinityProcess_martingale_of_ae_eq_condExp
    hX.stronglyAdapted
    stronglyMeasurable_limitProcess
    (submartingale_integrable_limitProcess_of_uniformIntegrable hX.submartingale hUI)
    (fun n ↦ (hX.ae_eq_condExp_limitProcess hUI n).symm)

/-- Remark 11.8 for submartingales: adjoining the canonical terminal random variable
`ℱ.limitProcess X μ` from Theorem 11.7 turns `(X n)ₙ` into a submartingale on `ℕ∞` for the
filtration extended by `ℱ∞ = ⨆ n, ℱ n`. -/
theorem withInfinityProcess_submartingale
    (hX : Submartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Submartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe (ℱ.limitProcess X μ) X)
      (withInfinityFiltration ℱ) μ := by
  simpa using withInfinityProcess_submartingale_of_ae_le_condExp
    hX
    stronglyMeasurable_limitProcess
    (submartingale_integrable_limitProcess_of_uniformIntegrable hX hUI)
    (submartingale_ae_le_condExp_limitProcess_of_uniformIntegrable hX hUI)

/-- Remark 11.8 for supermartingales: adjoining the canonical terminal random variable
`ω ↦ -ℱ.limitProcess (-X) μ ω` from Theorem 11.7 turns `(X n)ₙ` into a supermartingale on `ℕ∞`
for the filtration extended by `ℱ∞ = ⨆ n, ℱ n`. -/
theorem withInfinityProcess_supermartingale
    (hX : Supermartingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Supermartingale
      (show ℕ∞ → Ω → ℝ from ENat.recTopCoe supermartingaleLimit X)
      (withInfinityFiltration ℱ) μ := by
  simpa using withInfinityProcess_supermartingale_of_ae_ge_condExp
    hX
    supermartingale_stronglyMeasurable_limitProcess
    (supermartingale_integrable_limitProcess_of_uniformIntegrable hX hUI)
    (supermartingale_ae_ge_condExp_limit_of_uniformIntegrable hX hUI)

end Real
