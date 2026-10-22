/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Helper for Theorem 15.56: the scalar projection `x ↦ ⟪t, x⟫` is almost everywhere measurable
for every probability law on `ℝ^d`. -/
lemma scalarProjectionAEMeasurable (μ : ProbabilityMeasure E) (t : E) :
    AEMeasurable (fun x : E ↦ inner ℝ t x) (μ : Measure E) :=
  aemeasurable_id.const_inner

/-- Helper for Theorem 15.56: the one-dimensional law obtained by projecting `μ` along `t`. -/
def scalarProjectionLaw (μ : ProbabilityMeasure E) (t : E) : ProbabilityMeasure ℝ :=
  μ.map (scalarProjectionAEMeasurable μ t)

/-- Helper for Theorem 15.56: weak convergence is preserved under scalar projection. -/
lemma tendsto_scalarProjectionLaw_of_tendsto
    {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hμ : Tendsto μs atTop (𝓝 μ)) (t : E) :
    Tendsto (fun n ↦ scalarProjectionLaw (μs n) t) atTop (𝓝 (scalarProjectionLaw μ t)) := by
  -- Proof comment: the scalar projection is continuous, so weak convergence pushes forward.
  have hcont : Continuous (fun x : E ↦ inner ℝ t x) := by
    fun_prop
  simpa [scalarProjectionLaw, scalarProjectionAEMeasurable] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hμ hcont

/-- Helper for Theorem 15.56: the characteristic function of a projected law agrees with the
ambient characteristic function along the line `ℝ • t`. -/
lemma charFun_scalarProjection_eq (μ : ProbabilityMeasure E) (t : E) (u : ℝ) :
    charFun (scalarProjectionLaw μ t : Measure ℝ) u = charFun (μ : Measure E) (u • t) := by
  -- Proof comment: use the characteristic-function API for pushforwards by continuous linear
  -- forms instead of unfolding the integral definition in place.
  rw [MeasureTheory.charFun_eq_charFunDual_toDualMap]
  simpa [scalarProjectionLaw, scalarProjectionAEMeasurable,
    MeasureTheory.charFun_eq_charFunDual_toDualMap,
    InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using
    (MeasureTheory.charFun_map_eq_charFunDual_smul
      (μ := (μ : Measure E)) (L := InnerProductSpace.toDualMap ℝ E t) u)

/-- Helper for Theorem 15.56: convergence of every projected law yields pointwise convergence of
the multivariate characteristic functions. -/
lemma tendsto_charFun_of_tendsto_all_scalarProjectionLaws
    {μs : ℕ → ProbabilityMeasure E} {ν : E → ProbabilityMeasure ℝ}
    (hν : ∀ t : E, Tendsto (fun n ↦ scalarProjectionLaw (μs n) t) atTop (𝓝 (ν t))) :
    ∀ t : E, Tendsto (fun n ↦ charFun (μs n) t) atTop (𝓝 (charFun (ν t : Measure ℝ) (1 : ℝ))) := by
  intro t
  -- Proof comment: evaluate the one-dimensional characteristic functions at `u = 1`.
  have hchar :
      Tendsto (fun n ↦ charFun (scalarProjectionLaw (μs n) t : Measure ℝ) (1 : ℝ)) atTop
        (𝓝 (charFun (ν t : Measure ℝ) (1 : ℝ))) :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 (hν t)) (1 : ℝ)
  simpa [charFun_scalarProjection_eq] using hchar

/-- Helper for Theorem 15.56: the axis restriction of the candidate limit agrees with the
characteristic function of the fixed axis law `ν (single i 1)`. -/
lemma scalarProjectionAxisLimit_eq_charFun
    {μs : ℕ → ProbabilityMeasure E} {ν : E → ProbabilityMeasure ℝ}
    (hν : ∀ t : E, Tendsto (fun n ↦ scalarProjectionLaw (μs n) t) atTop (𝓝 (ν t)))
    (i : Fin d) (s : ℝ) :
    charFun (ν (EuclideanSpace.single i s) : Measure ℝ) (1 : ℝ) =
      charFun (ν (EuclideanSpace.single i 1) : Measure ℝ) s := by
  -- Proof comment: compare the two limits of the same scalar sequence along the `i`th axis.
  have hleft :
      Tendsto (fun n ↦ charFun (μs n) (EuclideanSpace.single i s)) atTop
        (𝓝 (charFun (ν (EuclideanSpace.single i s) : Measure ℝ) (1 : ℝ))) :=
    tendsto_charFun_of_tendsto_all_scalarProjectionLaws hν (EuclideanSpace.single i s)
  have hrightChar :
      Tendsto
        (fun n ↦ charFun (scalarProjectionLaw (μs n) (EuclideanSpace.single i 1) : Measure ℝ) s)
        atTop
        (𝓝 (charFun (ν (EuclideanSpace.single i 1) : Measure ℝ) s)) :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 (hν (EuclideanSpace.single i 1))) s
  have hright :
      Tendsto (fun n ↦ charFun (μs n) (EuclideanSpace.single i s)) atTop
        (𝓝 (charFun (ν (EuclideanSpace.single i 1) : Measure ℝ) s)) := by
    have hsingle : s • EuclideanSpace.single i (1 : ℝ) = EuclideanSpace.single i s := by
      ext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [EuclideanSpace.single, hij]
    simpa [charFun_scalarProjection_eq, hsingle] using hrightChar
  exact tendsto_nhds_unique hleft hright

/-- Helper for Theorem 15.56: the projected characteristic-function limit is partially continuous
at the origin. -/
lemma scalarProjectionLimit_partiallyContinuousAtZero
    {μs : ℕ → ProbabilityMeasure E} {ν : E → ProbabilityMeasure ℝ}
    (hν : ∀ t : E, Tendsto (fun n ↦ scalarProjectionLaw (μs n) t) atTop (𝓝 (ν t))) :
    PartiallyContinuousAtZero (d := d) (fun t : E ↦ charFun (ν t : Measure ℝ) (1 : ℝ)) := by
  intro i
  -- Proof comment: on each axis, the candidate limit is the characteristic function of one fixed
  -- one-dimensional probability law.
  have haxis :
      (fun s : ℝ ↦ charFun (ν (EuclideanSpace.single i s) : Measure ℝ) (1 : ℝ)) =
        fun s : ℝ ↦ charFun (ν (EuclideanSpace.single i 1) : Measure ℝ) s := by
    funext s
    exact scalarProjectionAxisLimit_eq_charFun hν i s
  rw [haxis]
  simpa using
    (MeasureTheory.continuous_charFun
      (μ := (ν (EuclideanSpace.single i 1) : Measure ℝ))).continuousAt

/-- Theorem 15.56: Cramer--Wold device. A sequence of probability laws on `ℝ^d` converges weakly
if and only if every one-dimensional projected law along `x ↦ ⟪t, x⟫` converges weakly. -/
-- Proof sketch: for the forward implication, apply weak convergence to the continuous scalar
-- projection `x ↦ ⟪t, x⟫`. For the converse, use convergence of the projected characteristic
-- functions together with uniqueness of probability measures on `ℝ^d` from all one-dimensional
-- projections.
theorem tendsto_iff_all_scalarProjectionLaws_tendsto
    (μs : ℕ → ProbabilityMeasure E) :
    (∃ μ : ProbabilityMeasure E, Tendsto μs atTop (𝓝 μ)) ↔
      ∀ t : E, ∃ νt : ProbabilityMeasure ℝ,
        Tendsto
          (fun n ↦
            ((μs n).map
              (show AEMeasurable (fun x : E ↦ inner ℝ t x) (μs n : Measure E) from
                aemeasurable_id.const_inner) : ProbabilityMeasure ℝ))
          atTop (𝓝 νt) := by
  constructor
  · rintro ⟨μ, hμ⟩ t
    refine ⟨scalarProjectionLaw μ t, ?_⟩
    -- Proof comment: the forward direction is exactly pushforward stability of weak convergence.
    simpa [scalarProjectionLaw, scalarProjectionAEMeasurable] using
      tendsto_scalarProjectionLaw_of_tendsto hμ t
  · intro hproj
    choose ν hν using hproj
    have hν' : ∀ t : E, Tendsto (fun n ↦ scalarProjectionLaw (μs n) t) atTop (𝓝 (ν t)) := by
      intro t
      -- Proof comment: rewrite the given projected-law convergence through the local owner API.
      simpa [scalarProjectionLaw, scalarProjectionAEMeasurable] using hν t
    let f : E → ℂ := fun t ↦ charFun (ν t : Measure ℝ) (1 : ℝ)
    have hchar : ∀ t : E, Tendsto (fun n ↦ charFun (μs n) t) atTop (𝓝 (f t)) := by
      -- Proof comment: each projected weak limit determines the corresponding line of the
      -- multivariate characteristic function.
      simpa [f] using tendsto_charFun_of_tendsto_all_scalarProjectionLaws hν'
    have hf : PartiallyContinuousAtZero (d := d) f := by
      -- Proof comment: axiswise, `f` is identified with a fixed one-dimensional characteristic
      -- function, hence is continuous at the origin on each coordinate axis.
      simpa [f] using scalarProjectionLimit_partiallyContinuousAtZero (d := d) hν'
    -- Proof comment: Theorem 15.23 reconstructs the weak limit from the pointwise
    -- characteristic-function limit and the axis continuity at `0`.
    rcases exists_probabilityMeasure_of_tendsto_charFun (d := d) μs hchar hf with
      ⟨Q, -, hQ⟩
    exact ⟨Q, hQ⟩

/-- If `μs` converges weakly to `μ` and the projected laws converge to `ν t`, then `ν t` is the
pushforward of `μ` along `x ↦ ⟪t, x⟫`. -/
-- Proof sketch: apply the forward direction of the Cramer--Wold device to the weak convergence of
-- `μs` in order to get convergence of each projected law to the pushforward of `μ` along
-- `x ↦ ⟪t, x⟫`, then use
-- uniqueness of limits in the Hausdorff weak topology on probability measures.
theorem scalarProjectionLaw_limit_eq_of_tendsto
    {μs : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E}
    {ν : E → ProbabilityMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : ∀ t : E,
      Tendsto
        (fun n ↦
          ((μs n).map
            (show AEMeasurable (fun x : E ↦ inner ℝ t x) (μs n : Measure E) from
              aemeasurable_id.const_inner) : ProbabilityMeasure ℝ))
        atTop (𝓝 (ν t))) :
    ∀ t : E,
      ν t =
        (μ.map
          (show AEMeasurable (fun x : E ↦ inner ℝ t x) (μ : Measure E) from
            aemeasurable_id.const_inner) : ProbabilityMeasure ℝ) := by
  intro t
  -- Proof comment: weak convergence of `μs` determines the projected weak limit uniquely.
  have hproj :
      Tendsto (fun n ↦ scalarProjectionLaw (μs n) t) atTop (𝓝 (scalarProjectionLaw μ t)) :=
    tendsto_scalarProjectionLaw_of_tendsto hμ t
  have hν' :
      Tendsto (fun n ↦ scalarProjectionLaw (μs n) t) atTop (𝓝 (ν t)) := by
    -- Proof comment: rewrite the assumed convergence through the local projected-law API.
    simpa [scalarProjectionLaw, scalarProjectionAEMeasurable] using hν t
  exact tendsto_nhds_unique hν' hproj

end
