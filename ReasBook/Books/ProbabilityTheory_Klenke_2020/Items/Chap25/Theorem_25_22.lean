/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_52
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_70
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_73
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_74
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_65
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_62
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

universe u v

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 25.22: the Brownian-side compensator `t ↦ ∫_0^t H_s^2 ds`. -/
noncomputable def secondMomentCompensator
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (H s.toNNReal ω) ^ 2

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 25.22: evaluate `secondMomentCompensator H` at `(t, ω)`. -/
theorem secondMomentCompensator_apply
    (H : NNReal → Ω → ℝ) (t : NNReal) (ω : Ω) :
    secondMomentCompensator H t ω =
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (H s.toNNReal ω) ^ 2 := by
  -- Proof comment: `secondMomentCompensator` is defined by this integral.
  rfl

/-- Helper for Theorem 25.22: cutting off a progressively measurable integrand before a stopping
time preserves progressive measurability. -/
theorem processBeforeStoppingTime_progMeasurable
    {ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {H : NNReal → Ω → ℝ}
    (hH : ProgMeasurable ℱ H)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    ProgMeasurable ℱ (ProbabilityTheory.processBeforeStoppingTime H τ) := by
  intro i
  letI : MeasurableSpace Ω := ℱ i
  let s : Set (Set.Iic i × Ω) :=
    {p | ((p.1 : NNReal) : ENNReal) ≤ min (τ p.2) i}
  have hs : MeasurableSet s := by
    -- Proof comment: the stopping strip is the measurable comparison between the time coordinate
    -- and the truncated stopping time `min τ i`.
    refine measurableSet_le ?_ ?_
    · exact ENNReal.continuous_coe.measurable.comp
        (measurable_subtype_coe.comp measurable_fst)
    · exact
        ((hτ.min_const i).measurable_of_le (fun _ ↦ min_le_right _ _)).comp
          (@measurable_snd (Set.Iic i) Ω Subtype.instMeasurableSpace (ℱ i))
  have hEq :
      (fun p : Set.Iic i × Ω ↦ ProbabilityTheory.processBeforeStoppingTime H τ p.1 p.2) =
        Set.indicator s (fun p : Set.Iic i × Ω ↦ H p.1 p.2) := by
    funext p
    have hp : ((p.1 : NNReal) : ENNReal) ≤ i := by
      exact_mod_cast p.1.2
    by_cases hmem : p ∈ s
    · have hle : ((p.1 : NNReal) : ENNReal) ≤ τ p.2 := by
        have hmin : ((p.1 : NNReal) : ENNReal) ≤ min (τ p.2) i := by
          simpa [s] using hmem
        exact le_trans hmin (min_le_left _ _)
      -- Proof comment: inside the stopping strip, the cutoff agrees with the original process.
      have hcut :
          ProbabilityTheory.processBeforeStoppingTime H τ p.1 p.2 = H p.1 p.2 := by
        simpa [ProbabilityTheory.processBeforeStoppingTime_apply, hle]
      rw [hcut]
      symm
      exact Set.indicator_of_mem hmem (f := fun q : Set.Iic i × Ω ↦ H q.1 q.2)
    · have hnot : ¬ ((p.1 : NNReal) : ENNReal) ≤ τ p.2 := by
        intro hle
        apply hmem
        have hmin : ((p.1 : NNReal) : ENNReal) ≤ min (τ p.2) i := le_min hle hp
        simpa [s] using hmin
      -- Proof comment: outside the strip, the cutoff vanishes by definition.
      have hcut :
          ProbabilityTheory.processBeforeStoppingTime H τ p.1 p.2 = 0 := by
        simpa [ProbabilityTheory.processBeforeStoppingTime_apply, hnot]
      rw [hcut]
      symm
      exact Set.indicator_of_notMem hmem (f := fun q : Set.Iic i × Ω ↦ H q.1 q.2)
  rw [hEq]
  -- Proof comment: on `[0, i] × Ω`, the cutoff is the indicator of a measurable strip applied to
  -- the progressively measurable restriction of `H`.
  exact (hH i).indicator hs

end MeasureTheory

namespace Theorem25_22

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}

local notation "PathSpace" => C(NNReal, ℝ)

/-- Helper for Theorem 25.22: pull back a continuous-time process along a map of sample spaces. -/
def pullbackProcess
    {Ω' : Type v} (π : Ω' → Ω) (X : NNReal → Ω → ℝ) : NNReal → Ω' → ℝ :=
  fun t ω ↦ X t (π ω)

omit mΩ in
/-- Helper for Theorem 25.22: evaluating `pullbackProcess π X` gives `X t (π ω)`. -/
@[simp] theorem pullbackProcess_apply
    {Ω' : Type v} (π : Ω' → Ω) (X : NNReal → Ω → ℝ)
    (t : NNReal) (ω : Ω') :
    pullbackProcess π X t ω = X t (π ω) := by
  -- Proof comment: `pullbackProcess` only precomposes the sample coordinate with `π`.
  rfl

/-- Helper for Theorem 25.22: center a process at time `0`. -/
def processCenteredAtZero
    (X : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ X t ω - X 0 ω

/-- Helper for Theorem 25.22: use the canonical Chapter 21 square-variation owner surface for the
local theorem file. -/
abbrev IsContinuousSquareVariationProcess
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (M A : NNReal → Ω → ℝ) : Prop :=
  ProbabilityTheory.IsContinuousSquareVariationProcess ℱ μ M A

/-- Helper for Theorem 25.22: choose one canonical square-variation witness for a continuous local
martingale. -/
noncomputable abbrev continuousSquareVariationProcess
    {M : NNReal → Ω → ℝ}
    (hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M) :
    NNReal → Ω → ℝ :=
  Classical.choose
    (_root_.ProbabilityTheory.existsUnique_continuousSquareVariationProcess
      (ℱ := ℱ) (μ := μ) hM)

/-- Helper for Theorem 25.22: the chosen canonical square-variation witness satisfies the square-
variation process axioms. -/
theorem continuousSquareVariationProcess_spec
    {M : NNReal → Ω → ℝ}
    (hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M) :
    IsContinuousSquareVariationProcess ℱ μ M (continuousSquareVariationProcess (ℱ := ℱ) (μ := μ) hM) := by
  -- Proof comment: the local chooser is defined by selecting the canonical Chapter 21 witness.
  exact
    (Classical.choose_spec
      (_root_.ProbabilityTheory.existsUnique_continuousSquareVariationProcess
        (ℱ := ℱ) (μ := μ) hM)).1

/-- Helper for Theorem 25.22: use the canonical Chapter 21 quadratic-covariation owner surface
for the local theorem file. -/
abbrev IsContinuousQuadraticCovariationProcess
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (M N A : NNReal → Ω → ℝ) : Prop :=
  ProbabilityTheory.IsContinuousQuadraticCovariationProcess ℱ μ M N A

/-- Helper for Theorem 25.22: `M` has absolutely continuous square variation with some
progressively measurable density. -/
def HasAbsolutelyContinuousSquareVariation
    (M : NNReal → Ω → ℝ)
    (hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M) : Prop :=
  let _ := hM
  ∃ density : NNReal → Ω → NNReal,
    ∃ squareVariation : NNReal → Ω → ℝ,
      IsContinuousSquareVariationProcess ℱ μ M squareVariation ∧
        ProgMeasurable ℱ (fun t ω ↦ (density t ω : ℝ)) ∧
        ∀ t : NNReal, ∀ ω : Ω,
          squareVariation t ω =
            ∫ s in Set.Icc (0 : ℝ) (t : ℝ), (density s.toNNReal ω : ℝ)

/-- Helper for Theorem 25.22: extract the bracket density from an absolutely continuous square
variation witness. -/
noncomputable def squareVariationDensity
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    NNReal → Ω → NNReal :=
  Classical.choose hbr

/-- Helper for Theorem 25.22: the bracket-density integral
`t ↦ ∫_0^t H_s^2 d⟨M⟩_s` written using the density of `⟨M⟩`. -/
def bracketDensityIntegralUpTo
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦
    ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      (H s.toNNReal ω) ^ 2 * (squareVariationDensity hbr s.toNNReal ω : ℝ)

/-- Helper for Theorem 25.22: the density root `sqrt (d⟨M⟩ / dt)`. -/
def squareVariationDensityRoot
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    NNReal → Ω → ℝ :=
  fun t ω ↦ Real.sqrt (squareVariationDensity hbr t ω : ℝ)

/-- Helper for Theorem 25.22: on the Brownian side, `∫ H dM` uses the integrand
`H * sqrt (d⟨M⟩ / dt)`. -/
def brownianRepresentationItoIntegrand
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ H t ω * squareVariationDensityRoot hbr t ω

/-- Helper for Theorem 25.22: the source finite-horizon square-bracket energy condition for the
integrand `H`, written in the canonical local-square-integrability form of
`H * sqrt (d⟨M⟩ / dt)`. -/
def HasFiniteBracketEnergy
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) : Prop :=
  IsLocallySquareIntegrableProcess ℱ μ (brownianRepresentationItoIntegrand hbr H)

/-- Helper for Theorem 25.22: the bracket-density root `sqrt (d⟨M⟩ / dt)` is progressively
measurable. -/
lemma squareVariationDensityRoot_progMeasurable
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    ProgMeasurable ℱ (squareVariationDensityRoot hbr) := by
  -- Proof comment: the density is already progressively measurable in the square-variation
  -- witness, and composing with the continuous square-root map preserves that property.
  have hDensity :
      ProgMeasurable ℱ (fun t ω ↦ (squareVariationDensity hbr t ω : ℝ)) :=
    (Classical.choose_spec (Classical.choose_spec hbr)).2.1
  intro i
  simpa [squareVariationDensityRoot] using
    (Real.continuous_sqrt.comp_stronglyMeasurable (hDensity i))

/-- Helper for Theorem 25.22: squaring the Brownian-side coefficient
`H * sqrt (d⟨M⟩ / dt)` recovers the bracket-density integrand `H² * d⟨M⟩ / dt`. -/
lemma brownianRepresentationItoIntegrand_sq
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) (t : NNReal) (ω : Ω) :
    (brownianRepresentationItoIntegrand hbr H t ω) ^ 2 =
      (H t ω) ^ 2 * (squareVariationDensity hbr t ω : ℝ) := by
  -- Proof comment: expand the coefficient and use `sqrt(a)^2 = a` for the nonnegative density
  -- `a = d⟨M⟩ / dt`.
  have hnonneg : 0 ≤ (squareVariationDensity hbr t ω : ℝ) := by
    exact_mod_cast (show (0 : NNReal) ≤ squareVariationDensity hbr t ω from bot_le)
  rw [brownianRepresentationItoIntegrand, squareVariationDensityRoot, mul_pow, Real.sq_sqrt hnonneg]

/-- Helper for Theorem 25.22: the all-horizons bracket-energy hypothesis is exactly the local
square-integrability condition for `brownianRepresentationItoIntegrand hbr H`. -/
lemma brownianRepresentationItoIntegrand_hasFiniteBracketEnergy
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    {H : NNReal → Ω → ℝ}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ T : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    HasFiniteBracketEnergy hbr H := by
  refine ⟨hH_prog.mul (squareVariationDensityRoot_progMeasurable (ℱ := ℱ) hbr), ?_⟩
  intro T
  -- Proof comment: after rewriting the pointwise square of the Brownian-side coefficient, the
  -- integrability hypothesis is exactly the local square-integrability clause.
  filter_upwards [hH_sq T] with ω hω
  simpa [HasFiniteBracketEnergy, brownianRepresentationItoIntegrand_sq] using hω

/-- Helper for Theorem 25.22: deterministically cutting off `H` at time `T` turns the single
finite-horizon bracket-energy hypothesis on `[0,T]` into the packaged local bracket-energy
condition for the stopped integrand. -/
lemma processBeforeStoppingTime_const_hasFiniteBracketEnergy
    {M H : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    HasFiniteBracketEnergy hbr
      (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) := by
  have hCut_prog :
      ProgMeasurable ℱ
        (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) :=
    MeasureTheory.processBeforeStoppingTime_progMeasurable
      hH_prog (show IsStoppingTime ℱ (fun _ ↦ (T : ENNReal)) from isStoppingTime_const ℱ T)
  refine
    brownianRepresentationItoIntegrand_hasFiniteBracketEnergy
      (ℱ := ℱ) (μ := μ) (M := M) (hM := hM) hbr hCut_prog ?_
  intro U
  filter_upwards [hH_sq] with ω hω
  let g : ℝ → ℝ := fun s ↦
    (ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
      (squareVariationDensity hbr s.toNNReal ω : ℝ)
  have hBase : IntegrableOn g (Set.Icc (0 : ℝ) (T : ℝ)) := by
    -- Proof comment: on the interval `[0,T]`, the deterministic cutoff leaves `H` unchanged.
    refine hω.congr_fun ?_ measurableSet_Icc
    intro s hs
    have hs_toNNReal_le : s.toNNReal ≤ T := by
      exact (Real.toNNReal_le_iff_le_coe).2 hs.2
    have hs_cutoff : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      exact_mod_cast hs_toNNReal_le
    dsimp [g]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply]
    rw [if_pos hs_cutoff]
  have hCut : IntegrableOn g (Set.Icc (0 : ℝ) (U : ℝ)) := by
    -- Proof comment: outside `[0,T]` but still inside `[0,U]`, the deterministic cutoff is zero.
    refine IntegrableOn.of_forall_diff_eq_zero hBase measurableSet_Icc ?_
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1.1
    have hs_not_le : ¬ s ≤ T := by
      intro hs_le
      exact hs.2 ⟨hs_nonneg, hs_le⟩
    have hs_not_cutoff :
        ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      intro hs_cutoff
      have hs_toNNReal_le : s.toNNReal ≤ T := by
        exact_mod_cast hs_cutoff
      have hs_le : s ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs_nonneg] using hs_toNNReal_le
      exact hs_not_le hs_le
    dsimp [g]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply]
    rw [if_neg hs_not_cutoff]
    simp
  exact hCut

/-- Helper for Theorem 25.22: the fixed-horizon bracket-density integrability of `H` upgrades to
the all-horizons bracket-density integrability statement needed for the deterministically stopped
coefficient `processBeforeStoppingTime H (fun _ ↦ T)`. -/
lemma processBeforeStoppingTime_const_integrableOn_bracketDensity_allHorizons
    {M H : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∀ U : NNReal, ∀ᵐ ω ∂μ,
      IntegrableOn
        (fun s : ℝ ↦
          (ProbabilityTheory.processBeforeStoppingTime H
              (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
            (squareVariationDensity hbr s.toNNReal ω : ℝ))
        (Set.Icc (0 : ℝ) (U : ℝ)) := by
  have hCut :
      HasFiniteBracketEnergy hbr
        (ProbabilityTheory.processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) :=
    processBeforeStoppingTime_const_hasFiniteBracketEnergy
      (ℱ := ℱ) (μ := μ) (M := M) (H := H) (hM := hM) hbr T hH_prog hH_sq
  intro U
  -- Proof comment: the packaged finite-bracket-energy statement is exactly the desired all-
  -- horizons integrability after rewriting the Brownian-side coefficient square.
  filter_upwards [hCut.2 U] with ω hω
  simpa [HasFiniteBracketEnergy, brownianRepresentationItoIntegrand_sq] using hω

/-- Helper for Theorem 25.22: the Brownian-side realization already carries the continuous local
martingale and square-variation data needed in this item. -/
def IsBrownianLocalItoIntegral
    {Ω' : Type v} [mΩ' : MeasurableSpace Ω']
    (filtration : Filtration NNReal mΩ') (law : Measure Ω')
    (_W H I : NNReal → Ω' → ℝ) : Prop :=
  ProbabilityTheory.IsContinuousLocalMartingale filtration law I ∧
    IsContinuousSquareVariationProcess filtration law I
      (MeasureTheory.secondMomentCompensator H)

/-- Helper for Theorem 25.22: any Brownian-side realization already exposes the martingale and
square-variation conclusion used below. -/
theorem brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
    {Ω' : Type v} [mΩ' : MeasurableSpace Ω']
    {filtration : Filtration NNReal mΩ'} {law : Measure Ω'}
    {W H M : NNReal → Ω' → ℝ}
    (hM : IsBrownianLocalItoIntegral filtration law W H M) :
    ProbabilityTheory.IsContinuousLocalMartingale filtration law M ∧
      IsContinuousSquareVariationProcess filtration law M
        (MeasureTheory.secondMomentCompensator H) := by
  -- Proof comment: the Brownian-side owner predicate is exactly this conjunction.
  exact hM

/-- Helper for Theorem 25.22: internal Brownian-extension witness used to compare the local file's
quadratic-variation setup with the public source-facing Itô-integral relation below. -/
structure HasBrownianExtensionItoWitness
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H N : NNReal → Ω → ℝ) : Prop where
  extensionWitness :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (law : ProbabilityMeasure Ω')
      (lift : Ω' → Ω) (filtration : Filtration NNReal mΩ')
      (brownian : NNReal → Ω' → ℝ),
      MeasurePreserving lift (law : Measure Ω') μ ∧
        (∀ t : NNReal, MeasurableSpace.comap lift (ℱ t) ≤ filtration t) ∧
        IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
          (pullbackProcess lift (squareVariationDensityRoot hbr))
          (pullbackProcess lift (processCenteredAtZero M)) ∧
        IsBrownianLocalItoIntegral filtration (law : Measure Ω') brownian
          (pullbackProcess lift (brownianRepresentationItoIntegrand hbr H))
          (pullbackProcess lift N)

/-- Helper for Theorem 25.22: the mixed bracket integral
`t ↦ ∫_0^t H_s K_s d⟨M,N⟩_s` written using the canonical pathwise quadratic-covariation
integral built from dyadic mixed-increment sums. -/
noncomputable def dyadicQuadraticCovariationIntegralApproximationUpTo
    (H : NNReal → ℝ) (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum
    (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    fun k ↦
      H (Definition2158.dyadicPartitionSequence n k) *
        (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          F (Definition2158.dyadicPartitionSequence n k)) *
        (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          G (Definition2158.dyadicPartitionSequence n k))

/-- Helper for Theorem 25.22: the canonical pathwise integral of `H` against the quadratic
covariation of `F` and `G`, defined as the `limUnder` of the dyadic mixed-increment sums. -/
noncomputable def pathwiseQuadraticCovariationIntegral
    (H : NNReal → ℝ) (F G : PathSpace) : NNReal → ℝ :=
  fun T ↦ limUnder atTop (dyadicQuadraticCovariationIntegralApproximationUpTo H F G T)

/-- Helper for Theorem 25.22: the left-point partition sum
`∑ H_t (X_{t'} - X_t)` on `[0, T]` along the `n`-th row of an admissible partition sequence `P`.
-/
def partitionPathwiseItoApproximationUpTo
    (H : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    H (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k))

/-- Helper for Theorem 25.22: every partition point that contributes to the truncated sum up to
`T` lies strictly before `T`. -/
lemma partitionPoint_lt_time_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k < T := by
  -- Proof comment: if `P n k` were already at or beyond `T`, the defining minimality of
  -- `partitionBoundIndex` would force the truncation index to be at most `k`.
  have hk_not : ¬ T ≤ P n k := by
    intro hkT
    have hmin : partitionBoundIndex P n T ≤ k := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P n T) hkT)
    exact (not_le_of_gt hk) hmin
  exact lt_of_not_ge hk_not

/-- Helper for Theorem 25.22: every partition point that contributes to the truncated sum up to
`T` belongs to `Set.Icc 0 T`. -/
lemma partitionPoint_mem_Icc_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k ∈ Set.Icc 0 T := by
  -- Proof comment: admissible partition points are nonnegative, and the previous lemma puts them
  -- below the truncation horizon.
  constructor
  · exact bot_le
  · exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk)

/-- Helper for Theorem 25.22: deterministic stopping at time `T` does not change the integrand on
`Set.Icc 0 T`. -/
lemma processBeforeStoppingTime_const_eqOn_Icc
    (H : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    Set.EqOn
      (fun t : NNReal ↦ ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω)
      (fun t : NNReal ↦ H t ω)
      (Set.Icc 0 T) := by
  intro t ht
  have htT : (t : ENNReal) ≤ (T : ENNReal) := by
    exact_mod_cast ht.2
  -- Proof comment: inside the deterministic cutoff window, the stopped process is definitionally
  -- the original process.
  simp [ProbabilityTheory.processBeforeStoppingTime_apply, htT]

/-- Helper for Theorem 25.22: truncated left-point partition sums only depend on the coefficient
function on `Set.Icc 0 T`. -/
lemma partitionPathwiseItoApproximationUpTo_congrOn_Icc
    {K L : NNReal → ℝ} {X : PathSpace}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {T : NNReal} (hKL : Set.EqOn K L (Set.Icc 0 T)) (row : ℕ) :
    partitionPathwiseItoApproximationUpTo K X P T row =
      partitionPathwiseItoApproximationUpTo L X P T row := by
  -- Proof comment: every left endpoint appearing in the truncated row belongs to `Set.Icc 0 T`,
  -- so the `EqOn` hypothesis rewrites the finite sum termwise.
  rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_mem :
      P row k ∈ Set.Icc 0 T :=
    partitionPoint_mem_Icc_of_lt_partitionBoundIndex P row k T (Finset.mem_range.mp hk)
  rw [hKL hk_mem]

/-- Helper for Theorem 25.22: truncated mixed partition sums only depend on the two paths on
`Set.Icc 0 T`. -/
lemma partitionQuadraticCovariationSum_congrOn_Icc
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {F₁ F₂ G₁ G₂ : PathSpace} {T : NNReal}
    (hF : Set.EqOn F₁ F₂ (Set.Icc 0 T))
    (hG : Set.EqOn G₁ G₂ (Set.Icc 0 T))
    (row : ℕ) :
    partitionQuadraticCovariationSum P F₁ G₁ T row =
      partitionQuadraticCovariationSum P F₂ G₂ T row := by
  -- Proof comment: every endpoint used by the truncated mixed sum lies in `Set.Icc 0 T`, so the
  -- two `EqOn` hypotheses rewrite both increment factors termwise.
  rw [partitionQuadraticCovariationSum, partitionQuadraticCovariationSum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_mem :
      P row k ∈ Set.Icc 0 T :=
    partitionPoint_mem_Icc_of_lt_partitionBoundIndex P row k T (Finset.mem_range.mp hk)
  have hnext_mem :
      partitionNextPointUpTo P row k T ∈ Set.Icc 0 T := by
    constructor
    · exact bot_le
    · simp [partitionNextPointUpTo]
  rw [hF hnext_mem, hF hk_mem, hG hnext_mem, hG hk_mem]

/-- Helper for Theorem 25.22: truncated dyadic mixed sums only depend on the weight on
`Set.Icc 0 T`. -/
lemma dyadicQuadraticCovariationIntegralApproximationUpTo_congrOn_Icc
    {K L : NNReal → ℝ} {F G : PathSpace}
    {T : NNReal} (hKL : Set.EqOn K L (Set.Icc 0 T)) (n : ℕ) :
    dyadicQuadraticCovariationIntegralApproximationUpTo K F G T n =
      dyadicQuadraticCovariationIntegralApproximationUpTo L F G T n := by
  -- Proof comment: the dyadic mixed sum also samples the coefficient only at left endpoints
  -- from the truncated row, so the same termwise rewrite applies.
  rw [dyadicQuadraticCovariationIntegralApproximationUpTo,
    dyadicQuadraticCovariationIntegralApproximationUpTo]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_mem :
      Definition2158.dyadicPartitionSequence n k ∈ Set.Icc 0 T :=
    partitionPoint_mem_Icc_of_lt_partitionBoundIndex
      Definition2158.dyadicPartitionSequence n k T (Finset.mem_range.mp hk)
  rw [hKL hk_mem]

/-- Helper for Theorem 25.22: truncating the dyadic row exactly at its own `k`-th partition point
uses precisely the first `k` summands. -/
lemma dyadicPartitionBoundIndex_partitionPoint
    (n k : ℕ) :
    partitionBoundIndex Definition2158.dyadicPartitionSequence n
        (Definition2158.dyadicPartitionSequence n k) =
      k := by
  let P := Definition2158.dyadicPartitionSequence
  have hle :
      partitionBoundIndex P n (P n k) ≤ k := by
    -- Proof comment: `k` itself is an admissible witness in the defining `Nat.find`.
    simpa [partitionBoundIndex] using
      (Nat.find_min' (exists_partition_index_le_time P n (P n k)) (le_rfl : P n k ≤ P n k))
  have hge :
      k ≤ partitionBoundIndex P n (P n k) := by
    -- Proof comment: any earlier truncation index would force the partition point `P n k` to lie
    -- strictly below itself by dyadic strict monotonicity.
    by_contra hlt
    have hlt' : partitionBoundIndex P n (P n k) < k := Nat.lt_of_not_ge hlt
    have hmono : StrictMono (P n) :=
      by simpa [P] using Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n
    have hstrict :
        P n (partitionBoundIndex P n (P n k)) < P n k :=
      hmono hlt'
    exact
      (not_lt_of_ge (le_partitionBoundIndex_time P n (P n k))) hstrict
  exact le_antisymm hle hge

/-- Helper for Theorem 25.22: clipping a partition row twice at the same left endpoint does not
change the clipped successor. -/
private lemma partitionNextPointUpTo_idem
    (P : ℕ → ℕ → NNReal) (n k : ℕ) (T : NNReal) :
    partitionNextPointUpTo P n k (partitionNextPointUpTo P n k T) =
      partitionNextPointUpTo P n k T := by
  -- Proof comment: both sides are the same iterated minimum `min (P n (k+1)) (min (P n (k+1)) T)`.
  simp [partitionNextPointUpTo]

/-- Helper for Theorem 25.22: on one fixed dyadic row, advancing the upper truncation horizon from
the `k`-th left endpoint to the next clipped endpoint adds exactly the `k`-th weighted increment.
-/
lemma partitionPathwiseItoApproximationUpTo_nextPoint_sub_sameRow
    (H : NNReal → ℝ) (X : PathSpace) (t : NNReal) (n k : ℕ)
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n t) :
    partitionPathwiseItoApproximationUpTo
        H X Definition2158.dyadicPartitionSequence
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
        n
      -
        partitionPathwiseItoApproximationUpTo
          H X Definition2158.dyadicPartitionSequence
          (Definition2158.dyadicPartitionSequence n k)
          n =
      H (Definition2158.dyadicPartitionSequence n k) *
        (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) -
          X (Definition2158.dyadicPartitionSequence n k)) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P n t
  have hmono : StrictMono (P n) := by
    simpa [P] using Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n
  have hk_succ_le : k + 1 ≤ N := Nat.succ_le_of_lt hk
  have hleft :
      partitionBoundIndex P n (P n k) = k :=
    dyadicPartitionBoundIndex_partitionPoint n k
  by_cases hlast : k + 1 < N
  · have hnext_lt : P n (k + 1) < t := dyadicPartition_lt_time_of_lt_boundIndex n hlast
    have hrightPoint :
        partitionNextPointUpTo P n k t = P n (k + 1) := by
      rw [partitionNextPointUpTo, min_eq_left (le_of_lt hnext_lt)]
    have hright :
        partitionBoundIndex P n (partitionNextPointUpTo P n k t) = k + 1 := by
      rw [hrightPoint]
      exact dyadicPartitionBoundIndex_partitionPoint n (k + 1)
    -- Proof comment: before the final truncation point, moving from `P n k` to `P n (k+1)`
    -- appends exactly one new left-point increment to the same-row finite sum, because the two
    -- prefix rows still use the same successors `P n (x + 1)`.
    rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo,
      hright, hleft, Finset.sum_range_succ]
    have hprefix :
        ∑ x ∈ Finset.range k,
            H (P n x) *
                (X (partitionNextPointUpTo P n x (partitionNextPointUpTo P n k t)) -
                  X (P n x)) =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hx_lt : x < k := Finset.mem_range.mp hx
      have hx_succ_le : x + 1 ≤ k := Nat.succ_le_of_lt hx_lt
      have hnext_left :
          partitionNextPointUpTo P n x (partitionNextPointUpTo P n k t) = P n (x + 1) := by
        rw [hrightPoint, partitionNextPointUpTo, min_eq_left (hmono.monotone (le_trans hx_succ_le
          (Nat.le_succ k)))]
      have hnext_right :
          partitionNextPointUpTo P n x (P n k) = P n (x + 1) := by
        rw [partitionNextPointUpTo, min_eq_left (hmono.monotone hx_succ_le)]
      rw [hnext_left, hnext_right]
    have hself :
        partitionNextPointUpTo P n k (partitionNextPointUpTo P n k t) =
          partitionNextPointUpTo P n k t :=
      partitionNextPointUpTo_idem P n k t
    rw [hprefix, hself]
    set rowPrefix :=
      (∑ x ∈ Finset.range k,
        (H (P n x) * X (partitionNextPointUpTo P n x (P n k)) - H (P n x) * X (P n x)) : ℝ)
      with hprefixDef
    -- Proof comment: after the common prefix cancels, only the new `k`-th weighted increment
    -- remains.
    calc
      ∑ x ∈ Finset.range k,
          H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) +
            H (P n k) * (X (partitionNextPointUpTo P n k t) - X (P n k)) -
        ∑ x ∈ Finset.range k,
          H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x))
          =
        ∑ x ∈ Finset.range k,
          (H (P n x) * X (partitionNextPointUpTo P n x (P n k)) - H (P n x) * X (P n x)) +
            H (P n k) * X (partitionNextPointUpTo P n k t) -
          H (P n k) * X (P n k) -
        ∑ x ∈ Finset.range k,
          (H (P n x) * X (partitionNextPointUpTo P n x (P n k)) - H (P n x) * X (P n x)) := by
              ring
      _ =
        rowPrefix + H (P n k) * X (partitionNextPointUpTo P n k t) -
          H (P n k) * X (P n k) - rowPrefix := by
              simp [hprefixDef]
      _ = H (P n k) * X (partitionNextPointUpTo P n k t) - H (P n k) * X (P n k) := by
            ring
      _ = H (P n k) * (X (partitionNextPointUpTo P n k t) - X (P n k)) := by
            ring
  · have hlastEq : k + 1 = N := le_antisymm hk_succ_le (Nat.le_of_not_gt hlast)
    have hbound :
        partitionBoundIndex P n t = k + 1 := by
      simpa [N] using hlastEq.symm
    have hrightPoint :
        partitionNextPointUpTo P n k t = t := by
      rw [partitionNextPointUpTo, min_eq_right]
      simpa [N, hlastEq] using le_partitionBoundIndex_time P n t
    -- Proof comment: on the last active cell, the clipped successor is the terminal time `t`, so
    -- the same-row finite sum again gains exactly one final weighted increment, with the earlier
    -- summands cancelling because both rows still use the same successors `P n (x + 1)`.
    rw [partitionPathwiseItoApproximationUpTo, partitionPathwiseItoApproximationUpTo,
      hrightPoint, hbound, hleft, Finset.sum_range_succ]
    have hprefix :
        ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x t) - X (P n x)) =
          ∑ x ∈ Finset.range k,
            H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hx_lt : x < k := Finset.mem_range.mp hx
      have hx_succ_lt : x + 1 < N := by
        rw [← hlastEq]
        exact Nat.succ_lt_succ hx_lt
      have hnext_left :
          partitionNextPointUpTo P n x t = P n (x + 1) := by
        rw [partitionNextPointUpTo, min_eq_left (le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex
          n hx_succ_lt))]
      have hnext_right :
          partitionNextPointUpTo P n x (P n k) = P n (x + 1) := by
        rw [partitionNextPointUpTo, min_eq_left (hmono.monotone (Nat.succ_le_of_lt hx_lt))]
      rw [hnext_left, hnext_right]
    rw [hprefix]
    set rowPrefix :=
      (∑ x ∈ Finset.range k,
        (H (P n x) * X (partitionNextPointUpTo P n x (P n k)) - H (P n x) * X (P n x)) : ℝ)
      with hprefixDef
    have hrightPoint' :
        partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t = t := by
      simpa [P] using hrightPoint
    -- Proof comment: the last active cell is handled by the same cancellation, now with terminal
    -- time `t` as the clipped successor.
    calc
      ∑ x ∈ Finset.range k,
          H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) +
            H (P n k) * (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) - X (P n k)) -
        ∑ x ∈ Finset.range k,
          H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x))
          =
        ∑ x ∈ Finset.range k,
          H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) +
            H (P n k) * (X t - X (P n k)) -
        ∑ x ∈ Finset.range k,
          H (P n x) * (X (partitionNextPointUpTo P n x (P n k)) - X (P n x)) := by
              rw [hrightPoint']
      _ =
        ∑ x ∈ Finset.range k,
          (H (P n x) * X (partitionNextPointUpTo P n x (P n k)) - H (P n x) * X (P n x)) +
            H (P n k) * X t -
          H (P n k) * X (P n k) -
        ∑ x ∈ Finset.range k,
          (H (P n x) * X (partitionNextPointUpTo P n x (P n k)) - H (P n x) * X (P n x)) := by
              ring
      _ = rowPrefix + H (P n k) * X t - H (P n k) * X (P n k) - rowPrefix := by
            simp [hprefixDef]
      _ = H (P n k) * X t - H (P n k) * X (P n k) := by
            ring
      _ = H (P n k) * (X t - X (P n k)) := by
            ring

/-- Helper for Theorem 25.22: if both dyadic Itô sums use the same row `n`, then the mixed
partition row of those sums is exactly the weighted mixed row of the original paths. -/
theorem partitionPathwiseItoApproximationUpTo_sameRow_mixed
    (H K : NNReal → ℝ) (X Y : PathSpace) (t : NNReal) (n : ℕ) :
    Finset.sum
        (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
        (fun k ↦
          (partitionPathwiseItoApproximationUpTo
              H X Definition2158.dyadicPartitionSequence
              (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
              n -
            partitionPathwiseItoApproximationUpTo
              H X Definition2158.dyadicPartitionSequence
              (Definition2158.dyadicPartitionSequence n k)
              n) *
            (partitionPathwiseItoApproximationUpTo
                K Y Definition2158.dyadicPartitionSequence
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                n -
              partitionPathwiseItoApproximationUpTo
                K Y Definition2158.dyadicPartitionSequence
                (Definition2158.dyadicPartitionSequence n k)
                n)) =
      dyadicQuadraticCovariationIntegralApproximationUpTo
        (fun s ↦ H s * K s) X Y t n := by
  rw [dyadicQuadraticCovariationIntegralApproximationUpTo]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [partitionPathwiseItoApproximationUpTo_nextPoint_sub_sameRow
      H X t n k (Finset.mem_range.mp hk)]
  rw [partitionPathwiseItoApproximationUpTo_nextPoint_sub_sameRow
      K Y t n k (Finset.mem_range.mp hk)]
  -- Proof comment: after normalizing both row increments, each summand is exactly the defining
  -- weighted mixed increment of `dyadicQuadraticCovariationIntegralApproximationUpTo`.
  ring

/-- Helper for Theorem 25.22: the mixed bracket integral
`t ↦ ∫_0^t H_s K_s d⟨M,N⟩_s` written using the canonical pathwise quadratic-covariation
integral. -/
noncomputable def quadraticCovariationIntegralUpTo
    {M N : NNReal → Ω → ℝ}
    (hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M)
    (hN : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ N)
    (H K : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦
    pathwiseQuadraticCovariationIntegral
      (fun s ↦ H s ω * K s ω)
      (⟨fun s ↦ M s ω, hM.continuous ω⟩)
      (⟨fun s ↦ N s ω, hN.continuous ω⟩)
      t

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 25.22: after pulling back to a Brownian representation, the Brownian-side
second-moment compensator of `H * sqrt (d⟨M⟩ / dt)` is exactly the pulled-back bracket-density
integral. -/
theorem pullbackSecondMomentCompensator_eq_pullbackBracketDensityIntegralUpTo
    {M H : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    {Ω' : Type v} [MeasurableSpace Ω']
    (lift : Ω' → Ω) :
    MeasureTheory.secondMomentCompensator
        (pullbackProcess lift (brownianRepresentationItoIntegrand hbr H)) =
      pullbackProcess lift (bracketDensityIntegralUpTo hbr H) := by
  -- Proof comment: after expanding the pullback coefficient, the integrands agree pointwise
  -- because `sqrt(a)^2 = a` for the nonnegative density `a = d⟨M⟩/dt`.
  funext t ω'
  simp [MeasureTheory.secondMomentCompensator, pullbackProcess, bracketDensityIntegralUpTo,
    brownianRepresentationItoIntegrand, squareVariationDensityRoot, mul_pow]

/-- Helper for Theorem 25.22: on the base space, the Brownian-side second-moment compensator of
`H * sqrt (d⟨M⟩ / dt)` is exactly `bracketDensityIntegralUpTo hbr H`. -/
theorem secondMomentCompensator_brownianRepresentationItoIntegrand_eq_bracketDensityIntegralUpTo
    {M H : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    MeasureTheory.secondMomentCompensator (brownianRepresentationItoIntegrand hbr H) =
      bracketDensityIntegralUpTo hbr H := by
  -- Proof comment: this is the identity-lift specialization of the pullback compensator
  -- normalization, so both sides reduce to the same integral formula.
  simpa using
    pullbackSecondMomentCompensator_eq_pullbackBracketDensityIntegralUpTo
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) hbr id

/-- Helper for Theorem 25.22: a zero-start process agrees with its centered version. -/
lemma processCenteredAtZero_eq_self_of_zero
    {M : NNReal → Ω → ℝ}
    (hM0 : M 0 = 0) :
    processCenteredAtZero M = M := by
  -- Proof comment: the centering formula subtracts `M 0`, which vanishes under the hypothesis.
  funext t ω
  simp [processCenteredAtZero, hM0]

/-- Helper for Theorem 25.22: for the unit integrand, the Brownian-side coefficient is just the
square-variation density root. -/
lemma brownianRepresentationItoIntegrand_one_eq_squareVariationDensityRoot
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    brownianRepresentationItoIntegrand hbr 1 = squareVariationDensityRoot hbr := by
  -- Proof comment: unfold the coefficient and simplify the pointwise multiplication by `1`.
  funext t ω
  simp [brownianRepresentationItoIntegrand]

/-- Helper for Theorem 25.22: pulling back the centered version of a zero-start process leaves
the process unchanged. -/
lemma pullbackProcess_processCenteredAtZero_eq_self_of_zero
    {Ω' : Type v} [MeasurableSpace Ω']
    (lift : Ω' → Ω)
    {M : NNReal → Ω → ℝ}
    (hM0 : M 0 = 0) :
    pullbackProcess lift (processCenteredAtZero M) = pullbackProcess lift M := by
  -- Proof comment: first normalize the base process by the zero-start hypothesis, then pull it
  -- back along the sample-space map.
  simpa using congrArg (pullbackProcess lift)
    (processCenteredAtZero_eq_self_of_zero (M := M) hM0)

/-- Helper for Theorem 25.22: pulling back the unit Brownian-side coefficient leaves exactly the
square-variation density root. -/
lemma pullbackProcess_brownianRepresentationItoIntegrand_one_eq_squareVariationDensityRoot
    {Ω' : Type v} [MeasurableSpace Ω']
    (lift : Ω' → Ω)
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM) :
    pullbackProcess lift (brownianRepresentationItoIntegrand hbr 1) =
      pullbackProcess lift (squareVariationDensityRoot hbr) := by
  -- Proof comment: the unit-integrand normalization commutes with pullback because both sides are
  -- defined pointwise.
  simpa using congrArg (pullbackProcess lift)
    (brownianRepresentationItoIntegrand_one_eq_squareVariationDensityRoot
      (M := M) (hM := hM) hbr)

/-- Helper for Theorem 25.22: pulling back a stopped coefficient commutes with the stopping rule.
-/
lemma pullbackProcess_processBeforeStoppingTime_local
    {Ω' : Type v} [MeasurableSpace Ω']
    (lift : Ω' → Ω) {H : NNReal → Ω → ℝ} {τ : Ω → ENNReal} :
    pullbackProcess lift (ProbabilityTheory.processBeforeStoppingTime H τ) =
      ProbabilityTheory.processBeforeStoppingTime
        (pullbackProcess lift H) (fun ω' ↦ τ (lift ω')) := by
  -- Proof comment: both sides evaluate `H t (lift ω')` on the same stopping event
  -- `{t ≤ τ (lift ω')}`.
  funext t ω'
  by_cases hτω' : (t : ENNReal) ≤ τ (lift ω')
  · simp [pullbackProcess, ProbabilityTheory.processBeforeStoppingTime_apply, hτω']
  · simp [pullbackProcess, ProbabilityTheory.processBeforeStoppingTime_apply, hτω']

/-- Helper for Theorem 25.22: pulling back a stopped process commutes with the stopping
operation. -/
lemma pullbackProcess_stoppedProcess_local
    {Ω' : Type v} [MeasurableSpace Ω']
    (lift : Ω' → Ω) {N : NNReal → Ω → ℝ} {τ : Ω → ENNReal} :
    pullbackProcess lift (stoppedProcess N τ) =
      stoppedProcess (pullbackProcess lift N) (fun ω' ↦ τ (lift ω')) := by
  -- Proof comment: both sides evaluate the same original process at the same stopped time.
  funext t ω'
  simp [pullbackProcess, stoppedProcess]

/-- Helper for Theorem 25.22: stopping `H` before forming the Brownian-side coefficient is the
same as stopping the coefficient `H * sqrt (d⟨M⟩ / dt)` afterwards. -/
lemma brownianRepresentationItoIntegrand_processBeforeStoppingTime_local
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    {H : NNReal → Ω → ℝ} {τ : Ω → ENNReal} :
    brownianRepresentationItoIntegrand hbr (ProbabilityTheory.processBeforeStoppingTime H τ) =
      ProbabilityTheory.processBeforeStoppingTime
        (brownianRepresentationItoIntegrand hbr H) τ := by
  -- Proof comment: the density-root factor is unaffected by stopping, so only the coefficient
  -- `H` is truncated.
  funext t ω
  by_cases hτω : (t : ENNReal) ≤ τ ω
  · simp [brownianRepresentationItoIntegrand, ProbabilityTheory.processBeforeStoppingTime_apply,
      hτω]
  · simp [brownianRepresentationItoIntegrand, ProbabilityTheory.processBeforeStoppingTime_apply,
      hτω]

/-- Helper for Theorem 25.22: on an extension space, the Brownian-side coefficient of a stopped
integrand is the stopped pullback of the original Brownian-side coefficient. -/
lemma pullbackBrownianRepresentationItoIntegrand_processBeforeStoppingTime_local
    {M : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    {Ω' : Type v} [MeasurableSpace Ω']
    (lift : Ω' → Ω) {H : NNReal → Ω → ℝ} {τ : Ω → ENNReal} :
    pullbackProcess lift
        (brownianRepresentationItoIntegrand hbr
          (ProbabilityTheory.processBeforeStoppingTime H τ)) =
      ProbabilityTheory.processBeforeStoppingTime
        (pullbackProcess lift (brownianRepresentationItoIntegrand hbr H))
        (fun ω' ↦ τ (lift ω')) := by
  -- Proof comment: first rewrite the base coefficient as a stopped Brownian-side integrand, then
  -- pull the stopping rule through the sample-space map.
  rw [brownianRepresentationItoIntegrand_processBeforeStoppingTime_local]
  exact pullbackProcess_processBeforeStoppingTime_local lift

/-- Helper for Theorem 25.22: measure-preserving pullback along a filtration-compatible lift
preserves local square-integrability of a continuous-time coefficient process. -/
lemma pullbackIsLocallySquareIntegrableProcess_of_measurePreserving
    {Ω' : Type v} [mΩ' : MeasurableSpace Ω']
    (law : ProbabilityMeasure Ω') (lift : Ω' → Ω)
    (filtration : Filtration NNReal mΩ')
    (hlift : MeasurePreserving lift (law : Measure Ω') μ)
    (hcomp : ∀ t : NNReal, MeasurableSpace.comap lift (ℱ t) ≤ filtration t)
    {K : NNReal → Ω → ℝ}
    (hK : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ K) :
    MeasureTheory.IsLocallySquareIntegrableProcess filtration (law : Measure Ω')
      (pullbackProcess lift K) := by
  refine ⟨?_, ?_⟩
  · intro i
    -- Proof comment: on each strip `[0, i] × Ω'`, compose the original progressive-measurability
    -- witness with the measurable map `(t, ω') ↦ (t, lift ω')`.
    have hlift_meas : Measurable[filtration i, ℱ i] lift :=
      Measurable.of_comap_le (hcomp i)
    simpa [pullbackProcess] using
      (hK.1 i).comp_measurable
        (Measurable.prodMk measurable_fst (hlift_meas.comp measurable_snd))
  · intro T
    -- Proof comment: measure preservation transfers the almost-sure interval-integrability event,
    -- and the pulled-back coefficient is definitionally the same pointwise integrand.
    filter_upwards [hlift.quasiMeasurePreserving.ae (hK.2 T)] with ω hω
    simpa [pullbackProcess] using hω

/-- Helper for Theorem 25.22: once the base-space coefficient has finite bracket energy, the same
Brownian-side coefficient remains locally square integrable after pullback to a witness space. -/
lemma pullbackBrownianRepresentationItoIntegrand_hasFiniteBracketEnergy
    {M H : NNReal → Ω → ℝ}
    {hM : ProbabilityTheory.IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    {Ω' : Type v} [mΩ' : MeasurableSpace Ω']
    (law : ProbabilityMeasure Ω') (lift : Ω' → Ω)
    (filtration : Filtration NNReal mΩ')
    (hlift : MeasurePreserving lift (law : Measure Ω') μ)
    (hcomp : ∀ t : NNReal, MeasurableSpace.comap lift (ℱ t) ≤ filtration t)
    (hH : HasFiniteBracketEnergy hbr H) :
    MeasureTheory.IsLocallySquareIntegrableProcess filtration (law : Measure Ω')
      (pullbackProcess lift (brownianRepresentationItoIntegrand hbr H)) := by
  -- Proof comment: the textbook bracket-energy hypothesis is exactly local square integrability
  -- of the Brownian-side coefficient, so the generic pullback lemma applies directly.
  exact
    pullbackIsLocallySquareIntegrableProcess_of_measurePreserving
      (μ := μ) (ℱ := ℱ) law lift filtration hlift hcomp hH

end Theorem25_22

namespace ProbabilityTheory

open Theorem25_22

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {M H N : NNReal → Ω → ℝ}

/-- Helper for Theorem 25.22: the Chapter 25 square-variation owner on the public
`ProbabilityTheory` surface. -/
abbrev HasAbsolutelyContinuousSquareVariation
    (M : NNReal → Ω → ℝ)
    (hM : IsContinuousLocalMartingale ℱ μ M) : Prop :=
  Theorem25_22.HasAbsolutelyContinuousSquareVariation M hM

/-- Helper for Theorem 25.22: the canonical bracket-density integral on the public
`ProbabilityTheory` surface. -/
abbrev bracketDensityIntegralUpTo
    {M : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  Theorem25_22.bracketDensityIntegralUpTo hbr H

/-- Helper for Theorem 25.22: the source finite-horizon square-bracket energy condition on the
public `ProbabilityTheory` surface. -/
abbrev HasFiniteBracketEnergy
    {M : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H : NNReal → Ω → ℝ) : Prop :=
  Theorem25_22.HasFiniteBracketEnergy hbr H

/-- Helper for Theorem 25.22: the canonical dyadic left-point realization of `∫ H dM` on the
base space of the continuous local martingale `M`. -/
noncomputable def continuousLocalMartingaleItoIntegralProcess
    {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (H : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun T ω ↦
    limUnder atTop <|
      Theorem25_22.partitionPathwiseItoApproximationUpTo
        (fun t ↦ H t ω)
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
        Definition2158.dyadicPartitionSequence
        T

/-- Helper for Theorem 25.22: a source-facing realization of `∫ H dM`, stated only as agreement
with the canonical base-space Itô-integral process outside one measurable null set, uniformly in
time. Brownian extensions and approximation machinery remain internal to later proof
infrastructure. -/
structure IsContinuousLocalMartingaleItoIntegral
    {M : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (H N : NNReal → Ω → ℝ) : Prop where
  indistinguishable_canonical :
    ProbabilityTheory.AreIndistinguishable μ N
      (continuousLocalMartingaleItoIntegralProcess hM H)

/-- Helper for Theorem 25.22: every martingale is a local martingale on a probability space. -/
theorem martingale_isLocalMartingale
    {M : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ) :
    IsLocalMartingale ℱ μ M := by
  refine (isLocalMartingale_iff ℱ μ M).2 ⟨hM.stronglyAdapted.adapted, ?_⟩
  let τs : ℕ → Ω → ENNReal := fun n _ ↦ (n : ENNReal)
  refine ⟨τs, ?_⟩
  refine (isLocalizingSequence_iff ℱ μ M τs).2 ⟨?_, ?_, ?_⟩
  · intro n
    simpa [τs] using isStoppingTime_const ℱ (n : NNReal)
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa [τs] using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    simpa [τs] using ENNReal.tendsto_nat_nhds_top
  · intro n
    simpa [τs] using
      martingaleUniformIntegrable_stoppedProcessConstTime
        (μ := μ) (ℱ := ℱ) hM (n : NNReal)

namespace IsContinuousLocalMartingaleItoIntegral

local notation "PathSpace" => C(NNReal, ℝ)

-- Semantic recall note: `lean_leansearch` timed out on this stochastic-integral query, so the
-- mixed-bracket clauses use the file-local quadratic-covariation process surface together with
-- the canonical Chapter 25 Itô-integral and square-variation API.
/-- Helper for Theorem 25.22: two time-indexed objects agree up to the horizon `T` if their
values coincide at every time `t ≤ T` outside one measurable `μ`-null set independent of `t`.
-/
def EqUpTo {α : Type _} (μ : Measure Ω) (T : NNReal) (X Y : NNReal → Ω → α) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
    ∀ ⦃t : NNReal⦄, t ≤ T → {ω | X t ω ≠ Y t ω} ⊆ N

/-- Helper for Theorem 25.22: indistinguishability gives equality on every finite horizon outside
one null set. -/
theorem eqUpTo_of_areIndistinguishable
    {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : ProbabilityTheory.AreIndistinguishable μ X Y) :
    EqUpTo μ T X Y := by
  -- Proof comment: the null set from indistinguishability already works for every bounded
  -- horizon because it controls all deterministic times simultaneously.
  rcases hXY with ⟨N, hNmeas, hNnull, hNsub⟩
  exact ⟨N, hNmeas, hNnull, fun _ _ ↦ hNsub _⟩

/-- Helper for Theorem 25.22: equality up to a horizon is reflexive. -/
theorem eqUpTo_rfl
    {α : Type _} (T : NNReal) (X : NNReal → Ω → α) :
    EqUpTo μ T X X := by
  -- Proof comment: there are no disagreement points between a process and itself.
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht ω hω
  simp at hω

/-- Helper for Theorem 25.22: equality up to a horizon composes transitively. -/
theorem eqUpTo_trans
    {α : Type _} {T : NNReal} {X Y Z : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) (hYZ : EqUpTo μ T Y Z) :
    EqUpTo μ T X Z := by
  -- Proof comment: outside the union of the two null sets, both comparison steps hold and hence
  -- so does their composition.
  rcases hXY with ⟨NXY, hNXY_meas, hNXY_null, hNXY_sub⟩
  rcases hYZ with ⟨NYZ, hNYZ_meas, hNYZ_null, hNYZ_sub⟩
  refine ⟨NXY ∪ NYZ, hNXY_meas.union hNYZ_meas, ?_, ?_⟩
  · have hUnionLe : μ (NXY ∪ NYZ) ≤ μ NXY + μ NYZ := measure_union_le NXY NYZ
    refine le_antisymm ?_ bot_le
    simpa [hNXY_null, hNYZ_null] using hUnionLe
  · intro t ht ω hω
    by_cases hXYω : X t ω ≠ Y t ω
    · exact Set.mem_union_left NYZ (hNXY_sub ht hXYω)
    · have hEqXY : X t ω = Y t ω := not_ne_iff.mp hXYω
      have hYZω : Y t ω ≠ Z t ω := by
        intro hEqYZ
        exact hω (hEqXY.trans hEqYZ)
      exact Set.mem_union_right NXY (hNYZ_sub ht hYZω)

/-- Helper for Theorem 25.22: equality up to a horizon is symmetric. -/
theorem eqUpTo_sym
    {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    EqUpTo μ T Y X := by
  -- Proof comment: outside the same null set, `X t ω = Y t ω` can be read in either direction.
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  exact hN_sub ht (by
    intro hEq
    exact hω hEq.symm)

/-- Helper for Theorem 25.22: an `EqUpTo` witness can be read as pointwise equality on `[0, T]`
outside one fixed measurable null set. -/
theorem eqUpTo_forall_eq
    {α : Type _} {T : NNReal} {X Y : NNReal → Ω → α}
    (hXY : EqUpTo μ T X Y) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
      ∀ ⦃t : NNReal⦄, t ≤ T → ∀ ⦃ω : Ω⦄, ω ∉ N → X t ω = Y t ω := by
  rcases hXY with ⟨N, hN_meas, hN_null, hN_sub⟩
  refine ⟨N, hN_meas, hN_null, ?_⟩
  intro t ht ω hω
  by_contra hneq
  exact hω (hN_sub ht hneq)

/-- Helper for Theorem 25.22: deterministic stopping at `T` turns an `EqUpTo` comparison on
`[0, T]` into all-times almost-sure equality of the two deterministic stops. -/
private theorem ae_eq_stoppedProcess_const_of_eqUpTo
    {T : NNReal} {X Y : NNReal → Ω → ℝ}
    (hXY : EqUpTo μ T X Y) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      stoppedProcess X (fun _ ↦ (T : ENNReal)) t ω =
        stoppedProcess Y (fun _ ↦ (T : ENNReal)) t ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hXY with
    ⟨N, hN_meas, hN_null, hN_eq⟩
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := compl_mem_ae_iff.mpr hN_null
  filter_upwards [hNae] with ω hω t
  -- Proof comment: both deterministic stops evaluate the source process at the clipped time
  -- `min t T`, which is still inside the horizon controlled by the `EqUpTo` witness.
  simpa [stoppedProcessConstTime_eq_min] using hN_eq (min_le_right t T) hω

/-- Helper for Theorem 25.22: an almost-everywhere statement can be realized outside one
measurable null set. -/
theorem ae_exists_nullSet_forall
    {P : Ω → Prop}
    (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ ⦃ω : Ω⦄, ω ∉ N → P ω := by
  classical
  let N : Set Ω := {ω | ¬ P ω}
  refine ⟨toMeasurable μ N, measurableSet_toMeasurable _ _, ?_, ?_⟩
  · -- Proof comment: the exceptional set is the measurable hull of `{ω | ¬ P ω}`, whose measure
    -- is zero because `P` holds almost everywhere.
    rw [measure_toMeasurable]
    simpa [N, ae_iff] using hP
  intro ω hω
  by_contra hPω
  exact hω (subset_toMeasurable μ N hPω)

/-- Helper for Theorem 25.22: one measurable null set can simultaneously realize two `EqUpTo`
comparisons on `[0,T]` together with any additional almost-sure property. -/
theorem existsNullSet_forall_eqUpTo_and_ae
    {α β : Type _} {T : NNReal}
    {X₁ Y₁ : NNReal → Ω → α} {X₂ Y₂ : NNReal → Ω → β} {P : Ω → Prop}
    (hEq₁ : EqUpTo μ T X₁ Y₁)
    (hEq₂ : EqUpTo μ T X₂ Y₂)
    (hP : ∀ᵐ ω ∂μ, P ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ N →
        (∀ ⦃t : NNReal⦄, t ≤ T → X₁ t ω = Y₁ t ω) ∧
        (∀ ⦃t : NNReal⦄, t ≤ T → X₂ t ω = Y₂ t ω) ∧
        P ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEq₁ with
    ⟨N₁, hN₁_meas, hN₁_null, hN₁_eq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEq₂ with
    ⟨N₂, hN₂_meas, hN₂_null, hN₂_eq⟩
  rcases ae_exists_nullSet_forall (μ := μ) hP with
    ⟨N₃, hN₃_meas, hN₃_null, hN₃_prop⟩
  have hN₁₂_null : μ (N₁ ∪ N₂) = 0 := by
    have hUnionLe : μ (N₁ ∪ N₂) ≤ μ N₁ + μ N₂ := measure_union_le N₁ N₂
    refine le_antisymm ?_ bot_le
    simpa [hN₁_null, hN₂_null] using hUnionLe
  have hN_null : μ ((N₁ ∪ N₂) ∪ N₃) = 0 := by
    have hUnionLe : μ ((N₁ ∪ N₂) ∪ N₃) ≤ μ (N₁ ∪ N₂) + μ N₃ :=
      measure_union_le (N₁ ∪ N₂) N₃
    refine le_antisymm ?_ bot_le
    simpa [hN₁₂_null, hN₃_null] using hUnionLe
  refine ⟨(N₁ ∪ N₂) ∪ N₃, (hN₁_meas.union hN₂_meas).union hN₃_meas, hN_null, ?_⟩
  intro ω hω
  have hω_not : ω ∉ N₁ ∧ ω ∉ N₂ ∧ ω ∉ N₃ := by
    simpa [Set.mem_union, not_or, and_assoc] using hω
  refine ⟨?_, ?_, hN₃_prop hω_not.2.2⟩
  · intro t ht
    exact hN₁_eq ht hω_not.1
  · intro t ht
    exact hN₂_eq ht hω_not.2.1

/-- Helper for Theorem 25.22: everywhere path continuity implies almost-sure path continuity. -/
theorem hasAlmostSurelyContinuousPaths_of_continuous
    {X : NNReal → Ω → ℝ}
    (hX : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω) :
    HasAlmostSurelyContinuousPaths μ X := by
  -- Proof comment: if every sample path is continuous, then the almost-sure continuity event is
  -- all of `Ω`.
  filter_upwards with ω
  simpa [processPath] using hX ω

/-- Helper for Theorem 25.22: `N` is a continuous local martingale up to `T` if it agrees on
`[0, T]` with some genuine continuous local martingale. -/
def IsContinuousLocalMartingaleUpTo
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (T : NNReal) (N : NNReal → Ω → ℝ) : Prop :=
  ∃ N' : NNReal → Ω → ℝ,
    IsContinuousLocalMartingale ℱ μ N' ∧ EqUpTo μ T N N'

/-- Helper for Theorem 25.22: `(N, A)` is a square-variation pair up to `T` if it agrees on
`[0, T]` with a genuine continuous square-variation process pair. -/
def IsContinuousSquareVariationProcessUpTo
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (T : NNReal) (N A : NNReal → Ω → ℝ) : Prop :=
  ∃ N' A' : NNReal → Ω → ℝ,
    IsContinuousSquareVariationProcess ℱ μ N' A' ∧
      EqUpTo μ T N N' ∧ EqUpTo μ T A A'

/-- Helper for Theorem 25.22: `(N₁, N₂, A)` is a quadratic-covariation triple up to `T` if it
agrees on `[0, T]` with a genuine continuous quadratic-covariation process triple. -/
def IsContinuousQuadraticCovariationProcessUpTo
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (T : NNReal) (N₁ N₂ A : NNReal → Ω → ℝ) : Prop :=
  ∃ N₁' N₂' A' : NNReal → Ω → ℝ,
    IsContinuousQuadraticCovariationProcess ℱ μ N₁' N₂' A' ∧
      EqUpTo μ T N₁ N₁' ∧ EqUpTo μ T N₂ N₂' ∧ EqUpTo μ T A A'

/-- Helper for Theorem 25.22: a genuine continuous local martingale can be packaged directly as an
`...UpTo` witness by using equality up to `T` with itself. -/
theorem isContinuousLocalMartingaleUpTo_of_isContinuousLocalMartingale
    {T : NNReal} {N : NNReal → Ω → ℝ}
    (hN : IsContinuousLocalMartingale ℱ μ N) :
    IsContinuousLocalMartingaleUpTo ℱ μ T N := by
  -- Proof comment: keep the given process as the genuine witness and package the horizon-wise
  -- agreement by reflexivity.
  exact ⟨N, hN, eqUpTo_rfl (μ := μ) T N⟩

/-- Helper for Theorem 25.22: a genuine square-variation pair can be packaged directly as an
`...UpTo` witness by using reflexive horizon-wise equality on both coordinates. -/
theorem isContinuousSquareVariationProcessUpTo_of_isContinuousSquareVariationProcess
    {T : NNReal} {N A : NNReal → Ω → ℝ}
    (hNA : IsContinuousSquareVariationProcess ℱ μ N A) :
    IsContinuousSquareVariationProcessUpTo ℱ μ T N A := by
  -- Proof comment: the genuine pair already has the target form, so only the two reflexive
  -- `EqUpTo` witnesses need to be recorded.
  exact ⟨N, A, hNA, eqUpTo_rfl (μ := μ) T N, eqUpTo_rfl (μ := μ) T A⟩

/-- Helper for Theorem 25.22: a genuine quadratic-covariation triple can be packaged directly as
an `...UpTo` witness by using reflexive horizon-wise equality on all three coordinates. -/
theorem isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
    {T : NNReal} {N₁ N₂ A : NNReal → Ω → ℝ}
    (hNA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ A := by
  -- Proof comment: no transport is needed when the genuine quadratic-covariation triple is
  -- already written on the target processes.
  exact
    ⟨N₁, N₂, A, hNA, eqUpTo_rfl (μ := μ) T N₁, eqUpTo_rfl (μ := μ) T N₂,
      eqUpTo_rfl (μ := μ) T A⟩

/-- Helper for Theorem 25.22: transport a local-martingale-up-to witness along horizon-wise
process equality. -/
theorem isContinuousLocalMartingaleUpTo_of_eqUpTo
    {T : NNReal} {N N' : NNReal → Ω → ℝ}
    (hN : EqUpTo μ T N N')
    (hN' : IsContinuousLocalMartingaleUpTo ℱ μ T N') :
    IsContinuousLocalMartingaleUpTo ℱ μ T N := by
  -- Proof comment: keep the same genuine local martingale witness and compose the two
  -- horizon-wise identifications.
  rcases hN' with ⟨M, hM, hEq⟩
  exact ⟨M, hM, eqUpTo_trans hN hEq⟩

/-- Helper for Theorem 25.22: transport a square-variation-up-to witness along horizon-wise
equality of both the martingale and compensator components. -/
theorem isContinuousSquareVariationProcessUpTo_of_eqUpTo
    {T : NNReal} {N N' A A' : NNReal → Ω → ℝ}
    (hN : EqUpTo μ T N N')
    (hA : EqUpTo μ T A A')
    (hNA : IsContinuousSquareVariationProcessUpTo ℱ μ T N' A') :
    IsContinuousSquareVariationProcessUpTo ℱ μ T N A := by
  -- Proof comment: reuse the same genuine square-variation pair and compose the two equality
  -- bridges separately.
  rcases hNA with ⟨M, B, hMB, hEqN, hEqA⟩
  exact ⟨M, B, hMB, eqUpTo_trans hN hEqN, eqUpTo_trans hA hEqA⟩

/-- Helper for Theorem 25.22: transport a quadratic-covariation-up-to witness along horizon-wise
equality of both integrals and the compensator. -/
theorem isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
    {T : NNReal} {N₁ N₁' N₂ N₂' A A' : NNReal → Ω → ℝ}
    (hN₁ : EqUpTo μ T N₁ N₁')
    (hN₂ : EqUpTo μ T N₂ N₂')
    (hA : EqUpTo μ T A A')
    (hNA : IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁' N₂' A') :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ A := by
  -- Proof comment: keep the same genuine quadratic-covariation triple and compose each
  -- coordinate-wise equality bridge with its witness comparison.
  rcases hNA with ⟨M₁, M₂, B, hMB, hEq₁, hEq₂, hEqA⟩
  exact ⟨M₁, M₂, B, hMB, eqUpTo_trans hN₁ hEq₁, eqUpTo_trans hN₂ hEq₂, eqUpTo_trans hA hEqA⟩

/-- Helper for Theorem 25.22: a genuine pointwise limit of the dyadic left-point sums identifies
the canonical `limUnder` realization `continuousLocalMartingaleItoIntegralProcess`. -/
theorem continuousLocalMartingaleItoIntegralProcess_eq_of_tendsto
    {M H I : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hI :
      ∀ T : NNReal, ∀ ω : Ω,
        Tendsto
          (fun n ↦
            Theorem25_22.partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              T
              n)
          atTop
          (𝓝 (I T ω))) :
    continuousLocalMartingaleItoIntegralProcess hM H = I := by
  -- Proof comment: the canonical dyadic Itô process is defined pointwise by `limUnder`, so any
  -- actual limit of those dyadic sums determines the same value at each horizon and sample point.
  funext T ω
  simpa [continuousLocalMartingaleItoIntegralProcess] using (hI T ω).limUnder_eq

/-- Helper for Theorem 25.22: a genuine pointwise limit of the dyadic mixed-increment sums
identifies the canonical pathwise quadratic-covariation integral on the base space. -/
theorem quadraticCovariationIntegralUpTo_eq_of_tendsto
    {M N H K A : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hN : IsContinuousLocalMartingale ℱ μ N}
    (hA :
      ∀ T : NNReal, ∀ ω : Ω,
        Tendsto
          (fun n ↦
            Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
              (fun s ↦ H s ω * K s ω)
              (⟨fun s ↦ M s ω, hM.continuous ω⟩ : C(NNReal, ℝ))
              (⟨fun s ↦ N s ω, hN.continuous ω⟩ : C(NNReal, ℝ))
              T
              n)
          atTop
          (𝓝 (A T ω))) :
    Theorem25_22.quadraticCovariationIntegralUpTo hM hN H K = A := by
  -- Proof comment: the mixed bracket integral was also defined by `limUnder`, so a pointwise
  -- dyadic limit pins down the same canonical value at every horizon and sample point.
  funext T ω
  simpa [Theorem25_22.quadraticCovariationIntegralUpTo,
    Theorem25_22.pathwiseQuadraticCovariationIntegral] using (hA T ω).limUnder_eq

/-- Helper for Theorem 25.22: a genuine pointwise limit of the dyadic mixed-increment sums on
path space identifies the canonical pathwise quadratic-covariation integral. -/
theorem pathwiseQuadraticCovariationIntegral_eq_of_tendsto
    {H : NNReal → ℝ} {F G : PathSpace} {A : NNReal → ℝ}
    (hA :
      ∀ T : NNReal,
        Tendsto
          (fun n ↦
            Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
              H F G T n)
          atTop
          (𝓝 (A T))) :
    Theorem25_22.pathwiseQuadraticCovariationIntegral H F G = A := by
  -- Proof comment: the pathwise quadratic-covariation integral is also defined by `limUnder`, so
  -- any actual dyadic mixed-sum limit determines the same pathwise process.
  funext T
  simpa [Theorem25_22.pathwiseQuadraticCovariationIntegral] using (hA T).limUnder_eq

/-- Helper for Theorem 25.22: at one fixed horizon `T`, the canonical Itô value only depends on
the integrand on `Set.Icc 0 T`. -/
private lemma continuousLocalMartingaleItoIntegralProcess_eq_of_eqOn_Icc_local
    {M K L : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {T : NNReal} {ω : Ω}
    (hKL : Set.EqOn (fun t : NNReal ↦ K t ω) (fun t ↦ L t ω) (Set.Icc 0 T)) :
    continuousLocalMartingaleItoIntegralProcess hM K T ω =
      continuousLocalMartingaleItoIntegralProcess hM L T ω := by
  let X : PathSpace := ⟨fun t ↦ M t ω, hM.continuous ω⟩
  have hRows :
      Theorem25_22.partitionPathwiseItoApproximationUpTo
          (fun t ↦ K t ω)
          X
          Definition2158.dyadicPartitionSequence
          T =
        Theorem25_22.partitionPathwiseItoApproximationUpTo
          (fun t ↦ L t ω)
          X
          Definition2158.dyadicPartitionSequence
          T := by
    -- Proof comment: every dyadic left endpoint contributing to the time-`T` row lies in
    -- `Set.Icc 0 T`, so the interval-wise coefficient identity rewrites the whole row family.
    funext row
    exact
      Theorem25_22.partitionPathwiseItoApproximationUpTo_congrOn_Icc
        (P := Definition2158.dyadicPartitionSequence)
        (X := X)
        (T := T)
        hKL
        row
  -- Proof comment: the canonical fixed-time Itô value is defined as the `limUnder` of those
  -- dyadic rows, so equality of the entire row family identifies the two values.
  simpa [continuousLocalMartingaleItoIntegralProcess] using
    congrArg (limUnder atTop) hRows

/-- Helper for Theorem 25.22: at the fixed horizon `T`, the canonical Itô value of `H` agrees
pointwise with the canonical Itô value of the deterministic cutoff of `H` at `T`. -/
private lemma continuousLocalMartingaleItoIntegralProcess_eq_constCutoff_value
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal) (ω : Ω) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
        T ω =
      continuousLocalMartingaleItoIntegralProcess hM H T ω := by
  -- Proof comment: on the active interval `[0, T]`, the deterministic cutoff already agrees
  -- pointwise with `H`, so the fixed-time interval-identification lemma applies directly.
  exact
    continuousLocalMartingaleItoIntegralProcess_eq_of_eqOn_Icc_local
      (μ := μ) (ℱ := ℱ) (M := M)
      (hM := hM)
      (T := T)
      (ω := ω)
      (Theorem25_22.processBeforeStoppingTime_const_eqOn_Icc (H := H) T ω)

/-- Helper for Theorem 25.22: a self-quadratic-covariation witness is already a square-variation
pathwise witness. -/
theorem hasSquareVariationAlong_of_selfQuadraticCovariationAlong
    {F : PathSpace} {VF : NNReal → ℝ}
    (hF : HasQuadraticCovariationAlong F F VF) :
    HasSquareVariationAlong F VF := by
  intro T
  -- Proof comment: on the diagonal, the mixed dyadic row is literally the square-variation row,
  -- so the pathwise mixed-limit hypothesis already gives the square-variation limit.
  convert HasQuadraticCovariationAlong.tendsto_partition_sum hF T using 1
  ext n
  rw [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum, partitionPVariationSum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [sq_abs]
  ring

/-- Helper for Theorem 25.22: deterministically cutting off `H` at time `T` does not change the
canonical dyadic Itô realization on the whole horizon `[0, T]`. -/
theorem continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal) :
    EqUpTo μ T
      (continuousLocalMartingaleItoIntegralProcess hM H)
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht ω hω
  have hSeq :
      (fun n ↦
        Theorem25_22.partitionPathwiseItoApproximationUpTo
          (fun s ↦ H s ω)
          (⟨fun s ↦ M s ω, hM.continuous ω⟩ : C(NNReal, ℝ))
          Definition2158.dyadicPartitionSequence
          t
          n) =
        (fun n ↦
          Theorem25_22.partitionPathwiseItoApproximationUpTo
            (fun s ↦ processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M s ω, hM.continuous ω⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            t
            n) := by
    funext n
    -- Proof comment: every left endpoint in the dyadic sum up to `t ≤ T` lies inside
    -- `Set.Icc 0 t`, where the deterministic cutoff agrees with `H`.
    exact
      (Theorem25_22.partitionPathwiseItoApproximationUpTo_congrOn_Icc
        (P := Definition2158.dyadicPartitionSequence)
        (X := (⟨fun s ↦ M s ω, hM.continuous ω⟩ : C(NNReal, ℝ)))
        (T := t)
        (row := n)
        (hKL := fun {s} hs ↦
          let hs_mem_T : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.trans ht⟩
          (Theorem25_22.processBeforeStoppingTime_const_eqOn_Icc (H := H) T ω)
            hs_mem_T)).symm
  have hEq :
      continuousLocalMartingaleItoIntegralProcess hM H t ω =
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) t ω := by
    simpa [continuousLocalMartingaleItoIntegralProcess] using
      congrArg (limUnder atTop) hSeq
  exact hω hEq

/-- Helper for Theorem 25.22: deterministically cutting off `H` at time `T` does not change the
bracket-density compensator on the whole horizon `[0, T]`. -/
theorem bracketDensityIntegralUpTo_eqUpTo_constCutoff
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (hbr : HasAbsolutelyContinuousSquareVariation M hM)
    (T : NNReal) :
    EqUpTo μ T
      (bracketDensityIntegralUpTo hbr H)
      (bracketDensityIntegralUpTo hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht ω hω
  have hEq :
      bracketDensityIntegralUpTo hbr H t ω =
        bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) t ω := by
    rw [bracketDensityIntegralUpTo, bracketDensityIntegralUpTo]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hs_le_T : s ≤ T := hs.2.trans ht
    have hsTnn : s.toNNReal ≤ T :=
      (Real.toNNReal_le_iff_le_coe).2 hs_le_T
    have hsT : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
      exact_mod_cast hsTnn
    -- Proof comment: inside the integration window `s ∈ [0,t] ⊆ [0,T]`, the deterministic
    -- cutoff leaves the integrand untouched.
    simp [ProbabilityTheory.processBeforeStoppingTime_apply, hsT]
  exact hω hEq

/-- Helper for Theorem 25.22: deterministically cutting off both coefficients at time `T` does
not change the canonical mixed bracket integral on `[0, T]`. -/
theorem quadraticCovariationIntegralUpTo_eqUpTo_constCutoffs
    {M N H K : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hN : IsContinuousLocalMartingale ℱ μ N}
    (T : NNReal) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM hN H K)
      (Theorem25_22.quadraticCovariationIntegralUpTo hM hN
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime K fun _ ↦ (T : ENNReal))) := by
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht ω hω
  have hSeq :
      (fun n ↦
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
          (fun s ↦ H s ω * K s ω)
          (⟨fun s ↦ M s ω, hM.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ N s ω, hN.continuous ω⟩ : C(NNReal, ℝ))
          t
          n) =
        (fun n ↦
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (fun s ↦
              processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s ω *
                processBeforeStoppingTime K (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M s ω, hM.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ N s ω, hN.continuous ω⟩ : C(NNReal, ℝ))
            t
            n) := by
    funext n
    -- Proof comment: the mixed weight uses only left endpoints from `Set.Icc 0 t`, where both
    -- deterministic cutoffs agree with the original coefficients.
    exact
      (Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo_congrOn_Icc
        (T := t)
        (n := n)
        (F := (⟨fun s ↦ M s ω, hM.continuous ω⟩ : C(NNReal, ℝ)))
        (G := (⟨fun s ↦ N s ω, hN.continuous ω⟩ : C(NNReal, ℝ)))
        (hKL := fun s hs ↦ by
          have hsH :
              processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s ω = H s ω :=
            (Theorem25_22.processBeforeStoppingTime_const_eqOn_Icc (H := H) T ω)
              ⟨hs.1, hs.2.trans ht⟩
          have hsK :
              processBeforeStoppingTime K (fun _ ↦ (T : ENNReal)) s ω = K s ω :=
            (Theorem25_22.processBeforeStoppingTime_const_eqOn_Icc (H := K) T ω)
              ⟨hs.1, hs.2.trans ht⟩
          rw [hsH, hsK])).symm
  have hEq :
      Theorem25_22.quadraticCovariationIntegralUpTo hM hN H K t ω =
        Theorem25_22.quadraticCovariationIntegralUpTo hM hN
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime K fun _ ↦ (T : ENNReal)) t ω := by
    simpa [Theorem25_22.quadraticCovariationIntegralUpTo,
      Theorem25_22.pathwiseQuadraticCovariationIntegral] using
      congrArg (limUnder atTop) hSeq
  exact hω hEq

/-- Helper for Theorem 25.22: the weighted dyadic square-variation sum on `[0, T]` along the
canonical dyadic partition. -/
noncomputable def weightedDyadicQuadraticVariationApproximationUpTo
    (H : NNReal → ℝ) (X : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum
    (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    fun k ↦
      H (Definition2158.dyadicPartitionSequence n k) *
        (X (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          X (Definition2158.dyadicPartitionSequence n k)) ^ 2

/-- Helper for Theorem 25.22: the dyadic mixed sums are the weighted polarization of the weighted
dyadic square-variation sums of `Y + Z` and `Y - Z`. -/
theorem dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization
    (H : NNReal → ℝ) (Y Z : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n =
      (1 / 4 : ℝ) *
        (weightedDyadicQuadraticVariationApproximationUpTo
            H
            (Y + Z)
            T
            n -
          weightedDyadicQuadraticVariationApproximationUpTo
            H
            (Y - Z)
            T
            n) := by
  let s := Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)
  let addTerm : ℕ → ℝ := fun k ↦
    H (Definition2158.dyadicPartitionSequence n k) *
      (((Y + Z) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          (Y + Z) (Definition2158.dyadicPartitionSequence n k)) ^ 2)
  let subTerm : ℕ → ℝ := fun k ↦
    H (Definition2158.dyadicPartitionSequence n k) *
      (((Y - Z) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          (Y - Z) (Definition2158.dyadicPartitionSequence n k)) ^ 2)
  have hterm :
      ∀ k ∈ s,
        H (Definition2158.dyadicPartitionSequence n k) *
            (Y (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              Y (Definition2158.dyadicPartitionSequence n k)) *
            (Z (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              Z (Definition2158.dyadicPartitionSequence n k)) =
          (addTerm k - subTerm k) / 4 := by
    intro k hk
    simp only [addTerm, subTerm, ContinuousMap.add_apply, ContinuousMap.sub_apply]
    ring
  calc
    Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n
        = Finset.sum s (fun k ↦ (addTerm k - subTerm k) / 4) := by
            rw [Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo]
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hterm k (by simpa [s] using hk)
    _ = (Finset.sum s addTerm - Finset.sum s subTerm) / 4 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ =
        (weightedDyadicQuadraticVariationApproximationUpTo
            H
            (Y + Z)
            T
            n -
          weightedDyadicQuadraticVariationApproximationUpTo
            H
            (Y - Z)
            T
            n) / 4 := by
      have haddSum :
          Finset.sum s addTerm =
            weightedDyadicQuadraticVariationApproximationUpTo
              H
              (Y + Z)
              T
              n := by
        rfl
      have hsubSum :
          Finset.sum s subTerm =
            weightedDyadicQuadraticVariationApproximationUpTo
              H
              (Y - Z)
              T
              n := by
        rfl
      rw [haddSum, hsubSum]
    _ =
        (1 / 4 : ℝ) *
          (weightedDyadicQuadraticVariationApproximationUpTo
              H
              (Y + Z)
              T
              n -
            weightedDyadicQuadraticVariationApproximationUpTo
              H
              (Y - Z)
              T
              n) := by
      ring

/-- Helper for Theorem 25.22: once the weighted square-variation sums of `Y + Z` and `Y - Z`
converge, the weighted mixed dyadic sums converge to their polarized difference. -/
theorem tendsto_dyadicQuadraticCovariationIntegralApproximationUpTo_of_weightedPolarization
    {H : NNReal → ℝ} {Y Z : C(NNReal, ℝ)} {T : NNReal} {Aadd Asub : ℝ}
    (hAdd :
      Tendsto
        (fun n ↦ weightedDyadicQuadraticVariationApproximationUpTo H (Y + Z) T n)
        atTop
        (𝓝 Aadd))
    (hSub :
      Tendsto
        (fun n ↦ weightedDyadicQuadraticVariationApproximationUpTo H (Y - Z) T n)
        atTop
        (𝓝 Asub)) :
    Tendsto
      (fun n ↦ Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
      atTop
      (𝓝 ((1 / 4 : ℝ) * (Aadd - Asub))) := by
  have hPolarized :
      Tendsto
        (fun n ↦
          (1 / 4 : ℝ) *
            (weightedDyadicQuadraticVariationApproximationUpTo H (Y + Z) T n -
              weightedDyadicQuadraticVariationApproximationUpTo H (Y - Z) T n))
        atTop
        (𝓝 ((1 / 4 : ℝ) * (Aadd - Asub))) :=
    (hAdd.sub hSub).const_mul (1 / 4 : ℝ)
  -- Proof comment: rewrite every mixed dyadic sum through the polarization identity and then use
  -- ordinary limit arithmetic on the two weighted square-variation sequences.
  exact
    Tendsto.congr' (Filter.Eventually.of_forall fun n ↦
      (dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization H Y Z T n).symm)
      hPolarized

/-- Helper for Theorem 25.22: a uniform bound on two weights controls the difference of the
corresponding mixed dyadic sums by the unweighted plus/minus square rows. -/
private theorem abs_sub_dyadicQuadraticCovariationIntegralApproximationUpTo_le
    (g h : NNReal → ℝ) (Y Z : C(NNReal, ℝ)) (T : NNReal) (ε : ℝ)
    (hε : ∀ s ∈ Set.Icc 0 T, |g s - h s| ≤ ε)
    (n : ℕ) :
    |Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo g Y Z T n -
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo h Y Z T n| ≤
      (ε / 4 : ℝ) *
        (weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y + Z) T n +
          weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y - Z) T n) := by
  have hε_nonneg : 0 ≤ ε := by
    have hzero :
        |g 0 - h 0| ≤ ε := hε 0 ⟨le_rfl, bot_le⟩
    exact le_trans (abs_nonneg _) hzero
  have hAdd :
      |weightedDyadicQuadraticVariationApproximationUpTo g (Y + Z) T n -
          weightedDyadicQuadraticVariationApproximationUpTo h (Y + Z) T n| ≤
        ε * weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y + Z) T n := by
    -- Proof comment: apply the Chapter 21 weighted square-row error bound to the plus path.
    simpa [weightedDyadicQuadraticVariationApproximationUpTo,
      weightedDyadicSquareVariationSum]
      using abs_sub_weightedDyadicSquareVariationSum_le g h (Y + Z) T ε hε n
  have hSub :
      |weightedDyadicQuadraticVariationApproximationUpTo g (Y - Z) T n -
          weightedDyadicQuadraticVariationApproximationUpTo h (Y - Z) T n| ≤
        ε * weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y - Z) T n := by
    -- Proof comment: the same weighted square-row estimate applies to the minus path.
    simpa [weightedDyadicQuadraticVariationApproximationUpTo,
      weightedDyadicSquareVariationSum]
      using abs_sub_weightedDyadicSquareVariationSum_le g h (Y - Z) T ε hε n
  let dAdd :=
    weightedDyadicQuadraticVariationApproximationUpTo g (Y + Z) T n -
      weightedDyadicQuadraticVariationApproximationUpTo h (Y + Z) T n
  let dSub :=
    weightedDyadicQuadraticVariationApproximationUpTo g (Y - Z) T n -
      weightedDyadicQuadraticVariationApproximationUpTo h (Y - Z) T n
  have hRewrite :
      Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo g Y Z T n -
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo h Y Z T n =
        (1 / 4 : ℝ) * (dAdd - dSub) := by
    -- Proof comment: rewrite both mixed rows through the polarization identity and collect the
    -- plus/minus square-row errors into `dAdd - dSub`.
    rw [dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization,
      dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization]
    simp [dAdd, dSub]
    ring
  have hTriangle : |dAdd - dSub| ≤ |dAdd| + |dSub| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using abs_sub_le dAdd 0 dSub
  calc
    |Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo g Y Z T n -
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo h Y Z T n|
        = |(1 / 4 : ℝ) * (dAdd - dSub)| := by rw [hRewrite]
    _ = (1 / 4 : ℝ) * |dAdd - dSub| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (1 / 4 : ℝ) * (|dAdd| + |dSub|) := by
          gcongr
    _ ≤ (1 / 4 : ℝ) *
          (ε * weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y + Z) T n +
            ε * weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y - Z) T n) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
          · simpa [dAdd] using hAdd
          · simpa [dSub] using hSub
    _ = (ε / 4 : ℝ) *
          (weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y + Z) T n +
            weightedDyadicQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) (Y - Z) T n) := by
          ring

/-- Helper for Theorem 25.22: the theorem-local weighted dyadic square-sum notation is exactly
the Chapter 21 `weightedDyadicSquareVariationSum`. -/
theorem weightedDyadicQuadraticVariationApproximationUpTo_eq_weightedDyadicSquareVariationSum
    (H : NNReal → ℝ) (X : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    weightedDyadicQuadraticVariationApproximationUpTo H X T n =
      weightedDyadicSquareVariationSum H X T n := by
  -- Proof comment: both names unfold to the same dyadic finite sum of weighted squared
  -- increments.
  rfl

/-- Helper for Theorem 25.22: the explicit coarse-step square-variation limit associated with one
chosen square-variation realization. -/
noncomputable def coarseIccStepSquareVariationLimit
    (w : NNReal → ℝ) (m : ℕ) (T : NNReal) (V : NNReal → ℝ) : ℝ :=
  w (Definition2158.dyadicPartitionSequence m
      (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) * V T +
    Finset.sum
      (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
      (fun i ↦
        (w (Definition2158.dyadicPartitionSequence m i) -
            w (Definition2158.dyadicPartitionSequence m (i + 1))) *
          V (Definition2158.dyadicPartitionSequence m (i + 1)))

/-- Helper for Theorem 25.22: once the plus and minus paths carry fixed square-variation
realizations, every fixed dyadic coarse-step weight has the expected polarized mixed-row limit. -/
theorem tendsto_constCutoffWeightedMixedRow_of_fixedCoarseStep
    {M₁ M₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {ω : Ω} {t : NNReal}
    (w : NNReal → ℝ) (m : ℕ)
    {brAdd brSub : NNReal → ℝ}
    (hBrAdd :
      HasSquareVariationAlong
        (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
          C(NNReal, ℝ))
        brAdd)
    (hBrSub :
      HasSquareVariationAlong
        (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
          C(NNReal, ℝ))
        brSub) :
    Tendsto
      (fun n ↦
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
          (dyadicCoarseIccStep w m t)
          (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
          t
          n)
      atTop
      (𝓝
        ((1 / 4 : ℝ) *
          (coarseIccStepSquareVariationLimit w m t brAdd -
            coarseIccStepSquareVariationLimit w m t brSub))) := by
  let Y : C(NNReal, ℝ) := ⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩
  let Z : C(NNReal, ℝ) := ⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩
  have hAdd :
      Tendsto
        (fun n ↦
          weightedDyadicQuadraticVariationApproximationUpTo
            (dyadicCoarseIccStep w m t)
            (Y + Z)
            t
            n)
        atTop
        (𝓝 (coarseIccStepSquareVariationLimit w m t brAdd)) := by
    -- Proof comment: the Chapter 21 coarse-step theorem already computes the dyadic square-sum
    -- limit for the plus path; the adapter lemma only normalizes the local notation.
    simpa [Y, Z, coarseIccStepSquareVariationLimit,
      weightedDyadicQuadraticVariationApproximationUpTo_eq_weightedDyadicSquareVariationSum] using
      (tendsto_weightedDyadicSquareVariationSum_coarseIccStep_linearCombination
        w hBrAdd m t)
  have hSub :
      Tendsto
        (fun n ↦
          weightedDyadicQuadraticVariationApproximationUpTo
            (dyadicCoarseIccStep w m t)
            (Y - Z)
            t
            n)
        atTop
        (𝓝 (coarseIccStepSquareVariationLimit w m t brSub)) := by
    -- Proof comment: the same fixed coarse-step formula applies to the minus path.
    simpa [Y, Z, coarseIccStepSquareVariationLimit,
      weightedDyadicQuadraticVariationApproximationUpTo_eq_weightedDyadicSquareVariationSum] using
      (tendsto_weightedDyadicSquareVariationSum_coarseIccStep_linearCombination
        w hBrSub m t)
  -- Proof comment: after the two square-variation limits are in hand, the mixed dyadic row is
  -- the polarized quarter-difference of those two rows.
  simpa [Y, Z] using
    (tendsto_dyadicQuadraticCovariationIntegralApproximationUpTo_of_weightedPolarization
      (H := dyadicCoarseIccStep w m t)
      (Y := Y) (Z := Z) (T := t)
      (Aadd := coarseIccStepSquareVariationLimit w m t brAdd)
      (Asub := coarseIccStepSquareVariationLimit w m t brSub)
      hAdd hSub)

/-- Helper for Theorem 25.22: after any prescribed dyadic level, some finer dyadic coarse-step
row still uniformly approximates a continuous weight on `[0,T]`. -/
private theorem exists_ge_dyadicCoarseIccStep_uniformApprox
    (w : NNReal → ℝ) (hw : Continuous w)
    (T : NNReal) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ m ≥ N, ∀ s ∈ Set.Icc 0 T, |w s - dyadicCoarseIccStep w m T s| ≤ ε := by
  have hUC :
      UniformContinuousOn w (Set.Icc 0 T) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).uniformContinuousOn_of_continuous
      hw.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hUC) ε hε with ⟨δ, hδ, hδclose⟩
  have hmesh :
      ∀ᶠ m in atTop,
        partitionMesh Definition2158.dyadicPartitionSequence m ≤ ENNReal.ofReal δ := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) with
      ⟨M, hM⟩
    exact Filter.eventually_atTop.2 ⟨M, hM⟩
  rcases Filter.eventually_atTop.1 hmesh with ⟨M, hM⟩
  let m := max N M
  have hm0 :
      partitionMesh Definition2158.dyadicPartitionSequence m ≤ ENNReal.ofReal δ :=
    hM m (le_max_right _ _)
  refine ⟨m, le_max_left _ _, ?_⟩
  intro s hs
  have hpred_mem : dyadicPartitionPredecessorPoint m s ∈ Set.Icc 0 T := by
    constructor
    · exact bot_le
    · exact le_trans (dyadicPartitionPredecessorPoint_le_time m s) hs.2
  have hpred_dist :
      dist s (dyadicPartitionPredecessorPoint m s) ≤ δ := by
    have hedist :
        edist s (dyadicPartitionPredecessorPoint m s) ≤
          partitionMesh Definition2158.dyadicPartitionSequence m := by
      simpa [edist_comm] using dyadicPartitionPredecessorPointWithinMesh m s
    have hedist' :
        edist s (dyadicPartitionPredecessorPoint m s) ≤ ENNReal.ofReal δ :=
      le_trans hedist hm0
    exact
      (ENNReal.ofReal_le_ofReal_iff hδ.le).mp
        (by simpa [edist_dist] using hedist')
  have hclose :
      dist (w s) (w (dyadicPartitionPredecessorPoint m s)) ≤ ε :=
    hδclose s hs (dyadicPartitionPredecessorPoint m s) hpred_mem hpred_dist
  -- Proof comment: once the chosen dyadic row is beyond the mesh threshold, its staircase value
  -- is exactly the predecessor-point sample, so uniform continuity closes the estimate.
  simpa [Real.dist_eq, m, dyadicCoarseIccStep_eq_partitionPredecessorValue w m T s hs] using hclose

/-- Helper for Theorem 25.22: for a continuous weight, sufficiently fine dyadic coarse-step rows
are eventually close to the original mixed dyadic row. -/
private theorem eventuallyClose_dyadicQuadraticCovariationIntegralApproximationUpTo_of_continuousWeight
    {Y Z : C(NNReal, ℝ)} {brAdd brSub : NNReal → ℝ}
    (w : NNReal → ℝ) (hw : Continuous w) (T : NNReal)
    (hAdd : HasSquareVariationAlong (Y + Z) brAdd)
    (hSub : HasSquareVariationAlong (Y - Z) brSub) :
    ∀ ε > 0, ∀ N : ℕ, ∃ m ≥ N,
      ∀ᶠ n in atTop,
        |Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo w Y Z T n -
            Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
              (dyadicCoarseIccStep w m T) Y Z T n| < ε := by
  intro ε hε N
  let B : ℝ := (|brAdd T| + 1) + (|brSub T| + 1)
  let η : ℝ := ε / (B + 1)
  have hηpos : 0 < η := by
    dsimp [η, B]
    positivity
  rcases exists_ge_dyadicCoarseIccStep_uniformApprox w hw T hηpos N with ⟨m, hmN, hmApprox⟩
  have hAddBound :
      ∀ᶠ n in atTop,
        weightedDyadicQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (Y + Z) T n ≤
          |brAdd T| + 1 := by
    -- Proof comment: the plus square-row masses are eventually trapped by their pathwise limit.
    simpa [weightedDyadicQuadraticVariationApproximationUpTo_eq_weightedDyadicSquareVariationSum]
      using eventually_le_weightedDyadicSquareVariationSum_one_abs_add_one hAdd T
  have hSubBound :
      ∀ᶠ n in atTop,
        weightedDyadicQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (Y - Z) T n ≤
          |brSub T| + 1 := by
    -- Proof comment: the same eventual mass bound holds for the minus square-row sequence.
    simpa [weightedDyadicQuadraticVariationApproximationUpTo_eq_weightedDyadicSquareVariationSum]
      using eventually_le_weightedDyadicSquareVariationSum_one_abs_add_one hSub T
  refine ⟨m, hmN, ?_⟩
  filter_upwards [hAddBound, hSubBound] with n hnAdd hnSub
  have hDiffLe :
      |Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo w Y Z T n -
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (dyadicCoarseIccStep w m T) Y Z T n| ≤
        (η / 4 : ℝ) *
          (weightedDyadicQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) (Y + Z) T n +
            weightedDyadicQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) (Y - Z) T n) := by
    -- Proof comment: uniform coefficient control turns directly into a dyadic mixed-row error
    -- bound through the polarized plus/minus estimate.
    simpa [η] using
      abs_sub_dyadicQuadraticCovariationIntegralApproximationUpTo_le
        w (dyadicCoarseIccStep w m T) Y Z T η hmApprox n
  have hMassLe :
      weightedDyadicQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (Y + Z) T n +
          weightedDyadicQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (Y - Z) T n ≤
        B := by
    dsimp [B]
    linarith
  have hLe :
      |Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo w Y Z T n -
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (dyadicCoarseIccStep w m T) Y Z T n| ≤
        (η / 4 : ℝ) * B := by
    refine le_trans hDiffLe ?_
    have hηnonneg : 0 ≤ η / 4 := by
      dsimp [η, B]
      positivity
    gcongr
  have hTargetLe : (η / 4 : ℝ) * B ≤ ε / 4 := by
    have hBnonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hBle : B ≤ B + 1 := by
      linarith
    have hηnonneg : 0 ≤ η / 4 := by
      dsimp [η, B]
      positivity
    have hBplus : B + 1 ≠ 0 := by
      have : 0 < B + 1 := by
        linarith
      linarith
    calc
      (η / 4 : ℝ) * B ≤ (η / 4 : ℝ) * (B + 1) := by
        gcongr
      _ = ε / 4 := by
        dsimp [η]
        field_simp [hBplus]
  have hQuarter : ε / 4 < ε := by
    nlinarith
  -- Proof comment: the unweighted plus/minus dyadic masses are eventually bounded, so choosing a
  -- sufficiently fine coarse-step row makes the mixed-row coefficient error uniformly small.
  exact lt_of_le_of_lt hLe (lt_of_le_of_lt hTargetLe hQuarter)

/-- Helper for Theorem 25.22: the finite-horizon single clauses for `H` reduce to the same
clauses for the deterministic cutoff `H 1_[0,T]`. -/
theorem canonicalItoIntegral_singleClausesUpTo_of_constCutoff
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    {T : NNReal}
    (hCut :
      IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H)
        (bracketDensityIntegralUpTo hbr H) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: transport the cutoff witness back to the original integrand using the
    -- horizon-wise equality of the two canonical dyadic realizations.
    exact
      isContinuousLocalMartingaleUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) T)
        hCut.1
  · -- Proof comment: the martingale coordinate and the compensator both agree with their
    -- deterministic-cutoff versions on `[0,T]`, so the square-variation witness transports.
    exact
      isContinuousSquareVariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) T)
        (bracketDensityIntegralUpTo_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) hbr T)
        hCut.2

/-- Helper for Theorem 25.22: the finite-horizon mixed clauses for `H₁`, `H₂` reduce to the same
clauses for their deterministic cutoffs `H₁ 1_[0,T]`, `H₂ 1_[0,T]`. -/
theorem canonicalItoIntegral_quadraticCovariationClausesUpTo_of_constCutoffs
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    {T : NNReal}
    (hCut :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            (continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
            (continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
            0)) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
      ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: transport the left-to-right cutoff witness through the horizon-wise
    -- equalities of both canonical integrals and their canonical mixed compensator.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M₁) (H := H₁) (hM := hM₁) T)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M₂) (H := H₂) (hM := hM₂) T)
        (quadraticCovariationIntegralUpTo_eqUpTo_constCutoffs
          (μ := μ) (ℱ := ℱ) (M := M₁) (N := M₂) (H := H₁) (K := H₂)
          (hM := hM₁) (hN := hM₂) T)
        hCut.1
  · -- Proof comment: the reverse mixed clause transports in the same way with the roles swapped.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M₂) (H := H₂) (hM := hM₂) T)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M₁) (H := H₁) (hM := hM₁) T)
        (quadraticCovariationIntegralUpTo_eqUpTo_constCutoffs
          (μ := μ) (ℱ := ℱ) (M := M₂) (N := M₁) (H := H₂) (K := H₁)
          (hM := hM₂) (hN := hM₁) T)
        hCut.2.1
  · intro hIndep
    -- Proof comment: the zero mixed-bracket clause depends only on the two canonical integral
    -- coordinates, so the same cutoff-to-original transport applies.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M₁) (H := H₁) (hM := hM₁) T)
        (continuousLocalMartingaleItoIntegralProcess_eqUpTo_constCutoff
          (μ := μ) (ℱ := ℱ) (M := M₂) (H := H₂) (hM := hM₂) T)
        (eqUpTo_rfl (μ := μ) T 0)
        (hCut.2.2 hIndep)

/-- Helper for Theorem 25.22: once one owner realization carries the finite-horizon single
clauses, the canonical dyadic realization inherits them by transport along indistinguishability.
-/
theorem canonicalItoIntegral_singleClausesUpTo_of_owner
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    {T : NNReal}
    (hN : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr H N)
    (hSingle :
      IsContinuousLocalMartingaleUpTo ℱ μ T N ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T N (bracketDensityIntegralUpTo hbr H)) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H)
        (bracketDensityIntegralUpTo hbr H) := by
  have hEq :
      EqUpTo μ T (continuousLocalMartingaleItoIntegralProcess hM H) N :=
    eqUpTo_sym <| eqUpTo_of_areIndistinguishable (μ := μ) (T := T)
      hN.indistinguishable_canonical
  refine ⟨?_, ?_⟩
  · -- Proof comment: transport the owner's local-martingale witness back to the canonical
    -- process through the finite-horizon equality.
    exact isContinuousLocalMartingaleUpTo_of_eqUpTo (μ := μ) (ℱ := ℱ) hEq hSingle.1
  · -- Proof comment: the compensator is already written in the canonical source form, so only the
    -- martingale coordinate needs transport.
    exact
      isContinuousSquareVariationProcessUpTo_of_eqUpTo (μ := μ) (ℱ := ℱ) hEq
        (eqUpTo_rfl (μ := μ) T (bracketDensityIntegralUpTo hbr H)) hSingle.2

/-- Helper for Theorem 25.22: the canonical dyadic realization is itself a valid owner witness for
the source-facing Itô-integral predicate. -/
theorem canonicalSelf
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM} :
    _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr H
      (continuousLocalMartingaleItoIntegralProcess hM H) := by
  -- Proof comment: the source-facing owner relation only asks for indistinguishability with the
  -- canonical dyadic realization, so the canonical process witnesses itself outside the empty
  -- null set.
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ω hω
  simp at hω

/-- Helper for Theorem 25.22: once a finite-horizon owner witness exists, the canonical dyadic
realization inherits the same single-integral clauses by the established owner-to-canonical
transport. -/
theorem canonicalItoIntegral_singleClausesUpToFrontier_of_existsOwner
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    {T : NNReal}
    (hExists :
      ∃ N : NNReal → Ω → ℝ,
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr H N ∧
          IsContinuousLocalMartingaleUpTo ℱ μ T N ∧
          IsContinuousSquareVariationProcessUpTo ℱ μ T N
            (bracketDensityIntegralUpTo hbr H)) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H)
        (bracketDensityIntegralUpTo hbr H) := by
  rcases hExists with ⟨N, hN, hLocal, hSq⟩
  -- Proof comment: the only remaining work is to transport the owner-level finite-horizon
  -- clauses to the canonical dyadic realization.
  exact
    canonicalItoIntegral_singleClausesUpTo_of_owner
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (N := N) (hM := hM) (hbr := hbr)
      (T := T) hN ⟨hLocal, hSq⟩

/-- Helper for Theorem 25.22: the canonical dyadic realization already supplies the owner part of
the deterministic-cutoff single-clause package. -/
theorem existsCanonicalOwnerForConstCutoff
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N := by
  -- Proof comment: the source-facing owner predicate is just global agreement with the canonical
  -- dyadic realization, so the canonical cutoff process witnesses itself.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M)
        (H := processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        (hM := hM) (hbr := hbr)⟩

/-- Helper for Theorem 25.22: once the canonical cutoff realization already satisfies the two
finite-horizon single clauses, the existential owner statement is witnessed by that same
canonical cutoff process. -/
theorem existsCutoffOwnerSingleClausesUpTo_of_canonicalCore
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hCore :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N ∧
        IsContinuousLocalMartingaleUpTo ℱ μ T N ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T N
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: after the canonical cutoff process has the genuine finite-horizon witnesses,
  -- the existential owner statement is immediate because the source-facing owner predicate is
  -- witnessed reflexively by that same canonical process.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M)
        (H := processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        (hM := hM) (hbr := hbr),
      hCore.1, hCore.2⟩

/-- Helper for Theorem 25.22: once the canonical deterministic cutoff process already has the
global martingale and square-variation clauses, the source-facing owner package is immediate. -/
theorem existsConstCutoffOwnerWithSingleClauses_of_canonicalGlobal
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hCanonical :
      IsContinuousLocalMartingale ℱ μ
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
        IsContinuousSquareVariationProcess ℱ μ
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N ∧
        IsContinuousLocalMartingale ℱ μ N ∧
        IsContinuousSquareVariationProcess ℱ μ N
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: once the canonical cutoff process has the genuine global clauses, the only
  -- remaining work is to record that the source-facing owner predicate is witnessed reflexively
  -- by that same canonical process.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M)
        (H := processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        (hM := hM) (hbr := hbr),
      hCanonical.1, hCanonical.2⟩

/-- Helper for Theorem 25.22: the remaining deterministic-cutoff premise is one genuine owner
realization carrying the global martingale and square-variation clauses for the stopped
integrand. -/
theorem canonicalConstCutoffGlobalClauses
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Route correction: reuse the Chapter 25.21 global canonical Itô theorems on the deterministically
  -- cut off coefficient instead of rebuilding the owner argument locally.
  have hCut_prog :
      ProgMeasurable ℱ (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) :=
    MeasureTheory.processBeforeStoppingTime_progMeasurable
      (Ω := Ω) (ℱ := ℱ) (H := H) hH_prog (isStoppingTime_const ℱ T)
  have hAllHorizons :
      ∀ U : NNReal, ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (ProbabilityTheory.processBeforeStoppingTime H
                (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (U : ℝ)) := by
    -- Proof comment: the deterministic cutoff already upgrades the single horizon assumption on
    -- `H` to the all-horizons bracket-energy package needed for the canonical cutoff process.
    exact
      Theorem25_22.processBeforeStoppingTime_const_integrableOn_bracketDensity_allHorizons
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) hbr
        T hH_prog hH_sq
  refine ⟨?_, ?_⟩
  · -- Proof comment: Chapter 25.21 already gives the global continuous-local-martingale clause
    -- for the canonical dyadic Itô process once the cutoff coefficient is progressively
    -- measurable and has the all-horizons bracket-density integrability package.
    exact
      _root_.ProbabilityTheory.canonicalItoIntegralContinuousLocalMartingale
        (ℱ := ℱ) (μ := μ) hM hbr hCut_prog hAllHorizons
  · -- Proof comment: the same Chapter 25.21 theorem supplies the genuine square-variation
    -- witness for the canonical deterministic-cutoff process.
    exact
      _root_.ProbabilityTheory.canonicalItoIntegralSquareVariation
        (ℱ := ℱ) (μ := μ) hM hbr hCut_prog hAllHorizons

/-- Helper for Theorem 25.22: the remaining deterministic-cutoff premise is one genuine owner
realization carrying the global martingale and square-variation clauses for the stopped
integrand. -/
theorem existsConstCutoffOwnerGlobalClauses
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N ∧
        IsContinuousLocalMartingale ℱ μ N ∧
        IsContinuousSquareVariationProcess ℱ μ N
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: once the canonical deterministic-cutoff process itself has the two genuine
  -- global clauses, the source-facing owner theorem is immediate by reflexive ownership.
  exact
    existsConstCutoffOwnerWithSingleClauses_of_canonicalGlobal
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T
      (canonicalConstCutoffGlobalClauses
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
        T hH_prog hH_sq)

/-- Helper for Theorem 25.22: the remaining single-cutoff input is the existence of one owner
realization carrying the genuine finite-horizon martingale and square-variation clauses for the
deterministically truncated integrand, derived directly from the source-side progressive
measurability and finite-horizon bracket-density integrability of `H`. -/
theorem canonicalConstCutoff_singleClauses
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Route correction: the actual single-cutoff frontier is a direct global theorem about the
  -- canonical cutoff dyadic realization, not another owner wrapper.
  rcases
      existsConstCutoffOwnerGlobalClauses
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
        T hH_prog hH_sq with
    ⟨N, hOwner, hN_mart, hN_sq⟩
  -- Proof comment: once one genuine cutoff owner is available globally, the existing
  -- owner-to-canonical transport already gives the requested finite-horizon canonical clauses.
  exact
    canonicalItoIntegral_singleClausesUpTo_of_owner
      (μ := μ) (ℱ := ℱ)
      (M := M)
      (H := processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
      (N := N)
      (hM := hM) (hbr := hbr) (T := T)
      hOwner
      ⟨isContinuousLocalMartingaleUpTo_of_isContinuousLocalMartingale
          (μ := μ) (ℱ := ℱ) (T := T) hN_mart,
        isContinuousSquareVariationProcessUpTo_of_isContinuousSquareVariationProcess
          (μ := μ) (ℱ := ℱ) (T := T) hN_sq⟩

/-- Helper for Theorem 25.22: the remaining single-cutoff input is the existence of one owner
realization carrying the genuine finite-horizon martingale and square-variation clauses for the
deterministically truncated integrand, derived directly from the source-side progressive
measurability and finite-horizon bracket-density integrability of `H`. -/
theorem existsConstCutoffOwnerWithSingleClauses
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N ∧
        IsContinuousLocalMartingale ℱ μ N ∧
        IsContinuousSquareVariationProcess ℱ μ N
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: the global owner theorem is now the explicit structural blocker, so this
  -- source-facing existential wrapper is just that theorem.
  exact
    existsConstCutoffOwnerGlobalClauses
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq

/-- Helper for Theorem 25.22: once one genuine owner carries the global cutoff single clauses,
the canonical cutoff realization inherits the finite-horizon single clauses by the existing
owner-to-canonical transport. -/
theorem canonicalItoIntegral_singleClausesUpTo_constCutoffDirect
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: the finite-horizon canonical cutoff theorem now records the exact frontier we
  -- need here, so no extra owner packaging remains.
  exact
    canonicalConstCutoff_singleClauses
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq

/-- Helper for Theorem 25.22: the remaining single-cutoff input is the existence of one owner
realization carrying the genuine finite-horizon martingale and square-variation clauses for the
deterministically truncated integrand, derived directly from the source-side progressive
measurability and finite-horizon bracket-density integrability of `H`. -/
theorem existsCutoffOwnerSingleClausesUpTo
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N ∧
        IsContinuousLocalMartingaleUpTo ℱ μ T N ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T N
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: the existential owner theorem is only a packaging step once the direct
  -- canonical cutoff clauses are available.
  exact
    existsCutoffOwnerSingleClausesUpTo_of_canonicalCore
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T
      (canonicalItoIntegral_singleClausesUpTo_constCutoffDirect
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
        T hH_prog hH_sq)

/-- Helper for Theorem 25.22: the deterministic-cutoff single-input core is to show directly that
the canonical dyadic process already satisfies the finite-horizon martingale and square-variation
clauses for the cutoff integrand. -/
theorem canonicalItoIntegral_singleClausesUpTo_constCutoffCore
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: the direct canonical cutoff theorem records the actual unresolved frontier, so
  -- this named core is now just that direct theorem.
  exact
    canonicalItoIntegral_singleClausesUpTo_constCutoffDirect
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq

/-- Helper for Theorem 25.22: the single-clause frontier is the existence of one owner
realization carrying the genuine finite-horizon martingale and square-variation clauses. -/
theorem existsCutoffOwnerSingleClausesUpToData
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N ∧
        IsContinuousLocalMartingaleUpTo ℱ μ T N ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T N
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  have hCanonical :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) :=
    canonicalItoIntegral_singleClausesUpTo_constCutoffCore
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq
  -- Proof comment: once the cutoff canonical dyadic realization carries the two finite-horizon
  -- clauses, it witnesses the existential owner theorem by reflexive ownership.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M)
        (H := processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        (hM := hM) (hbr := hbr),
      hCanonical.1, hCanonical.2⟩

/-- Helper for Theorem 25.22: the single-clause frontier is the existence of one owner
realization carrying the genuine finite-horizon martingale and square-variation clauses. -/
theorem canonicalItoIntegral_singleClausesUpToFrontier
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H)
        (bracketDensityIntegralUpTo hbr H) := by
  have hCut :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) :=
    canonicalItoIntegral_singleClausesUpTo_constCutoffCore
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq
  -- Proof comment: once the deterministic cutoff carries the two genuine clauses, the original
  -- coefficient inherits them by the already-proved horizon-wise cutoff transport.
  exact
    canonicalItoIntegral_singleClausesUpTo_of_constCutoff
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) hCut

/-- Helper for Theorem 25.22: the single-clause frontier is the existence of one owner
realization carrying the genuine finite-horizon martingale and square-variation clauses. -/
theorem existsOwnerSingleClausesUpToData
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr H N ∧
        IsContinuousLocalMartingaleUpTo ℱ μ T N ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T N
          (bracketDensityIntegralUpTo hbr H) := by
  have hCanonical :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM H) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM H)
          (bracketDensityIntegralUpTo hbr H) :=
    canonicalItoIntegral_singleClausesUpToFrontier
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq
  -- Proof comment: once the canonical dyadic realization has the two finite-horizon clauses, it
  -- witnesses the existential owner statement by reflexive ownership.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM H,
      canonicalSelf (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr),
      hCanonical.1, hCanonical.2⟩

/-- Helper for Theorem 25.22: the real single-clause frontier is to show that the canonical dyadic
realization already carries the finite-horizon local-martingale and square-variation clauses. -/
theorem canonicalItoIntegral_singleClausesUpToCore
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H)
        (bracketDensityIntegralUpTo hbr H) := by
  -- Proof comment: the existential owner wrapper is now derived from the canonical frontier, so
  -- the core theorem is exactly that frontier.
  exact
    canonicalItoIntegral_singleClausesUpToFrontier
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq

/-- Helper for Theorem 25.22: the unresolved owner-level single-clause witness should produce a
finite-horizon continuous-local-martingale witness and the matching square-variation witness for
one genuine Itô owner. -/
theorem exists_ownerSingleClausesUpToWitness
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr H N ∧
        IsContinuousLocalMartingaleUpTo ℱ μ T N ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T N
          (bracketDensityIntegralUpTo hbr H) := by
  -- Proof comment: the core theorem now depends only on the earlier witness-existence helper, so
  -- this theorem is just its public theorem-local alias.
  exact
    existsOwnerSingleClausesUpToData
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq

/-- Helper for Theorem 25.22: the remaining single-integral input is to compare the canonical
dyadic realization with a genuine Itô owner on `[0,T]`. -/
theorem canonicalItoIntegral_singleClausesUpTo
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM H)
        (bracketDensityIntegralUpTo hbr H) := by
  -- Proof comment: the canonical single-clause theorem is now the direct frontier; the owner
  -- wrapper above is derived from this theorem rather than the other way around.
  exact
    canonicalItoIntegral_singleClausesUpToCore
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq

/-- Helper for Theorem 25.22: once one owner pair carries the finite-horizon mixed clauses, the
canonical dyadic realizations inherit them by transport along indistinguishability. -/
theorem canonicalItoIntegral_quadraticCovariationClausesUpTo_of_owners
    {M₁ M₂ H₁ H₂ N₁ N₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    {T : NNReal}
    (hN₁ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁)
    (hN₂ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂)
    (hQuad :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₁ N₂ (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₂ N₁ (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0)) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
      ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          0) := by
  have hEq₁ :
      EqUpTo μ T (continuousLocalMartingaleItoIntegralProcess hM₁ H₁) N₁ :=
    eqUpTo_sym <| eqUpTo_of_areIndistinguishable (μ := μ) (T := T)
      hN₁.indistinguishable_canonical
  have hEq₂ :
      EqUpTo μ T (continuousLocalMartingaleItoIntegralProcess hM₂ H₂) N₂ :=
    eqUpTo_sym <| eqUpTo_of_areIndistinguishable (μ := μ) (T := T)
      hN₂.indistinguishable_canonical
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: transport the left-to-right quadratic-covariation witness along the two
    -- owner-to-canonical equality bridges.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ) hEq₁ hEq₂
        (eqUpTo_rfl (μ := μ) T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂))
        hQuad.1
  · -- Proof comment: the right-to-left clause is the symmetric transport.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ) hEq₂ hEq₁
        (eqUpTo_rfl (μ := μ) T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁))
        hQuad.2.1
  · intro hIndep
    -- Proof comment: once the owner-level zero-bracket clause is known, the same transport sends
    -- it to the canonical dyadic realizations.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ) hEq₁ hEq₂
        (eqUpTo_rfl (μ := μ) T 0)
        (hQuad.2.2 hIndep)

/-- Helper for Theorem 25.22: once a finite-horizon owner pair exists, the canonical dyadic
realizations inherit the mixed quadratic-covariation clauses by the established owner transport.
-/
theorem canonicalItoIntegral_quadraticCovariationClausesUpToFrontier_of_existsOwners
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    {T : NNReal}
    (hExists :
      ∃ N₁ N₂ : NNReal → Ω → ℝ,
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁ ∧
          _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂ ∧
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            N₁ N₂ (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            N₂ N₁ (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
          ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
              (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
            IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0)) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
      ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          0) := by
  rcases hExists with ⟨N₁, N₂, hN₁, hN₂, hLeftRight, hRightLeft, hZero⟩
  -- Proof comment: after the owner pair is available, the mixed canonical clauses are exactly the
  -- owner-to-canonical transport already proved above.
  exact
    canonicalItoIntegral_quadraticCovariationClausesUpTo_of_owners
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (N₁ := N₁) (N₂ := N₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂) (T := T)
      hN₁ hN₂ ⟨hLeftRight, hRightLeft, hZero⟩

/-- Helper for Theorem 25.22: the canonical dyadic realizations already supply the owner part of
the deterministic-cutoff mixed-clause package. -/
theorem existsCanonicalOwnerPairForConstCutoffs
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal) :
    ∃ N₁ N₂ : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) N₁ ∧
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) N₂ := by
  -- Proof comment: each deterministic cutoff is owned by its own canonical dyadic realization,
  -- so the mixed package can start from that canonical pair.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)),
      continuousLocalMartingaleItoIntegralProcess hM₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M₁)
        (H := processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (hM := hM₁) (hbr := hbr₁),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M₂)
        (H := processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
        (hM := hM₂) (hbr := hbr₂)⟩

/-- Helper for Theorem 25.22: once the canonical cutoff pair already satisfies the three
finite-horizon mixed clauses, the existential owner-pair statement is witnessed by that same
canonical cutoff pair. -/
theorem existsCutoffOwnerQuadraticCovariationClausesUpTo_of_canonicalCore
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hCore :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            (continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
            (continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
            0)) :
    ∃ N₁ N₂ : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) N₁ ∧
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) N₂ ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₁ N₂
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₂ N₁
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
  -- Proof comment: after the canonical cutoff pair has the genuine mixed witnesses, the
  -- existential owner statement is immediate because each source-facing owner predicate is again
  -- witnessed reflexively by the corresponding canonical process.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)),
      continuousLocalMartingaleItoIntegralProcess hM₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M₁)
        (H := processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (hM := hM₁) (hbr := hbr₁),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M₂)
        (H := processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
        (hM := hM₂) (hbr := hbr₂),
      hCore.1, hCore.2.1, hCore.2.2⟩

/-- Helper for Theorem 25.22: polarization turns square-variation witnesses of `F + G` and
`F - G` into a pathwise quadratic-covariation witness of `F` and `G`. -/
private theorem hasQuadraticCovariationAlong_polarizationPathLocal
    {F G : C(NNReal, ℝ)} {brAdd brSub : NNReal → ℝ}
    (hAdd : HasSquareVariationAlong (F + G) brAdd)
    (hSub : HasSquareVariationAlong (F - G) brSub) :
    HasQuadraticCovariationAlong F G ((1 / 4 : ℝ) • (brAdd - brSub)) := by
  intro T
  have hPolarized :
      Tendsto
        (fun n ↦
          ((dyadic_p_variation_sum 2 (F + G) T n) -
            (dyadic_p_variation_sum 2 (F - G) T n)) / 4)
        atTop
        (nhds (((1 / 4 : ℝ) • (brAdd - brSub)) T)) := by
    -- Proof comment: the mixed dyadic sums are the polarized difference of the two square
    -- variation sums, so their limit is the same polarized difference of the witness paths.
    simpa [Pi.smul_apply, Pi.sub_apply, div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((HasSquareVariationAlongPartition.tendsto_partition_sum hAdd T).sub
        (HasSquareVariationAlongPartition.tendsto_partition_sum hSub T)).mul_const (1 / 4 : ℝ)
  convert hPolarized using 1
  ext n
  simpa [dyadic_quadratic_covariation_sum, dyadic_p_variation_sum] using
    (partitionQuadraticCovariationSum_eq_polarization
      Definition2158.dyadicPartitionSequence F G T n)

/-- Helper for Theorem 25.22: on `[s, t]`, the variation of a difference of monotone continuous
paths is bounded by the sum of the endpoint increments. -/
private theorem eVariationOnIccSubLeOfMonotonePaths
    {G Gplus Gminus : C(NNReal, ℝ)} (hG : G = Gplus - Gminus)
    (hGplus_mono : Monotone Gplus) (hGminus_mono : Monotone Gminus)
    {s t : NNReal} (hst : s ≤ t) :
    eVariationOn G (Set.Icc s t) ≤
      ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
  rw [hG]
  have hGplus_nonneg : 0 ≤ Gplus t - Gplus s := sub_nonneg_of_le (hGplus_mono hst)
  have hGminus_nonneg : 0 ≤ Gminus t - Gminus s := sub_nonneg_of_le (hGminus_mono hst)
  have hGplus_var :
      eVariationOn Gplus (Set.Icc s t) ≤ ENNReal.ofReal (Gplus t - Gplus s) := by
    simpa [Set.univ_inter] using
      (MonotoneOn.eVariationOn_le
        (f := Gplus) (s := Set.univ) (hGplus_mono.monotoneOn Set.univ)
        (a := s) (b := t) (Set.mem_univ _) (Set.mem_univ _))
  have hGminus_var :
      eVariationOn Gminus (Set.Icc s t) ≤ ENNReal.ofReal (Gminus t - Gminus s) := by
    simpa [Set.univ_inter] using
      (MonotoneOn.eVariationOn_le
        (f := Gminus) (s := Set.univ) (hGminus_mono.monotoneOn Set.univ)
        (a := s) (b := t) (Set.mem_univ _) (Set.mem_univ _))
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    ∑ i ∈ Finset.range n, edist ((Gplus - Gminus) (u (i + 1))) ((Gplus - Gminus) (u i))
        ≤ ∑ i ∈ Finset.range n,
            (edist (Gplus (u (i + 1))) (Gplus (u i)) +
              edist (Gminus (u (i + 1))) (Gminus (u i))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          simpa [Pi.sub_apply] using
            (edist_vsub_vsub_le
              (Gplus (u (i + 1))) (Gminus (u (i + 1))) (Gplus (u i)) (Gminus (u i)))
    _ = (∑ i ∈ Finset.range n, edist (Gplus (u (i + 1))) (Gplus (u i))) +
          ∑ i ∈ Finset.range n, edist (Gminus (u (i + 1))) (Gminus (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn Gplus (Set.Icc s t) + eVariationOn Gminus (Set.Icc s t) := by
      exact add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)
    _ ≤ ENNReal.ofReal (Gplus t - Gplus s) + ENNReal.ofReal (Gminus t - Gminus s) := by
      exact add_le_add hGplus_var hGminus_var
    _ = ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
      rw [ENNReal.ofReal_add hGplus_nonneg hGminus_nonneg]

/-- Helper for Theorem 25.22: a difference of two continuous monotone increasing paths has
locally bounded variation on `[0, ∞)`. -/
private theorem locallyBoundedVariationOnUnivOfSubMonotone
    {G Gplus Gminus : C(NNReal, ℝ)} (hG : G = Gplus - Gminus)
    (hGplus_mono : Monotone Gplus) (hGminus_mono : Monotone Gminus) :
    LocallyBoundedVariationOn G Set.univ := by
  -- Proof comment: the interval variation estimate on each `[0, t]` is exactly the owner needed
  -- for locally bounded variation on `Set.univ`.
  rw [locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero]
  intro t
  have hbound :=
    eVariationOnIccSubLeOfMonotonePaths hG hGplus_mono hGminus_mono (s := 0) (t := t) bot_le
  simpa [BoundedVariationOn] using (hbound.trans_lt ENNReal.ofReal_lt_top).ne

/-- Helper for Theorem 25.22: the polarized difference of two square-variation witnesses has
almost surely locally bounded variation on `[0, ∞)`. -/
private theorem polarizedSquareVariationWitness_locallyFiniteVariation
    {M N Aadd Asub : NNReal → Ω → ℝ}
    (hAdd : IsContinuousSquareVariationProcess ℱ μ (fun t ω ↦ M t ω + N t ω) Aadd)
    (hSub : IsContinuousSquareVariationProcess ℱ μ (fun t ω ↦ M t ω - N t ω) Asub) :
    ∀ᵐ ω ∂μ,
      LocallyBoundedVariationOn
        (⟨fun t ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω), by
          simpa [Pi.smul_apply] using
            Continuous.const_mul ((hAdd.continuous ω).sub (hSub.continuous ω)) (1 / 4 : ℝ)⟩ :
          C(NNReal, ℝ))
        Set.univ := by
  -- Proof comment: each square-variation witness is pathwise monotone, so their scaled
  -- difference has locally bounded variation by the monotone-difference estimate above.
  filter_upwards with ω
  let G : C(NNReal, ℝ) := ⟨fun t ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω), by
    simpa [Pi.smul_apply] using
      Continuous.const_mul ((hAdd.continuous ω).sub (hSub.continuous ω)) (1 / 4 : ℝ)⟩
  let Gplus : C(NNReal, ℝ) := (1 / 4 : ℝ) • ⟨fun t ↦ Aadd t ω, hAdd.continuous ω⟩
  let Gminus : C(NNReal, ℝ) := (1 / 4 : ℝ) • ⟨fun t ↦ Asub t ω, hSub.continuous ω⟩
  have hG : G = Gplus - Gminus := by
    ext t
    simp [G, Gplus, Gminus]
    ring
  have hGplus_mono : Monotone Gplus := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left (hAdd.monotone ω hst) (by positivity)
  have hGminus_mono : Monotone Gminus := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left (hSub.monotone ω hst) (by positivity)
  exact locallyBoundedVariationOnUnivOfSubMonotone hG hGplus_mono hGminus_mono

/-- Helper for Theorem 25.22: polarization turns square-variation witnesses of `M + N` and
`M - N` into a quadratic-covariation witness for `(M, N)`. -/
private theorem isContinuousQuadraticCovariationProcess_polarizationLocal
    {M N Aadd Asub : NNReal → Ω → ℝ}
    (hAdd : IsContinuousSquareVariationProcess ℱ μ (fun t ω ↦ M t ω + N t ω) Aadd)
    (hSub : IsContinuousSquareVariationProcess ℱ μ (fun t ω ↦ M t ω - N t ω) Asub) :
    IsContinuousQuadraticCovariationProcess ℱ μ M N
      (fun t ω ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext ω
    simp [hAdd.zero, hSub.zero]
  · simpa [Pi.smul_apply] using Adapted.smul (1 / 4 : ℝ) (hAdd.adapted.sub hSub.adapted)
  · intro ω
    simpa [Pi.smul_apply] using
      Continuous.const_mul ((hAdd.continuous ω).sub (hSub.continuous ω)) (1 / 4 : ℝ)
  · exact polarizedSquareVariationWitness_locallyFiniteVariation (ℱ := ℱ) (μ := μ) hAdd hSub
  · have hDiffSq :
        IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            ((M t ω + N t ω) ^ 2 - Aadd t ω) -
              ((M t ω - N t ω) ^ 2 - Asub t ω)) := by
      simpa using hAdd.local_martingale_sq_sub.sub hSub.local_martingale_sq_sub
    simpa using (hDiffSq.const_mul (1 / 4 : ℝ)).local_martingale

/-- Helper for Theorem 25.22: continuous local martingales admit a continuous quadratic-
covariation process, and any two such processes are indistinguishable. -/
private theorem existsUniqueContinuousQuadraticCovariationProcessLocal
    {M N : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ) (hN : N ∈ Mlocc ℱ μ) :
    ∃ A : NNReal → Ω → ℝ,
      IsContinuousQuadraticCovariationProcess ℱ μ M N A ∧
        ∀ A' : NNReal → Ω → ℝ,
          IsContinuousQuadraticCovariationProcess ℱ μ M N A' →
            AreIndistinguishable μ A A' := by
  -- Proof comment: reuse the Chapter 21 owner theorem directly; the local theorem only repackages
  -- that witness under this file's namespace.
  exact
    _root_.ProbabilityTheory.existsUnique_continuousQuadraticCovariationProcess
      (ℱ := ℱ) (μ := μ) hM hN

/-- Helper for Theorem 25.22: continuous local martingale pairs admit at least one genuine
continuous quadratic-covariation process. -/
private theorem existsContinuousQuadraticCovariationProcessLocal
    {M N : NNReal → Ω → ℝ} (hM : M ∈ Mlocc ℱ μ) (hN : N ∈ Mlocc ℱ μ) :
    ∃ A : NNReal → Ω → ℝ, IsContinuousQuadraticCovariationProcess ℱ μ M N A := by
  -- Proof comment: forget the uniqueness clause from the restored owner-level existence theorem.
  rcases
      existsUniqueContinuousQuadraticCovariationProcessLocal
        (ℱ := ℱ) (μ := μ) hM hN with
    ⟨A, hA, _⟩
  exact ⟨A, hA⟩

/-- Helper for Theorem 25.22: deterministic stopped-martingale owners reconstruct a continuous
local martingale. -/
private theorem isContinuousLocalMartingale_of_constStoppedMartingaleLocal
    {Y : NNReal → Ω → ℝ}
    (hY_adapted : Adapted ℱ Y)
    (hY_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω)
    (hStopped :
      ∀ T : NNReal, Martingale (stoppedProcess Y (fun _ ↦ (T : ENNReal))) ℱ μ) :
    IsContinuousLocalMartingale ℱ μ Y := by
  refine
    { local_martingale := ?_
      continuous := hY_cont }
  refine (isLocalMartingale_iff ℱ μ Y).2 ⟨hY_adapted, ?_⟩
  refine ⟨fun n _ ↦ (n : ENNReal), ?_⟩
  refine (isLocalizingSequence_iff ℱ μ Y (fun n _ ↦ (n : ENNReal))).2 ⟨?_, ?_, ?_⟩
  · intro n
    simpa using (isStoppingTime_const ℱ (n : NNReal))
  · refine Filter.Eventually.of_forall fun _ ↦ ?_
    refine ⟨fun a b hab ↦ by
      simpa using (show (a : ENNReal) ≤ (b : ENNReal) by exact_mod_cast hab), ?_⟩
    -- Proof comment: the deterministic horizons increase pointwise to `∞`.
    simpa using ENNReal.tendsto_nat_nhds_top
  · intro n
    have hMart :
        Martingale (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ :=
      hStopped n
    have hUI :
        UniformIntegrable
          (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          1
          μ := by
      have hDet :
          Martingale
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) ℱ μ ∧
            UniformIntegrable
              (stoppedProcess
                (stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
                (fun _ ↦ ((n : NNReal) : ENNReal))) 1 μ :=
        martingaleUniformIntegrable_stoppedProcessConstTime
          (ℱ := ℱ)
          (μ := μ)
          (X := stoppedProcess Y (fun _ ↦ ((n : NNReal) : ENNReal)))
          hMart
          (n : NNReal)
      -- Proof comment: stopping the deterministic-stop martingale again at the same horizon does
      -- nothing, so the uniform-integrability clause descends immediately.
      simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using hDet.2
    exact ⟨hMart, hUI⟩

/-- Helper for Theorem 25.22: the sum of two continuous local martingales is again a continuous
local martingale. -/
private theorem isContinuousLocalMartingale_addLocal
    {M N : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N) :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω + N t ω) := by
  -- Proof comment: add the local-martingale owners and combine the pathwise continuity.
  refine ⟨hM.local_martingale.add hN.local_martingale, ?_⟩
  intro ω
  exact (hM.continuous ω).add (hN.continuous ω)

/-- Helper for Theorem 25.22: the difference of two continuous local martingales is again a
continuous local martingale. -/
private theorem isContinuousLocalMartingale_subLocal
    {M N : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N) :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω - N t ω) := by
  -- Proof comment: subtraction is the same closure argument as addition with pathwise
  -- continuity preserved.
  refine ⟨hM.local_martingale.sub hN.local_martingale, ?_⟩
  intro ω
  exact (hM.continuous ω).sub (hN.continuous ω)

/-- Helper for Theorem 25.22: a genuine continuous quadratic-covariation process yields the
almost-sure pathwise dyadic mixed-sum convergence needed to identify the canonical mixed
compensator. -/
theorem aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
    {M N A : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ M N A) :
    ∀ᵐ ω ∂μ,
      HasQuadraticCovariationAlong
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ N t ω, hN.continuous ω⟩ : C(NNReal, ℝ))
        (fun t ↦ A t ω) := by
  have hAdd : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω + N t ω) := by
    -- Proof comment: the polarization route starts from the canonical square-variation owners of
    -- `M + N`.
    exact isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hM hN
  have hSub : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω - N t ω) := by
    -- Proof comment: the same owner-level closure provides the `M - N` branch.
    exact isContinuousLocalMartingale_subLocal (ℱ := ℱ) (μ := μ) hM hN
  rcases _root_.ProbabilityTheory.existsUnique_continuousSquareVariationProcess
      (ℱ := ℱ) (μ := μ) hAdd with
    ⟨Aadd, hAadd, _⟩
  rcases _root_.ProbabilityTheory.existsUnique_continuousSquareVariationProcess
      (ℱ := ℱ) (μ := μ) hSub with
    ⟨Asub, hAsub, _⟩
  let Apolar : NNReal → Ω → ℝ := fun t ω ↦ (1 / 4 : ℝ) * (Aadd t ω - Asub t ω)
  have hApolar :
      IsContinuousQuadraticCovariationProcess ℱ μ M N Apolar :=
    isContinuousQuadraticCovariationProcess_polarizationLocal hAadd hAsub
  rcases
      existsUniqueContinuousQuadraticCovariationProcessLocal
        (ℱ := ℱ)
        (μ := μ)
        (((ProbabilityTheory.mem_Mlocc_iff ℱ μ M)).2 hM)
        (((ProbabilityTheory.mem_Mlocc_iff ℱ μ N)).2 hN) with
    ⟨B, hB, huniq⟩
  have hApolarEq : AreIndistinguishable μ Apolar A := by
    -- Proof comment: uniqueness identifies the polarized canonical witness with the supplied
    -- covariation process.
    exact areIndistinguishable_trans
      (areIndistinguishable_symm (huniq Apolar hApolar))
      (huniq A hA)
  have hAddAE :
      ∀ᵐ ω ∂μ,
        HasSquareVariationAlong
          (⟨fun t ↦ M t ω + N t ω, (hM.continuous ω).add (hN.continuous ω)⟩ : C(NNReal, ℝ))
          (fun t ↦ Aadd t ω) := by
    simpa using
      (_root_.ProbabilityTheory.ae_hasSquareVariationAlong_continuousSquareVariationProcess
        (ℱ := ℱ) (μ := μ) hAdd hAadd)
  have hSubAE :
      ∀ᵐ ω ∂μ,
        HasSquareVariationAlong
          (⟨fun t ↦ M t ω - N t ω, (hM.continuous ω).sub (hN.continuous ω)⟩ : C(NNReal, ℝ))
          (fun t ↦ Asub t ω) := by
    simpa using
      (_root_.ProbabilityTheory.ae_hasSquareVariationAlong_continuousSquareVariationProcess
        (ℱ := ℱ) (μ := μ) hSub hAsub)
  have hEqAE : ∀ᵐ ω ∂μ, ∀ t : NNReal, Apolar t ω = A t ω := by
    rcases hApolarEq with ⟨S, hSmeas, hSzero, hSsub⟩
    rw [ae_iff]
    refine ⟨S, hSmeas, hSzero, ?_⟩
    intro ω hω t
    by_contra hneq
    exact hω (hSsub t hneq)
  filter_upwards [hAddAE, hSubAE, hEqAE] with ω hAddω hSubω hEqω
  have hPolarω :
      HasQuadraticCovariationAlong
        (⟨fun t ↦ M t ω, hM.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun t ↦ N t ω, hN.continuous ω⟩ : C(NNReal, ℝ))
        (fun t ↦ Apolar t ω) := by
    -- Proof comment: on each good path, the mixed covariation is the polarization of the plus and
    -- minus square-variation limits.
    simpa [Apolar, Pi.smul_apply, Pi.sub_apply] using
      (hasQuadraticCovariationAlong_polarizationPath hAddω hSubω)
  intro T
  simpa [hEqω T] using hPolarω T

/-- Helper for Theorem 25.22: any genuine quadratic-covariation processes for `N₁,N₂` and
`N₂,N₁` package directly into the two horizon-wise `...UpTo` clauses needed later. -/
theorem existsQuadraticCovariationPair_of_isContinuousLocalMartingale
    {N₁ N₂ : NNReal → Ω → ℝ}
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂) :
    ∃ A₁₂ A₂₁ : NNReal → Ω → ℝ,
      IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A₁₂ ∧
        IsContinuousQuadraticCovariationProcess ℱ μ N₂ N₁ A₂₁ := by
  rcases
      existsContinuousQuadraticCovariationProcessLocal
        (ℱ := ℱ) (μ := μ)
        (((ProbabilityTheory.mem_Mlocc_iff ℱ μ N₁)).2 hN₁_mart)
        (((ProbabilityTheory.mem_Mlocc_iff ℱ μ N₂)).2 hN₂_mart) with
    ⟨A₁₂, hA₁₂⟩
  rcases
      existsContinuousQuadraticCovariationProcessLocal
        (ℱ := ℱ) (μ := μ)
        (((ProbabilityTheory.mem_Mlocc_iff ℱ μ N₂)).2 hN₂_mart)
        (((ProbabilityTheory.mem_Mlocc_iff ℱ μ N₁)).2 hN₁_mart) with
    ⟨A₂₁, hA₂₁⟩
  -- Proof comment: choose genuine Chapter 21 covariation processes in both orders before any
  -- finite-horizon transport; later callers can package these witnesses as needed.
  exact ⟨A₁₂, A₂₁, hA₁₂, hA₂₁⟩

/-- Helper for Theorem 25.22: any genuine quadratic-covariation processes for `N₁,N₂` and
`N₂,N₁` package directly into the two horizon-wise `...UpTo` clauses needed later. -/
theorem existsQuadraticCovariationUpToPair_of_isContinuousLocalMartingale
    {N₁ N₂ : NNReal → Ω → ℝ}
    (T : NNReal)
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂) :
    ∃ A₁₂ A₂₁ : NNReal → Ω → ℝ,
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ A₁₂ ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₂ N₁ A₂₁ := by
  rcases
      existsQuadraticCovariationPair_of_isContinuousLocalMartingale
        (μ := μ) (ℱ := ℱ) hN₁_mart hN₂_mart with
    ⟨A₁₂, A₂₁, hA₁₂, hA₂₁⟩
  -- Proof comment: once the genuine Chapter 21 witnesses exist in both orders, the horizon-wise
  -- `...UpTo` package is only reflexive transport.
  exact
    ⟨A₁₂, A₂₁,
      isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
        (μ := μ) (ℱ := ℱ) (T := T) hA₁₂,
      isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
        (μ := μ) (ℱ := ℱ) (T := T) hA₂₁⟩

/-- Helper for Theorem 25.22: an owner of the deterministically stopped Itô integral agrees on
`[0,T]` with the canonical cutoff dyadic realization. -/
theorem eqUpTo_constCutoffOwner_canonical
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hN :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N) :
    EqUpTo μ T
      N
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: the owner predicate is exactly indistinguishability with the canonical cutoff
  -- dyadic process, so the finite-horizon equality follows from the generic wrapper.
  exact
    eqUpTo_of_areIndistinguishable
      (μ := μ) (T := T) hN.indistinguishable_canonical

/-- Helper for Theorem 25.22: once the genuine mixed compensators have been identified with the
canonical cutoff formulas on `[0,T]`, the three mixed clauses follow by `EqUpTo` transport. -/
theorem constCutoffQuadraticCovariationClauses_of_eqUpToCompensators
    {M₁ M₂ H₁ H₂ N₁ N₂ A₁₂ A₂₁ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hLeft :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ A₁₂)
    (hRight :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₂ N₁ A₂₁)
    (hEqLeft :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂)
        A₁₂)
    (hEqRight :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁)
        A₂₁)
    (hZero :
      (IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        N₁ N₂
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        N₂ N₁
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
  refine ⟨?_, ?_, hZero⟩
  · -- Proof comment: transport the left-to-right witness from the genuine compensator `A₁₂` to
    -- the canonical cutoff formula via the horizon-wise compensator equality.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ)
        (eqUpTo_rfl (μ := μ) T N₁)
        (eqUpTo_rfl (μ := μ) T N₂)
        hEqLeft
        hLeft
  · -- Proof comment: the reverse-direction clause is the same transport with the two roles
    -- swapped.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
        (μ := μ) (ℱ := ℱ)
        (eqUpTo_rfl (μ := μ) T N₂)
        (eqUpTo_rfl (μ := μ) T N₁)
        hEqRight
        hRight

/-- Helper for Theorem 25.22: any cutoff mixed compensator that already appears in an
`...UpTo`-witness should agree on `[0,T]` with the canonical dyadic quadratic-covariation
integral for the stopped coefficients, provided the two integral coordinates are already tied to
their canonical cutoff realizations. -/
theorem existsNullSet_forall_constCutoffEqUpTo_and_quadraticCovariationAlong
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₁ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω) ∧
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₂ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) ∧
        HasQuadraticCovariationAlong
          (⟨fun t ↦ N₁ t ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun t ↦ N₂ t ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
          (fun t ↦ A t ω) := by
  -- Proof comment: package the two finite-horizon process identifications and the almost-sure
  -- pathwise quadratic-covariation convergence into one fixed measurable good event.
  exact
    existsNullSet_forall_eqUpTo_and_ae
      (μ := μ) (T := T) hEq₁ hEq₂
      (aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
        (μ := μ) (ℱ := ℱ) hN₁_mart hN₂_mart hA)

/-- Helper for Theorem 25.22: on one measurable null-set complement, the two owner processes
agree with the canonical cutoff realizations on `[0,T]` and their own dyadic mixed partition sums
converge to the genuine compensator. -/
theorem existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicQuadraticCovariationTendsto
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₁ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω) ∧
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₂ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) ∧
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  rcases
      existsNullSet_forall_constCutoffEqUpTo_and_quadraticCovariationAlong
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
        (H₁ := H₁) (H₂ := H₂) (A := A)
        T hEq₁ hEq₂ hN₁_mart hN₂_mart hA with
    ⟨S, hSmeas, hSnull, hSgood⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro ω hω
  rcases hSgood hω with ⟨hEq₁ω, hEq₂ω, hPathω⟩
  refine ⟨hEq₁ω, hEq₂ω, ?_⟩
  intro t ht
  -- Proof comment: once the good event already carries the owner pathwise quadratic-covariation
  -- witness, the owner dyadic mixed sums converge by the defining limit theorem.
  simpa [dyadic_quadratic_covariation_sum] using
    HasQuadraticCovariationAlong.tendsto_partition_sum hPathω t

/-- Helper for Theorem 25.22: a genuine quadratic-covariation process for the owner pair yields
one fixed null set on which the owner dyadic mixed sums converge at every horizon up to `T`. -/
theorem existsNullSet_forall_ownerDyadicQuadraticCovariationTendsto
    {N₁ N₂ A : NNReal → Ω → ℝ}
    (T : NNReal)
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  rcases
      ae_exists_nullSet_forall
        (μ := μ)
        (P := fun ω ↦
          HasQuadraticCovariationAlong
            (⟨fun t ↦ N₁ t ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun t ↦ N₂ t ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
            (fun t ↦ A t ω))
        (aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
          (μ := μ) (ℱ := ℱ) hN₁_mart hN₂_mart hA) with
    ⟨S, hSmeas, hSnull, hSgood⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro ω hω t _ht
  have hPath :
      HasQuadraticCovariationAlong
        (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
        (fun s ↦ A s ω) :=
    hSgood hω
  -- Proof comment: off the fixed null set, the owner paths themselves already satisfy the dyadic
  -- mixed-sum convergence that defines pathwise quadratic covariation.
  simpa [dyadic_quadratic_covariation_sum] using
    HasQuadraticCovariationAlong.tendsto_partition_sum hPath t

/-- Helper for Theorem 25.22: a genuine square-variation process for the owner path yields one
fixed null set on which the owner dyadic square sums converge at every horizon up to `T`. -/
theorem existsNullSet_forall_ownerDyadicSquareVariationTendsto
    {N A : NNReal → Ω → ℝ}
    (T : NNReal)
    (hN_mart : IsContinuousLocalMartingale ℱ μ N)
    (hA : IsContinuousSquareVariationProcess ℱ μ N A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N s ω, hN_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N s ω, hN_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  -- Proof comment: a square-variation witness is also the diagonal quadratic-covariation witness,
  -- so the mixed-row theorem applies verbatim with both paths equal.
  exact
    existsNullSet_forall_ownerDyadicQuadraticCovariationTendsto
      (μ := μ)
      (ℱ := ℱ)
      (N₁ := N)
      (N₂ := N)
      (A := A)
      T
      hN_mart
      hN_mart
      (selfContinuousQuadraticCovariation_of_squareVariation hA)

/-- Helper for Theorem 25.22: on one measurable null-set complement, an owner process agrees with
the canonical deterministic-cutoff realization on `[0,T]` and its own dyadic square sums converge
to the genuine compensator. -/
theorem existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicSquareVariationTendsto
    {M N H A : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal)
    (hEq :
      EqUpTo μ T
        N
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))))
    (hN_mart : IsContinuousLocalMartingale ℱ μ N)
    (hA : IsContinuousSquareVariationProcess ℱ μ N A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N t ω =
            continuousLocalMartingaleItoIntegralProcess hM
              (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) t ω) ∧
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N s ω, hN_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N s ω, hN_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  rcases
      eqUpTo_forall_eq (μ := μ) (T := T) hEq with
    ⟨S₁, hS₁meas, hS₁null, hS₁eq⟩
  rcases
      existsNullSet_forall_ownerDyadicSquareVariationTendsto
        (μ := μ) (ℱ := ℱ) (N := N) (A := A) T hN_mart hA with
    ⟨S₂, hS₂meas, hS₂null, hS₂good⟩
  have hSnull : μ (S₁ ∪ S₂) = 0 := by
    have hUnionLe : μ (S₁ ∪ S₂) ≤ μ S₁ + μ S₂ := measure_union_le S₁ S₂
    refine le_antisymm ?_ bot_le
    simpa [hS₁null, hS₂null] using hUnionLe
  refine ⟨S₁ ∪ S₂, hS₁meas.union hS₂meas, hSnull, ?_⟩
  intro ω hω
  have hω₁ : ω ∉ S₁ := by
    exact fun hS₁ω ↦ hω (Set.mem_union_left S₂ hS₁ω)
  have hω₂ : ω ∉ S₂ := by
    exact fun hS₂ω ↦ hω (Set.mem_union_right S₁ hS₂ω)
  refine ⟨?_, ?_⟩
  · intro t ht
    exact hS₁eq ht hω₁
  · intro t ht
    exact hS₂good hω₂ ht

/-- Helper for Theorem 25.22: once two deterministic-cutoff owners already carry the global
single clauses, one fixed null set controls both owner/canonical comparisons and the owner-side
dyadic mixed-sum convergence for any genuine compensator of the owner pair. -/
theorem existsNullSet_forall_constCutoffOwners_and_ownerDyadicQuadraticCovariationTendsto
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hOwner₁ :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) N₁)
    (hOwner₂ :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) N₂)
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₁ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω) ∧
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₂ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) ∧
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  have hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) :=
    -- Proof comment: the first owner already agrees with the first canonical cutoff integral on
    -- `[0, T]`.
    eqUpTo_constCutoffOwner_canonical
      (μ := μ) (ℱ := ℱ)
      (M := M₁) (H := H₁) (N := N₁) (hM := hM₁) (hbr := hbr₁) T hOwner₁
  have hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) :=
    -- Proof comment: the second owner supplies the same horizon-wise comparison for the second
    -- canonical cutoff integral.
    eqUpTo_constCutoffOwner_canonical
      (μ := μ) (ℱ := ℱ)
      (M := M₂) (H := H₂) (N := N₂) (hM := hM₂) (hbr := hbr₂) T hOwner₂
  -- Proof comment: after extracting those two owner/canonical comparisons, the existing good-
  -- event theorem gives the full owner-side dyadic convergence package.
  exact
    existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicQuadraticCovariationTendsto
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      T hEq₁ hEq₂ hN₁_mart hN₂_mart hA

/-- Helper for Theorem 25.22: one fixed null set can simultaneously control the two
deterministic-cutoff owner/canonical comparisons together with the owner-side dyadic
self-variation convergence for both coordinates. -/
theorem existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicSquareVariationTendsto_pair
    {M₁ M₂ N₁ N₂ H₁ H₂ A₁ A₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hA₁ : IsContinuousSquareVariationProcess ℱ μ N₁ A₁)
    (hA₂ : IsContinuousSquareVariationProcess ℱ μ N₂ A₂) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₁ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω) ∧
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₂ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) ∧
        (∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A₁ t ω))) ∧
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A₂ t ω)) := by
  rcases
      existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicSquareVariationTendsto
        (μ := μ) (ℱ := ℱ)
        (M := M₁) (N := N₁) (H := H₁) (A := A₁)
        T hEq₁ hN₁_mart hA₁ with
    ⟨S₁, hS₁meas, hS₁null, hS₁good⟩
  rcases
      existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicSquareVariationTendsto
        (μ := μ) (ℱ := ℱ)
        (M := M₂) (N := N₂) (H := H₂) (A := A₂)
        T hEq₂ hN₂_mart hA₂ with
    ⟨S₂, hS₂meas, hS₂null, hS₂good⟩
  have hSnull : μ (S₁ ∪ S₂) = 0 := by
    have hUnionLe : μ (S₁ ∪ S₂) ≤ μ S₁ + μ S₂ := measure_union_le S₁ S₂
    refine le_antisymm ?_ bot_le
    simpa [hS₁null, hS₂null] using hUnionLe
  refine ⟨S₁ ∪ S₂, hS₁meas.union hS₂meas, hSnull, ?_⟩
  intro ω hω
  have hω₁ : ω ∉ S₁ := by
    exact fun hS₁ω ↦ hω (Set.mem_union_left S₂ hS₁ω)
  have hω₂ : ω ∉ S₂ := by
    exact fun hS₂ω ↦ hω (Set.mem_union_right S₁ hS₂ω)
  rcases hS₁good hω₁ with ⟨hEq₁ω, hSq₁ω⟩
  rcases hS₂good hω₂ with ⟨hEq₂ω, hSq₂ω⟩
  -- Proof comment: both single-coordinate good events now live off one null set, so later
  -- callers can consume the two owner/canonical comparisons and the two self-row limits
  -- together.
  exact ⟨hEq₁ω, hEq₂ω, hSq₁ω, hSq₂ω⟩

/-- Helper for Theorem 25.22: a genuine mixed compensator for `N₁,N₂` transports directly to an
`...UpTo` witness for the canonical deterministic-cutoff pair once both coordinates are already
identified with that pair on `[0,T]`. -/
theorem constCutoffQuadraticCovariationUpTo_of_eqUpTo
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
      (continuousLocalMartingaleItoIntegralProcess hM₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
      (continuousLocalMartingaleItoIntegralProcess hM₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      A := by
  -- Proof comment: first package the genuine quadratic-covariation process as an `...UpTo`
  -- witness for itself, then transport both integral coordinates along the two finite-horizon
  -- identifications to the canonical deterministic-cutoff pair.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (μ := μ) (ℱ := ℱ)
      (eqUpTo_sym hEq₁)
      (eqUpTo_sym hEq₂)
      (eqUpTo_rfl (μ := μ) T A)
      (isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
        (μ := μ) (ℱ := ℱ) (T := T) hA)

/-- Helper for Theorem 25.22: once a genuine owner-side quadratic-covariation witness and the two
owner/canonical comparisons are fixed, one additional `EqUpTo` comparison on the compensator
transports the owner-side dyadic good event from the witness compensator `A'` to the target
compensator `A`. -/
theorem constCutoffOwnerGoodEvent_of_upToWitness
    {M₁ M₂ N₁ N₂ A A' H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hOwner : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A')
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hEqA : EqUpTo μ T A A')
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₁ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω) ∧
        (∀ ⦃t : NNReal⦄, t ≤ T →
          N₂ t ω =
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) ∧
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  rcases
      existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicQuadraticCovariationTendsto
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂) (H₁ := H₁) (H₂ := H₂) (A := A')
        T hEq₁ hEq₂ hN₁_mart hN₂_mart hOwner with
    ⟨S₁, hS₁meas, hS₁null, hS₁good⟩
  rcases
      eqUpTo_forall_eq (μ := μ) (T := T) hEqA with
    ⟨S₂, hS₂meas, hS₂null, hS₂eq⟩
  have hSnull : μ (S₁ ∪ S₂) = 0 := by
    have hUnionLe : μ (S₁ ∪ S₂) ≤ μ S₁ + μ S₂ := measure_union_le S₁ S₂
    refine le_antisymm ?_ bot_le
    simpa [hS₁null, hS₂null] using hUnionLe
  refine ⟨S₁ ∪ S₂, hS₁meas.union hS₂meas, hSnull, ?_⟩
  intro ω hω
  have hω₁ : ω ∉ S₁ := by
    exact fun hS₁ω ↦ hω (Set.mem_union_left S₂ hS₁ω)
  have hω₂ : ω ∉ S₂ := by
    exact fun hS₂ω ↦ hω (Set.mem_union_right S₁ hS₂ω)
  rcases hS₁good hω₁ with ⟨hEq₁ω, hEq₂ω, hLimit⟩
  refine ⟨hEq₁ω, hEq₂ω, ?_⟩
  intro t ht
  have hAeq : A t ω = A' t ω := hS₂eq ht hω₂
  -- Proof comment: the good event from the genuine witness already gives the owner-side dyadic
  -- limit, and the additional `EqUpTo` comparison only rewrites the limit value from `A'` to `A`.
  simpa [hAeq] using hLimit ht

/-- Helper for Theorem 25.22: pointwise-identical real sequences have the same limit. -/
theorem tendsto_nhds_of_seq_eq
    {u v : ℕ → ℝ} {L : ℝ}
    (hEq : ∀ n : ℕ, u n = v n)
    (hv : Tendsto v atTop (𝓝 L)) :
    Tendsto u atTop (𝓝 L) := by
  -- Proof comment: replacing every term of a sequence by an equal term preserves its filter
  -- limit.
  convert hv using 1
  ext n
  exact hEq n

/-- Helper for Theorem 25.22: a real sequence converges to `L` once every sufficiently fine frozen
approximation converges to `L` and the original sequence is eventually uniformly close to one such
frozen approximation. -/
theorem tendsto_atTop_of_frozenApproximation
    {u : ℕ → ℝ} {v : ℕ → ℕ → ℝ} {L : ℝ}
    (hFrozen : ∀ m : ℕ, Tendsto (v m) atTop (𝓝 L))
    (hApprox :
      ∀ ε > 0, ∃ m : ℕ, ∀ᶠ n in atTop, |u n - v m n| < ε) :
    Tendsto u atTop (𝓝 L) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hεhalf : 0 < ε / 2 := by positivity
  rcases hApprox (ε / 2) hεhalf with ⟨m, hm⟩
  have hFrozenEventually :
      ∀ᶠ n in atTop, |v m n - L| < ε / 2 := by
    -- Proof comment: convergence of the frozen row gives eventual membership in the open ball of
    -- radius `ε / 2` around `L`.
    exact (hFrozen m) <| by simpa [Real.dist_eq] using Metric.ball_mem_nhds L hεhalf
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hm
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hFrozenEventually
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hApproxN : |u n - v m n| < ε / 2 := hN₁ n (le_trans (le_max_left _ _) hn)
  have hFrozenN : |v m n - L| < ε / 2 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hdist :
      |u n - L| ≤ |u n - v m n| + |v m n - L| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      abs_sub_le (u n) (v m n) L
  have hsum : |u n - v m n| + |v m n - L| < ε / 2 + ε / 2 := by
    exact add_lt_add hApproxN hFrozenN
  have hltAbs : |u n - L| < ε := by
    refine lt_of_le_of_lt hdist ?_
    simpa using hsum
  simpa [Real.dist_eq] using hltAbs

/-- Helper for Theorem 25.22: a real sequence converges to `A` once it is eventually close to
arbitrarily far frozen rows whose own limits converge to a limit family `L m → A`. -/
theorem tendsto_atTop_of_frozenApproximationOfLimitFamily
    {u : ℕ → ℝ} {v : ℕ → ℕ → ℝ} {L : ℕ → ℝ} {A : ℝ}
    (hFrozen : ∀ m : ℕ, Tendsto (v m) atTop (𝓝 (L m)))
    (hLimit : Tendsto L atTop (𝓝 A))
    (hApprox :
      ∀ ε > 0, ∀ N : ℕ, ∃ m ≥ N, ∀ᶠ n in atTop, |u n - v m n| < ε) :
    Tendsto u atTop (𝓝 A) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  have hεthird : 0 < ε / 3 := by positivity
  rcases Metric.tendsto_atTop.1 hLimit (ε / 3) hεthird with ⟨N, hN⟩
  rcases hApprox (ε / 3) hεthird N with ⟨m, hmN, hmApprox⟩
  have hLm : |L m - A| < ε / 3 := hN m hmN
  have hFrozenEventually :
      ∀ᶠ n in atTop, |v m n - L m| < ε / 3 := by
    -- Proof comment: the chosen frozen row eventually stays inside the open ball of radius
    -- `ε / 3` around its own limit `L m`.
    exact (hFrozen m) <| by
      simpa [Real.dist_eq] using Metric.ball_mem_nhds (L m) hεthird
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hmApprox
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hFrozenEventually
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hApproxN : |u n - v m n| < ε / 3 := hN₁ n (le_trans (le_max_left _ _) hn)
  have hFrozenN : |v m n - L m| < ε / 3 := hN₂ n (le_trans (le_max_right _ _) hn)
  have hdist₁ : |u n - A| ≤ |u n - v m n| + |v m n - A| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      abs_sub_le (u n) (v m n) A
  have hdist₂ : |v m n - A| ≤ |v m n - L m| + |L m - A| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      abs_sub_le (v m n) (L m) A
  have hdist :
      |u n - A| ≤ |u n - v m n| + |v m n - L m| + |L m - A| := by
    refine le_trans hdist₁ ?_
    calc
      |u n - v m n| + |v m n - A|
          ≤ |u n - v m n| + (|v m n - L m| + |L m - A|) := by
              gcongr
      _ = |u n - v m n| + |v m n - L m| + |L m - A| := by ring
  have hlt : dist (u n) A < ε := by
    have hdist' : dist (u n) A ≤ |u n - v m n| + |v m n - L m| + |L m - A| := by
      simpa [Real.dist_eq] using hdist
    nlinarith [hApproxN, hFrozenN, hLm, hdist']
  simpa [Real.dist_eq] using hlt

/-- Helper for Theorem 25.22: off one null set, the sample paths `M₁ + M₂` and `M₁ - M₂`
both carry square-variation witnesses. -/
theorem constCutoffGoodPath_plusMinusSquareVariation
    {M₁ M₂ : NNReal → Ω → ℝ}
    (hM₁ : IsContinuousLocalMartingale ℱ μ M₁)
    (hM₂ : IsContinuousLocalMartingale ℱ μ M₂) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∃ brAdd brSub : NNReal → ℝ,
          HasSquareVariationAlong
            (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
              C(NNReal, ℝ))
            brAdd ∧
          HasSquareVariationAlong
            (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
              C(NNReal, ℝ))
            brSub := by
  have hAdd : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M₁ t ω + M₂ t ω) := by
    -- Proof comment: sums of continuous local martingales stay in the same class.
    exact isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hM₁ hM₂
  have hSub : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M₁ t ω - M₂ t ω) := by
    -- Proof comment: the same closure property gives a continuous local martingale for `M₁ - M₂`.
    exact isContinuousLocalMartingale_subLocal (ℱ := ℱ) (μ := μ) hM₁ hM₂
  let Vadd : NNReal → Ω → ℝ := continuousSquareVariationProcess hAdd
  let Vsub : NNReal → Ω → ℝ := continuousSquareVariationProcess hSub
  have hAddAE :
      ∀ᵐ ω ∂μ,
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          (fun s ↦ Vadd s ω) := by
    -- Proof comment: Chapter 21 already gives almost-sure square variation for the sum process.
    simpa [Vadd] using
      (_root_.ProbabilityTheory.ae_hasSquareVariationAlong_continuousSquareVariationProcess
        hAdd
        (continuousSquareVariationProcess_spec hAdd))
  have hSubAE :
      ∀ᵐ ω ∂μ,
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          (fun s ↦ Vsub s ω) := by
    -- Proof comment: the difference process is handled by the same square-variation chooser.
    simpa [Vsub] using
      (_root_.ProbabilityTheory.ae_hasSquareVariationAlong_continuousSquareVariationProcess
        hSub
        (continuousSquareVariationProcess_spec hSub))
  have hAE :
      ∀ᵐ ω ∂μ,
        ∃ brAdd brSub : NNReal → ℝ,
          HasSquareVariationAlong
            (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
              C(NNReal, ℝ))
            brAdd ∧
          HasSquareVariationAlong
            (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
              C(NNReal, ℝ))
            brSub := by
    -- Proof comment: package the two almost-sure square-variation witnesses into one good-event
    -- predicate so later mixed arguments can work pathwise off a single null set.
    filter_upwards [hAddAE, hSubAE] with ω hAddω hSubω
    exact ⟨fun s ↦ Vadd s ω, fun s ↦ Vsub s ω, hAddω, hSubω⟩
  exact ae_exists_nullSet_forall (μ := μ) hAE

/-- Helper for Theorem 25.22: the weighted cutoff source dyadic row is exactly the same-row mixed
partition sum of the two row-`n` cutoff Itô approximants. -/
theorem constCutoffWeightedSourceDyadic_eq_sameRowApproxMixed
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal) {ω : Ω} {t : NNReal} (n : ℕ) :
    Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
      (fun s ↦
        processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
          processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
      (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
      (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
      t
      n =
    Finset.sum
      (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
      (fun k ↦
        (Theorem25_22.partitionPathwiseItoApproximationUpTo
            (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
            n -
          Theorem25_22.partitionPathwiseItoApproximationUpTo
            (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            Definition2158.dyadicPartitionSequence
            (Definition2158.dyadicPartitionSequence n k)
            n) *
          (Theorem25_22.partitionPathwiseItoApproximationUpTo
              (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
              (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
              n -
            Theorem25_22.partitionPathwiseItoApproximationUpTo
              (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
              (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
              Definition2158.dyadicPartitionSequence
              (Definition2158.dyadicPartitionSequence n k)
              n)) := by
  -- Proof comment: this is the theorem-local same-row identity from
  -- `partitionPathwiseItoApproximationUpTo_sameRow_mixed`, specialized to the two deterministic
  -- cutoff coefficients.
  symm
  simpa using
    Theorem25_22.partitionPathwiseItoApproximationUpTo_sameRow_mixed
      (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
      (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
      (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
      (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
      t
      n

/-- Helper for Theorem 25.22: once the canonical cutoff partition sums converge pathwise to `A`,
the matching weighted source dyadic sums along `M₁` and `M₂` converge to the same value. -/
theorem hasQuadraticCovariationAlong_of_constCutoffGoodPath
    {M₁ M₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {ω : Ω}
    (hGoodω :
      ∃ brAdd brSub : NNReal → ℝ,
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brAdd ∧
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brSub) :
    ∃ B : NNReal → ℝ,
      HasQuadraticCovariationAlong
        (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
        B := by
  rcases hGoodω with ⟨brAdd, brSub, hBrAdd, hBrSub⟩
  refine ⟨(1 / 4 : ℝ) • (brAdd - brSub), ?_⟩
  -- Proof comment: the good path already carries square-variation witnesses for the sum and
  -- difference paths, so the theorem-local polarization lemma produces the mixed covariation
  -- witness for the original pair.
  exact hasQuadraticCovariationAlong_polarizationPathLocal hBrAdd hBrSub

/-- Helper for Theorem 25.22: pathwise quadratic-covariation witnesses are unique because they
are determined by the common dyadic mixed-sum limit. -/
private theorem hasQuadraticCovariationAlong_eq
    {F G : C(NNReal, ℝ)} {B₁ B₂ : NNReal → ℝ}
    (hB₁ : HasQuadraticCovariationAlong F G B₁)
    (hB₂ : HasQuadraticCovariationAlong F G B₂) :
    B₁ = B₂ := by
  -- Proof comment: at each deterministic horizon, both witness paths are limits of the same
  -- dyadic mixed-sum sequence, so uniqueness of limits forces equality.
  funext T
  exact
    tendsto_nhds_unique
      (HasQuadraticCovariationAlong.tendsto_partition_sum hB₁ T)
      (HasQuadraticCovariationAlong.tendsto_partition_sum hB₂ T)

/-- Helper for Theorem 25.22: replacing either continuous path by an exactly equal one preserves
the same pathwise quadratic-covariation witness. -/
private theorem hasQuadraticCovariationAlong_congr_paths
    {F₁ F₂ G₁ G₂ : C(NNReal, ℝ)} {B : NNReal → ℝ}
    (hF : F₁ = F₂)
    (hG : G₁ = G₂)
    (hB : HasQuadraticCovariationAlong F₁ G₁ B) :
    HasQuadraticCovariationAlong F₂ G₂ B := by
  intro T
  -- Proof comment: the defining dyadic mixed-sum sequence only sees the two sample paths, so an
  -- exact path rewrite leaves the same limit witness at every deterministic horizon.
  simpa [hF, hG] using hB T

/-- Helper for Theorem 25.22: if a path pair already has zero quadratic covariation, then every
frozen coarse-step polarized mixed-row limit vanishes. -/
private theorem coarseIccStepMixedLimit_eq_zero_of_zeroCovariation
    {F G : C(NNReal, ℝ)} {brAdd brSub : NNReal → ℝ}
    (hAdd : HasSquareVariationAlong (F + G) brAdd)
    (hSub : HasSquareVariationAlong (F - G) brSub)
    (hZero : HasQuadraticCovariationAlong F G 0)
    (w : NNReal → ℝ) (m : ℕ) (T : NNReal) :
    (1 / 4 : ℝ) *
        (coarseIccStepSquareVariationLimit w m T brAdd -
          coarseIccStepSquareVariationLimit w m T brSub) =
      0 := by
  have hPolar :
      HasQuadraticCovariationAlong F G ((1 / 4 : ℝ) • (brAdd - brSub)) :=
    hasQuadraticCovariationAlong_polarizationPathLocal hAdd hSub
  have hEqBr : brAdd = brSub := by
    funext t
    have hEqAt :
        ((1 / 4 : ℝ) • (brAdd - brSub)) t = 0 := by
      simpa using congrFun (hasQuadraticCovariationAlong_eq hPolar hZero) t
    have hEqScaled : (1 / 4 : ℝ) * (brAdd t - brSub t) = 0 := by
      simpa [Pi.smul_apply, Pi.sub_apply] using hEqAt
    linarith
  -- Proof comment: after identifying the plus and minus square-variation witnesses, the frozen
  -- polarized limit is the quarter-difference of two identical terms.
  simpa [hEqBr]

/-- Helper for Theorem 25.22: on `[0,T]`, the owner partition row agrees termwise with the
canonical cutoff partition row once both owner paths are identified with the canonical cutoff
integrals. -/
theorem ownerPartitionSum_eq_constCutoffCanonicalRow
    {M₁ M₂ N₁ N₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    {t : NNReal} (ht : t ≤ T)
    {ω : Ω}
    {hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁}
    {hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂}
    (hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)
    (hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)
    (n : ℕ) :
    partitionQuadraticCovariationSum
        Definition2158.dyadicPartitionSequence
        (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
        t
        n =
      Finset.sum
        (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
        (fun k ↦
          (continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
              (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
              (Definition2158.dyadicPartitionSequence n k) ω) *
            (continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
              continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                (Definition2158.dyadicPartitionSequence n k) ω)) := by
  -- Proof comment: unfold the owner partition row and rewrite each active endpoint directly with
  -- the horizon-wise owner/canonical equalities on `[0,t] ⊆ [0,T]`.
  rw [partitionQuadraticCovariationSum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_mem :
      Definition2158.dyadicPartitionSequence n k ∈ Set.Icc 0 t :=
    Theorem25_22.partitionPoint_mem_Icc_of_lt_partitionBoundIndex
      Definition2158.dyadicPartitionSequence n k t (Finset.mem_range.mp hk)
  have hnext_mem :
      partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t ∈ Set.Icc 0 t := by
    constructor
    · exact bot_le
    · simp [partitionNextPointUpTo]
  -- Proof comment: each active endpoint of the owner row lies in `[0,t]`, so both factors
  -- rewrite pointwise to their canonical cutoff counterparts.
  simp [hEq₁ω (hnext_mem.2.trans ht), hEq₁ω (hk_mem.2.trans ht),
    hEq₂ω (hnext_mem.2.trans ht), hEq₂ω (hk_mem.2.trans ht)]

/-- Helper for Theorem 25.22: the owner partition limit transfers immediately to the canonical
cutoff partition row once the two owner paths agree with the canonical cutoff integrals on
`[0,T]`. -/
theorem constCutoffCanonicalPartition_tendsto_of_ownerPartitionLimit
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁}
    {hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂}
    (T : NNReal)
    {ω : Ω} {t : NNReal} (ht : t ≤ T)
    (hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)
    (hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)
    (hOwnerPartitionLimit :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
          (fun k ↦
            (continuousLocalMartingaleItoIntegralProcess hM₁
                (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
              continuousLocalMartingaleItoIntegralProcess hM₁
                (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                (Definition2158.dyadicPartitionSequence n k) ω) *
              (continuousLocalMartingaleItoIntegralProcess hM₂
                  (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                continuousLocalMartingaleItoIntegralProcess hM₂
                  (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                  (Definition2158.dyadicPartitionSequence n k) ω)))
      atTop
      (𝓝 (A t ω)) := by
  -- Proof comment: termwise equality of the owner and canonical cutoff partition rows lets the
  -- owner limit pass directly to the canonical row.
  exact
    tendsto_nhds_of_seq_eq
      (fun n ↦
        (ownerPartitionSum_eq_constCutoffCanonicalRow
          (μ := μ) (ℱ := ℱ)
          (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
          (H₁ := H₁) (H₂ := H₂)
          (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
          T ht hEq₁ω hEq₂ω n).symm)
      hOwnerPartitionLimit

/-- Helper for Theorem 25.22: subtracting two finite mixed rows splits into the two one-coordinate
error families obtained by adding and subtracting the mixed cross term cellwise. -/
private theorem sum_mul_sub_sum_mul_split
    {ι : Type*} (s : Finset ι) (a a' b b' : ι → ℝ) :
    Finset.sum s (fun i ↦ a i * b i) - Finset.sum s (fun i ↦ a' i * b' i) =
      Finset.sum s (fun i ↦ ((a i - a' i) * b i + a' i * (b i - b' i))) := by
  -- Proof comment: rewrite the difference of the two row sums as one finite sum and split each
  -- cellwise mixed-product difference by adding and subtracting `a'ᵢ * bᵢ`.
  calc
    Finset.sum s (fun i ↦ a i * b i) - Finset.sum s (fun i ↦ a' i * b' i) =
        Finset.sum s (fun i ↦ (a i * b i - a' i * b' i)) := by
          rw [← Finset.sum_sub_distrib]
    _ = Finset.sum s (fun i ↦ ((a i - a' i) * b i + a' i * (b i - b' i))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

/-- Helper for Theorem 25.22: once the owner partition sums converge pathwise to `A` and the
owner paths agree with the canonical cutoff realizations on `[0,T]`, the matching same-row mixed
cutoff approximation converges to the same value. -/
private theorem sameRowCutoffApproxMixed_tendsto_of_sourceDyadicLimit
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal) {ω : Ω} {t : NNReal}
    (hSourceLimit :
      Tendsto
        (fun n ↦
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (fun s ↦
              processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
          (fun k ↦
            (Theorem25_22.partitionPathwiseItoApproximationUpTo
                (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                n -
              Theorem25_22.partitionPathwiseItoApproximationUpTo
                (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                (Definition2158.dyadicPartitionSequence n k)
                n) *
              (Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                  n -
                Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (Definition2158.dyadicPartitionSequence n k)
                  n)))
      atTop
      (𝓝 (A t ω)) := by
  -- Proof comment: the same-row cutoff sum is exactly the weighted source dyadic row, so once the
  -- source-facing sequence converges, the same limit transfers by termwise equality.
  exact
    tendsto_nhds_of_seq_eq
      (fun n ↦
        (constCutoffWeightedSourceDyadic_eq_sameRowApproxMixed
          (μ := μ) (ℱ := ℱ)
          (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
          (hM₁ := hM₁) (hM₂ := hM₂)
          T
          (ω := ω)
          (t := t)
          n).symm)
      hSourceLimit

/-- Helper for Theorem 25.22: the canonical same-row mixed partition limit is exactly the weighted
source dyadic limit for the stopped coefficients. -/
private theorem constCutoffWeightedSourceDyadic_tendsto_of_canonicalPartitionLimit
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal) {ω : Ω} {t : NNReal}
    (hCanonicalPartitionLimit :
      Tendsto
        (fun n ↦
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
            (fun k ↦
              (continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (Definition2158.dyadicPartitionSequence n k) ω) *
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω)))
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
          (fun s ↦
            processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
              processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
          (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
          t
          n)
      atTop
      (𝓝 (A t ω)) := by
  -- Proof comment: the weighted source dyadic row is definitionally the same sequence as the
  -- canonical same-row mixed partition sum.
  exact
    tendsto_nhds_of_seq_eq
      (fun n ↦
        constCutoffWeightedSourceDyadic_eq_sameRowApproxMixed
          (μ := μ) (ℱ := ℱ)
          (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
          (hM₁ := hM₁) (hM₂ := hM₂)
          T
          (ω := ω)
          (t := t)
          n)
      hCanonicalPartitionLimit

/-- Helper for Theorem 25.22: once the owner partition sums converge pathwise to `A` and the
owner paths agree with the canonical cutoff realizations on `[0,T]`, the matching same-row mixed
cutoff approximation converges to the same value. -/
private theorem constCutoffWeightedSourceDyadic_tendsto_of_canonicalPartitionCore
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal) {ω : Ω} {t : NNReal} (ht : t ≤ T)
    (hGoodω :
      ∃ brAdd brSub : NNReal → ℝ,
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brAdd ∧
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brSub)
    (hSq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)))
    (hSq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)))
    (hCanonicalPartitionLimit :
      Tendsto
        (fun n ↦
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
            (fun k ↦
              (continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (Definition2158.dyadicPartitionSequence n k) ω) *
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω)))
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
          (fun s ↦
            processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
              processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
          (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
          t
          n)
      atTop
      (𝓝 (A t ω)) := by
  -- Route correction: this theorem already assumes the exact canonical same-row partition limit
  -- needed by the direct source-dyadic theorem, so the frozen/common-grid branch is redundant.
  -- Proof comment: transfer the supplied canonical same-row limit directly to the weighted source
  -- dyadic row and stop there.
  simpa using
    (constCutoffWeightedSourceDyadic_tendsto_of_canonicalPartitionLimit
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      (hM₁ := hM₁) (hM₂ := hM₂)
      T
      (ω := ω)
      (t := t)
      hCanonicalPartitionLimit)

/-- Helper for Theorem 25.22: once the owner partition sums converge pathwise to `A` and the
owner paths agree with the canonical cutoff realizations on `[0,T]`, the matching same-row mixed
cutoff approximation converges to the same value. -/
private theorem sameRowCutoffApproxMixed_tendsto_of_canonicalPartitionCore
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal) {ω : Ω} {t : NNReal} (ht : t ≤ T)
    (hGoodω :
      ∃ brAdd brSub : NNReal → ℝ,
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brAdd ∧
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brSub)
    (hSq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)))
    (hSq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)))
    (hCanonicalPartitionLimit :
      Tendsto
        (fun n ↦
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
            (fun k ↦
              (continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (Definition2158.dyadicPartitionSequence n k) ω) *
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω)))
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
          (fun k ↦
            (Theorem25_22.partitionPathwiseItoApproximationUpTo
                (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                n -
              Theorem25_22.partitionPathwiseItoApproximationUpTo
                (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                (Definition2158.dyadicPartitionSequence n k)
                n) *
              (Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                  n -
                Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (Definition2158.dyadicPartitionSequence n k)
                  n)))
      atTop
      (𝓝 (A t ω)) := by
  have hSourceLimit :
      Tendsto
        (fun n ↦
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (fun s ↦
              processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (A t ω)) :=
    constCutoffWeightedSourceDyadic_tendsto_of_canonicalPartitionCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T ht hGoodω hSq₁ω hSq₂ω hCanonicalPartitionLimit
  -- Proof comment: after isolating the source-facing convergence theorem, the same-row surface is
  -- only a termwise rewrite of that sequence.
  exact
    sameRowCutoffApproxMixed_tendsto_of_sourceDyadicLimit
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      (hM₁ := hM₁) (hM₂ := hM₂)
      T
      (ω := ω)
      (t := t)
      hSourceLimit

/-- Helper for Theorem 25.22: the same-row cutoff approximation is termwise equal to the weighted
source dyadic approximation, so any same-row limit transfers back to the source-facing sequence.
-/
private theorem constCutoffWeightedSourceDyadic_tendsto_of_sameRowLimit
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal) {ω : Ω} {t : NNReal}
    (hSameRowLimit :
      Tendsto
        (fun n ↦
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
            (fun k ↦
              (Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                  n -
                Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (Definition2158.dyadicPartitionSequence n k)
                  n) *
                (Theorem25_22.partitionPathwiseItoApproximationUpTo
                    (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                    (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                    Definition2158.dyadicPartitionSequence
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                    n -
                  Theorem25_22.partitionPathwiseItoApproximationUpTo
                    (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                    (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                    Definition2158.dyadicPartitionSequence
                    (Definition2158.dyadicPartitionSequence n k)
                    n)))
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
          (fun s ↦
            processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
              processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
          (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
          t
          n)
      atTop
      (𝓝 (A t ω)) := by
  -- Proof comment: the source-facing mixed row and the same-row cutoff approximation agree
  -- termwise, so the limit transfers back by a single sequence rewrite.
  exact
    tendsto_nhds_of_seq_eq
      (fun n ↦
        constCutoffWeightedSourceDyadic_eq_sameRowApproxMixed
          (μ := μ) (ℱ := ℱ)
          (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
          (hM₁ := hM₁) (hM₂ := hM₂)
          T
          (ω := ω)
          (t := t)
          n)
      hSameRowLimit

/-- Helper for Theorem 25.22: once the owner partition sums converge pathwise to `A` and the
owner paths agree with the canonical cutoff realizations on `[0,T]`, the matching same-row mixed
cutoff approximation converges to the same value. -/
theorem sameRowCutoffApproxMixed_tendsto_of_ownerPartitionLimit
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    {hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁}
    {hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂}
    (T : NNReal) {ω : Ω} {t : NNReal} (ht : t ≤ T)
    (hGoodω :
      ∃ brAdd brSub : NNReal → ℝ,
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brAdd ∧
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brSub)
    (hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)
    (hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)
    (hSq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            partitionQuadraticCovariationSum
              Definition2158.dyadicPartitionSequence
              (⟨fun u ↦ N₁ u ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
              (⟨fun u ↦ N₁ u ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
              s
              n)
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)))
    (hSq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            partitionQuadraticCovariationSum
              Definition2158.dyadicPartitionSequence
              (⟨fun u ↦ N₂ u ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
              (⟨fun u ↦ N₂ u ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
              s
              n)
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)))
    (hOwnerPartitionLimit :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
          (fun k ↦
            (Theorem25_22.partitionPathwiseItoApproximationUpTo
                (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                n -
              Theorem25_22.partitionPathwiseItoApproximationUpTo
                (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                Definition2158.dyadicPartitionSequence
                (Definition2158.dyadicPartitionSequence n k)
                n) *
              (Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                  n -
                Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (Definition2158.dyadicPartitionSequence n k)
                  n)))
      atTop
      (𝓝 (A t ω)) := by
  have hCanonicalSq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)) := by
    intro s hs
    -- Proof comment: transport the owner-side self-covariation row to the canonical cutoff row
    -- by reusing the already proved owner-to-canonical partition comparison in the diagonal case.
    exact
      constCutoffCanonicalPartition_tendsto_of_ownerPartitionLimit
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₁) (N₁ := N₁) (N₂ := N₁)
        (H₁ := H₁) (H₂ := H₁)
        (A := bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (hN₁_mart := hN₁_mart) (hN₂_mart := hN₁_mart)
        T hs hEq₁ω hEq₁ω (hSq₁ω hs)
  have hCanonicalSq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k s) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)) := by
    intro s hs
    -- Proof comment: the same diagonal transport handles the second coordinate.
    exact
      constCutoffCanonicalPartition_tendsto_of_ownerPartitionLimit
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₂) (M₂ := M₂) (N₁ := N₂) (N₂ := N₂)
        (H₁ := H₂) (H₂ := H₂)
        (A := bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (hN₁_mart := hN₂_mart) (hN₂_mart := hN₂_mart)
        T hs hEq₂ω hEq₂ω (hSq₂ω hs)
  have hCanonicalPartitionLimit :
      Tendsto
        (fun n ↦
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
            (fun k ↦
              (continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (Definition2158.dyadicPartitionSequence n k) ω) *
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω)))
        atTop
        (𝓝 (A t ω)) :=
    constCutoffCanonicalPartition_tendsto_of_ownerPartitionLimit
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
      (H₁ := H₁) (H₂ := H₂)
      (A := A)
      (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
      T ht hEq₁ω hEq₂ω hOwnerPartitionLimit
  -- Proof comment: after transporting the owner self-rows and mixed row to the canonical cutoff
  -- partition surface, the remaining convergence is exactly the canonical-partition theorem.
  exact
    sameRowCutoffApproxMixed_tendsto_of_canonicalPartitionCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T ht hGoodω hCanonicalSq₁ω hCanonicalSq₂ω hCanonicalPartitionLimit

/-- Helper for Theorem 25.22: once the owner partition sums converge pathwise to `A`, the
matching weighted source dyadic sums along `M₁` and `M₂` converge to the same value. -/
theorem constCutoffWeightedSourceDyadicTendstoCore
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    {hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁}
    {hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂}
    (T : NNReal) {ω : Ω} {t : NNReal} (ht : t ≤ T)
    (hGoodω :
      ∃ brAdd brSub : NNReal → ℝ,
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω + M₂ s ω, (hM₁.continuous ω).add (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brAdd ∧
        HasSquareVariationAlong
          (⟨fun s ↦ M₁ s ω - M₂ s ω, (hM₁.continuous ω).sub (hM₂.continuous ω)⟩ :
            C(NNReal, ℝ))
          brSub)
    (hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)
    (hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)
    (hSq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            partitionQuadraticCovariationSum
              Definition2158.dyadicPartitionSequence
              (⟨fun u ↦ N₁ u ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
              (⟨fun u ↦ N₁ u ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
              s
              n)
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)))
    (hSq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        Tendsto
          (fun n ↦
            partitionQuadraticCovariationSum
              Definition2158.dyadicPartitionSequence
              (⟨fun u ↦ N₂ u ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
              (⟨fun u ↦ N₂ u ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
              s
              n)
          atTop
          (𝓝
            (bracketDensityIntegralUpTo hbr₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)))
    (hOwnerPartitionLimit :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
          (fun s ↦
            processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
              processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
          (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
          t
          n)
      atTop
      (𝓝 (A t ω)) := by
  have hSameRowLimit :
      Tendsto
        (fun n ↦
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
            (fun k ↦
              (Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                  n -
                Theorem25_22.partitionPathwiseItoApproximationUpTo
                  (fun s ↦ processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  Definition2158.dyadicPartitionSequence
                  (Definition2158.dyadicPartitionSequence n k)
                  n) *
                (Theorem25_22.partitionPathwiseItoApproximationUpTo
                    (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                    (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                    Definition2158.dyadicPartitionSequence
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t)
                    n -
                  Theorem25_22.partitionPathwiseItoApproximationUpTo
                    (fun s ↦ processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                    (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                    Definition2158.dyadicPartitionSequence
                    (Definition2158.dyadicPartitionSequence n k)
                    n)))
        atTop
        (𝓝 (A t ω)) :=
    -- Proof comment: the independent owner-level same-row theorem already transports the owner
    -- pathwise limit to the canonical same-row cutoff surface.
    sameRowCutoffApproxMixed_tendsto_of_ownerPartitionLimit
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
      (H₁ := H₁) (H₂ := H₂) (A := A)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
      T ht hGoodω hEq₁ω hEq₂ω hSq₁ω hSq₂ω hOwnerPartitionLimit
  -- Proof comment: after the route correction, the weighted source sequence is recovered from
  -- the same-row limit by the explicit termwise identity.
  exact
    constCutoffWeightedSourceDyadic_tendsto_of_sameRowLimit
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      (hM₁ := hM₁) (hM₂ := hM₂)
      T
      (ω := ω)
      (t := t)
      hSameRowLimit

/-- Helper for Theorem 25.22: any cutoff mixed compensator that already appears in an
`...UpTo`-witness should agree on `[0,T]` with the canonical dyadic quadratic-covariation
integral for the stopped coefficients, provided the two integral coordinates are already tied to
their canonical cutoff realizations and are genuine continuous local martingales. -/
theorem partitionQuadraticCovariationSum_eq_constCutoffCanonical_of_forall_eq
    {M₁ M₂ N₁ N₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    {t : NNReal} (ht : t ≤ T)
    {ω : Ω}
    {hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁}
    {hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂}
    (hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)
    (hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)
    (n : ℕ) :
    partitionQuadraticCovariationSum
        Definition2158.dyadicPartitionSequence
        (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
        t
        n =
      Finset.sum
        (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
        (fun k ↦
          (continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
              (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
              (Definition2158.dyadicPartitionSequence n k) ω) *
            (continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
              (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
              continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                (Definition2158.dyadicPartitionSequence n k) ω)) := by
  -- Proof comment: reuse the earlier theorem-local helper so later callers and the same-row
  -- bridge share the exact same owner-to-canonical partition-row normalization.
  exact
    ownerPartitionSum_eq_constCutoffCanonicalRow
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
      (H₁ := H₁) (H₂ := H₂)
      (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
      T ht hEq₁ω hEq₂ω n

/-- Helper for Theorem 25.22: any cutoff mixed compensator that already appears in an
`...UpTo`-witness should agree on `[0,T]` with the canonical dyadic quadratic-covariation
integral for the stopped coefficients, provided the two integral coordinates are already tied to
their canonical cutoff realizations and are genuine continuous local martingales. -/
theorem constCutoffWeightedSourceDyadicTendsto_of_ownerGoodEvent
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ N₁
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ N₂
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  rcases
      existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicSquareVariationTendsto_pair
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
        (H₁ := H₁) (H₂ := H₂)
        (A₁ := bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (A₂ := bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        T hEq₁ hEq₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq with
    ⟨SSq, hSSqMeas, hSSqNull, hSSqGood⟩
  rcases
      constCutoffGoodPath_plusMinusSquareVariation
        (μ := μ) (ℱ := ℱ) (M₁ := M₁) (M₂ := M₂) hM₁ hM₂ with
    ⟨SPath, hSPathMeas, hSPathNull, hSPathGood⟩
  rcases
      constCutoffOwnerGoodEvent_of_upToWitness
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂) (A := A) (A' := A)
        (H₁ := H₁) (H₂ := H₂)
        T hA hEq₁ hEq₂ (eqUpTo_rfl (μ := μ) T A) hN₁_mart hN₂_mart with
    ⟨SOwner, hSOwnerMeas, hSOwnerNull, hSOwnerGood⟩
  have hSnull : μ (SOwner ∪ SPath ∪ SSq) = 0 := by
    have hUnionLe :
        μ (SOwner ∪ SPath ∪ SSq) ≤ μ (SOwner ∪ SPath) + μ SSq := by
      simpa [Set.union_assoc] using measure_union_le (SOwner ∪ SPath) SSq
    have hLeftNull : μ (SOwner ∪ SPath) = 0 := by
      have hLeftLe : μ (SOwner ∪ SPath) ≤ μ SOwner + μ SPath := measure_union_le SOwner SPath
      refine le_antisymm ?_ bot_le
      simpa [hSOwnerNull, hSPathNull] using hLeftLe
    refine le_antisymm ?_ bot_le
    simpa [hLeftNull, hSSqNull] using hUnionLe
  refine ⟨SOwner ∪ SPath ∪ SSq, (hSOwnerMeas.union hSPathMeas).union hSSqMeas, hSnull, ?_⟩
  intro ω hω t ht
  have hωOwner : ω ∉ SOwner := by
    exact fun hSOwnerω ↦ hω (by
      exact Set.mem_union_left SSq (Set.mem_union_left SPath hSOwnerω))
  have hωPath : ω ∉ SPath := by
    exact fun hSPathω ↦ hω (by
      exact Set.mem_union_left SSq (Set.mem_union_right SOwner hSPathω))
  have hωSq : ω ∉ SSq := by
    exact fun hSSqω ↦ hω (Set.mem_union_right (SOwner ∪ SPath) hSSqω)
  rcases hSOwnerGood hωOwner with ⟨hEq₁ω, hEq₂ω, hOwnerLimit⟩
  rcases hSSqGood hωSq with ⟨_, _, hSq₁ω, hSq₂ω⟩
  rcases hSPathGood hωPath with ⟨brAdd, brSub, hBrAdd, hBrSub⟩
  -- Proof comment: after moving the same-row theorem to the owner-partition normal form, the
  -- owner good event and the two single-coordinate square-variation good events provide exactly
  -- the hypotheses the same-row frontier now expects.
  exact
    constCutoffWeightedSourceDyadicTendstoCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
      (H₁ := H₁) (H₂ := H₂) (A := A)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
      T ht ⟨brAdd, brSub, hBrAdd, hBrSub⟩ hEq₁ω hEq₂ω hSq₁ω hSq₂ω (hOwnerLimit ht)

/-- Helper for Theorem 25.22: any cutoff mixed compensator that already appears in an
`...UpTo`-witness should agree on `[0,T]` with the canonical dyadic quadratic-covariation
integral for the stopped coefficients, provided the two integral coordinates are already tied to
their canonical cutoff realizations. -/
theorem constCutoffDyadicQuadraticCovariationTendsto
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ N₁
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ N₂
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (A t ω)) := by
  -- Proof comment: after correcting the helper interface, the mixed dyadic frontier is exactly
  -- the source-facing bridge theorem with explicit martingale data for `N₁` and `N₂`.
  exact
    constCutoffWeightedSourceDyadicTendsto_of_ownerGoodEvent
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      T hEq₁ hEq₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA

/-- Helper for Theorem 25.22: any cutoff mixed compensator that already appears in an
`...UpTo`-witness should agree on `[0,T]` with the canonical dyadic quadratic-covariation
integral for the stopped coefficients, provided the two integral coordinates are already tied to
their canonical cutoff realizations. -/
theorem eqUpTo_quadraticCovariationIntegralUpTo_of_isContinuousQuadraticCovariationProcess
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ N₁
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ N₂
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      A := by
  rcases
      constCutoffDyadicQuadraticCovariationTendsto
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
        (H₁ := H₁) (H₂ := H₂) (A := A)
        T hEq₁ hEq₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA with
    ⟨S, hSmeas, hSnull, hSlimit⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro t ht ω hNe
  by_contra hωS
  have hEq :
      Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω =
        A t ω := by
    -- Proof comment: off the fixed null set, the dyadic approximations converge to `A t ω`, so
    -- the canonical `limUnder` definition of the cutoff mixed compensator has that same value.
    simpa [Theorem25_22.quadraticCovariationIntegralUpTo,
      Theorem25_22.pathwiseQuadraticCovariationIntegral] using
      (hSlimit hωS ht).limUnder_eq
  exact hNe hEq

/-- Helper for Theorem 25.22: the zero compensator has almost surely locally finite variation. -/
lemma zeroProcess_locallyFiniteVariation :
    ∀ᵐ ω : Ω ∂μ,
      LocallyBoundedVariationOn
        (⟨fun t ↦ (0 : ℝ), continuous_const⟩ : C(NNReal, ℝ))
        Set.univ := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hzeroMem :
      (0 : C(NNReal, ℝ)) ∈ continuousVariationSubmodule := by
    exact Submodule.zero_mem continuousVariationSubmodule
  -- Proof comment: the zero path is a canonical element of the continuous-variation submodule,
  -- so the owner-side bounded-variation property follows immediately.
  simpa using (mem_continuousVariationSubmodule_iff (0 : C(NNReal, ℝ))).1 hzeroMem

/-- Helper for Theorem 25.22: a continuous monotone real-valued path has locally finite
variation. -/
lemma locallyFiniteVariation_of_continuous_monotone
    {A : NNReal → Ω → ℝ}
    (hA_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ A t ω)
    (hA_mono : ∀ ω : Ω, Monotone (fun t : NNReal ↦ A t ω)) :
    ∀ᵐ ω : Ω ∂μ,
      LocallyBoundedVariationOn
        (⟨fun t ↦ A t ω, hA_cont ω⟩ : C(NNReal, ℝ))
        Set.univ := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  let G : C(NNReal, ℝ) := ⟨fun t ↦ A t ω, hA_cont ω⟩
  let Z : C(NNReal, ℝ) := 0
  have hG : G = G - Z := by
    ext t
    simp [G, Z]
  have hG_mono : Monotone G := hA_mono ω
  have hZ_mono : Monotone Z := by
    intro s t hst
    simp [Z]
  exact locallyBoundedVariationOnUnivOfSubMonotone hG hG_mono hZ_mono

/-- Helper for Theorem 25.22: a local-martingale product already packages the zero process as a
genuine quadratic-covariation compensator. -/
private theorem isContinuousQuadraticCovariationProcess_zero_of_localMartingaleMul
    {N₁ N₂ : NNReal → Ω → ℝ}
    (hMul : IsLocalMartingale ℱ μ (fun t ω ↦ N₁ t ω * N₂ t ω)) :
    IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ 0 := by
  -- Proof comment: for the zero compensator, the only nontrivial owner field is that the product
  -- process itself is a local martingale.
  refine
    { zero := by
        funext ω
        simp
      adapted := by
        exact adapted_const' ℱ (fun _ : NNReal ↦ (0 : ℝ))
      continuous := by
        intro ω
        simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      locally_finite_variation := zeroProcess_locallyFiniteVariation (μ := μ)
      local_martingale_mul_sub := ?_ }
  simpa using hMul

/-- Helper for Theorem 25.22: the nonnegative rationals are dense in `NNReal`. -/
private lemma nnratDense : Dense (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
  -- Proof comment: every open interval in `NNReal` contains a nonnegative rational point.
  refine dense_of_exists_between ?_
  intro a b hab
  rcases NNReal.lt_iff_exists_rat_btwn a b |>.1 hab with ⟨q, hq0, haq, hqb⟩
  let q₀ : ℚ≥0 := ⟨q, hq0⟩
  refine ⟨(q₀ : NNReal), ?_, ?_, ?_⟩
  · exact ⟨q₀, rfl⟩
  · have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq0
    simpa [q₀, Real.toNNReal_of_nonneg hq'] using haq
  · have hq' : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq0
    simpa [q₀, Real.toNNReal_of_nonneg hq'] using hqb

/-- Helper for Theorem 25.22: a continuous path is determined by its values on `ℚ≥0`. -/
private lemma continuous_eq_const_of_eqOnNNRat
    {f : NNReal → ℝ} (hf : Continuous f) {c : ℝ}
    (hq : ∀ q : ℚ≥0, f q = c) :
    ∀ t : NNReal, f t = c := by
  -- Proof comment: continuity extends the rational-time identity to the dense subset `ℚ≥0`.
  have hEq :
      Set.EqOn f (fun _ : NNReal ↦ c) (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    intro t ht
    rcases ht with ⟨q, rfl⟩
    simpa using hq q
  intro t
  exact congrFun (Continuous.ext_on nnratDense hf continuous_const hEq) t

/-- Helper for Theorem 25.22: an all-times almost-sure identity transports deterministic-time
stopped slices under a fixed clock. -/
private theorem stoppedProcess_congr_process_ae_allTimes_local
    {M N : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hMN : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω)
    (t : NNReal) :
    stoppedProcess M τ t =ᵐ[μ] stoppedProcess N τ t := by
  filter_upwards [hMN] with ω hω
  simpa [stoppedProcess] using hω ((min (t : ENNReal) (τ ω)).untopA)

/-- Helper for Theorem 25.22: if a continuous local martingale has almost surely vanishing
square variation, then its square is again a continuous local martingale. -/
private lemma isContinuousLocalMartingale_sq_of_ae_squareVariation_eq_zero
    {X B : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hB : IsContinuousSquareVariationProcess ℱ μ X B)
    (hzero : ∀ᵐ ω ∂μ, ∀ t : NNReal, B t ω = 0) :
    IsContinuousLocalMartingale ℱ μ (fun t ω ↦ X t ω ^ 2) := by
  have hSquareAdapted : Adapted ℱ (fun t ω ↦ X t ω ^ 2) := by
    simpa [pow_two] using hX.adapted.mul hX.adapted
  have hSquareCont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω ^ 2 := by
    intro ω
    simpa [pow_two] using (hX.continuous ω).mul (hX.continuous ω)
  refine ⟨?_, hSquareCont⟩
  -- Proof comment: `X² - B` is already a local martingale, and the bracket vanishes almost
  -- surely at all times.
  have hEqAll : ∀ᵐ ω ∂μ, ∀ t : NNReal,
      (fun t ω ↦ X t ω ^ 2 - B t ω) t ω = X t ω ^ 2 := by
    filter_upwards [hzero] with ω hω t
    simpa using hω t
  rcases
      (isLocalMartingale_iff ℱ μ (fun t ω ↦ X t ω ^ 2 - B t ω)).1
        hB.local_martingale_sq_sub.local_martingale with
    ⟨_hAdapted, τSeq, hτSeq⟩
  refine (isLocalMartingale_iff ℱ μ (fun t ω ↦ X t ω ^ 2)).2 ⟨hSquareAdapted, τSeq, ?_⟩
  rcases (isLocalizingSequence_iff ℱ μ (fun t ω ↦ X t ω ^ 2 - B t ω) τSeq).1 hτSeq with
    ⟨hStopping, hLim, hStopped⟩
  refine (isLocalizingSequence_iff ℱ μ (fun t ω ↦ X t ω ^ 2) τSeq).2 ⟨hStopping, hLim, ?_⟩
  intro n
  obtain ⟨hMart, hUI⟩ := hStopped n
  have hStoppedEq :
      ∀ t : NNReal,
        stoppedProcess (fun t ω ↦ X t ω ^ 2 - B t ω) (τSeq n) t =ᵐ[μ]
          stoppedProcess (fun t ω ↦ X t ω ^ 2) (τSeq n) t := by
    intro t
    exact
      stoppedProcess_congr_process_ae_allTimes_local (μ := μ) hEqAll t
  have hStoppedStrong :
      StronglyAdapted ℱ (stoppedProcess (fun t ω ↦ X t ω ^ 2) (τSeq n)) :=
    (hSquareAdapted.stronglyAdapted.stoppedProcess hSquareCont (hStopping n))
  refine ⟨?_, ?_⟩
  · refine ⟨hStoppedStrong, ?_⟩
    intro s t hst
    exact
      (MeasureTheory.condExp_congr_ae (hStoppedEq t)).symm.trans
        ((hMart.condExp_ae_eq hst).trans (hStoppedEq s))
  · exact hUI.ae_eq hStoppedEq

/-- Helper for Theorem 25.22: if `M` and `M²` are martingales, then the terminal-initial cross
moment equals the initial square moment. -/
private lemma integral_terminal_mul_initial_eq_initial_sq_of_martingale_sq_martingale
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hMsq : Martingale (fun t ω ↦ M t ω ^ 2) ℱ μ) (t : NNReal) :
    μ[fun ω ↦ M t ω * M 0 ω] = μ[fun ω ↦ M 0 ω ^ 2] := by
  have hMt_meas : AEStronglyMeasurable (M t) μ := by
    exact ((hM.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
  have hM0_meas : AEStronglyMeasurable (M 0) μ := by
    exact ((hM.stronglyMeasurable 0).mono (ℱ.le 0)).aestronglyMeasurable
  have hMtLp : MemLp (M t) 2 μ :=
    (memLp_two_iff_integrable_sq hMt_meas).2 (hMsq.integrable t)
  have hM0Lp : MemLp (M 0) 2 μ :=
    (memLp_two_iff_integrable_sq hM0_meas).2 (hMsq.integrable 0)
  have hProdInt : Integrable (fun ω ↦ M t ω * M 0 ω) μ := by
    simpa using MemLp.integrable_mul hMtLp hM0Lp
  have hCond :
      μ[(fun ω ↦ M t ω * M 0 ω) | ℱ 0] =ᵐ[μ] fun ω ↦ M 0 ω ^ 2 := by
    -- Proof comment: factor out the `ℱ₀`-measurable initial value from the conditional
    -- expectation and then apply the martingale identity.
    refine
      (condExp_mul_of_stronglyMeasurable_right
          (hM.stronglyMeasurable 0)
          hProdInt
          (hM.integrable t)).trans ?_
    refine ((hM.condExp_ae_eq (zero_le t)).mul Filter.EventuallyEq.rfl).trans ?_
    filter_upwards with ω
    simp [pow_two]
  -- Proof comment: integrating the conditional-expectation identity yields the scalar
  -- cross-term formula.
  calc
    μ[fun ω ↦ M t ω * M 0 ω] = μ[μ[(fun ω ↦ M t ω * M 0 ω) | ℱ 0]] := by
      symm
      exact integral_condExp (ℱ.le 0)
    _ = μ[fun ω ↦ M 0 ω ^ 2] := by
      exact integral_congr_ae hCond

/-- Helper for Theorem 25.22: once a martingale and its square are martingales, every fixed-time
value agrees almost surely with the initial value. -/
private lemma ae_eq_initial_at_time_of_martingale_sq_martingale
    {M : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hMsq : Martingale (fun t ω ↦ M t ω ^ 2) ℱ μ) (t : NNReal) :
    M t =ᵐ[μ] M 0 := by
  let Y : Ω → ℝ := fun ω ↦ M t ω - M 0 ω
  have hMt_meas : AEStronglyMeasurable (M t) μ := by
    exact ((hM.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
  have hM0_meas : AEStronglyMeasurable (M 0) μ := by
    exact ((hM.stronglyMeasurable 0).mono (ℱ.le 0)).aestronglyMeasurable
  have hMtLp : MemLp (M t) 2 μ :=
    (memLp_two_iff_integrable_sq hMt_meas).2 (hMsq.integrable t)
  have hM0Lp : MemLp (M 0) 2 μ :=
    (memLp_two_iff_integrable_sq hM0_meas).2 (hMsq.integrable 0)
  have hYLp : MemLp Y 2 μ := by
    simpa [Y] using hMtLp.sub hM0Lp
  have hProdInt : Integrable (fun ω ↦ M t ω * M 0 ω) μ := by
    simpa using MemLp.integrable_mul hMtLp hM0Lp
  have hCrossEq :
      μ[fun ω ↦ M t ω * M 0 ω] = μ[fun ω ↦ M 0 ω ^ 2] :=
    integral_terminal_mul_initial_eq_initial_sq_of_martingale_sq_martingale hM hMsq t
  have hSqEq : μ[fun ω ↦ M t ω ^ 2] = μ[fun ω ↦ M 0 ω ^ 2] := by
    simpa using (hMsq.setIntegral_eq (zero_le t) (s := Set.univ) MeasurableSet.univ).symm
  have hSecondMomentZero : ∫ ω, Y ω ^ 2 ∂μ = 0 := by
    have hMidInt :
        Integrable (fun ω ↦ M t ω ^ 2 - 2 * (M t ω * M 0 ω)) μ := by
      exact (hMsq.integrable t).sub (hProdInt.const_mul 2)
    have hSecondMoment :
        ∫ ω, (M t ω - M 0 ω) ^ 2 ∂μ =
          ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ + ∫ ω, M 0 ω ^ 2 ∂μ := by
      have hMid :
          ∫ ω, (M t ω ^ 2 - 2 * (M t ω * M 0 ω)) ∂μ =
            ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ := by
        calc
          ∫ ω, (M t ω ^ 2 - 2 * (M t ω * M 0 ω)) ∂μ =
              ∫ ω, M t ω ^ 2 ∂μ - ∫ ω, 2 * (M t ω * M 0 ω) ∂μ := by
            simpa using integral_sub' (hMsq.integrable t) (hProdInt.const_mul 2)
          _ = ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ := by
            rw [integral_const_mul]
      calc
        ∫ ω, (M t ω - M 0 ω) ^ 2 ∂μ =
            ∫ ω, ((M t ω ^ 2 - 2 * (M t ω * M 0 ω)) + M 0 ω ^ 2) ∂μ := by
              congr 1
              ext ω
              ring
        _ = ∫ ω, (M t ω ^ 2 - 2 * (M t ω * M 0 ω)) ∂μ + ∫ ω, M 0 ω ^ 2 ∂μ := by
              simpa using integral_add hMidInt (hMsq.integrable 0)
        _ = ∫ ω, M t ω ^ 2 ∂μ - 2 * ∫ ω, M t ω * M 0 ω ∂μ + ∫ ω, M 0 ω ^ 2 ∂μ := by
              rw [hMid]
    calc
      ∫ ω, Y ω ^ 2 ∂μ = ∫ ω, (M t ω - M 0 ω) ^ 2 ∂μ := by rfl
      _ = μ[fun ω ↦ M t ω ^ 2] - 2 * μ[fun ω ↦ M t ω * M 0 ω] + μ[fun ω ↦ M 0 ω ^ 2] := by
        simpa using hSecondMoment
      _ = 0 := by
        nlinarith [hCrossEq, hSqEq]
  have hYsqInt : Integrable (fun ω ↦ Y ω ^ 2) μ := hYLp.integrable_sq
  have hYsqNonneg : 0 ≤ᵐ[μ] fun ω ↦ Y ω ^ 2 :=
    Filter.Eventually.of_forall fun ω ↦ sq_nonneg _
  filter_upwards
    [(integral_eq_zero_iff_of_nonneg_ae hYsqNonneg hYsqInt).1 hSecondMomentZero]
    with ω hω
  -- Proof comment: a nonnegative square vanishes exactly when the increment itself vanishes.
  exact sub_eq_zero.mp <| by
    simpa [Y] using (sq_eq_zero_iff.mp hω)

/-- Helper for Theorem 25.22: squaring a bounded process preserves boundedness. -/
private lemma isBoundedProcess_sq
    {M : NNReal → Ω → ℝ} (hbounded : IsBoundedProcess M) :
    IsBoundedProcess (fun t ω ↦ M t ω ^ 2) := by
  rcases hbounded with ⟨C, hC_nonneg, hC⟩
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro t ω
  have hCω := hC t ω
  -- Proof comment: `|M_t| ≤ C` forces `(M_t)^2 ≤ C²`.
  have hsq : M t ω ^ 2 ≤ C ^ 2 := by
    have hsq' : |M t ω| ^ 2 ≤ C ^ 2 := by
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hC_nonneg] using hCω)
    simpa [sq_abs] using hsq'
  have hsq_nonneg : 0 ≤ M t ω ^ 2 := by positivity
  simpa [abs_of_nonneg hsq_nonneg] using hsq

/-- Helper for Theorem 25.22: a bounded stopped process inherits the martingale property for its
square from the square local-martingale owner. -/
private lemma martingale_sq_of_bounded_stoppedProcess
    {M : NNReal → Ω → ℝ}
    (hMsq : IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω ^ 2))
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ)
    (hbounded : IsBoundedProcess (stoppedProcess M τ)) :
    Martingale (fun t ω ↦ (stoppedProcess M τ t ω) ^ 2) ℱ μ := by
  have hStoppedSqLocal :
      IsLocalMartingale ℱ μ (stoppedProcess (fun t ω ↦ M t ω ^ 2) τ) := by
    -- Proof comment: stop the square local martingale first.
    exact
      isLocalMartingale_stoppedProcess
        hMsq.local_martingale
        hMsq.continuous
        hτ
  have hTargetLocal :
      IsLocalMartingale ℱ μ (fun t ω ↦ (stoppedProcess M τ t ω) ^ 2) := by
    -- Proof comment: stopping commutes pointwise with squaring.
    simpa [stoppedProcess] using hStoppedSqLocal
  -- Proof comment: boundedness upgrades the stopped square local martingale to a genuine
  -- martingale.
  exact
    martingale_of_bounded_local_martingale
      hTargetLocal
      (boundedInTimeAe_of_boundedProcess (isBoundedProcess_sq hbounded))

/-- Helper for Theorem 25.22: convergence of a localizing sequence to `∞` forces the fixed-time
stopped values to converge to the original value. -/
private lemma ae_tendsto_stoppedProcess_at_time_of_stoppingTimeApproximationUpToInfinity
    {M : NNReal → Ω → ℝ} {τSeq : ℕ → Ω → ENNReal}
    (hApprox :
      IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ (∞ : ENNReal))) (u : NNReal) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedProcess M (τSeq n) u ω) atTop (nhds (M u ω)) := by
  rcases hApprox with ⟨_, _, hlim⟩
  filter_upwards [hlim] with ω hω
  rcases hω with ⟨_, hωtendsto⟩
  -- Proof comment: once `τₙ ω` lies beyond `u`, the stop is inactive at time `u`.
  have hu_eventually : ∀ᶠ n in atTop, (u : ENNReal) ≤ τSeq n ω :=
    (ENNReal.tendsto_nhds_top_iff_nnreal.1 hωtendsto u).mono fun _ hn ↦ le_of_lt hn
  have hEventuallyEq :
      (fun n ↦ stoppedProcess M (τSeq n) u ω) =ᶠ[atTop] fun _ ↦ M u ω :=
    hu_eventually.mono fun _ hn ↦ stoppedProcess_eq_of_le hn
  exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds

/-- Helper for Theorem 25.22: bracket-zero continuous local martingales are constant at a fixed
deterministic time almost surely. -/
private lemma ae_eq_initial_at_time_of_ae_squareVariation_eq_zero
    {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hzero : ∀ᵐ ω ∂μ, ∀ t : NNReal, continuousSquareVariationProcess hX t ω = 0)
    (t : NNReal) :
    X t =ᵐ[μ] X 0 := by
  -- Proof comment: this is exactly the Chapter 21 bracket-zero theorem specialized to the local
  -- chosen square-variation witness.
  exact
    _root_.ProbabilityTheory.ae_eq_initial_at_time_of_ae_squareVariation_eq_zero
      (μ := μ)
      ℱ
      hX
      hzero
      t

/-- Helper for Theorem 25.22: if two continuous local martingales share the same square-variation
witness and that same witness is also their quadratic-covariation process, then their difference
has zero square variation. -/
private lemma selfContinuousQuadraticCovariation_of_squareVariation
    {M A : NNReal → Ω → ℝ}
    (hA : IsContinuousSquareVariationProcess ℱ μ M A) :
    IsContinuousQuadraticCovariationProcess ℱ μ M M A := by
  refine
    { zero := hA.zero
      adapted := hA.adapted
      continuous := hA.continuous
      locally_finite_variation :=
        locallyFiniteVariation_of_continuous_monotone
          hA.continuous
          hA.monotone
      local_martingale_mul_sub := ?_ }
  -- Proof comment: on the diagonal, the compensated product `M * M - A` is exactly the
  -- square-variation local martingale `M^2 - A`.
  simpa [pow_two] using hA.local_martingale_sq_sub.local_martingale

/-- Helper for Theorem 25.22: if two continuous local martingales share the same square-variation
witness and that same witness is also their quadratic-covariation process, then their difference
has zero square variation. -/
private lemma sub_zeroSquareVariation_of_sharedWitness
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A) :
    IsContinuousSquareVariationProcess ℱ μ
      (fun t ω ↦ M t ω - N t ω)
      (fun _ _ ↦ (0 : ℝ)) := by
  refine
    { zero := ?_
      adapted := ?_
      continuous := ?_
      monotone := ?_
      local_martingale_sq_sub := ?_ }
  · -- Proof comment: the zero square-variation witness starts from `0` by definition.
    funext ω
    simp
  · -- Proof comment: the zero witness is adapted at every deterministic time.
    intro t
    simpa using (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
  · -- Proof comment: the zero witness is pathwise continuous.
    intro ω
    simpa using (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  · -- Proof comment: the zero witness is monotone because it is constant.
    intro ω s t hst
    simp
  · -- Proof comment: expand `(M - N)^2` as
    -- `(M^2 - A) + (N^2 - A) - 2 * (M * N - A)` and reuse the three local-martingale clauses.
    have hQuadCont :
        IsContinuousLocalMartingale ℱ μ (fun t ω ↦ M t ω * N t ω - A t ω) := by
      refine ⟨hQuad.local_martingale_mul_sub, ?_⟩
      intro ω
      exact (hMmart.continuous ω).mul (hNmart.continuous ω) |>.sub (hQuad.continuous ω)
    refine
      { local_martingale := ?_
        continuous := ?_ }
    · let hDoubleQuad : IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            (M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)) :=
          isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hQuadCont hQuadCont
      have hTarget :
          IsContinuousLocalMartingale ℱ μ
            (fun t ω ↦
              (M t ω ^ 2 - A t ω) +
                ((N t ω ^ 2 - A t ω) -
                  ((M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)))) :=
        isContinuousLocalMartingale_addLocal
          (ℱ := ℱ)
          (μ := μ)
          hAleft.local_martingale_sq_sub
          (isContinuousLocalMartingale_subLocal
            (ℱ := ℱ)
            (μ := μ)
            hAright.local_martingale_sq_sub
            hDoubleQuad)
      convert hTarget.local_martingale using 1
      funext t ω
      ring
    · intro ω
      let hDoubleQuad : IsContinuousLocalMartingale ℱ μ
          (fun t ω ↦
            (M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)) :=
          isContinuousLocalMartingale_addLocal (ℱ := ℱ) (μ := μ) hQuadCont hQuadCont
      let hTarget :
          IsContinuousLocalMartingale ℱ μ
            (fun t ω ↦
              (M t ω ^ 2 - A t ω) +
                ((N t ω ^ 2 - A t ω) -
                  ((M t ω * N t ω - A t ω) + (M t ω * N t ω - A t ω)))) :=
        isContinuousLocalMartingale_addLocal
          (ℱ := ℱ)
          (μ := μ)
          hAleft.local_martingale_sq_sub
          (isContinuousLocalMartingale_subLocal
            (ℱ := ℱ)
            (μ := μ)
            hAright.local_martingale_sq_sub
            hDoubleQuad)
      convert hTarget.continuous ω using 1
      funext t
      ring

/-- Helper for Theorem 25.22: a continuous local martingale with identically zero square
variation is almost surely zero at every fixed deterministic time once its initial value is zero.
-/
private lemma ae_eq_zero_at_time_of_zeroSquareVariation
    {X : NNReal → Ω → ℝ}
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hXsq : IsContinuousSquareVariationProcess ℱ μ X (fun _ _ ↦ (0 : ℝ)))
    (hX0 : X 0 =ᵐ[μ] fun _ : Ω ↦ 0)
    (T : NNReal) :
    X T =ᵐ[μ] fun _ : Ω ↦ 0 := by
  rcases _root_.ProbabilityTheory.existsUnique_continuousSquareVariationProcess
      (ℱ := ℱ) (μ := μ) hX with
    ⟨B, _hB, huniq⟩
  have hCanonEqB :
      AreIndistinguishable μ (continuousSquareVariationProcess hX) B := by
    exact huniq _ (continuousSquareVariationProcess_spec hX)
  have hBEqZero :
      AreIndistinguishable μ B (fun _ _ ↦ (0 : ℝ)) := by
    exact huniq _ hXsq
  have hCanonEqZero :
      AreIndistinguishable μ (continuousSquareVariationProcess hX) (fun _ _ ↦ (0 : ℝ)) := by
    exact areIndistinguishable_trans hCanonEqB hBEqZero
  have hZeroAllTimes :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, continuousSquareVariationProcess hX t ω = 0 := by
    rcases hCanonEqZero with ⟨bad, _hbad_meas, hbad_null, hbad_sub⟩
    have hbad_ae : ∀ᵐ ω ∂μ, ω ∉ bad :=
      compl_mem_ae_iff.mpr hbad_null
    filter_upwards [hbad_ae] with ω hωbad t
    by_contra hneq
    exact hωbad (hbad_sub t hneq)
  have hConstAtTime :
      X T =ᵐ[μ] X 0 :=
    ae_eq_initial_at_time_of_ae_squareVariation_eq_zero ℱ hX hZeroAllTimes T
  exact hConstAtTime.trans hX0

/-- Helper for Theorem 25.22: two continuous local martingales that share the same square
variation witness and the same quadratic-covariation witness agree almost surely at every fixed
deterministic time once they agree at time `0`. -/
private lemma ae_eq_at_time_of_sharedWitness
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hZero : M 0 =ᵐ[μ] N 0)
    (T : NNReal) :
    M T =ᵐ[μ] N T := by
  have hSubSq :
      IsContinuousSquareVariationProcess ℱ μ
        (fun t ω ↦ M t ω - N t ω)
        (fun _ _ ↦ (0 : ℝ)) :=
    sub_zeroSquareVariation_of_sharedWitness hMmart hNmart hAleft hAright hQuad
  have hSubZero :
      (fun ω ↦ M 0 ω - N 0 ω) =ᵐ[μ] fun _ : Ω ↦ 0 := by
    -- Proof comment: the shared initial-value hypothesis turns the difference process into a
    -- zero-start continuous local martingale.
    filter_upwards [hZero] with ω hω
    simp [hω]
  have hSubAtTime :
      (fun ω ↦ M T ω - N T ω) =ᵐ[μ] fun _ : Ω ↦ 0 :=
    ae_eq_zero_at_time_of_zeroSquareVariation
      (ℱ := ℱ)
      (μ := μ)
      (X := fun t ω ↦ M t ω - N t ω)
      (isContinuousLocalMartingale_subLocal (ℱ := ℱ) (μ := μ) hMmart hNmart)
      hSubSq
      hSubZero
      T
  -- Proof comment: once the difference vanishes almost surely at time `T`, the two endpoint
  -- values agree there.
  filter_upwards [hSubAtTime] with ω hω
  exact sub_eq_zero.mp hω

/-- Helper for Theorem 25.22: deterministic-time modifications of continuous paths agree
simultaneously at all times almost surely. -/
private theorem ae_all_eq_of_modifications_of_continuous
    {X Y : NNReal → Ω → ℝ}
    (hXY : AreModifications μ X Y)
    (hXcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    (hYcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, X t ω = Y t ω := by
  have hRat : ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, X (q : NNReal) ω = Y (q : NNReal) ω := by
    rw [ae_all_iff]
    intro q
    simpa using hXY (q : NNReal)
  filter_upwards [hRat] with ω hωRat t
  have hEqOn :
      Set.EqOn (fun s : NNReal ↦ X s ω) (fun s : NNReal ↦ Y s ω)
        (Set.range fun q : ℚ≥0 ↦ (q : NNReal)) := by
    intro s hs
    rcases hs with ⟨q, rfl⟩
    exact hωRat q
  -- Proof comment: rational nonnegative times are dense in `NNReal`, so continuity upgrades the
  -- fixed-time modification relation to one null set controlling all times.
  exact congrFun (Continuous.ext_on nnratDense (hXcont ω) (hYcont ω) hEqOn) t

/-- Helper for Theorem 25.22: the shared-witness comparison can be upgraded from every
deterministic time separately to one all-times almost-sure identity. -/
private lemma ae_eq_allTimes_of_sharedWitness
    {M N A : NNReal → Ω → ℝ}
    (hMmart : IsContinuousLocalMartingale ℱ μ M)
    (hNmart : IsContinuousLocalMartingale ℱ μ N)
    (hAleft : IsContinuousSquareVariationProcess ℱ μ M A)
    (hAright : IsContinuousSquareVariationProcess ℱ μ N A)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hZero : M 0 =ᵐ[μ] N 0) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω := by
  have hMods : AreModifications μ M N := by
    intro t
    -- Proof comment: the fixed-time shared-witness comparison supplies the modification relation.
    exact
      ae_eq_at_time_of_sharedWitness
        (ℱ := ℱ)
        (μ := μ)
        hMmart
        hNmart
        hAleft
        hAright
        hQuad
        hZero
        t
  -- Proof comment: continuity of both sample-path families upgrades the timewise modification
  -- relation to one all-times almost-sure identity.
  exact
    ae_all_eq_of_modifications_of_continuous
      (μ := μ)
      hMods
      hMmart.continuous
      hNmart.continuous

/-- Helper for Theorem 25.22: independence of the source path maps is preserved by deterministic
cutoff at time `T`. -/
theorem indepFun_constCutoffPath
    {X Y : NNReal → Ω → ℝ}
    (T : NNReal)
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ X t ω)
        (fun ω ↦ fun t : NNReal ↦ Y t ω) μ) :
    IndepFun
      (fun ω ↦ fun t : NNReal ↦
        processBeforeStoppingTime X (fun _ ↦ (T : ENNReal)) t ω)
      (fun ω ↦ fun t : NNReal ↦
        processBeforeStoppingTime Y (fun _ ↦ (T : ENNReal)) t ω) μ := by
  let cutoffPath : (NNReal → ℝ) → NNReal → ℝ :=
    fun f t ↦ if t ≤ T then f t else 0
  have hcutoff_meas : Measurable cutoffPath := by
    -- Proof comment: the deterministic cutoff acts pointwise on the path, so measurability is a
    -- coordinatewise `measurable_pi_lambda` check.
    refine measurable_pi_lambda _ fun t ↦ ?_
    by_cases ht : t ≤ T
    · simpa [cutoffPath, ht] using
        (measurable_pi_apply t : Measurable fun f : NNReal → ℝ ↦ f t)
    · simpa [cutoffPath, ht] using
        (measurable_const : Measurable fun _ : NNReal → ℝ ↦ (0 : ℝ))
  have hcompX :
      cutoffPath ∘ (fun ω ↦ fun t : NNReal ↦ X t ω) =
        fun ω ↦ fun t : NNReal ↦
          processBeforeStoppingTime X (fun _ ↦ (T : ENNReal)) t ω := by
    funext ω t
    by_cases ht : t ≤ T
    · have htle : (t : ENNReal) ≤ (T : ENNReal) := by
        exact_mod_cast ht
      -- Proof comment: on `[0, T]`, deterministic cutoff leaves the path unchanged.
      simp [cutoffPath, ht, ProbabilityTheory.processBeforeStoppingTime_apply, htle]
    · have htle : ¬ (t : ENNReal) ≤ (T : ENNReal) := by
        intro h
        exact ht (by exact_mod_cast h)
      -- Proof comment: beyond `T`, deterministic cutoff replaces the path value by `0`.
      simp [cutoffPath, ht, ProbabilityTheory.processBeforeStoppingTime_apply, htle]
  have hcompY :
      cutoffPath ∘ (fun ω ↦ fun t : NNReal ↦ Y t ω) =
        fun ω ↦ fun t : NNReal ↦
          processBeforeStoppingTime Y (fun _ ↦ (T : ENNReal)) t ω := by
    funext ω t
    by_cases ht : t ≤ T
    · have htle : (t : ENNReal) ≤ (T : ENNReal) := by
        exact_mod_cast ht
      -- Proof comment: the second path undergoes the same deterministic cutoff normalization.
      simp [cutoffPath, ht, ProbabilityTheory.processBeforeStoppingTime_apply, htle]
    · have htle : ¬ (t : ENNReal) ≤ (T : ENNReal) := by
        intro h
        exact ht (by exact_mod_cast h)
      -- Proof comment: outside `[0, T]`, the cutoff again kills the path pointwise.
      simp [cutoffPath, ht, ProbabilityTheory.processBeforeStoppingTime_apply, htle]
  -- Proof comment: independence is stable under measurable postcomposition on both coordinates.
  simpa [Function.comp, hcompX, hcompY] using
    IndepFun.comp hIndep hcutoff_meas hcutoff_meas

/-- Helper for Theorem 25.22: independence of source path maps is preserved by deterministic
stopping at time `U`. -/
private theorem indepFun_constStoppedPath
    {X Y : NNReal → Ω → ℝ}
    (U : NNReal)
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ X t ω)
        (fun ω ↦ fun t : NNReal ↦ Y t ω) μ) :
    IndepFun
      (fun ω ↦ fun t : NNReal ↦ stoppedProcess X (fun _ ↦ (U : ENNReal)) t ω)
      (fun ω ↦ fun t : NNReal ↦ stoppedProcess Y (fun _ ↦ (U : ENNReal)) t ω) μ := by
  let stoppedPath : (NNReal → ℝ) → NNReal → ℝ := fun f t ↦ f (min t U)
  have hStopped_meas : Measurable stoppedPath := by
    -- Proof comment: deterministic stopping only precomposes a path with the measurable time map
    -- `t ↦ min t U`, so coordinatewise measurability is immediate.
    refine measurable_pi_lambda _ fun t ↦ ?_
    simpa [stoppedPath] using
      (measurable_pi_apply (min t U) : Measurable fun f : NNReal → ℝ ↦ f (min t U))
  have hcompX :
      stoppedPath ∘ (fun ω ↦ fun t : NNReal ↦ X t ω) =
        fun ω ↦ fun t : NNReal ↦ stoppedProcess X (fun _ ↦ (U : ENNReal)) t ω := by
    funext ω t
    -- Proof comment: a deterministic stop evaluates the source path exactly at the clipped time.
    simpa [stoppedPath] using
      congrFun (stoppedProcessConstTime_eq_min (X := X) U t).symm ω
  have hcompY :
      stoppedPath ∘ (fun ω ↦ fun t : NNReal ↦ Y t ω) =
        fun ω ↦ fun t : NNReal ↦ stoppedProcess Y (fun _ ↦ (U : ENNReal)) t ω := by
    funext ω t
    -- Proof comment: the second path undergoes the same deterministic clipping.
    simpa [stoppedPath] using
      congrFun (stoppedProcessConstTime_eq_min (X := Y) U t).symm ω
  -- Proof comment: independence is stable under the same measurable deterministic stopping map on
  -- both path coordinates.
  simpa [Function.comp, hcompX, hcompY] using
    IndepFun.comp hIndep hStopped_meas hStopped_meas

/-- Helper for Theorem 25.22: deterministic cutoff followed by deterministic stopping still
preserves independence of the source path maps. -/
private theorem indepFun_constStoppedConstCutoffPath
    {X Y : NNReal → Ω → ℝ}
    (T U : NNReal)
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ X t ω)
        (fun ω ↦ fun t : NNReal ↦ Y t ω) μ) :
    IndepFun
      (fun ω ↦ fun t : NNReal ↦
        stoppedProcess
          (processBeforeStoppingTime X (fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (U : ENNReal))
          t
          ω)
      (fun ω ↦ fun t : NNReal ↦
        stoppedProcess
          (processBeforeStoppingTime Y (fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (U : ENNReal))
          t
          ω) μ := by
  -- Proof comment: first cut off both source paths at the deterministic horizon `T`, then apply
  -- the deterministic stopping map at `U`; each step preserves independence by measurable
  -- postcomposition on the path space.
  exact
    indepFun_constStoppedPath
      (μ := μ)
      U
      (indepFun_constCutoffPath (μ := μ) T hIndep)

/-- Helper for Theorem 25.22: once a Brownian extension witness is available, the only remaining
independence input is the Chapter 21 almost-sure vanishing of Brownian mixed covariation. -/
theorem aeHasQuadraticCovariationAlong_zero_of_indepBrownian
    {W₁ W₂ : NNReal → Ω → ℝ}
    (hW₁ : IsBrownianMotion μ W₁)
    (hW₂ : IsBrownianMotion μ W₂)
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ W₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ W₂ t ω) μ) :
    ∀ᵐ ω ∂μ,
      ∀ hW₁ω : Continuous (processPath W₁ ω),
      ∀ hW₂ω : Continuous (processPath W₂ ω),
        HasQuadraticCovariationAlong
          (⟨processPath W₁ ω, hW₁ω⟩ : C(NNReal, ℝ))
          (⟨processPath W₂ ω, hW₂ω⟩ : C(NNReal, ℝ))
          0 := by
  -- Proof comment: this is exactly Corollary 21.65 on the theorem-local pathwise surface, so
  -- the remaining independence blocker is the owner-descent from the Brownian extension rather
  -- than the Brownian zero-covariation theorem itself.
  exact
    _root_.ProbabilityTheory.covariation_ae_eq_zero_of_indep_brownian
      (μ := μ) (W := W₁) (Wtilde := W₂) hW₁ hW₂ hIndep

/-- Helper for Theorem 25.22: a genuine zero quadratic-covariation process for the canonical
cutoff pair already yields the downstream `EqUpTo μ T ... 0` statement. -/
theorem eqUpTo_zero_of_isContinuousQuadraticCovariationProcess_zero
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      0 := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  -- Proof comment: with short aliases for the two canonical cutoff coordinates, the generic
  -- compensator-identification theorem specializes directly to the zero process.
  simpa [N₁c, N₂c] using
    (eqUpTo_quadraticCovariationIntegralUpTo_of_isContinuousQuadraticCovariationProcess
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁c) (N₂ := N₂c)
      (H₁ := H₁) (H₂ := H₂) (A := 0)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T
      (eqUpTo_rfl (μ := μ) T N₁c)
      (eqUpTo_rfl (μ := μ) T N₂c)
      hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZero)

/-- Helper for Theorem 25.22: source-path independence should force the canonical cutoff mixed
pair to have zero quadratic covariation as a genuine owner-side process. -/
private theorem constCutoffProduct_adapted_continuous
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))) :
    Adapted ℱ
        (fun t ω ↦
          continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) ∧
      (∀ ω : Ω,
        Continuous fun t : NNReal ↦
          continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: adaptedness is stable under pointwise multiplication of the two canonical
    -- cutoff integrals.
    exact hN₁_mart.adapted.mul hN₂_mart.adapted
  · intro ω
    -- Proof comment: pathwise continuity follows from continuity of each canonical cutoff
    -- integral path and continuity of multiplication on `ℝ`.
    exact (hN₁_mart.continuous ω).mul (hN₂_mart.continuous ω)

/-- Helper for Theorem 25.22: a deterministic stop of the cutoff product is exactly the product
of the two deterministically stopped cutoff integrals. -/
private theorem stoppedProcess_const_mul
    {X Y : NNReal → Ω → ℝ}
    (U t : NNReal) (ω : Ω) :
    stoppedProcess
        (fun s ω ↦ X s ω * Y s ω)
        (fun _ ↦ (U : ENNReal))
        t
        ω =
      stoppedProcess X (fun _ ↦ (U : ENNReal)) t ω *
        stoppedProcess Y (fun _ ↦ (U : ENNReal)) t ω := by
  by_cases htu : (t : ENNReal) ≤ (U : ENNReal)
  · -- Proof comment: before the deterministic stop time, all three stopped processes agree with
    -- their unstopped values at time `t`.
    rw [stoppedProcess_eq_of_le (u := fun s ω ↦ X s ω * Y s ω) (ω := ω) (i := t) htu]
    rw [stoppedProcess_eq_of_le (u := X) (ω := ω) (i := t) htu]
    rw [stoppedProcess_eq_of_le (u := Y) (ω := ω) (i := t) htu]
  · have hUtt : (U : ENNReal) ≤ (t : ENNReal) := le_of_not_ge htu
    -- Proof comment: after the deterministic stop time, all three stopped processes are frozen
    -- at the common cutoff value at time `U`.
    rw [stoppedProcess_eq_of_ge (u := fun s ω ↦ X s ω * Y s ω) (ω := ω) (i := t) hUtt]
    rw [stoppedProcess_eq_of_ge (u := X) (ω := ω) (i := t) hUtt]
    rw [stoppedProcess_eq_of_ge (u := Y) (ω := ω) (i := t) hUtt]

/-- Helper for Theorem 25.22: the canonical dyadic Itô realization always starts at `0`. -/
private theorem continuousLocalMartingaleItoIntegralProcess_zero
    {M H : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M) (ω : Ω) :
    continuousLocalMartingaleItoIntegralProcess hM H 0 ω = 0 := by
  have hdyadicZero :
      Tendsto
        (fun n ↦
            Theorem25_22.partitionPathwiseItoApproximationUpTo
              (fun t ↦ H t ω)
              (⟨fun t ↦ M t ω, hM.continuous ω⟩ : PathSpace)
              Definition2158.dyadicPartitionSequence
              0
              n)
        atTop
        (𝓝 (0 : ℝ)) := by
    -- Proof comment: every dyadic row sum at horizon `0` is empty, so the approximants are
    -- constantly `0`.
    simpa [Theorem25_22.partitionPathwiseItoApproximationUpTo, partitionBoundIndex_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  -- Proof comment: the canonical process is defined by this dyadic limit, so the initial value
  -- is the same zero limit.
  simpa [continuousLocalMartingaleItoIntegralProcess] using hdyadicZero.limUnder_eq

/-- Helper for Theorem 25.22: each deterministic-cutoff canonical Itô coordinate has an `L²`
initial value because the process starts from `0`. -/
private theorem constCutoffCoordinate_initial_memLp_two
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal) :
    MemLp
      ((continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) 0)
      2
      μ := by
  have hzero :
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) 0 = 0 := by
    funext ω
    -- Proof comment: apply the generic zero-start lemma to the cutoff coefficient.
    exact
      continuousLocalMartingaleItoIntegralProcess_zero
        (ℱ := ℱ) (μ := μ)
        (M := M)
        (H := processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        hM
        ω
  -- Proof comment: once the initial slice is literally the zero random variable, `MemLp`
  -- follows from the standard zero-function instance.
  simpa [hzero] using (MemLp.zero : MemLp (0 : Ω → ℝ) 2 μ)

/-- Helper for Theorem 25.22: every canonical deterministic-cutoff Itô coordinate is a
continuous local martingale up to the deterministic horizon `∞`. -/
private theorem constCutoffCoordinate_continuousLocalMartingaleUpToInfinity
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal)
    (hN :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    _root_.ProbabilityTheory.IsContinuousLocalMartingaleUpTo ℱ μ
      (fun _ : Ω ↦ (∞ : ENNReal))
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  refine ⟨?_, hN.continuous⟩
  -- Proof comment: `∞`-up-to local martingales are exactly ordinary local martingales.
  exact
    (_root_.ProbabilityTheory.isLocalMartingaleUpTo_iff ℱ μ (fun _ : Ω ↦ (∞ : ENNReal))
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))).2
      ((_root_.ProbabilityTheory.isLocalMartingale_iff ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))).1 hN.local_martingale)

/-- Helper for Theorem 25.22: deterministic stopping preserves the local-martingale property for
continuous paths. -/
private theorem isLocalMartingale_stoppedProcess_constTime
    {M : NNReal → Ω → ℝ}
    (hM : IsLocalMartingale ℱ μ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    (T : NNReal) :
    IsLocalMartingale ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨hM_adapted, τSeq, hτSeq⟩
  refine
    (isLocalMartingale_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal)))).2
      ⟨?_, τSeq, ?_⟩
  · -- Proof comment: deterministic stopping preserves adaptedness because the source paths are
    -- continuous and the clock `T` is a stopping time.
    exact
      (hM_adapted.stronglyAdapted.stoppedProcess hM_cont (isStoppingTime_const ℱ T)).adapted
  · rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hLim, hStopped⟩
    refine
      (isLocalizingSequence_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) τSeq).2
        ⟨hStopping, hLim, ?_⟩
    intro n
    obtain ⟨hMart, hUI⟩ := hStopped n
    have hDoubleStop :
        stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) := by
      have hLeft :
          stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
              stoppedProcess M
                (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))))
      have hRight :
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
              stoppedProcess M
                (fun ω ↦ min (((fun _ ↦ (T : ENNReal)) ω)) ((τSeq n) ω)))
      exact hLeft.trans hRight.symm
    have hStoppedConst :
        Martingale
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            ℱ
            μ ∧
          UniformIntegrable
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            1
            μ :=
      martingaleUniformIntegrable_stoppedProcessConstTime
        (ℱ := ℱ) (μ := μ) (X := stoppedProcess M (τSeq n)) hMart T
    -- Proof comment: after swapping the two stops, the localized stopped process is just a
    -- deterministic stop of the martingale owner supplied by the localizing sequence.
    exact hDoubleStop ▸ hStoppedConst

/-- Helper for Theorem 25.22: each deterministic stop of a canonical cutoff Itô coordinate is
again a local martingale. -/
private theorem constCutoffCoordinate_stoppedLocalMartingale_of_constTime
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T U : NNReal)
    (hN :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    IsLocalMartingale ℱ μ
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (U : ENNReal))) := by
  -- Proof comment: specialize the generic deterministic-stop local-martingale theorem to the
  -- canonical cutoff coordinate.
  exact
    isLocalMartingale_stoppedProcess_constTime
      (ℱ := ℱ) (μ := μ)
      hN.local_martingale hN.continuous U

/-- Helper for Theorem 25.22: deterministic constant stops already form a localizing sequence
once each stopped process is a uniformly integrable martingale. -/
private theorem isLocalMartingale_of_constStoppedMartingale
    {X : NNReal → Ω → ℝ}
    (hAdapted : Adapted ℱ X)
    (hStopped :
      ∀ n : ℕ, Martingale (stoppedProcess X (fun _ ↦ (n : ENNReal))) ℱ μ ∧
        UniformIntegrable (stoppedProcess X (fun _ ↦ (n : ENNReal))) 1 μ) :
    IsLocalMartingale ℱ μ X := by
  -- Proof comment: use the deterministic localization sequence `τₙ ≡ n`; the only real input is
  -- that each deterministically stopped process is already a uniformly integrable martingale.
  refine (ProbabilityTheory.isLocalMartingale_iff ℱ μ X).2 ?_
  refine ⟨hAdapted, ?_⟩
  let τs : ℕ → Ω → ENNReal := fun n _ ↦ (n : ENNReal)
  refine ⟨τs, (ProbabilityTheory.isLocalizingSequence_iff ℱ μ X τs).2 ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [τs] using (MeasureTheory.isStoppingTime_const ℱ n)
  · refine Filter.Eventually.of_forall ?_
    intro ω
    refine ⟨?_, ?_⟩
    · intro i j hij
      simpa [τs] using (show (i : ENNReal) ≤ (j : ENNReal) from by exact_mod_cast hij)
    · simpa [τs] using
        (ENNReal.tendsto_nat_nhds_top : Tendsto (fun n : ℕ ↦ (n : ENNReal)) atTop (𝓝 ∞))
  · intro n
    simpa [τs] using hStopped n

/-- Helper for Theorem 25.22: timewise almost-everywhere equality preserves the martingale
property once the target process is already strongly adapted. -/
private theorem martingale_congr_ae_local
    {M N : NNReal → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hN_stronglyAdapted : StronglyAdapted ℱ N)
    (hMN : ∀ t : NNReal, M t =ᵐ[μ] N t) :
    Martingale N ℱ μ := by
  refine ⟨hN_stronglyAdapted, ?_⟩
  intro s t hst
  -- Proof comment: conditional expectation respects timewise almost-sure equality, so the
  -- martingale identity transfers directly from `M` to `N`.
  exact
    (MeasureTheory.condExp_congr_ae (hMN t)).symm.trans
      ((hM.condExp_ae_eq hst).trans (hMN s))

/-- Helper for Theorem 25.22: one all-times almost-sure identity transports deterministic-time
stopped slices under a fixed clock. -/
private theorem stoppedProcess_congr_process_ae_allTimes
    {M N : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hMN : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω)
    (t : NNReal) :
    stoppedProcess M τ t =ᵐ[μ] stoppedProcess N τ t := by
  -- Proof comment: both stopped slices evaluate the source process at the same clipped time
  -- `t ∧ τ(ω)`, so the all-times equality transfers immediately.
  filter_upwards [hMN] with ω hω
  simpa [stoppedProcess] using hω ((min (t : ENNReal) (τ ω)).untopA)

/-- Helper for Theorem 25.22: an all-times almost-sure identity transports the local-martingale
property to a continuous adapted modification. -/
private theorem isLocalMartingale_congr_ae_allTimes
    {M N : NNReal → Ω → ℝ}
    (hM : IsLocalMartingale ℱ μ M)
    (hN_adapted : Adapted ℱ N)
    (hN_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω)
    (hMN : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω) :
    IsLocalMartingale ℱ μ N := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨_, τSeq, hτSeq⟩
  refine (isLocalMartingale_iff ℱ μ N).2 ⟨hN_adapted, τSeq, ?_⟩
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hLim, hStopped⟩
  refine (isLocalizingSequence_iff ℱ μ N τSeq).2 ⟨hStopping, hLim, ?_⟩
  intro n
  obtain ⟨hMart, hUI⟩ := hStopped n
  have hStoppedEq :
      ∀ t : NNReal,
        stoppedProcess M (τSeq n) t =ᵐ[μ] stoppedProcess N (τSeq n) t := by
    intro t
    -- Proof comment: the common localizing stop preserves the all-times almost-sure identity.
    exact stoppedProcess_congr_process_ae_allTimes (μ := μ) hMN t
  have hStoppedStrong :
      StronglyAdapted ℱ (stoppedProcess N (τSeq n)) := by
    -- Proof comment: continuity upgrades adaptedness to strong adaptedness after stopping.
    exact hN_adapted.stronglyAdapted.stoppedProcess hN_cont (hStopping n)
  refine ⟨martingale_congr_ae_local hMart hStoppedStrong hStoppedEq, ?_⟩
  -- Proof comment: uniform integrability is stable under timewise almost-sure equality.
  exact (uniformIntegrable_congr_ae hStoppedEq).1 hUI

/-- Helper for Theorem 25.22: the correct independence frontier is the canonical cutoff
compensator itself, not a stopped-product martingale reconstruction. -/
private theorem constCutoffCanonicalZeroEqUpTo_of_zeroWitness
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      0 := by
  -- Proof comment: once the genuine owner-side zero quadratic-covariation witness is available,
  -- the canonical cutoff compensator is `EqUpTo` to `0` by the generic identification theorem.
  exact
    eqUpTo_zero_of_isContinuousQuadraticCovariationProcess_zero
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZero

/-- Helper for Theorem 25.22: the remaining independence blocker is one fixed measurable null set
on which the canonical cutoff mixed compensator vanishes pointwise on `[0,T]`. -/
private theorem constCutoffCanonicalZeroGoodEvent_of_zeroWitness
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            t
            ω = 0 := by
  -- Proof comment: first convert the genuine zero quadratic-covariation witness into the
  -- corresponding `EqUpTo` statement for the canonical cutoff compensator.
  have hEqZero :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0 := by
    exact
      eqUpTo_zero_of_isContinuousQuadraticCovariationProcess_zero
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
        T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZero
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEqZero with
    ⟨S, hSmeas, hSnull, hSzero⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro ω hω t ht
  -- Proof comment: outside that fixed null set, the `EqUpTo` witness is already pointwise zero.
  simpa using hSzero ht hω

/-- Helper for Theorem 25.22: source-path independence should force the canonical cutoff mixed
quadratic-covariation integral to agree with `0` on `[0,T]` once the same weighted source dyadic
rows are already known to converge pathwise to `0`. -/
private theorem constCutoffOwnerCompensator_eqUpTo_zero_of_zeroDyadic
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ N₁
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ N₂
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A)
    (hZeroDyadic :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                  (fun s ↦
                    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  t
                  n)
              atTop
              (𝓝 (0 : ℝ))) :
    EqUpTo μ T A 0 := by
  rcases
      constCutoffDyadicQuadraticCovariationTendsto
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
        (H₁ := H₁) (H₂ := H₂) (A := A)
        (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T hEq₁ hEq₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA with
    ⟨S₁, hS₁meas, hS₁null, hS₁good⟩
  rcases hZeroDyadic with ⟨S₂, hS₂meas, hS₂null, hS₂good⟩
  refine ⟨S₁ ∪ S₂, hS₁meas.union hS₂meas, ?_, ?_⟩
  · have hUnionLe : μ (S₁ ∪ S₂) ≤ μ S₁ + μ S₂ := measure_union_le S₁ S₂
    refine le_antisymm ?_ bot_le
    simpa [hS₁null, hS₂null] using hUnionLe
  · intro t ht ω hω
    by_contra hωS
    have hω₁ : ω ∉ S₁ := by
      exact fun hS₁ω ↦ hωS (Set.mem_union_left S₂ hS₁ω)
    have hω₂ : ω ∉ S₂ := by
      exact fun hS₂ω ↦ hωS (Set.mem_union_right S₁ hS₂ω)
    have hLimitA : Tendsto
        (fun n ↦
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (fun s ↦
              processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (A t ω)) :=
      hS₁good hω₁ ht
    have hLimitZero : Tendsto
        (fun n ↦
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (fun s ↦
              processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
            (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (0 : ℝ)) :=
      hS₂good hω₂ ht
    have hAt : A t ω = 0 := tendsto_nhds_unique hLimitA hLimitZero
    exact hω hAt

/-- Helper for Theorem 25.22: a genuine zero quadratic-covariation witness for the canonical
cutoff pair already forces the weighted cutoff source dyadic rows to converge pathwise to `0`. -/
private theorem constCutoffZeroDyadicTendsto_of_zeroWitness
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  -- Proof comment: once the canonical cutoff pair already has the genuine zero compensator, the
  -- existing source-facing dyadic bridge specializes immediately to the zero limit.
  simpa [N₁c, N₂c] using
    (constCutoffDyadicQuadraticCovariationTendsto
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁c) (N₂ := N₂c)
      (H₁ := H₁) (H₂ := H₂) (A := 0)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T
      (eqUpTo_rfl (μ := μ) T N₁c)
      (eqUpTo_rfl (μ := μ) T N₂c)
      hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZero)

/-- Helper for Theorem 25.22: once the canonical deterministic-cutoff pair already has almost
sure pathwise zero quadratic covariation, the weighted cutoff source dyadic rows converge to `0`
off one fixed null set. -/
private theorem constCutoffZeroDyadicTendsto_of_aeZeroCanonicalPath
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZeroAE :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun s ↦
              continuousLocalMartingaleItoIntegralProcess hM₁
                (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω,
            hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦
              continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω,
            hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
          0) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  have hZeroAE' :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun s ↦ N₁c s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ N₂c s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
          0 := by
    -- Proof comment: first rewrite the almost-sure zero pathwise statement in terms of short
    -- aliases for the two canonical deterministic-cutoff coordinates.
    simpa [N₁c, N₂c] using hZeroAE
  rcases ae_exists_nullSet_forall (μ := μ) hZeroAE' with
    ⟨SZero, hSZeroMeas, hSZeroNull, hSZeroGood⟩
  rcases
      constCutoffGoodPath_plusMinusSquareVariation
        (μ := μ) (ℱ := ℱ) (M₁ := M₁) (M₂ := M₂) hM₁ hM₂ with
    ⟨SPath, hSPathMeas, hSPathNull, hSPathGood⟩
  rcases
      existsNullSet_forall_ownerDyadicSquareVariationTendsto
        (μ := μ) (ℱ := ℱ)
        (N := N₁c)
        (A := bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        T hN₁_mart hN₁_sq with
    ⟨SSq₁, hSSq₁Meas, hSSq₁Null, hSSq₁Good⟩
  rcases
      existsNullSet_forall_ownerDyadicSquareVariationTendsto
        (μ := μ) (ℱ := ℱ)
        (N := N₂c)
        (A := bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        T hN₂_mart hN₂_sq with
    ⟨SSq₂, hSSq₂Meas, hSSq₂Null, hSSq₂Good⟩
  let S : Set Ω := (((SZero ∪ SPath) ∪ SSq₁) ∪ SSq₂)
  have hSnull : μ S = 0 := by
    have hLeftNull : μ (SZero ∪ SPath) = 0 := by
      have hUnionLe : μ (SZero ∪ SPath) ≤ μ SZero + μ SPath := measure_union_le SZero SPath
      refine le_antisymm ?_ bot_le
      simpa [hSZeroNull, hSPathNull] using hUnionLe
    have hMidNull : μ ((SZero ∪ SPath) ∪ SSq₁) = 0 := by
      have hUnionLe :
          μ ((SZero ∪ SPath) ∪ SSq₁) ≤ μ (SZero ∪ SPath) + μ SSq₁ :=
        measure_union_le (SZero ∪ SPath) SSq₁
      refine le_antisymm ?_ bot_le
      simpa [hLeftNull, hSSq₁Null] using hUnionLe
    have hUnionLe :
        μ (((SZero ∪ SPath) ∪ SSq₁) ∪ SSq₂) ≤ μ ((SZero ∪ SPath) ∪ SSq₁) + μ SSq₂ :=
      measure_union_le (((SZero ∪ SPath) ∪ SSq₁)) SSq₂
    refine le_antisymm ?_ bot_le
    simpa [S, hMidNull, hSSq₂Null] using hUnionLe
  refine ⟨S, ((hSZeroMeas.union hSPathMeas).union hSSq₁Meas).union hSSq₂Meas, hSnull, ?_⟩
  intro ω hω t ht
  have hω_not : ω ∉ SZero ∧ ω ∉ SPath ∧ ω ∉ SSq₁ ∧ ω ∉ SSq₂ := by
    simpa [S, Set.mem_union, not_or, and_assoc] using hω
  rcases hSPathGood hω_not.2.1 with ⟨brAdd, brSub, hBrAdd, hBrSub⟩
  have hOwnerLimit :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            (⟨fun s ↦ N₁c s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ N₂c s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hPath :
        HasQuadraticCovariationAlong
          (⟨fun s ↦ N₁c s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ N₂c s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
          0 :=
      hSZeroGood hω_not.1
    -- Proof comment: off the fixed zero-covariation null set, the canonical cutoff pair already
    -- has mixed dyadic partition sums converging to `0`.
    simpa [dyadic_quadratic_covariation_sum] using
      HasQuadraticCovariationAlong.tendsto_partition_sum hPath t
  have hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁c s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω := by
    intro s _hs
    rfl
  have hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂c s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω := by
    intro s _hs
    rfl
  -- Proof comment: the zero pathwise owner limit, the two single-coordinate square-row limits,
  -- and the source-path good event are exactly the hypotheses of the source-dyadic bridge.
  exact
    constCutoffWeightedSourceDyadicTendstoCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁c) (N₂ := N₂c)
      (H₁ := H₁) (H₂ := H₂) (A := 0)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
      T ht ⟨brAdd, brSub, hBrAdd, hBrSub⟩ hEq₁ω hEq₂ω
      (hSSq₁Good hω_not.2.2.1) (hSSq₂Good hω_not.2.2.2) hOwnerLimit

/-- Helper for Theorem 25.22: source-path independence should force the weighted cutoff source
dyadic rows to converge pathwise to `0` on one fixed null-set complement. -/
private theorem constCutoffZeroDyadicTendsto_of_frozenApproximationData
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hApproxData :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            ∃ v : ℕ → ℕ → ℝ, ∃ L : ℕ → ℝ,
              (∀ m : ℕ, Tendsto (v m) atTop (𝓝 (L m))) ∧
                Tendsto L atTop (𝓝 (0 : ℝ)) ∧
                ∀ ε > 0, ∀ N : ℕ, ∃ m ≥ N,
                  ∀ᶠ n in atTop,
                    |Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                        (fun s ↦
                          processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                            processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                        (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                        (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                        t
                        n -
                      v m n| < ε) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  rcases hApproxData with ⟨S, hSmeas, hSnull, hSgood⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro ω hω t ht
  rcases hSgood hω ht with ⟨v, L, hFrozen, hLimit, hApprox⟩
  -- Proof comment: once the actual cutoff mixed row is approximated by arbitrarily far frozen
  -- rows whose own limits converge to `0`, the generic frozen-approximation theorem closes the
  -- pointwise limit.
  exact
    tendsto_atTop_of_frozenApproximationOfLimitFamily
      (u := fun n ↦
        Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
          (fun s ↦
            processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
              processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
          (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
          t
          n)
      (v := v) (L := L) (A := 0)
      hFrozen hLimit hApprox

/-- Helper for Theorem 25.22: source-path independence should provide the frozen approximation
data needed to make the cutoff weighted source dyadic row converge to `0`. -/
private theorem constCutoffFrozenRows_of_goodPath
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          ∃ L : ℕ → ℝ,
            ∀ m : ℕ,
              Tendsto
                (fun n ↦
                  Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                    (dyadicCoarseIccStep
                      (fun s ↦
                        processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                          processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                      m
                      t)
                    (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                    (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                    t
                    n)
                atTop
                (𝓝 (L m)) := by
  rcases
      constCutoffGoodPath_plusMinusSquareVariation
        (μ := μ) (ℱ := ℱ) (M₁ := M₁) (M₂ := M₂) hM₁ hM₂ with
    ⟨S, hSmeas, hSnull, hSgood⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro ω hω t ht
  rcases hSgood hω with ⟨brAdd, brSub, hBrAdd, hBrSub⟩
  let w : NNReal → ℝ := fun s ↦
    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω
  let L : ℕ → ℝ := fun m ↦
    (1 / 4 : ℝ) *
      (coarseIccStepSquareVariationLimit w m t brAdd -
        coarseIccStepSquareVariationLimit w m t brSub)
  refine ⟨L, ?_⟩
  intro m
  -- Proof comment: off the fixed square-variation good event, the Chapter 21 coarse-step limit
  -- theorem already computes the limit of each frozen mixed row.
  simpa [w, L] using
    (tendsto_constCutoffWeightedMixedRow_of_fixedCoarseStep
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (hM₁ := hM₁) (hM₂ := hM₂)
      (ω := ω) (t := t)
      w m hBrAdd hBrSub)

/-- Helper for Theorem 25.22: once the source path pair already has almost-sure zero quadratic
covariation, every frozen coarse-step cutoff row has limit `0`, so the frozen limit family is the
constant-zero sequence. -/
private theorem constCutoffFrozenLimit_zero_of_aeZeroPath
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hZeroAE :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
          0) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          ∃ L : ℕ → ℝ,
            (∀ m : ℕ,
              Tendsto
                (fun n ↦
                  Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                    (dyadicCoarseIccStep
                      (fun s ↦
                        processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                          processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                      m
                      t)
                    (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                    (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                    t
                    n)
                atTop
                (𝓝 (L m))) ∧
              Tendsto L atTop (𝓝 (0 : ℝ)) := by
  rcases ae_exists_nullSet_forall (μ := μ) hZeroAE with
    ⟨S₀, hS₀meas, hS₀null, hS₀good⟩
  rcases
      constCutoffGoodPath_plusMinusSquareVariation
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁)
        (M₂ := M₂)
        hM₁
        hM₂ with
    ⟨S₁, hS₁meas, hS₁null, hS₁good⟩
  have hSnull : μ (S₀ ∪ S₁) = 0 := by
    have hUnionLe : μ (S₀ ∪ S₁) ≤ μ S₀ + μ S₁ := measure_union_le S₀ S₁
    refine le_antisymm ?_ bot_le
    simpa [hS₀null, hS₁null] using hUnionLe
  refine ⟨S₀ ∪ S₁, hS₀meas.union hS₁meas, hSnull, ?_⟩
  intro ω hω t ht
  have hω₀ : ω ∉ S₀ := by
    exact fun hS₀ω ↦ hω (Set.mem_union_left S₁ hS₀ω)
  have hω₁ : ω ∉ S₁ := by
    exact fun hS₁ω ↦ hω (Set.mem_union_right S₀ hS₁ω)
  have hZeroω :
      HasQuadraticCovariationAlong
        (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
        0 :=
    hS₀good hω₀
  rcases hS₁good hω₁ with ⟨brAdd, brSub, hBrAdd, hBrSub⟩
  refine ⟨fun _ ↦ (0 : ℝ), ?_, tendsto_const_nhds⟩
  intro m
  let w : NNReal → ℝ := fun s ↦
    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω
  have hRow :
      Tendsto
        (fun n ↦
          Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
            (dyadicCoarseIccStep w m t)
            (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
            (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
            t
            n)
        atTop
        (𝓝
          ((1 / 4 : ℝ) *
            (coarseIccStepSquareVariationLimit w m t brAdd -
              coarseIccStepSquareVariationLimit w m t brSub))) :=
    tendsto_constCutoffWeightedMixedRow_of_fixedCoarseStep
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁)
      (M₂ := M₂)
      (hM₁ := hM₁)
      (hM₂ := hM₂)
      (ω := ω)
      (t := t)
      w
      m
      hBrAdd
      hBrSub
  have hLimitZero :
      (1 / 4 : ℝ) *
          (coarseIccStepSquareVariationLimit w m t brAdd -
            coarseIccStepSquareVariationLimit w m t brSub) =
        0 :=
    coarseIccStepMixedLimit_eq_zero_of_zeroCovariation hBrAdd hBrSub hZeroω w m t
  -- Proof comment: the fixed coarse-step row already has the polarized limit, and the zero
  -- pathwise covariation forces that limit to vanish.
  simpa [w, hLimitZero] using hRow

/-- Helper for Theorem 25.22: once a fixed null-set complement carries frozen coarse-step rows
with limits tending to `0` and eventual approximation of the actual cutoff mixed row by those
frozen rows, the existing frozen-approximation theorem closes the zero-dyadic limit. -/
private theorem constCutoffZeroDyadicTendsto_of_frozenLimitApproximation
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hFrozenApprox :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            ∃ L : ℕ → ℝ,
              (∀ m : ℕ,
                Tendsto
                  (fun n ↦
                    Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                      (dyadicCoarseIccStep
                        (fun s ↦
                          processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                            processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                        m
                        t)
                      (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                      (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                      t
                      n)
                  atTop
                  (𝓝 (L m))) ∧
                Tendsto L atTop (𝓝 (0 : ℝ)) ∧
                ∀ ε > 0, ∀ N : ℕ, ∃ m ≥ N,
                  ∀ᶠ n in atTop,
                    |Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                        (fun s ↦
                          processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                            processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                        (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                        (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                        t
                        n -
                      Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                        (dyadicCoarseIccStep
                          (fun s ↦
                            processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                              processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                          m
                          t)
                        (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                        (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                        t
                        n| < ε) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  rcases hFrozenApprox with ⟨S, hSmeas, hSnull, hSgood⟩
  refine
    constCutoffZeroDyadicTendsto_of_frozenApproximationData
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂)
      T ?_
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro ω hω t ht
  rcases hSgood hω ht with ⟨L, hFrozen, hLimit, hApprox⟩
  refine ⟨?_, L, ?_, hLimit, ?_⟩
  · intro m n
    exact
      Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
        (dyadicCoarseIccStep
          (fun s ↦
            processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
              processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
          m
          t)
        (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
        t
        n
  · intro m
    -- Proof comment: the provided frozen-row hypotheses already match the `v m` branches needed
    -- by the abstract frozen-approximation interface.
    simpa using hFrozen m
  · simpa using hApprox

/-- Helper for Theorem 25.22: source-path independence should imply almost-sure vanishing
pathwise quadratic covariation for the canonical deterministic-cutoff pair. -/
private theorem constCutoffAeZeroCanonicalPath_of_zeroWitness
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    ∀ᵐ ω ∂μ,
      HasQuadraticCovariationAlong
        (⟨fun s ↦
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω,
          hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω,
          hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
        0 := by
  -- Proof comment: a genuine zero quadratic-covariation process already supplies the desired
  -- almost-sure pathwise quadratic-covariation witness by the generic local theorem.
  simpa using
    (aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
      (μ := μ) (ℱ := ℱ) hN₁_mart hN₂_mart hZero)

/-- Helper for Theorem 25.22: source-path independence should imply almost-sure vanishing of the
canonical same-row mixed partition sums for the deterministic-cutoff pair on `[0,T]`. -/
private theorem constCutoffAeZeroCanonicalPartition_of_eqUpToZero
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A)
    (hEqZero : EqUpTo μ T A 0) :
    ∀ᵐ ω ∂μ,
      ∀ ⦃t : NNReal⦄, t ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝 (0 : ℝ)) := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  rcases
      constCutoffOwnerGoodEvent_of_upToWitness
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁c) (N₂ := N₂c)
        (H₁ := H₁) (H₂ := H₂) (A := 0) (A' := A)
        T hA
        (eqUpTo_rfl (μ := μ) T N₁c)
        (eqUpTo_rfl (μ := μ) T N₂c)
        (eqUpTo_sym hEqZero)
        hN₁_mart hN₂_mart with
    ⟨S, hSmeas, hSnull, hSgood⟩
  -- Proof comment: once the compensator itself is identified with `0` on `[0,T]`, the owner-side
  -- good event already gives the canonical cutoff partition-row limit at every deterministic
  -- horizon.
  refine ae_iff.2 ?_
  refine measure_mono_null ?_ hSnull
  intro ω hω
  by_contra hωS
  apply hω
  rcases hSgood hωS with ⟨_, _, hLimit⟩
  intro t ht
  simpa [N₁c, N₂c, partitionQuadraticCovariationSum] using hLimit ht

/-- Helper for Theorem 25.22: a zero quadratic-covariation witness up to `U` upgrades to a
genuine zero witness after deterministically stopping both coordinates at `U`. -/
private theorem stoppedQuadraticCovariation_zero_of_upTo
    {M N : NNReal → Ω → ℝ}
    {U : NNReal}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hUpTo : IsContinuousQuadraticCovariationProcessUpTo ℱ μ U M N 0) :
    IsContinuousQuadraticCovariationProcess ℱ μ
      (stoppedProcess M (fun _ ↦ (U : ENNReal)))
      (stoppedProcess N (fun _ ↦ (U : ENNReal)))
      0 := by
  let σ : Ω → ENNReal := fun _ ↦ (U : ENNReal)
  have hσ : IsStoppingTime ℱ σ := by
    simpa [σ] using isStoppingTime_const ℱ U
  rcases hUpTo with ⟨Mw, Nw, Aw, hMwNwAw, hEqMw, hEqNw, hEqAw⟩
  have hStoppedDriver :
      IsLocalMartingale ℱ μ
        (stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ) := by
    -- Proof comment: deterministically stopping the genuine compensated-product witness preserves
    -- its local-martingale property.
    exact
      isLocalMartingale_stoppedProcess
        hMwNwAw.local_martingale_mul_sub.local_martingale
        hMwNwAw.local_martingale_mul_sub.continuous
        hσ
  have hStoppedMAdapted : Adapted ℱ (stoppedProcess M σ) :=
    (hM.adapted.stronglyAdapted.stoppedProcess hM.continuous hσ).adapted
  have hStoppedNAdapted : Adapted ℱ (stoppedProcess N σ) :=
    (hN.adapted.stronglyAdapted.stoppedProcess hN.continuous hσ).adapted
  have hStoppedTargetAdapted :
      Adapted ℱ
        (fun t ω ↦
          stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ)) := by
    exact
      (hStoppedMAdapted.mul hStoppedNAdapted).sub
        (adapted_const' ℱ (fun _ : NNReal ↦ (0 : ℝ)))
  have hStoppedTargetCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦
        stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ) := by
    intro ω
    -- Proof comment: deterministic stopping preserves continuity of both coordinates, so their
    -- stopped product remains continuous.
    exact
      ((continuous_stoppedProcess_of_continuous hM.continuous ω).mul
        (continuous_stoppedProcess_of_continuous hN.continuous ω)).sub
        (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
  rcases eqUpTo_forall_eq (μ := μ) (T := U) hEqMw with
    ⟨SMw, hSMwMeas, hSMwNull, hSMwEq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := U) hEqNw with
    ⟨SNw, hSNwMeas, hSNwNull, hSNwEq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := U) hEqAw with
    ⟨SAw, hSAwMeas, hSAwNull, hSAwEq⟩
  have hStoppedEq :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ t ω =
          (stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ)) := by
    let S : Set Ω := (SMw ∪ SNw) ∪ SAw
    have hSnull : μ S = 0 := by
      have hLeftNull : μ (SMw ∪ SNw) = 0 := by
        have hUnionLe : μ (SMw ∪ SNw) ≤ μ SMw + μ SNw := measure_union_le SMw SNw
        refine le_antisymm ?_ bot_le
        simpa [hSMwNull, hSNwNull] using hUnionLe
      have hUnionLe : μ ((SMw ∪ SNw) ∪ SAw) ≤ μ (SMw ∪ SNw) + μ SAw :=
        measure_union_le (SMw ∪ SNw) SAw
      refine le_antisymm ?_ bot_le
      simpa [S, hLeftNull, hSAwNull] using hUnionLe
    refine ae_iff.2 ?_
    refine measure_mono_null ?_ hSnull
    intro ω hω
    by_contra hωS
    have hωMw : ω ∉ SMw := by
      exact fun hSMwω ↦ hωS (Set.mem_union_left SAw (Set.mem_union_left SNw hSMwω))
    have hωNw : ω ∉ SNw := by
      exact fun hSNwω ↦ hωS (Set.mem_union_left SAw (Set.mem_union_right SMw hSNwω))
    have hωAw : ω ∉ SAw := by
      exact fun hSAwω ↦ hωS (Set.mem_union_right (SMw ∪ SNw) hSAwω)
    apply hω
    intro t
    have hMwStopped :
        stoppedProcess Mw σ t ω = stoppedProcess M σ t ω := by
      have hEq : Mw (min t U) ω = M (min t U) ω :=
        (hSMwEq (min_le_right _ _) hωMw).symm
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    have hNwStopped :
        stoppedProcess Nw σ t ω = stoppedProcess N σ t ω := by
      have hEq : Nw (min t U) ω = N (min t U) ω :=
        (hSNwEq (min_le_right _ _) hωNw).symm
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    have hAwStopped :
        stoppedProcess Aw σ t ω = 0 := by
      have hEq : Aw (min t U) ω = 0 := (hSAwEq (min_le_right _ _) hωAw).symm
      simpa [σ, stoppedProcessConstTime_eq_min] using hEq
    calc
      stoppedProcess (fun t ω ↦ Mw t ω * Nw t ω - Aw t ω) σ t ω =
          stoppedProcess Mw σ t ω * stoppedProcess Nw σ t ω - stoppedProcess Aw σ t ω := by
        simp [σ, stoppedProcess]
      _ = stoppedProcess M σ t ω * stoppedProcess N σ t ω - (0 : ℝ) := by
        rw [hMwStopped, hNwStopped, hAwStopped]
  refine
    { zero := by
        funext ω
        simp [σ, stoppedProcess]
      adapted := by
        intro t
        exact (measurable_const : Measurable[ℱ t] fun _ : Ω ↦ (0 : ℝ))
      continuous := by
        intro ω
        exact (continuous_const : Continuous fun _ : NNReal ↦ (0 : ℝ))
      locally_finite_variation := zeroProcess_locallyFiniteVariation (μ := μ)
      local_martingale_mul_sub := by
        -- Proof comment: after stopping, the compensated-product driver agrees almost surely at
        -- all times with the target stopped product because the compensator coordinate is
        -- `EqUpTo` to `0`.
        exact
          isLocalMartingale_congr_ae_allTimes
            hStoppedDriver
            hStoppedTargetAdapted
            hStoppedTargetCont
            hStoppedEq }

/-- Helper for Theorem 25.22: a zero quadratic-covariation witness up to `U` makes the
deterministically stopped cutoff product a martingale at horizon `U`. -/
private theorem constCutoffStoppedProduct_martingale_of_zeroUpTo
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T U : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hQuadUpTo :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ U
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    Martingale
      (stoppedProcess
        (fun t ω ↦
          continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω)
        (fun _ ↦ (U : ENNReal))) ℱ μ := by
  let σ : Ω → ENNReal := fun _ ↦ (U : ENNReal)
  have hStoppedQuad :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) σ)
        (stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) σ)
        0 := by
    -- Proof comment: the supplied `...UpTo` witness becomes a genuine zero witness after
    -- stopping both cutoff coordinates at the same deterministic horizon.
    exact
      stoppedQuadraticCovariation_zero_of_upTo
        (ℱ := ℱ)
        (μ := μ)
        (M := continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (N := continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        hN₁_mart
        hN₂_mart
        hQuadUpTo
  have hStoppedProd :
      IsContinuousLocalMartingale ℱ μ
        (stoppedProcess
          (fun t ω ↦
            continuousLocalMartingaleItoIntegralProcess hM₁
                (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
              continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω)
          σ) := by
    -- Proof comment: with zero compensator, the stopped cutoff product itself is the compensated
    -- product local martingale coming from the stopped zero witness.
    refine ⟨?_, ?_⟩
    · simpa [σ, stoppedProcess_const_mul] using hStoppedQuad.local_martingale_mul_sub
    · intro ω
      exact
        continuous_stoppedProcess_of_continuous
          (fun ω ↦ (hN₁_mart.continuous ω).mul (hN₂_mart.continuous ω))
          ω
  -- Proof comment: a deterministic stop of this continuous local martingale is a true martingale,
  -- and stopping twice at the same deterministic horizon does not change the process.
  simpa [σ, stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
    _root_.ProbabilityTheory.IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
      (ℱ := ℱ)
      (μ := μ)
      (τ := fun _ ↦ (∞ : ENNReal))
      (M := stoppedProcess
        (fun t ω ↦
          continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω)
        σ)
      (continuousLocalMartingaleUpToInfinity
        (ℱ := ℱ)
        (μ := μ)
        hStoppedProd)
      U

/-- Helper for Theorem 25.22: once every deterministic horizon carries a zero
quadratic-covariation witness up to that horizon, the cutoff product is a continuous local
martingale. -/
private theorem constCutoffProduct_continuousLocalMartingale_of_zeroUpTo
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hQuadUpTo :
      ∀ U : NNReal,
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ U
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          0) :
    IsContinuousLocalMartingale ℱ μ
      (fun t ω ↦
        continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω) := by
  obtain ⟨hProdAdapted, hProdCont⟩ :=
    constCutoffProduct_adapted_continuous
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂)
      T hN₁_mart hN₂_mart
  -- Proof comment: deterministic-stop martingale reconstruction now globalizes the cutoff
  -- product once the zero `...UpTo` witness is available at every horizon.
  exact
    isContinuousLocalMartingale_of_constStoppedMartingaleLocal
      (μ := μ)
      (ℱ := ℱ)
      hProdAdapted
      hProdCont
      (fun U ↦
        constCutoffStoppedProduct_martingale_of_zeroUpTo
          (μ := μ)
          (ℱ := ℱ)
          (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
          (hM₁ := hM₁) (hM₂ := hM₂)
          T U hN₁_mart hN₂_mart (hQuadUpTo U))

/-- Helper for Theorem 25.22: if a common deterministic stop of the product is already a local
martingale, then the original pair has zero quadratic covariation up to that horizon. -/
private theorem zeroQuadraticCovariationUpTo_of_constStoppedProductLocalMartingale
    {M N : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    {U : NNReal}
    (hStoppedMul :
      IsLocalMartingale ℱ μ
        (stoppedProcess
          (fun t ω ↦ M t ω * N t ω)
          (fun _ ↦ (U : ENNReal)))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ U M N 0 := by
  let σ : Ω → ENNReal := fun _ ↦ (U : ENNReal)
  have hσ : IsStoppingTime ℱ σ := by
    simpa [σ] using isStoppingTime_const ℱ U
  have hStoppedM :
      IsContinuousLocalMartingale ℱ μ (stoppedProcess M σ) := by
    -- Proof comment: deterministic stopping preserves continuous local martingales.
    exact
      { local_martingale :=
          isLocalMartingale_stoppedProcess_constTime
            (ℱ := ℱ)
            (μ := μ)
            hM.local_martingale
            hM.continuous
            U
        continuous := by
          intro ω
          exact continuous_stoppedProcess_of_continuous hM.continuous ω }
  have hStoppedN :
      IsContinuousLocalMartingale ℱ μ (stoppedProcess N σ) := by
    -- Proof comment: apply the same deterministic-stopping argument to the second coordinate.
    exact
      { local_martingale :=
          isLocalMartingale_stoppedProcess_constTime
            (ℱ := ℱ)
            (μ := μ)
            hN.local_martingale
            hN.continuous
            U
        continuous := by
          intro ω
          exact continuous_stoppedProcess_of_continuous hN.continuous ω }
  have hStoppedProd :
      IsLocalMartingale ℱ μ
        (fun t ω ↦ stoppedProcess M σ t ω * stoppedProcess N σ t ω) := by
    -- Proof comment: under a common deterministic stop, the stopped product is the product of the
    -- stopped coordinates.
    simpa [σ, stoppedProcess_const_mul] using hStoppedMul
  have hStoppedZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (stoppedProcess M σ)
        (stoppedProcess N σ)
        0 := by
    -- Proof comment: once the stopped product is a local martingale, the zero process is a
    -- genuine quadratic-covariation compensator for the stopped pair.
    exact
      isContinuousQuadraticCovariationProcess_zero_of_localMartingaleMul
        (ℱ := ℱ)
        (μ := μ)
        (N₁ := stoppedProcess M σ)
        (N₂ := stoppedProcess N σ)
        hStoppedProd
  have hEqM : EqUpTo μ U M (stoppedProcess M σ) := by
    -- Proof comment: before the deterministic horizon, stopping does not change the first
    -- coordinate.
    refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
    intro t ht ω hω
    have hStoppedEq :
        stoppedProcess M σ t ω = M t ω := by
      simpa [σ, min_eq_left ht] using
        congrFun (stoppedProcessConstTime_eq_min (X := M) U t) ω
    exact (hω hStoppedEq.symm).elim
  have hEqN : EqUpTo μ U N (stoppedProcess N σ) := by
    -- Proof comment: the same deterministic-stop identity holds for the second coordinate.
    refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
    intro t ht ω hω
    have hStoppedEq :
        stoppedProcess N σ t ω = N t ω := by
      simpa [σ, min_eq_left ht] using
        congrFun (stoppedProcessConstTime_eq_min (X := N) U t) ω
    exact (hω hStoppedEq.symm).elim
  -- Proof comment: package the stopped zero witness and transport it back to the original pair on
  -- the finite horizon `[0,U]`.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (μ := μ)
      (ℱ := ℱ)
      hEqM
      hEqN
      (eqUpTo_rfl (μ := μ) U 0)
      (isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
        (μ := μ)
        (ℱ := ℱ)
        (T := U)
        hStoppedZero)

/-- Helper for Theorem 25.22: source-path independence should imply almost-sure vanishing of the
canonical same-row mixed partition sums for the deterministic-cutoff pair. -/
private theorem constCutoffAeZeroCanonicalPartition_of_zeroWitness
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    ∀ᵐ ω ∂μ,
      ∀ ⦃t : NNReal⦄, t ≤ T →
        Tendsto
          (fun n ↦
            Finset.sum
              (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
              (fun k ↦
                (continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₁
                    (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω) *
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω)))
          atTop
          (𝓝 (0 : ℝ)) := by
  filter_upwards
    [constCutoffAeZeroCanonicalPath_of_zeroWitness
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      T hN₁_mart hN₂_mart hZero] with ω hω t ht
  -- Proof comment: once the canonical cutoff pair has pathwise quadratic covariation `0`, the
  -- defining dyadic partition sums converge to `0` at every deterministic horizon.
  simpa [partitionQuadraticCovariationSum] using
    (HasQuadraticCovariationAlong.tendsto_partition_sum hω t)

/-- Helper for Theorem 25.22: a genuine zero quadratic-covariation witness for the canonical
deterministic-cutoff pair already yields one fixed null-set complement on which the canonical
same-row mixed partition sums converge to `0` on `[0, T]`. -/
private theorem constCutoffCanonicalPartitionGoodEvent_of_zeroWitness
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZero :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Finset.sum
                (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
                (fun k ↦
                  (continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
            atTop
            (𝓝 (0 : ℝ)) := by
  rcases
      ae_exists_nullSet_forall
        (μ := μ)
        (constCutoffAeZeroCanonicalPartition_of_zeroWitness
          (μ := μ) (ℱ := ℱ)
          (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
          T hN₁_mart hN₂_mart hZero) with
    ⟨S, hSmeas, hSnull, hSgood⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro ω hω t ht
  -- Proof comment: `ae_exists_nullSet_forall` fixes a single measurable null set that works for
  -- every deterministic horizon `t ≤ T` at once.
  exact hSgood hω ht

/-- Helper for Theorem 25.22: once one deterministic-cutoff owner pair already has a fixed
null-set complement on which its own mixed dyadic partition sums converge to `0`, the weighted
source dyadic row also converges to `0` on one fixed null-set complement. -/
private theorem constCutoffZeroDyadicTendsto_of_ownerPartitionGoodEvent
    {M₁ M₂ N₁ N₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hOwner₁ :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) N₁)
    (hOwner₂ :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) N₂)
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ N₁
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ N₂
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hOwnerZero :
      ∃ SOwner : Set Ω, MeasurableSet SOwner ∧ μ SOwner = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ SOwner →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                partitionQuadraticCovariationSum
                  Definition2158.dyadicPartitionSequence
                  (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                  (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                  t
                  n)
              atTop
              (𝓝 (0 : ℝ))) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  have hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) :=
    -- Proof comment: the first owner agrees with the first canonical cutoff realization on
    -- `[0, T]`.
    eqUpTo_constCutoffOwner_canonical
      (μ := μ) (ℱ := ℱ)
      (M := M₁) (H := H₁) (N := N₁) (hM := hM₁) (hbr := hbr₁) T hOwner₁
  have hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) :=
    -- Proof comment: the second owner gives the same comparison for the second cutoff
    -- realization.
    eqUpTo_constCutoffOwner_canonical
      (μ := μ) (ℱ := ℱ)
      (M := M₂) (H := H₂) (N := N₂) (hM := hM₂) (hbr := hbr₂) T hOwner₂
  rcases
      existsNullSet_forall_constCutoffEqUpTo_and_ownerDyadicSquareVariationTendsto_pair
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
        (H₁ := H₁) (H₂ := H₂)
        (A₁ := bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (A₂ := bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        T hEq₁ hEq₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq with
    ⟨SSq, hSSqMeas, hSSqNull, hSSqGood⟩
  rcases
      constCutoffGoodPath_plusMinusSquareVariation
        (μ := μ) (ℱ := ℱ) (M₁ := M₁) (M₂ := M₂) hM₁ hM₂ with
    ⟨SPath, hSPathMeas, hSPathNull, hSPathGood⟩
  rcases hOwnerZero with ⟨SOwner, hSOwnerMeas, hSOwnerNull, hSOwnerGood⟩
  have hSnull : μ (SOwner ∪ SPath ∪ SSq) = 0 := by
    have hUnionLe :
        μ (SOwner ∪ SPath ∪ SSq) ≤ μ (SOwner ∪ SPath) + μ SSq := by
      simpa [Set.union_assoc] using measure_union_le (SOwner ∪ SPath) SSq
    have hLeftNull : μ (SOwner ∪ SPath) = 0 := by
      have hLeftLe : μ (SOwner ∪ SPath) ≤ μ SOwner + μ SPath := measure_union_le SOwner SPath
      refine le_antisymm ?_ bot_le
      simpa [hSOwnerNull, hSPathNull] using hLeftLe
    refine le_antisymm ?_ bot_le
    simpa [hLeftNull, hSSqNull] using hUnionLe
  refine ⟨SOwner ∪ SPath ∪ SSq, (hSOwnerMeas.union hSPathMeas).union hSSqMeas, hSnull, ?_⟩
  intro ω hω t ht
  have hωOwner : ω ∉ SOwner := by
    exact fun hSOwnerω ↦ hω (by
      exact Set.mem_union_left SSq (Set.mem_union_left SPath hSOwnerω))
  have hωPath : ω ∉ SPath := by
    exact fun hSPathω ↦ hω (by
      exact Set.mem_union_left SSq (Set.mem_union_right SOwner hSPathω))
  have hωSq : ω ∉ SSq := by
    exact fun hSSqω ↦ hω (Set.mem_union_right (SOwner ∪ SPath) hSSqω)
  rcases hSSqGood hωSq with ⟨hEq₁ω, hEq₂ω, hSq₁ω, hSq₂ω⟩
  rcases hSPathGood hωPath with ⟨brAdd, brSub, hBrAdd, hBrSub⟩
  -- Proof comment: the owner mixed-row zero limit now supplies exactly the remaining input for
  -- the same-row transport theorem, while the two diagonal owner limits and the source-path good
  -- event are already packaged by existing helpers.
  exact
    constCutoffWeightedSourceDyadicTendstoCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
      (H₁ := H₁) (H₂ := H₂) (A := 0)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
      T ht ⟨brAdd, brSub, hBrAdd, hBrSub⟩ hEq₁ω hEq₂ω hSq₁ω hSq₂ω
      (hSOwnerGood hωOwner ht)

/-- Helper for Theorem 25.22: a canonical cutoff mixed partition limit transfers back to the
owner partition row once both owner paths agree with the canonical cutoff realizations on
`[0, T]`. -/
private theorem ownerPartition_tendsto_of_constCutoffCanonicalPartitionLimit
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁}
    {hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂}
    (T : NNReal)
    {ω : Ω} {t : NNReal} (ht : t ≤ T)
    (hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω)
    (hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω)
    (hCanonicalPartitionLimit :
      Tendsto
        (fun n ↦
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
            (fun k ↦
              (continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                continuousLocalMartingaleItoIntegralProcess hM₁
                  (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                  (Definition2158.dyadicPartitionSequence n k) ω) *
                (continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                  continuousLocalMartingaleItoIntegralProcess hM₂
                    (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                    (Definition2158.dyadicPartitionSequence n k) ω)))
        atTop
        (𝓝 (A t ω))) :
    Tendsto
      (fun n ↦
        partitionQuadraticCovariationSum
          Definition2158.dyadicPartitionSequence
          (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
          t
          n)
      atTop
      (𝓝 (A t ω)) := by
  -- Proof comment: the owner and canonical same-row partition sums agree termwise on `[0, T]`,
  -- so the canonical limit transfers back by one sequence rewrite.
  exact
    tendsto_nhds_of_seq_eq
      (fun n ↦
        ownerPartitionSum_eq_constCutoffCanonicalRow
          (μ := μ) (ℱ := ℱ)
          (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
          (H₁ := H₁) (H₂ := H₂)
          (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
          T ht hEq₁ω hEq₂ω n)
      hCanonicalPartitionLimit

/-- Helper for Theorem 25.22: once the canonical deterministic-cutoff pair already has a fixed
null-set complement on which its own mixed dyadic partition sums converge to `0`, the same owner
good event follows for any indistinguishable owner pair on `[0, T]`. -/
private theorem constCutoffOwnerPartitionGoodEvent_of_zeroCanonicalPartition
    {M₁ M₂ N₁ N₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁}
    {hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hCanonicalZero :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                Finset.sum
                  (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
                  (fun k ↦
                    (continuousLocalMartingaleItoIntegralProcess hM₁
                        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                      continuousLocalMartingaleItoIntegralProcess hM₁
                        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                        (Definition2158.dyadicPartitionSequence n k) ω) *
                    (continuousLocalMartingaleItoIntegralProcess hM₂
                        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                      continuousLocalMartingaleItoIntegralProcess hM₂
                        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                        (Definition2158.dyadicPartitionSequence n k) ω)))
              atTop
              (𝓝 (0 : ℝ))) :
    ∃ SOwner : Set Ω, MeasurableSet SOwner ∧ μ SOwner = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ SOwner →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              partitionQuadraticCovariationSum
                Definition2158.dyadicPartitionSequence
                (⟨fun s ↦ N₁ s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ N₂ s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEq₁ with
    ⟨S₁, hS₁meas, hS₁null, hS₁eq⟩
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEq₂ with
    ⟨S₂, hS₂meas, hS₂null, hS₂eq⟩
  rcases hCanonicalZero with ⟨S₀, hS₀meas, hS₀null, hS₀good⟩
  let SOwner : Set Ω := (S₀ ∪ S₁) ∪ S₂
  have hSOwnerNull : μ SOwner = 0 := by
    have hLeftNull : μ (S₀ ∪ S₁) = 0 := by
      have hUnionLe : μ (S₀ ∪ S₁) ≤ μ S₀ + μ S₁ := measure_union_le S₀ S₁
      refine le_antisymm ?_ bot_le
      simpa [hS₀null, hS₁null] using hUnionLe
    have hUnionLe : μ ((S₀ ∪ S₁) ∪ S₂) ≤ μ (S₀ ∪ S₁) + μ S₂ :=
      measure_union_le (S₀ ∪ S₁) S₂
    refine le_antisymm ?_ bot_le
    simpa [SOwner, hLeftNull, hS₂null] using hUnionLe
  refine ⟨SOwner, (hS₀meas.union hS₁meas).union hS₂meas, hSOwnerNull, ?_⟩
  intro ω hω t ht
  have hω₀ : ω ∉ S₀ := by
    exact fun hS₀ω ↦ hω (by exact Set.mem_union_left S₂ (Set.mem_union_left S₁ hS₀ω))
  have hω₁ : ω ∉ S₁ := by
    exact fun hS₁ω ↦ hω (by exact Set.mem_union_left S₂ (Set.mem_union_right S₀ hS₁ω))
  have hω₂ : ω ∉ S₂ := by
    exact fun hS₂ω ↦ hω (Set.mem_union_right (S₀ ∪ S₁) hS₂ω)
  have hEq₁ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₁ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω := by
    intro s hs
    exact hS₁eq hs hω₁
  have hEq₂ω :
      ∀ ⦃s : NNReal⦄, s ≤ T →
        N₂ s ω =
          continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω := by
    intro s hs
    exact hS₂eq hs hω₂
  -- Proof comment: off the combined good event, the canonical same-row limit is already zero,
  -- and the owner row is the same sequence after rewriting both coordinates on `[0, T]`.
  exact
    ownerPartition_tendsto_of_constCutoffCanonicalPartitionLimit
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂)
      (H₁ := H₁) (H₂ := H₂) (A := 0)
      (hN₁_mart := hN₁_mart) (hN₂_mart := hN₂_mart)
      T ht hEq₁ω hEq₂ω
      (hS₀good hω₀ ht)

/-- Helper for Theorem 25.22: once the canonical deterministic-cutoff pair already has almost
sure zero canonical same-row partition limit, the weighted cutoff source dyadic rows converge to
`0` off one fixed null set. -/
private theorem constCutoffZeroDyadicTendsto_of_aeZeroCanonicalPartition
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZeroCanonical :
      ∀ᵐ ω ∂μ,
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Finset.sum
                (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
                (fun k ↦
                  (continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
            atTop
            (𝓝 (0 : ℝ))) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  rcases ae_exists_nullSet_forall (μ := μ) hZeroCanonical with
    ⟨SZero, hSZeroMeas, hSZeroNull, hSZeroGood⟩
  rcases
      constCutoffGoodPath_plusMinusSquareVariation
        (μ := μ) (ℱ := ℱ) (M₁ := M₁) (M₂ := M₂) hM₁ hM₂ with
    ⟨SPath, hSPathMeas, hSPathNull, hSPathGood⟩
  rcases
      existsNullSet_forall_ownerDyadicSquareVariationTendsto
        (μ := μ) (ℱ := ℱ)
        (N := continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (A := bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        T hN₁_mart hN₁_sq with
    ⟨SSq₁, hSSq₁Meas, hSSq₁Null, hSSq₁Good⟩
  rcases
      existsNullSet_forall_ownerDyadicSquareVariationTendsto
        (μ := μ) (ℱ := ℱ)
        (N := continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (A := bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        T hN₂_mart hN₂_sq with
    ⟨SSq₂, hSSq₂Meas, hSSq₂Null, hSSq₂Good⟩
  let S : Set Ω := (((SZero ∪ SPath) ∪ SSq₁) ∪ SSq₂)
  have hSnull : μ S = 0 := by
    have hLeftNull : μ (SZero ∪ SPath) = 0 := by
      have hUnionLe : μ (SZero ∪ SPath) ≤ μ SZero + μ SPath := measure_union_le SZero SPath
      refine le_antisymm ?_ bot_le
      simpa [hSZeroNull, hSPathNull] using hUnionLe
    have hMidNull : μ ((SZero ∪ SPath) ∪ SSq₁) = 0 := by
      have hUnionLe :
          μ ((SZero ∪ SPath) ∪ SSq₁) ≤ μ (SZero ∪ SPath) + μ SSq₁ :=
        measure_union_le (SZero ∪ SPath) SSq₁
      refine le_antisymm ?_ bot_le
      simpa [hLeftNull, hSSq₁Null] using hUnionLe
    have hUnionLe :
        μ (((SZero ∪ SPath) ∪ SSq₁) ∪ SSq₂) ≤ μ ((SZero ∪ SPath) ∪ SSq₁) + μ SSq₂ :=
      measure_union_le (((SZero ∪ SPath) ∪ SSq₁)) SSq₂
    refine le_antisymm ?_ bot_le
    simpa [S, hMidNull, hSSq₂Null] using hUnionLe
  refine ⟨S, ((hSZeroMeas.union hSPathMeas).union hSSq₁Meas).union hSSq₂Meas, hSnull, ?_⟩
  intro ω hω t ht
  have hω_not : ω ∉ SZero ∧ ω ∉ SPath ∧ ω ∉ SSq₁ ∧ ω ∉ SSq₂ := by
    simpa [S, Set.mem_union, not_or, and_assoc] using hω
  rcases hSPathGood hω_not.2.1 with ⟨brAdd, brSub, hBrAdd, hBrSub⟩
  -- Proof comment: off the combined good event, the canonical same-row mixed partition sum
  -- already tends to `0`, and the existing source-dyadic bridge transfers that limit to the
  -- weighted source row using the two single-coordinate square-variation limits.
  exact
    constCutoffWeightedSourceDyadic_tendsto_of_canonicalPartitionCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (A := 0)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T ht ⟨brAdd, brSub, hBrAdd, hBrSub⟩
      (hSSq₁Good hω_not.2.2.1)
      (hSSq₂Good hω_not.2.2.2)
      (hSZeroGood hω_not.1 ht)

-- Route correction: the obsolete early `EqUpTo` branch is gone. This source-facing dyadic-zero
-- theorem should now consume the smaller compensator-to-zero core directly.
private theorem constCutoffZeroDyadicTendsto_of_zeroCompensatorCore
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZeroCore :
      ∃ A : NNReal → Ω → ℝ,
        IsContinuousQuadraticCovariationProcess ℱ μ
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          A ∧
        EqUpTo μ T A 0) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  rcases hZeroCore with ⟨A, hA, hEqZero⟩
  have hZeroCanonical :
      ∀ᵐ ω ∂μ,
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Finset.sum
                (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
                (fun k ↦
                  (continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₁
                      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω) *
                  (continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k t) ω -
                    continuousLocalMartingaleItoIntegralProcess hM₂
                      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
                      (Definition2158.dyadicPartitionSequence n k) ω)))
            atTop
            (𝓝 (0 : ℝ)) := by
    -- Proof comment: once one genuine canonical compensator is already `EqUpTo μ T` to `0`,
    -- the canonical same-row mixed partition sums converge to `0` on `[0, T]`.
    exact
      constCutoffAeZeroCanonicalPartition_of_eqUpToZero
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
        T hN₁_mart hN₂_mart hA hEqZero
  -- Proof comment: the existing canonical-partition-to-source-dyadic bridge now finishes the
  -- source-facing dyadic-zero statement without reconstructing a global zero witness.
  exact
    constCutoffZeroDyadicTendsto_of_aeZeroCanonicalPartition
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZeroCanonical

/-- Helper for Theorem 25.22: any genuine mixed compensator for the canonical deterministic-cutoff
pair agrees on `[0,T]` with the canonical dyadic mixed compensator. -/
private theorem constCutoffCanonicalCompensator_eqUpTo
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      A := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  -- Proof comment: specialize the generic compensator-identification theorem to the canonical
  -- deterministic-cutoff pair and rewrite the two coordinates through short aliases.
  simpa [N₁c, N₂c] using
    (eqUpTo_quadraticCovariationIntegralUpTo_of_isContinuousQuadraticCovariationProcess
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁c) (N₂ := N₂c)
      (H₁ := H₁) (H₂ := H₂) (A := A)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T
      (eqUpTo_rfl (μ := μ) T N₁c)
      (eqUpTo_rfl (μ := μ) T N₂c)
      hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA)

/-- Helper for Theorem 25.22: once the canonical cutoff pair has almost-sure pathwise zero
quadratic covariation, any genuine compensator of that pair is `EqUpTo μ T` to `0`. -/
private theorem constCutoffOwnerCompensator_eqUpTo_zero_of_aeZeroCanonicalPath
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A)
    (hZeroAE :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun s ↦
              continuousLocalMartingaleItoIntegralProcess hM₁
                (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω,
            hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦
              continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω,
            hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
          0) :
    EqUpTo μ T A 0 := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  have hAPath :
      ∀ᵐ ω ∂μ,
        HasQuadraticCovariationAlong
          (⟨fun s ↦ N₁c s ω, hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
          (⟨fun s ↦ N₂c s ω, hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
          (fun s ↦ A s ω) := by
    -- Proof comment: the generic owner theorem already gives the pathwise witness attached to
    -- the genuine compensator `A`.
    simpa [N₁c, N₂c] using
      (aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
        (μ := μ) (ℱ := ℱ) hN₁_mart hN₂_mart hA)
  have hEqAE : ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = 0 := by
    filter_upwards [hAPath, hZeroAE] with ω hAω hZeroω
    intro t
    -- Proof comment: pathwise quadratic covariation is unique, so on each good sample path the
    -- genuine compensator path must equal the zero path at every deterministic time.
    simpa using congrFun (hasQuadraticCovariationAlong_eq hAω hZeroω) t
  rcases ae_exists_nullSet_forall (μ := μ) hEqAE with
    ⟨S, hSmeas, hSnull, hSgood⟩
  refine ⟨S, hSmeas, hSnull, ?_⟩
  intro t _ht ω hneq
  by_contra hωS
  -- Proof comment: outside the fixed null set produced from the almost-sure pathwise equality,
  -- the compensator path is literally zero at every time.
  exact hneq (hSgood hωS t)

/-- Helper for Theorem 25.22: once the weighted cutoff source dyadic rows already converge to `0`,
one genuine compensator of the canonical cutoff pair is automatically `EqUpTo μ T` to `0`. -/
private theorem constCutoffZeroCompensatorCore_of_zeroDyadic
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZeroDyadic :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                  (fun s ↦
                    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  t
                  n)
              atTop
              (𝓝 (0 : ℝ))) :
    ∃ A : NNReal → Ω → ℝ,
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A ∧
      EqUpTo μ T A 0 := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  rcases
      existsQuadraticCovariationPair_of_isContinuousLocalMartingale
        (μ := μ) (ℱ := ℱ)
        (N₁ := N₁c) (N₂ := N₂c)
        hN₁_mart hN₂_mart with
    ⟨A, _, hA, _⟩
  refine ⟨A, hA, ?_⟩
  -- Proof comment: choose any genuine owner compensator for the canonical cutoff pair and use
  -- the already-proved zero-dyadic transport theorem to identify it with `0` on `[0, T]`.
  exact
    constCutoffOwnerCompensator_eqUpTo_zero_of_zeroDyadic
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (N₁ := N₁c) (N₂ := N₂c)
      (H₁ := H₁) (H₂ := H₂)
      (A := A)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T
      (eqUpTo_rfl (μ := μ) T N₁c)
      (eqUpTo_rfl (μ := μ) T N₂c)
      hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA hZeroDyadic

/-- Helper for Theorem 25.22: if every integer horizon already carries zero quadratic covariation
up to that horizon, then almost every sample path has global zero quadratic covariation. -/
private theorem aeHasQuadraticCovariationAlong_zero_of_upToNat
    {N₁ N₂ : NNReal → Ω → ℝ}
    (hN₁ : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂ : IsContinuousLocalMartingale ℱ μ N₂)
    (hZeroNat :
      ∀ n : ℕ, IsContinuousQuadraticCovariationProcessUpTo ℱ μ (n : NNReal) N₁ N₂ 0) :
    ∀ᵐ ω ∂μ,
      HasQuadraticCovariationAlong
        (⟨fun s ↦ N₁ s ω, hN₁.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦ N₂ s ω, hN₂.continuous ω⟩ : C(NNReal, ℝ))
        0 := by
  have hStoppedGood :
      ∀ n : ℕ,
        ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
          ∀ ⦃ω : Ω⦄, ω ∉ S →
            ∀ t : NNReal,
              Tendsto
                (fun m ↦
                  partitionQuadraticCovariationSum
                    Definition2158.dyadicPartitionSequence
                    (⟨fun s ↦
                        stoppedProcess N₁ (fun _ ↦ ((n : NNReal) : ENNReal)) s ω,
                      continuous_stoppedProcess_of_continuous hN₁.continuous ω⟩ :
                      C(NNReal, ℝ))
                    (⟨fun s ↦
                        stoppedProcess N₂ (fun _ ↦ ((n : NNReal) : ENNReal)) s ω,
                      continuous_stoppedProcess_of_continuous hN₂.continuous ω⟩ :
                      C(NNReal, ℝ))
                    t
                    m)
                atTop
                (𝓝 (0 : ℝ)) := by
    intro n
    let σ : Ω → ENNReal := fun _ ↦ ((n : NNReal) : ENNReal)
    have hStoppedN₁ :
        IsContinuousLocalMartingale ℱ μ (stoppedProcess N₁ σ) := by
      -- Proof comment: deterministic stopping preserves the continuous local-martingale
      -- structure of the first coordinate.
      exact
        { local_martingale :=
            isLocalMartingale_stoppedProcess_constTime
              (ℱ := ℱ)
              (μ := μ)
              hN₁.local_martingale
              hN₁.continuous
              (n : NNReal)
          continuous := by
            intro ω
            exact continuous_stoppedProcess_of_continuous hN₁.continuous ω }
    have hStoppedN₂ :
        IsContinuousLocalMartingale ℱ μ (stoppedProcess N₂ σ) := by
      -- Proof comment: apply the same deterministic-stopping argument to the second coordinate.
      exact
        { local_martingale :=
            isLocalMartingale_stoppedProcess_constTime
              (ℱ := ℱ)
              (μ := μ)
              hN₂.local_martingale
              hN₂.continuous
              (n : NNReal)
          continuous := by
            intro ω
            exact continuous_stoppedProcess_of_continuous hN₂.continuous ω }
    have hStoppedZero :
        IsContinuousQuadraticCovariationProcess ℱ μ
          (stoppedProcess N₁ σ)
          (stoppedProcess N₂ σ)
          0 := by
      -- Proof comment: the supplied `...UpTo` witness becomes a genuine global zero witness
      -- after deterministically stopping both coordinates at the same integer horizon.
      exact
        stoppedQuadraticCovariation_zero_of_upTo
          (ℱ := ℱ)
          (μ := μ)
          (M := N₁)
          (N := N₂)
          hN₁
          hN₂
          (hZeroNat n)
    have hStoppedAE :
        ∀ᵐ ω ∂μ,
          ∀ t : NNReal,
            Tendsto
              (fun m ↦
                partitionQuadraticCovariationSum
                  Definition2158.dyadicPartitionSequence
                  (⟨fun s ↦ stoppedProcess N₁ σ s ω,
                    continuous_stoppedProcess_of_continuous hN₁.continuous ω⟩ :
                    C(NNReal, ℝ))
                  (⟨fun s ↦ stoppedProcess N₂ σ s ω,
                    continuous_stoppedProcess_of_continuous hN₂.continuous ω⟩ :
                    C(NNReal, ℝ))
                  t
                  m)
              atTop
              (𝓝 (0 : ℝ)) := by
      have hPath :
          ∀ᵐ ω ∂μ,
            HasQuadraticCovariationAlong
              (⟨fun s ↦ stoppedProcess N₁ σ s ω,
                continuous_stoppedProcess_of_continuous hN₁.continuous ω⟩ :
                C(NNReal, ℝ))
              (⟨fun s ↦ stoppedProcess N₂ σ s ω,
                continuous_stoppedProcess_of_continuous hN₂.continuous ω⟩ :
                C(NNReal, ℝ))
              0 := by
        -- Proof comment: the generic owner theorem turns the stopped zero witness into an
        -- almost-sure pathwise zero-covariation statement.
        exact
          aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
            (μ := μ)
            (ℱ := ℱ)
            hStoppedN₁
            hStoppedN₂
            hStoppedZero
      filter_upwards [hPath] with ω hω t
      -- Proof comment: on each good stopped path, the defining dyadic partition sums converge to
      -- the zero witness at every deterministic horizon.
      simpa [partitionQuadraticCovariationSum] using
        HasQuadraticCovariationAlong.tendsto_partition_sum hω t
    exact ae_exists_nullSet_forall (μ := μ) hStoppedAE
  choose S hSmeas hSnull hSgood using hStoppedGood
  let Sbad : Set Ω := ⋃ n : ℕ, S n
  have hSbadMeas : MeasurableSet Sbad := by
    exact MeasurableSet.iUnion hSmeas
  have hSbadNull : μ Sbad = 0 := by
    refine measure_iUnion_null ?_
    intro n
    exact hSnull n
  refine ae_iff.2 ?_
  refine measure_mono_null ?_ hSbadNull
  intro ω hωBad
  by_contra hωSbad
  apply hωBad
  intro t
  let n : ℕ := Nat.ceil (t : ℝ)
  have ht_le_n : t ≤ (n : NNReal) := by
    exact_mod_cast (Nat.le_ceil (t : ℝ))
  have hωSn : ω ∉ S n := by
    intro hωSn
    exact hωSbad (Set.mem_iUnion.2 ⟨n, hωSn⟩)
  let F : C(NNReal, ℝ) := ⟨fun s ↦ N₁ s ω, hN₁.continuous ω⟩
  let G : C(NNReal, ℝ) := ⟨fun s ↦ N₂ s ω, hN₂.continuous ω⟩
  let Fstop : C(NNReal, ℝ) := ⟨fun s ↦
      stoppedProcess N₁ (fun _ ↦ ((n : NNReal) : ENNReal)) s ω,
      continuous_stoppedProcess_of_continuous hN₁.continuous ω⟩
  let Gstop : C(NNReal, ℝ) := ⟨fun s ↦
      stoppedProcess N₂ (fun _ ↦ ((n : NNReal) : ENNReal)) s ω,
      continuous_stoppedProcess_of_continuous hN₂.continuous ω⟩
  have hStoppedLimit :
      Tendsto
        (fun m ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            Fstop
            Gstop
            t
            m)
        atTop
        (𝓝 (0 : ℝ)) :=
    hSgood n hωSn t
  have hEqF : Set.EqOn F Fstop (Set.Icc 0 t) := by
    intro s hs
    have hs_le_n : s ≤ (n : NNReal) := le_trans hs.2 ht_le_n
    have hStoppedEq :
        stoppedProcess N₁ (fun _ ↦ ((n : NNReal) : ENNReal)) s ω = N₁ s ω := by
      simpa [min_eq_left hs_le_n] using
        congrFun (stoppedProcessConstTime_eq_min (X := N₁) (n : NNReal) s) ω
    exact hStoppedEq.symm
  have hEqG : Set.EqOn G Gstop (Set.Icc 0 t) := by
    intro s hs
    have hs_le_n : s ≤ (n : NNReal) := le_trans hs.2 ht_le_n
    have hStoppedEq :
        stoppedProcess N₂ (fun _ ↦ ((n : NNReal) : ENNReal)) s ω = N₂ s ω := by
      simpa [min_eq_left hs_le_n] using
        congrFun (stoppedProcessConstTime_eq_min (X := N₂) (n : NNReal) s) ω
    exact hStoppedEq.symm
  have hRowEq :
      ∀ m : ℕ,
        partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            t
            m =
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            Fstop
            Gstop
            t
            m := by
    intro m
    -- Proof comment: at the chosen integer horizon, stopping does not change either path on
    -- `[0, t]`, so the dyadic mixed rows agree termwise.
    exact
      Theorem25_22.partitionQuadraticCovariationSum_congrOn_Icc
        Definition2158.dyadicPartitionSequence
        hEqF
        hEqG
        m
  exact
    Tendsto.congr'
      (Filter.Eventually.of_forall fun m ↦ (hRowEq m).symm)
      hStoppedLimit

/-- Helper for Theorem 25.22: the remaining finite-horizon independence input is that the
deterministically stopped product of the two canonical cutoff coordinates is a local martingale. -/
private theorem constCutoffZeroUpTo_of_zeroDyadic_of_le
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T U : NNReal)
    (hUT : U ≤ T)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZeroDyadic :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                  (fun s ↦
                    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  t
                  n)
              atTop
              (𝓝 (0 : ℝ))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ U
      (continuousLocalMartingaleItoIntegralProcess hM₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
      (continuousLocalMartingaleItoIntegralProcess hM₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      0 := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  rcases
      constCutoffZeroCompensatorCore_of_zeroDyadic
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂)
        (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂)
        (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZeroDyadic with
    ⟨A, hA, hEqZero⟩
  have hEqZeroU : EqUpTo μ U A 0 := by
    rcases hEqZero with ⟨S, hSmeas, hSnull, hSsub⟩
    refine ⟨S, hSmeas, hSnull, ?_⟩
    intro t ht
    -- Proof comment: the original `EqUpTo` witness on `[0, T]` restricts immediately to the
    -- smaller horizon `[0, U]`.
    exact hSsub (le_trans ht hUT)
  have hQuadUpToA :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ U N₁c N₂c A := by
    -- Proof comment: once the genuine owner compensator exists globally, packaging it on the
    -- shorter horizon `[0, U]` is only the reflexive `...UpTo` wrapper.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
        (μ := μ) (ℱ := ℱ) (T := U) hA
  -- Proof comment: transport the packaged owner witness from the genuine compensator `A` to the
  -- zero compensator using the restricted `EqUpTo` comparison.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (μ := μ) (ℱ := ℱ)
      (eqUpTo_rfl (μ := μ) U N₁c)
      (eqUpTo_rfl (μ := μ) U N₂c)
      (eqUpTo_sym hEqZeroU)
      hQuadUpToA

/-- Helper for Theorem 25.22: below the cutoff horizon, a zero-dyadic witness already makes the
deterministically stopped cutoff product a local martingale. -/
private theorem constCutoffStoppedProductLocalMartingale_of_zeroDyadic_of_le
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T U : NNReal)
    (hUT : U ≤ T)
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hZeroDyadic :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                  (fun s ↦
                    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  t
                  n)
              atTop
              (𝓝 (0 : ℝ))) :
    IsLocalMartingale ℱ μ
      (stoppedProcess
        (fun t ω ↦
          continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
          continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω)
        (fun _ ↦ (U : ENNReal))) := by
  have hQuadUpTo :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ U
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0 := by
    -- Proof comment: first package the zero-dyadic convergence into a finite-horizon zero
    -- quadratic-covariation witness on `[0, U]`.
    exact
      constCutoffZeroUpTo_of_zeroDyadic_of_le
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂)
        (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂)
        (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T U hUT hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZeroDyadic
  have hMart :
      Martingale
        (stoppedProcess
          (fun t ω ↦
            continuousLocalMartingaleItoIntegralProcess hM₁
                (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
            continuousLocalMartingaleItoIntegralProcess hM₂
                (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω)
          (fun _ ↦ (U : ENNReal))) ℱ μ := by
    -- Proof comment: the existing stopped-product theorem turns that zero witness into a true
    -- martingale at the deterministic stop `U`.
    exact
      constCutoffStoppedProduct_martingale_of_zeroUpTo
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂)
        (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂)
        T U hN₁_mart hN₂_mart hQuadUpTo
  -- Proof comment: every martingale is, in particular, a local martingale.
  exact martingale_isLocalMartingale hMart

/-- Helper for Theorem 25.22: once an integrand is already cut off at `T`, cutting it off again
at any later deterministic horizon `U` does not change it. -/
private lemma processBeforeStoppingTime_constCutoff_eq_self_of_le
    {H : NNReal → Ω → ℝ} {T U : NNReal} (hTU : T ≤ U) :
    processBeforeStoppingTime
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)))
      (fun _ ↦ (U : ENNReal)) =
    processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) := by
  funext t ω
  have hTU' : (T : ENNReal) ≤ (U : ENNReal) := by
    exact_mod_cast hTU
  by_cases hU : (t : ENNReal) ≤ (U : ENNReal)
  · by_cases hT : (t : ENNReal) ≤ (T : ENNReal)
    · -- Proof comment: before `T`, both nested deterministic cutoffs return the original value.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hU, hT]
    · -- Proof comment: between `T` and `U`, the inner deterministic cutoff has already forced the
      -- coefficient to vanish.
      simp [ProbabilityTheory.processBeforeStoppingTime_apply, hU, hT]
  · have hT : ¬ (t : ENNReal) ≤ (T : ENNReal) := by
      intro ht
      exact hU (le_trans ht hTU')
    -- Proof comment: after the later cutoff time `U`, both sides vanish by definition.
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hU]
    rw [ProbabilityTheory.processBeforeStoppingTime_apply, if_neg hT]

/-- Helper for Theorem 25.22: on `[0,T]`, a deterministic stop at `T` does not change the
canonical cutoff coordinate. -/
private theorem constCutoffCoordinate_eqUpTo_stoppedConstTime
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal) :
    EqUpTo μ T
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (T : ENNReal))) := by
  refine ⟨∅, MeasurableSet.empty, by simp, ?_⟩
  intro t ht ω hω
  have hStoppedEq :
      stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal))
          t
          ω =
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
          t
          ω := by
    -- Proof comment: before the deterministic horizon `T`, the stopped process is just the
    -- original cutoff coordinate evaluated at the same time.
    simpa [min_eq_left ht] using
      congrFun
        (stoppedProcessConstTime_eq_min
          (X := continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          T t)
        ω
  exact (hω hStoppedEq.symm).elim

/-- Helper for Theorem 25.22: any cutoff owner agrees almost surely at a fixed deterministic
time with the canonical dyadic value of the same deterministic cutoff. -/
private theorem itoIntegralOwner_aeEq_constCutoffCanonicalAtFixedTime
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (hOwner :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr H N)
    (U : NNReal) :
    N U =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H (fun _ ↦ (U : ENNReal)))
        U := by
  have hCanonical :
      N U =ᵐ[μ] continuousLocalMartingaleItoIntegralProcess hM H U := by
    rcases hOwner.indistinguishable_canonical with ⟨bad, _hbad_meas, hbad_null, hbad_sub⟩
    -- Proof comment: indistinguishability already stores one null set controlling every
    -- deterministic time, so a fixed time slice is immediate.
    refine ae_iff.2 ?_
    exact measure_mono_null (hbad_sub U) hbad_null
  have hCutoff :
      continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H (fun _ ↦ (U : ENNReal)))
          U =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM H U := by
    -- Proof comment: at the same deterministic horizon `U`, cutting off the integrand at `U`
    -- does not change the canonical dyadic value.
    refine Filter.Eventually.of_forall ?_
    intro ω
    exact
      continuousLocalMartingaleItoIntegralProcess_eq_constCutoff_value
        (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) U ω
  -- Proof comment: first identify the owner with the unstopped canonical value, then normalize
  -- that fixed-time canonical value through the matching deterministic cutoff.
  exact hCanonical.trans hCutoff.symm

/-- Helper for Theorem 25.22: deterministic stopping preserves the square-variation witness of a
canonical cutoff coordinate. -/
private theorem constCutoffCoordinate_stoppedSquareVariation_of_constTime
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T U : NNReal)
    (hN_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    IsContinuousSquareVariationProcess ℱ μ
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (U : ENNReal)))
      (stoppedProcess
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (U : ENNReal))) := by
  -- Proof comment: stopping the canonical cutoff coordinate and its bracket witness at the same
  -- deterministic horizon is exactly the Chapter 21 stopped square-variation theorem.
  exact
    _root_.ProbabilityTheory.stoppedSquareVariationProcess
      (ℱ := ℱ)
      (μ := μ)
      hN_sq
      (isStoppingTime_const ℱ U)

/-- Helper for Theorem 25.22: the bracket witness of a deterministic-cutoff coefficient is
already frozen by the same deterministic stop. -/
private theorem bracketDensityIntegralUpTo_constCutoff_eq_stoppedConstTime
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal) :
    stoppedProcess
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (T : ENNReal)) =
      bracketDensityIntegralUpTo hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) := by
  funext t ω
  by_cases ht : t ≤ T
  · -- Proof comment: before the cutoff horizon, deterministic stopping just evaluates the same
    -- bracket witness at time `t`.
    simp [stoppedProcessConstTime_eq_min, min_eq_left ht]
  · have hTt : T ≤ t := le_of_not_ge ht
    have hTt_real : (T : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hTt
    let f : ℝ → ℝ := fun s ↦
      (processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s.toNNReal ω) ^ 2 *
        (squareVariationDensity hbr s.toNNReal ω : ℝ)
    have hCutoffZero :
        ∀ ⦃s : ℝ⦄, s ∈ Set.Icc (0 : ℝ) (t : ℝ) →
          ¬ s ∈ Set.Icc (0 : ℝ) (T : ℝ) →
            f s = 0 := by
      intro s hs hs_not_mem
      have hsT : ¬ s ≤ (T : ℝ) := by
        intro hs_le_T
        exact hs_not_mem ⟨hs.1, hs_le_T⟩
      have hs_not_cutoff : ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
        intro hs_cutoff
        exact hsT ((Real.toNNReal_le_iff_le_coe).1 (by exact_mod_cast hs_cutoff))
      -- Proof comment: beyond `T`, the deterministic cutoff kills the coefficient, so the
      -- bracket-density integrand itself vanishes.
      have hcut :
          ProbabilityTheory.processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) s.toNNReal ω = 0 := by
        simp [ProbabilityTheory.processBeforeStoppingTime_apply, hs_not_cutoff]
      simp [f, hcut]
    have hIndicatorEq :
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), f s) =
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
            Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := by
      refine integral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 ?_
      refine Filter.Eventually.of_forall ?_
      intro s hs
      by_cases hs_mem : s ∈ Set.Icc (0 : ℝ) (T : ℝ)
      · -- Proof comment: on `[0,T]`, the indicator leaves the bracket-density integrand
        -- unchanged.
        simp [Set.indicator_of_mem, hs_mem]
      · -- Proof comment: on `(T,t]`, the deterministic cutoff has already forced the integrand
        -- to vanish.
        simp [Set.indicator_of_notMem, hs_mem, hCutoffZero hs hs_mem]
    have hSubset :
        Set.Icc (0 : ℝ) (T : ℝ) ⊆ Set.Icc (0 : ℝ) (t : ℝ) := by
      intro s hs
      exact ⟨hs.1, hs.2.trans hTt_real⟩
    have hFreeze :
        bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            t
            ω =
          bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            T
            ω := by
      -- Proof comment: after rewriting the later-horizon integral by the indicator of `[0,T]`,
      -- only the original interval `[0,T]` remains.
      simpa [bracketDensityIntegralUpTo, f] using
        (calc
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ), f s =
          ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
                Set.indicator (Set.Icc (0 : ℝ) (T : ℝ)) f s := hIndicatorEq
          _ = ∫ s in Set.Icc (0 : ℝ) (T : ℝ), f s := by
            rw [integral_indicator measurableSet_Icc]
            simp [Measure.restrict_restrict, Set.inter_eq_left.mpr hSubset, measurableSet_Icc])
    -- Proof comment: once the bracket witness is constant after `T`, its deterministic stop at
    -- `T` is literally the same process.
    calc
      stoppedProcess
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal))
          t
          ω =
        bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
          T
          ω := by
            simp [stoppedProcessConstTime_eq_min, min_eq_right hTt]
      _ =
        bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
          t
          ω := hFreeze.symm

/-- Helper for Theorem 25.22: a deterministic cutoff vanishes strictly after its cutoff time. -/
private theorem constCutoffCoordinate_stoppedSquareVariation_sameWitness
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hStoppedN_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal)))
        (stoppedProcess
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal)))) :
    IsContinuousSquareVariationProcess ℱ μ
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (T : ENNReal)))
      (bracketDensityIntegralUpTo hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  -- Proof comment: the stopped square-variation theorem introduces the stopped bracket witness,
  -- but for a deterministic cutoff coefficient that bracket process is already frozen at time `T`.
  simpa
    [bracketDensityIntegralUpTo_constCutoff_eq_stoppedConstTime
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using
    hStoppedN_sq

/-- Helper for Theorem 25.22: a deterministic cutoff vanishes strictly after its cutoff time. -/
private lemma processBeforeStoppingTime_apply_eq_zero_of_lt_const
    {H : NNReal → Ω → ℝ} {T t : NNReal} {ω : Ω}
    (hTt : T < t) :
    processBeforeStoppingTime H (fun _ ↦ (T : ENNReal)) t ω = 0 := by
  have htT : ¬ (t : ENNReal) ≤ (T : ENNReal) := by
    intro htt
    exact not_lt_of_ge (by exact_mod_cast htt) hTt
  -- Proof comment: once `t` is strictly past the deterministic cutoff time, the stopped
  -- coefficient takes its zero branch by definition.
  simp [ProbabilityTheory.processBeforeStoppingTime_apply, htT]

/-- Helper for Theorem 25.22: a source owner whose later deterministic value already freezes at
`T` immediately transports that fixed-time equality to the canonical cutoff coordinate. -/
private theorem constCutoffCoordinate_ae_eq_terminalValue_of_le_of_ownerFreeze
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T U : NNReal)
    (hOwner :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N)
    (hFreeze : N U =ᵐ[μ] N T) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        U =ᵐ[μ]
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        T := by
  have hAtU :
      N U =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
          U :=
    ProbabilityTheory.areModifications_of_areIndistinguishable
      μ
      N
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
      hOwner.indistinguishable_canonical
      U
  have hAtT :
      N T =ᵐ[μ]
        continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
          T :=
    ProbabilityTheory.areModifications_of_areIndistinguishable
      μ
      N
      (continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
      hOwner.indistinguishable_canonical
      T
  -- Proof comment: compare both canonical fixed-time values with the same owner process, then
  -- insert the owner-side freeze at times `U` and `T`.
  exact hAtU.symm.trans (hFreeze.trans hAtT)

/-- Helper for Theorem 25.22: stopping a genuine cutoff owner at the cutoff horizon preserves the
same bracket witness because the bracket process is already frozen after `T`. -/
private theorem constCutoffOwner_stoppedSquareVariation_sameWitness
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hN_sq :
      IsContinuousSquareVariationProcess ℱ μ
        N
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    IsContinuousSquareVariationProcess ℱ μ
      (stoppedProcess N (fun _ ↦ (T : ENNReal)))
      (bracketDensityIntegralUpTo hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) := by
  have hStoppedSq :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess N (fun _ ↦ (T : ENNReal)))
        (stoppedProcess
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: first stop both the owner and its square-variation witness at the same
    -- deterministic horizon.
    exact
      _root_.ProbabilityTheory.stoppedSquareVariationProcess
        (ℱ := ℱ)
        (μ := μ)
        hN_sq
        (isStoppingTime_const ℱ T)
  -- Proof comment: for a deterministically cut-off coefficient, the bracket witness is already
  -- frozen after `T`, so the extra stop on the witness disappears.
  simpa
    [bracketDensityIntegralUpTo_constCutoff_eq_stoppedConstTime
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using
    hStoppedSq

/-- Helper for Theorem 25.22: deterministically stopping the canonical cutoff coordinate at its
own cutoff horizon keeps it inside the continuous-local-martingale surface. -/
private theorem constCutoffCoordinate_stoppedContinuousLocalMartingale_of_constTime
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    (T : NNReal)
    (hN_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))) :
    IsContinuousLocalMartingale ℱ μ
      (stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (T : ENNReal))) := by
  refine
    { local_martingale := ?_
      continuous := ?_ }
  · -- Proof comment: deterministic stopping preserves the local-martingale field of the cutoff
    -- coordinate.
    simpa using
      constCutoffCoordinate_stoppedLocalMartingale_of_constTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        T
        T
        hN_mart
  · -- Proof comment: pathwise continuity is preserved by deterministic stopping.
    intro ω
    exact continuous_stoppedProcess_of_continuous hN_mart.continuous ω

/-- Helper for Theorem 25.22: if two continuous compensators agree on `[0,T]` off one null set
and both are frozen after `T`, then they agree for all deterministic times off one null set. -/
private theorem ae_eq_allTimes_of_eqUpTo_and_frozen_after
    {A B : NNReal → Ω → ℝ}
    {T : NNReal}
    (hEq : EqUpTo μ T A B)
    (hAfreeze :
      ∀ ω : Ω, ∀ t : NNReal, T ≤ t → A t ω = A T ω)
    (hBfreeze :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → B t ω = B T ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω := by
  rcases eqUpTo_forall_eq (μ := μ) (T := T) hEq with
    ⟨S, _hSmeas, hSnull, hSeq⟩
  have hSae : ∀ᵐ ω ∂μ, ω ∉ S :=
    compl_mem_ae_iff.mpr hSnull
  filter_upwards [hSae, hBfreeze] with ω hωS hBω t
  by_cases ht : t ≤ T
  · -- Proof comment: below the horizon, the original `EqUpTo` witness already gives the pointwise
    -- compensator equality.
    exact hSeq ht hωS
  · have hTt : T ≤ t := le_of_not_ge ht
    -- Proof comment: above `T`, both compensators collapse to their time-`T` value.
    calc
      A t ω = A T ω := hAfreeze ω t hTt
      _ = B T ω := hSeq le_rfl hωS
      _ = B t ω := (hBω t hTt).symm

/-- Helper for Theorem 25.22: a genuine quadratic-covariation witness can be transported across an
all-times almost-sure compensator equality once the replacement process already carries the
structural compensator fields. -/
private theorem continuousQuadraticCovariation_of_ae_eq_allTimes_compensator
    {M N A B : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hCovB : IsContinuousQuadraticCovariationProcess ℱ μ M N B)
    (hAzero : A 0 = 0)
    (hAadapted : Adapted ℱ A)
    (hAcont : ∀ ω : Ω, Continuous fun t : NNReal ↦ A t ω)
    (hALFV :
      ∀ᵐ ω ∂μ,
        LocallyBoundedVariationOn
          (⟨fun t ↦ A t ω, hAcont ω⟩ : C(NNReal, ℝ))
          Set.univ)
    (hABall : ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω) :
    IsContinuousQuadraticCovariationProcess ℱ μ M N A := by
  have hMulAdapted :
      Adapted ℱ (fun t ω ↦ M t ω * N t ω) := by
    exact hM.adapted.mul hN.adapted
  have hMulCont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω * N t ω := by
    intro ω
    exact (hM.continuous ω).mul (hN.continuous ω)
  refine
    { zero := hAzero
      adapted := hAadapted
      continuous := hAcont
      locally_finite_variation := hALFV
      local_martingale_mul_sub := ?_ }
  -- Proof comment: once `A` and `B` agree outside one null set for all deterministic times, the
  -- same compensated-product local martingale transports from `B` to `A`.
  exact
    isLocalMartingale_congr_ae_allTimes
      hCovB.local_martingale_mul_sub
      (hMulAdapted.sub hAadapted)
      (fun ω ↦ (hMulCont ω).sub (hAcont ω))
          (by
        filter_upwards [hABall] with ω hω t
        simp [hω t])

/-- Helper for Theorem 25.22: once the right path is frozen after `T`, the dyadic mixed sum at a
later horizon `t` differs from the horizon-`T` row by exactly one boundary increment. -/
private theorem partitionQuadraticCovariationSum_eq_terminal_plus_boundary_of_rightConstAfter
    {F G : PathSpace}
    {T t : NNReal}
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T)
    (n : ℕ) :
    partitionQuadraticCovariationSum
        Definition2158.dyadicPartitionSequence
        F
        G
        t
        n =
      partitionQuadraticCovariationSum
          Definition2158.dyadicPartitionSequence
          F
          G
          T
          n +
        (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
            F T) *
          (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
  let P := Definition2158.dyadicPartitionSequence
  let K := partitionBoundIndex P n T
  let N := partitionBoundIndex P n t
  let termt : ℕ → ℝ := fun k ↦
    (F (partitionNextPointUpTo P n k t) - F (P n k)) *
      (G (partitionNextPointUpTo P n k t) - G (P n k))
  let termT : ℕ → ℝ := fun k ↦
    (F (partitionNextPointUpTo P n k T) - F (P n k)) *
      (G (partitionNextPointUpTo P n k T) - G (P n k))
  have hKN : K ≤ N := dyadicPartitionBoundIndex_monotone n hTt
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [K, hK0] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by
        simpa [P, Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hle0' bot_le
    subst hT0
    have hsumt_zero :
        partitionQuadraticCovariationSum P F G t n = 0 := by
      rw [partitionQuadraticCovariationSum]
      have htail :
          ∀ k ∈ Finset.range (partitionBoundIndex P n t), termt k = 0 := by
        intro k hk
        have hk_mem :
            P n k ∈ Set.Icc 0 t :=
          Theorem25_22.partitionPoint_mem_Icc_of_lt_partitionBoundIndex
            P n k t (Finset.mem_range.mp hk)
        have hnext_mem :
            partitionNextPointUpTo P n k t ∈ Set.Icc 0 t := by
          constructor
          · exact bot_le
          · simp [partitionNextPointUpTo]
        have hleft : G (P n k) = G 0 := hGconst (P n k) hk_mem.1
        have hright : G (partitionNextPointUpTo P n k t) = G 0 := hGconst _ hnext_mem.1
        -- Proof comment: after time `0`, the frozen right path contributes only zero increments.
        simp [termt, hleft, hright]
      refine Finset.sum_eq_zero ?_
      intro k hk
      exact htail k hk
    have hsumT_zero :
        partitionQuadraticCovariationSum P F G 0 n = 0 := by
      simp [P, partitionQuadraticCovariationSum, dyadicPartitionBoundIndex_zero]
    -- Proof comment: if `T = 0`, both truncated mixed rows vanish because the right path is
    -- already constant from time `0` onward, and the boundary factor also vanishes.
    simp [P, K, hK0, hsumt_zero, hsumT_zero, dyadicSquareVariationBoundaryPoint,
      Definition2158.dyadicPartitionSequence, partitionNextPointUpTo]
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, K = j + 1 := ⟨K - 1, (Nat.sub_add_cancel hKpos).symm⟩
    have hjBoundT : j < K := by
      rw [hj]
      exact Nat.lt_succ_self j
    have hjBoundt : j < N := lt_of_lt_of_le hjBoundT hKN
    have hPj_lt_T : P n j < T := by
      simpa [K] using dyadicPartition_lt_time_of_lt_boundIndex n hjBoundT
    have hPj1_ge_T : T ≤ P n (j + 1) := by
      simpa [K, hj] using le_partitionBoundIndex_time P n T
    have htruncate_t :
        partitionQuadraticCovariationSum P F G t n =
          Finset.sum (Finset.range (j + 1)) termt := by
      rw [partitionQuadraticCovariationSum]
      have hsplit :
          Finset.sum (Finset.range N) termt =
            Finset.sum (Finset.range (j + 1)) termt +
              Finset.sum (Finset.Ico (j + 1) N) termt := by
        symm
        exact Finset.sum_range_add_sum_Ico termt (Nat.succ_le_of_lt hjBoundt)
      have htail :
          Finset.sum (Finset.Ico (j + 1) N) termt = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        have hk_ge : j + 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hPk_ge_T : T ≤ P n k := by
          exact le_trans hPj1_ge_T
            ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone hk_ge)
        have hk_lt_N : k < N := (Finset.mem_Ico.mp hk).2
        have hPk_lt_t : P n k < t := by
          simpa [N] using dyadicPartition_lt_time_of_lt_boundIndex n hk_lt_N
        have hnext_ge_T : T ≤ partitionNextPointUpTo P n k t := by
          rw [partitionNextPointUpTo]
          exact le_min
            (le_trans hPk_ge_T
              ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n).monotone
              (Nat.le_succ k)))
            hTt
        have hleft : G (P n k) = G T := hGconst _ hPk_ge_T
        have hright : G (partitionNextPointUpTo P n k t) = G T := hGconst _ hnext_ge_T
        -- Proof comment: after the boundary cell, every right increment starts and ends in the
        -- frozen region, so those tail terms vanish.
        simp [termt, hleft, hright]
      rw [hsplit, htail, add_zero]
    have hprefix :
        Finset.sum (Finset.range j) termt =
          Finset.sum (Finset.range j) termT := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk_lt_j : k < j := Finset.mem_range.mp hk
      have hk1_lt_K : k + 1 < K := by
        rw [hj]
        exact Nat.succ_lt_succ hk_lt_j
      have hk1_lt_T : P n (k + 1) < T := by
        simpa [K] using dyadicPartition_lt_time_of_lt_boundIndex n hk1_lt_K
      have hnext_t :
          partitionNextPointUpTo P n k t = P n (k + 1) := by
        rw [partitionNextPointUpTo, min_eq_left (le_of_lt (lt_of_lt_of_le hk1_lt_T hTt))]
      have hnext_T :
          partitionNextPointUpTo P n k T = P n (k + 1) := by
        rw [partitionNextPointUpTo, min_eq_left (le_of_lt hk1_lt_T)]
      -- Proof comment: strictly before the boundary cell, both truncation horizons use the same
      -- dyadic successor.
      simp [termt, termT, hnext_t, hnext_T]
    have htermT_last :
        termT j =
          (F T - F (dyadicSquareVariationBoundaryPoint T n)) *
            (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
      have hnext_T :
          partitionNextPointUpTo P n j T = T := by
        rw [partitionNextPointUpTo, min_eq_right hPj1_ge_T]
      have hboundary :
          dyadicSquareVariationBoundaryPoint T n = P n j := by
        simp [dyadicSquareVariationBoundaryPoint, P, K, hj]
      -- Proof comment: the last horizon-`T` cell ends exactly at `T`, with left endpoint the
      -- dyadic predecessor of `T`.
      simp [termT, hnext_T, hboundary]
    have htermt_last :
        termt j =
          (F (partitionNextPointUpTo P n j t) - F (dyadicSquareVariationBoundaryPoint T n)) *
            (G T - G (dyadicSquareVariationBoundaryPoint T n)) := by
      have hnext_ge_T : T ≤ partitionNextPointUpTo P n j t := by
        rw [partitionNextPointUpTo]
        exact le_min
          hPj1_ge_T
          hTt
      have hboundary :
          dyadicSquareVariationBoundaryPoint T n = P n j := by
        simp [dyadicSquareVariationBoundaryPoint, P, K, hj]
      have hfreeze :
          G (partitionNextPointUpTo P n j t) = G T := hGconst _ hnext_ge_T
      -- Proof comment: on the unique boundary cell, only the right increment freezes to the
      -- terminal value `G T`.
      simp [termt, hfreeze, hboundary]
    have hsumT :
        partitionQuadraticCovariationSum P F G T n =
          Finset.sum (Finset.range j) termT + termT j := by
      simp [partitionQuadraticCovariationSum, K, hj, termT, Finset.sum_range_succ]
    have hsumt :
        partitionQuadraticCovariationSum P F G t n =
          Finset.sum (Finset.range j) termt + termt j := by
      rw [htruncate_t, Finset.sum_range_succ]
    -- Proof comment: after canceling the common prefix, the difference is exactly the boundary
    -- mixed increment over the dyadic predecessor of `T`.
    calc
      partitionQuadraticCovariationSum P F G t n
          = Finset.sum (Finset.range j) termT + termt j := by
              rw [hsumt, hprefix]
      _ = partitionQuadraticCovariationSum P F G T n - termT j + termt j := by
            rw [hsumT]
            ring
      _ = partitionQuadraticCovariationSum P F G T n +
            ((F (partitionNextPointUpTo P n j t) - F T) *
                (G T - G (dyadicSquareVariationBoundaryPoint T n))) := by
            rw [htermT_last, htermt_last]
            ring
      _ = partitionQuadraticCovariationSum P F G T n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n))) := by
            simp [P, K, hj]

/-- Helper for Theorem 25.22: when `T < t`, the clipped successor of the dyadic predecessor cell
for `T` at horizon `t` still converges back to `T`. -/
private theorem tendsto_boundarySuccessor_of_lt
    (t T : NNReal)
    (hTt : T < t) :
    Tendsto
      (fun n ↦
        partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)
          t)
      atTop
      (𝓝 T) := by
  let P := Definition2158.dyadicPartitionSequence
  let pred : ℕ → NNReal := fun n ↦ dyadicSquareVariationBoundaryPoint T n
  let succ : ℕ → NNReal := fun n ↦
    partitionNextPointUpTo P n (partitionBoundIndex P n T - 1) t
  have hpred : Tendsto pred atTop (𝓝 T) := tendsto_dyadicSquareVariationBoundaryPoint T
  have hmesh :
      Tendsto (fun n : ℕ ↦ partitionMesh P n) atTop (𝓝 0) :=
    Definition2158.tendsto_partitionMesh_dyadicPartitionSequence
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hεhalf : 0 < ε / 2 := by positivity
  rcases Metric.tendsto_atTop.1 hpred (ε / 2) hεhalf with ⟨N₁, hN₁⟩
  rcases
      (ENNReal.tendsto_atTop_zero.mp hmesh) (ENNReal.ofReal (ε / 2))
        (ENNReal.ofReal_pos.mpr hεhalf) with
    ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hpred_dist : dist (pred n) T < ε / 2 := hN₁ n hn₁
  have hpred_le_T : pred n ≤ T := by
    simpa [pred, dyadicSquareVariationBoundaryPoint, dyadicPartitionPredecessorPoint] using
      dyadicPartitionPredecessorPoint_le_time n T
  have hpred_lt : pred n < t := lt_of_le_of_lt hpred_le_T hTt
  have hpred_lt_bound :
      partitionBoundIndex P n T - 1 < partitionBoundIndex P n t := by
    have hpred_eq :
        pred n = P n (partitionBoundIndex P n T - 1) := by
      rfl
    have hlt :
        P n (partitionBoundIndex P n T - 1) < t := by
      simpa [hpred_eq] using hpred_lt
    exact lt_partitionBoundIndex_of_dyadicPartitionPoint_lt_time n
      (partitionBoundIndex P n T - 1) t hlt
  have hsucc_edist :
      edist (pred n) (succ n) ≤ partitionMesh P n := by
    simpa [pred, succ, P] using
      edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n
        (partitionBoundIndex P n T - 1) t hpred_lt_bound
  have hsucc_dist :
      dist (pred n) (succ n) ≤ ε / 2 := by
    have hmesh_le :
        partitionMesh P n ≤ ENNReal.ofReal (ε / 2) := hN₂ n hn₂
    have hsucc_edist' :
        edist (pred n) (succ n) ≤ ENNReal.ofReal (ε / 2) :=
      le_trans hsucc_edist hmesh_le
    exact
      (ENNReal.ofReal_le_ofReal_iff hεhalf.le).mp
        (by simpa [edist_dist] using hsucc_edist')
  -- Proof comment: the boundary predecessor already converges to `T`, and the clipped successor
  -- stays within one dyadic mesh width of that predecessor once it remains below `t`.
  calc
    dist (succ n) T ≤ dist (succ n) (pred n) + dist T (pred n) :=
      dist_triangle_right (succ n) T (pred n)
    _ < ε / 2 + ε / 2 := by
      exact add_lt_add_of_le_of_lt
        (by simpa [dist_comm] using hsucc_dist)
        (by simpa [dist_comm] using hpred_dist)
    _ = ε := by ring

/-- Helper for Theorem 25.22: if the right path is frozen after `T`, the unique boundary
increment relating the horizon-`t` and horizon-`T` dyadic mixed rows vanishes as the mesh
shrinks. -/
private theorem tendsto_boundaryMixedIncrement_zero_of_rightConstAfter
    {F G : PathSpace}
    {T t : NNReal}
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T) :
    Tendsto
      (fun n ↦
        (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
            F T) *
          (G T - G (dyadicSquareVariationBoundaryPoint T n)))
      atTop
      (𝓝 0) := by
  by_cases hEq : t = T
  · subst hEq
    -- Proof comment: at the terminal horizon itself, the boundary factor is identically zero.
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    rcases Nat.eq_zero_or_pos
        (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) with hidx | hidx
    · have hT0 : T = 0 := by
        have hle0 : T ≤ Definition2158.dyadicPartitionSequence n 0 := by
          simpa [hidx] using
            le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
        have hle0' : T ≤ 0 := by
          simpa [Definition2158.dyadicPartitionSequence] using hle0
        exact le_antisymm hle0' bot_le
      simp [dyadicSquareVariationBoundaryPoint, hidx, hT0]
    · obtain ⟨j, hj⟩ :
          ∃ j : ℕ,
            partitionBoundIndex Definition2158.dyadicPartitionSequence n T = j + 1 :=
          ⟨partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1,
            (Nat.sub_add_cancel hidx).symm⟩
      have hnext :
          partitionNextPointUpTo Definition2158.dyadicPartitionSequence n j T = T := by
        have hT_le :
            T ≤ Definition2158.dyadicPartitionSequence n (j + 1) := by
          simpa [hj] using
            le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
        rw [partitionNextPointUpTo, min_eq_right hT_le]
      simp [hj, hnext]
  · have hLt : T < t := lt_of_le_of_ne hTt (Ne.symm hEq)
    have hsucc :
        Tendsto
          (fun n ↦
            F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t))
          atTop
          (𝓝 (F T)) :=
      F.continuous.continuousAt.tendsto.comp
        (tendsto_boundarySuccessor_of_lt t T hLt)
    have hpred :
        Tendsto (fun n ↦ G (dyadicSquareVariationBoundaryPoint T n)) atTop (𝓝 (G T)) :=
      G.continuous.continuousAt.tendsto.comp
        (tendsto_dyadicSquareVariationBoundaryPoint T)
    have hleft :
        Tendsto
          (fun n ↦
            F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) - F T)
          atTop
          (𝓝 0) := by
      simpa using hsucc.sub tendsto_const_nhds
    have hright :
        Tendsto (fun n ↦ G T - G (dyadicSquareVariationBoundaryPoint T n))
          atTop
          (𝓝 0) := by
      simpa using tendsto_const_nhds.sub hpred
    -- Proof comment: both boundary endpoints converge to `T`, so each factor vanishes.
    simpa using hleft.mul hright

/-- Helper for Theorem 25.22: a pathwise quadratic-covariation witness against a path that is
constant after `T` must itself be frozen after `T`. -/
private theorem hasQuadraticCovariationAlong_eq_terminal_of_rightConstAfter
    {F G : PathSpace}
    {B : NNReal → ℝ}
    {T t : NNReal}
    (hB : HasQuadraticCovariationAlong F G B)
    (hTt : T ≤ t)
    (hGconst : ∀ s : NNReal, T ≤ s → G s = G T) :
    B t = B T := by
  have hrewrite :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            T
            n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n))))
        atTop
        (𝓝 (B T)) := by
    simpa using
      (HasQuadraticCovariationAlong.tendsto_partition_sum hB T).add
        (tendsto_boundaryMixedIncrement_zero_of_rightConstAfter
          (F := F) (G := G) hTt hGconst)
  have hEqRows :
      (fun n ↦
        partitionQuadraticCovariationSum
          Definition2158.dyadicPartitionSequence
          F
          G
          t
          n) =ᶠ[atTop]
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            T
            n +
            ((F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                  (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1) t) -
                F T) *
              (G T - G (dyadicSquareVariationBoundaryPoint T n)))) :=
    Filter.Eventually.of_forall fun n ↦
      partitionQuadraticCovariationSum_eq_terminal_plus_boundary_of_rightConstAfter
        (F := F) (G := G) hTt hGconst n
  have hLimitAtT :
      Tendsto
        (fun n ↦
          partitionQuadraticCovariationSum
            Definition2158.dyadicPartitionSequence
            F
            G
            t
            n)
        atTop
        (𝓝 (B T)) :=
    Tendsto.congr' hEqRows.symm hrewrite
  -- Proof comment: the same dyadic mixed row at horizon `t` converges both to `B t` and, after
  -- the boundary correction, to `B T`, so uniqueness of limits freezes the witness path.
  exact tendsto_nhds_unique
    (HasQuadraticCovariationAlong.tendsto_partition_sum hB t)
    hLimitAtT

/-- Helper for Theorem 25.22: a genuine quadratic-covariation process with the second coordinate
deterministically stopped at `T` has a compensator that is almost surely frozen after `T`. -/
private theorem ae_compensator_eq_terminal_of_rightStoppedCovariation
    {X A : NNReal → Ω → ℝ}
    (T : NNReal)
    (hX : IsContinuousLocalMartingale ℱ μ X)
    (hA :
      IsContinuousQuadraticCovariationProcess ℱ μ
        X
        (stoppedProcess X (fun _ ↦ (T : ENNReal)))
        A) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
  let Xstop : NNReal → Ω → ℝ := stoppedProcess X (fun _ ↦ (T : ENNReal))
  have hXstop :
      IsContinuousLocalMartingale ℱ μ Xstop := by
    -- Proof comment: deterministic stopping preserves the continuous-local-martingale structure
    -- of the second coordinate.
    exact
      { local_martingale :=
          isLocalMartingale_stoppedProcess_constTime
            (ℱ := ℱ)
            (μ := μ)
            hX.local_martingale
            hX.continuous
            T
        continuous := by
          intro ω
          exact continuous_stoppedProcess_of_continuous hX.continuous ω }
  filter_upwards
    [aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
      (μ := μ)
      (ℱ := ℱ)
      (M := X)
      (N := Xstop)
      (A := A)
      hX
      hXstop
      hA] with ω hω t hTt
  let F : PathSpace := ⟨fun s ↦ X s ω, hX.continuous ω⟩
  let G : PathSpace := ⟨fun s ↦ Xstop s ω, hXstop.continuous ω⟩
  have hGconst : ∀ s : NNReal, T ≤ s → G s = G T := by
    intro s hs
    -- Proof comment: after the deterministic stop time, the second path is literally frozen at
    -- its terminal value `X T ω`.
    calc
      G s = X T ω := by
        simp [G, Xstop, stoppedProcessConstTime_eq_min, min_eq_right hs]
      _ = G T := by
        simp [G, Xstop, stoppedProcessConstTime_eq_min]
  simpa [F, G] using
    hasQuadraticCovariationAlong_eq_terminal_of_rightConstAfter
      (F := F)
      (G := G)
      (B := fun s ↦ A s ω)
      hω
      hTt
      hGconst

/-- Helper for Theorem 25.22: once the coefficient is already cut off at `T`, the canonical
deterministic-cutoff coordinate should be frozen almost surely at every later deterministic time.
-/
private theorem constCutoffCoordinate_ae_eq_terminalValue_of_le
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T U : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hTU : T ≤ U) :
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        U =ᵐ[μ]
    continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        T := by
  let Ncut :
      NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM
      (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  let Nstop :
      NNReal → Ω → ℝ :=
    stoppedProcess Ncut (fun _ ↦ (T : ENNReal))
  let A :
      NNReal → Ω → ℝ :=
    bracketDensityIntegralUpTo hbr
      (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  have hCanonical :
      IsContinuousLocalMartingale ℱ μ Ncut ∧
        IsContinuousSquareVariationProcess ℱ μ Ncut A := by
    -- Proof comment: the Chapter 25.21 canonical global clauses already realize the cutoff
    -- coordinate as a genuine continuous local martingale with the stated bracket witness.
    simpa [Ncut, A] using
      canonicalConstCutoffGlobalClauses
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        (hbr := hbr)
        T
        hH_prog
        hH_sq
  have hStoppedMart :
      IsLocalMartingale ℱ μ Nstop := by
    -- Proof comment: deterministic stopping preserves the local-martingale clause of the
    -- canonical cutoff coordinate.
    simpa [Ncut, Nstop] using
      constCutoffCoordinate_stoppedLocalMartingale_of_constTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        T
        T
        hCanonical.1
  have hStoppedCanonical :
      IsContinuousLocalMartingale ℱ μ Nstop := by
    -- Proof comment: package the deterministic-stop local-martingale clause together with the
    -- inherited continuity of the cutoff coordinate.
    simpa [Ncut, Nstop] using
      constCutoffCoordinate_stoppedContinuousLocalMartingale_of_constTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        T
        hCanonical.1
  have hStoppedSq :
      IsContinuousSquareVariationProcess ℱ μ Nstop A := by
    have hStoppedSqRaw :
        IsContinuousSquareVariationProcess ℱ μ
          Nstop
          (stoppedProcess A (fun _ ↦ (T : ENNReal))) := by
      -- Proof comment: first stop the canonical square-variation witness at the same
      -- deterministic horizon as the coordinate.
      simpa [Ncut, Nstop, A] using
        constCutoffCoordinate_stoppedSquareVariation_of_constTime
          (μ := μ)
          (ℱ := ℱ)
          (M := M)
          (H := H)
          (hM := hM)
          (hbr := hbr)
          T
          T
          hCanonical.2
    -- Proof comment: for a deterministically cut-off coefficient, the bracket witness is already
    -- frozen after `T`, so the stopped witness is the same process.
    simpa [A, bracketDensityIntegralUpTo_constCutoff_eq_stoppedConstTime
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using
      hStoppedSqRaw
  have hEqUpTo :
      EqUpTo μ T Ncut Nstop := by
    -- Proof comment: below the cutoff horizon, the canonical coordinate and its deterministic
    -- stop are literally the same process.
    simpa [Ncut, Nstop] using
      constCutoffCoordinate_eqUpTo_stoppedConstTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        T
  have hSelfQuad :
      IsContinuousQuadraticCovariationProcess ℱ μ Ncut Ncut A := by
    -- Proof comment: on the diagonal, the square-variation witness is already the matching
    -- quadratic-covariation witness.
    exact selfContinuousQuadraticCovariation_of_squareVariation (ℱ := ℱ) (μ := μ) hCanonical.2
  have hCross :
      IsContinuousQuadraticCovariationProcess ℱ μ Ncut Nstop A := by
    rcases
        existsContinuousQuadraticCovariationProcessLocal
          (ℱ := ℱ)
          (μ := μ)
          (((ProbabilityTheory.mem_Mlocc_iff ℱ μ Ncut)).2 hCanonical.1)
          (((ProbabilityTheory.mem_Mlocc_iff ℱ μ Nstop)).2 hStoppedCanonical) with
      ⟨B, hCrossRaw⟩
    have hCanonicalEqB :
        EqUpTo μ T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          B := by
      -- Proof comment: any genuine mixed witness for `Ncut` and its deterministic stop agrees on
      -- `[0,T]` with the canonical mixed compensator for the same cutoff coefficient.
      exact
        eqUpTo_quadraticCovariationIntegralUpTo_of_isContinuousQuadraticCovariationProcess
          (μ := μ)
          (ℱ := ℱ)
          (M₁ := M)
          (M₂ := M)
          (H₁ := H)
          (H₂ := H)
          (hM₁ := hM)
          (hM₂ := hM)
          (hbr₁ := hbr)
          (hbr₂ := hbr)
          T
          (eqUpTo_rfl (μ := μ) T Ncut)
          (eqUpTo_sym hEqUpTo)
          hCanonical.1
          hStoppedCanonical
          hCanonical.2
          hStoppedSq
          hCrossRaw
    have hCanonicalEqA :
        EqUpTo μ T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          A := by
      -- Proof comment: on the diagonal, the same canonical mixed compensator identifies with the
      -- canonical square-variation witness `A`.
      exact
        eqUpTo_quadraticCovariationIntegralUpTo_of_isContinuousQuadraticCovariationProcess
          (μ := μ)
          (ℱ := ℱ)
          (M₁ := M)
          (M₂ := M)
          (H₁ := H)
          (H₂ := H)
          (hM₁ := hM)
          (hM₂ := hM)
          (hbr₁ := hbr)
          (hbr₂ := hbr)
          T
          (eqUpTo_rfl (μ := μ) T Ncut)
          (eqUpTo_rfl (μ := μ) T Ncut)
          hCanonical.1
          hCanonical.1
          hCanonical.2
          hCanonical.2
          hSelfQuad
    have hEqBAUpTo : EqUpTo μ T B A := by
      -- Proof comment: both `B` and `A` are identified on `[0,T]` with the same canonical mixed
      -- cutoff compensator, so they agree up to the cutoff horizon.
      exact eqUpTo_trans (eqUpTo_sym hCanonicalEqB) hCanonicalEqA
    have hAfreeze :
        ∀ ω : Ω, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
      intro ω t hTt
      have hAeq :
          stoppedProcess A (fun _ ↦ (T : ENNReal)) t ω = A t ω := by
        simpa [A, bracketDensityIntegralUpTo_constCutoff_eq_stoppedConstTime
          (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr) T] using rfl
      calc
        A t ω = stoppedProcess A (fun _ ↦ (T : ENNReal)) t ω := hAeq.symm
        _ = A T ω := by
          simpa [stoppedProcessConstTime_eq_min, min_eq_right hTt] using
            congrFun (stoppedProcessConstTime_eq_min (X := A) T t) ω
    have hBfreeze :
        ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → B t ω = B T ω := by
      -- Route correction: the frontier is the pathwise boundary-increment argument, not another
      -- owner-side existence bridge. Apply the generic stopped-right-coordinate freeze theorem to
      -- the genuine witness `hCrossRaw`.
      exact
        ae_compensator_eq_terminal_of_rightStoppedCovariation
          (μ := μ)
          (ℱ := ℱ)
          (X := Ncut)
          (A := B)
          T
          hCanonical.1
          hCrossRaw
    have hABall :
        ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = B t ω := by
      -- Proof comment: once both compensators are frozen after `T`, the earlier `EqUpTo` witness
      -- extends from `[0,T]` to all deterministic times.
      exact ae_eq_allTimes_of_eqUpTo_and_frozen_after
        (μ := μ)
        (T := T)
        (eqUpTo_sym hEqBAUpTo)
        hAfreeze
        hBfreeze
    -- Proof comment: transport the genuine witness `B` to the canonical frozen compensator `A`
    -- using the all-times almost-sure compensator equality.
    exact
      continuousQuadraticCovariation_of_ae_eq_allTimes_compensator
        (μ := μ)
        (ℱ := ℱ)
        hCanonical.1
        hStoppedCanonical
        hCrossRaw
        hCanonical.2.zero
        hCanonical.2.adapted
        hCanonical.2.continuous
        (locallyFiniteVariation_of_continuous_monotone
          hCanonical.2.continuous
          hCanonical.2.monotone)
        hABall
  have hZero :
      Ncut 0 =ᵐ[μ] Nstop 0 := by
    -- Proof comment: deterministic stopping never changes the time-`0` value.
    refine Filter.Eventually.of_forall ?_
    intro ω
    simp [Nstop, stoppedProcess]
  have hEqAtU :
      Ncut U =ᵐ[μ] Nstop U := by
    -- Proof comment: once the stopped process shares the same square-variation and
    -- quadratic-covariation witness as the canonical cutoff coordinate, the shared-witness
    -- comparison identifies their fixed-time values at `U`.
    exact
      ae_eq_at_time_of_sharedWitness
        (ℱ := ℱ)
        (μ := μ)
        hCanonical.1
        hStoppedCanonical
        hCanonical.2
        hStoppedSq
        hCross
        hZero
        U
  have hStoppedAtU :
      Nstop U =ᵐ[μ] Ncut T := by
    -- Proof comment: after time `T`, the deterministic stop is literally frozen at the time-`T`
    -- value of the cutoff coordinate.
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [Nstop, min_eq_right hTU] using
      congrFun (stoppedProcessConstTime_eq_min (X := Ncut) T U) ω
  -- Proof comment: compare the later cutoff value to its deterministic stop, then evaluate that
  -- stop at the clipped time `T`.
  simpa [Ncut] using hEqAtU.trans hStoppedAtU

/-- Helper for Theorem 25.22: a canonical deterministic-cutoff Itô coordinate agrees almost surely
at all times with its deterministic stop at the same cutoff horizon. -/
private theorem constCutoffCoordinate_ae_eq_stoppedConstTime_allTimes
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))))
    (hStoppedN_mart :
      IsLocalMartingale ℱ μ
        (stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal))))
    (hN_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))))
    (hStoppedN_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess
          (continuousLocalMartingaleItoIntegralProcess hM
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal)))
        (stoppedProcess
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal)))) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) t ω =
      stoppedProcess
        (continuousLocalMartingaleItoIntegralProcess hM
          (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
        (fun _ ↦ (T : ENNReal)) t ω := by
  let Ncut :
      NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM
      (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  let Nstop :
      NNReal → Ω → ℝ :=
    stoppedProcess Ncut (fun _ ↦ (T : ENNReal))
  have hMods : AreModifications μ Ncut Nstop := by
    intro U
    by_cases hUT : U ≤ T
    · rcases
        constCutoffCoordinate_eqUpTo_stoppedConstTime
          (μ := μ)
          (ℱ := ℱ)
          (M := M)
          (H := H)
          (hM := hM)
          T with
        ⟨S, _hSmeas, hSnull, hSsub⟩
      -- Proof comment: below the cutoff horizon, the earlier `EqUpTo` witness already gives the
      -- required fixed-time almost-sure identity.
      exact ae_iff.2 <| measure_mono_null (hSsub hUT) hSnull
    · have hTU : T ≤ U := le_of_not_ge hUT
      have hFreeze :
          Ncut U =ᵐ[μ] Ncut T :=
        constCutoffCoordinate_ae_eq_terminalValue_of_le
          (μ := μ)
          (ℱ := ℱ)
          (M := M)
          (H := H)
          (hM := hM)
          (hbr := hbr)
          T
          U
          hH_prog
          hH_sq
          hTU
      have hStoppedAtU :
          Nstop U =ᵐ[μ] Ncut T := by
        -- Proof comment: after time `T`, the deterministic stop is literally frozen at the time-`T`
        -- value of the same cutoff coordinate.
        refine Filter.Eventually.of_forall ?_
        intro ω
        simpa [Nstop, min_eq_right hTU] using
          congrFun (stoppedProcessConstTime_eq_min (X := Ncut) T U) ω
      -- Proof comment: the supercritical branch is exactly the missing fixed-time freeze followed
      -- by the literal deterministic-stop normalization at time `U`.
      exact hFreeze.trans hStoppedAtU.symm
  have hNstop_cont :
      ∀ ω : Ω, Continuous fun t : NNReal ↦ Nstop t ω := by
    -- Proof comment: deterministic stopping preserves pathwise continuity of the canonical cutoff
    -- coordinate.
    simpa [Nstop] using continuous_stoppedProcess_of_continuous hN_mart.continuous
  -- Proof comment: once the timewise modification relation is available, continuity upgrades it
  -- to one null set controlling all deterministic times simultaneously.
  simpa [Ncut, Nstop] using
    ae_all_eq_of_modifications_of_continuous
      (μ := μ)
      hMods
      hN_mart.continuous
      hNstop_cont

/-- Helper for Theorem 25.22: once the canonical cutoff coordinate is frozen after `T`, any
owner of the same cutoff integrand inherits the same all-times stopped-process identity by
transport along the owner/canonical modification relation. -/
private theorem constCutoffOwner_ae_eq_stoppedConstTime_allTimes
    {M H N : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hOwner :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N)
    (hN_mart : IsContinuousLocalMartingale ℱ μ N) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal,
      N t ω = stoppedProcess N (fun _ ↦ (T : ENNReal)) t ω := by
  let Ncut :
      NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM
      (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
  have hCanonical :
      IsContinuousLocalMartingale ℱ μ Ncut ∧
        IsContinuousSquareVariationProcess ℱ μ
          Ncut
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal))) :=
    canonicalConstCutoffGlobalClauses
      (μ := μ) (ℱ := ℱ) (M := M) (H := H) (hM := hM) (hbr := hbr)
      T hH_prog hH_sq
  have hMods : AreModifications μ N Ncut := by
    intro t
    exact
      ProbabilityTheory.areModifications_of_areIndistinguishable
        μ
        N
        Ncut
        hOwner.indistinguishable_canonical
        t
  have hEqCanonAll :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, N t ω = Ncut t ω := by
    -- Proof comment: continuity upgrades the owner/canonical fixed-time modification relation to
    -- one null set controlling all deterministic times.
    simpa [Ncut] using
      ae_all_eq_of_modifications_of_continuous
        (μ := μ)
        hMods
        hN_mart.continuous
        hCanonical.1.continuous
  have hStoppedCanonicalMart :
      IsLocalMartingale ℱ μ
        (stoppedProcess Ncut (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: deterministic stopping preserves the local-martingale clause of the
    -- canonical cutoff coordinate.
    simpa [Ncut] using
      constCutoffCoordinate_stoppedLocalMartingale_of_constTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        T
        T
        hCanonical.1
  have hStoppedCanonicalSq :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess Ncut (fun _ ↦ (T : ENNReal)))
        (stoppedProcess
          (bracketDensityIntegralUpTo hbr
            (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: the canonical square-variation witness stops compatibly at the same
    -- deterministic horizon.
    simpa [Ncut] using
      constCutoffCoordinate_stoppedSquareVariation_of_constTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        (hbr := hbr)
        T
        T
        hCanonical.2
  have hCanonicalFreezeAll :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        Ncut t ω = stoppedProcess Ncut (fun _ ↦ (T : ENNReal)) t ω := by
    -- Proof comment: the canonical all-times freeze is now the primary theorem, so the owner
    -- identity is only its transport along the owner/canonical equality.
    simpa [Ncut] using
      constCutoffCoordinate_ae_eq_stoppedConstTime_allTimes
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := H)
        (hM := hM)
        (hbr := hbr)
        T
        hH_prog
        hH_sq
        hCanonical.1
        hStoppedCanonicalMart
        hCanonical.2
        hStoppedCanonicalSq
  filter_upwards [hEqCanonAll, hCanonicalFreezeAll] with ω hωCanon hωFreeze t
  have hStoppedEq :
      stoppedProcess Ncut (fun _ ↦ (T : ENNReal)) t ω =
        stoppedProcess N (fun _ ↦ (T : ENNReal)) t ω := by
    -- Proof comment: both deterministic stops evaluate at the same clipped time, where the
    -- owner and canonical coordinate already agree on the common full-measure event.
    simpa [stoppedProcess] using
      (hωCanon ((min (t : ENNReal) ((fun _ ↦ (T : ENNReal)) ω)).untopA)).symm
  calc
    N t ω = Ncut t ω := hωCanon t
    _ = stoppedProcess Ncut (fun _ ↦ (T : ENNReal)) t ω := hωFreeze t
    _ = stoppedProcess N (fun _ ↦ (T : ENNReal)) t ω := hStoppedEq

/-- Helper for Theorem 25.22: the actual source-facing content is now only to choose the
canonical cutoff owner and reuse the direct canonical fixed-time freeze. -/
private theorem constCutoffSourceOwner_exists_freeze_of_le
    {M H : NNReal → Ω → ℝ}
    {hM : IsContinuousLocalMartingale ℱ μ M}
    {hbr : HasAbsolutelyContinuousSquareVariation M hM}
    (T U : NNReal)
    (hH_prog : ProgMeasurable ℱ H)
    (hH_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hTU : T ≤ U) :
    ∃ N : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)) N ∧
        N U =ᵐ[μ] N T := by
  refine
    ⟨continuousLocalMartingaleItoIntegralProcess hM
        (processBeforeStoppingTime H fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ)
        (ℱ := ℱ)
        (M := M)
        (H := processBeforeStoppingTime H fun _ ↦ (T : ENNReal))
        (hM := hM)
        (hbr := hbr),
      ?_⟩
  -- Proof comment: after the cycle is removed, the source-side existence theorem is just the
  -- canonical cutoff owner together with the direct fixed-time freeze.
  exact
    constCutoffCoordinate_ae_eq_terminalValue_of_le
      (μ := μ)
      (ℱ := ℱ)
      (M := M)
      (H := H)
      (hM := hM)
      (hbr := hbr)
      T
      U
      hH_prog
      hH_sq
      hTU

/-- Helper for Theorem 25.22: if the right coordinate is almost surely frozen after `T`, then any
genuine quadratic-covariation compensator for the pair is also almost surely frozen after `T`. -/
private theorem ae_compensator_eq_terminal_of_rightConstAfter
    {M N A : NNReal → Ω → ℝ}
    (T : NNReal)
    (hM : IsContinuousLocalMartingale ℱ μ M)
    (hN : IsContinuousLocalMartingale ℱ μ N)
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ M N A)
    (hNconst :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → N t ω = N T ω) :
    ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
  filter_upwards
    [aeHasQuadraticCovariationAlong_of_continuousQuadraticCovariationProcessLocal
      (μ := μ)
      (ℱ := ℱ)
      hM
      hN
      hA, hNconst] with ω hωA hωN t hTt
  let F : PathSpace := ⟨fun s ↦ M s ω, hM.continuous ω⟩
  let G : PathSpace := ⟨fun s ↦ N s ω, hN.continuous ω⟩
  have hGconst : ∀ s : NNReal, T ≤ s → G s = G T := by
    intro s hs
    exact hωN s hs
  -- Proof comment: the pathwise right-constant-after-`T` theorem freezes the compensator sample
  -- path at the same deterministic horizon.
  simpa [F, G] using
    hasQuadraticCovariationAlong_eq_terminal_of_rightConstAfter
      (F := F)
      (G := G)
      (B := fun s ↦ A s ω)
      hωA
      hTt
      hGconst

/-- Helper for Theorem 25.22: once one genuine compensator is `EqUpTo μ T` to `0` and frozen
after `T`, the zero quadratic-covariation witness extends to every later horizon `U ≥ T`. -/
private theorem zeroUpTo_of_compensatorEqUpTo_zero_and_frozen_after
    {N₁ N₂ A : NNReal → Ω → ℝ}
    {T U : NNReal}
    (hTU : T ≤ U)
    (hQuad : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A)
    (hEqZero : EqUpTo μ T A 0)
    (hAfreeze :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → A t ω = A T ω) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ U N₁ N₂ 0 := by
  have hEqAllZero :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, A t ω = 0 := by
    have hZeroAll :
        ∀ᵐ ω ∂μ, ∀ t : NNReal, (0 : ℝ) = A t ω := by
      -- Proof comment: compare the zero process and `A` on `[0,T]`, then use that both are
      -- frozen after `T`.
      exact
        ae_eq_allTimes_of_eqUpTo_and_frozen_after
          (μ := μ)
          (T := T)
          (eqUpTo_sym hEqZero)
          (fun _ _ _ ↦ rfl)
          hAfreeze
    filter_upwards [hZeroAll] with ω hω t
    exact (hω t).symm
  rcases ae_exists_nullSet_forall (μ := μ) hEqAllZero with
    ⟨S, hSmeas, hSnull, hSzero⟩
  have hEqZeroU : EqUpTo μ U A 0 := by
    refine ⟨S, hSmeas, hSnull, ?_⟩
    intro t ht ω hneq
    -- Proof comment: one null set controls all deterministic times, so it certainly controls the
    -- smaller family `t ≤ U`.
    by_contra hωS
    exact hneq (hSzero hωS t)
  have hQuadUpToA :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ U N₁ N₂ A := by
    -- Proof comment: package the genuine witness `hQuad` on the larger horizon `[0,U]` before
    -- changing only the compensator coordinate.
    exact
      isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
        (μ := μ)
        (ℱ := ℱ)
        (T := U)
        hQuad
  -- Proof comment: package the genuine witness on `[0,U]` and transport only the compensator
  -- coordinate from `A` to `0`.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (μ := μ)
      (ℱ := ℱ)
      (eqUpTo_rfl (μ := μ) U N₁)
      (eqUpTo_rfl (μ := μ) U N₂)
      (eqUpTo_sym hEqZeroU)
      hQuadUpToA

/-- Helper for Theorem 25.22: the real remaining independence frontier is the fixed deterministic
stop martingale theorem for the canonical cutoff product. -/
private theorem constCutoffCanonicalZeroUpTo_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T U : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ U
      (continuousLocalMartingaleItoIntegralProcess hM₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
      (continuousLocalMartingaleItoIntegralProcess hM₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      0 := by
  -- Route correction: the independence frontier is the canonical zero `...UpTo` theorem for the
  -- deterministic-cutoff pair, not another stopped-product reconstruction.
  -- Proof comment: once this finite-horizon zero witness is supplied, the stopped-product
  -- martingale, pathwise zero-covariation, and compensator-zero transport statements become
  -- downstream wrappers.
  let N₁c :
      NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c :
      NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  have hStoppedN₂_mart :
      IsLocalMartingale ℱ μ
        (stoppedProcess N₂c (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: deterministic stopping preserves the local-martingale clause of the second
    -- canonical cutoff coordinate.
    simpa [N₂c] using
      constCutoffCoordinate_stoppedLocalMartingale_of_constTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M₂)
        (H := H₂)
        (hM := hM₂)
        T
        T
        hN₂_mart
  have hStoppedN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (stoppedProcess N₂c (fun _ ↦ (T : ENNReal)))
        (stoppedProcess
          (bracketDensityIntegralUpTo hbr₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (fun _ ↦ (T : ENNReal))) := by
    -- Proof comment: the canonical square-variation witness stops compatibly with the same
    -- deterministic horizon.
    simpa [N₂c] using
      constCutoffCoordinate_stoppedSquareVariation_of_constTime
        (μ := μ)
        (ℱ := ℱ)
        (M := M₂)
        (H := H₂)
        (hM := hM₂)
        (hbr := hbr₂)
        T
        T
        hN₂_sq
  have hFreezeN₂all :
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        N₂c t ω = stoppedProcess N₂c (fun _ ↦ (T : ENNReal)) t ω := by
    -- Proof comment: the second canonical cutoff coordinate agrees almost surely at all times
    -- with its deterministic stop at the same cutoff horizon.
    simpa [N₂c] using
      constCutoffCoordinate_ae_eq_stoppedConstTime_allTimes
        (μ := μ)
        (ℱ := ℱ)
        (M := M₂)
        (H := H₂)
        (hM := hM₂)
        (hbr := hbr₂)
        T
        hH₂_prog
        hH₂_sq
        hN₂_mart
        hStoppedN₂_mart
        hN₂_sq
        hStoppedN₂_sq
  have hFreezeN₂ :
      ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → N₂c t ω = N₂c T ω := by
    filter_upwards [hFreezeN₂all] with ω hω t hTt
    calc
      N₂c t ω = stoppedProcess N₂c (fun _ ↦ (T : ENNReal)) t ω := hω t
      _ = N₂c T ω := by
        simpa [stoppedProcessConstTime_eq_min, min_eq_right hTt] using
          congrFun (stoppedProcessConstTime_eq_min (X := N₂c) T t) ω
  have hZeroDyadic :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                  (fun s ↦
                    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  t
                  n)
              atTop
              (𝓝 (0 : ℝ)) := by
    -- TODO: derive the canonical cutoff zero-dyadic convergence directly from `hIndep`. The
    -- remaining blocker is exactly this earlier bridge from source-path independence to one fixed
    -- null set on which the weighted cutoff dyadic rows vanish for every `t ≤ T`.
    sorry
  by_cases hUT : U ≤ T
  · -- Proof comment: on the subhorizon branch, the previously proved zero-dyadic packaging
    -- theorem already gives the required `...UpTo` zero witness.
    exact
      constCutoffZeroUpTo_of_zeroDyadic_of_le
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁)
        (M₂ := M₂)
        (H₁ := H₁)
        (H₂ := H₂)
        (hM₁ := hM₁)
        (hM₂ := hM₂)
        (hbr₁ := hbr₁)
        (hbr₂ := hbr₂)
        T
        U
        hUT
        hN₁_mart
        hN₂_mart
        hN₁_sq
        hN₂_sq
        hZeroDyadic
  · have hTU : T ≤ U := le_of_not_ge hUT
    rcases
        constCutoffZeroCompensatorCore_of_zeroDyadic
          (μ := μ)
          (ℱ := ℱ)
          (M₁ := M₁)
          (M₂ := M₂)
          (H₁ := H₁)
          (H₂ := H₂)
          (hM₁ := hM₁)
          (hM₂ := hM₂)
          (hbr₁ := hbr₁)
          (hbr₂ := hbr₂)
          T
          hN₁_mart
          hN₂_mart
          hN₁_sq
          hN₂_sq
          hZeroDyadic with
      ⟨A, hA, hEqZero⟩
    have hAfreeze :
        ∀ᵐ ω ∂μ, ∀ t : NNReal, T ≤ t → A t ω = A T ω := by
      -- Proof comment: after time `T`, the second canonical cutoff coordinate is already frozen,
      -- so the generic right-constant-after-`T` theorem freezes every genuine compensator `A`.
      exact
        ae_compensator_eq_terminal_of_rightConstAfter
          (μ := μ)
          (ℱ := ℱ)
          (M := N₁c)
          (N := N₂c)
          (A := A)
          T
          hN₁_mart
          hN₂_mart
          hA
          hFreezeN₂
    -- Proof comment: once the compensator is already `EqUpTo μ T` to `0` and frozen after `T`,
    -- the zero witness extends from the cutoff horizon to the larger horizon `U`.
    exact
      zeroUpTo_of_compensatorEqUpTo_zero_and_frozen_after
        (μ := μ)
        (ℱ := ℱ)
        hTU
        hA
        hEqZero
        hAfreeze

/-- Helper for Theorem 25.22: the real remaining independence frontier is the fixed deterministic
stop martingale theorem for the canonical cutoff product. -/
private theorem constStoppedCutoffProduct_martingale_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T U : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    Martingale
      (stoppedProcess
        (fun t ω ↦
          continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω)
        (fun _ ↦ (U : ENNReal))) ℱ μ := by
  -- Route correction: the stopped-product martingale is no longer primitive. Once the canonical
  -- zero `...UpTo` witness is available at horizon `U`, the deterministic-stop martingale theorem
  -- is the standard wrapper `constCutoffStoppedProduct_martingale_of_zeroUpTo`.
  exact
    constCutoffStoppedProduct_martingale_of_zeroUpTo
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂)
      T U hN₁_mart hN₂_mart
      (constCutoffCanonicalZeroUpTo_of_indepFun
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T U hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep)

/-- Helper for Theorem 25.22: the remaining finite-horizon independence input is that the
deterministically stopped product of the two canonical cutoff coordinates is a local martingale. -/
private theorem constCutoffStoppedProductLocalMartingale_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T U : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    IsLocalMartingale ℱ μ
      (stoppedProcess
        (fun t ω ↦
          continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) t ω *
          continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) t ω)
        (fun _ ↦ (U : ENNReal))) := by
  -- Route correction: the circular dependency on the dyadic-zero theorem is removed. Once the
  -- fixed-horizon stopped-product theorem is available, the local-martingale clause is immediate.
  exact
    martingale_isLocalMartingale
      (constStoppedCutoffProduct_martingale_of_indepFun
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂)
        (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂)
        (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T U hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep)

/-- Helper for Theorem 25.22: source-path independence gives zero quadratic covariation up to
every integer horizon for the canonical deterministic-cutoff pair. -/
private theorem constCutoffZeroUpToNat_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    ∀ n : ℕ,
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ (n : NNReal)
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        0 := by
  intro n
  -- Proof comment: the primitive independence theorem is the canonical zero `...UpTo` statement,
  -- so the integer-horizon clause is a direct specialization.
  exact
    constCutoffCanonicalZeroUpTo_of_indepFun
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T (n : NNReal) hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep

/-- Helper for Theorem 25.22: source-path independence yields almost-sure pathwise zero
quadratic covariation for the canonical deterministic-cutoff pair. -/
private theorem constCutoffAeZeroCanonicalPath_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    ∀ᵐ ω ∂μ,
      HasQuadraticCovariationAlong
        (⟨fun s ↦
            continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) s ω,
          hN₁_mart.continuous ω⟩ : C(NNReal, ℝ))
        (⟨fun s ↦
            continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) s ω,
          hN₂_mart.continuous ω⟩ : C(NNReal, ℝ))
        0 := by
  let N₁c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₁
      (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
  let N₂c : NNReal → Ω → ℝ :=
    continuousLocalMartingaleItoIntegralProcess hM₂
      (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
  -- Proof comment: globalize the finite-horizon zero witnesses for the canonical cutoff pair to
  -- one almost-sure pathwise zero statement.
  simpa [N₁c, N₂c] using
    aeHasQuadraticCovariationAlong_zero_of_upToNat
      (μ := μ)
      (ℱ := ℱ)
      (N₁ := N₁c)
      (N₂ := N₂c)
      hN₁_mart
      hN₂_mart
      (constCutoffZeroUpToNat_of_indepFun
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T
        hH₁_prog
        hH₂_prog
        hH₁_sq
        hH₂_sq
        hN₁_mart
        hN₂_mart
        hN₁_sq
        hN₂_sq
        hIndep)

-- Route correction: the real open frontier is the direct independence-to-zero dyadic theorem.
-- The compensator packaging and downstream `EqUpTo` transport are now isolated in
-- `constCutoffZeroCompensatorCore_of_zeroDyadic`.
private theorem constCutoffZeroDyadicTendsto_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
      ∀ ⦃ω : Ω⦄, ω ∉ S →
        ∀ ⦃t : NNReal⦄, t ≤ T →
          Tendsto
            (fun n ↦
              Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦
                  processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                    processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                t
                n)
            atTop
            (𝓝 (0 : ℝ)) := by
  -- Proof comment: after moving the independence frontier upstream to the stopped-product
  -- martingale theorem, this dyadic-zero theorem is again just the downstream canonical-path
  -- wrapper.
  exact
    constCutoffZeroDyadicTendsto_of_aeZeroCanonicalPath
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T
      hN₁_mart
      hN₂_mart
      hN₁_sq
      hN₂_sq
      (constCutoffAeZeroCanonicalPath_of_indepFun
        (μ := μ)
        (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂)
        (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂)
        (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T
        hH₁_prog
        hH₂_prog
        hH₁_sq
        hH₂_sq
        hN₁_mart
        hN₂_mart
        hN₁_sq
        hN₂_sq
        hIndep)

/-- Helper for Theorem 25.22: under source-path independence, the canonical deterministic-cutoff
pair should admit one genuine quadratic-covariation compensator that is already `EqUpTo μ T` to
`0`. -/
private theorem constCutoffZeroCompensatorCore_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    ∃ A : NNReal → Ω → ℝ,
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A ∧
      EqUpTo μ T A 0 := by
  have hZeroDyadic :
      ∃ S : Set Ω, MeasurableSet S ∧ μ S = 0 ∧
        ∀ ⦃ω : Ω⦄, ω ∉ S →
          ∀ ⦃t : NNReal⦄, t ≤ T →
            Tendsto
              (fun n ↦
                Theorem25_22.dyadicQuadraticCovariationIntegralApproximationUpTo
                  (fun s ↦
                    processBeforeStoppingTime H₁ (fun _ ↦ (T : ENNReal)) s ω *
                      processBeforeStoppingTime H₂ (fun _ ↦ (T : ENNReal)) s ω)
                  (⟨fun s ↦ M₁ s ω, hM₁.continuous ω⟩ : C(NNReal, ℝ))
                  (⟨fun s ↦ M₂ s ω, hM₂.continuous ω⟩ : C(NNReal, ℝ))
                  t
                  n)
              atTop
              (𝓝 (0 : ℝ)) :=
    constCutoffZeroDyadicTendsto_of_indepFun
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep
  -- Proof comment: the remaining independence input is now exactly the direct dyadic-zero theorem;
  -- once that is supplied, the compensator packaging is already complete.
  exact
    constCutoffZeroCompensatorCore_of_zeroDyadic
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hZeroDyadic

/-- Helper for Theorem 25.22: any genuine compensator of the canonical cutoff pair is `EqUpTo μ T`
to `0` once source-path independence gives the canonical pair almost-sure pathwise zero quadratic
covariation. -/
private theorem constCutoffOwnerCompensator_eqUpTo_zero_of_indepFun
    {M₁ M₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA :
      IsContinuousQuadraticCovariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A)
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    EqUpTo μ T A 0 := by
  rcases
      constCutoffZeroCompensatorCore_of_indepFun
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep with
    ⟨A₀, hA₀, hA₀Zero⟩
  have hEqCanonical :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A :=
    constCutoffCanonicalCompensator_eqUpTo
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (A := A)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA
  have hEqCanonical₀ :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A₀ :=
    constCutoffCanonicalCompensator_eqUpTo
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := H₁) (H₂ := H₂)
      (A := A₀)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA₀
  -- Proof comment: once one genuine compensator is already known to be `EqUpTo μ T` to `0`,
  -- every other genuine compensator agrees with it through the same canonical mixed integral.
  exact
    eqUpTo_trans
      (eqUpTo_trans (eqUpTo_sym hEqCanonical) hEqCanonical₀)
      hA₀Zero

/-- Helper for Theorem 25.22: the correct independence frontier is the canonical cutoff
compensator itself, not a stopped-product martingale reconstruction. -/
private theorem constCutoffCanonicalZeroEqUpTo_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
  0 := by
  rcases
      constCutoffZeroCompensatorCore_of_indepFun
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep with
    ⟨A, hA, hEqAZero⟩
  have hEqCanonical :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A :=
    constCutoffCanonicalCompensator_eqUpTo
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂) (A := A)
      (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA
  -- Proof comment: the direct compensator core already packages one genuine witness `A` that is
  -- `EqUpTo μ T` to `0`, so the canonical mixed integral reaches `0` by one comparison step.
  exact eqUpTo_trans hEqCanonical hEqAZero

/-- Helper for Theorem 25.22: source-path independence should force the canonical cutoff mixed
pair to have zero quadratic covariation on `[0,T]`. -/
theorem constCutoffZeroQuadraticCovariationProcess_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
      (continuousLocalMartingaleItoIntegralProcess hM₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
      (continuousLocalMartingaleItoIntegralProcess hM₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      0 := by
  exact
    constCutoffCanonicalZeroUpTo_of_indepFun
      (μ := μ)
      (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T T hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep

/-- Helper for Theorem 25.22: source-path independence should force the canonical cutoff mixed
quadratic-covariation integral to agree with `0` on `[0,T]`. -/
theorem constCutoffZeroQuadraticCovariationEqUpTo_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      0 := by
  -- Proof comment: after the route correction, this theorem is exactly the canonical cutoff
  -- zero-compensator statement.
  exact
    constCutoffCanonicalZeroEqUpTo_of_indepFun
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep

/-- Helper for Theorem 25.22: source-path independence should force the canonical cutoff mixed
quadratic-covariation integral to vanish on `[0,T]`. -/
theorem quadraticCovariationIntegralUpTo_eqUpTo_zero_of_indepFun
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_mart :
      IsContinuousLocalMartingale ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hIndep :
      IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      0 := by
  -- Proof comment: after isolating the independence work at the theorem boundary, the public zero
  -- statement is exactly that direct canonical-cutoff `EqUpTo ... 0` theorem.
  exact
    constCutoffZeroQuadraticCovariationEqUpTo_of_indepFun
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq hN₁_mart hN₂_mart hN₁_sq hN₂_sq hIndep

/-- Helper for Theorem 25.22: a genuine mixed compensator with explicit martingale data agrees on
`[0,T]` with the canonical dyadic quadratic-covariation integral for the stopped coefficients,
provided the two integral coordinates are already tied to their canonical cutoff realizations. -/
theorem eqUpTo_quadraticCovariationIntegralUpTo_of_continuousQuadraticCovariationProcessLocal
    {M₁ M₂ N₁ N₂ H₁ H₂ A : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ N₁
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ N₂
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))))
    (hA : IsContinuousQuadraticCovariationProcess ℱ μ N₁ N₂ A) :
    EqUpTo μ T
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
      A := by
  -- Proof comment: after the statement correction, the local theorem is just the explicit-
  -- martingale version of the genuine compensator identification theorem.
  have hCore :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A :=
    eqUpTo_quadraticCovariationIntegralUpTo_of_isContinuousQuadraticCovariationProcess
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂) (H₁ := H₁) (H₂ := H₂)
      (A := A) T hEq₁ hEq₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA
  exact hCore

/-- Helper for Theorem 25.22: if a genuine compensator agrees on `[0,T]` with a canonical mixed
bracket formula and that canonical formula agrees with `0`, then the compensator also agrees with
`0` on `[0,T]`. -/
theorem eqUpTo_zero_of_compensatorEqCanonical
    {A B : NNReal → Ω → ℝ}
    {T : NNReal}
    (hEqCanonical : EqUpTo μ T B A)
    (hZeroCanonical : EqUpTo μ T B 0) :
    EqUpTo μ T A 0 := by
  -- Proof comment: compare `A` with the canonical intermediary `B`, then compose with the
  -- canonical zero comparison.
  exact eqUpTo_trans (eqUpTo_sym hEqCanonical) hZeroCanonical

/-- Helper for Theorem 25.22: an `EqUpTo μ T` witness identifying a mixed compensator with `0`
transports any existing `...UpTo` quadratic-covariation witness to the zero compensator. -/
theorem zeroQuadraticCovariationUpTo_of_eqUpToZeroWitness
    {N₁ N₂ A : NNReal → Ω → ℝ}
    {T : NNReal}
    (hQuad : IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ A)
    (hZero : EqUpTo μ T A 0) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0 := by
  -- Proof comment: keep the same genuine quadratic-covariation witness and transport only the
  -- compensator coordinate from `A` to `0`.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (μ := μ) (ℱ := ℱ)
      (eqUpTo_rfl (μ := μ) T N₁)
      (eqUpTo_rfl (μ := μ) T N₂)
      (eqUpTo_sym hZero)
      hQuad

/-- Helper for Theorem 25.22: the remaining mixed-cutoff input is the existence of one owner
pair carrying the genuine finite-horizon quadratic-covariation clauses for the deterministically
truncated integrands, derived directly from the source-side progressive measurability and
finite-horizon bracket-density integrability of `H₁` and `H₂`. -/
theorem constCutoffQuadraticCovariationClauses_of_singleClauses
    {M₁ M₂ H₁ H₂ N₁ N₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hOwner₁ :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) N₁)
    (hOwner₂ :
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) N₂)
    (hN₁_mart : IsContinuousLocalMartingale ℱ μ N₁)
    (hN₂_mart : IsContinuousLocalMartingale ℱ μ N₂)
    (hN₁_sq :
      IsContinuousSquareVariationProcess ℱ μ N₁
        (bracketDensityIntegralUpTo hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))))
    (hN₂_sq :
      IsContinuousSquareVariationProcess ℱ μ N₂
        (bracketDensityIntegralUpTo hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        N₁ N₂
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        N₂ N₁
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
  -- Route correction: after the single-cutoff owners are global, the remaining mixed frontier is
  -- to identify the genuine quadratic-covariation compensators with the two canonical dyadic
  -- integrals on `[0,T]`; the existence and packaging of genuine compensators is already isolated
  -- below.
  rcases
      existsQuadraticCovariationPair_of_isContinuousLocalMartingale
        (μ := μ) (ℱ := ℱ) (N₁ := N₁) (N₂ := N₂) hN₁_mart hN₂_mart with
    ⟨A₁₂, A₂₁, hA₁₂, hA₂₁⟩
  have hEq₁ :
      EqUpTo μ T
        N₁
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) :=
    eqUpTo_constCutoffOwner_canonical
      (μ := μ) (ℱ := ℱ)
      (M := M₁) (H := H₁) (N := N₁) (hM := hM₁) (hbr := hbr₁) T hOwner₁
  have hEq₂ :
      EqUpTo μ T
        N₂
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) :=
    eqUpTo_constCutoffOwner_canonical
      (μ := μ) (ℱ := ℱ)
      (M := M₂) (H := H₂) (N := N₂) (hM := hM₂) (hbr := hbr₂) T hOwner₂
  have hPackage :
      EqUpTo μ T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          A₁₂ →
        EqUpTo μ T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          A₂₁ →
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            N₁ N₂
            (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            N₂ N₁
            (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
          ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
              (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
            IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
    intro hEqLeft hEqRight hZero
    -- Proof comment: after the compensator identifications are available, the mixed clauses are
    -- pure `EqUpTo` transport from the genuine Chapter 21 covariation witnesses.
    exact
      constCutoffQuadraticCovariationClauses_of_eqUpToCompensators
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂)
        (H₁ := processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (H₂ := processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
        (N₁ := N₁) (N₂ := N₂) (A₁₂ := A₁₂) (A₂₁ := A₂₁)
        T
        (isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
          (μ := μ) (ℱ := ℱ) (T := T) hA₁₂)
        (isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
          (μ := μ) (ℱ := ℱ) (T := T) hA₂₁)
        hEqLeft hEqRight hZero
  have hEqLeft :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        A₁₂ :=
    eqUpTo_quadraticCovariationIntegralUpTo_of_continuousQuadraticCovariationProcessLocal
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (N₁ := N₁) (N₂ := N₂) (H₁ := H₁) (H₂ := H₂)
      (A := A₁₂) T hEq₁ hEq₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq hA₁₂
  have hEqRight :
      EqUpTo μ T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        A₂₁ :=
    eqUpTo_quadraticCovariationIntegralUpTo_of_continuousQuadraticCovariationProcessLocal
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₂) (M₂ := M₁) (N₁ := N₂) (N₂ := N₁) (H₁ := H₂) (H₂ := H₁)
      (A := A₂₁) T hEq₂ hEq₁ hN₂_mart hN₁_mart hN₂_sq hN₁_sq hA₂₁
  have hCanonicalZero :
      (IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        EqUpTo μ T
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          0 := by
    intro hIndep
    have hCanonical₁ :
        IsContinuousLocalMartingale ℱ μ
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) :=
      (canonicalConstCutoffGlobalClauses
        (μ := μ) (ℱ := ℱ)
        (M := M₁) (H := H₁) (hM := hM₁) (hbr := hbr₁)
        T hH₁_prog hH₁_sq).1
    have hCanonical₂ :
        IsContinuousLocalMartingale ℱ μ
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) :=
      (canonicalConstCutoffGlobalClauses
        (μ := μ) (ℱ := ℱ)
        (M := M₂) (H := H₂) (hM := hM₂) (hbr := hbr₂)
        T hH₂_prog hH₂_sq).1
    have hCanonicalSq₁ :
        IsContinuousSquareVariationProcess ℱ μ
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (bracketDensityIntegralUpTo hbr₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) :=
      (canonicalConstCutoffGlobalClauses
        (μ := μ) (ℱ := ℱ)
        (M := M₁) (H := H₁) (hM := hM₁) (hbr := hbr₁)
        T hH₁_prog hH₁_sq).2
    have hCanonicalSq₂ :
        IsContinuousSquareVariationProcess ℱ μ
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (bracketDensityIntegralUpTo hbr₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) :=
      (canonicalConstCutoffGlobalClauses
        (μ := μ) (ℱ := ℱ)
        (M := M₂) (H := H₂) (hM := hM₂) (hbr := hbr₂)
        T hH₂_prog hH₂_sq).2
    -- Proof comment: this is the higher theorem boundary where the canonical cutoff pair really
    -- has the genuine single-clause data needed by the zero-bracket theorem.
    exact
      quadraticCovariationIntegralUpTo_eqUpTo_zero_of_indepFun
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
        T hH₁_prog hH₂_prog hH₁_sq hH₂_sq
        hCanonical₁ hCanonical₂ hCanonicalSq₁ hCanonicalSq₂ hIndep
  have hZero :
      (IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0 := by
    intro hIndep
    have hEqZero :
        EqUpTo μ T A₁₂ 0 :=
      eqUpTo_zero_of_compensatorEqCanonical
        (μ := μ)
        (hEqCanonical := hEqLeft)
        (hZeroCanonical := hCanonicalZero hIndep)
    exact
      zeroQuadraticCovariationUpTo_of_eqUpToZeroWitness
        (μ := μ) (ℱ := ℱ)
        (isContinuousQuadraticCovariationProcessUpTo_of_isContinuousQuadraticCovariationProcess
          (μ := μ) (ℱ := ℱ) (T := T) hA₁₂)
        hEqZero
  exact hPackage hEqLeft hEqRight hZero

/-- Helper for Theorem 25.22: once two genuine owners carry the global cutoff single clauses, the
canonical cutoff realizations inherit the finite-horizon mixed clauses by the existing
owner-to-canonical transport. -/
theorem canonicalItoIntegral_quadraticCovariationClausesUpTo_constCutoffDirect
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          0) := by
  rcases
      existsConstCutoffOwnerWithSingleClauses
        (μ := μ) (ℱ := ℱ) (M := M₁) (H := H₁) (hM := hM₁) (hbr := hbr₁)
        T hH₁_prog hH₁_sq with
    ⟨N₁, hOwner₁, hN₁_mart, hN₁_sq⟩
  rcases
      existsConstCutoffOwnerWithSingleClauses
        (μ := μ) (ℱ := ℱ) (M := M₂) (H := H₂) (hM := hM₂) (hbr := hbr₂)
        T hH₂_prog hH₂_sq with
    ⟨N₂, hOwner₂, hN₂_mart, hN₂_sq⟩
  -- Proof comment: the mixed cutoff theorem now splits cleanly: obtain one genuine owner for
  -- each stopped integrand, prove the mixed clauses for that owner pair, and then transport them
  -- to the canonical dyadic cutoff pair.
  exact
    canonicalItoIntegral_quadraticCovariationClausesUpTo_of_owners
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂)
      (H₁ := processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
      (H₂ := processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
      (N₁ := N₁) (N₂ := N₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      (T := T)
      hOwner₁ hOwner₂
      (constCutoffQuadraticCovariationClauses_of_singleClauses
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
        (N₁ := N₁) (N₂ := N₂)
        (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T hH₁_prog hH₂_prog hH₁_sq hH₂_sq
        hOwner₁ hOwner₂ hN₁_mart hN₂_mart hN₁_sq hN₂_sq)

/-- Helper for Theorem 25.22: the remaining mixed-cutoff input is the existence of one owner
pair carrying the genuine finite-horizon quadratic-covariation clauses for the deterministically
truncated integrands, derived directly from the source-side progressive measurability and
finite-horizon bracket-density integrability of `H₁` and `H₂`. -/
theorem existsCutoffOwnerQuadraticCovariationClausesUpTo
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N₁ N₂ : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) N₁ ∧
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) N₂ ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₁ N₂
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₂ N₁
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
  -- Proof comment: once the direct canonical mixed-cutoff theorem is available, the existential
  -- owner-pair statement is only reflexive packaging.
  exact
    existsCutoffOwnerQuadraticCovariationClausesUpTo_of_canonicalCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T
      (canonicalItoIntegral_quadraticCovariationClausesUpTo_constCutoffDirect
        (μ := μ) (ℱ := ℱ)
        (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
        (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
        T hH₁_prog hH₂_prog hH₁_sq hH₂_sq)

/-- Helper for Theorem 25.22: the deterministic-cutoff mixed-input core is to show directly that
the canonical dyadic pair already satisfies the finite-horizon quadratic-covariation clauses for
the cutoff integrands. -/
theorem canonicalItoIntegral_quadraticCovariationClausesUpTo_constCutoffCore
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
        (continuousLocalMartingaleItoIntegralProcess hM₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          0) := by
  -- Proof comment: the direct canonical mixed-cutoff theorem records the actual unresolved
  -- frontier, so this named core is now just that direct theorem.
  exact
    canonicalItoIntegral_quadraticCovariationClausesUpTo_constCutoffDirect
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq

/-- Helper for Theorem 25.22: the mixed-clause frontier is the existence of one owner pair
carrying the genuine finite-horizon quadratic-covariation clauses. -/
theorem existsCutoffOwnerQuadraticCovariationClausesUpToData
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N₁ N₂ : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁
          (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)) N₁ ∧
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂
          (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)) N₂ ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₁ N₂
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₂ N₁
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
  have hCanonical :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            (continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
            (continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
            0) :=
    canonicalItoIntegral_quadraticCovariationClausesUpTo_constCutoffCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq
  -- Proof comment: once the cutoff canonical dyadic pair carries the mixed clauses, the
  -- existential owner theorem is witnessed by that pair itself via reflexive ownership.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM₁
        (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)),
      continuousLocalMartingaleItoIntegralProcess hM₂
        (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M₁)
        (H := processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
        (hM := hM₁) (hbr := hbr₁),
      canonicalSelf
        (μ := μ) (ℱ := ℱ) (M := M₂)
        (H := processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
        (hM := hM₂) (hbr := hbr₂),
      hCanonical.1, hCanonical.2.1, hCanonical.2.2⟩

/-- Helper for Theorem 25.22: the mixed-clause frontier is the existence of one owner pair
carrying the genuine finite-horizon quadratic-covariation clauses. -/
theorem canonicalItoIntegral_quadraticCovariationClausesUpToFrontier
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
      ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          0) := by
  have hCut :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
          (continuousLocalMartingaleItoIntegralProcess hM₁
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁
            (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal))
            (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal))) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            (continuousLocalMartingaleItoIntegralProcess hM₁
              (processBeforeStoppingTime H₁ fun _ ↦ (T : ENNReal)))
            (continuousLocalMartingaleItoIntegralProcess hM₂
              (processBeforeStoppingTime H₂ fun _ ↦ (T : ENNReal)))
            0) :=
    canonicalItoIntegral_quadraticCovariationClausesUpTo_constCutoffCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq
  -- Proof comment: the mixed cutoff clauses are the true finite-horizon input; once they are in
  -- place, the original coefficients follow from the established cutoff transport on all three
  -- components.
  exact
    canonicalItoIntegral_quadraticCovariationClausesUpTo_of_constCutoffs
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂) hCut

/-- Helper for Theorem 25.22: the mixed-clause frontier is the existence of one owner pair
carrying the genuine finite-horizon quadratic-covariation clauses. -/
theorem existsOwnerQuadraticCovariationClausesUpToData
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N₁ N₂ : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁ ∧
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂ ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₁ N₂ (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₂ N₁ (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
  have hCanonical :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
            (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
            0) :=
    canonicalItoIntegral_quadraticCovariationClausesUpToFrontier
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq
  -- Proof comment: once the canonical pair satisfies the mixed clauses, the existential owner
  -- theorem is witnessed by the two canonical dyadic processes themselves.
  exact
    ⟨continuousLocalMartingaleItoIntegralProcess hM₁ H₁,
      continuousLocalMartingaleItoIntegralProcess hM₂ H₂,
      canonicalSelf (μ := μ) (ℱ := ℱ) (M := M₁) (H := H₁) (hM := hM₁) (hbr := hbr₁),
      canonicalSelf (μ := μ) (ℱ := ℱ) (M := M₂) (H := H₂) (hM := hM₂) (hbr := hbr₂),
      hCanonical.1, hCanonical.2.1, hCanonical.2.2⟩

/-- Helper for Theorem 25.22: the real mixed-clause frontier is to show that the canonical dyadic
pair already carries the finite-horizon quadratic-covariation clauses. -/
theorem canonicalItoIntegral_quadraticCovariationClausesUpToCore
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
      ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          0) := by
  -- Proof comment: after removing the existential wrapper, the core theorem is exactly the
  -- canonical mixed frontier.
  exact
    canonicalItoIntegral_quadraticCovariationClausesUpToFrontier
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq

/-- Helper for Theorem 25.22: the unresolved mixed-clause witness should produce owner-level
finite-horizon quadratic-covariation clauses before the final canonical transport. -/
theorem exists_ownerQuadraticCovariationClausesUpToWitness
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    ∃ N₁ N₂ : NNReal → Ω → ℝ,
      _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁ ∧
        _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂ ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₁ N₂ (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          N₂ N₁ (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0) := by
  -- Proof comment: the core theorem now depends only on the earlier mixed witness helper, so
  -- this theorem is just its public theorem-local alias.
  exact
    existsOwnerQuadraticCovariationClausesUpToData
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq

/-- Helper for Theorem 25.22: the remaining mixed-bracket input is to compare the two canonical
dyadic realizations with a genuine quadratic-covariation owner on `[0,T]`. -/
theorem canonicalItoIntegral_quadraticCovariationClausesUpTo
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
      ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          0) := by
  -- Proof comment: the canonical mixed-clause theorem is now the direct frontier; the owner
  -- wrapper above is derived from this theorem rather than the other way around.
  exact
    canonicalItoIntegral_quadraticCovariationClausesUpToCore
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq

/-- Helper for Theorem 25.22: the remaining dyadic-to-owner comparison should supply all seven
finite-horizon clauses for the canonical dyadic Itô realizations at once. -/
theorem canonicalItoIntegral_allClausesUpTo
    {M₁ M₂ H₁ H₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ))) :
    IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (bracketDensityIntegralUpTo hbr₁ H₁) ∧
      IsContinuousLocalMartingaleUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂) ∧
      IsContinuousSquareVariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (bracketDensityIntegralUpTo hbr₂ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
        (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
        (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
      ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
          (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          0) := by
  -- Proof comment: the downstream packaging only needs the single-integral clauses and the mixed
  -- quadratic-covariation clauses separately, so combine those two focused frontiers here.
  have hSingle₁ :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (bracketDensityIntegralUpTo hbr₁ H₁) :=
    canonicalItoIntegral_singleClausesUpTo
      (μ := μ) (ℱ := ℱ) (M := M₁) (H := H₁) (hM := hM₁) (hbr := hbr₁)
      T hH₁_prog hH₁_sq
  have hSingle₂ :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (bracketDensityIntegralUpTo hbr₂ H₂) :=
    canonicalItoIntegral_singleClausesUpTo
      (μ := μ) (ℱ := ℱ) (M := M₂) (H := H₂) (hM := hM₂) (hbr := hbr₂)
      T hH₂_prog hH₂_sq
  have hQuad :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
            (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
            0) :=
    canonicalItoIntegral_quadraticCovariationClausesUpTo
      (μ := μ) (ℱ := ℱ)
      (M₁ := M₁) (M₂ := M₂) (H₁ := H₁) (H₂ := H₂)
      (hM₁ := hM₁) (hM₂ := hM₂) (hbr₁ := hbr₁) (hbr₂ := hbr₂)
      T hH₁_prog hH₂_prog hH₁_sq hH₂_sq
  exact ⟨hSingle₁.1, hSingle₁.2, hSingle₂.1, hSingle₂.2, hQuad.1, hQuad.2.1, hQuad.2.2⟩

/-- Bundle of the seven source conclusions in Theorem 25.22 on the finite horizon `[0, T]` for
two Itô-integral realizations. -/
structure PairSpecUpTo
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω)
    (T : NNReal)
    (M₁ M₂ H₁ H₂ N₁ N₂ : NNReal → Ω → ℝ)
    (hM₁ : IsContinuousLocalMartingale ℱ μ M₁)
    (hM₂ : IsContinuousLocalMartingale ℱ μ M₂)
    (hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁)
    (hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂) : Prop where
  continuousLocalMartingale_left :
    IsContinuousLocalMartingaleUpTo ℱ μ T N₁
  continuousLocalMartingale_right :
    IsContinuousLocalMartingaleUpTo ℱ μ T N₂
  squareVariation_left :
    IsContinuousSquareVariationProcessUpTo ℱ μ T N₁ (bracketDensityIntegralUpTo hbr₁ H₁)
  squareVariation_right :
    IsContinuousSquareVariationProcessUpTo ℱ μ T N₂ (bracketDensityIntegralUpTo hbr₂ H₂)
  quadraticCovariation_left_right :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂)
  quadraticCovariation_right_left :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₂ N₁
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁)
  quadraticCovariation_zero_of_indepFun :
    (IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0

/-- Theorem 25.22: source-faithful finite-horizon reformulation of the source statement for two
Itô-integral realizations on `[0, T]`. -/
theorem pair_spec
    {M₁ M₂ H₁ H₂ N₁ N₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁)
    (hN₂ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂) :
    PairSpecUpTo ℱ μ T M₁ M₂ H₁ H₂ N₁ N₂ hM₁ hM₂ hbr₁ hbr₂ := by
  -- Proof comment: transport the canonical single-integral and mixed-bracket witnesses along the
  -- indistinguishability data packaged in `hN₁` and `hN₂`.
  have hEq₁ :
      EqUpTo μ T N₁ (continuousLocalMartingaleItoIntegralProcess hM₁ H₁) :=
    eqUpTo_of_areIndistinguishable (T := T) hN₁.indistinguishable_canonical
  have hEq₂ :
      EqUpTo μ T N₂ (continuousLocalMartingaleItoIntegralProcess hM₂ H₂) :=
    eqUpTo_of_areIndistinguishable (T := T) hN₂.indistinguishable_canonical
  have hSingle₁ :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (bracketDensityIntegralUpTo hbr₁ H₁) :=
    canonicalItoIntegral_singleClausesUpTo
      (μ := μ) (ℱ := ℱ) (T := T) hH₁_prog hH₁_sq
  have hSingle₂ :
      IsContinuousLocalMartingaleUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂) ∧
        IsContinuousSquareVariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (bracketDensityIntegralUpTo hbr₂ H₂) :=
    canonicalItoIntegral_singleClausesUpTo
      (μ := μ) (ℱ := ℱ) (T := T) hH₂_prog hH₂_sq
  have hQuad :
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) ∧
        IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
          (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
          (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
          (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) ∧
        ((IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
            (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
          IsContinuousQuadraticCovariationProcessUpTo ℱ μ T
            (continuousLocalMartingaleItoIntegralProcess hM₁ H₁)
            (continuousLocalMartingaleItoIntegralProcess hM₂ H₂)
            0) :=
    canonicalItoIntegral_quadraticCovariationClausesUpTo
      (μ := μ) (ℱ := ℱ) (T := T) hH₁_prog hH₂_prog hH₁_sq hH₂_sq
  refine
    { continuousLocalMartingale_left :=
        isContinuousLocalMartingaleUpTo_of_eqUpTo hEq₁ hSingle₁.1
      continuousLocalMartingale_right :=
        isContinuousLocalMartingaleUpTo_of_eqUpTo hEq₂ hSingle₂.1
      squareVariation_left :=
        isContinuousSquareVariationProcessUpTo_of_eqUpTo hEq₁
          (eqUpTo_rfl (μ := μ) T (bracketDensityIntegralUpTo hbr₁ H₁)) hSingle₁.2
      squareVariation_right :=
        isContinuousSquareVariationProcessUpTo_of_eqUpTo hEq₂
          (eqUpTo_rfl (μ := μ) T (bracketDensityIntegralUpTo hbr₂ H₂)) hSingle₂.2
      quadraticCovariation_left_right :=
        isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo hEq₁ hEq₂
          (eqUpTo_rfl (μ := μ) T
            (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂))
          hQuad.1
      quadraticCovariation_right_left :=
        isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo hEq₂ hEq₁
          (eqUpTo_rfl (μ := μ) T
            (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁))
          hQuad.2.1
      quadraticCovariation_zero_of_indepFun :=
        fun hIndep ↦
          isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo hEq₁ hEq₂
            (eqUpTo_rfl (μ := μ) T 0)
            (hQuad.2.2 hIndep) }

/-- First source clause of the finite-horizon reformulation of Theorem 25.22 on `[0, T]`. -/
theorem continuousLocalMartingale_left
    {M₁ H₁ N₁ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁) :
    IsContinuousLocalMartingaleUpTo ℱ μ T N₁ := by
  -- Proof comment: transport the owner-level local-martingale witness for the canonical dyadic
  -- realization along the indistinguishability relation packaged in `hN₁`.
  exact
    isContinuousLocalMartingaleUpTo_of_eqUpTo
      (eqUpTo_of_areIndistinguishable (T := T) hN₁.indistinguishable_canonical)
      (canonicalItoIntegral_singleClausesUpTo
        (μ := μ) (ℱ := ℱ) (T := T) hH₁_prog hH₁_sq).1

/-- Second source clause of the finite-horizon reformulation of Theorem 25.22 on `[0, T]`. -/
theorem continuousLocalMartingale_right
    {M₂ H₂ N₂ : NNReal → Ω → ℝ}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₂ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂) :
    IsContinuousLocalMartingaleUpTo ℱ μ T N₂ := by
  -- Proof comment: the right-hand process is handled by the same transport step as the left.
  exact
    isContinuousLocalMartingaleUpTo_of_eqUpTo
      (eqUpTo_of_areIndistinguishable (T := T) hN₂.indistinguishable_canonical)
      (canonicalItoIntegral_singleClausesUpTo
        (μ := μ) (ℱ := ℱ) (T := T) hH₂_prog hH₂_sq).1

/-- Third source clause of the finite-horizon reformulation of Theorem 25.22 on `[0, T]`. -/
theorem squareVariation_left
    {M₁ H₁ N₁ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁) :
    IsContinuousSquareVariationProcessUpTo ℱ μ T N₁ (bracketDensityIntegralUpTo hbr₁ H₁) := by
  -- Proof comment: keep the canonical square-variation witness and only transport the martingale
  -- coordinate from the canonical dyadic realization to the given source-facing process.
  exact
    isContinuousSquareVariationProcessUpTo_of_eqUpTo
      (eqUpTo_of_areIndistinguishable (T := T) hN₁.indistinguishable_canonical)
      (eqUpTo_rfl (μ := μ) T (bracketDensityIntegralUpTo hbr₁ H₁))
      (canonicalItoIntegral_singleClausesUpTo
        (μ := μ) (ℱ := ℱ) (T := T) hH₁_prog hH₁_sq).2

/-- Fourth source clause of the finite-horizon reformulation of Theorem 25.22 on `[0, T]`. -/
theorem squareVariation_right
    {M₂ H₂ N₂ : NNReal → Ω → ℝ}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₂ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂) :
    IsContinuousSquareVariationProcessUpTo ℱ μ T N₂ (bracketDensityIntegralUpTo hbr₂ H₂) := by
  -- Proof comment: this is the symmetric transport of the canonical square-variation witness.
  exact
    isContinuousSquareVariationProcessUpTo_of_eqUpTo
      (eqUpTo_of_areIndistinguishable (T := T) hN₂.indistinguishable_canonical)
      (eqUpTo_rfl (μ := μ) T (bracketDensityIntegralUpTo hbr₂ H₂))
      (canonicalItoIntegral_singleClausesUpTo
        (μ := μ) (ℱ := ℱ) (T := T) hH₂_prog hH₂_sq).2

/-- Fifth source clause of the finite-horizon reformulation of Theorem 25.22 on `[0, T]`. -/
theorem quadraticCovariation_left_right
    {M₁ M₂ H₁ H₂ N₁ N₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁)
    (hN₂ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂) := by
  -- Proof comment: transport the canonical mixed-bracket witness along the two
  -- indistinguishability relations coming from the source-facing hypotheses.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (eqUpTo_of_areIndistinguishable (T := T) hN₁.indistinguishable_canonical)
      (eqUpTo_of_areIndistinguishable (T := T) hN₂.indistinguishable_canonical)
      (eqUpTo_rfl (μ := μ) T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₁ hM₂ H₁ H₂))
      (canonicalItoIntegral_quadraticCovariationClausesUpTo
        (μ := μ) (ℱ := ℱ) (T := T) hH₁_prog hH₂_prog hH₁_sq hH₂_sq).1

/-- Sixth source clause of the finite-horizon reformulation of Theorem 25.22 on `[0, T]`. -/
theorem quadraticCovariation_right_left
    {M₁ M₂ H₁ H₂ N₁ N₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁)
    (hN₂ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂) :
    IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₂ N₁
      (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁) := by
  -- Proof comment: this is the symmetric transport of the canonical mixed-bracket witness.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (eqUpTo_of_areIndistinguishable (T := T) hN₂.indistinguishable_canonical)
      (eqUpTo_of_areIndistinguishable (T := T) hN₁.indistinguishable_canonical)
      (eqUpTo_rfl (μ := μ) T
        (Theorem25_22.quadraticCovariationIntegralUpTo hM₂ hM₁ H₂ H₁))
      (canonicalItoIntegral_quadraticCovariationClausesUpTo
        (μ := μ) (ℱ := ℱ) (T := T) hH₁_prog hH₂_prog hH₁_sq hH₂_sq).2.1

/-- Seventh source clause of the finite-horizon reformulation of Theorem 25.22 on `[0, T]`. -/
theorem quadraticCovariation_zero_of_indepFun
    {M₁ M₂ H₁ H₂ N₁ N₂ : NNReal → Ω → ℝ}
    {hM₁ : IsContinuousLocalMartingale ℱ μ M₁}
    {hM₂ : IsContinuousLocalMartingale ℱ μ M₂}
    {hbr₁ : HasAbsolutelyContinuousSquareVariation M₁ hM₁}
    {hbr₂ : HasAbsolutelyContinuousSquareVariation M₂ hM₂}
    (T : NNReal)
    (hH₁_prog : ProgMeasurable ℱ H₁)
    (hH₂_prog : ProgMeasurable ℱ H₂)
    (hH₁_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₁ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₁ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH₂_sq :
      ∀ᵐ ω ∂μ,
        IntegrableOn
          (fun s : ℝ ↦
            (H₂ s.toNNReal ω) ^ 2 *
              (Theorem25_22.squareVariationDensity hbr₂ s.toNNReal ω : ℝ))
          (Set.Icc (0 : ℝ) (T : ℝ)))
    (hN₁ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₁ H₁ N₁)
    (hN₂ : _root_.ProbabilityTheory.IsContinuousLocalMartingaleItoIntegral hbr₂ H₂ N₂) :
    (IndepFun (fun ω ↦ fun t : NNReal ↦ M₁ t ω)
        (fun ω ↦ fun t : NNReal ↦ M₂ t ω) μ) →
      IsContinuousQuadraticCovariationProcessUpTo ℱ μ T N₁ N₂ 0 := by
  intro hIndep
  -- Proof comment: once the canonical zero-bracket clause is known, the source-facing processes
  -- inherit it by the same finite-horizon transport as above.
  exact
    isContinuousQuadraticCovariationProcessUpTo_of_eqUpTo
      (eqUpTo_of_areIndistinguishable (T := T) hN₁.indistinguishable_canonical)
      (eqUpTo_of_areIndistinguishable (T := T) hN₂.indistinguishable_canonical)
      (eqUpTo_rfl (μ := μ) T 0)
      ((canonicalItoIntegral_quadraticCovariationClausesUpTo
        (μ := μ) (ℱ := ℱ) (T := T) hH₁_prog hH₂_prog hH₁_sq hH₂_sq).2.2 hIndep)

end IsContinuousLocalMartingaleItoIntegral

end ProbabilityTheory
