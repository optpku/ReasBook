/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Probability.HasLaw

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology lp

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The symmetric law on `ℤ` giving mass `1 / 2` to both `1` and `-1`. -/
def symmetricRademacherLaw : Measure ℤ :=
  ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℤ)) +
    ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℤ))

/-- The symmetric Rademacher law assigns probability `1 / 2` to the singleton `{1}`. -/
theorem symmetricRademacherLaw_apply_singleton_one :
    symmetricRademacherLaw ({1} : Set ℤ) = 1 / 2 := by
  simp [symmetricRademacherLaw]

/-- The partial sum `Sₙ = X₀ + ⋯ + Xₙ₋₁` of a `0`-based real sequence `X 0, X 1, …`. -/
def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, X i ω

/-- For `1 ≤ p`, a sequence `fₙ : Ω → E` converges to `f` in `L^p(μ)` when each `fₙ` and `f`
belongs to `ℒ^p(μ)` and the associated classes in `MeasureTheory.Lp E p μ` converge. -/
abbrev TendstoInLp (p : ℝ≥0∞) {E : Type v} [NormedAddCommGroup E] [Fact (1 ≤ p)]
    (μ : Measure Ω) (fSeq : ℕ → Ω → E) (f : Ω → E) : Prop :=
  ∃ h_memLpSeq : ∀ n, MemLp (fSeq n) p μ,
    ∃ h_memLp : MemLp f p μ,
      Tendsto (fun n ↦ (h_memLpSeq n).toLp (fSeq n)) atTop (𝓝 (h_memLp.toLp f))

namespace ProbabilityTheory

/-- The symmetric Rademacher law on `ℝ`, assigning mass `1 / 2` to each of the values `-1` and
`1`. -/
abbrev symmetricRademacherRealLaw : Measure ℝ :=
  Measure.map ((↑) : ℤ → ℝ) symmetricRademacherLaw

-- Proof sketch: rewrite the real-valued law as the pushforward of the Chapter 9 Rademacher law
-- along the integer embedding `ℤ → ℝ`, then apply the singleton formula upstream.
/-- The symmetric `{-1, 1}`-valued law on `ℝ` assigns probability `1 / 2` to the value `1`. -/
theorem rademacherRealLaw_apply_singleton_one :
    symmetricRademacherRealLaw ({1} : Set ℝ) = 1 / 2 := by
  rw [symmetricRademacherRealLaw,
    Measure.map_apply (by fun_prop) (measurableSet_singleton (1 : ℝ))]
  have hpreimage : ((↑) : ℤ → ℝ) ⁻¹' ({1} : Set ℝ) = ({1} : Set ℤ) := by
    ext z
    simp
  rw [hpreimage]
  exact symmetricRademacherLaw_apply_singleton_one

/-- The source-facing subspace `ℓ^f ⊆ ℓ²(ℕ, ℝ)` of finitely supported sequences. -/
def l2FinitelySupported : Submodule ℝ ℓ²(ℕ, ℝ) where
  carrier := { h | Function.HasFiniteSupport h }
  zero_mem' := by
    change (Function.support (0 : ℕ → ℝ)).Finite
    simp
  add_mem' := by
    intro h g hh hg
    exact (hh.union hg).subset (Function.support_add h g)
  smul_mem' := by
    intro c h hh
    exact hh.subset (Function.support_const_smul_subset c h)

private theorem finiteSupport_sum_single_mem (f : ℓ²(ℕ, ℝ)) (s : Finset ℕ) :
    Function.HasFiniteSupport (∑ i ∈ s, lp.single 2 i (f i) : ℓ²(ℕ, ℝ)) := by
  refine (Set.toFinite (↑s : Set ℕ)).subset ?_
  rw [Function.support_subset_iff']
  intro n hn
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hni : n ≠ i := by
    intro h
    apply hn
    simpa [h] using hi
  simp [lp.single_apply, hni]

private theorem denseRange_l2FinitelySupported_subtype :
    DenseRange (l2FinitelySupported.subtypeₗᵢ : l2FinitelySupported → ℓ²(ℕ, ℝ)) := by
  intro f
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f) ?_
  refine Filter.Eventually.of_forall ?_
  intro s
  refine ⟨⟨∑ i ∈ s, lp.single 2 i (f i), finiteSupport_sum_single_mem f s⟩, rfl⟩

/-- Helper for Example 25.1: the real-valued Rademacher law is the equally weighted sum of the
two Dirac masses at `1` and `-1`. -/
private theorem symmetricRademacherRealLaw_eq :
    symmetricRademacherRealLaw =
      ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) +
        ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) := by
  -- Proof comment: expand the integer-valued source law and compute its pushforward under the
  -- cast `ℤ → ℝ` on each Dirac atom.
  have hmeas : Measurable ((↑) : ℤ → ℝ) := measurable_of_countable _
  rw [symmetricRademacherRealLaw, symmetricRademacherLaw, Measure.map_add _ _ hmeas,
    Measure.map_smul, Measure.map_smul, Measure.map_dirac' hmeas, Measure.map_dirac' hmeas]
  simp

/-- Helper for Example 25.1: the real-valued Rademacher law is itself a probability measure. -/
private instance symmetricRademacherRealLaw_isProbabilityMeasure :
    IsProbabilityMeasure symmetricRademacherRealLaw := by
  -- Proof comment: the explicit two-atom description has total mass `1`.
  refine ⟨?_⟩
  rw [symmetricRademacherRealLaw_eq]
  simpa using (ENNReal.add_halves (1 : ℝ≥0∞))

/-- Helper for Example 25.1: the identity random variable on the real Rademacher law is square
integrable because it is almost surely bounded by `1` in absolute value. -/
private theorem memLp_two_id_symmetricRademacherRealLaw :
    MemLp (id : ℝ → ℝ) 2 symmetricRademacherRealLaw := by
  -- Proof comment: after rewriting the law as a two-atom measure, the sample points are literally
  -- the endpoints `-1` and `1`, so `memLp_of_bounded` applies immediately.
  have hbound : ∀ᵐ x ∂symmetricRademacherRealLaw, x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [symmetricRademacherRealLaw_eq]
    simp
  exact memLp_of_bounded hbound aestronglyMeasurable_id 2

/-- Helper for Example 25.1: the real-valued symmetric Rademacher law has mean zero. -/
private theorem symmetricRademacherRealLaw_mean_zero :
    symmetricRademacherRealLaw[(id : ℝ → ℝ)] = 0 := by
  -- Proof comment: evaluate the integral on the explicit two-point law and cancel the two atoms.
  rw [symmetricRademacherRealLaw_eq]
  have hposDirac : Integrable (id : ℝ → ℝ) (Measure.dirac (1 : ℝ)) := by
    exact integrable_dirac (a := (1 : ℝ)) (f := id) (by norm_num : ‖(1 : ℝ)‖ₑ < ∞)
  have hnegDirac : Integrable (id : ℝ → ℝ) (Measure.dirac (-1 : ℝ)) := by
    exact integrable_dirac (a := (-1 : ℝ)) (f := id) (by norm_num : ‖(-1 : ℝ)‖ₑ < ∞)
  have hpos : Integrable (id : ℝ → ℝ) ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) := by
    exact hposDirac.smul_measure (by simp)
  have hneg : Integrable (id : ℝ → ℝ) ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) := by
    exact hnegDirac.smul_measure (by simp)
  rw [integral_add_measure hpos hneg, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  norm_num

/-- Helper for Example 25.1: the real-valued symmetric Rademacher law has variance one. -/
private theorem symmetricRademacherRealLaw_variance_one :
    Var[(id : ℝ → ℝ); symmetricRademacherRealLaw] = 1 := by
  -- Proof comment: use the standard variance identity `E[X²] - E[X]²`; the mean is zero and the
  -- second moment of the two-atom law is exactly `1`.
  rw [ProbabilityTheory.variance_eq_sub memLp_two_id_symmetricRademacherRealLaw,
    symmetricRademacherRealLaw_mean_zero]
  rw [symmetricRademacherRealLaw_eq]
  change ∫ x : ℝ, x ^ 2 ∂(((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) +
      ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ))) - 0 ^ 2 = 1
  have hsqPosDirac : Integrable (fun x : ℝ ↦ x ^ 2) (Measure.dirac (1 : ℝ)) := by
    exact integrable_dirac (a := (1 : ℝ)) (f := fun x : ℝ ↦ x ^ 2)
      (by norm_num : ‖(1 : ℝ) ^ 2‖ₑ < ∞)
  have hsqNegDirac : Integrable (fun x : ℝ ↦ x ^ 2) (Measure.dirac (-1 : ℝ)) := by
    exact integrable_dirac (a := (-1 : ℝ)) (f := fun x : ℝ ↦ x ^ 2)
      (by norm_num : ‖(-1 : ℝ) ^ 2‖ₑ < ∞)
  have hsqPos : Integrable (fun x : ℝ ↦ x ^ 2) ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) := by
    exact hsqPosDirac.smul_measure (by simp)
  have hsqNeg : Integrable (fun x : ℝ ↦ x ^ 2) ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) := by
    exact hsqNegDirac.smul_measure (by simp)
  rw [integral_add_measure hsqPos hsqNeg, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  norm_num

private theorem memLp_two_of_hasLaw_symmetricRademacher
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X symmetricRademacherRealLaw P) :
    MemLp X 2 P := by
  -- Proof comment: the law is supported on `{-1, 1}`, so `X` is almost surely bounded by `1`
  -- in absolute value; `memLp_of_bounded` then gives the `L²` bound directly.
  have hbound_law : ∀ᵐ x ∂symmetricRademacherRealLaw, x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [symmetricRademacherRealLaw_eq]
    simp
  have hmeas : Measurable fun x : ℝ ↦ x ∈ Set.Icc (-1 : ℝ) 1 := measurableSet_Icc.mem
  have hbound : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (-1 : ℝ) 1 := by
    exact (hX.ae_iff hmeas).2 hbound_law
  exact memLp_of_bounded hbound hX.aemeasurable.aestronglyMeasurable 2

private def rademacherCoordinate
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) (n : ℕ) :
    Lp ℝ 2 P :=
  (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).toLp (X n)

private def weightedCoordinate
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) :
    ℕ → Lp ℝ 2 P :=
  fun n ↦ ((h : ℓ²(ℕ, ℝ)) n) • rademacherCoordinate P X hX_rademacher n

private theorem weightedCoordinate_hasFiniteSupport
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) :
    Function.HasFiniteSupport (weightedCoordinate P X hX_rademacher h) := by
  exact h.2.subset <| by
    simpa [weightedCoordinate] using
      Function.support_smul_subset_left (h : ℓ²(ℕ, ℝ))
        (fun n ↦ rademacherCoordinate P X hX_rademacher n)

private theorem rademacherSeriesOnFiniteSupport_map_add
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h g : l2FinitelySupported) :
    ∑ᶠ n, weightedCoordinate P X hX_rademacher (h + g) n =
      ∑ᶠ n, weightedCoordinate P X hX_rademacher h n +
        ∑ᶠ n, weightedCoordinate P X hX_rademacher g n := by
  -- Proof comment: all three `finsum`s are supported inside the union of the supports of `h`
  -- and `g`, so we can rewrite them over one common `Finset` and compare summands pointwise.
  let s : Finset ℕ := (h.2.union g.2).toFinset
  have hs_add :
      Function.support (weightedCoordinate P X hX_rademacher (h + g)) ⊆ s := by
    intro n hn
    have hsub :
        Function.support (((h + g : l2FinitelySupported) : ℓ²(ℕ, ℝ))) ⊆
          Function.support (h : ℓ²(ℕ, ℝ)) ∪ Function.support (g : ℓ²(ℕ, ℝ)) := by
      simpa using (Function.support_add (h : ℓ²(ℕ, ℝ)) (g : ℓ²(ℕ, ℝ)))
    exact ((h.2.union g.2).mem_toFinset).2 <|
      hsub <| by
        simpa [weightedCoordinate] using
          (Function.support_smul_subset_left (((h + g : l2FinitelySupported) : ℓ²(ℕ, ℝ)))
            (fun n ↦ rademacherCoordinate P X hX_rademacher n) hn)
  have hs_h :
      Function.support (weightedCoordinate P X hX_rademacher h) ⊆ s := by
    intro n hn
    have hsub :
        Function.support (weightedCoordinate P X hX_rademacher h) ⊆ Function.support
          (h : ℓ²(ℕ, ℝ)) := by
      simpa [weightedCoordinate] using
        (Function.support_smul_subset_left (h : ℓ²(ℕ, ℝ))
          (fun n ↦ rademacherCoordinate P X hX_rademacher n))
    exact ((h.2.union g.2).mem_toFinset).2 <| Set.mem_union_left _ <| hsub hn
  have hs_g :
      Function.support (weightedCoordinate P X hX_rademacher g) ⊆ s := by
    intro n hn
    have hsub :
        Function.support (weightedCoordinate P X hX_rademacher g) ⊆ Function.support
          (g : ℓ²(ℕ, ℝ)) := by
      simpa [weightedCoordinate] using
        (Function.support_smul_subset_left (g : ℓ²(ℕ, ℝ))
          (fun n ↦ rademacherCoordinate P X hX_rademacher n))
    exact ((h.2.union g.2).mem_toFinset).2 <| Set.mem_union_right _ <| hsub hn
  have hsum_add :
      ∑ᶠ n, weightedCoordinate P X hX_rademacher (h + g) n =
        ∑ n ∈ s, weightedCoordinate P X hX_rademacher (h + g) n :=
    finsum_eq_sum_of_support_subset _ hs_add
  have hsum_h :
      ∑ᶠ n, weightedCoordinate P X hX_rademacher h n =
        ∑ n ∈ s, weightedCoordinate P X hX_rademacher h n :=
    finsum_eq_sum_of_support_subset _ hs_h
  have hsum_g :
      ∑ᶠ n, weightedCoordinate P X hX_rademacher g n =
        ∑ n ∈ s, weightedCoordinate P X hX_rademacher g n :=
    finsum_eq_sum_of_support_subset _ hs_g
  rw [hsum_add, hsum_h, hsum_g]
  -- Proof comment: on the common support set, linearity is just the pointwise identity
  -- `(h n + g n) • eₙ = h n • eₙ + g n • eₙ`.
  calc
    ∑ n ∈ s, weightedCoordinate P X hX_rademacher (h + g) n
      = ∑ n ∈ s,
          (weightedCoordinate P X hX_rademacher h n +
            weightedCoordinate P X hX_rademacher g n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa [weightedCoordinate] using
              add_smul ((h : ℓ²(ℕ, ℝ)) n) ((g : ℓ²(ℕ, ℝ)) n)
                (rademacherCoordinate P X hX_rademacher n)
    _ = ∑ n ∈ s, weightedCoordinate P X hX_rademacher h n +
          ∑ n ∈ s, weightedCoordinate P X hX_rademacher g n := by
            rw [Finset.sum_add_distrib]

private theorem rademacherSeriesOnFiniteSupport_map_smul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (c : ℝ) (h : l2FinitelySupported) :
    ∑ᶠ n, weightedCoordinate P X hX_rademacher (c • h) n =
      c • ∑ᶠ n, weightedCoordinate P X hX_rademacher h n := by
  -- Proof comment: rewrite both sides over the original support of `h`; pointwise this is just
  -- the scalar identity `((c * h n) • eₙ) = c • (h n • eₙ)`.
  let s : Finset ℕ := h.2.toFinset
  have hs_smul :
      Function.support (weightedCoordinate P X hX_rademacher (c • h)) ⊆ s := by
    intro n hn
    have hsub :
        Function.support (weightedCoordinate P X hX_rademacher (c • h)) ⊆ Function.support
          (((c • h : l2FinitelySupported) : ℓ²(ℕ, ℝ))) := by
      simpa [weightedCoordinate] using
        (Function.support_smul_subset_left (((c • h : l2FinitelySupported) : ℓ²(ℕ, ℝ)))
          (fun n ↦ rademacherCoordinate P X hX_rademacher n))
    have hsub' :
        Function.support (((c • h : l2FinitelySupported) : ℓ²(ℕ, ℝ))) ⊆ Function.support
          (h : ℓ²(ℕ, ℝ)) := by
      exact Function.support_const_smul_subset c (h : ℓ²(ℕ, ℝ))
    exact h.2.mem_toFinset.2 <| hsub' (hsub hn)
  have hs_h :
      Function.support (weightedCoordinate P X hX_rademacher h) ⊆ s := by
    intro n hn
    have hsub :
        Function.support (weightedCoordinate P X hX_rademacher h) ⊆ Function.support
          (h : ℓ²(ℕ, ℝ)) := by
      simpa [weightedCoordinate] using
        (Function.support_smul_subset_left (h : ℓ²(ℕ, ℝ))
          (fun n ↦ rademacherCoordinate P X hX_rademacher n))
    exact h.2.mem_toFinset.2 <| hsub hn
  have hsum_smul :
      ∑ᶠ n, weightedCoordinate P X hX_rademacher (c • h) n =
        ∑ n ∈ s, weightedCoordinate P X hX_rademacher (c • h) n :=
    finsum_eq_sum_of_support_subset _ hs_smul
  have hsum_h :
      ∑ᶠ n, weightedCoordinate P X hX_rademacher h n =
        ∑ n ∈ s, weightedCoordinate P X hX_rademacher h n :=
    finsum_eq_sum_of_support_subset _ hs_h
  rw [hsum_smul, hsum_h]
  -- Proof comment: once both sides are finite sums on the same index set, scalar compatibility is
  -- pointwise associativity of scalar multiplication in `L²(P)`.
  calc
    ∑ n ∈ s, weightedCoordinate P X hX_rademacher (c • h) n
      = ∑ n ∈ s, c • weightedCoordinate P X hX_rademacher h n := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [weightedCoordinate, smul_smul]
    _ = c • ∑ n ∈ s, weightedCoordinate P X hX_rademacher h n := by
          rw [Finset.smul_sum]

/-- For `h ∈ ℓ^f`, the finite random series `R(h) = ∑ hₙ Xₙ` viewed as an element of
`L²(P)`. -/
def rademacherSeriesOnFiniteSupport
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    l2FinitelySupported →ₗ[ℝ] Lp ℝ 2 P where
  toFun := fun h ↦ ∑ᶠ n, weightedCoordinate P X hX_rademacher h n
  map_add' := rademacherSeriesOnFiniteSupport_map_add P X hX_rademacher
  map_smul' := rademacherSeriesOnFiniteSupport_map_smul P X hX_rademacher

/-- On `ℓ^f`, the operator `R` is the finite sum of the coordinates against the Rademacher family
`X`, over any finite set containing the support of `h`. -/
theorem rademacherSeriesOnFiniteSupport_apply
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) {s : Finset ℕ}
    (hs : Function.support (h : ℓ²(ℕ, ℝ)) ⊆ s) :
    rademacherSeriesOnFiniteSupport P X hX_rademacher h =
      Finset.sum s fun n ↦
        ((h : ℓ²(ℕ, ℝ)) n) • rademacherCoordinate P X hX_rademacher n := by
  -- Proof comment: the `finsum` defining `R(h)` is supported inside the support of `h`, so any
  -- finite superset of that support gives the same finite sum formula.
  have hs_weighted :
      Function.support (weightedCoordinate P X hX_rademacher h) ⊆ s := by
    intro n hn
    have hsub :
        Function.support (weightedCoordinate P X hX_rademacher h) ⊆ Function.support
          (h : ℓ²(ℕ, ℝ)) := by
      simpa [weightedCoordinate] using
        (Function.support_smul_subset_left (h : ℓ²(ℕ, ℝ))
          (fun n ↦ rademacherCoordinate P X hX_rademacher n))
    exact hs (hsub hn)
  change ∑ᶠ n, weightedCoordinate P X hX_rademacher h n =
    Finset.sum s (fun n ↦ ((h : ℓ²(ℕ, ℝ)) n) • rademacherCoordinate P X hX_rademacher n)
  rw [finsum_eq_sum_of_support_subset _ hs_weighted]
  -- Proof comment: on the chosen finite support set, the summand is exactly the weighted
  -- coordinate by definition.
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [weightedCoordinate]

/-- Helper for Example 25.1: each Rademacher coordinate has mean `0` and variance `1`. -/
private theorem rademacherCoordinate_mean_zero_variance_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) (n : ℕ) :
    P[X n] = 0 ∧ Var[X n; P] = 1 := by
  constructor
  · -- Proof comment: transfer the expectation from the coordinate law to the model
    -- Rademacher law, whose mean is already computed.
    calc
      P[X n] = ∫ x, x ∂symmetricRademacherRealLaw := (hX_rademacher n).integral_eq
      _ = 0 := symmetricRademacherRealLaw_mean_zero
  · -- Proof comment: the same law transfer identifies the variance with the variance of the
    -- identity under the symmetric Rademacher law.
    calc
      Var[X n; P] = Var[(id : ℝ → ℝ); symmetricRademacherRealLaw] :=
        (hX_rademacher n).variance_eq
      _ = 1 := symmetricRademacherRealLaw_variance_one

/-- Helper for Example 25.1: a finite weighted Rademacher sum is represented in `L²(P)` by the
corresponding finite sum of weighted coordinate classes. -/
private theorem finiteWeightedCoordinate_sum_eq_toLp
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    ∑ n ∈ s, a n • rademacherCoordinate P X hX_rademacher n =
      (memLp_finset_sum s fun n _ ↦
        (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul (a n)).toLp
        (fun ω ↦ ∑ n ∈ s, a n * X n ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty finite sum is the zero class in `L²(P)`.
      simp
  | @insert i s hi ih =>
      -- Proof comment: split off the first summand, rewrite both pieces as `toLp` classes, and
      -- reassemble them with `MemLp.toLp_add`.
      have hiMem :
          MemLp (fun ω ↦ a i * X i ω) 2 P := by
        simpa [smul_eq_mul, Pi.smul_apply] using
          (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher i)).const_smul (a i)
      have hsMem :
          MemLp (fun ω ↦ ∑ n ∈ s, a n * X n ω) 2 P := by
        exact memLp_finset_sum s fun n hn ↦ by
          simpa [smul_eq_mul, Pi.smul_apply] using
            (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul (a n)
      have hhead :
          a i • rademacherCoordinate P X hX_rademacher i =
            hiMem.toLp (fun ω ↦ a i * X i ω) := by
        simpa [rademacherCoordinate, smul_eq_mul, Pi.smul_apply] using
          (MemLp.toLp_const_smul (a i)
            (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher i))).symm
      calc
        ∑ n ∈ insert i s, a n • rademacherCoordinate P X hX_rademacher n
            = a i • rademacherCoordinate P X hX_rademacher i +
                ∑ n ∈ s, a n • rademacherCoordinate P X hX_rademacher n := by
                  rw [Finset.sum_insert hi]
        _ = hiMem.toLp (fun ω ↦ a i * X i ω) +
              hsMem.toLp (fun ω ↦ ∑ n ∈ s, a n * X n ω) := by
                rw [hhead, ih]
        _ = (hiMem.add hsMem).toLp
              ((fun ω ↦ a i * X i ω) + fun ω ↦ ∑ n ∈ s, a n * X n ω) := by
                rw [← MemLp.toLp_add hiMem hsMem]
        _ =
            (memLp_finset_sum (insert i s) fun n _ ↦
              (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul
                (a n)).toLp
              (fun ω ↦ ∑ n ∈ insert i s, a n * X n ω) := by
                apply (MemLp.toLp_eq_toLp_iff _ _).2
                filter_upwards with ω
                rw [Finset.sum_insert hi]
                rfl

/-- Helper for Example 25.1: the squared `L²` norm of a real `Lp` class is the second moment of
any representative. -/
private theorem toLpNormSq_eq_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = P[fun ω ↦ (f ω) ^ 2] := by
  -- Proof comment: identify the `L²` norm with the square root of the second moment, then square
  -- back using nonnegativity of the integral of `f²`.
  have hnorm : ‖hf.toLp f‖ = Real.sqrt (∫ ω, (f ω) ^ 2 ∂P) := by
    rw [Lp.norm_toLp]
    rw [show eLpNorm f 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, (f ω) ^ 2 ∂P)) by
      simpa [Real.sqrt_eq_rpow, one_div, sq_abs] using
        (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hf)]
    rw [ENNReal.toReal_ofReal]
    positivity
  calc
    ‖hf.toLp f‖ ^ 2 = (Real.sqrt (∫ ω, (f ω) ^ 2 ∂P)) ^ 2 := by rw [hnorm]
    _ = P[fun ω ↦ (f ω) ^ 2] := by
          rw [Real.sq_sqrt]
          positivity

/-- Helper for Example 25.1: the variance of a finite weighted Rademacher sum is the sum of the
squared coefficients. -/
private theorem finiteWeightedRademacherSum_variance_eq_sum_sq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    Var[(fun ω ↦ ∑ n ∈ s, a n * X n ω); P] = ∑ n ∈ s, (a n) ^ 2 := by
  -- Proof comment: apply the finite-sum variance additivity theorem to the independent weighted
  -- coordinates, then rewrite each diagonal variance using the Rademacher variance `1`.
  have hmem :
      ∀ n ∈ s, MemLp (fun ω ↦ a n * X n ω) 2 P := by
    intro n hn
    simpa [smul_eq_mul, Pi.smul_apply] using
      (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul (a n)
  have hpairwise :
      Set.Pairwise (↑s) fun i j ↦
        (fun ω ↦ a i * X i ω) ⟂ᵢ[P] (fun ω ↦ a j * X j ω) := by
    intro i hi j hj hij
    exact IndepFun.comp₀ (hX_indep.indepFun hij)
      (hX_rademacher i).aemeasurable
      (hX_rademacher j).aemeasurable
      (measurable_const.mul measurable_id).aemeasurable
      (measurable_const.mul measurable_id).aemeasurable
  calc
    Var[(fun ω ↦ ∑ n ∈ s, a n * X n ω); P]
        = Var[∑ n ∈ s, fun ω ↦ a n * X n ω; P] := by
            refine congrArg (fun f : Ω → ℝ ↦ Var[f; P]) ?_
            funext ω
            simp
    _ = ∑ n ∈ s, Var[(fun ω ↦ a n * X n ω); P] := by
          exact IndepFun.variance_sum hmem hpairwise
    _ = ∑ n ∈ s, (a n) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rcases rademacherCoordinate_mean_zero_variance_one P X hX_rademacher n with ⟨-, hvar⟩
          rw [show Var[(fun ω ↦ a n * X n ω); P] = (a n) ^ 2 * Var[X n; P] by
            simpa [smul_eq_mul, Pi.smul_apply] using variance_smul (a n) (X n) P]
          simp [hvar]

/-- Helper for Example 25.1: the `ℓ²` norm of a finitely supported sequence is the finite sum of
the squared nonzero coordinates. -/
private theorem l2FinitelySupported_norm_sq_eq_sum_sq (h : l2FinitelySupported) :
    ‖(h : ℓ²(ℕ, ℝ))‖ ^ 2 = ∑ n ∈ h.2.toFinset, ((h : ℓ²(ℕ, ℝ)) n) ^ 2 := by
  -- Proof comment: reduce the `ℓ²` norm square to the defining `tsum`, then collapse the `tsum`
  -- to the finite support of `h`.
  have hsupport :
      Function.support (fun n ↦ ‖((h : ℓ²(ℕ, ℝ)) n)‖ ^ (2 : ℝ)) ⊆
        Function.support (h : ℓ²(ℕ, ℝ)) := by
    intro n hn
    by_contra hzero
    have hz : ((h : ℓ²(ℕ, ℝ)) n) = 0 := by
      simpa [Function.mem_support] using hzero
    apply hn
    simp [hz]
  have hfinite :
      (Function.support fun n ↦ ‖((h : ℓ²(ℕ, ℝ)) n)‖ ^ (2 : ℝ)).Finite :=
    h.2.subset hsupport
  calc
    ‖(h : ℓ²(ℕ, ℝ))‖ ^ 2
        = ∑' n, ‖((h : ℓ²(ℕ, ℝ)) n)‖ ^ (2 : ℝ) := by
            simpa using
              (lp.norm_rpow_eq_tsum (E := fun _ : ℕ ↦ ℝ) (p := 2) (by norm_num)
                (h : ℓ²(ℕ, ℝ)))
    _ = ∑ᶠ n, ‖((h : ℓ²(ℕ, ℝ)) n)‖ ^ (2 : ℝ) := by
          rw [tsum_eq_finsum hfinite]
    _ = ∑ n ∈ h.2.toFinset, ‖((h : ℓ²(ℕ, ℝ)) n)‖ ^ (2 : ℝ) := by
          rw [finsum_eq_sum_of_support_subset _ fun n hn ↦ h.2.mem_toFinset.2 (hsupport hn)]
    _ = ∑ n ∈ h.2.toFinset, ((h : ℓ²(ℕ, ℝ)) n) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [sq_abs]

/-- Helper for Example 25.1: each finite weighted partial sum belongs to `L²(P)`. -/
private theorem weightedPartialSum_memLp_two
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (a : ℕ → ℝ) (N : ℕ) :
    MemLp (fun ω ↦ partialSum (fun n ω ↦ a n * X n ω) N ω) 2 P := by
  -- Proof comment: each weighted coordinate is in `L²(P)`, and finite sums preserve `L²`.
  simpa [partialSum] using
    (memLp_finset_sum (Finset.range N) fun n _ ↦ by
      simpa [smul_eq_mul, Pi.smul_apply] using
        (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul (a n))

/-- Helper for Example 25.1: the canonical truncation of `h ∈ ℓ²(ℕ, ℝ)` to the first `N`
coordinates lives in `ℓ^f`. -/
private def l2Truncation (h : ℓ²(ℕ, ℝ)) (N : ℕ) : l2FinitelySupported :=
  ⟨∑ i ∈ Finset.range N, lp.single 2 i (h i), finiteSupport_sum_single_mem h (Finset.range N)⟩

/-- Helper for Example 25.1: the `N`-th truncation keeps exactly the coordinates with index
`< N`. -/
private theorem l2Truncation_apply (h : ℓ²(ℕ, ℝ)) (N n : ℕ) :
    (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n) = if n < N then h n else 0 := by
  -- Proof comment: evaluate the finite sum of `lp.single` vectors at the coordinate `n`.
  dsimp [l2Truncation]
  rw [lp.coeFn_sum, Finset.sum_apply]
  by_cases hn : n < N
  · rw [if_pos hn]
    have hn_mem : n ∈ Finset.range N := Finset.mem_range.2 hn
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hn_mem]
    simp [lp.single_apply, hn]
  · rw [if_neg hn]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hni : n ≠ i := by
      intro hEq
      apply hn
      simpa [hEq] using (Finset.mem_range.1 hi)
    simp [lp.single_apply, hni]

/-- Helper for Example 25.1: on the active truncation range, the truncation agrees with the
original `ℓ²` sequence. -/
private theorem l2Truncation_apply_of_mem_range (h : ℓ²(ℕ, ℝ)) {N n : ℕ}
    (hn : n ∈ Finset.range N) :
    (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n) = h n := by
  -- Proof comment: inside `Finset.range N`, the projection formula specializes to the original
  -- coefficient.
  simp [l2Truncation_apply, Finset.mem_range.1 hn]

/-- Helper for Example 25.1: the support of the `N`-th truncation is contained in
`Finset.range N`. -/
private theorem l2Truncation_support_subset_range (h : ℓ²(ℕ, ℝ)) (N : ℕ) :
    Function.support ((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) ⊆ Finset.range N := by
  -- Proof comment: outside `Finset.range N`, the projection formula for the truncation is zero.
  rw [Function.support_subset_iff']
  intro n hn
  rw [l2Truncation_apply]
  split_ifs with hlt
  · exact False.elim <| hn (Finset.mem_range.2 hlt)
  · rfl

/-- Helper for Example 25.1: the canonical truncations converge to `h` in `ℓ²(ℕ, ℝ)`. -/
private theorem l2Truncation_tendsto (h : ℓ²(ℕ, ℝ)) :
    Tendsto (fun N ↦ ((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ))) atTop (𝓝 h) := by
  -- Proof comment: the truncations are exactly the standard partial sums of the canonical
  -- `lp.single` expansion of an `ℓ²` vector.
  simpa [l2Truncation] using (lp.hasSum_single ENNReal.ofNat_ne_top h).tendsto_sum_nat

-- Proof sketch: for finitely supported `h`, the random variable `R(h)` is a finite sum of
-- independent centered `{-1,1}`-valued coordinates. The cross-terms vanish, and each diagonal term
-- contributes `h n ^ 2`, so `‖R(h)‖_{L²(P)}^2 = ∑ h n ^ 2 = ‖h‖_{ℓ²}^2`.
/-- For Example 25.1, the source-facing operator `R : ℓ^f → L²(P)` is an isometry on finitely
supported sequences. -/
theorem rademacherSeriesOnFiniteSupport_isometry
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    Isometry (rademacherSeriesOnFiniteSupport P X hX_rademacher) := by
  refine AddMonoidHomClass.isometry_of_norm _ ?_
  intro h
  -- Proof comment: rewrite `R(h)` as the `toLp` class of the scalar finite sum over the support
  -- of `h`, compute its second moment as a variance, and compare with the domain `ℓ²` norm.
  let s : Finset ℕ := h.2.toFinset
  have hs :
      Function.support (h : ℓ²(ℕ, ℝ)) ⊆ s := by
    intro n hn
    exact h.2.mem_toFinset.2 hn
  have hrepr :
      rademacherSeriesOnFiniteSupport P X hX_rademacher h =
        ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) • rademacherCoordinate P X hX_rademacher n := by
    exact rademacherSeriesOnFiniteSupport_apply P X hX_rademacher h hs
  have hmem :
      MemLp (fun ω ↦ ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) * X n ω) 2 P := by
    exact memLp_finset_sum s fun n hn ↦ by
      simpa [smul_eq_mul, Pi.smul_apply] using
        (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul
          (((h : ℓ²(ℕ, ℝ)) n))
  have htoLp :
      rademacherSeriesOnFiniteSupport P X hX_rademacher h =
        hmem.toLp (fun ω ↦ ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) * X n ω) := by
    calc
      rademacherSeriesOnFiniteSupport P X hX_rademacher h
          = ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) • rademacherCoordinate P X hX_rademacher n := hrepr
      _ =
          (memLp_finset_sum s fun n _ ↦
            (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul
              (((h : ℓ²(ℕ, ℝ)) n))).toLp
            (fun ω ↦ ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) * X n ω) := by
              simpa using
                finiteWeightedCoordinate_sum_eq_toLp P X hX_rademacher
                  (fun n ↦ ((h : ℓ²(ℕ, ℝ)) n)) s
  have hmean :
      P[fun ω ↦ ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) * X n ω] = 0 := by
    -- Proof comment: each coordinate has mean zero, so the finite weighted sum is centered.
    have hInt :
        ∀ n ∈ s, Integrable (fun ω ↦ ((h : ℓ²(ℕ, ℝ)) n) * X n ω) P := by
      intro n hn
      simpa [smul_eq_mul, Pi.smul_apply] using
        ((memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul
          (((h : ℓ²(ℕ, ℝ)) n))).integrable (by norm_num)
    rw [integral_finset_sum s hInt]
    refine Finset.sum_eq_zero ?_
    intro n hn
    rcases rademacherCoordinate_mean_zero_variance_one P X hX_rademacher n with ⟨hmean_n, -⟩
    rw [integral_const_mul]
    simp [hmean_n]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  calc
    ‖rademacherSeriesOnFiniteSupport P X hX_rademacher h‖ ^ 2
        = ‖hmem.toLp (fun ω ↦ ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) * X n ω)‖ ^ 2 := by
            rw [htoLp]
    _ = P[fun ω ↦ (∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) * X n ω) ^ 2] := by
          exact toLpNormSq_eq_integral_sq hmem
    _ = Var[(fun ω ↦ ∑ n ∈ s, ((h : ℓ²(ℕ, ℝ)) n) * X n ω); P] := by
          symm
          exact ProbabilityTheory.variance_of_integral_eq_zero hmem.aemeasurable hmean
    _ = ∑ n ∈ s, (((h : ℓ²(ℕ, ℝ)) n) ^ 2) := by
          exact finiteWeightedRademacherSum_variance_eq_sum_sq P X hX_indep hX_rademacher
            (fun n ↦ ((h : ℓ²(ℕ, ℝ)) n)) s
    _ = ‖(h : ℓ²(ℕ, ℝ))‖ ^ 2 := by
          simpa [s] using (l2FinitelySupported_norm_sq_eq_sum_sq h).symm

private theorem rademacherSeriesOnFiniteSupport_norm_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    ∀ h : l2FinitelySupported,
      ‖rademacherSeriesOnFiniteSupport P X hX_rademacher h‖ ≤
        1 * ‖l2FinitelySupported.subtype h‖ := by
  intro h
  have hnorm :
      ‖rademacherSeriesOnFiniteSupport P X hX_rademacher h‖ = ‖h‖ :=
    ((rademacherSeriesOnFiniteSupport P X hX_rademacher).toLinearIsometry
      (rademacherSeriesOnFiniteSupport_isometry P X hX_indep hX_rademacher)).norm_map h
  simpa using hnorm.le

-- Proof sketch: `ℓ^f` is dense in `ℓ²(ℕ, ℝ)` by the canonical finite-support truncations, and the
-- isometry estimate above gives the norm bound needed for the standard dense-subspace extension
-- theorem.
/-- For Example 25.1, the finite-support isometry `R : ℓ^f → L²(P)` has its canonical continuous
extension to all of `ℓ²(ℕ, ℝ)`. -/
def rademacherSeries
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P) :
    ℓ²(ℕ, ℝ) →L[ℝ] Lp ℝ 2 P :=
  let _ := rademacherSeriesOnFiniteSupport_norm_le P X hX_indep hX_rademacher
  (rademacherSeriesOnFiniteSupport P X hX_rademacher).extendOfNorm l2FinitelySupported.subtype

/-- The canonical extension `rademacherSeries` agrees with the finite-sum operator `R` on
`ℓ^f`. -/
theorem rademacherSeries_eq_onFiniteSupport
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : l2FinitelySupported) :
    rademacherSeries P X hX_indep hX_rademacher h =
      rademacherSeriesOnFiniteSupport P X hX_rademacher h := by
  simpa [rademacherSeries] using
    LinearMap.extendOfNorm_eq
      (by simpa using denseRange_l2FinitelySupported_subtype)
      ⟨1, rademacherSeriesOnFiniteSupport_norm_le P X hX_indep hX_rademacher⟩
      h

/-- The canonical extension `rademacherSeries` is the unique continuous linear map on `ℓ²(ℕ, ℝ)`
whose restriction to `ℓ^f` is the finite-sum operator `R`. -/
theorem rademacherSeries_unique
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (R : ℓ²(ℕ, ℝ) →L[ℝ] Lp ℝ 2 P)
    (hR : R.toLinearMap.comp l2FinitelySupported.subtype =
      rademacherSeriesOnFiniteSupport P X hX_rademacher) :
    rademacherSeries P X hX_indep hX_rademacher = R := by
  simpa [rademacherSeries] using
    (LinearMap.extendOfNorm_unique
      (by simpa using denseRange_l2FinitelySupported_subtype)
      1
      (rademacherSeriesOnFiniteSupport_norm_le P X hX_indep hX_rademacher)
      R
      hR)

/-- Helper for Example 25.1: the truncation-weighted scalar sum agrees pointwise with the textbook
partial sum. -/
private theorem truncationRangeScalarSum_eq_partialSum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (h : ℓ²(ℕ, ℝ)) (N : ℕ) :
    (fun ω ↦
      ∑ n ∈ Finset.range N,
        (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n) * X n ω) =
      fun ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω := by
  -- Proof comment: every active truncation coefficient agrees with `h n`, so the finite scalar
  -- sum is exactly the textbook partial sum before passing to `L²(P)`.
  funext ω
  unfold partialSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [l2Truncation_apply_of_mem_range h hn]

/-- Helper for Example 25.1: the truncation scalar sum and the textbook partial sum define the
same `L²(P)` class. -/
private theorem truncationRange_toLp_eq_partialSum_toLp
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : ℓ²(ℕ, ℝ)) (N : ℕ) :
    (memLp_finset_sum (Finset.range N) fun n _ ↦ by
      simpa [smul_eq_mul, Pi.smul_apply] using
        (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul
          ((((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n))).toLp
      (fun ω ↦
        ∑ n ∈ Finset.range N,
          (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n) * X n ω) =
      (weightedPartialSum_memLp_two P X hX_rademacher (fun n ↦ h n) N).toLp
        (fun ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω) := by
  -- Proof comment: both `toLp` representatives come from the same raw function, so it suffices
  -- to prove pointwise equality of the two finite sums.
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  filter_upwards with ω
  simpa using congrFun (truncationRangeScalarSum_eq_partialSum P X h N) ω

/-- Helper for Example 25.1: the image of the `N`-th truncation under the extended series map is
the `L²(P)` class of the corresponding weighted partial sum. -/
private theorem rademacherSeries_truncation_eq_partialSum_toLp
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : ℓ²(ℕ, ℝ)) (N : ℕ) :
    rademacherSeries P X hX_indep hX_rademacher
        (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ))) =
      (weightedPartialSum_memLp_two P X hX_rademacher (fun n ↦ h n) N).toLp
        (fun ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω) :=
by
  -- Route correction: the old proof normalized coefficients inside the `Lp` world. The new route
  -- stays in raw scalar functions until the last `toLp` adapter.
  calc
    rademacherSeries P X hX_indep hX_rademacher
        (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)))
      = rademacherSeriesOnFiniteSupport P X hX_rademacher (l2Truncation h N) := by
          simpa using
            rademacherSeries_eq_onFiniteSupport P X hX_indep hX_rademacher (l2Truncation h N)
    _ = ∑ n ∈ Finset.range N,
          (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n) •
            rademacherCoordinate P X hX_rademacher n := by
          -- Proof comment: evaluate the finite-support operator on the canonical support set of
          -- the truncation.
          simpa using
            rademacherSeriesOnFiniteSupport_apply P X hX_rademacher (l2Truncation h N)
              (l2Truncation_support_subset_range h N)
    _ =
        (memLp_finset_sum (Finset.range N) fun n _ ↦ by
          simpa [smul_eq_mul, Pi.smul_apply] using
            (memLp_two_of_hasLaw_symmetricRademacher P (hX_rademacher n)).const_smul
              ((((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n))).toLp
          (fun ω ↦
            ∑ n ∈ Finset.range N,
              (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n) * X n ω) := by
          -- Proof comment: apply the finite weighted-sum formula directly to the truncation
          -- coefficients before any textbook normalization.
          simpa [smul_eq_mul, Pi.smul_apply] using
            (finiteWeightedCoordinate_sum_eq_toLp P X hX_rademacher
              (fun n ↦ (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ)) n))
              (Finset.range N))
    _ =
        (weightedPartialSum_memLp_two P X hX_rademacher (fun n ↦ h n) N).toLp
          (fun ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω) := by
            -- Proof comment: convert the raw truncation scalar sum to the textbook partial sum
            -- by the dedicated pointwise equality.
            exact truncationRange_toLp_eq_partialSum_toLp P X hX_rademacher h N

/-- Helper for Example 25.1: the extended series map sends the canonical truncations of `h` to a
convergent sequence in `L²(P)`. -/
private theorem rademacherSeries_truncation_tendsto
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : ℓ²(ℕ, ℝ)) :
    Tendsto
      (fun N ↦
        rademacherSeries P X hX_indep hX_rademacher
          (((l2Truncation h N : l2FinitelySupported) : ℓ²(ℕ, ℝ))))
      atTop
      (𝓝 (rademacherSeries P X hX_indep hX_rademacher h)) := by
  -- Proof comment: continuity of the extended linear map transports the convergence of the
  -- truncations in `ℓ²(ℕ, ℝ)`.
  exact
    ((rademacherSeries P X hX_indep hX_rademacher).continuous.tendsto _).comp
      (l2Truncation_tendsto h)

-- Proof sketch: approximate `h ∈ ℓ²` by the canonical truncations in `ℓ^f`, apply the extension
-- property of `rademacherSeries`, and identify the truncation images with the textbook partial sums
-- `∑_{n < N} h_n X_n`.
/-- Example 25.1: for `h ∈ ℓ²(ℕ, ℝ)`, the weighted partial sums converge in `L²(P)` to the
extended random series `R(h)`. -/
theorem rademacherSeries_partialSums_is_l2_limit
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (h : ℓ²(ℕ, ℝ)) :
    TendstoInLp 2 P
      (fun N ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω)
      (rademacherSeries P X hX_indep hX_rademacher h) := by
  -- Route correction: the final theorem now only assembles the convergence of truncation images
  -- with a dedicated per-`N` bridge to the textbook partial sums.
  refine
    ⟨fun N ↦ weightedPartialSum_memLp_two P X hX_rademacher (fun n ↦ h n) N,
      Lp.memLp (rademacherSeries P X hX_indep hX_rademacher h), ?_⟩
  have hpartial :
      Tendsto
        (fun N ↦
          (weightedPartialSum_memLp_two P X hX_rademacher (fun n ↦ h n) N).toLp
            (fun ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω))
        atTop
        (𝓝 (rademacherSeries P X hX_indep hX_rademacher h)) := by
    -- Proof comment: rewrite each truncation image as the corresponding weighted partial sum.
    exact
      (rademacherSeries_truncation_tendsto P X hX_indep hX_rademacher h).congr' <|
        Filter.Eventually.of_forall fun N ↦
          rademacherSeries_truncation_eq_partialSum_toLp P X hX_indep hX_rademacher h N
  simpa [Lp.toLp_coeFn] using hpartial

private theorem memℓp_two_of_summable_sq (h : ℕ → ℝ) (hh_sq : Summable fun n ↦ h n ^ 2) :
    Memℓp h 2 := by
  refine memℓp_gen ?_
  simpa [pow_two, Real.norm_eq_abs, sq_abs] using hh_sq

-- Proof sketch: package the coefficient sequence `h` as an element of `ℓ²(ℕ, ℝ)` and apply
-- `rademacherSeries_partialSums_is_l2_limit`.
/-- As a corollary to Example 25.1, if `X 0, X 1, …` are independent random variables with the
symmetric `{-1, 1}`-valued law on `ℝ` and `∑ (h n)^2 < ∞`, then the weighted partial sums
`S_N(ω) = ∑_{n < N} h n * X n ω` converge in `L²(P)` to a square-integrable random variable.
This existential corollary is the direct consequence of the canonical operator
`rademacherSeries : ℓ²(ℕ, ℝ) → L²(P)`. -/
theorem exists_l2_limit_of_iid_rademacher_series
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (h : ℕ → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_rademacher : ∀ n, HasLaw (X n) symmetricRademacherRealLaw P)
    (hh_sq : Summable fun n ↦ h n ^ 2) :
    ∃ R : Ω → ℝ,
      TendstoInLp 2 P
        (fun N ω ↦ partialSum (fun n ω ↦ h n * X n ω) N ω)
        R := by
  let hL2 : ℓ²(ℕ, ℝ) := ⟨h, memℓp_two_of_summable_sq h hh_sq⟩
  refine ⟨rademacherSeries P X hX_indep hX_rademacher hL2, ?_⟩
  exact rademacherSeries_partialSums_is_l2_limit P X hX_indep hX_rademacher hL2

end ProbabilityTheory
