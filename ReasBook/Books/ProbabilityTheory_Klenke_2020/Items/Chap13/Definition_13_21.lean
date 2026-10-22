/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_59

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

section

/-- For a defective distribution function, the textbook endpoint value `sup (range F)` is the
total mass of the associated Lebesgue--Stieltjes measure. -/
theorem sSup_range_eq_measure_univ_toReal (F : StieltjesFunction ℝ)
    [hF : IsDefectiveDistributionFunction F] :
    sSup (range F) = (F.measure univ).toReal := by
  have h_atTop : Tendsto F atTop (𝓝 (sSup (range F))) := by
    simpa [sSup_range] using
      (tendsto_atTop_ciSup F.mono
        ⟨1, fun y hy ↦ by
          rcases hy with ⟨x, rfl⟩
          exact hF.le_one x⟩)
  have h_nonneg : 0 ≤ sSup (range F) := by
    refine le_trans (hF.nonneg 0) ?_
    exact le_csSup
      ⟨1, fun y hy ↦ by
        rcases hy with ⟨x, rfl⟩
        exact hF.le_one x⟩
      (mem_range_self 0)
  rw [F.measure_univ hF.tendsto_atBot_zero h_atTop]
  simp [h_nonneg]

/-- Definition 13.21: a sequence of defective distribution functions converges weakly to `F` when
`Fₙ x → F x` at every continuity point `x` of `F`, and the endpoint values satisfy the
sub-probability endpoint condition `F(∞) ≥ limsup Fₙ(∞)`. Using
`sSup_range_eq_measure_univ_toReal`, this endpoint value is the total mass of the associated
Lebesgue--Stieltjes measure. For honest distribution functions, the endpoint condition is
automatic because every endpoint value is `1`. -/
def distribution_function_weakly_converges_to
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ) : Prop :=
  IsDefectiveDistributionFunction F ∧
    (∀ n, IsDefectiveDistributionFunction (Fs n)) ∧
    (∀ ⦃x : ℝ⦄, ContinuousAt F x → Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x))) ∧
      (F.measure univ).toReal ≥ limsup (fun n ↦ ((Fs n).measure univ).toReal) atTop

/-- The source-facing weak convergence predicate for defective distribution functions is
exactly the textbook criterion: pointwise convergence at every continuity point of the limit
function together with the endpoint limsup inequality. -/
theorem distribution_function_weakly_converges_to_iff
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ) :
    distribution_function_weakly_converges_to Fs F ↔
      IsDefectiveDistributionFunction F ∧
        (∀ n, IsDefectiveDistributionFunction (Fs n)) ∧
        (∀ ⦃x : ℝ⦄, ContinuousAt F x → Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x))) ∧
          (F.measure univ).toReal ≥ limsup (fun n ↦ ((Fs n).measure univ).toReal) atTop :=
  Iff.rfl

/-- Helper for Definition 13.21: every value of a defective distribution function is bounded by
its endpoint mass. -/
lemma stieltjesValue_le_measureUnivToReal (G : StieltjesFunction ℝ)
    [hG : IsDefectiveDistributionFunction G] (x : ℝ) :
    G x ≤ (G.measure univ).toReal := by
  -- Rewrite the endpoint mass as the supremum of the range and compare with a range element.
  rw [← sSup_range_eq_measure_univ_toReal G]
  exact le_csSup
    ⟨1, fun y hy ↦ by
      rcases hy with ⟨z, rfl⟩
      exact hG.le_one z⟩
    (mem_range_self x)

/-- Helper for Definition 13.21: above every real threshold there is a continuity point of a
defective distribution function. -/
lemma exists_continuityPoint_gt (F : StieltjesFunction ℝ)
    [IsDefectiveDistributionFunction F] (x : ℝ) :
    ∃ z > x, ContinuousAt F z := by
  let s : Set ℝ := {y | ¬ ContinuousAt F y}
  have hs_countable : s.Countable := F.mono.countable_not_continuousAt
  have hs_dense : Dense sᶜ := hs_countable.dense_compl ℝ
  -- Pick a point of the dense continuity set inside the open ray `(x, ∞)`.
  obtain ⟨z, hz_mem, hz_gt⟩ := hs_dense.exists_mem_open (U := Set.Ioi x) isOpen_Ioi
    ⟨x + 1, lt_add_of_pos_right x zero_lt_one⟩
  refine ⟨z, hz_gt, ?_⟩
  simpa [s] using hz_mem

/-- Helper for Definition 13.21: continuity-point convergence bounds each value of the limit
distribution function by the liminf of the approximating endpoint masses. -/
lemma distributionFunctionValue_le_liminfEndpointMass
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDefectiveDistributionFunction F)
    (hFs : ∀ n, IsDefectiveDistributionFunction (Fs n))
    (hcont : ∀ ⦃x : ℝ⦄, ContinuousAt F x → Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x)))
    (x : ℝ) :
    F x ≤ liminf (fun n ↦ ((Fs n).measure univ).toReal) atTop := by
  letI : IsDefectiveDistributionFunction F := hF
  obtain ⟨z, hz_gt, hz_cont⟩ := exists_continuityPoint_gt F x
  have hxz : F x ≤ F z := F.mono hz_gt.le
  have hz_tendsto : Tendsto (fun n ↦ Fs n z) atTop (𝓝 (F z)) := hcont hz_cont
  have hz_liminf : liminf (fun n ↦ Fs n z) atTop = F z := by
    simpa using hz_tendsto.liminf_eq
  have h_eventually :
      ∀ᶠ n in atTop, Fs n z ≤ ((Fs n).measure univ).toReal :=
    Filter.Eventually.of_forall fun n ↦ by
      letI : IsDefectiveDistributionFunction (Fs n) := hFs n
      exact stieltjesValue_le_measureUnivToReal (Fs n) z
  have h_endpoint_le_one : ∀ n, ((Fs n).measure univ).toReal ≤ 1 := by
    intro n
    rw [← sSup_range_eq_measure_univ_toReal (Fs n)]
    exact csSup_le ⟨Fs n 0, mem_range_self 0⟩ fun y hy ↦ by
      rcases hy with ⟨w, rfl⟩
      exact (hFs n).le_one w
  have h_liminf_le :
      liminf (fun n ↦ Fs n z) atTop ≤
        liminf (fun n ↦ ((Fs n).measure univ).toReal) atTop := by
    -- Compare liminfs using the eventual pointwise domination by endpoint masses.
    refine Filter.liminf_le_liminf h_eventually ?_ ?_
    · exact Filter.isBoundedUnder_of_eventually_ge <|
        Filter.Eventually.of_forall fun n ↦ (hFs n).nonneg z
    · exact Filter.isCoboundedUnder_ge_of_le atTop h_endpoint_le_one
  -- First move from `x` to a larger continuity point `z`, then pass to the liminf.
  calc
    F x ≤ F z := hxz
    _ = liminf (fun n ↦ Fs n z) atTop := by symm; exact hz_liminf
    _ ≤ liminf (fun n ↦ ((Fs n).measure univ).toReal) atTop := h_liminf_le

-- Proof sketch: use monotonicity of defective distribution functions to compare `F(∞)` and
-- `Fₙ(∞)` with values at large continuity points of `F`; then pass to the limit in `n` and let
-- the continuity points tend to `+∞`.
/-- The continuity-point convergence part of weak convergence forces the endpoint value of the
limit distribution function to be bounded above by the limit inferior of the endpoint values of
the approximating sequence. -/
theorem distribution_function_at_top_value_le_liminf_of_continuity_convergence
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (hF : IsDefectiveDistributionFunction F)
    (hFs : ∀ n, IsDefectiveDistributionFunction (Fs n))
    (hcont : ∀ ⦃x : ℝ⦄, ContinuousAt F x → Tendsto (fun n ↦ Fs n x) atTop (𝓝 (F x))) :
    (F.measure Set.univ).toReal ≤ liminf (fun n ↦ ((Fs n).measure Set.univ).toReal) atTop := by
  letI : IsDefectiveDistributionFunction F := hF
  -- Rewrite the endpoint value as the supremum of the range and bound every range point.
  rw [← sSup_range_eq_measure_univ_toReal F]
  refine csSup_le ?_ ?_
  · exact ⟨F 0, mem_range_self 0⟩
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact distributionFunctionValue_le_liminfEndpointMass Fs F hF hFs hcont x

-- Proof sketch: combine the endpoint limsup inequality from
-- `distribution_function_weakly_converges_to_iff` with
-- `distribution_function_at_top_value_le_liminf_of_continuity_convergence`; then `liminf` and
-- `limsup` squeeze the endpoint values to the same limit.
/-- Under weak convergence of defective distribution functions, the endpoint values `Fₙ(∞)`
converge to `F(∞)`. -/
theorem tendsto_distribution_function_at_top_value_of_weak_convergence
    (Fs : ℕ → StieltjesFunction ℝ) (F : StieltjesFunction ℝ)
    (h : distribution_function_weakly_converges_to Fs F) :
    Tendsto (fun n ↦ ((Fs n).measure univ).toReal) atTop
      (𝓝 ((F.measure univ).toReal)) := by
  rcases h with ⟨hF, hFs, hcont, hlimsup⟩
  have h_liminf :
      (F.measure univ).toReal ≤ liminf (fun n ↦ ((Fs n).measure univ).toReal) atTop :=
    distribution_function_at_top_value_le_liminf_of_continuity_convergence Fs F hF hFs hcont
  have h_bddAbove :
      Filter.IsBoundedUnder (fun x y : ℝ ↦ x ≤ y) atTop
        (fun n ↦ ((Fs n).measure univ).toReal) := by
    -- The endpoint masses are uniformly bounded above by `1`.
    refine Filter.isBoundedUnder_of_eventually_le (a := 1) <|
      Filter.Eventually.of_forall fun n ↦ ?_
    rw [← sSup_range_eq_measure_univ_toReal (Fs n)]
    exact csSup_le ⟨Fs n 0, mem_range_self 0⟩ fun y hy ↦ by
      rcases hy with ⟨z, rfl⟩
      exact (hFs n).le_one z
  have h_bddBelow :
      Filter.IsBoundedUnder (fun x y : ℝ ↦ x ≥ y) atTop
        (fun n ↦ ((Fs n).measure univ).toReal) := by
    -- Nonnegativity of `ENNReal.toReal` gives a global lower bound by `0`.
    refine Filter.isBoundedUnder_of_eventually_ge (a := 0) <|
      Filter.Eventually.of_forall fun n ↦ ?_
    exact ENNReal.toReal_nonneg
  -- The liminf lower bound and the defining limsup upper bound force convergence.
  exact tendsto_of_le_liminf_of_limsup_le h_liminf hlimsup h_bddAbove h_bddBelow

end
