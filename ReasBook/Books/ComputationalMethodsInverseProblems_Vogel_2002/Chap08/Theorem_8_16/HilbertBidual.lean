/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Function.L2Space

public section

noncomputable section

namespace VariationalRegularization.BVCompactness

/-- A real Hilbert space fills its continuous bidual.  This is a direct
twofold application of Riesz representation and does not require finite
dimension. -/
lemma hilbert_inclusionInDoubleDual_surjective
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro Φ
  let J := InnerProductSpace.toDual ℝ E
  let ψ : StrongDual ℝ E := Φ.comp J.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨J.symm ψ, ?_⟩
  ext g
  obtain ⟨x, rfl⟩ := J.surjective g
  change J x (J.symm ψ) = Φ (J x)
  rw [InnerProductSpace.toDual_apply_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  rfl

/-- Consequently the canonical weak-to-weak-star bidual map of a real
Hilbert space has closed range, indeed its range is the entire bidual. -/
lemma hilbert_inclusionInDoubleDualWeak_range_isClosed
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsClosed (Set.range (NormedSpace.inclusionInDoubleDualWeak ℝ E)) := by
  have hsurj : Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
    intro Φ
    obtain ⟨x, hx⟩ := hilbert_inclusionInDoubleDual_surjective E Φ.toStrongDual
    refine ⟨toWeakSpace ℝ E x, ?_⟩
    apply WeakDual.toStrongDual.injective
    exact hx
  rw [Set.range_eq_univ.mpr hsurj]
  exact isClosed_univ

/-- The critical exponent in spatial dimension two is two; its `L²` space
therefore has closed weak-star bidual range for every measure. -/
lemma lpTwo_inclusionInDoubleDualWeak_range_isClosed
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) :
    IsClosed (Set.range
      (NormedSpace.inclusionInDoubleDualWeak ℝ (MeasureTheory.Lp ℝ 2 μ))) :=
  hilbert_inclusionInDoubleDualWeak_range_isClosed (MeasureTheory.Lp ℝ 2 μ)

/-- Equality with the Hilbert exponent transports the result without
rewriting under the normed-space instances carried by the weak topology. -/
lemma lp_inclusionInDoubleDualWeak_range_isClosed_of_eq_two
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p = 2) :
    IsClosed (Set.range
      (NormedSpace.inclusionInDoubleDualWeak ℝ (MeasureTheory.Lp ℝ p μ))) := by
  subst p
  exact lpTwo_inclusionInDoubleDualWeak_range_isClosed μ

end VariationalRegularization.BVCompactness
