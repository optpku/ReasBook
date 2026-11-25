/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Reflexivity from two dual representations

Hölder's inequality constructs maps from conjugate `Lp` spaces to their
continuous duals, but does not prove that those maps are surjective.  This
file proves the bidual consequence from two explicit dual-representation
statements. Their finite-measure `Lp` proofs are supplied by `LpDual.lean`.
-/

public section

noncomputable section

namespace VariationalRegularization.BVCompactness

/-- Two mutually representing symmetric dual pairings make the canonical
bidual inclusion surjective. -/
lemma inclusionInDoubleDual_surjective_of_dualPair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] StrongDual ℝ F) (Q : F →L[ℝ] StrongDual ℝ E)
    (hflip : ∀ x y, P x y = Q y x)
    (hP : Function.Surjective P) (hQ : Function.Surjective Q) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro Φ
  obtain ⟨x, hx⟩ := hP (Φ.comp Q)
  refine ⟨x, ?_⟩
  ext g
  obtain ⟨y, rfl⟩ := hQ g
  change Q y x = Φ (Q y)
  rw [← hflip, hx]
  rfl

/-- The same representation data fill the weak-star bidual, so the range
of the canonical weak-space map is closed. -/
lemma inclusionInDoubleDualWeak_range_isClosed_of_dualPair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] StrongDual ℝ F) (Q : F →L[ℝ] StrongDual ℝ E)
    (hflip : ∀ x y, P x y = Q y x)
    (hP : Function.Surjective P) (hQ : Function.Surjective Q) :
    IsClosed (Set.range (NormedSpace.inclusionInDoubleDualWeak ℝ E)) := by
  have hsurj : Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
    intro Φ
    obtain ⟨x, hx⟩ := inclusionInDoubleDual_surjective_of_dualPair P Q hflip hP hQ
      Φ.toStrongDual
    refine ⟨toWeakSpace ℝ E x, ?_⟩
    apply WeakDual.toStrongDual.injective
    exact hx
  rw [Set.range_eq_univ.mpr hsurj]
  exact isClosed_univ

/-- A general real `Lp` closed-bidual-range theorem with its two
Hölder dual-representation inputs visible in the statement. These are exact
representation properties of continuous linear functionals, not the desired
compactness or closed-range conclusion. -/
lemma lp_inclusionInDoubleDualWeak_range_isClosed_of_pairingSurjective
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] [q.HolderConjugate p]
    (hp : Function.Surjective ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q))
    (hq : Function.Surjective ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p)) :
    IsClosed (Set.range
      (NormedSpace.inclusionInDoubleDualWeak ℝ (MeasureTheory.Lp ℝ p μ))) := by
  apply inclusionInDoubleDualWeak_range_isClosed_of_dualPair
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q)
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p) _ hp hq
  intro f g
  rw [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.lpPairing_eq_integral]
  congr 1
  funext x
  exact mul_comm _ _

end VariationalRegularization.BVCompactness
