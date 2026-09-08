module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Algebra

public section

open scoped BigOperators

namespace Asymptotics.IsUniformRemainderOn

universe u v w

/-- A finite sum of uniform remainders of one order has coefficient equal to the
sum of the individual coefficients. -/
theorem finsetSum
    {Θ : Type u} {ι : Type v} {E : Type w} [SeminormedAddCommGroup E]
    (u : Finset ι) {R : ι → Θ → ℝ → E} {s : Set Θ} {C : ι → ℝ} {q : ℝ}
    (hR : ∀ i ∈ u, IsUniformRemainderOn (R i) s (C i) q) :
    IsUniformRemainderOn (fun θ ε ↦ ∑ i ∈ u, R i θ ε) s
      (∑ i ∈ u, C i) q := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      refine (isBigOWith_iff (fun θ ε ↦ ∑ i ∈ (∅ : Finset ι), R i θ ε) s
        (∑ i ∈ (∅ : Finset ι), C i) q).mp ?_
      apply IsBigOWith.of_bound
      apply Filter.Eventually.of_forall
      intro z
      simp only [Finset.sum_empty, norm_zero, zero_mul, le_refl]
  | @insert i u hi ih =>
      have hsum : IsUniformRemainderOn (fun θ ε ↦ ∑ j ∈ u, R j θ ε) s
          (∑ j ∈ u, C j) q :=
        ih (fun j hj ↦ hR j (Finset.mem_insert_of_mem hj))
      have hinsert : IsUniformRemainderOn (R i) s (C i) q :=
        hR i (Finset.mem_insert_self i u)
      have hadd := add hinsert hsum
      simpa only [Finset.sum_insert hi] using hadd

end Asymptotics.IsUniformRemainderOn
