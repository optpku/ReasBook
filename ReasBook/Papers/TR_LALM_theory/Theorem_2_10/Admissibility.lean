/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Algorithm_2_1.Iteration

public section

namespace LALM.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- A run is admissible when every completed-iteration segment lies in the
regularity region. -/
def IsAdmissible (run : Run f c ρ β x₀ multiplier₀)
    (h : EqualityConstrained.Regularity f c) : Prop :=
  ∀ k, segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region

/-- Global admissibility is pointwise segment containment at every iteration. -/
theorem isAdmissible_iff (run : Run f c ρ β x₀ multiplier₀)
    (h : EqualityConstrained.Regularity f c) :
    run.IsAdmissible h ↔
      ∀ k, segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region := Iff.rfl

/-- Every segment of a globally admissible run lies in the regularity region. -/
theorem IsAdmissible.segment_subset {run : Run f c ρ β x₀ multiplier₀}
    {h : EqualityConstrained.Regularity f c} (h_admissible : run.IsAdmissible h)
    (k : ℕ) : segment ℝ (run.point k) (run.point (k + 1)) ⊆ h.region :=
  (isAdmissible_iff run h).1 h_admissible k

/-- A globally admissible run has every finite prefix admissible. -/
theorem IsAdmissible.prefix {run : Run f c ρ β x₀ multiplier₀}
    {h : EqualityConstrained.Regularity f c} (h_admissible : run.IsAdmissible h)
    (K : ℕ) : run.IsAdmissiblePrefix h K :=
  (isAdmissiblePrefix_iff run h K).2 (fun k _ ↦ h_admissible.segment_subset k)

/-- Global admissibility is equivalent to admissibility of every finite prefix. -/
theorem isAdmissible_iff_allPrefixes (run : Run f c ρ β x₀ multiplier₀)
    (h : EqualityConstrained.Regularity f c) :
    run.IsAdmissible h ↔ ∀ K, run.IsAdmissiblePrefix h K := by
  constructor
  · intro h_admissible K
    exact h_admissible.prefix K
  · intro h_prefix k
    exact (isAdmissiblePrefix_iff run h (k + 1)).1
      (h_prefix (k + 1)) k (Nat.lt_succ_self k)

end LALM.Run

end
