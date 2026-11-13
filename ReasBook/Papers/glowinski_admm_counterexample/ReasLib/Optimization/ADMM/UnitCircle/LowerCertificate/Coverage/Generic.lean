/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Coverage

/-- Adjacent closed intervals in any finite chain cover the interval from
its first endpoint to its last. Monotonicity of the intermediate cuts is not
needed: the first crossing already supplies a covering interval. -/
theorem interval_chain_cover (n : ℕ) (cuts : Fin (n + 2) → ℝ) {x : ℝ}
    (hleft : cuts 0 ≤ x) (hright : x ≤ cuts (Fin.last (n + 1))) :
    ∃ i : Fin (n + 1), x ∈ Set.Icc (cuts i.castSucc) (cuts i.succ) := by
  induction n with
  | zero => exact ⟨0, hleft, hright⟩
  | succ n ih =>
    by_cases hfirst : x ≤ cuts 1
    · exact ⟨0, hleft, hfirst⟩
    · have htailLeft : (fun i : Fin (n + 2) ↦ cuts i.succ) 0 ≤ x :=
        le_of_not_ge hfirst
      have htailRight : x ≤ (fun i : Fin (n + 2) ↦ cuts i.succ) (Fin.last (n + 1)) := by
        simpa using hright
      obtain ⟨i, hi⟩ := ih (fun i : Fin (n + 2) ↦ cuts i.succ) htailLeft htailRight
      refine ⟨i.succ, ?_, ?_⟩
      · simpa only [Fin.succ_castSucc] using hi.1
      · exact hi.2

/-- Strict positivity on each of the closed subintervals gives strict
positivity throughout the full interval, including every shared endpoint. -/
theorem positive_of_interval_chain (n : ℕ) (cuts : Fin (n + 2) → ℝ)
    (f : ℝ → ℝ)
    (hleaf : ∀ i : Fin (n + 1), ∀ x ∈ Set.Icc (cuts i.castSucc) (cuts i.succ), 0 < f x)
    {x : ℝ} (hleft : cuts 0 ≤ x) (hright : x ≤ cuts (Fin.last (n + 1))) :
    0 < f x := by
  obtain ⟨i, hi⟩ := interval_chain_cover n cuts hleft hright
  exact hleaf i x hi

end ADMM.UnitCircle.LowerCertificate.Coverage
