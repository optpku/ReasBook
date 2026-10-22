/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

namespace ProbabilityTheory

universe uΩ uT uE

variable {Ω : Type uΩ} {T : Type uT} {E : Type uE}
variable [MeasurableSpace Ω] [MeasurableSpace E]

variable {P : Measure Ω} {σ : T → T} {X : T → Ω → E}

-- Proof sketch: this is the canonical owner-level theorem
-- `map_eq_iff_forall_finset_map_restrict_eq` specialized to the shifted family
-- `fun t ω ↦ X (σ t) ω`; for `I = ℕ`, `ℕ+`, or `ℤ` with `σ n = n + 1`, this is
-- exactly the textbook reformulation of (20.1) as equality of the full process laws.
/-- Remark 20.2: for index sets such as `ℕ`, `ℕ+`, or `ℤ`, condition `(20.1)` is equivalent to the
equality of the law of the shifted process `(X_{n+1})` and the law of the original process
`(X_n)`. Here this is stated in the canonical process-law form for an arbitrary self-map `σ` on the
index set. -/
theorem shifted_process_law_eq_iff_finiteDimensionalDistributions_eq [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω ↦ (X · ω)) P)
    (hσX : AEMeasurable (fun ω ↦ fun t ↦ X (σ t) ω) P) :
    P.map (fun ω ↦ fun t ↦ X (σ t) ω) = P.map (fun ω ↦ (X · ω)) ↔
      ∀ I : Finset T,
        P.map (fun ω ↦ I.restrict (fun t ↦ X (σ t) ω)) =
          P.map (fun ω ↦ I.restrict (X · ω)) := by
  simpa using (map_eq_iff_forall_finset_map_restrict_eq hσX hX)

end ProbabilityTheory
