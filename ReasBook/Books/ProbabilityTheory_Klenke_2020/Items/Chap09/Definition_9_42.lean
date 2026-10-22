/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The positive-time history `(X₁(ω), …, Xₙ(ω))` preceding time `n + 1`. -/
def binaryModelHistory {T : ℕ} (X : Fin (T + 1) → Ω → ℝ) (n : Fin T) (ω : Ω) :
    Fin n.1 → ℝ :=
  fun i ↦ X ⟨i.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt i.2) (Nat.lt_succ_of_lt n.2)⟩ ω

/-- The `i`th entry of the history before time `n + 1` is the process value at time `i + 1`. -/
@[simp] theorem binaryModelHistory_apply {T : ℕ} (X : Fin (T + 1) → Ω → ℝ) (n : Fin T) (ω : Ω)
    (i : Fin n.1) :
    binaryModelHistory X n ω i =
      X ⟨i.1 + 1, lt_of_le_of_lt (Nat.succ_le_of_lt i.2) (Nat.lt_succ_of_lt n.2)⟩ ω := rfl

variable [MeasurableSpace Ω]

/-- Definition 9.42: a finite real-valued process is a binary model if it is a stochastic
process, starts from a deterministic initial value, and each later value is a deterministic
function of the previous values `X₁, …, Xₙ` and a `{-1,1}`-valued innovation at time `n + 1`. -/
def IsBinaryModel {T : ℕ} (X : Fin (T + 1) → Ω → ℝ) : Prop :=
  IsStochasticProcess X ∧
    ∃ x0 : ℝ,
      X 0 = (fun _ ↦ x0) ∧
        ∃ D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1},
          (∀ n, Measurable (D n)) ∧
            ∃ f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ,
              ∀ n : Fin T,
                X ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ =
                  fun ω ↦ f n (binaryModelHistory X n ω) (D n ω)

namespace IsBinaryModel

variable {T : ℕ} {X : Fin (T + 1) → Ω → ℝ}

/-- Every binary model is, in particular, a stochastic process. -/
theorem isStochasticProcess (hX : IsBinaryModel X) : IsStochasticProcess X :=
  hX.1

-- Proof sketch: project to the existence part of `IsBinaryModel`; this recovers the deterministic
-- initial value, the `{-1,1}`-valued innovations, and the update maps witnessing the binary
-- splitting representation.
/-- A binary model admits measurable `{-1,1}`-valued innovations and deterministic update maps
realizing each time `n + 1` from the previous positive-time history. -/
theorem exists_representation (hX : IsBinaryModel X) :
    ∃ x0 : ℝ,
      X 0 = (fun _ ↦ x0) ∧
        ∃ D : Fin T → Ω → {x : ℝ // x = -1 ∨ x = 1},
          (∀ n, Measurable (D n)) ∧
            ∃ f : ∀ n : Fin T, (Fin n.1 → ℝ) → {x : ℝ // x = -1 ∨ x = 1} → ℝ,
              ∀ n : Fin T,
                X ⟨n.1 + 1, Nat.succ_lt_succ n.2⟩ =
                  fun ω ↦ f n (binaryModelHistory X n ω) (D n ω) :=
  hX.2

end IsBinaryModel

/-- If every finite truncation of a discrete real process is a binary model, then each time
marginal is strongly measurable. -/
theorem binaryModelTruncations_stronglyMeasurable {X : ℕ → Ω → ℝ}
    (hX_binary : ∀ T, IsBinaryModel (fun i : Fin (T + 1) ↦ X i.1)) :
    ∀ n, StronglyMeasurable (X n) := by
  intro n
  exact ((hX_binary n).isStochasticProcess ⟨n, Nat.lt_succ_self n⟩).stronglyMeasurable

/- The filtration `σ(X)` mentioned in Definition 9.42 is the natural filtration of the process,
formalized in mathlib by `MeasureTheory.Filtration.natural`. -/
recall MeasureTheory.Filtration.natural

end ProbabilityTheory
