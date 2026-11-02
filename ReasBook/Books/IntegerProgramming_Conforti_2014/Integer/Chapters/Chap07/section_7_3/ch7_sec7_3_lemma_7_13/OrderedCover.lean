module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Embedding.Basic

public section

variable {n : ℕ}

/-
Source-facing ordered-cover primitives for Lemma 7.13.
-/
namespace OrderedFlowCover

/-- `enumerates C coverOrder` means that the finite ordering
`coverOrder : Fin C.card ↪ Fin n` enumerates the elements of the cover `C`. -/
def enumerates
    (C : Finset (Fin n)) (coverOrder : Fin C.card ↪ Fin n) : Prop :=
  Set.range coverOrder = (↑C : Set (Fin n))

/-- The ordered cover coefficient `a_{j_h}` attached to the `h`-th element of `coverOrder`,
written with the source indexing convention `h = 1, 2, ...`. -/
def weight
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n) : ℕ → ℝ
  | 0 => 0
  | h + 1 =>
      if hh : h < C.card then a (coverOrder ⟨h, hh⟩) else 0

/-- The source coefficient at position `h + 1` is `a` evaluated on the `h`-th entry of
`coverOrder` whenever that position lies in the ordered cover. -/
theorem weight_succ
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n)
    {h : ℕ} (hh : h < C.card) :
    weight C a coverOrder (h + 1) = a (coverOrder ⟨h, hh⟩) := by
  simp [weight, hh]

/-- The partial sums `μ_h = a_{j_1} + ⋯ + a_{j_h}` of the ordered cover coefficients. -/
def partialSum
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n) : ℕ → ℝ
  | 0 => 0
  | h + 1 =>
      partialSum C a coverOrder h +
        weight C a coverOrder (h + 1)

/-- The source partial sums satisfy `μ_{h+1} = μ_h + a_{j_{h+1}}`. -/
theorem partialSum_succ
    (C : Finset (Fin n)) (a : Fin n → ℝ) (coverOrder : Fin C.card ↪ Fin n) (h : ℕ) :
    partialSum C a coverOrder (h + 1) =
      partialSum C a coverOrder h +
        weight C a coverOrder (h + 1) := by
  rfl

/-- `isCutIndex a C coverOrder λ r` means that `r` is the last ordered cover
position among the first `C.card` cover coefficients whose coefficient still exceeds `λ`. -/
def isCutIndex
    (a : Fin n → ℝ) (C : Finset (Fin n)) (coverOrder : Fin C.card ↪ Fin n)
    (lam : ℝ) (r : ℕ) : Prop :=
  1 ≤ r ∧
    r ≤ C.card ∧
      lam < weight C a coverOrder r ∧
        ∀ h, r < h → h ≤ C.card → weight C a coverOrder h ≤ lam

end OrderedFlowCover

end
