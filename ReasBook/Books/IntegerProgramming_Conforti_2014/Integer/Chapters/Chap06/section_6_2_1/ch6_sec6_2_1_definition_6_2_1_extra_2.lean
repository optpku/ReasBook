import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

namespace Function

variable {E : Type*}

/-- Definition 6.2.1-extra-2 (1): a real-valued function on a real vector space is subadditive if
`g (x + y) ≤ g x + g y` for all vectors `x, y`. Specializing `E` to `Fin n → ℝ` recovers the
textbook `ℝ^n` formulation. -/
def Subadditive [Add E] (g : E → ℝ) : Prop :=
  ∀ x y : E, g (x + y) ≤ g x + g y

namespace Subadditive

section Zero

variable [AddZeroClass E] {g : E → ℝ}

/-- A subadditive real-valued map takes a nonnegative value at the origin. -/
theorem map_zero_nonneg (hg : g.Subadditive) : 0 ≤ g 0 := by
  have h : g 0 ≤ g 0 + g 0 := by
    simpa using hg (0 : E) 0
  have h' := add_le_add_left h (-g 0)
  simpa [add_assoc, add_left_comm, add_comm] using h'

end Zero

variable [Add E] {f g : E → ℝ}

/-- The pointwise maximum of two subadditive real-valued maps is subadditive. -/
theorem max (hf : f.Subadditive) (hg : g.Subadditive) :
    (fun x ↦ max (f x) (g x)).Subadditive := by
  intro u v
  refine max_le ?_ ?_
  · calc
      f (u + v) ≤ f u + f v := hf u v
      _ ≤ Max.max (f u) (g u) + Max.max (f v) (g v) :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      g (u + v) ≤ g u + g v := hg u v
      _ ≤ Max.max (f u) (g u) + Max.max (f v) (g v) :=
        add_le_add (le_max_right _ _) (le_max_right _ _)

end Subadditive

/-- Definition 6.2.1-extra-2 (2): a real-valued function on a real vector space is positively
homogeneous if `g (c • x) = c * g x` for every vector `x` and every real scalar `c > 0`.
Specializing `E` to `Fin n → ℝ` recovers the textbook `ℝ^n` formulation. -/
def PositivelyHomogeneous [SMul ℝ E] (g : E → ℝ) : Prop :=
  ∀ (x : E) (c : ℝ), 0 < c → g (c • x) = c * g x

/-- Definition 6.2.1-extra-2 (3): a real-valued function on a real vector space is sublinear if it
is both subadditive and positively homogeneous. Specializing `E` to `Fin n → ℝ` recovers the
textbook `ℝ^n` formulation. -/
@[mk_iff sublinear_iff]
class Sublinear [Add E] [SMul ℝ E] (g : E → ℝ) : Prop where
  subadditive : g.Subadditive
  positivelyHomogeneous : g.PositivelyHomogeneous

section Zero

variable [Zero E] {g : E → ℝ}

/-- Definition 6.2.1-extra-2 (4): if `g` is positively homogeneous, then `g 0 = 0`. -/
theorem PositivelyHomogeneous.map_zero [SMulZeroClass ℝ E]
    (hg : g.PositivelyHomogeneous) : g 0 = 0 := by
  have h : g 0 = 2 * g 0 := by
    simpa using hg (0 : E) 2 zero_lt_two
  have h' : 0 = g 0 := by
    have hsub := congrArg (fun t ↦ t - g 0) h
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
  exact h'.symm

/-- Positive homogeneity extends to the zero scalar. -/
theorem PositivelyHomogeneous.smul_nonneg [SMulWithZero ℝ E]
    (hg : g.PositivelyHomogeneous) (x : E) (c : ℝ) (hc : 0 ≤ c) :
    g (c • x) = c * g x := by
  rcases lt_or_eq_of_le hc with hc_pos | rfl
  · exact hg x c hc_pos
  · simp [hg.map_zero]

end Zero

namespace Sublinear

section Zero

variable [Add E] [Zero E] {g : E → ℝ}

/-- A sublinear real-valued map sends the origin to `0`. -/
theorem map_zero [SMulZeroClass ℝ E] (hg : g.Sublinear) : g 0 = 0 :=
  hg.positivelyHomogeneous.map_zero

/-- A sublinear real-valued map satisfies the homogeneity formula for nonnegative scalars. -/
theorem smul_nonneg [SMulWithZero ℝ E] (hg : g.Sublinear) (x : E) (c : ℝ) (hc : 0 ≤ c) :
    g (c • x) = c * g x :=
  hg.positivelyHomogeneous.smul_nonneg x c hc

end Zero

end Sublinear

end Function
