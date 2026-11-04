/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic

/-- A subset of `ι → ℝ` is integral if it is the convex hull of its integer points. -/
def is_integral {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  P =
    convexHull ℝ
      (P ∩ Set.range (fun z : ι → ℤ ↦ Int.cast ∘ z))

/-- A subset of `ι → ℝ` is integral exactly when it equals the convex hull of its integer points. -/
theorem is_integral_iff {ι : Type*} {P : Set (ι → ℝ)} :
    is_integral P ↔
      P =
        convexHull ℝ
          (P ∩ Set.range (fun z : ι → ℤ ↦ Int.cast ∘ z)) :=
  Iff.rfl
