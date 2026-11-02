module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Real.Basic

public section

variable {n : ℕ}

/-
Definition 1.27 (Convex hull). For `S : Set (Fin n → ℝ)` representing a subset of `ℝ^n`,
the textbook convex hull `conv(S)` is mathlib's `convexHull ℝ S`. The source's basic
characterizations are provided by the canonical API:

* `convexHull ℝ S` is the ambient owner for the convex hull of `S`;
* `subset_convexHull` states that `S ⊆ convexHull ℝ S`;
* `convex_convexHull` states that `convexHull ℝ S` is convex;
* `convexHull_min` states that it is the inclusionwise minimal convex set containing `S`;
* `convexHull_eq_iInter` states that it is the intersection of all convex supersets of `S`.
-/

#check (convexHull ℝ : Set (Fin n → ℝ) → Set (Fin n → ℝ))
#check (subset_convexHull ℝ : ∀ S : Set (Fin n → ℝ), S ⊆ convexHull ℝ S)
#check (convex_convexHull ℝ : ∀ S : Set (Fin n → ℝ), Convex ℝ (convexHull ℝ S))
#check
  (convexHull_min :
    ∀ {S T : Set (Fin n → ℝ)}, S ⊆ T → Convex ℝ T → convexHull ℝ S ⊆ T)
#check
  (convexHull_eq_iInter ℝ :
    ∀ S : Set (Fin n → ℝ),
      convexHull ℝ S = ⋂ (T : Set (Fin n → ℝ)) (_ : S ⊆ T) (_ : Convex ℝ T), T)
