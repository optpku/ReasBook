/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5

open scoped BigOperators Matrix

noncomputable section

section Remark66

variable {p q k : ℕ}

local notation "flatSet(" C ")" => Fin.appendEquiv p q '' C
local notation "flatPoint(" x ")" => Fin.appendEquiv p q x
local notation "flatRays(" rays ")" => (fun j ↦ Fin.appendEquiv p q (rays j))

/-- The mixed-space intersection cut attached to `C`, viewed in the nonnegative ray-coordinate
space. Its coefficient vector is obtained by applying the Chapter 6.2 owner
`intersection_cut_coeff` to the flattened mixed-space data in `ℝ^(p + q)`. -/
def intersection_cut_region
    (C : Set (MixedRealPoint p q))
    (xbar : MixedRealPoint p q)
    (rays : Fin k → MixedRealPoint p q) :
    Set (Fin k → ℝ) :=
  {s |
    (∀ j : Fin k, 0 ≤ s j) ∧
      1 ≤ (fun j ↦
        IntersectionCut.intersection_cut_coeff
          (flatSet(C)) (flatPoint(xbar)) (flatRays(rays)) j) ⬝ᵥ s}

/-- Membership in `intersection_cut_region C xbar rays` means nonnegative coefficients satisfying
the mixed-space intersection-cut inequality induced from the flattened Chapter 6.2 owner. -/
theorem mem_intersection_cut_region_iff
    (C : Set (MixedRealPoint p q))
    (xbar : MixedRealPoint p q)
    (rays : Fin k → MixedRealPoint p q)
    (s : Fin k → ℝ) :
    s ∈ intersection_cut_region C xbar rays ↔
      (∀ j : Fin k, 0 ≤ s j) ∧
        1 ≤ (fun j ↦
          IntersectionCut.intersection_cut_coeff
            (flatSet(C)) (flatPoint(xbar)) (flatRays(rays)) j) ⬝ᵥ s :=
  Iff.rfl

/-- Remark 6.6. In the usual textbook setting of closed convex `ℤ^p × ℝ^q`-free sets whose
interiors contain `xbar`, the domination claim is the subset-monotonicity statement below: if
`C₁ ⊆ C₂`, then the intersection cut defined by `C₂` dominates the one defined by `C₁`. -/
theorem intersection_cut_dominates_of_subset
    (xbar : MixedRealPoint p q)
    (rays : Fin k → MixedRealPoint p q)
    (C1 C2 : Set (MixedRealPoint p q))
    (hx1 : xbar ∈ interior C1)
    (hsubset : C1 ⊆ C2) :
    intersection_cut_region C2 xbar rays ⊆
      intersection_cut_region C1 xbar rays := by
  intro s hs
  rw [mem_intersection_cut_region_iff] at hs ⊢
  rcases hs with ⟨hs_nonneg, hs_cut⟩
  refine ⟨hs_nonneg, ?_⟩
  -- Transport the interior hypothesis to the flattened ambient space used by the cut owner.
  have hflatInterior :
      flatPoint(xbar) ∈ interior (flatSet(C1)) := by
    have hflatImage :
        flatPoint(xbar) ∈ (Fin.appendHomeomorph (X := ℝ) p q) '' interior C1 := by
      exact ⟨xbar, hx1, rfl⟩
    have hflatInteriorHomeomorph :
        flatPoint(xbar) ∈ interior ((Fin.appendHomeomorph (X := ℝ) p q) '' C1) := by
      rw [← (Fin.appendHomeomorph (X := ℝ) p q).image_interior C1]
      exact hflatImage
    simpa [Fin.appendHomeomorph_toEquiv] using hflatInteriorHomeomorph
  -- Set inclusion is preserved by the flattening map.
  have hflatSubset : flatSet(C1) ⊆ flatSet(C2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hsubset hx, rfl⟩
  -- The larger set yields smaller cut coefficients on every ray.
  have hcoeff :
      (fun j ↦
        IntersectionCut.intersection_cut_coeff
          (flatSet(C2)) (flatPoint(xbar)) (flatRays(rays)) j) ≤
        fun j ↦
          IntersectionCut.intersection_cut_coeff
            (flatSet(C1)) (flatPoint(xbar)) (flatRays(rays)) j := by
    intro j
    exact
      IntersectionCut.intersection_cut_coeff_antitone_of_subset
        (xbar := flatPoint(xbar))
        (rays := flatRays(rays))
        (C1 := flatSet(C1))
        (C2 := flatSet(C2))
        hflatInterior hflatSubset j
  -- Monotonicity of the dot product on the nonnegative orthant transfers the cut inequality.
  have hdot :
      (fun j ↦
        IntersectionCut.intersection_cut_coeff
          (flatSet(C2)) (flatPoint(xbar)) (flatRays(rays)) j) ⬝ᵥ s ≤
        (fun j ↦
          IntersectionCut.intersection_cut_coeff
            (flatSet(C1)) (flatPoint(xbar)) (flatRays(rays)) j) ⬝ᵥ s :=
    dotProduct_le_dotProduct_of_nonneg_right hcoeff hs_nonneg
  exact le_trans hs_cut hdot

end Remark66
