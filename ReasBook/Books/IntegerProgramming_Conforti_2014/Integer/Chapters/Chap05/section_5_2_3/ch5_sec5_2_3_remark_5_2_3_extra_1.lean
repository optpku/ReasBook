/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2.ch5_sec5_2_definition_5_2_extra_2

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: mixed-integer Chvatal cut presentations for systems with `x ≥ 0`;
-- * core/canonical owners: Chapter 5 `IsChvatalMultiplier` and `IsMixedIntegerCoefficient`;
-- * source-facing layer kept here: the system-specific feasible-set corollaries for
--   Remark 5.2.3-extra-1;
-- * bridge/view layer used here: coefficient vectors `((u ᵥ* A) - v)`.

section Remark523Extra1

variable {m n : ℕ}
variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (I : Finset (Fin n))

/-- The mixed-integer feasible set for the nonnegative inequality system
`P = {x : ℝ^n | A x ≤ b, x ≥ 0}` is the Chapter 5 owner `mixed_integer_feasible_set A b I`
intersected with the nonnegative orthant. -/
theorem mem_mixed_integer_feasible_set_inter_nonnegative_iff
    (x : Fin n → ℝ) :
    x ∈ mixed_integer_feasible_set A b I ∩ {x : Fin n → ℝ | 0 ≤ x} ↔
      A *ᵥ x ≤ b ∧ 0 ≤ x ∧ ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ) := by
  rw [Set.mem_inter_iff, mem_mixed_integer_feasible_set_iff]
  constructor
  · rintro ⟨hx, hx_nonneg⟩
    exact ⟨hx.1, hx_nonneg, hx.2⟩
  · rintro ⟨hAx, hx_nonneg, hI⟩
    exact ⟨⟨hAx, hI⟩, hx_nonneg⟩

/-- Helper for Remark 5.2.3-extra-1: the mixed-integer Chvátal coefficient vector
`((u ᵥ* A) - v)` is pointwise dominated by the supported floor vector on `I`. -/
lemma subtractedCoeff_le_supportedFloorCoeff
    (u : Fin m → ℝ)
    (v : Fin n → ℝ)
    (hv : ∀ j : Fin n, 0 ≤ v j)
    (hcoeff : IsMixedIntegerCoefficient I ((u ᵥ* A) - v)) :
    ((u ᵥ* A) - v) ≤ fun j ↦ if j ∈ I then ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) else 0 := by
  intro j
  by_cases hj : j ∈ I
  · -- On the integer coordinates, compare first with `(u ᵥ* A) j` and then take floors.
    have hzsub : ((u ᵥ* A) - v) j ≤ (u ᵥ* A) j := by
      simpa using sub_le_self ((u ᵥ* A) j) (hv j)
    rcases hcoeff.exists_int hj with ⟨z, hz⟩
    have hzle : (z : ℝ) ≤ (u ᵥ* A) j := by
      simpa [hz] using hzsub
    have hzfloor : z ≤ ⌊(u ᵥ* A) j⌋ := Int.le_floor.mpr hzle
    have hpoint : ((u ᵥ* A) - v) j ≤ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) := by
      calc
        ((u ᵥ* A) - v) j = (z : ℝ) := hz
        _ ≤ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) := by
          exact_mod_cast hzfloor
    simpa [hj] using hpoint
  · -- Outside `I`, the mixed-integer coefficient hypothesis forces the coefficient to vanish.
    have hpoint : ((u ᵥ* A) - v) j ≤ 0 := by
      exact le_of_eq (hcoeff.eq_zero_of_not_mem hj)
    simpa [hj] using hpoint

/-- Helper for Remark 5.2.3-extra-1: the supported floor coefficient vector has dot product equal
to the textbook floor sum over `I`. -/
lemma supportedFloorCoeffDot_eq_floorSum
    (u : Fin m → ℝ)
    (x : Fin n → ℝ) :
    (fun j ↦ if j ∈ I then ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) else 0) ⬝ᵥ x =
      Finset.sum I (fun j ↦ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) * x j) := by
  classical
  -- Expand the dot product and discard the zero coefficients off `I`.
  simp [dotProduct]

/-- Helper for Remark 5.2.3-extra-1: nonnegative coordinates of `x` transfer the coefficientwise
domination to the corresponding dot products. -/
lemma subtractedCoeffDot_le_floorSum
    (u : Fin m → ℝ)
    (v : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hv : ∀ j : Fin n, 0 ≤ v j)
    (hcoeff : IsMixedIntegerCoefficient I ((u ᵥ* A) - v))
    (hx_nonneg : 0 ≤ x) :
    ((u ᵥ* A) - v) ⬝ᵥ x ≤
      Finset.sum I (fun j ↦ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) * x j) := by
  -- Monotonicity of the dot product on the nonnegative orthant reduces the claim to the
  -- supported floor vector, whose dot product is the required floor sum.
  calc
    ((u ᵥ* A) - v) ⬝ᵥ x
        ≤ (fun j ↦ if j ∈ I then ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) else 0) ⬝ᵥ x :=
          dotProduct_le_dotProduct_of_nonneg_right
            (subtractedCoeff_le_supportedFloorCoeff A I u v hv hcoeff)
            hx_nonneg
    _ = Finset.sum I (fun j ↦ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) * x j) :=
      supportedFloorCoeffDot_eq_floorSum A I u x

/-- Remark 5.2.3-extra-1: the shared domination step depends only on nonnegative coordinates,
integrality on `I`, nonnegative slack coefficients `v`, and the mixed-integer coefficient
property of `u A - v`. -/
theorem chvatal_cut_le_of_floor_form
    (u : Fin m → ℝ)
    (v : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hv : ∀ j : Fin n, 0 ≤ v j)
    (hcoeff : IsMixedIntegerCoefficient I ((u ᵥ* A) - v))
    (hx_nonneg : 0 ≤ x)
    (hx_int : ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ))
    (hfloor :
      Finset.sum I (fun j ↦ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) * x j) ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ)) :
    ((u ᵥ* A) - v) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) := by
  -- The domination argument only needs the nonnegative orthant and the supported floor bound;
  -- the source-facing integrality hypothesis on `x` remains in the theorem interface.
  let _ := hx_int
  calc
    ((u ᵥ* A) - v) ⬝ᵥ x
        ≤ Finset.sum I (fun j ↦ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) * x j) :=
          subtractedCoeffDot_le_floorSum A I u v hv hcoeff hx_nonneg
    _ ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) := hfloor

/-- Source-facing corollary for Remark 5.2.3-extra-1 (1): for points of
`mixed_integer_feasible_set A b I` that also
satisfy `x ≥ 0`, the floor-form cut `∑ j ∈ I, ⌊(u ᵥ* A) j⌋ x_j ≤ ⌊u b⌋` dominates the
Chvátal inequality `((u ᵥ* A) - v) x ≤ ⌊u b⌋`. The reusable domination theorem is
`chvatal_cut_le_of_floor_form`, whose hypotheses record only the nonnegative and
mixed-integral data actually used in the proof. -/
theorem nonnegative_inequality_system_chvatal_cut_le_of_floor_form
    (u : Fin m → ℝ)
    (v : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hv : ∀ j : Fin n, 0 ≤ v j)
    (hcoeff : IsMixedIntegerCoefficient I ((u ᵥ* A) - v))
    (hx_mixed : x ∈ mixed_integer_feasible_set A b I)
    (hx_nonneg : 0 ≤ x)
    (hfloor :
      Finset.sum I (fun j ↦ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) * x j) ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ)) :
    ((u ᵥ* A) - v) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) := by
  obtain ⟨_, hx_int⟩ := (mem_mixed_integer_feasible_set_iff A b I x).1 hx_mixed
  exact chvatal_cut_le_of_floor_form A b I u v hv hcoeff hx_nonneg hx_int hfloor

/-- Source-facing corollary for Remark 5.2.3-extra-1 (2): for points of
`standard_equality_form A b` whose coordinates indexed by `I` are integral, the same floor-form
cut dominates the Chvátal inequality `((u ᵥ* A) - v) x ≤ ⌊u b⌋`. The irredundancy-side
assumption `u b ∉ ℤ` is not needed for this domination statement, and the reusable theorem is
again `chvatal_cut_le_of_floor_form`. -/
theorem standard_equality_system_chvatal_cut_le_of_floor_form
    (u : Fin m → ℝ)
    (v : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hv : ∀ j : Fin n, 0 ≤ v j)
    (hcoeff : IsMixedIntegerCoefficient I ((u ᵥ* A) - v))
    (hx_standard : x ∈ standard_equality_form A b)
    (hx_int : ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ))
    (hfloor :
      Finset.sum I (fun j ↦ ((⌊(u ᵥ* A) j⌋ : ℤ) : ℝ) * x j) ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ)) :
    ((u ᵥ* A) - v) ⬝ᵥ x ≤ ((⌊u ⬝ᵥ b⌋ : ℤ) : ℝ) := by
  obtain ⟨_, hx_nonneg⟩ := (mem_standard_equality_form_iff).1 hx_standard
  exact chvatal_cut_le_of_floor_form A b I u v hv hcoeff hx_nonneg hx_int hfloor

end Remark523Extra1
