/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15.Normed
public import Mathlib.Analysis.Seminorm

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

namespace BV

variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

/-- The Chapter 8 total-variation functional restricted from `L¹(Ω)` to `BV(Ω)` and converted to
a real-valued quantity by `EReal.toReal`. -/
@[expose]
def totalVariation (u : BV(Ω)) : ℝ :=
  (VariationalRegularization.totalVariation u.toL1).toReal

/-- The defining formula for the restricted Chapter 8 total-variation functional on `BV(Ω)`. -/
theorem totalVariation_def (u : BV(Ω)) :
    u.totalVariation = (VariationalRegularization.totalVariation u.toL1).toReal := by
  -- Unfold the wrapper once to expose the restricted real-valued formula.
  rfl

/-- The restricted Chapter 8 total-variation functional is subadditive on `BV(Ω)`. -/
theorem totalVariation_add_le (u v : BV(Ω)) :
    totalVariation (u + v) ≤ totalVariation u + totalVariation v := by
  -- This is the real-valued transport of the raw `L¹(Ω)` subadditivity lemma.
  simpa [totalVariation_def] using lpTotalVariationToReal_add_le u v

/-- The restricted Chapter 8 total-variation functional is homogeneous under real scalar
multiplication on `BV(Ω)`. -/
theorem totalVariation_smul (a : ℝ) (u : BV(Ω)) :
    totalVariation (a • u) = ‖a‖ * totalVariation u := by
  -- This is the real-valued transport of the raw `L¹(Ω)` scaling identity.
  simpa [totalVariation_def] using lpTotalVariationToReal_smul a u

/-- The canonical seminorm on `BV(Ω)` induced by the restricted Chapter 8 total variation. -/
@[expose]
def tvSeminorm : Seminorm ℝ (BV(Ω)) :=
  Seminorm.of totalVariation totalVariation_add_le totalVariation_smul

/-- Applying `BV.tvSeminorm` recovers the restricted Chapter 8 total-variation functional. -/
theorem tvSeminorm_apply (u : BV(Ω)) :
    tvSeminorm u = totalVariation u := by
  -- The bundled seminorm applies by definition to the wrapped total variation.
  rfl

end BV

end VariationalRegularization
