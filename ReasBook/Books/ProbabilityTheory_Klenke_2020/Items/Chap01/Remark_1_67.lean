/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

/-- Remark 1.67: The Lebesgue measure on `ℝ^n`, formalized as `volume` on `Fin n → ℝ`, is a
regular measure. In particular, it is outer regular and inner regular on measurable sets of finite
measure. -/
instance volume_regular (n : ℕ) : Measure.Regular (volume : Measure (Fin n → ℝ)) :=
  inferInstance

/-- The canonical volume measure on `ℝ^n` is outer regular: its value on a set is the infimum of
the measures of open supersets. -/
theorem volume_measure_eq_iInf_isOpen (n : ℕ) (A : Set (Fin n → ℝ)) :
    volume A = ⨅ (U : Set (Fin n → ℝ)) (_ : A ⊆ U) (_ : IsOpen U), volume U :=
  Set.measure_eq_iInf_isOpen A volume

/-- For the canonical volume measure on `ℝ^n`, any measurable set of finite measure is inner
regular with respect to compact subsets. -/
theorem volume_measure_eq_iSup_isCompact_of_ne_top (n : ℕ) {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hAfinite : volume A ≠ ⊤) :
    volume A = ⨆ (K : Set (Fin n → ℝ)) (_ : K ⊆ A) (_ : IsCompact K), volume K :=
  MeasurableSet.measure_eq_iSup_isCompact_of_ne_top hA hAfinite
