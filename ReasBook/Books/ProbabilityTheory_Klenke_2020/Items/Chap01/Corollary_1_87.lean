/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- Corollary 1.87: Restricting the Borel `σ`-algebra of `EReal` along the canonical inclusion
`ℝ → EReal` recovers the Borel `σ`-algebra of `ℝ`. -/
theorem borel_ereal_comap_toEReal :
    MeasurableSpace.comap Real.toEReal (borel EReal) = borel ℝ :=
  EReal.measurableEmbedding_coe.comap_eq
