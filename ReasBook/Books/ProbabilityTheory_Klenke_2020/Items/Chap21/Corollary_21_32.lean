/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

noncomputable section

local instance : MeasurableSpace BrownianPathSpace := borel _

local instance : BorelSpace BrownianPathSpace := ⟨rfl⟩

/-- The supremum of a continuous real path on `[0,1]`. -/
noncomputable def brownianPathSupOnUnitInterval (ω : BrownianPathSpace) : ℝ :=
  sSup (Set.range (ω.restrict (Set.Icc (0 : NNReal) 1)))

-- Proof sketch: the time `0` belongs to `[0,1]`, so a path started at `0` contributes the value
-- `0` to the set over which the supremum is taken.
/-- If a path starts at `0`, then its supremum on `[0,1]` is nonnegative. -/
theorem brownianPathSupOnUnitInterval_nonneg {ω : BrownianPathSpace} (hω : ω 0 = 0) :
    0 ≤ brownianPathSupOnUnitInterval ω := by
  -- Unfold the definition so the interval point `0` can be inserted into the supremum range.
  rw [brownianPathSupOnUnitInterval]
  have hbdd : BddAbove ((↑ω) '' Set.Icc (0 : NNReal) 1) := by
    -- Compactness of the closed interval bounds the continuous image of the path from above.
    exact isCompact_Icc.bddAbove_image ω.continuous.continuousOn
  have hmem : 0 ∈ ((↑ω) '' Set.Icc (0 : NNReal) 1) := by
    -- The start time `0` lies in `[0,1]` and contributes the value `0`.
    exact ⟨0, by simp, hω⟩
  simpa [Set.image_eq_range, ContinuousMap.restrict_apply] using le_csSup hbdd hmem

/-- The unit-interval supremum is the supremum of the path values on `[0,1]`. -/
theorem brownianPathSupOnUnitInterval_spec (ω : BrownianPathSpace) :
    brownianPathSupOnUnitInterval ω =
      sSup (Set.range fun t : Set.Icc (0 : NNReal) 1 ↦ ω t) :=
  rfl

/-- Helper for Corollary 21.32: evaluation on `BrownianPathSpace × Set.Icc (0 : NNReal) 1` is
continuous. -/
lemma continuousEvalOnUnitInterval :
    Continuous (fun p : BrownianPathSpace × Set.Icc (0 : NNReal) 1 ↦ p.1 p.2) := by
  -- The compact-open topology makes evaluation continuous in the map and time variables together.
  simpa using
    (continuous_fst.eval (continuous_subtype_val.comp continuous_snd) :
      Continuous (fun p : BrownianPathSpace × Set.Icc (0 : NNReal) 1 ↦ p.1 p.2))

-- Proof sketch: if two continuous paths are uniformly close on `[0,1]`, then their suprema on
-- `[0,1]` differ by at most the same uniform error. This yields continuity for the path functional.
/-- The unit-interval supremum is continuous on the continuous path space. -/
theorem continuous_brownianPathSupOnUnitInterval :
    Continuous brownianPathSupOnUnitInterval := by
  -- Express the path functional as a compact supremum over the interval subtype.
  simpa [brownianPathSupOnUnitInterval_spec, Set.image_univ] using
    (isCompact_univ : IsCompact (Set.univ : Set (Set.Icc (0 : NNReal) 1))).continuous_sSup
      (f := fun (ω : BrownianPathSpace) (t : Set.Icc (0 : NNReal) 1) ↦ ω t)
      continuousEvalOnUnitInterval

-- Proof sketch: apply `Continuous.measurable` to the continuity statement for the supremum map.
/-- Corollary 21.32: the map sending a continuous path, hence in particular a Brownian path, to
its supremum on `[0,1]` is Borel measurable. -/
theorem measurable_brownianPathSupOnUnitInterval :
    Measurable brownianPathSupOnUnitInterval := by
  -- Borel measurability follows immediately from continuity on the Borel path space.
  exact continuous_brownianPathSupOnUnitInterval.measurable
