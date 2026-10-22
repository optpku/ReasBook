/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Remark 1.62 (finite-dimensional part): for a finite family of measurable spaces and
σ-finite measures, the canonical product measure `Measure.pi` evaluates on measurable rectangles
as the product of the factor masses. -/
recall Measure.pi_pi

/- Remark 1.62 (infinite-dimensional part): for an arbitrary family of measurable spaces equipped
with probability measures, the canonical infinite product measure `infinitePi` exists and assigns
to each measurable cylinder the product of the corresponding factor masses. -/
recall Measure.infinitePi_pi
