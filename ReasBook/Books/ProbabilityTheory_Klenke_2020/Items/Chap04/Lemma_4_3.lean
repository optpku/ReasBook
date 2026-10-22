/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {α : Type u} [MeasurableSpace α] (μ : Measure α)

/- Lemma 4.3 (1): Part (i): the map `I` on nonnegative elementary functions is homogeneous for
nonnegative scalars. -/
recall SimpleFunc.const_mul_lintegral

/- Lemma 4.3 (2): Part (ii): the map `I` on nonnegative elementary functions is additive. -/
recall SimpleFunc.add_lintegral

/- Lemma 4.3 (3): Part (iii): the map `I` on nonnegative elementary functions is monotone
increasing. -/
recall SimpleFunc.lintegral_mono_fun
