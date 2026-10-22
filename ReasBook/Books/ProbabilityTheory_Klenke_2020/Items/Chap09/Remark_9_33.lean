/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 9.33: The submartingale analogues singled out in the text already belong to the
canonical mathlib owner API. Negating a submartingale produces a supermartingale. -/
recall MeasureTheory.Submartingale.neg

/- Negating a supermartingale produces a submartingale, giving the converse sign-change duality. -/
recall MeasureTheory.Supermartingale.neg

/- The pointwise maximum of two submartingales is again a submartingale. -/
recall MeasureTheory.Submartingale.sup
