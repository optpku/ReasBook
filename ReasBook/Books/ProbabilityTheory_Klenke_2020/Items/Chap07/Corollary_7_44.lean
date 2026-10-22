/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 7.44: Jordan's decomposition theorem is the canonical equivalence between signed
measures and Jordan decompositions. For a signed measure `φ`, the corresponding Jordan
decomposition has finite mutually singular positive and negative parts
`φ.toJordanDecomposition.posPart` and `φ.toJordanDecomposition.negPart`, and the inverse map
`JordanDecomposition.toSignedMeasure` encodes uniqueness of this decomposition. -/
recall MeasureTheory.SignedMeasure.toJordanDecompositionEquiv
