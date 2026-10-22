/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_23

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 24.2.2: the coloring theorem requested here is exactly the already formalized theorem
`ProbabilityTheory.coloredPointProcess_isPoissonPointProcess`, stating that coloring a Poisson
point process by an iid mark family independent of the process again yields a Poisson point
process with product intensity. -/
recall ProbabilityTheory.coloredPointProcess_isPoissonPointProcess
