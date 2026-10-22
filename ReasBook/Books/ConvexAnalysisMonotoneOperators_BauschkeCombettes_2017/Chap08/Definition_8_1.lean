/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]
variable (f : H → EReal)

/- Definition 8.1: the textbook real-height epigraph of an extended-real-valued function is the
canonical set `epigraph f` already introduced in Definition 1.4; concretely, it consists of the
pairs `(x, ξ) : H × ℝ` with `f x ≤ ξ`. In this chapter, convexity of `f` is expressed by
`Convex ℝ (epigraph f)`, and concavity by convexity of the epigraph of `-f`. -/
recall epigraph

/- Companion recall: membership in the real-height epigraph is exactly the inequality `f x ≤ ξ`. -/
recall mem_epigraph_iff

/- Companion recall: the textbook statement that `f` is convex is expressed by the proposition
`Convex ℝ (epigraph f)`. -/
#check Convex ℝ (epigraph f)

/- Companion recall: the textbook statement that `f` is concave is expressed by convexity of the
real-height epigraph of `-f`. -/
#check Convex ℝ (epigraph (-f))

end RealVectorSpace

end ERealFunction
