/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 13.1: a Polish space is the canonical owner class `PolishSpace`. Its primitive
ingredients are `SecondCountableTopology` and
`TopologicalSpace.IsCompletelyMetrizableSpace`, so the textbook description of a separable space
admitting a compatible complete metric is already packaged by this owner abstraction. -/
recall PolishSpace
