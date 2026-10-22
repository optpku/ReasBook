/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory Set
open scoped Topology BoundedContinuousFunction CompactlySupported

variable {E : Type u}

section RadonOwners

variable [TopologicalSpace E] [MeasurableSpace E]

/- Definition 13.4 (1): `𝓜(E)` is the set of measures satisfying the canonical owner predicate
`IsRadonMeasure`. -/
#check ({ μ : Measure E | IsRadonMeasure μ } : Set (Measure E))

/- The corresponding subtype `{ μ : Measure E // IsRadonMeasure μ }` is used later only as a
bridge/view carrier for topological constructions; it is not a second owner definition. -/
#check ({ μ : Measure E // IsRadonMeasure μ } : Type u)

end RadonOwners

section MeasureOwners

variable [MeasurableSpace E]

/- Definition 13.4 (2): the textbook space `𝓜_f(E)` of finite measures is the canonical owner
type `FiniteMeasure E`. -/
#check (FiniteMeasure E)

/- Definition 13.4 (3): the textbook space `𝓜_1(E)` of probability measures is the canonical
owner type `ProbabilityMeasure E`. -/
#check (ProbabilityMeasure E)

/- Definition 13.4 (4): for a finite measure `μ`, the textbook subprobability condition is the
canonical inequality `μ.mass ≤ 1`, expressed using the owner map `FiniteMeasure.mass`. -/
#check (FiniteMeasure.mass : FiniteMeasure E → NNReal)

end MeasureOwners

section FunctionOwners

variable [TopologicalSpace E]

/- Definition 13.4 (5): the textbook space `C(E)` is the canonical owner type `C(E, ℝ)`. -/
#check (C(E, ℝ))

/- Definition 13.4 (6): the textbook space `C_b(E)` is the canonical owner type `E →ᵇ ℝ`. -/
#check (E →ᵇ ℝ)

/- Definition 13.4 (7): the textbook space `C_c(E)` is the canonical owner type `C_c(E, ℝ)`. -/
#check (C_c(E, ℝ))

/- Definition 13.4 (8): every compactly supported continuous real-valued function canonically
defines a bounded continuous real-valued function via
`CompactlySupportedContinuousMap.toBoundedContinuousFunction`. -/
#check (CompactlySupportedContinuousMap.toBoundedContinuousFunction : C_c(E, ℝ) → E →ᵇ ℝ)

end FunctionOwners

/- Definition 13.4 (9): The textbook support
`\overline{f^{-1}(\mathbb{R} \setminus \{0\})}` is the canonical topological support `tsupport f`.
-/
recall tsupport

/- The textbook sup-norm convention is represented canonically in mathlib on bounded continuous and
compactly supported continuous functions. For arbitrary `C(E)`, the supremum norm requires extra
compactness or boundedness hypotheses, so that convention is left informal at this stage. -/
