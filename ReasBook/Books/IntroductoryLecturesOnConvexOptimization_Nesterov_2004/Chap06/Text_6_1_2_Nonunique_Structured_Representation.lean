/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_6

noncomputable section

open scoped ConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Text 6.1.2 lies in the chapter's Fenchel-conjugacy / structured-objective bridge domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel.objective` and `StructuredObjectiveModel.objective_apply` in
  `Chap06/Definition_6_6`, the canonical owner of Chapter 6 structured objectives;
- `fenchelConjugate` and `fenchelConjugate_apply` in `Chap06/Definition_6_1`, the chapter owner
  for the dual objective on `StrongDual ℝ E`;
- `strongFenchelConjugate` in `Chap06/Definition_6_1`, the reusable continuous-dual bridge owner
  for real-valued objectives on normed spaces;
- `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the canonical finite-domain /
  finite-real-part bridge for the dual objective;
- `NormedSpace.inclusionInDoubleDual`, the canonical evaluation map `x ↦ (s ↦ s x)`.

Best owner abstraction:
- source-facing: the claim that the Fenchel-conjugate formula gives a structured representation of
  the objective;
- core/canonical: `StructuredObjectiveModel.objective`;
- bridge/view: the specialization with `smoothPart = 0`,
  `linearMap = NormedSpace.inclusionInDoubleDual ℝ E`,
  `dualSet = dom (strongFenchelConjugate f)`, and
  `dualPenalty = extendedRealRealPart (strongFenchelConjugate f)`.

Primitive data:
- the real-valued objective `f : E → ℝ`;
- a structured model `problem : StructuredObjectiveModel E (StrongDual ℝ E)`;
- a primal point `x : problem.primalSet`.

Derived API:
- the explicit Fenchel-conjugate expansion of `problem.objective x` under the bridge hypotheses;
- the source-facing equality `problem.objective x = f x` when the Fenchel formula represents `f`
  at `x`.

Source/core/bridge triage:
- source-facing: the representation of `f` by the Fenchel formula;
- core/canonical: `StructuredObjectiveModel.objective`;
- bridge/view: the theorems below identifying that owner objective with the Fenchel formula.

The previous file introduced a second root owner `fenchelDualRepresentation` and weakened the
statement to an arbitrary dual penalty `fStar`. This refinement deletes that duplicate owner,
keeps the actual Fenchel-conjugate data on the theorem surface through the reusable bridge owner
`strongFenchelConjugate`, and states Text 6.1.2 as a bridge from those canonical data to the
existing Chapter 6 structured-objective owner.
-/

/- The canonical double-dual inclusion is the structured linear term used in the Fenchel
representation. -/
recall NormedSpace.inclusionInDoubleDual

namespace StructuredObjectiveModel

variable (f : E → ℝ)

/-- Text 6.1.2, bridge form: if a structured model uses zero smooth part, the canonical
double-dual inclusion, and the actual Fenchel conjugate data of `f`, then its owner objective is
exactly the Fenchel-conjugate representation formula. -/
theorem objective_eq_fenchelConjugate_representation
    (problem : StructuredObjectiveModel E (StrongDual ℝ E))
    (x : problem.primalSet)
    (hsmooth : problem.smoothPart = 0)
    (hdualSet : problem.dualSet = dom (strongFenchelConjugate f))
    (hlinear : problem.linearMap = NormedSpace.inclusionInDoubleDual ℝ E)
    (hdualPenalty : problem.dualPenalty = extendedRealRealPart (strongFenchelConjugate f)) :
    problem.objective x =
      sSup
        ((fun s : StrongDual ℝ E ↦
            ((NormedSpace.inclusionInDoubleDual ℝ E x s -
                extendedRealRealPart (strongFenchelConjugate f) s : ℝ) :
              EReal)) ''
          dom (strongFenchelConjugate f)) := by
  rw [problem.objective_apply]
  have hrange :
      Set.range (fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal)) =
        ((fun s : StrongDual ℝ E ↦
            ((problem.smoothPart x + problem.linearMap x s - problem.dualPenalty s : ℝ) :
              EReal)) ''
          problem.dualSet) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [hrange, hdualSet]
  simp [hsmooth, hlinear, hdualPenalty]

/-- Text 6.1.2-Nonunique Structured Representation: whenever the Fenchel-conjugate formula
represents the objective `f` at `x`, the same value is the canonical Chapter 6 objective of any
structured model carrying exactly that Fenchel data. -/
theorem objective_eq_of_eq_fenchelConjugate_representation
    (problem : StructuredObjectiveModel E (StrongDual ℝ E))
    (x : problem.primalSet)
    (hsmooth : problem.smoothPart = 0)
    (hdualSet : problem.dualSet = dom (strongFenchelConjugate f))
    (hlinear : problem.linearMap = NormedSpace.inclusionInDoubleDual ℝ E)
    (hdualPenalty : problem.dualPenalty = extendedRealRealPart (strongFenchelConjugate f))
    (hf :
      ((f x : ℝ) : EReal) =
        sSup
          ((fun s : StrongDual ℝ E ↦
              ((NormedSpace.inclusionInDoubleDual ℝ E x s -
                  extendedRealRealPart (strongFenchelConjugate f) s : ℝ) :
                EReal)) ''
            dom (strongFenchelConjugate f))) :
    problem.objective x = (f x : EReal) := by
  rw [objective_eq_fenchelConjugate_representation f problem x hsmooth hdualSet hlinear
    hdualPenalty]
  exact hf.symm

end StructuredObjectiveModel

end
