/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/-- Algorithm 1.2.10: a general iterative scheme is organized around the accumulated informational
set `𝓘_k` of oracle samples. The current query point, the stopping criterion, and the output are
all chosen from that informational set; in particular, the initial point is `query ∅ = x₀`. This
uses the informational state owner from Definition 1.2.13 directly, rather than an auxiliary
ordered transcript. -/
structure GeneralIterativeScheme (Query : Type u) (Answer : Type v) where
  oracle : Query → Answer
  query : Set (Query × Answer) → Query
  shouldStop : Set (Set (Query × Answer))
  output : Set (Query × Answer) → Query

namespace GeneralIterativeScheme

/-- The recursively generated informational sets of the iterative scheme. Here
`informationState 0` is the empty set representing the pre-oracle state `𝓘_{-1} = ∅`, and
`informationState (k + 1)` is obtained from `informationState k` by inserting the current query
point together with its oracle reply. -/
def informationState
    (scheme : GeneralIterativeScheme Query Answer) :
    ℕ → Set (Query × Answer)
  | 0 => ∅
  | k + 1 =>
      let Ik := scheme.informationState k
      let xk := scheme.query Ik
      insert (xk, scheme.oracle xk) Ik

/-- A general iterative scheme can be used as its underlying trajectory of informational sets. -/
instance : CoeFun (GeneralIterativeScheme Query Answer)
    (fun _ ↦ ℕ → Set (Query × Answer)) where
  coe scheme := scheme.informationState

/-- The current query point at iteration `k` is chosen from the informational set available after
`k` oracle calls. In particular, `currentPoint 0 = query ∅ = x₀`. -/
def currentPoint
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Query :=
  scheme.query (scheme k)

/-- The oracle reply observed at the current query point of iteration `k`. -/
def currentAnswer
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Answer :=
  scheme.oracle (scheme.currentPoint k)

/-- The new sample added to the informational set at iteration `k`. -/
def currentSample
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Query × Answer :=
  (scheme.currentPoint k, scheme.currentAnswer k)

/-- The informational set before any oracle call is empty. -/
@[simp] theorem informationState_zero
    (scheme : GeneralIterativeScheme Query Answer) :
    scheme 0 = ∅ := rfl

/-- The informational set after `k + 1` oracle calls is obtained from the informational set after
`k` calls by adjoining the current query point together with its oracle reply. -/
@[simp] theorem informationState_succ
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) :
    scheme (k + 1) =
      insert (scheme.currentSample k) (scheme k) := by
  simp [informationState, currentSample, currentAnswer, currentPoint]

/-- The scheme halts after `k` oracle-call/update cycles when `k > 0` and the reached
informational set satisfies the chosen stopping criterion, for instance a fixed `ε`-stopping
rule. -/
def HaltsAt
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Prop :=
  0 < k ∧ scheme.shouldStop (scheme k)

/-- The output produced at iteration `k` is obtained by applying the output rule to the current
informational set. -/
def outputAt
    (scheme : GeneralIterativeScheme Query Answer) (k : ℕ) : Query :=
  scheme.output (scheme k)

end GeneralIterativeScheme
