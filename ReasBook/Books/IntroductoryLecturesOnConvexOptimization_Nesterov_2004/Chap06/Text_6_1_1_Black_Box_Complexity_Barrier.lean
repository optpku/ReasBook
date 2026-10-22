/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain note: this item lies in the chapter's nonsmooth first-order black-box complexity domain.

Mandatory domain-style sampling before refinement:
- `exists_problem_with_nonsmooth_firstOrder_lower_bound` in `Chap03/Theorem_3_2_1`, the chapter's
  canonical owner theorem for the nonsmooth black-box lower bound;
- `Theorem_3_39`, the earlier chapter recall that already records this owner theorem as the
  textbook barrier and explicitly notes that separate positivity guards on `R, M : NNReal` are
  redundant;
- `f_k` in `Chap03/Definition_3_35`, the source-facing Nemirovski hard-instance family;
- `f_k_minimizer` in `Chap03/Proposition_3_30`, the canonical minimizer attached to that explicit
  witness family.

Best owner abstraction:
- source-facing: Text 6.1.1 as the black-box `O(1 / ε^2)` barrier statement;
- core/canonical: `exists_problem_with_nonsmooth_firstOrder_lower_bound`;
- bridge/view: the explicit Nemirovski witness family `f_k` with `f_k_minimizer`, which explains
  how the owner theorem can be realized but should not replace the owner surface here.

Primitive data on the owner surface:
- the dimension `n`;
- the starting point `x₀`;
- the radius and Lipschitz parameters `R M : NNReal`;
- the iteration index `k` with `k + 1 ≤ n`.

Derived API:
- existence of a hard instance `f` with chosen minimizer `xStar` in `𝒫(x₀, R, M)`;
- the lower bound for every first-order oracle satisfying the prefix-support-growth condition and
  every iterate sequence satisfying the linear-span condition for that oracle.

This Chapter 6 text item is therefore a direct recall of the canonical Chapter 3 owner theorem.
The explicit hard family `f_k` remains upstream as an auxiliary witness layer rather than the main
public declaration here.
-/

/- Text 6.1.1-Black-Box Complexity Barrier: the Chapter 3 black-box lower-bound theorem gives the
canonical `O(1 / ε^2)` oracle-complexity barrier for span-based nonsmooth convex minimization
under the resisting-oracle prefix-support-growth hypothesis, and the Nemirovski hard family `f_k`
explains this barrier constructively through explicit simple witness problems. -/
recall exists_problem_with_nonsmooth_firstOrder_lower_bound
