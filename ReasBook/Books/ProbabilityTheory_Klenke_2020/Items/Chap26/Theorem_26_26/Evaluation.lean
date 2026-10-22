/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Coefficients

namespace ProbabilityTheory

variable {n : ℕ}

/-- Deterministic-time evaluation on the canonical path space used in Theorem 26.26 is
measurable. -/
theorem measurable_path_eval (t : NNReal) :
    Measurable
      (ContinuousMap.evalCLM ℝ t :
        StroockVaradhanPathSpace n → StroockVaradhanState n) := by
  simpa using (continuous_eval_const t).measurable

end ProbabilityTheory
