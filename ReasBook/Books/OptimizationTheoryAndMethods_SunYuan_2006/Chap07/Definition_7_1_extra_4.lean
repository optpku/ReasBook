/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

noncomputable section

-- Domain sampling:
-- * primary domain: nonlinear least-squares / Gauss-Newton correction term;
-- * inspected project owners: `leastSquaresCorrectionMatrix`,
--   `leastSquaresHessianMatrix`, `gaussNewtonLinearErrorCoefficient`,
--   `leastSquaresCorrectionMatrix_eq_zero_of_residual_eq_zero`;
-- * source/core/bridge triage:
--   - source-facing layer here: the textbook labels "small residual problem" and
--     "large residual problem" are qualitative language about the size of `S(x)`;
--   - core/canonical owner: `leastSquaresCorrectionMatrix`;
--   - this file stays at the recall layer and does not introduce a second predicate owner;
-- * primitive data vs derived API:
--   - primitive owner: the correction term `S(x) = leastSquaresCorrectionMatrix r x`;
--   - derived quantitative API elsewhere in the chapter: `gaussNewtonLinearErrorCoefficient`.

section

variable {m n : ℕ}

/- Chapter07 Definition 7.1-extra-4: the textbook terminology "small residual problem" and
"large residual problem" is qualitative commentary on whether the canonical correction term
`S(x) = leastSquaresCorrectionMatrix r x` is negligible at the point under discussion.

This item introduces no new mathematical owner: the Chapter 7 source-facing object is already the
correction term `leastSquaresCorrectionMatrix`, and later quantitative statements in the chapter
reuse that owner directly. -/

#check leastSquaresCorrectionMatrix

end
