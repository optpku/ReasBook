/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_15

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 24.2.1 (1): the expectation identity from Corollary 24.15 can also be proved by
approximating the integrand by simple functions instead of using characteristic functions. -/
recall ProbabilityTheory.poissonPointProcess_integral_expectation_eq

/- Exercise 24.2.1 (2): the variance identity from Corollary 24.15 can likewise be obtained by a
simple-function approximation argument, avoiding characteristic functions. -/
recall ProbabilityTheory.poissonPointProcess_integral_variance_eq
