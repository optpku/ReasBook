/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: specialize mathlib's Euler-product theorem `riemannZeta_eulerProduct_tprod` to
-- the real argument `(s : ℂ)` and simplify `((s : ℂ)).re = s`.
/-- Example 2.6: Euler's prime number formula expresses the Riemann zeta function for real `s > 1`
as the infinite product over all primes. -/
theorem euler_prime_number_formula {s : ℝ} (hs : 1 < s) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹ = riemannZeta (s : ℂ) := by
  have hs' : 1 < ((s : ℂ)).re := by
    simpa
  simpa using
    (riemannZeta_eulerProduct_tprod hs' :
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹ = riemannZeta (s : ℂ))
