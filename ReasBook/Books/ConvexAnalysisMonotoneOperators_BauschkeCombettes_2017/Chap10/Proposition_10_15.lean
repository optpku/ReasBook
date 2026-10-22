/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace EReal

/-- The nonnegative real power of an extended real, computed through its canonical
`ℝ≥0∞` representative. This is the bridge/view used when a source-facing nonnegative quantity is
expressed in the `EReal` owner API. -/
noncomputable def nnrpow (x : EReal) (p : ℝ) : EReal :=
  ENNReal.toEReal (x.toENNReal ^ p)

end EReal

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (g : H → NNReal) (p : ℝ)

local notation "gE" => Function.toEReal (fun x : H ↦ (g x : ℝ))
local notation "gPow" => Function.toEReal (fun x : H ↦ (g x : ℝ) ^ p)
local notation "φ" => exactModulusOfConvexity gE
local notation "χ" => exactModulusOfConvexity gPow

-- Proof sketch: apply the midpoint Jensen-gap estimate from the textbook proof to the finite
-- `EReal` models `(fun x ↦ (g x : ℝ)).toEReal` and `(fun x ↦ (g x : ℝ) ^ p).toEReal`, then use
-- Proposition 10.14 to pass from midpoint gaps to the exact modulus of convexity. The owner
-- modulus is `EReal`-valued, while the textbook lower bound uses the nonnegative power `φ(t)^p`;
-- `EReal.nnrpow` is the thin bridge/view that keeps the theorem surface at the exact-modulus
-- level and hides the `toENNReal`/`toEReal` conversion bookkeeping.
/-- Proposition 10.15: for a uniformly convex nonnegative real-valued function `g`, the exact
modulus of convexity of the pointwise power `g^p` is bounded below by
`2^(1 - 2p) * min (p * 2^(1 - p)) (1 - 2^(-p)) * φ^p`, where `φ` is the exact modulus of
convexity of `g`. -/
theorem exactModulusOfConvexity_nnreal_rpow_lower_bound
    (hp : 1 ≤ p) (hg : UniformlyConvex gE φ) (t : NNReal) :
    ((((2 : ℝ) ^ (1 - 2 * p) *
        min (p * (2 : ℝ) ^ (1 - p)) (1 - (2 : ℝ) ^ (-p))) : ℝ) : EReal) *
      (φ t).nnrpow p ≤
      χ t := sorry

-- Proof sketch: use the lower bound on the exact modulus from
-- `exactModulusOfConvexity_nnreal_rpow_lower_bound`; the modulus of `g` vanishes only at `0` by
-- `hg`, so the lower bound shows the exact modulus of `g^p` also vanishes only at `0`, and then
-- Corollary 10.13 gives uniform convexity with the exact modulus.
/-- The pointwise `p`-power of a uniformly convex nonnegative real-valued function is uniformly
convex with its exact modulus. -/
theorem uniformlyConvex_nnreal_rpow
    (hp : 1 ≤ p) (hg : UniformlyConvex gE φ) :
    UniformlyConvex gPow χ := sorry

end ERealFunction
