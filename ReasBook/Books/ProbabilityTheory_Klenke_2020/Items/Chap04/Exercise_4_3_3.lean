/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Theorem_4_23

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoxIntegral intervalIntegral

local notation "unitIntervalSet" => Set.Icc (0 : ℝ) 1

-- Proof sketch: use Theorem 4.23 to identify the chapter's Riemann box integral on `[0,1]` with
-- the interval integral on `0..1`, then prove positivity of that interval integral.
/-- Exercise 4.3.3: if `f` is Riemann integrable on `[0,1]` and `f` is strictly positive on
`[0,1]`, then its Riemann integral on `[0,1]`, encoded by the chapter's box integral, is strictly
positive. -/
theorem riemannIntegral_pos_of_posOn_unitInterval
    {f : ℝ → ℝ}
    (hf : RiemannIntegrableOnUnitInterval f)
    (hpos : ∀ x ∈ unitIntervalSet, 0 < f x) :
    0 <
      integral (realIntervalBox 0 1 zero_lt_one) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := by
  rcases intervalIntegrable_and_intervalIntegral_eq_of_riemannIntegrable zero_lt_one hf with
    ⟨hf_interval, h_integral_eq⟩
  have h_interval_pos : 0 < ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral_pos_of_pos_on hf_interval
      (fun x hx ↦ hpos x <| Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩) zero_lt_one
  simpa [h_integral_eq] using h_interval_pos
