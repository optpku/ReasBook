/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

variable {Ω : Type u}

namespace Function

/-- Definition 1.95: A sequence of extended-real-valued maps on `Ω` increases pointwise to `f` if
for every `ω : Ω` the scalar sequence `n ↦ F n ω` is monotone and converges to `f ω`; this is the
meaning of the notation `F ↑ f`. The companion notation `F ↓ f` is formalized below by the
corresponding pointwise decreasing notion. -/
class IncreasesPointwiseTo (F : ℕ → Ω → EReal) (f : outParam (Ω → EReal)) : Prop where
  /-- At each point, the values of the sequence are monotone in the index. -/
  mono : ∀ ω : Ω, Monotone (fun n ↦ F n ω)
  /-- At each point, the sequence converges to the limiting value of `f`. -/
  tendsto : ∀ ω : Ω, Tendsto (fun n ↦ F n ω) atTop (nhds (f ω))

/-- A pointwise increasing sequence is canonically monotone at each point of the domain. -/
instance instMonotoneOfIncreasesPointwiseTo (ω : Ω) {F : ℕ → Ω → EReal} {f : Ω → EReal}
    [h : IncreasesPointwiseTo F f] : Monotone (fun n ↦ F n ω) :=
  h.mono ω

/-- A sequence of extended-real-valued maps on `Ω` decreases pointwise to `f` if for every
`ω : Ω` the scalar sequence `n ↦ F n ω` is antitone and converges to `f ω`. -/
class DecreasesPointwiseTo (F : ℕ → Ω → EReal) (f : outParam (Ω → EReal)) : Prop where
  /-- At each point, the values of the sequence are antitone in the index. -/
  antitone : ∀ ω : Ω, Antitone (fun n ↦ F n ω)
  /-- At each point, the sequence converges to the limiting value of `f`. -/
  tendsto : ∀ ω : Ω, Tendsto (fun n ↦ F n ω) atTop (nhds (f ω))

/-- A pointwise decreasing sequence is canonically antitone at each point of the domain. -/
instance instAntitoneOfDecreasesPointwiseTo (ω : Ω) {F : ℕ → Ω → EReal} {f : Ω → EReal}
    [h : DecreasesPointwiseTo F f] : Antitone (fun n ↦ F n ω) :=
  h.antitone ω

infixl:50 " ↑ " => IncreasesPointwiseTo
infixl:50 " ↓ " => DecreasesPointwiseTo

end Function
