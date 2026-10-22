/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {E : Type u} [MeasurableSpace E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

/-- Helper for Example 20.10: iterating the one-sided shift drops the first `n` coordinates of a
path. -/
private lemma iterateTail_apply (ω : Stream' E) (n k : ℕ) :
    (Stream'.tail^[n]) ω k = ω (n + k) := by
  induction n generalizing ω k with
  | zero =>
      -- Proof comment: the zeroth iterate of the shift is the identity map.
      simp
  | succ n ih =>
      -- Proof comment: one further iterate applies `Stream'.tail` once and then uses the
      -- induction hypothesis on the remaining `n` iterates.
      rw [Function.iterate_succ, Function.comp_apply]
      simpa [Stream'.tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (ω := Stream'.tail ω) (k := k)

/-- Helper for Example 20.10: the shifted path map is the `n`th iterate of `Stream'.tail`. -/
private lemma shiftedPath_eq_iterateTail (n : ℕ) :
    (fun ω : Stream' E ↦ fun t : ℕ ↦ Function.eval (n + t) ω) = Stream'.tail^[n] := by
  -- Proof comment: compare both path-valued maps coordinatewise and use the iterate formula.
  ext ω t
  simpa [Function.eval] using (iterateTail_apply (ω := ω) n t).symm

/-- Helper for Example 20.10: every iterate of a measure-preserving tail map gives the path-law
identity required for stationarity. -/
private lemma identDistrib_shiftedPath_of_measurePreservingTail
    (P : Measure (Stream' E)) (hτ : MeasurePreserving Stream'.tail P P) (n : ℕ) :
    IdentDistrib (fun ω t ↦ Function.eval (n + t) ω) (fun ω t ↦ Function.eval t ω) P P := by
  let hnPres : MeasurePreserving (Stream'.tail^[n]) P P := hτ.iterate n
  have hshiftedEval :
      (fun ω : Stream' E ↦ fun t : ℕ ↦ Function.eval (n + t) ω) = Stream'.tail^[n] :=
    shiftedPath_eq_iterateTail (E := E) n
  have hshifted : (fun ω : Stream' E ↦ fun t : ℕ ↦ ω (n + t)) = Stream'.tail^[n] := by
    simpa [Function.eval] using hshiftedEval
  have hmapShifted :
      Measure.map (fun ω t ↦ Function.eval (n + t) ω) P = Measure.map (Stream'.tail^[n]) P :=
    congrArg (fun f => Measure.map f P) hshiftedEval
  refine
    { aemeasurable_fst := ?_
      aemeasurable_snd := ?_
      map_eq := ?_ }
  · -- Proof comment: rewrite the shifted path map as the iterate of the measurable tail map.
    exact hshifted ▸ hnPres.measurable.aemeasurable
  · -- Proof comment: the unshifted path map is the identity on the path space.
    simpa [Function.eval] using measurable_id.aemeasurable
  · -- Proof comment: `MeasurePreserving.iterate` gives invariance under `Stream'.tail^[n]`.
    exact hmapShifted.trans <| hnPres.map_eq.trans <| by
      simpa [Function.eval] using (Measure.map_id (μ := P)).symm

-- Proof sketch: prove by induction on `n` that each iterate of `Stream'.tail` drops the first
-- `n` coordinates, and then evaluate the resulting identity at `0`.
/-- The `n`th coordinate of a path is the initial coordinate after `n` iterates of the one-sided
shift. -/
theorem coordinate_eq_zero_after_iterate_tail (ω : ℕ → E) (n : ℕ) :
    ω n = (Stream'.tail^[n]) ω 0 := by
  -- Proof comment: specialize the general iterate-of-tail formula to the zero coordinate.
  simpa using (iterateTail_apply (ω := ω) n 0).symm

-- Proof sketch: rewrite stationarity of the canonical coordinate process as invariance of the path
-- law under every iterate of `Stream'.tail`; the case `n = 1` is exactly
-- `MeasurePreserving Stream'.tail P P`, and conversely measure preservation of `Stream'.tail`
-- propagates to all iterates.
/-- Example 20.10: on the canonical path space `E^ℕ`, the coordinate process is stationary exactly
when the left shift preserves the path measure. -/
theorem canonical_process_stationary_iff_measurePreserving_tail
    (P : Measure (ℕ → E)) :
    IsStationaryProcess Function.eval P ↔ MeasurePreserving Stream'.tail P P := by
  constructor
  · intro hstationary
    have htailMeas : Measurable (Stream'.tail : Stream' E → Stream' E) := by
      -- Proof comment: each shifted coordinate map is measurable, so the tail map is measurable.
      refine measurable_pi_lambda _ fun i ↦ ?_
      simpa [Stream'.tail] using (measurable_pi_apply (i + 1 : ℕ))
    have htailEq :
        (Stream'.tail : Stream' E → Stream' E) = fun ω t ↦ Function.eval (1 + t) ω := by
      -- Proof comment: the one-step shift is the tail map on the canonical path space.
      ext ω t
      change ω.get (t + 1) = ω.get (1 + t)
      rw [Nat.add_comm]
    refine ⟨htailMeas, ?_⟩
    -- Proof comment: the one-step stationarity identity is exactly invariance under the tail map.
    calc
      Measure.map Stream'.tail P
          = Measure.map (fun ω t ↦ Function.eval (1 + t) ω) P :=
            congrArg (fun f => Measure.map f P) htailEq
      _ = Measure.map (fun ω t ↦ Function.eval t ω) P := (hstationary 1).map_eq
      _ = P := by
            simpa [Function.eval] using (Measure.map_id (μ := P))
  · intro hτ
    change ∀ n, IdentDistrib (fun ω t ↦ Function.eval (n + t) ω) (fun ω t ↦ Function.eval t ω) P P
    intro n
    -- Proof comment: iterate the measure-preserving tail map and rewrite the shifted path map.
    exact identDistrib_shiftedPath_of_measurePreservingTail (E := E) P hτ n
