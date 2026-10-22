/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_32

-- Declarations for this item will be appended below by the statement pipeline.

open Finset MeasureTheory ProbabilityTheory MeasurableEquiv Preorder
open scoped BigOperators ProbabilityTheory
open ProbabilityTheory.Kernel

noncomputable section

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

/-- The uniform Bernoulli law on `Bool`, used for the standard nonstationary counterexample with
constant tail coordinates. -/
def example203_counterexample_law : ProbabilityMeasure Bool :=
  ⟨(PMF.uniformOfFintype Bool).toMeasure, inferInstance⟩

-- Proof sketch: unfold `example203_counterexample_law`; it is defined to be the probability
-- measure associated with the uniform pmf on `Bool`.
/-- The counterexample law is the uniform law on `Bool`. -/
theorem example203_counterexample_law_eq_uniform :
    (example203_counterexample_law : Measure Bool) = (PMF.uniformOfFintype Bool).toMeasure := rfl

/-- The explicit counterexample process with `X₀(ω) = !ω` and `X_{n + 1}(ω) = ω`, so the tail is
constant while the initial coordinate is different. -/
def example203_counterexample_process : ℕ → Bool → Bool
  | 0, ω => !ω
  | _ + 1, ω => ω

-- Proof sketch: unfold `example203_counterexample_process`; every positive-time coordinate is the
-- identity map on `Bool`.
/-- Every positive-time coordinate of the counterexample process is the identity map on `Bool`. -/
theorem example203_counterexample_process_succ_apply (n : ℕ) (ω : Bool) :
    example203_counterexample_process (n + 1) ω = ω := rfl

/-- The textbook coefficients `c₁, …, c_k` induce the Chapter 9 owner coefficients by inserting
the zero coefficient `c₀ = 0`. -/
def movingAverageOneBasedWeights {k : ℕ} (c : Fin k → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => if h : i < k then c ⟨i, h⟩ else 0

-- Proof sketch: split the Chapter 9 moving-average sum into the zero term and the positive-time
-- tail; the inserted zero coefficient kills the `i = 0` term, and the remaining range is exactly
-- the textbook sum over `l = 1, ..., k`.
/-- The Chapter 9 moving-average owner recovers the textbook one-based finite sum after inserting
the zero coefficient `c₀ = 0`. -/
theorem movingAverageProcess_oneBased_apply {Ω' : Type u} (Y : ℤ → Ω' → ℝ) {k : ℕ}
    (c : Fin k → ℝ) (n : ℤ) (ω : Ω') :
    movingAverageProcess Y (movingAverageOneBasedWeights c) k n ω =
      ∑ l : Fin k, c l * Y (n - (((l : ℕ) + 1 : ℕ) : ℤ)) ω := by
  rw [movingAverageProcess_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ movingAverageOneBasedWeights c i * Y (n - i) ω)
    (k + 1)]
  rw [Fin.sum_univ_succ]
  simp [movingAverageOneBasedWeights]

/- Example 20.3 (1): item (i). An i.i.d. process is stationary via the Chapter 9 owner theorem
`example_9_8_isIID_isStationary`. -/

/-- Helper for Example 20.3: the counterexample Bernoulli law is invariant under Boolean
negation. -/
theorem example203_counterexample_law_map_not :
    Measure.map (fun ω : Bool ↦ !ω) (example203_counterexample_law : Measure Bool) =
      (example203_counterexample_law : Measure Bool) := by
  -- Proof comment: rewrite both measures as the uniform law on `Bool` and compare all measurable
  -- sets through the induced `PMF.map`.
  have hmap :
      Measure.map (fun ω : Bool ↦ !ω) ((PMF.uniformOfFintype Bool).toMeasure) =
        ((PMF.uniformOfFintype Bool).map (fun ω : Bool ↦ !ω)).toMeasure := by
    simpa using
      (PMF.toMeasure_map
        (p := PMF.uniformOfFintype Bool)
        (f := fun ω : Bool ↦ !ω)
        (hf := by fun_prop))
  rw [example203_counterexample_law_eq_uniform, hmap]
  congr
  ext b
  fin_cases b <;> simp [PMF.uniformOfFintype_apply]

/-- Helper for Example 20.3: stationarity of the path law forces equality in distribution of the
consecutive coordinate pairs `(X₁, X₂)` and `(X₀, X₁)` for the counterexample process. -/
theorem counterexamplePairIdentDistrib_of_stationary
    (hX :
      IsStationaryProcess
        example203_counterexample_process
        (example203_counterexample_law : Measure Bool)) :
    IdentDistrib
      (fun ω ↦
        (example203_counterexample_process 1 ω, example203_counterexample_process 2 ω))
      (fun ω ↦
        (example203_counterexample_process 0 ω, example203_counterexample_process 1 ω))
      (example203_counterexample_law : Measure Bool)
      (example203_counterexample_law : Measure Bool) := by
  -- Proof comment: specialize stationarity to the shift `1` and read off the first two
  -- coordinates of the shifted and unshifted paths.
  let pairAtZeroOne : (ℕ → Bool) → Bool × Bool := fun x ↦ (x 0, x 1)
  have hpair :
      IdentDistrib
        (pairAtZeroOne ∘ fun ω t ↦ example203_counterexample_process (1 + t) ω)
        (pairAtZeroOne ∘ fun ω t ↦ example203_counterexample_process t ω)
        (example203_counterexample_law : Measure Bool)
        (example203_counterexample_law : Measure Bool) :=
    (hX 1).comp (by
      dsimp [pairAtZeroOne]
      fun_prop)
  -- Proof comment: unfold the pair projection after the shift.
  simpa [pairAtZeroOne, example203_counterexample_process] using hpair

/-- Helper for Example 20.3: iterating the one-sided shift drops the first `s` coordinates of a
path. -/
theorem tailIterate_apply (s : ℕ) (x : Stream' E) (t : ℕ) :
    (Stream'.tail^[s]) x t = x (s + t) := by
  induction s generalizing x t with
  | zero =>
      -- Proof comment: the zeroth iterate is the identity map.
      simp
  | succ s hs =>
      -- Proof comment: one more iterate applies `Stream'.tail` once and then uses the induction
      -- hypothesis on the remaining `s` iterates.
      rw [Function.iterate_succ, Function.comp_apply]
      simpa [Stream'.tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hs (x := Stream'.tail x) (t := t)

/-- Helper for Example 20.3: the shifted canonical path is the corresponding iterate of
`Stream'.tail`. -/
theorem shiftedCanonicalPath_eq_tailIterate (s : ℕ) :
    (fun x : Stream' E ↦ fun t : ℕ ↦ Function.eval (s + t) x) = Stream'.tail^[s] := by
  -- Proof comment: compare both path-valued maps coordinatewise and use `tailIterate_apply`.
  ext x t
  simpa [Function.eval] using (tailIterate_apply (E := E) s x t).symm

/-- Helper for Example 20.3: the one-sided shift `Stream'.tail` is measurable on path space. -/
theorem measurable_tail : Measurable (Stream'.tail : Stream' E → Stream' E) := by
  -- Proof comment: every shifted coordinate map is measurable, so the product map is measurable.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [Stream'.tail] using (measurable_pi_apply (i + 1 : ℕ))

/-- Helper for Example 20.3: invariance of a path law under `Stream'.tail` implies stationarity of
the canonical coordinate process. -/
theorem identDistrib_shiftedCanonicalPath_of_tailInvariant
    (P : Measure (Stream' E)) (htail : Measure.map Stream'.tail P = P) (s : ℕ) :
    IdentDistrib (fun x t ↦ x (s + t)) (fun x t ↦ x t) P P := by
  -- Proof comment: package the one-step tail invariance as a measure-preserving map and iterate
  -- it exactly as in the canonical path-space criterion.
  have htailMeas : Measurable (Stream'.tail : Stream' E → Stream' E) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Stream'.tail] using (measurable_pi_apply (i + 1 : ℕ))
  let hτ : MeasurePreserving Stream'.tail P P := ⟨htailMeas, htail⟩
  let hsPres : MeasurePreserving (Stream'.tail^[s]) P P := hτ.iterate s
  have hshiftedEval :
      (fun x : Stream' E ↦ fun t : ℕ ↦ Function.eval (s + t) x) = Stream'.tail^[s] :=
    shiftedCanonicalPath_eq_tailIterate (E := E) s
  have hshifted :
      (fun x : Stream' E ↦ fun t : ℕ ↦ x (s + t)) = Stream'.tail^[s] := by
    simpa [Function.eval] using hshiftedEval
  have hmapShifted :
      Measure.map (fun x t ↦ Function.eval (s + t) x) P = Measure.map (Stream'.tail^[s]) P :=
    congrArg (fun f ↦ Measure.map f P) hshiftedEval
  refine
    { aemeasurable_fst := ?_
      aemeasurable_snd := ?_
      map_eq := ?_ }
  · -- Proof comment: rewrite the shifted path map as an iterate of the measurable tail map.
    exact hshifted ▸ hsPres.measurable.aemeasurable
  · -- Proof comment: the unshifted canonical path is the identity on path space.
    simpa [Function.eval] using measurable_id.aemeasurable
  · -- Proof comment: the path map equality follows from the iterated tail invariance.
    simpa [Function.eval] using
      (hmapShifted.trans <| hsPres.map_eq.trans <| by
        exact (Measure.map_id (μ := P)).symm)

/-- Helper for Example 20.3: `dropFirstPrefix n` forgets the time-`0` coordinate of a history on
`Iic (n + 1)`, reindexing the remaining coordinates as a history on `Iic n`. -/
def dropFirstPrefix (n : ℕ) : (Π i : Iic (n + 1), E) → Π i : Iic n, E :=
  fun x j ↦ x ⟨j.1 + 1, mem_Iic.2 (Nat.succ_le_succ (mem_Iic.1 j.2))⟩

/-- Helper for Example 20.3: `dropFirstPrefix` is measurable because each output coordinate is a
coordinate projection on the longer prefix space. -/
@[fun_prop] theorem measurable_dropFirstPrefix (n : ℕ) :
    Measurable (dropFirstPrefix (E := E) n) := by
  -- Proof comment: product measurability reduces to measurability of each shifted coordinate.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [dropFirstPrefix] using
    (measurable_pi_apply
      (⟨i.1 + 1, mem_Iic.2 (Nat.succ_le_succ (mem_Iic.1 i.2))⟩ : Iic (n + 1)))

/-- Helper for Example 20.3: restricting a shifted path to times `≤ n` is the same as first
restricting to times `≤ n + 1` and then dropping the initial coordinate. -/
theorem dropFirstPrefix_frestrictLe_succ (n : ℕ) (x : Stream' E) :
    dropFirstPrefix (E := E) n (frestrictLe (n + 1) x) = frestrictLe n (Stream'.tail x) := by
  -- Proof comment: both sides evaluate to the coordinate `x (i + 1)` at each index `i ≤ n`.
  ext i
  rfl

/-- Helper for Example 20.3: restricting the shifted path is the same as dropping the initial
coordinate after restricting the original path one step further. -/
theorem frestrictLe_tail_eq_dropFirstPrefix_comp_frestrictLeSucc
    (n : ℕ) :
    (frestrictLe n : Stream' E → Π i : Iic n, E) ∘ Stream'.tail =
      dropFirstPrefix (E := E) n ∘ frestrictLe (n + 1) := by
  -- Proof comment: this is the function-level packaging of
  -- `dropFirstPrefix_frestrictLe_succ` for later `Measure.map_map` rewrites.
  funext x
  exact (dropFirstPrefix_frestrictLe_succ (E := E) n x).symm

/-- Helper for Example 20.3: repack the last state of a one-step history as the unique
length-zero history. -/
def lastStateAsHistory : (Π i : Iic 1, E) → Π i : Iic 0, E :=
  fun x _ ↦ x ⟨1, mem_Iic.2 le_rfl⟩

/-- Helper for Example 20.3: `lastStateAsHistory` is measurable because each output coordinate is
the terminal coordinate projection on `Iic 1`. -/
@[fun_prop] theorem measurable_lastStateAsHistory :
    Measurable (lastStateAsHistory (E := E)) := by
  -- Proof comment: the codomain is a singleton product, so measurability reduces to the last
  -- coordinate projection.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [lastStateAsHistory] using
    (measurable_pi_apply (⟨1, mem_Iic.2 le_rfl⟩ : Iic 1))

/-- Helper for Example 20.3: on one-step histories, dropping the initial coordinate is exactly the
same as repacking the terminal state as the unique length-zero history. -/
theorem dropFirstPrefix_zero_eq_lastStateAsHistory :
    dropFirstPrefix (E := E) 0 = lastStateAsHistory (E := E) := by
  -- Proof comment: both maps send a one-step history to its time-`1` coordinate.
  ext x i
  rcases i with ⟨i, hi⟩
  have hi0 : i = 0 := Nat.eq_zero_of_le_zero (mem_Iic.1 hi)
  subst hi0
  rfl

/-- Helper for Example 20.3: repacking the terminal state of a one-step history is the same as
evaluating that terminal state and then packaging it as the unique length-zero history. -/
theorem lastStateAsHistory_eq_piUniqueSymm_comp :
    lastStateAsHistory (E := E) =
      (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm ∘
        (fun x : Π i : Iic 1, E ↦ x ⟨1, mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: both sides produce the unique zero-length history whose sole coordinate is the
  -- last state of the one-step history.
  funext x
  ext i
  simp [lastStateAsHistory, MeasurableEquiv.piUnique]

/-- Helper for Example 20.3: the homogeneous Markov trajectory kernel reads only the last state of
a finite history before applying `κ`. -/
def homogeneousTrajectoryKernel (κ : Kernel E E) (n : ℕ) : Kernel (Π i : Iic n, E) E :=
  comap κ (fun x : Π i : Iic n, E ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop)

/-- Helper for Example 20.3: `succHistoryEquiv` records the dropped prefix and terminal state of a
successor history. -/
noncomputable def succHistoryEquiv (n : ℕ) :
    (Π i : Iic (n + 1), E) ≃ᵐ ((Π i : Iic n, E) × E) :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ ↦ E) (Nat.le_succ n)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n).symm)

/-- Helper for Example 20.3: `succHistoryEquiv` splits a successor history into the truncated
prefix and the final state. -/
@[simp] theorem succHistoryEquiv_apply
    (n : ℕ) (z : Π i : Iic (n + 1), E) :
    succHistoryEquiv (E := E) n z =
      (frestrictLe₂ (π := fun _ : ℕ ↦ E) (Nat.le_succ n) z,
        z ⟨n + 1, mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: unfold the measurable equivalence and read off its two coordinates.
  rfl

/-- Helper for Example 20.3: the inverse of `succHistoryEquiv` glues a prefix history and a final
state back into the corresponding successor history. -/
@[simp] theorem succHistoryEquiv_symm_apply
    (n : ℕ) (z : (Π i : Iic n, E) × E) :
    (succHistoryEquiv (E := E) n).symm z =
      _root_.IicProdIoc (X := fun _ : ℕ ↦ E) n (n + 1)
        (z.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n z.2) := by
  -- Proof comment: unfold `succHistoryEquiv`; its inverse restores the singleton tail and then
  -- applies the canonical `IicProdIoc` gluing map.
  rfl

/-- Helper for Example 20.3: after gluing a prefix history with a one-point tail, applying
`succHistoryEquiv` recovers the prefix together with the terminal state. -/
@[simp] theorem succHistoryEquiv_apply_IicProdIoc
    (n : ℕ) (z : (Π i : Iic n, E) × (Π i : Ioc n (n + 1), E)) :
    succHistoryEquiv (E := E) n
        (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) n (n + 1) z) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n).symm z := by
  -- Proof comment: `succHistoryEquiv` splits the glued successor history back into its stored
  -- prefix restriction and unique terminal coordinate.
  rcases z with ⟨z₁, z₂⟩
  ext i
  · simpa [succHistoryEquiv_apply] using
      congrFun
        (congrFun
          (frestrictLe₂_comp_IicProdIoc (X := fun _ : ℕ ↦ E) (hab := Nat.le_succ n))
          (z₁, z₂))
        i
  · simp [succHistoryEquiv_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- Helper for Example 20.3: package the pointwise `succHistoryEquiv` normalization as the
function equality consumed by `Kernel.map_comp_right`. -/
theorem succHistoryEquiv_comp_IicProdIoc
    (n : ℕ) :
    succHistoryEquiv (E := E) n ∘
        _root_.IicProdIoc (X := fun _ : ℕ ↦ E) n (n + 1) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n).symm := by
  -- Proof comment: the previous pointwise lemma is exactly the composed-map normal form needed
  -- when rewriting mapped successor-history kernels.
  funext z
  simpa using succHistoryEquiv_apply_IicProdIoc (E := E) n z

/-- Helper for Example 20.3: dropping time `0` from a successor history and then splitting by
`succHistoryEquiv` is the same as first splitting and then dropping time `0` from the prefix
component. -/
@[simp] theorem succHistoryEquiv_apply_dropFirstPrefix
    (n : ℕ) (z : Π i : Iic (n + 2), E) :
    succHistoryEquiv (E := E) n (dropFirstPrefix (E := E) (n + 1) z) =
      Prod.map (dropFirstPrefix (E := E) n) id (succHistoryEquiv (E := E) (n + 1) z) := by
  -- Proof comment: both sides remember the dropped prefix and the terminal coordinate of `z`.
  ext i
  · simp [succHistoryEquiv_apply, dropFirstPrefix]
  · rfl

/-- Helper for Example 20.3: `dropFirstPrefix` is conjugate to the product map that drops time `0`
from the prefix component under `succHistoryEquiv`. -/
theorem dropFirstPrefix_eq_succHistoryEquiv_comp
    (n : ℕ) :
    dropFirstPrefix (E := E) (n + 1) =
      (succHistoryEquiv (E := E) n).symm ∘
        Prod.map (dropFirstPrefix (E := E) n) id ∘
        succHistoryEquiv (E := E) (n + 1) := by
  -- Proof comment: apply `succHistoryEquiv` to both sides and use the previous componentwise
  -- description after dropping the first coordinate.
  funext z
  ext i
  by_cases hi : i.1 ≤ n
  · simp [Function.comp, succHistoryEquiv_symm_apply, _root_.IicProdIoc_def, dropFirstPrefix,
      MeasurableEquiv.piSingleton, hi]
  · simp [Function.comp, succHistoryEquiv_symm_apply, _root_.IicProdIoc_def, dropFirstPrefix,
      MeasurableEquiv.piSingleton, hi]
    have hi_eq : i.1 = n + 1 := by
      exact le_antisymm (mem_Iic.1 i.2) (Nat.succ_le_of_lt (lt_of_not_ge hi))
    simpa [hi_eq]

/-- Helper for Example 20.3: the homogeneous kernel at stage `n + 1` is obtained from the stage-`n`
kernel by forgetting the initial coordinate of the history. -/
theorem homogeneousTrajectoryKernel_comap_dropFirstPrefix
    (κ : Kernel E E) (n : ℕ) :
    homogeneousTrajectoryKernel (E := E) κ (n + 1) =
      (homogeneousTrajectoryKernel (E := E) κ n).comap
        (dropFirstPrefix (E := E) n) (measurable_dropFirstPrefix (E := E) n) := by
  -- Proof comment: both kernels evaluate `κ` at the same terminal state of the history.
  ext x s hs
  simp [homogeneousTrajectoryKernel, dropFirstPrefix]

/-- Helper for Example 20.3: under `succHistoryEquiv`, a one-step homogeneous partial trajectory
splits as the current history together with the next-state kernel. -/
theorem partialTraj_succ_self_map_succHistoryEquiv
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    ((partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) n (n + 1)).map
      (succHistoryEquiv (E := E) n)) =
      Kernel.id ×ₖ homogeneousTrajectoryKernel (E := E) κ n := by
  let _ : IsMarkovKernel (homogeneousTrajectoryKernel (E := E) κ n) := by
    dsimp [homogeneousTrajectoryKernel]
    infer_instance
  let _ : IsSFiniteKernel
      ((homogeneousTrajectoryKernel (E := E) κ n).map
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n)) := by
    infer_instance
  -- Route correction: normalize the mapped successor kernel before comparing coordinates, exactly
  -- as in the stable sibling proof from `Example_20_32`.
  -- Proof comment: rewrite the one-step partial trajectory by `partialTraj_succ_self`, then
  -- collapse the singleton tail coordinate through `succHistoryEquiv`.
  rw [ProbabilityTheory.Kernel.partialTraj_succ_self
    (X := fun _ : ℕ ↦ E) (κ := homogeneousTrajectoryKernel (E := E) κ) n]
  rw [← Kernel.map_comp_right
    (κ := Kernel.id ×ₖ
      ((homogeneousTrajectoryKernel (E := E) κ n).map
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n)))
    (f := _root_.IicProdIoc (X := fun _ : ℕ ↦ E) n (n + 1))
    (g := succHistoryEquiv (E := E) n) measurable_IicProdIoc (by fun_prop)]
  rw [succHistoryEquiv_comp_IicProdIoc]
  rw [← Kernel.map_prod_map _ _ measurable_id
    (MeasurableEquiv.symm (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n)).measurable]
  rw [Kernel.map_id]
  rw [← Kernel.map_comp_right
    (κ := homogeneousTrajectoryKernel (E := E) κ n)
    (f := MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n)
    (g := (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n).symm)
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n).measurable
    (MeasurableEquiv.symm (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n)).measurable]
  simpa using (Kernel.map_id (homogeneousTrajectoryKernel (E := E) κ n))

/-- Helper for Example 20.3: mapping the product split back through
`succHistoryEquiv.symm` reconstructs the one-step homogeneous partial trajectory. -/
theorem idProd_homogeneousTrajectoryKernel_map_succHistoryEquiv_symm
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    ((Kernel.id ×ₖ homogeneousTrajectoryKernel (E := E) κ n).map
      (succHistoryEquiv (E := E) n).symm) =
      partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) n (n + 1) := by
  -- Proof comment: invert the previous measurable-equivalence pushforward.
  exact
    ((Kernel.map_apply_eq_iff_map_symm_apply_eq
      (κ := partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) n (n + 1))
      (f := succHistoryEquiv (E := E) n)
      (η := Kernel.id ×ₖ homogeneousTrajectoryKernel (E := E) κ n)).1
      (partialTraj_succ_self_map_succHistoryEquiv (E := E) κ n)).symm

/-- Helper for Example 20.3: dropping the initial coordinate after one more homogeneous Markov
step is the same as first dropping the initial coordinate of the current prefix and then taking one
homogeneous Markov step from the shortened history. -/
theorem partialTraj_succ_map_dropFirstPrefix
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    (partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) (n + 1)
      (n + 2)).map
      (dropFirstPrefix (E := E) (n + 1)) =
      partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) n (n + 1) ∘ₖ
        Kernel.deterministic (dropFirstPrefix (E := E) n)
          (measurable_dropFirstPrefix (E := E) n) := by
  letI : ∀ m, IsMarkovKernel (homogeneousTrajectoryKernel (E := E) κ m) := fun m ↦ by
    dsimp [homogeneousTrajectoryKernel]
    infer_instance
  letI : ∀ m, IsSFiniteKernel (homogeneousTrajectoryKernel (E := E) κ m) := fun m ↦ by
    dsimp [homogeneousTrajectoryKernel]
    infer_instance
  -- Proof comment: normalize the left-hand side by splitting a successor history into its dropped
  -- prefix and terminal state through `succHistoryEquiv`.
  calc
    (partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) (n + 1)
        (n + 2)).map
        (dropFirstPrefix (E := E) (n + 1)) =
      ((((partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) (n + 1)
            (n + 2)).map (succHistoryEquiv (E := E) (n + 1))).map
          (Prod.map (dropFirstPrefix (E := E) n) id)).map
        (succHistoryEquiv (E := E) n).symm) := by
          rw [dropFirstPrefix_eq_succHistoryEquiv_comp]
          calc
            (partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) (n + 1)
                (n + 2)).map
                (((succHistoryEquiv (E := E) n).symm ∘
                  Prod.map (dropFirstPrefix (E := E) n) id) ∘
                  succHistoryEquiv (E := E) (n + 1)) =
              (((partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ)
                    (n + 1) (n + 2)).map
                  (succHistoryEquiv (E := E) (n + 1))).map
                ((succHistoryEquiv (E := E) n).symm ∘
                  Prod.map (dropFirstPrefix (E := E) n) id)) := by
                    simpa [Function.comp] using
                      (Kernel.map_comp_right
                        (κ := partialTraj (X := fun _ : ℕ ↦ E)
                          (homogeneousTrajectoryKernel (E := E) κ) (n + 1) (n + 2))
                        (f := succHistoryEquiv (E := E) (n + 1))
                        (g := (succHistoryEquiv (E := E) n).symm ∘
                          Prod.map (dropFirstPrefix (E := E) n) id)
                        (MeasurableEquiv.measurable (succHistoryEquiv (E := E) (n + 1)))
                        (by fun_prop))
            _ =
              ((((partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ)
                    (n + 1) (n + 2)).map
                  (succHistoryEquiv (E := E) (n + 1))).map
                (Prod.map (dropFirstPrefix (E := E) n) id)).map
                (succHistoryEquiv (E := E) n).symm) := by
                  simpa [Function.comp] using
                    (Kernel.map_comp_right
                      (κ := (partialTraj (X := fun _ : ℕ ↦ E)
                        (homogeneousTrajectoryKernel (E := E) κ) (n + 1) (n + 2)).map
                          (succHistoryEquiv (E := E) (n + 1)))
                      (f := Prod.map (dropFirstPrefix (E := E) n) id)
                      (g := (succHistoryEquiv (E := E) n).symm)
                      (by fun_prop)
                      (MeasurableEquiv.symm (succHistoryEquiv (E := E) n)).measurable)
    _ =
      ((((Kernel.id ×ₖ homogeneousTrajectoryKernel (E := E) κ (n + 1)).map
          (Prod.map (dropFirstPrefix (E := E) n) id)).map
        (succHistoryEquiv (E := E) n).symm)) := by
          rw [partialTraj_succ_self_map_succHistoryEquiv (E := E) κ (n + 1)]
    _ =
      ((Kernel.deterministic (dropFirstPrefix (E := E) n)
          (measurable_dropFirstPrefix (E := E) n) ×ₖ
        homogeneousTrajectoryKernel (E := E) κ (n + 1)).map
          (succHistoryEquiv (E := E) n).symm) := by
            rw [← Kernel.map_prod_map _ _ (measurable_dropFirstPrefix (E := E) n) measurable_id]
            rw [Kernel.id_map (measurable_dropFirstPrefix (E := E) n), Kernel.map_id]
    _ =
      partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) n (n + 1) ∘ₖ
        Kernel.deterministic (dropFirstPrefix (E := E) n)
          (measurable_dropFirstPrefix (E := E) n) := by
            -- Proof comment: rewrite the common normal form back as the deterministic dropped
            -- prefix followed by the shorter homogeneous extension kernel.
            rw [← Kernel.id_comap (measurable_dropFirstPrefix (E := E) n)]
            rw [homogeneousTrajectoryKernel_comap_dropFirstPrefix (E := E) κ n]
            rw [← Kernel.comap_prod]
            rw [← Kernel.comap_map_comm
              (κ := Kernel.id ×ₖ homogeneousTrajectoryKernel (E := E) κ n)
              (f := dropFirstPrefix (E := E) n)
              (g := (succHistoryEquiv (E := E) n).symm)
              (measurable_dropFirstPrefix (E := E) n)
              (MeasurableEquiv.symm (succHistoryEquiv (E := E) n)).measurable]
            rw [idProd_homogeneousTrajectoryKernel_map_succHistoryEquiv_symm (E := E) κ n]
            rw [← Kernel.comp_deterministic_eq_comap]
            rw [Kernel.id_comap (measurable_dropFirstPrefix (E := E) n)]

/-- Helper for Example 20.3: after dropping the first coordinate of a homogeneous Markov prefix
law, one obtains the restarted homogeneous prefix law driven by the time-`1` initial state. -/
theorem partialTraj_map_dropFirstPrefix_eq_restart
    (κ : Kernel E E) [IsMarkovKernel κ] :
    ∀ n : ℕ,
      (partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) 0 (n + 1)).map
        (dropFirstPrefix (E := E) n) =
        partialTraj (X := fun _ : ℕ ↦ E) (homogeneousTrajectoryKernel (E := E) κ) 0 n ∘ₖ
          ((homogeneousTrajectoryKernel (E := E) κ 0).map
            (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm)
  | 0 => by
      letI : ∀ m, IsMarkovKernel (homogeneousTrajectoryKernel (E := E) κ m) := fun m ↦ by
        dsimp [homogeneousTrajectoryKernel]
        infer_instance
      -- Proof comment: the one-step prefix law maps to the last state, and that last state is
      -- exactly the unique zero-length history after packaging with `piUnique.symm`.
      rw [dropFirstPrefix_zero_eq_lastStateAsHistory]
      rw [lastStateAsHistory_eq_piUniqueSymm_comp]
      rw [Kernel.map_comp_right
        (κ := partialTraj (X := fun _ : ℕ ↦ E)
          (homogeneousTrajectoryKernel (E := E) κ) 0 1)
        (f := fun x : Π i : Iic 1, E ↦ x ⟨1, mem_Iic.2 le_rfl⟩)
        (g := (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm)
        (by fun_prop)
        (MeasurableEquiv.symm (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E))).measurable]
      rw [ProbabilityTheory.Kernel.map_partialTraj_succ_self
        (X := fun _ : ℕ ↦ E) (κ := homogeneousTrajectoryKernel (E := E) κ) 0]
      rw [ProbabilityTheory.Kernel.partialTraj_self (X := fun _ : ℕ ↦ E)
        (κ := homogeneousTrajectoryKernel (E := E) κ) 0]
      rw [Kernel.id_comp]
  | n + 1 => by
      letI : ∀ m, IsMarkovKernel (homogeneousTrajectoryKernel (E := E) κ m) := fun m ↦ by
        dsimp [homogeneousTrajectoryKernel]
        infer_instance
      -- Proof comment: split the longer prefix law at time `n + 1`, apply the one-step dropped
      -- prefix bridge, and then insert the induction hypothesis for the shortened prefix.
      rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
        (X := fun _ : ℕ ↦ E) (κ := homogeneousTrajectoryKernel (E := E) κ) (Nat.zero_le (n + 1))]
      rw [Kernel.map_comp]
      rw [partialTraj_succ_map_dropFirstPrefix (E := E) κ n]
      rw [Kernel.comp_assoc]
      rw [Kernel.deterministic_comp_eq_map (measurable_dropFirstPrefix (E := E) n)]
      rw [partialTraj_map_dropFirstPrefix_eq_restart (κ := κ) n]
      rw [← Kernel.comp_assoc]
      rw [ProbabilityTheory.Kernel.partialTraj_comp_partialTraj
        (X := fun _ : ℕ ↦ E) (κ := homogeneousTrajectoryKernel (E := E) κ)
        (Nat.zero_le n) (Nat.le_succ n)]

/-- Helper for Example 20.3: the `n`-prefix marginal of the shifted path law is the dropped
`(n + 1)`-prefix marginal of the original path law. -/
theorem trajMeasure_tailPrefixMarginal_eq
    (P : Measure (Stream' E)) (n : ℕ) :
    ((Measure.map Stream'.tail P).map (frestrictLe n)) =
      (P.map (frestrictLe (n + 1))).map (dropFirstPrefix (E := E) n) := by
  -- Proof comment: expand both iterated pushforwards to the corresponding composed map and then
  -- use the already isolated finite-prefix identity for `Stream'.tail`.
  calc
    ((Measure.map Stream'.tail P).map (frestrictLe n)) =
      P.map ((frestrictLe n) ∘ Stream'.tail) := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := P) (f := Stream'.tail) (g := frestrictLe n)
            (measurable_frestrictLe n) measurable_tail)
    _ = P.map (dropFirstPrefix (E := E) n ∘ frestrictLe (n + 1)) := by
          rw [frestrictLe_tail_eq_dropFirstPrefix_comp_frestrictLeSucc (E := E) n]
    _ = (P.map (frestrictLe (n + 1))).map (dropFirstPrefix (E := E) n) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (μ := P) (f := frestrictLe (n + 1)) (g := dropFirstPrefix (E := E) n)
              (measurable_dropFirstPrefix (E := E) n) (measurable_frestrictLe (n + 1)))

/-- Helper for Example 20.3: composing the zero-step homogeneous history kernel with the packaged
initial law recovers the usual one-step pushforward `π.bind κ`. -/
theorem homogeneousTrajectoryKernel_zero_comp_initial
    (κ : Kernel E E) [IsMarkovKernel κ] (π : Measure E) :
    homogeneousTrajectoryKernel (E := E) κ 0 ∘ₘ
      π.map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm =
      (π.bind κ) := by
  let e : E ≃ᵐ Π i : Iic 0, E := (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm
  -- Proof comment: rewrite the packaged initial law as a deterministic composition, then collapse
  -- the two `comap`s because `e` followed by evaluation at the unique index is the identity.
  rw [← Measure.deterministic_comp_eq_map e.measurable, Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap]
  rw [homogeneousTrajectoryKernel]
  rw [← Kernel.comap_comp_right
    (κ := κ)
    (f := e)
    (g := fun x : Π i : Iic 0, E ↦ x ⟨0, mem_Iic.2 le_rfl⟩)
    e.measurable
    (by fun_prop)]
  have heval :
      ((fun x : Π i : Iic 0, E ↦ x ⟨0, mem_Iic.2 le_rfl⟩) ∘ e) = id := by
    funext x
    simp [e]
  simpa [heval] using (rfl : (Kernel.comap κ id measurable_id : Kernel E E) ∘ₘ π = κ ∘ₘ π)

/-- Helper for Example 20.3: packaging the one-step pushed-forward initial law as the unique
zero-length history commutes with the zero-step homogeneous history kernel. -/
theorem homogeneousTrajectoryKernel_zero_map_piUniqueSymm_comp_initial
    (κ : Kernel E E) [IsMarkovKernel κ] (π : Measure E) :
    ((homogeneousTrajectoryKernel (E := E) κ 0).map
      (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm) ∘ₘ
        π.map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm =
      (π.bind κ).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm := by
  -- Proof comment: move the final packaging map across the measure-kernel composition and then
  -- reuse the zero-step normalization.
  rw [← Measure.map_comp
    (μ := π.map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm)
    (κ := homogeneousTrajectoryKernel (E := E) κ 0)
    (f := (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm)
    (by fun_prop)]
  rw [homogeneousTrajectoryKernel_zero_comp_initial (E := E) κ π]

-- Proof sketch: the measure `example203_counterexample_law` is symmetric under `ω ↦ !ω`, while
-- every positive-time coordinate of `example203_counterexample_process` is the identity map; hence
-- each marginal has the same Bernoulli law.
/-- Supporting result for Example 20.3: item (i). The explicit process with
`X₁ = X₂ = X₃ = ...` still has the same one-dimensional marginal law at every time. -/
theorem example203_counterexample_identically_distributed (n : ℕ) :
    IdentDistrib
      (example203_counterexample_process n)
      (example203_counterexample_process 0)
      (example203_counterexample_law : Measure Bool)
      (example203_counterexample_law : Measure Bool) := by
  cases n with
  | zero =>
      -- Proof comment: time `0` is identically distributed with itself.
      simpa using
        (IdentDistrib.refl
          (μ := (example203_counterexample_law : Measure Bool))
          (f := fun ω : Bool ↦ !ω)
          ((by fun_prop : Measurable (fun ω : Bool ↦ !ω)).aemeasurable))
  | succ n =>
      -- Proof comment: every positive-time coordinate is the identity, while time `0` is Boolean
      -- negation; the counterexample law is symmetric under this negation.
      refine
        { aemeasurable_fst := measurable_id.aemeasurable
          aemeasurable_snd := (by
            fun_prop : Measurable (fun ω : Bool ↦ !ω)).aemeasurable
          map_eq := ?_ }
      calc
        Measure.map (example203_counterexample_process (n + 1))
            (example203_counterexample_law : Measure Bool)
            = Measure.map (fun ω : Bool ↦ ω) (example203_counterexample_law : Measure Bool) := by
              rfl
        _ = (example203_counterexample_law : Measure Bool) := by
              simp
        _ = Measure.map (fun ω : Bool ↦ !ω) (example203_counterexample_law : Measure Bool) := by
              rw [example203_counterexample_law_map_not]
        _ = Measure.map (example203_counterexample_process 0)
              (example203_counterexample_law : Measure Bool) := by
              rfl

-- Proof sketch: under this process, the shifted pair `(X₁, X₂)` is almost surely concentrated on
-- the diagonal because all positive-time coordinates agree, while `(X₀, X₁)` is not; therefore the
-- whole process law cannot be shift-invariant.
/-- Supporting result for Example 20.3: item (i). Equal one-dimensional marginals without
independence do not imply stationarity in general. -/
theorem example203_counterexample_not_stationary :
    ¬ IsStationaryProcess
      example203_counterexample_process
      (example203_counterexample_law : Measure Bool) := by
  intro hX
  let diagonal : Set (Bool × Bool) := {p | p.1 = p.2}
  have hdiag_meas : MeasurableSet diagonal := by
    -- Proof comment: every subset of the finite space `Bool × Bool` is measurable.
    classical
    exact (Set.toFinite diagonal).measurableSet
  have hpair_diag :
      ∀ᵐ ω ∂(example203_counterexample_law : Measure Bool),
        (example203_counterexample_process 1 ω, example203_counterexample_process 2 ω) ∈
          diagonal := by
    -- Proof comment: all positive-time coordinates coincide pointwise.
    filter_upwards [] with ω
    simp [diagonal, example203_counterexample_process]
  have hpair_zero_one_diag :
      ∀ᵐ ω ∂(example203_counterexample_law : Measure Bool),
        (example203_counterexample_process 0 ω, example203_counterexample_process 1 ω) ∈
          diagonal :=
    (counterexamplePairIdentDistrib_of_stationary hX).ae_snd hdiag_meas hpair_diag
  -- Proof comment: the pair `(X₀, X₁)` is always off the diagonal, contradicting the transferred
  -- almost-sure diagonal event.
  have hnot_diag :
      ¬ ∀ᵐ ω ∂(example203_counterexample_law : Measure Bool),
          (example203_counterexample_process 0 ω, example203_counterexample_process 1 ω) ∈
            diagonal := by
    simpa [diagonal, example203_counterexample_process] using
      (show ¬ ∀ᵐ ω ∂(example203_counterexample_law : Measure Bool), False from by
        intro hzero
        have hzero' : (example203_counterexample_law : Measure Bool) = 0 := by
          simpa using hzero
        have huniv :
            (example203_counterexample_law : Measure Bool) Set.univ ≠ 0 := by
          have huniv' :
              (example203_counterexample_law : Measure Bool) Set.univ = 1 := by
            simpa using (measure_univ (μ := (example203_counterexample_law : Measure Bool)))
          rw [huniv']
          norm_num
        exact huniv (by simpa using congrArg (fun μ : Measure Bool ↦ μ Set.univ) hzero'))
  exact hnot_diag hpair_zero_one_diag

-- Proof sketch: `Kernel.trajMeasure` builds the canonical path law of the homogeneous Markov
-- chain started from `π`. Since `π` is invariant under `κ`, every time shift of the coordinate
-- process has the same finite-dimensional distributions as the original one.
/-- Helper for Example 20.3: the homogeneous trajectory measure started from an invariant law is
 preserved by the one-sided shift. -/
theorem trajMeasure_map_tail_eq_self_of_invariant
    (κ : Kernel E E) [IsMarkovKernel κ] (π : ProbabilityMeasure E)
    (hπ : Invariant κ (π : Measure E)) :
    Measure.map Stream'.tail
      (trajMeasure
        (π : Measure E)
        (fun n ↦
          (comap κ (fun x : Π i : Iic n, E ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop) :
            Kernel (Π i : Iic n, E) E))) =
      trajMeasure
        (π : Measure E)
        (fun n ↦
          (comap κ (fun x : Π i : Iic n, E ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop) :
            Kernel (Π i : Iic n, E) E)) := by
  let η : (n : ℕ) → Kernel (Π i : Iic n, E) E :=
    fun n ↦ comap κ (fun x : Π i : Iic n, E ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop)
  let P : Measure (Stream' E) := trajMeasure (π : Measure E) η
  let μinit : Measure (Π i : Iic 0, E) :=
    (π : Measure E).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm
  letI : ∀ n, IsMarkovKernel (η n) := fun n ↦ by
    dsimp [η, homogeneousTrajectoryKernel]
    infer_instance
  have hPprob' :
      IsProbabilityMeasure (trajMeasure (X := fun _ : ℕ ↦ E) (π : Measure E) η) := by
    infer_instance
  have hPprob : IsProbabilityMeasure P := by
    simpa [P] using hPprob'
  have hP :
      IsProbabilityMeasure P ∧
        ∀ n : ℕ,
          P.map (frestrictLe n) =
            partialTraj (X := fun _ : ℕ ↦ E) η 0 n ∘ₘ μinit := by
    refine ⟨hPprob, ?_⟩
    intro n
    simpa [P, μinit] using
      (ProbabilityTheory.Kernel.trajMeasure_map_frestrictLe
        (X := fun _ : ℕ ↦ E) (μ₀ := (π : Measure E)) (κ := η) n)
  have hshiftInit :
      ((η 0).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm) ∘ₘ μinit =
        ((π : Measure E).bind κ).map
          (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm := by
    -- Proof comment: the first dropped coordinate restarts the chain from the time-`1`
    -- distribution, which is exactly `π.bind κ`.
    simpa [η, μinit] using
      homogeneousTrajectoryKernel_zero_map_piUniqueSymm_comp_initial
        (E := E) κ (π : Measure E)
  have hshift :
      IsProbabilityMeasure (Measure.map Stream'.tail P) ∧
        ∀ n : ℕ,
          (Measure.map Stream'.tail P).map (frestrictLe n) =
            partialTraj (X := fun _ : ℕ ↦ E) η 0 n ∘ₘ μinit := by
    refine ⟨Measure.isProbabilityMeasure_map measurable_tail.aemeasurable, ?_⟩
    intro n
    have hrestart :
        ((partialTraj (X := fun _ : ℕ ↦ E) η 0 (n + 1)).map
          (dropFirstPrefix (E := E) n)) =
          partialTraj (X := fun _ : ℕ ↦ E) η 0 n ∘ₖ
            ((η 0).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm) := by
      simpa [η] using partialTraj_map_dropFirstPrefix_eq_restart (E := E) (κ := κ) n
    -- Proof comment: compare the shifted and unshifted path laws on every finite prefix, rewrite
    -- the shifted prefix as a dropped longer prefix, then collapse the restarted initial law by
    -- invariance of `π`.
    calc
      (Measure.map Stream'.tail P).map (frestrictLe n) =
        (P.map (frestrictLe (n + 1))).map (dropFirstPrefix (E := E) n) := by
          exact trajMeasure_tailPrefixMarginal_eq (E := E) P n
      _ =
        ((partialTraj (X := fun _ : ℕ ↦ E) η 0 (n + 1) ∘ₘ μinit)).map
          (dropFirstPrefix (E := E) n) := by
            rw [hP.2 (n + 1)]
      _ =
        ((partialTraj (X := fun _ : ℕ ↦ E) η 0 (n + 1)).map
          (dropFirstPrefix (E := E) n)) ∘ₘ μinit := by
            rw [Measure.map_comp _ _ (measurable_dropFirstPrefix (E := E) n)]
      _ =
        (partialTraj (X := fun _ : ℕ ↦ E) η 0 n ∘ₖ
          ((η 0).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm)) ∘ₘ μinit := by
            rw [hrestart]
      _ =
        partialTraj (X := fun _ : ℕ ↦ E) η 0 n ∘ₘ
          (((η 0).map (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm) ∘ₘ μinit) := by
            rw [Measure.comp_assoc]
      _ =
        partialTraj (X := fun _ : ℕ ↦ E) η 0 n ∘ₘ
          (((π : Measure E).bind κ).map
            (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ E)).symm) := by
              rw [hshiftInit]
      _ =
        partialTraj (X := fun _ : ℕ ↦ E) η 0 n ∘ₘ μinit := by
          rw [hπ.def]
  rcases
      ProbabilityTheory.Kernel.existsUnique_probability_measure_with_prescribed_finite_dimensional_marginals
        (X := fun _ : ℕ ↦ E) (μ₀ := (π : Measure E)) (κ := η)
    with ⟨μ, hμ, huniq⟩
  -- Proof comment: both the canonical path law and its tail pushforward satisfy the same
  -- finite-dimensional characterization, so uniqueness identifies them.
  have hTailEq : Measure.map Stream'.tail P = P := by
    have hshiftEq : Measure.map Stream'.tail P = μ := huniq (Measure.map Stream'.tail P) hshift
    have hPEq : P = μ := huniq P hP
    exact hshiftEq.trans hPEq.symm
  simpa [P, η] using hTailEq

/-- Example 20.3 (4): item (ii). A Markov chain started from an invariant distribution is
stationary. -/

theorem coordinate_process_traj_measure_is_stationary_of_invariant
    (κ : Kernel E E) [IsMarkovKernel κ] (π : ProbabilityMeasure E)
    (hπ : Invariant κ (π : Measure E)) :
    IsStationaryProcess
      (fun n x ↦ x n)
      (trajMeasure
        (π : Measure E)
        (fun n ↦
          (comap κ (fun x : Π i : Iic n, E ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop) :
            Kernel (Π i : Iic n, E) E))) := by
  let η : (n : ℕ) → Kernel (Π i : Iic n, E) E :=
    fun n ↦ comap κ (fun x : Π i : Iic n, E ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop)
  let P : Measure (Stream' E) :=
    trajMeasure (π : Measure E) η
  have htail : Measure.map Stream'.tail P = P := by
    -- Proof comment: reduce stationarity to the one-step path-law invariance of the homogeneous
    -- Markov trajectory measure.
    simpa [P, η] using trajMeasure_map_tail_eq_self_of_invariant (κ := κ) (π := π) hπ
  -- Proof comment: once the path law is tail-invariant, stationarity of the coordinate process is
  -- the canonical path-space argument.
  change ∀ s,
      IdentDistrib (fun x t ↦ x (s + t)) (fun x t ↦ x t) P P
  intro s
  exact identDistrib_shiftedCanonicalPath_of_tailInvariant (E := E) P htail s

-- Proof sketch: each shifted moving-average coordinate is the same finite linear combination of a
-- shifted stationary family `Y`; after translating the textbook coefficients to the Chapter 9
-- owner coefficients, the result is exactly `movingAverageProcess_isStationary`.
/-- Supporting result for Example 20.3: item (iii). After inserting the zero coefficient `c₀ = 0`,
the Chapter 9 moving-average owner shows that the textbook finite linear filter
`X_n = ∑_{l=1}^k c_l Y_{n-l}` is stationary whenever `Y` is stationary. -/
theorem movingAverageProcess_isStationary_of_oneBasedCoefficients
    (μ : Measure Ω) (Y : ℤ → Ω → ℝ) {k : ℕ} (c : Fin k → ℝ)
    (hY_stationary : IsStationaryProcess Y μ) :
    IsStationaryProcess (movingAverageProcess Y (movingAverageOneBasedWeights c) k) μ :=
  movingAverageProcess_isStationary μ Y (movingAverageOneBasedWeights c) k hY_stationary
