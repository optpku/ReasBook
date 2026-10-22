/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_3_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable (n : ℕ)

open scoped ConstrainedArgmin

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Algorithm 1.3.5 lies in the Chapter 1 value-oracle domain for box-constrained minimization.

Relevant owner-style declarations sampled before refining:
* `uniformGridPoint n` and `uniformGrid n` in `Theorem_1_3_6.lean`, where the midpoint grid is
  owned by its source-facing point map and derived range;
* `uniformGridPoint_mem_zeroOneBox` in `Theorem_1_3_6.lean`, the canonical feasibility bridge
  for those midpoint grid points;
* `DeterministicValueOracleMethod (zeroOneBox n)` in `Theorem_1_3_9.lean`, whose primitive
  query/output data are already `zeroOneBox n`-valued;
* `DeterministicValueOracleMethod.oracleTranscript` in `Theorem_1_3_9.lean`, the derived ordered
  sampled-value history;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Definition_1_3_3.lean`, the chapter owner of
  feasible minimizers, which packages both grid membership and minimality.

Owner abstraction:
* source-facing: `uniformGridMethod n p`;
* core/canonical: `DeterministicValueOracleMethod (zeroOneBox n)` together with
  `argmin[uniformGrid n p] f`;
* bridge/view: the finite ordered enumeration of the midpoint grid as feasible points of
  `zeroOneBox n`, and the transcript-based output theorem below.

Primitive data:
* the ordered feasible grid points queried by the method.

Derived API:
* the query/output rules of `uniformGridMethod`;
* the canonical `outputAfter` point after `p^n` calls;
* its canonical argmin membership, together with the grid-membership and `IsMinOn`
  companions derived from that owner statement. -/

/-- The `k`-th midpoint grid point in a fixed canonical ordering of the `p^n` grid points. -/
private noncomputable def orderedGridPoint (p : ℕ+) :
    Fin ((p : ℕ) ^ n) → zeroOneBox n :=
  fun k ↦
    let α := (Fintype.equivFinOfCardEq (by simp)).symm k
    ⟨uniformGridPoint n p α, uniformGridPoint_mem_zeroOneBox p α⟩

/-- Algorithm 1.3.5 as a deterministic value-oracle method: query the midpoint grid
`uniformGrid n p` in a canonical order and return the sampled grid point with minimal observed
value. -/
noncomputable def uniformGridMethod (p : ℕ+) : DeterministicValueOracleMethod (zeroOneBox n) where
  query transcript :=
    if hk : transcript.length < (p : ℕ) ^ n then
      orderedGridPoint n p ⟨transcript.length, hk⟩
    else
      orderedGridPoint n p 0
  output transcript :=
    match transcript.argmin Prod.snd with
    | some sample => sample.1
    | none => orderedGridPoint n p 0

/-- Helper for Algorithm 1.3.5: every canonically ordered grid point lies on the midpoint grid. -/
private theorem orderedGridPoint_mem_uniformGrid (p : ℕ+) (k : Fin ((p : ℕ) ^ n)) :
    (orderedGridPoint n p k : E) ∈ uniformGrid n p := by
  -- The ordered enumeration is obtained by reindexing the source grid points by `Fin ((p : ℕ)^n)`.
  refine ⟨(Fintype.equivFinOfCardEq (by simp)).symm k, ?_⟩
  simp [orderedGridPoint]

/-- Helper for Algorithm 1.3.5: the canonical ordering parametrizes every midpoint grid point. -/
private theorem mem_uniformGrid_iff_exists_orderedGridPoint (p : ℕ+) {x : E} :
    x ∈ uniformGrid n p ↔ ∃ k : Fin ((p : ℕ) ^ n), (orderedGridPoint n p k : E) = x := by
  constructor
  · rintro ⟨α, rfl⟩
    -- Reindex the given multi-index `α` through the canonical equivalence to obtain its position.
    refine ⟨Fintype.equivFinOfCardEq (by simp) α, ?_⟩
    simp [orderedGridPoint]
  · rintro ⟨k, rfl⟩
    exact orderedGridPoint_mem_uniformGrid n p k

/-- Helper for Algorithm 1.3.5: every deterministic oracle transcript has length equal to the
number of calls already made. -/
private theorem oracleTranscript_length {X : Type*} (method : DeterministicValueOracleMethod X)
    (oracle : X → ℝ) (k : ℕ) :
    (method.oracleTranscript oracle k).length = k := by
  induction k with
  | zero =>
      -- Before any call, the transcript is empty.
      simp
  | succ k ih =>
      -- Each new oracle call appends exactly one sampled pair to the existing transcript.
      rw [DeterministicValueOracleMethod.oracleTranscript_succ, List.length_append, ih]
      simp

/-- Helper for Algorithm 1.3.5: after `k ≤ p^n` calls, the transcript of `uniformGridMethod`
contains exactly the first `k` ordered midpoint-grid samples. -/
private theorem oracleTranscript_uniformGridMethod_eq_of_le
    (p : ℕ+) (f : E → ℝ) {k : ℕ} (hk : k ≤ (p : ℕ) ^ n) :
    (uniformGridMethod n p).oracleTranscript (f ∘ (↑)) k =
      List.ofFn (fun i : Fin k =>
        (orderedGridPoint n p (Fin.castLE hk i), f (orderedGridPoint n p (Fin.castLE hk i)))) := by
  induction k with
  | zero =>
      -- With zero calls, both sides are definitionally the empty transcript.
      simp [DeterministicValueOracleMethod.oracleTranscript]
  | succ k ih =>
      have hk_le : k ≤ (p : ℕ) ^ n := Nat.le_of_succ_le hk
      have hk_lt : k < (p : ℕ) ^ n := Nat.lt_of_succ_le hk
      have hquery :
          (uniformGridMethod n p).queryAfter (f ∘ (↑)) k =
            orderedGridPoint n p ⟨k, hk_lt⟩ := by
        -- The query rule reads the current transcript length, which is exactly `k`.
        rw [DeterministicValueOracleMethod.queryAfter, uniformGridMethod]
        simp [oracleTranscript_length, hk_lt]
      have hprefix :
          (fun i : Fin k =>
            (orderedGridPoint n p (Fin.castLE hk_le i),
              f (orderedGridPoint n p (Fin.castLE hk_le i)))) =
            fun i : Fin k =>
              (orderedGridPoint n p (Fin.castLE hk i.castSucc),
                f (orderedGridPoint n p (Fin.castLE hk i.castSucc))) := by
        -- Restricting the `(k + 1)`-indexing to the first `k` entries matches `Fin.castSucc`.
        funext i
        simp
      have hlastIndex :
          (⟨k, hk_lt⟩ : Fin ((p : ℕ) ^ n)) = Fin.castLE hk (Fin.last k) := by
        -- The last element of `Fin (k + 1)` has value `k`, so both indices are equal.
        ext
        simp
      have hlast :
          (orderedGridPoint n p ⟨k, hk_lt⟩, (f ∘ (↑)) (orderedGridPoint n p ⟨k, hk_lt⟩)) =
            (orderedGridPoint n p (Fin.castLE hk (Fin.last k)),
              f (orderedGridPoint n p (Fin.castLE hk (Fin.last k)))) := by
        -- The last index of `Fin (k + 1)` is exactly the newly appended grid point.
        simp [hlastIndex]
      -- Appending the next queried sample matches the `List.ofFn` description at length `k + 1`.
      rw [DeterministicValueOracleMethod.oracleTranscript_succ, ih hk_le, hquery,
        List.ofFn_succ', List.concat_eq_append]
      rw [hprefix, hlast]

/-- Helper for Algorithm 1.3.5: a list-level argmin sample from the full ordered transcript
produces a constrained argmin point on the midpoint grid. -/
private theorem ordered_grid_sample_mem_argmin_of_list_argmin
    (p : ℕ+) (f : E → ℝ) {sample : zeroOneBox n × ℝ}
    (hsample :
      sample ∈
        (List.ofFn (fun k : Fin ((p : ℕ) ^ n) =>
          (orderedGridPoint n p k, f (orderedGridPoint n p k)))).argmin Prod.snd) :
    (sample.1 : E) ∈ argmin[uniformGrid n p] f := by
  -- Recover the ordered-grid index of the chosen sample from its membership in the transcript.
  have hsample_mem :
      sample ∈ Set.range (fun k : Fin ((p : ℕ) ^ n) =>
        (orderedGridPoint n p k, f (orderedGridPoint n p k))) := by
    rw [← List.mem_ofFn']
    exact List.argmin_mem hsample
  rcases hsample_mem with ⟨k, rfl⟩
  rw [mem_constrainedArgmin_iff]
  refine ⟨orderedGridPoint_mem_uniformGrid n p k, ?_⟩
  -- Compare the chosen sample with an arbitrary feasible grid point using list-level minimality.
  rw [isMinOn_iff]
  intro x hx
  rcases (mem_uniformGrid_iff_exists_orderedGridPoint n (p := p)).1 hx with ⟨j, rfl⟩
  have hj_mem :
      (orderedGridPoint n p j, f (orderedGridPoint n p j)) ∈
        List.ofFn (fun k : Fin ((p : ℕ) ^ n) =>
          (orderedGridPoint n p k, f (orderedGridPoint n p k))) := by
    rw [List.mem_ofFn']
    exact ⟨j, rfl⟩
  simpa using List.le_of_mem_argmin (f := Prod.snd) hj_mem hsample

/-- After exactly `p^n` value-oracle calls, the canonical uniform grid method returns a minimizer
of `f` on the midpoint grid `uniformGrid n p`, in the canonical constrained-argmin sense. -/
-- Proof sketch: after `p^n` steps the transcript contains exactly the ordered list of all grid
-- points with their sampled values, so the `List.argmin` rule in `uniformGridMethod` returns a
-- grid point with minimal recorded objective value among the whole grid, hence a member of the
-- canonical argmin set on that grid.
theorem uniformGridMethod_output_mem_argmin (p : ℕ+) (f : E → ℝ) :
    ↑((uniformGridMethod n p).outputAfter (f ∘ (↑)) ((p : ℕ) ^ n)) ∈ argmin[uniformGrid n p] f :=
  by
  let samples : List (zeroOneBox n × ℝ) :=
    List.ofFn (fun k : Fin ((p : ℕ) ^ n) =>
      (orderedGridPoint n p k, f (orderedGridPoint n p k)))
  have htrans :
      (uniformGridMethod n p).oracleTranscript (f ∘ (↑)) ((p : ℕ) ^ n) = samples := by
    -- At the full budget `p^n`, the transcript has enumerated the entire ordered grid.
    simpa [samples] using
      oracleTranscript_uniformGridMethod_eq_of_le n p f (k := (p : ℕ) ^ n) le_rfl
  have hsamples_ne : samples ≠ [] := by
    -- The midpoint grid has cardinality `(p : ℕ)^n`, which is always positive.
    intro hsamples
    have hcard : (p : ℕ) ^ n = 0 := by
      simpa [samples] using congrArg List.length hsamples
    exact (Nat.ne_of_gt (pow_pos p.pos n)) hcard
  have harg_ne_none : samples.argmin Prod.snd ≠ none := by
    -- A nonempty list always has a selected `argmin`.
    intro hnone
    exact hsamples_ne ((List.argmin_eq_none).1 hnone)
  cases harg : samples.argmin Prod.snd with
  | none =>
      exact False.elim (harg_ne_none harg)
  | some sample =>
      have harg_trans :
          List.argmin Prod.snd
              ((uniformGridMethod n p).oracleTranscript (f ∘ (↑)) ((p : ℕ) ^ n)) =
            some sample := by
        -- Transfer the chosen `argmin` witness back to the actual transcript.
        rw [htrans]
        exact harg
      have hout :
          (uniformGridMethod n p).outputAfter (f ∘ (↑)) ((p : ℕ) ^ n) = sample.1 := by
        -- Write the output as the transcript-side `argmin` match and reduce it with `harg_trans`.
        change
          (match
              List.argmin Prod.snd
                ((uniformGridMethod n p).oracleTranscript (f ∘ (↑)) ((p : ℕ) ^ n))
            with
            | some sample => sample.1
            | none => orderedGridPoint n p 0) = sample.1
        rw [harg_trans]
      have hout_coe :
          (↑((uniformGridMethod n p).outputAfter (f ∘ (↑)) ((p : ℕ) ^ n)) : E) = sample.1 := by
        -- Coercing the output equality to the ambient Euclidean space matches the target surface.
        simpa using congrArg (fun x : zeroOneBox n => (x : E)) hout
      have hsample_argmin : (sample.1 : E) ∈ argmin[uniformGrid n p] f :=
        ordered_grid_sample_mem_argmin_of_list_argmin n p f (sample := sample) (by simpa [harg])
      -- Rewrite the output to `sample.1` and reuse the constrained-argmin decomposition.
      rw [mem_constrainedArgmin_iff]
      rw [hout_coe]
      exact mem_constrainedArgmin_iff.mp hsample_argmin

/-- After exactly `p^n` value-oracle calls, the output of `uniformGridMethod n p` lies on the
midpoint grid `uniformGrid n p`. -/
theorem uniformGridMethod_output_mem_uniformGrid (p : ℕ+) (f : E → ℝ) :
    ↑((uniformGridMethod n p).outputAfter (f ∘ (↑)) ((p : ℕ) ^ n)) ∈ uniformGrid n p := by
  exact (mem_constrainedArgmin_iff.mp (uniformGridMethod_output_mem_argmin n p f)).1

/-- After exactly `p^n` value-oracle calls, the output of `uniformGridMethod n p` minimizes `f`
on the midpoint grid `uniformGrid n p`. -/
theorem uniformGridMethod_output_isMinOn (p : ℕ+) (f : E → ℝ) :
    IsMinOn f (uniformGrid n p) ((uniformGridMethod n p).outputAfter (f ∘ (↑)) ((p : ℕ) ^ n)) :=
  by
  exact (mem_constrainedArgmin_iff.mp (uniformGridMethod_output_mem_argmin n p f)).2

end
