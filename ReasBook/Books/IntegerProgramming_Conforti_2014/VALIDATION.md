# Validation record: Lean 4.30.0 candidate

## Original remote result

M2F Job 2907 succeeded on 2026-11-02 at 07:46:21 UTC. The remote runner invoked
lake lean for each original target file, recorded Lean OK (proof), and published
all three files. The compiler reported non-sorry warnings. Published hashes matched
the terminal snapshot; results precede the ReasBook import-prefix relocation.

| Original path below Integer/Chapters | Attempt | Published original SHA256 |
| --- | --- | --- |
| Chap04/section_4_12/ch4_sec4_12_exercise_4_27.lean | 252165 | e91167695ec97487ae2152d05200b485cc0ee6893302dfd733a3095bf0a7e83c |
| Chap04/section_4_8/ch4_sec4_8_remark_4_32.lean | 252179 | 87143d50c418554eec8fe73af6fa89f766c6b0f71f56e7c7d74ff8cab89099b6 |
| Chap09/section_9_5/ch9_sec9_5_exercise_9_9.lean | 252169 | 63d4830a0c0f707701a02bc61e99e3076b7cec9169e243e30ea885c65ba65bec |

## Original five targets

| Declaration | Source / original file compilation | Explicit final axiom result |
| --- | --- | --- |
| SimpleGraph.matchingIncidenceVector_segment_isEdgeOf_iff_symmDiff_isCycleOrPath | replaced; original file compiled | passed: propext, Classical.choice, Quot.sound |
| SimpleGraph.matchingPolytope_inter_cardinality_hyperplane_eq_convexHull | replaced; original file compiled | missing actual output |
| rational_matrices_real_rhs_mixed_integer_hull_is_polyhedron | replaced; original file compiled | missing actual output |
| rational_matrices_real_rhs_mixed_integer_hull_recessionCone_eq | replaced; original file compiled | missing actual output |
| exists_open_split_cover_constant | replaced; original file compiled | passed: propext, Classical.choice, Quot.sound |

The Exercise 4.27 runner explicitly audited its first theorem only; its second
print-axioms command appears in source, but the returned logs lack its actual output.
The Remark 4.32 runner reconciled the planned main declaration to
exists_nonrational_matrix_counterexample_to_polyhedral_mixed_integer_hull and audited
that different theorem. Its passed output does not audit the original two targets.
An earlier worker_shutdown attempt was automatically retried by the service.
All five original statement headers were preserved against the pre-task baseline.
Only the three target Lean files changed before contribution packaging. Core object
definitions were preserved; stronger Chap09 helpers and imported Remark helpers were reviewed.
Job success and lexical zero placeholders are not complete per-target axiom evidence.

## Integration checks and limitations

- Proof source is preserved modulo the internal import-prefix rewrite and trimming 14 pre-existing trailing-whitespace lines.
- Book.lean imports all 1064 chapter modules. Static import closure and metadata
  schema/toolchain checks are run; these are not Lean kernel validation.
- Official main-branch author check reports 1065 files checked, 1065 invalid:
  verified opening Authors: headers are unresolved for the source and generated root.
- Relocated-root compilation has not been run. Intended command, from ReasBook/:
  lake env lean Books/IntegerProgramming_Conforti_2014/Book.lean
- No repository-wide build, new proof job, local proof-search pipeline, or budget increase
  is performed. Original 3-file compile results do not validate the combined public surface.
- Remark lifetime usage has token_accounting_complete=false after an interrupted
  in-flight call. Reported usage is below the original caps, but complete native/cached
  token usage cannot be certified; the old cached-input accounting issue is not claimed fixed.

Full axiom coverage, the relocated root build and verified per-file attribution remain
outstanding before this candidate can be described as fully validated.
