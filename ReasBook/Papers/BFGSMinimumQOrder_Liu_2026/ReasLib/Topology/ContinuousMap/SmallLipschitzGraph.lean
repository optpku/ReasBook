module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Instances.ENNReal.Lemmas

public section

open scoped NNReal

universe u

/-- Bounded continuous graphs `ζ : ℝ → E` that vanish at zero and obey prescribed
uniform and Lipschitz bounds. -/
abbrev SmallLipschitzGraph (E : Type u) [NormedAddCommGroup E]
    (radius slope : ℝ≥0) :
    Type u :=
  { ζ : BoundedContinuousFunction ℝ E //
    ζ 0 = 0 ∧ ‖ζ‖ ≤ (radius : ℝ) ∧ LipschitzWith slope ζ }

namespace SmallLipschitzGraph

variable {E : Type u} [NormedAddCommGroup E] {radius slope : ℝ≥0}

/-- A small Lipschitz graph evaluates through its underlying bounded continuous function. -/
instance instCoeFun : CoeFun (SmallLipschitzGraph E radius slope) (fun _ ↦ ℝ → E) :=
  ⟨fun ζ ↦ ζ.1⟩

/-- Construct a small Lipschitz graph from a bounded continuous function satisfying
the three defining constraints. -/
def of (ζ : BoundedContinuousFunction ℝ E) (h_zero : ζ 0 = 0)
    (h_norm : ‖ζ‖ ≤ (radius : ℝ)) (h_lipschitz : LipschitzWith slope ζ) :
    SmallLipschitzGraph E radius slope :=
  ⟨ζ, h_zero, h_norm, h_lipschitz⟩

/-- The combined defining specification of a small Lipschitz graph. -/
theorem spec (ζ : SmallLipschitzGraph E radius slope) :
    ζ 0 = 0 ∧ ‖(ζ : BoundedContinuousFunction ℝ E)‖ ≤ (radius : ℝ) ∧
      LipschitzWith slope ζ := by
  -- Project the three constraints stored in the defining subtype.
  exact ζ.property

/-- A small Lipschitz graph vanishes at zero. -/
theorem zero_apply (ζ : SmallLipschitzGraph E radius slope) : ζ 0 = 0 := by
  exact (spec ζ).1

/-- The bounded-continuous-function norm of a small Lipschitz graph is at most its radius. -/
theorem norm_le (ζ : SmallLipschitzGraph E radius slope) :
    ‖(ζ : BoundedContinuousFunction ℝ E)‖ ≤ (radius : ℝ) := by
  exact (spec ζ).2.1

/-- A small Lipschitz graph obeys its prescribed Lipschitz bound. -/
theorem lipschitzWith (ζ : SmallLipschitzGraph E radius slope) :
    LipschitzWith slope ζ := by
  exact (spec ζ).2.2

/-- Coercing a graph built with `of` recovers the original bounded continuous function. -/
theorem coe_of (ζ : BoundedContinuousFunction ℝ E) (h_zero : ζ 0 = 0)
    (h_norm : ‖ζ‖ ≤ (radius : ℝ)) (h_lipschitz : LipschitzWith slope ζ) :
    (of ζ h_zero h_norm h_lipschitz : BoundedContinuousFunction ℝ E) = ζ := by
  rfl

/-- The inherited distance is the distance between the underlying bounded continuous functions. -/
theorem dist_eq (ζ η : SmallLipschitzGraph E radius slope) :
    dist ζ η = dist (ζ : BoundedContinuousFunction ℝ E)
      (η : BoundedContinuousFunction ℝ E) := by
  rfl

/-- The constraint that a bounded continuous graph vanish at zero is closed. -/
theorem isClosed_valueAtZero :
    IsClosed { ζ : BoundedContinuousFunction ℝ E | ζ 0 = 0 } := by
  -- Evaluation at zero is continuous, so the zero fiber is closed.
  exact isClosed_eq (continuous_eval_const 0) continuous_const

/-- The constraint that the uniform norm be bounded by `radius` is closed. -/
theorem isClosed_supNorm (radius : ℝ≥0) :
    IsClosed { ζ : BoundedContinuousFunction ℝ E | ‖ζ‖ ≤ (radius : ℝ) } := by
  -- The norm bound is the preimage of a closed order interval.
  exact isClosed_le continuous_norm continuous_const

/-- The cone of bounded continuous graphs with Lipschitz constant at most `slope` is closed. -/
theorem isClosed_lipschitzWith (slope : ℝ≥0) :
    IsClosed { ζ : BoundedContinuousFunction ℝ E | LipschitzWith slope ζ } := by
  -- Pull back the closed Lipschitz cone along the continuous coercion to functions.
  exact (isClosed_setOf_lipschitzWith slope).preimage continuous_coeFun

/-- The ambient carrier cut out by all three small-graph constraints is closed. -/
theorem isClosed_carrier (radius slope : ℝ≥0) :
    IsClosed { ζ : BoundedContinuousFunction ℝ E |
      ζ 0 = 0 ∧ ‖ζ‖ ≤ (radius : ℝ) ∧ LipschitzWith slope ζ } := by
  -- Intersect the three closed defining constraints.
  simpa only [Set.setOf_and] using
    isClosed_valueAtZero.inter (isClosed_supNorm radius |>.inter (isClosed_lipschitzWith slope))

/-- The zero bounded continuous graph satisfies every nonnegative radius and slope bound. -/
theorem zero_spec (radius slope : ℝ≥0) :
    (0 : BoundedContinuousFunction ℝ E) 0 = 0 ∧
      ‖(0 : BoundedContinuousFunction ℝ E)‖ ≤ (radius : ℝ) ∧
        LipschitzWith slope (0 : BoundedContinuousFunction ℝ E) := by
  -- The zero graph is constant, and both bounds are nonnegative.
  constructor
  · rfl
  constructor
  · simpa only [norm_zero] using radius.coe_nonneg
  · refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, dist_self]
    exact mul_nonneg slope.coe_nonneg dist_nonneg

/-- The canonical zero small Lipschitz graph. -/
def zero (E : Type u) [NormedAddCommGroup E] (radius slope : ℝ≥0) :
    SmallLipschitzGraph E radius slope :=
  ⟨0, zero_spec radius slope⟩

/-- The underlying bounded continuous function of the zero graph is zero. -/
theorem coe_zero (radius slope : ℝ≥0) :
    (zero E radius slope : BoundedContinuousFunction ℝ E) = 0 := by
  rfl

/-- The zero graph gives a canonical inhabitant of every small Lipschitz graph space. -/
instance instNonempty (radius slope : ℝ≥0) :
    Nonempty (SmallLipschitzGraph E radius slope) :=
  ⟨zero E radius slope⟩

/-- A small Lipschitz graph space over a complete codomain is complete in the sup metric. -/
instance instCompleteSpace [CompleteSpace E] (radius slope : ℝ≥0) :
    CompleteSpace (SmallLipschitzGraph E radius slope) := by
  -- A closed subtype of the complete bounded-function space is complete.
  exact (isClosed_carrier radius slope).isComplete.completeSpace_coe

end SmallLipschitzGraph
