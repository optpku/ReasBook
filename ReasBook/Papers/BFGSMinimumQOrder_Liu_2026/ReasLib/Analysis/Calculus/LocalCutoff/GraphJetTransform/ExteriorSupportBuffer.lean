module

public import Mathlib.Analysis.Normed.Group.Basic

public section

universe u v

namespace LocalCutoff.GraphTransform

variable {E : Type u} [NormedAddCommGroup E]

/-- Helper for Infrastructure I.16a: a point outside an enlarged closed ball
remains outside the original closed ball after a displacement smaller than the
radius buffer. -/
theorem add_not_mem_closedBall_of_norm_lt_buffer
    {c x h : E} {R δ : ℝ}
    (hx : x ∉ Metric.closedBall c (R + δ)) (hh : ‖h‖ < δ) :
    x + h ∉ Metric.closedBall c R := by
  intro hxadd
  have hx_large : R + δ < dist x c := by
    simpa only [Metric.mem_closedBall, not_le] using hx
  have hxadd_le : dist (x + h) c ≤ R := by
    simpa only [Metric.mem_closedBall] using hxadd
  have hstep : dist x (x + h) = ‖h‖ := by
    rw [dist_eq_norm]
    simp only [sub_add_cancel_left, norm_neg]
  have htriangle : dist x c ≤ ‖h‖ + dist (x + h) c := by
    rw [← hstep]
    exact dist_triangle x (x + h) c
  linarith

/-- Helper for Infrastructure I.16a: a function vanishing outside a closed ball
vanishes at both endpoints of every sufficiently short displacement based
outside the buffered ball. -/
theorem eq_zero_pair_of_eq_zero_outside_closedBall
    {F : Type v} [Zero F] (f : E → F)
    {c x h : E} {R δ : ℝ}
    (hzero : ∀ y, y ∉ Metric.closedBall c R → f y = 0)
    (hx : x ∉ Metric.closedBall c (R + δ)) (hh : ‖h‖ < δ) :
    f x = 0 ∧ f (x + h) = 0 := by
  have hδ : 0 < δ := (norm_nonneg h).trans_lt hh
  have hzero_displacement : ‖(0 : E)‖ < δ := by
    simpa only [norm_zero] using hδ
  have hx_outside := add_not_mem_closedBall_of_norm_lt_buffer
    (c := c) (h := (0 : E)) hx hzero_displacement
  have hx_outside' : x ∉ Metric.closedBall c R := by
    simpa only [add_zero] using hx_outside
  have hxadd_outside := add_not_mem_closedBall_of_norm_lt_buffer hx hh
  exact ⟨hzero x hx_outside', hzero (x + h) hxadd_outside⟩

/-- Helper for Infrastructure I.16a: the endpoint difference of a function
vanishing outside a closed ball is zero on every sufficiently short
displacement based outside the buffered ball. -/
theorem sub_eq_zero_of_eq_zero_outside_closedBall
    {F : Type v} [AddGroup F] (f : E → F)
    {c x h : E} {R δ : ℝ}
    (hzero : ∀ y, y ∉ Metric.closedBall c R → f y = 0)
    (hx : x ∉ Metric.closedBall c (R + δ)) (hh : ‖h‖ < δ) :
    f x - f (x + h) = 0 := by
  obtain ⟨hx_zero, hxadd_zero⟩ :=
    eq_zero_pair_of_eq_zero_outside_closedBall f hzero hx hh
  rw [hx_zero, hxadd_zero, sub_zero]

end LocalCutoff.GraphTransform
